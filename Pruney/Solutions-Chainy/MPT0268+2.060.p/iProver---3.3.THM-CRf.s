%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:42 EST 2020

% Result     : Theorem 11.25s
% Output     : CNFRefutation 11.25s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 848 expanded)
%              Number of clauses        :   58 ( 156 expanded)
%              Number of leaves         :   13 ( 226 expanded)
%              Depth                    :   19
%              Number of atoms          :  357 (3201 expanded)
%              Number of equality atoms :  179 (1273 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f27,f30])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f28,f30])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f24,f30])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f18])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f42])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f31,f43])).

fof(f63,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f30,f43,f43])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK3,sK2)
        | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2 )
      & ( ~ r2_hidden(sK3,sK2)
        | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2 ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ( r2_hidden(sK3,sK2)
      | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2 )
    & ( ~ r2_hidden(sK3,sK2)
      | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f22])).

fof(f40,plain,
    ( ~ r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2 ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,
    ( ~ r2_hidden(sK3,sK2)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) = sK2 ),
    inference(definition_unfolding,[],[f40,f30,f43])).

fof(f41,plain,
    ( r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2 ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,
    ( r2_hidden(sK3,sK2)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != sK2 ),
    inference(definition_unfolding,[],[f41,f30,f43])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f32,f43])).

fof(f61,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f52])).

fof(f62,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f61])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f25,f30])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f48])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) != k2_enumset1(X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f38,f30,f43,f43])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_549,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_550,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2323,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1
    | r2_hidden(sK0(X0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_549,c_550])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_546,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2582,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(sK0(X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2323,c_546])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_542,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4692,plain,
    ( sK0(X0,X0,k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2))) = X1
    | k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_2582,c_542])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_541,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1094,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k2_enumset1(X0,X0,X0,X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_541,c_546])).

cnf(c_13,negated_conjecture,
    ( ~ r2_hidden(sK3,sK2)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) = sK2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_538,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) = sK2
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6571,plain,
    ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))) = k2_enumset1(sK3,sK3,sK3,sK3)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) = sK2 ),
    inference(superposition,[status(thm)],[c_1094,c_538])).

cnf(c_16883,plain,
    ( sK0(X0,X0,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k5_xboole_0(sK2,k3_xboole_0(sK2,X1))))) = sK3
    | k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k2_enumset1(sK3,sK3,sK3,sK3)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) = sK2 ),
    inference(superposition,[status(thm)],[c_4692,c_6571])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(sK3,sK2)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != sK2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_539,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != sK2
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_18868,plain,
    ( sK0(X0,X0,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k5_xboole_0(sK2,k3_xboole_0(sK2,X1))))) = sK3
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) = sK2
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(X0,X0)))) != sK2
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_16883,c_539])).

cnf(c_15,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != sK2
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_20083,plain,
    ( sK0(X0,X0,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k5_xboole_0(sK2,k3_xboole_0(sK2,X1))))) = sK3
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(X0,X0)))) != sK2
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18868,c_15])).

cnf(c_20096,plain,
    ( sK0(X0,X0,k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2))) = X1
    | sK0(X0,X0,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k5_xboole_0(sK2,k3_xboole_0(sK2,X3))))) = sK3
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)))) != sK2
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4692,c_20083])).

cnf(c_23,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_26,plain,
    ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_678,plain,
    ( r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),sK2)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) = sK2 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_686,plain,
    ( r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),sK2)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_812,plain,
    ( r2_hidden(sK3,sK2)
    | k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_818,plain,
    ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) = k2_enumset1(sK3,sK3,sK3,sK3)
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_812])).

cnf(c_202,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_707,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4)))
    | X2 != X0
    | k5_xboole_0(X3,k3_xboole_0(X3,X4)) != X1 ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_1263,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(X1,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)))
    | X1 != X0
    | k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(c_1265,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(sK3,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)))
    | k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) != k2_enumset1(sK3,sK3,sK3,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1263])).

cnf(c_199,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_788,plain,
    ( X0 != X1
    | k5_xboole_0(X2,k3_xboole_0(X2,X3)) != X1
    | k5_xboole_0(X2,k3_xboole_0(X2,X3)) = X0 ),
    inference(instantiation,[status(thm)],[c_199])).

cnf(c_1271,plain,
    ( X0 != k2_enumset1(sK3,sK3,sK3,sK3)
    | k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) = X0
    | k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_2091,plain,
    ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) != k2_enumset1(sK3,sK3,sK3,sK3)
    | k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) = k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) ),
    inference(instantiation,[status(thm)],[c_1271])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2045,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)))
    | ~ r2_hidden(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4414,plain,
    ( ~ r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)))
    | ~ r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_2045])).

cnf(c_783,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | r2_hidden(X3,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | X3 != X0
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(c_1249,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)))
    | ~ r2_hidden(sK3,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)))
    | X0 != sK3
    | k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) != k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) ),
    inference(instantiation,[status(thm)],[c_783])).

cnf(c_9951,plain,
    ( r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)))
    | ~ r2_hidden(sK3,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)))
    | sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2) != sK3
    | k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) != k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) ),
    inference(instantiation,[status(thm)],[c_1249])).

cnf(c_44644,plain,
    ( ~ r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),k2_enumset1(sK3,sK3,sK3,sK3))
    | sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2) = sK3 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_44649,plain,
    ( r2_hidden(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20096,c_15,c_23,c_26,c_678,c_686,c_818,c_1265,c_2091,c_4414,c_9951,c_44644])).

cnf(c_44661,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) = sK2 ),
    inference(superposition,[status(thm)],[c_44649,c_538])).

cnf(c_543,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_547,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1095,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k2_enumset1(X0,X0,X0,X0)
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_541,c_547])).

cnf(c_6729,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))))) = k2_enumset1(X0,X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_543,c_1095])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) != k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_540,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) != k2_enumset1(X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9406,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6729,c_540])).

cnf(c_44777,plain,
    ( r2_hidden(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_44661,c_9406])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44777,c_44649])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:45:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 11.25/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.25/1.99  
% 11.25/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.25/1.99  
% 11.25/1.99  ------  iProver source info
% 11.25/1.99  
% 11.25/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.25/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.25/1.99  git: non_committed_changes: false
% 11.25/1.99  git: last_make_outside_of_git: false
% 11.25/1.99  
% 11.25/1.99  ------ 
% 11.25/1.99  
% 11.25/1.99  ------ Input Options
% 11.25/1.99  
% 11.25/1.99  --out_options                           all
% 11.25/1.99  --tptp_safe_out                         true
% 11.25/1.99  --problem_path                          ""
% 11.25/1.99  --include_path                          ""
% 11.25/1.99  --clausifier                            res/vclausify_rel
% 11.25/1.99  --clausifier_options                    --mode clausify
% 11.25/1.99  --stdin                                 false
% 11.25/1.99  --stats_out                             all
% 11.25/1.99  
% 11.25/1.99  ------ General Options
% 11.25/1.99  
% 11.25/1.99  --fof                                   false
% 11.25/1.99  --time_out_real                         305.
% 11.25/1.99  --time_out_virtual                      -1.
% 11.25/1.99  --symbol_type_check                     false
% 11.25/1.99  --clausify_out                          false
% 11.25/1.99  --sig_cnt_out                           false
% 11.25/1.99  --trig_cnt_out                          false
% 11.25/1.99  --trig_cnt_out_tolerance                1.
% 11.25/1.99  --trig_cnt_out_sk_spl                   false
% 11.25/1.99  --abstr_cl_out                          false
% 11.25/1.99  
% 11.25/1.99  ------ Global Options
% 11.25/1.99  
% 11.25/1.99  --schedule                              default
% 11.25/1.99  --add_important_lit                     false
% 11.25/1.99  --prop_solver_per_cl                    1000
% 11.25/1.99  --min_unsat_core                        false
% 11.25/1.99  --soft_assumptions                      false
% 11.25/1.99  --soft_lemma_size                       3
% 11.25/1.99  --prop_impl_unit_size                   0
% 11.25/1.99  --prop_impl_unit                        []
% 11.25/1.99  --share_sel_clauses                     true
% 11.25/1.99  --reset_solvers                         false
% 11.25/1.99  --bc_imp_inh                            [conj_cone]
% 11.25/1.99  --conj_cone_tolerance                   3.
% 11.25/1.99  --extra_neg_conj                        none
% 11.25/1.99  --large_theory_mode                     true
% 11.25/1.99  --prolific_symb_bound                   200
% 11.25/1.99  --lt_threshold                          2000
% 11.25/1.99  --clause_weak_htbl                      true
% 11.25/1.99  --gc_record_bc_elim                     false
% 11.25/1.99  
% 11.25/1.99  ------ Preprocessing Options
% 11.25/1.99  
% 11.25/1.99  --preprocessing_flag                    true
% 11.25/1.99  --time_out_prep_mult                    0.1
% 11.25/1.99  --splitting_mode                        input
% 11.25/1.99  --splitting_grd                         true
% 11.25/1.99  --splitting_cvd                         false
% 11.25/1.99  --splitting_cvd_svl                     false
% 11.25/1.99  --splitting_nvd                         32
% 11.25/1.99  --sub_typing                            true
% 11.25/1.99  --prep_gs_sim                           true
% 11.25/1.99  --prep_unflatten                        true
% 11.25/1.99  --prep_res_sim                          true
% 11.25/1.99  --prep_upred                            true
% 11.25/1.99  --prep_sem_filter                       exhaustive
% 11.25/1.99  --prep_sem_filter_out                   false
% 11.25/1.99  --pred_elim                             true
% 11.25/1.99  --res_sim_input                         true
% 11.25/1.99  --eq_ax_congr_red                       true
% 11.25/1.99  --pure_diseq_elim                       true
% 11.25/1.99  --brand_transform                       false
% 11.25/1.99  --non_eq_to_eq                          false
% 11.25/1.99  --prep_def_merge                        true
% 11.25/1.99  --prep_def_merge_prop_impl              false
% 11.25/1.99  --prep_def_merge_mbd                    true
% 11.25/1.99  --prep_def_merge_tr_red                 false
% 11.25/1.99  --prep_def_merge_tr_cl                  false
% 11.25/1.99  --smt_preprocessing                     true
% 11.25/1.99  --smt_ac_axioms                         fast
% 11.25/1.99  --preprocessed_out                      false
% 11.25/1.99  --preprocessed_stats                    false
% 11.25/1.99  
% 11.25/1.99  ------ Abstraction refinement Options
% 11.25/1.99  
% 11.25/1.99  --abstr_ref                             []
% 11.25/1.99  --abstr_ref_prep                        false
% 11.25/1.99  --abstr_ref_until_sat                   false
% 11.25/1.99  --abstr_ref_sig_restrict                funpre
% 11.25/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.25/1.99  --abstr_ref_under                       []
% 11.25/1.99  
% 11.25/1.99  ------ SAT Options
% 11.25/1.99  
% 11.25/1.99  --sat_mode                              false
% 11.25/1.99  --sat_fm_restart_options                ""
% 11.25/1.99  --sat_gr_def                            false
% 11.25/1.99  --sat_epr_types                         true
% 11.25/1.99  --sat_non_cyclic_types                  false
% 11.25/1.99  --sat_finite_models                     false
% 11.25/1.99  --sat_fm_lemmas                         false
% 11.25/1.99  --sat_fm_prep                           false
% 11.25/1.99  --sat_fm_uc_incr                        true
% 11.25/1.99  --sat_out_model                         small
% 11.25/1.99  --sat_out_clauses                       false
% 11.25/1.99  
% 11.25/1.99  ------ QBF Options
% 11.25/1.99  
% 11.25/1.99  --qbf_mode                              false
% 11.25/1.99  --qbf_elim_univ                         false
% 11.25/1.99  --qbf_dom_inst                          none
% 11.25/1.99  --qbf_dom_pre_inst                      false
% 11.25/1.99  --qbf_sk_in                             false
% 11.25/1.99  --qbf_pred_elim                         true
% 11.25/1.99  --qbf_split                             512
% 11.25/1.99  
% 11.25/1.99  ------ BMC1 Options
% 11.25/1.99  
% 11.25/1.99  --bmc1_incremental                      false
% 11.25/1.99  --bmc1_axioms                           reachable_all
% 11.25/1.99  --bmc1_min_bound                        0
% 11.25/1.99  --bmc1_max_bound                        -1
% 11.25/1.99  --bmc1_max_bound_default                -1
% 11.25/1.99  --bmc1_symbol_reachability              true
% 11.25/1.99  --bmc1_property_lemmas                  false
% 11.25/1.99  --bmc1_k_induction                      false
% 11.25/1.99  --bmc1_non_equiv_states                 false
% 11.25/1.99  --bmc1_deadlock                         false
% 11.25/1.99  --bmc1_ucm                              false
% 11.25/1.99  --bmc1_add_unsat_core                   none
% 11.25/1.99  --bmc1_unsat_core_children              false
% 11.25/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.25/1.99  --bmc1_out_stat                         full
% 11.25/1.99  --bmc1_ground_init                      false
% 11.25/1.99  --bmc1_pre_inst_next_state              false
% 11.25/1.99  --bmc1_pre_inst_state                   false
% 11.25/1.99  --bmc1_pre_inst_reach_state             false
% 11.25/1.99  --bmc1_out_unsat_core                   false
% 11.25/1.99  --bmc1_aig_witness_out                  false
% 11.25/1.99  --bmc1_verbose                          false
% 11.25/1.99  --bmc1_dump_clauses_tptp                false
% 11.25/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.25/1.99  --bmc1_dump_file                        -
% 11.25/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.25/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.25/1.99  --bmc1_ucm_extend_mode                  1
% 11.25/1.99  --bmc1_ucm_init_mode                    2
% 11.25/1.99  --bmc1_ucm_cone_mode                    none
% 11.25/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.25/1.99  --bmc1_ucm_relax_model                  4
% 11.25/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.25/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.25/1.99  --bmc1_ucm_layered_model                none
% 11.25/1.99  --bmc1_ucm_max_lemma_size               10
% 11.25/1.99  
% 11.25/1.99  ------ AIG Options
% 11.25/1.99  
% 11.25/1.99  --aig_mode                              false
% 11.25/1.99  
% 11.25/1.99  ------ Instantiation Options
% 11.25/1.99  
% 11.25/1.99  --instantiation_flag                    true
% 11.25/1.99  --inst_sos_flag                         false
% 11.25/1.99  --inst_sos_phase                        true
% 11.25/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.25/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.25/1.99  --inst_lit_sel_side                     num_symb
% 11.25/1.99  --inst_solver_per_active                1400
% 11.25/1.99  --inst_solver_calls_frac                1.
% 11.25/1.99  --inst_passive_queue_type               priority_queues
% 11.25/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.25/1.99  --inst_passive_queues_freq              [25;2]
% 11.25/1.99  --inst_dismatching                      true
% 11.25/1.99  --inst_eager_unprocessed_to_passive     true
% 11.25/1.99  --inst_prop_sim_given                   true
% 11.25/1.99  --inst_prop_sim_new                     false
% 11.25/1.99  --inst_subs_new                         false
% 11.25/1.99  --inst_eq_res_simp                      false
% 11.25/1.99  --inst_subs_given                       false
% 11.25/1.99  --inst_orphan_elimination               true
% 11.25/1.99  --inst_learning_loop_flag               true
% 11.25/1.99  --inst_learning_start                   3000
% 11.25/1.99  --inst_learning_factor                  2
% 11.25/1.99  --inst_start_prop_sim_after_learn       3
% 11.25/1.99  --inst_sel_renew                        solver
% 11.25/1.99  --inst_lit_activity_flag                true
% 11.25/1.99  --inst_restr_to_given                   false
% 11.25/1.99  --inst_activity_threshold               500
% 11.25/1.99  --inst_out_proof                        true
% 11.25/1.99  
% 11.25/1.99  ------ Resolution Options
% 11.25/1.99  
% 11.25/1.99  --resolution_flag                       true
% 11.25/1.99  --res_lit_sel                           adaptive
% 11.25/1.99  --res_lit_sel_side                      none
% 11.25/1.99  --res_ordering                          kbo
% 11.25/1.99  --res_to_prop_solver                    active
% 11.25/1.99  --res_prop_simpl_new                    false
% 11.25/1.99  --res_prop_simpl_given                  true
% 11.25/1.99  --res_passive_queue_type                priority_queues
% 11.25/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.25/1.99  --res_passive_queues_freq               [15;5]
% 11.25/1.99  --res_forward_subs                      full
% 11.25/1.99  --res_backward_subs                     full
% 11.25/1.99  --res_forward_subs_resolution           true
% 11.25/1.99  --res_backward_subs_resolution          true
% 11.25/1.99  --res_orphan_elimination                true
% 11.25/1.99  --res_time_limit                        2.
% 11.25/1.99  --res_out_proof                         true
% 11.25/1.99  
% 11.25/1.99  ------ Superposition Options
% 11.25/1.99  
% 11.25/1.99  --superposition_flag                    true
% 11.25/1.99  --sup_passive_queue_type                priority_queues
% 11.25/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.25/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.25/1.99  --demod_completeness_check              fast
% 11.25/1.99  --demod_use_ground                      true
% 11.25/1.99  --sup_to_prop_solver                    passive
% 11.25/1.99  --sup_prop_simpl_new                    true
% 11.25/1.99  --sup_prop_simpl_given                  true
% 11.25/1.99  --sup_fun_splitting                     false
% 11.25/1.99  --sup_smt_interval                      50000
% 11.25/1.99  
% 11.25/1.99  ------ Superposition Simplification Setup
% 11.25/1.99  
% 11.25/1.99  --sup_indices_passive                   []
% 11.25/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.25/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.25/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.25/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.25/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.25/1.99  --sup_full_bw                           [BwDemod]
% 11.25/1.99  --sup_immed_triv                        [TrivRules]
% 11.25/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.25/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.25/1.99  --sup_immed_bw_main                     []
% 11.25/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.25/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.25/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.25/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.25/1.99  
% 11.25/1.99  ------ Combination Options
% 11.25/1.99  
% 11.25/1.99  --comb_res_mult                         3
% 11.25/1.99  --comb_sup_mult                         2
% 11.25/1.99  --comb_inst_mult                        10
% 11.25/1.99  
% 11.25/1.99  ------ Debug Options
% 11.25/1.99  
% 11.25/1.99  --dbg_backtrace                         false
% 11.25/1.99  --dbg_dump_prop_clauses                 false
% 11.25/1.99  --dbg_dump_prop_clauses_file            -
% 11.25/1.99  --dbg_out_stat                          false
% 11.25/1.99  ------ Parsing...
% 11.25/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.25/1.99  
% 11.25/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.25/1.99  
% 11.25/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.25/1.99  
% 11.25/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.25/1.99  ------ Proving...
% 11.25/1.99  ------ Problem Properties 
% 11.25/1.99  
% 11.25/1.99  
% 11.25/1.99  clauses                                 14
% 11.25/1.99  conjectures                             2
% 11.25/1.99  EPR                                     0
% 11.25/1.99  Horn                                    8
% 11.25/1.99  unary                                   1
% 11.25/1.99  binary                                  7
% 11.25/1.99  lits                                    34
% 11.25/1.99  lits eq                                 12
% 11.25/1.99  fd_pure                                 0
% 11.25/1.99  fd_pseudo                               0
% 11.25/1.99  fd_cond                                 0
% 11.25/1.99  fd_pseudo_cond                          5
% 11.25/1.99  AC symbols                              0
% 11.25/1.99  
% 11.25/1.99  ------ Schedule dynamic 5 is on 
% 11.25/1.99  
% 11.25/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.25/1.99  
% 11.25/1.99  
% 11.25/1.99  ------ 
% 11.25/1.99  Current options:
% 11.25/1.99  ------ 
% 11.25/1.99  
% 11.25/1.99  ------ Input Options
% 11.25/1.99  
% 11.25/1.99  --out_options                           all
% 11.25/1.99  --tptp_safe_out                         true
% 11.25/1.99  --problem_path                          ""
% 11.25/1.99  --include_path                          ""
% 11.25/1.99  --clausifier                            res/vclausify_rel
% 11.25/1.99  --clausifier_options                    --mode clausify
% 11.25/1.99  --stdin                                 false
% 11.25/1.99  --stats_out                             all
% 11.25/1.99  
% 11.25/1.99  ------ General Options
% 11.25/1.99  
% 11.25/1.99  --fof                                   false
% 11.25/1.99  --time_out_real                         305.
% 11.25/1.99  --time_out_virtual                      -1.
% 11.25/1.99  --symbol_type_check                     false
% 11.25/1.99  --clausify_out                          false
% 11.25/1.99  --sig_cnt_out                           false
% 11.25/1.99  --trig_cnt_out                          false
% 11.25/1.99  --trig_cnt_out_tolerance                1.
% 11.25/1.99  --trig_cnt_out_sk_spl                   false
% 11.25/1.99  --abstr_cl_out                          false
% 11.25/1.99  
% 11.25/1.99  ------ Global Options
% 11.25/1.99  
% 11.25/1.99  --schedule                              default
% 11.25/1.99  --add_important_lit                     false
% 11.25/1.99  --prop_solver_per_cl                    1000
% 11.25/1.99  --min_unsat_core                        false
% 11.25/1.99  --soft_assumptions                      false
% 11.25/1.99  --soft_lemma_size                       3
% 11.25/1.99  --prop_impl_unit_size                   0
% 11.25/1.99  --prop_impl_unit                        []
% 11.25/1.99  --share_sel_clauses                     true
% 11.25/1.99  --reset_solvers                         false
% 11.25/1.99  --bc_imp_inh                            [conj_cone]
% 11.25/1.99  --conj_cone_tolerance                   3.
% 11.25/1.99  --extra_neg_conj                        none
% 11.25/1.99  --large_theory_mode                     true
% 11.25/1.99  --prolific_symb_bound                   200
% 11.25/1.99  --lt_threshold                          2000
% 11.25/1.99  --clause_weak_htbl                      true
% 11.25/1.99  --gc_record_bc_elim                     false
% 11.25/1.99  
% 11.25/1.99  ------ Preprocessing Options
% 11.25/1.99  
% 11.25/1.99  --preprocessing_flag                    true
% 11.25/1.99  --time_out_prep_mult                    0.1
% 11.25/1.99  --splitting_mode                        input
% 11.25/1.99  --splitting_grd                         true
% 11.25/1.99  --splitting_cvd                         false
% 11.25/1.99  --splitting_cvd_svl                     false
% 11.25/1.99  --splitting_nvd                         32
% 11.25/1.99  --sub_typing                            true
% 11.25/1.99  --prep_gs_sim                           true
% 11.25/1.99  --prep_unflatten                        true
% 11.25/1.99  --prep_res_sim                          true
% 11.25/1.99  --prep_upred                            true
% 11.25/1.99  --prep_sem_filter                       exhaustive
% 11.25/1.99  --prep_sem_filter_out                   false
% 11.25/1.99  --pred_elim                             true
% 11.25/1.99  --res_sim_input                         true
% 11.25/1.99  --eq_ax_congr_red                       true
% 11.25/1.99  --pure_diseq_elim                       true
% 11.25/1.99  --brand_transform                       false
% 11.25/1.99  --non_eq_to_eq                          false
% 11.25/1.99  --prep_def_merge                        true
% 11.25/1.99  --prep_def_merge_prop_impl              false
% 11.25/1.99  --prep_def_merge_mbd                    true
% 11.25/1.99  --prep_def_merge_tr_red                 false
% 11.25/1.99  --prep_def_merge_tr_cl                  false
% 11.25/1.99  --smt_preprocessing                     true
% 11.25/1.99  --smt_ac_axioms                         fast
% 11.25/1.99  --preprocessed_out                      false
% 11.25/1.99  --preprocessed_stats                    false
% 11.25/1.99  
% 11.25/1.99  ------ Abstraction refinement Options
% 11.25/1.99  
% 11.25/1.99  --abstr_ref                             []
% 11.25/1.99  --abstr_ref_prep                        false
% 11.25/1.99  --abstr_ref_until_sat                   false
% 11.25/1.99  --abstr_ref_sig_restrict                funpre
% 11.25/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.25/1.99  --abstr_ref_under                       []
% 11.25/1.99  
% 11.25/1.99  ------ SAT Options
% 11.25/1.99  
% 11.25/1.99  --sat_mode                              false
% 11.25/1.99  --sat_fm_restart_options                ""
% 11.25/1.99  --sat_gr_def                            false
% 11.25/1.99  --sat_epr_types                         true
% 11.25/1.99  --sat_non_cyclic_types                  false
% 11.25/1.99  --sat_finite_models                     false
% 11.25/1.99  --sat_fm_lemmas                         false
% 11.25/1.99  --sat_fm_prep                           false
% 11.25/1.99  --sat_fm_uc_incr                        true
% 11.25/1.99  --sat_out_model                         small
% 11.25/1.99  --sat_out_clauses                       false
% 11.25/1.99  
% 11.25/1.99  ------ QBF Options
% 11.25/1.99  
% 11.25/1.99  --qbf_mode                              false
% 11.25/1.99  --qbf_elim_univ                         false
% 11.25/1.99  --qbf_dom_inst                          none
% 11.25/1.99  --qbf_dom_pre_inst                      false
% 11.25/1.99  --qbf_sk_in                             false
% 11.25/1.99  --qbf_pred_elim                         true
% 11.25/1.99  --qbf_split                             512
% 11.25/1.99  
% 11.25/1.99  ------ BMC1 Options
% 11.25/1.99  
% 11.25/1.99  --bmc1_incremental                      false
% 11.25/1.99  --bmc1_axioms                           reachable_all
% 11.25/1.99  --bmc1_min_bound                        0
% 11.25/1.99  --bmc1_max_bound                        -1
% 11.25/1.99  --bmc1_max_bound_default                -1
% 11.25/1.99  --bmc1_symbol_reachability              true
% 11.25/1.99  --bmc1_property_lemmas                  false
% 11.25/1.99  --bmc1_k_induction                      false
% 11.25/1.99  --bmc1_non_equiv_states                 false
% 11.25/1.99  --bmc1_deadlock                         false
% 11.25/1.99  --bmc1_ucm                              false
% 11.25/1.99  --bmc1_add_unsat_core                   none
% 11.25/1.99  --bmc1_unsat_core_children              false
% 11.25/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.25/1.99  --bmc1_out_stat                         full
% 11.25/1.99  --bmc1_ground_init                      false
% 11.25/1.99  --bmc1_pre_inst_next_state              false
% 11.25/1.99  --bmc1_pre_inst_state                   false
% 11.25/1.99  --bmc1_pre_inst_reach_state             false
% 11.25/1.99  --bmc1_out_unsat_core                   false
% 11.25/1.99  --bmc1_aig_witness_out                  false
% 11.25/1.99  --bmc1_verbose                          false
% 11.25/1.99  --bmc1_dump_clauses_tptp                false
% 11.25/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.25/1.99  --bmc1_dump_file                        -
% 11.25/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.25/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.25/1.99  --bmc1_ucm_extend_mode                  1
% 11.25/1.99  --bmc1_ucm_init_mode                    2
% 11.25/1.99  --bmc1_ucm_cone_mode                    none
% 11.25/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.25/1.99  --bmc1_ucm_relax_model                  4
% 11.25/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.25/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.25/1.99  --bmc1_ucm_layered_model                none
% 11.25/1.99  --bmc1_ucm_max_lemma_size               10
% 11.25/1.99  
% 11.25/1.99  ------ AIG Options
% 11.25/1.99  
% 11.25/1.99  --aig_mode                              false
% 11.25/1.99  
% 11.25/1.99  ------ Instantiation Options
% 11.25/1.99  
% 11.25/1.99  --instantiation_flag                    true
% 11.25/1.99  --inst_sos_flag                         false
% 11.25/1.99  --inst_sos_phase                        true
% 11.25/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.25/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.25/1.99  --inst_lit_sel_side                     none
% 11.25/1.99  --inst_solver_per_active                1400
% 11.25/1.99  --inst_solver_calls_frac                1.
% 11.25/1.99  --inst_passive_queue_type               priority_queues
% 11.25/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.25/1.99  --inst_passive_queues_freq              [25;2]
% 11.25/1.99  --inst_dismatching                      true
% 11.25/1.99  --inst_eager_unprocessed_to_passive     true
% 11.25/1.99  --inst_prop_sim_given                   true
% 11.25/1.99  --inst_prop_sim_new                     false
% 11.25/1.99  --inst_subs_new                         false
% 11.25/1.99  --inst_eq_res_simp                      false
% 11.25/1.99  --inst_subs_given                       false
% 11.25/1.99  --inst_orphan_elimination               true
% 11.25/1.99  --inst_learning_loop_flag               true
% 11.25/1.99  --inst_learning_start                   3000
% 11.25/1.99  --inst_learning_factor                  2
% 11.25/1.99  --inst_start_prop_sim_after_learn       3
% 11.25/1.99  --inst_sel_renew                        solver
% 11.25/1.99  --inst_lit_activity_flag                true
% 11.25/1.99  --inst_restr_to_given                   false
% 11.25/1.99  --inst_activity_threshold               500
% 11.25/1.99  --inst_out_proof                        true
% 11.25/1.99  
% 11.25/1.99  ------ Resolution Options
% 11.25/1.99  
% 11.25/1.99  --resolution_flag                       false
% 11.25/1.99  --res_lit_sel                           adaptive
% 11.25/1.99  --res_lit_sel_side                      none
% 11.25/1.99  --res_ordering                          kbo
% 11.25/1.99  --res_to_prop_solver                    active
% 11.25/1.99  --res_prop_simpl_new                    false
% 11.25/1.99  --res_prop_simpl_given                  true
% 11.25/1.99  --res_passive_queue_type                priority_queues
% 11.25/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.25/1.99  --res_passive_queues_freq               [15;5]
% 11.25/1.99  --res_forward_subs                      full
% 11.25/1.99  --res_backward_subs                     full
% 11.25/1.99  --res_forward_subs_resolution           true
% 11.25/1.99  --res_backward_subs_resolution          true
% 11.25/1.99  --res_orphan_elimination                true
% 11.25/1.99  --res_time_limit                        2.
% 11.25/1.99  --res_out_proof                         true
% 11.25/1.99  
% 11.25/1.99  ------ Superposition Options
% 11.25/1.99  
% 11.25/1.99  --superposition_flag                    true
% 11.25/1.99  --sup_passive_queue_type                priority_queues
% 11.25/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.25/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.25/1.99  --demod_completeness_check              fast
% 11.25/1.99  --demod_use_ground                      true
% 11.25/1.99  --sup_to_prop_solver                    passive
% 11.25/1.99  --sup_prop_simpl_new                    true
% 11.25/1.99  --sup_prop_simpl_given                  true
% 11.25/1.99  --sup_fun_splitting                     false
% 11.25/1.99  --sup_smt_interval                      50000
% 11.25/1.99  
% 11.25/1.99  ------ Superposition Simplification Setup
% 11.25/1.99  
% 11.25/1.99  --sup_indices_passive                   []
% 11.25/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.25/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.25/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.25/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.25/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.25/1.99  --sup_full_bw                           [BwDemod]
% 11.25/1.99  --sup_immed_triv                        [TrivRules]
% 11.25/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.25/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.25/1.99  --sup_immed_bw_main                     []
% 11.25/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.25/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.25/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.25/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.25/1.99  
% 11.25/1.99  ------ Combination Options
% 11.25/1.99  
% 11.25/1.99  --comb_res_mult                         3
% 11.25/1.99  --comb_sup_mult                         2
% 11.25/1.99  --comb_inst_mult                        10
% 11.25/1.99  
% 11.25/1.99  ------ Debug Options
% 11.25/1.99  
% 11.25/1.99  --dbg_backtrace                         false
% 11.25/1.99  --dbg_dump_prop_clauses                 false
% 11.25/1.99  --dbg_dump_prop_clauses_file            -
% 11.25/1.99  --dbg_out_stat                          false
% 11.25/1.99  
% 11.25/1.99  
% 11.25/1.99  
% 11.25/1.99  
% 11.25/1.99  ------ Proving...
% 11.25/1.99  
% 11.25/1.99  
% 11.25/1.99  % SZS status Theorem for theBenchmark.p
% 11.25/1.99  
% 11.25/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.25/1.99  
% 11.25/1.99  fof(f1,axiom,(
% 11.25/1.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f11,plain,(
% 11.25/1.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.25/1.99    inference(nnf_transformation,[],[f1])).
% 11.25/1.99  
% 11.25/1.99  fof(f12,plain,(
% 11.25/1.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.25/1.99    inference(flattening,[],[f11])).
% 11.25/1.99  
% 11.25/1.99  fof(f13,plain,(
% 11.25/1.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.25/1.99    inference(rectify,[],[f12])).
% 11.25/1.99  
% 11.25/1.99  fof(f14,plain,(
% 11.25/1.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 11.25/1.99    introduced(choice_axiom,[])).
% 11.25/1.99  
% 11.25/1.99  fof(f15,plain,(
% 11.25/1.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.25/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).
% 11.25/1.99  
% 11.25/1.99  fof(f27,plain,(
% 11.25/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 11.25/1.99    inference(cnf_transformation,[],[f15])).
% 11.25/1.99  
% 11.25/1.99  fof(f2,axiom,(
% 11.25/1.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f30,plain,(
% 11.25/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.25/1.99    inference(cnf_transformation,[],[f2])).
% 11.25/1.99  
% 11.25/1.99  fof(f46,plain,(
% 11.25/1.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 11.25/1.99    inference(definition_unfolding,[],[f27,f30])).
% 11.25/1.99  
% 11.25/1.99  fof(f28,plain,(
% 11.25/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 11.25/1.99    inference(cnf_transformation,[],[f15])).
% 11.25/1.99  
% 11.25/1.99  fof(f45,plain,(
% 11.25/1.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 11.25/1.99    inference(definition_unfolding,[],[f28,f30])).
% 11.25/1.99  
% 11.25/1.99  fof(f24,plain,(
% 11.25/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 11.25/1.99    inference(cnf_transformation,[],[f15])).
% 11.25/1.99  
% 11.25/1.99  fof(f49,plain,(
% 11.25/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 11.25/1.99    inference(definition_unfolding,[],[f24,f30])).
% 11.25/1.99  
% 11.25/1.99  fof(f60,plain,(
% 11.25/1.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 11.25/1.99    inference(equality_resolution,[],[f49])).
% 11.25/1.99  
% 11.25/1.99  fof(f3,axiom,(
% 11.25/1.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f16,plain,(
% 11.25/1.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 11.25/1.99    inference(nnf_transformation,[],[f3])).
% 11.25/1.99  
% 11.25/1.99  fof(f17,plain,(
% 11.25/1.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.25/1.99    inference(rectify,[],[f16])).
% 11.25/1.99  
% 11.25/1.99  fof(f18,plain,(
% 11.25/1.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 11.25/1.99    introduced(choice_axiom,[])).
% 11.25/1.99  
% 11.25/1.99  fof(f19,plain,(
% 11.25/1.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.25/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f18])).
% 11.25/1.99  
% 11.25/1.99  fof(f31,plain,(
% 11.25/1.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 11.25/1.99    inference(cnf_transformation,[],[f19])).
% 11.25/1.99  
% 11.25/1.99  fof(f4,axiom,(
% 11.25/1.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f35,plain,(
% 11.25/1.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 11.25/1.99    inference(cnf_transformation,[],[f4])).
% 11.25/1.99  
% 11.25/1.99  fof(f5,axiom,(
% 11.25/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f36,plain,(
% 11.25/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.25/1.99    inference(cnf_transformation,[],[f5])).
% 11.25/1.99  
% 11.25/1.99  fof(f6,axiom,(
% 11.25/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f37,plain,(
% 11.25/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.25/1.99    inference(cnf_transformation,[],[f6])).
% 11.25/1.99  
% 11.25/1.99  fof(f42,plain,(
% 11.25/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 11.25/1.99    inference(definition_unfolding,[],[f36,f37])).
% 11.25/1.99  
% 11.25/1.99  fof(f43,plain,(
% 11.25/1.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 11.25/1.99    inference(definition_unfolding,[],[f35,f42])).
% 11.25/1.99  
% 11.25/1.99  fof(f53,plain,(
% 11.25/1.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 11.25/1.99    inference(definition_unfolding,[],[f31,f43])).
% 11.25/1.99  
% 11.25/1.99  fof(f63,plain,(
% 11.25/1.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 11.25/1.99    inference(equality_resolution,[],[f53])).
% 11.25/1.99  
% 11.25/1.99  fof(f7,axiom,(
% 11.25/1.99    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f20,plain,(
% 11.25/1.99    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)))),
% 11.25/1.99    inference(nnf_transformation,[],[f7])).
% 11.25/1.99  
% 11.25/1.99  fof(f39,plain,(
% 11.25/1.99    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) )),
% 11.25/1.99    inference(cnf_transformation,[],[f20])).
% 11.25/1.99  
% 11.25/1.99  fof(f54,plain,(
% 11.25/1.99    ( ! [X0,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0) | r2_hidden(X0,X1)) )),
% 11.25/1.99    inference(definition_unfolding,[],[f39,f30,f43,f43])).
% 11.25/1.99  
% 11.25/1.99  fof(f8,conjecture,(
% 11.25/1.99    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 11.25/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.25/1.99  
% 11.25/1.99  fof(f9,negated_conjecture,(
% 11.25/1.99    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 11.25/1.99    inference(negated_conjecture,[],[f8])).
% 11.25/1.99  
% 11.25/1.99  fof(f10,plain,(
% 11.25/1.99    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 11.25/1.99    inference(ennf_transformation,[],[f9])).
% 11.25/1.99  
% 11.25/1.99  fof(f21,plain,(
% 11.25/1.99    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 11.25/1.99    inference(nnf_transformation,[],[f10])).
% 11.25/1.99  
% 11.25/1.99  fof(f22,plain,(
% 11.25/1.99    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2) & (~r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2))),
% 11.25/1.99    introduced(choice_axiom,[])).
% 11.25/1.99  
% 11.25/1.99  fof(f23,plain,(
% 11.25/1.99    (r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2) & (~r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2)),
% 11.25/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f22])).
% 11.25/1.99  
% 11.25/1.99  fof(f40,plain,(
% 11.25/1.99    ~r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2),
% 11.25/1.99    inference(cnf_transformation,[],[f23])).
% 11.25/1.99  
% 11.25/1.99  fof(f57,plain,(
% 11.25/1.99    ~r2_hidden(sK3,sK2) | k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) = sK2),
% 11.25/1.99    inference(definition_unfolding,[],[f40,f30,f43])).
% 11.25/1.99  
% 11.25/1.99  fof(f41,plain,(
% 11.25/1.99    r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2),
% 11.25/1.99    inference(cnf_transformation,[],[f23])).
% 11.25/1.99  
% 11.25/1.99  fof(f56,plain,(
% 11.25/1.99    r2_hidden(sK3,sK2) | k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != sK2),
% 11.25/1.99    inference(definition_unfolding,[],[f41,f30,f43])).
% 11.25/1.99  
% 11.25/1.99  fof(f32,plain,(
% 11.25/1.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 11.25/1.99    inference(cnf_transformation,[],[f19])).
% 11.25/1.99  
% 11.25/1.99  fof(f52,plain,(
% 11.25/1.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 11.25/1.99    inference(definition_unfolding,[],[f32,f43])).
% 11.25/1.99  
% 11.25/1.99  fof(f61,plain,(
% 11.25/1.99    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 11.25/1.99    inference(equality_resolution,[],[f52])).
% 11.25/1.99  
% 11.25/1.99  fof(f62,plain,(
% 11.25/1.99    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 11.25/1.99    inference(equality_resolution,[],[f61])).
% 11.25/1.99  
% 11.25/1.99  fof(f29,plain,(
% 11.25/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 11.25/1.99    inference(cnf_transformation,[],[f15])).
% 11.25/1.99  
% 11.25/1.99  fof(f44,plain,(
% 11.25/1.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 11.25/1.99    inference(definition_unfolding,[],[f29,f30])).
% 11.25/1.99  
% 11.25/1.99  fof(f25,plain,(
% 11.25/1.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 11.25/1.99    inference(cnf_transformation,[],[f15])).
% 11.25/1.99  
% 11.25/1.99  fof(f48,plain,(
% 11.25/1.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 11.25/1.99    inference(definition_unfolding,[],[f25,f30])).
% 11.25/1.99  
% 11.25/1.99  fof(f59,plain,(
% 11.25/1.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 11.25/1.99    inference(equality_resolution,[],[f48])).
% 11.25/1.99  
% 11.25/1.99  fof(f38,plain,(
% 11.25/1.99    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)) )),
% 11.25/1.99    inference(cnf_transformation,[],[f20])).
% 11.25/1.99  
% 11.25/1.99  fof(f55,plain,(
% 11.25/1.99    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) != k2_enumset1(X0,X0,X0,X0)) )),
% 11.25/1.99    inference(definition_unfolding,[],[f38,f30,f43,f43])).
% 11.25/1.99  
% 11.25/1.99  cnf(c_2,plain,
% 11.25/1.99      ( r2_hidden(sK0(X0,X1,X2),X0)
% 11.25/1.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 11.25/1.99      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 11.25/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_549,plain,
% 11.25/1.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 11.25/1.99      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 11.25/1.99      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1,plain,
% 11.25/1.99      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 11.25/1.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 11.25/1.99      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 11.25/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_550,plain,
% 11.25/1.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 11.25/1.99      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 11.25/1.99      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_2323,plain,
% 11.25/1.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1
% 11.25/1.99      | r2_hidden(sK0(X0,X0,X1),X1) = iProver_top ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_549,c_550]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_5,plain,
% 11.25/1.99      ( r2_hidden(X0,X1)
% 11.25/1.99      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 11.25/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_546,plain,
% 11.25/1.99      ( r2_hidden(X0,X1) = iProver_top
% 11.25/1.99      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_2582,plain,
% 11.25/1.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
% 11.25/1.99      | r2_hidden(sK0(X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X1) = iProver_top ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_2323,c_546]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_9,plain,
% 11.25/1.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 11.25/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_542,plain,
% 11.25/1.99      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_4692,plain,
% 11.25/1.99      ( sK0(X0,X0,k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2))) = X1
% 11.25/1.99      | k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_2582,c_542]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_10,plain,
% 11.25/1.99      ( r2_hidden(X0,X1)
% 11.25/1.99      | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0) ),
% 11.25/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_541,plain,
% 11.25/1.99      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0)
% 11.25/1.99      | r2_hidden(X0,X1) = iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1094,plain,
% 11.25/1.99      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k2_enumset1(X0,X0,X0,X0)
% 11.25/1.99      | r2_hidden(X0,X1) = iProver_top ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_541,c_546]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_13,negated_conjecture,
% 11.25/1.99      ( ~ r2_hidden(sK3,sK2)
% 11.25/1.99      | k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) = sK2 ),
% 11.25/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_538,plain,
% 11.25/1.99      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) = sK2
% 11.25/1.99      | r2_hidden(sK3,sK2) != iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_6571,plain,
% 11.25/1.99      ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))) = k2_enumset1(sK3,sK3,sK3,sK3)
% 11.25/1.99      | k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) = sK2 ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_1094,c_538]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_16883,plain,
% 11.25/1.99      ( sK0(X0,X0,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k5_xboole_0(sK2,k3_xboole_0(sK2,X1))))) = sK3
% 11.25/1.99      | k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k2_enumset1(sK3,sK3,sK3,sK3)
% 11.25/1.99      | k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) = sK2 ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_4692,c_6571]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_12,negated_conjecture,
% 11.25/1.99      ( r2_hidden(sK3,sK2)
% 11.25/1.99      | k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != sK2 ),
% 11.25/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_539,plain,
% 11.25/1.99      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != sK2
% 11.25/1.99      | r2_hidden(sK3,sK2) = iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_18868,plain,
% 11.25/1.99      ( sK0(X0,X0,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k5_xboole_0(sK2,k3_xboole_0(sK2,X1))))) = sK3
% 11.25/1.99      | k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) = sK2
% 11.25/1.99      | k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(X0,X0)))) != sK2
% 11.25/1.99      | r2_hidden(sK3,sK2) = iProver_top ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_16883,c_539]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_15,plain,
% 11.25/1.99      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != sK2
% 11.25/1.99      | r2_hidden(sK3,sK2) = iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_20083,plain,
% 11.25/1.99      ( sK0(X0,X0,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k5_xboole_0(sK2,k3_xboole_0(sK2,X1))))) = sK3
% 11.25/1.99      | k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(X0,X0)))) != sK2
% 11.25/1.99      | r2_hidden(sK3,sK2) = iProver_top ),
% 11.25/1.99      inference(global_propositional_subsumption,
% 11.25/1.99                [status(thm)],
% 11.25/1.99                [c_18868,c_15]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_20096,plain,
% 11.25/1.99      ( sK0(X0,X0,k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2))) = X1
% 11.25/1.99      | sK0(X0,X0,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k5_xboole_0(sK2,k3_xboole_0(sK2,X3))))) = sK3
% 11.25/1.99      | k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)))) != sK2
% 11.25/1.99      | r2_hidden(sK3,sK2) = iProver_top ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_4692,c_20083]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_23,plain,
% 11.25/1.99      ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) | sK3 = sK3 ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_9]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_8,plain,
% 11.25/1.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 11.25/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_26,plain,
% 11.25/1.99      ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_8]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_678,plain,
% 11.25/1.99      ( r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),sK2)
% 11.25/1.99      | k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) = sK2 ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_2]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_0,plain,
% 11.25/1.99      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 11.25/1.99      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 11.25/1.99      | r2_hidden(sK0(X0,X1,X2),X1)
% 11.25/1.99      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 11.25/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_686,plain,
% 11.25/1.99      ( r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),k2_enumset1(sK3,sK3,sK3,sK3))
% 11.25/1.99      | ~ r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),sK2)
% 11.25/1.99      | k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) = sK2 ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_0]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_812,plain,
% 11.25/1.99      ( r2_hidden(sK3,sK2)
% 11.25/1.99      | k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_10]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_818,plain,
% 11.25/1.99      ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) = k2_enumset1(sK3,sK3,sK3,sK3)
% 11.25/1.99      | r2_hidden(sK3,sK2) = iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_812]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_202,plain,
% 11.25/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.25/1.99      theory(equality) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_707,plain,
% 11.25/1.99      ( ~ r2_hidden(X0,X1)
% 11.25/1.99      | r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4)))
% 11.25/1.99      | X2 != X0
% 11.25/1.99      | k5_xboole_0(X3,k3_xboole_0(X3,X4)) != X1 ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_202]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1263,plain,
% 11.25/1.99      ( ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
% 11.25/1.99      | r2_hidden(X1,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)))
% 11.25/1.99      | X1 != X0
% 11.25/1.99      | k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) != k2_enumset1(sK3,sK3,sK3,sK3) ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_707]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1265,plain,
% 11.25/1.99      ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
% 11.25/1.99      | r2_hidden(sK3,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)))
% 11.25/1.99      | k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) != k2_enumset1(sK3,sK3,sK3,sK3)
% 11.25/1.99      | sK3 != sK3 ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_1263]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_199,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_788,plain,
% 11.25/1.99      ( X0 != X1
% 11.25/1.99      | k5_xboole_0(X2,k3_xboole_0(X2,X3)) != X1
% 11.25/1.99      | k5_xboole_0(X2,k3_xboole_0(X2,X3)) = X0 ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_199]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1271,plain,
% 11.25/1.99      ( X0 != k2_enumset1(sK3,sK3,sK3,sK3)
% 11.25/1.99      | k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) = X0
% 11.25/1.99      | k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) != k2_enumset1(sK3,sK3,sK3,sK3) ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_788]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_2091,plain,
% 11.25/1.99      ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) != k2_enumset1(sK3,sK3,sK3,sK3)
% 11.25/1.99      | k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) = k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_1271]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_4,plain,
% 11.25/1.99      ( ~ r2_hidden(X0,X1)
% 11.25/1.99      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 11.25/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_2045,plain,
% 11.25/1.99      ( ~ r2_hidden(X0,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)))
% 11.25/1.99      | ~ r2_hidden(X0,sK2) ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_4]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_4414,plain,
% 11.25/1.99      ( ~ r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)))
% 11.25/1.99      | ~ r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),sK2) ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_2045]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_783,plain,
% 11.25/1.99      ( ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
% 11.25/1.99      | r2_hidden(X3,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
% 11.25/1.99      | X3 != X0
% 11.25/1.99      | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_707]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1249,plain,
% 11.25/1.99      ( r2_hidden(X0,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)))
% 11.25/1.99      | ~ r2_hidden(sK3,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)))
% 11.25/1.99      | X0 != sK3
% 11.25/1.99      | k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) != k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_783]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_9951,plain,
% 11.25/1.99      ( r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)))
% 11.25/1.99      | ~ r2_hidden(sK3,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)))
% 11.25/1.99      | sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2) != sK3
% 11.25/1.99      | k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) != k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK2)) ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_1249]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_44644,plain,
% 11.25/1.99      ( ~ r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),k2_enumset1(sK3,sK3,sK3,sK3))
% 11.25/1.99      | sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2) = sK3 ),
% 11.25/1.99      inference(instantiation,[status(thm)],[c_9]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_44649,plain,
% 11.25/1.99      ( r2_hidden(sK3,sK2) = iProver_top ),
% 11.25/1.99      inference(global_propositional_subsumption,
% 11.25/1.99                [status(thm)],
% 11.25/1.99                [c_20096,c_15,c_23,c_26,c_678,c_686,c_818,c_1265,c_2091,
% 11.25/1.99                 c_4414,c_9951,c_44644]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_44661,plain,
% 11.25/1.99      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) = sK2 ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_44649,c_538]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_543,plain,
% 11.25/1.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_547,plain,
% 11.25/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.25/1.99      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_1095,plain,
% 11.25/1.99      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k2_enumset1(X0,X0,X0,X0)
% 11.25/1.99      | r2_hidden(X0,X2) != iProver_top ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_541,c_547]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_6729,plain,
% 11.25/1.99      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))))) = k2_enumset1(X0,X0,X0,X0) ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_543,c_1095]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_11,plain,
% 11.25/1.99      ( ~ r2_hidden(X0,X1)
% 11.25/1.99      | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) != k2_enumset1(X0,X0,X0,X0) ),
% 11.25/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_540,plain,
% 11.25/1.99      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) != k2_enumset1(X0,X0,X0,X0)
% 11.25/1.99      | r2_hidden(X0,X1) != iProver_top ),
% 11.25/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_9406,plain,
% 11.25/1.99      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) != iProver_top ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_6729,c_540]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(c_44777,plain,
% 11.25/1.99      ( r2_hidden(sK3,sK2) != iProver_top ),
% 11.25/1.99      inference(superposition,[status(thm)],[c_44661,c_9406]) ).
% 11.25/1.99  
% 11.25/1.99  cnf(contradiction,plain,
% 11.25/1.99      ( $false ),
% 11.25/1.99      inference(minisat,[status(thm)],[c_44777,c_44649]) ).
% 11.25/1.99  
% 11.25/1.99  
% 11.25/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.25/1.99  
% 11.25/1.99  ------                               Statistics
% 11.25/1.99  
% 11.25/1.99  ------ General
% 11.25/1.99  
% 11.25/1.99  abstr_ref_over_cycles:                  0
% 11.25/1.99  abstr_ref_under_cycles:                 0
% 11.25/1.99  gc_basic_clause_elim:                   0
% 11.25/1.99  forced_gc_time:                         0
% 11.25/1.99  parsing_time:                           0.009
% 11.25/1.99  unif_index_cands_time:                  0.
% 11.25/1.99  unif_index_add_time:                    0.
% 11.25/1.99  orderings_time:                         0.
% 11.25/1.99  out_proof_time:                         0.009
% 11.25/1.99  total_time:                             1.386
% 11.25/1.99  num_of_symbols:                         39
% 11.25/1.99  num_of_terms:                           35182
% 11.25/1.99  
% 11.25/1.99  ------ Preprocessing
% 11.25/1.99  
% 11.25/1.99  num_of_splits:                          0
% 11.25/1.99  num_of_split_atoms:                     0
% 11.25/1.99  num_of_reused_defs:                     0
% 11.25/1.99  num_eq_ax_congr_red:                    10
% 11.25/1.99  num_of_sem_filtered_clauses:            1
% 11.25/1.99  num_of_subtypes:                        0
% 11.25/1.99  monotx_restored_types:                  0
% 11.25/1.99  sat_num_of_epr_types:                   0
% 11.25/1.99  sat_num_of_non_cyclic_types:            0
% 11.25/1.99  sat_guarded_non_collapsed_types:        0
% 11.25/1.99  num_pure_diseq_elim:                    0
% 11.25/1.99  simp_replaced_by:                       0
% 11.25/1.99  res_preprocessed:                       55
% 11.25/1.99  prep_upred:                             0
% 11.25/1.99  prep_unflattend:                        0
% 11.25/1.99  smt_new_axioms:                         0
% 11.25/1.99  pred_elim_cands:                        1
% 11.25/1.99  pred_elim:                              0
% 11.25/1.99  pred_elim_cl:                           0
% 11.25/1.99  pred_elim_cycles:                       1
% 11.25/1.99  merged_defs:                            12
% 11.25/1.99  merged_defs_ncl:                        0
% 11.25/1.99  bin_hyper_res:                          12
% 11.25/1.99  prep_cycles:                            3
% 11.25/1.99  pred_elim_time:                         0.
% 11.25/1.99  splitting_time:                         0.
% 11.25/1.99  sem_filter_time:                        0.
% 11.25/1.99  monotx_time:                            0.001
% 11.25/1.99  subtype_inf_time:                       0.
% 11.25/1.99  
% 11.25/1.99  ------ Problem properties
% 11.25/1.99  
% 11.25/1.99  clauses:                                14
% 11.25/1.99  conjectures:                            2
% 11.25/1.99  epr:                                    0
% 11.25/1.99  horn:                                   8
% 11.25/1.99  ground:                                 2
% 11.25/1.99  unary:                                  1
% 11.25/1.99  binary:                                 7
% 11.25/1.99  lits:                                   34
% 11.25/1.99  lits_eq:                                12
% 11.25/1.99  fd_pure:                                0
% 11.25/1.99  fd_pseudo:                              0
% 11.25/1.99  fd_cond:                                0
% 11.25/1.99  fd_pseudo_cond:                         5
% 11.25/1.99  ac_symbols:                             0
% 11.25/1.99  
% 11.25/1.99  ------ Propositional Solver
% 11.25/1.99  
% 11.25/1.99  prop_solver_calls:                      26
% 11.25/1.99  prop_fast_solver_calls:                 729
% 11.25/1.99  smt_solver_calls:                       0
% 11.25/1.99  smt_fast_solver_calls:                  0
% 11.25/1.99  prop_num_of_clauses:                    10418
% 11.25/1.99  prop_preprocess_simplified:             16304
% 11.25/1.99  prop_fo_subsumed:                       17
% 11.25/1.99  prop_solver_time:                       0.
% 11.25/1.99  smt_solver_time:                        0.
% 11.25/1.99  smt_fast_solver_time:                   0.
% 11.25/1.99  prop_fast_solver_time:                  0.
% 11.25/1.99  prop_unsat_core_time:                   0.
% 11.25/1.99  
% 11.25/1.99  ------ QBF
% 11.25/1.99  
% 11.25/1.99  qbf_q_res:                              0
% 11.25/1.99  qbf_num_tautologies:                    0
% 11.25/1.99  qbf_prep_cycles:                        0
% 11.25/1.99  
% 11.25/1.99  ------ BMC1
% 11.25/1.99  
% 11.25/1.99  bmc1_current_bound:                     -1
% 11.25/1.99  bmc1_last_solved_bound:                 -1
% 11.25/1.99  bmc1_unsat_core_size:                   -1
% 11.25/1.99  bmc1_unsat_core_parents_size:           -1
% 11.25/1.99  bmc1_merge_next_fun:                    0
% 11.25/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.25/1.99  
% 11.25/1.99  ------ Instantiation
% 11.25/1.99  
% 11.25/1.99  inst_num_of_clauses:                    1700
% 11.25/1.99  inst_num_in_passive:                    1159
% 11.25/1.99  inst_num_in_active:                     502
% 11.25/1.99  inst_num_in_unprocessed:                39
% 11.25/1.99  inst_num_of_loops:                      630
% 11.25/1.99  inst_num_of_learning_restarts:          0
% 11.25/1.99  inst_num_moves_active_passive:          126
% 11.25/1.99  inst_lit_activity:                      0
% 11.25/1.99  inst_lit_activity_moves:                0
% 11.25/1.99  inst_num_tautologies:                   0
% 11.25/1.99  inst_num_prop_implied:                  0
% 11.25/1.99  inst_num_existing_simplified:           0
% 11.25/1.99  inst_num_eq_res_simplified:             0
% 11.25/1.99  inst_num_child_elim:                    0
% 11.25/1.99  inst_num_of_dismatching_blockings:      2627
% 11.25/1.99  inst_num_of_non_proper_insts:           2077
% 11.25/1.99  inst_num_of_duplicates:                 0
% 11.25/1.99  inst_inst_num_from_inst_to_res:         0
% 11.25/1.99  inst_dismatching_checking_time:         0.
% 11.25/1.99  
% 11.25/1.99  ------ Resolution
% 11.25/1.99  
% 11.25/1.99  res_num_of_clauses:                     0
% 11.25/1.99  res_num_in_passive:                     0
% 11.25/1.99  res_num_in_active:                      0
% 11.25/1.99  res_num_of_loops:                       58
% 11.25/1.99  res_forward_subset_subsumed:            178
% 11.25/1.99  res_backward_subset_subsumed:           0
% 11.25/1.99  res_forward_subsumed:                   0
% 11.25/1.99  res_backward_subsumed:                  0
% 11.25/1.99  res_forward_subsumption_resolution:     0
% 11.25/1.99  res_backward_subsumption_resolution:    0
% 11.25/1.99  res_clause_to_clause_subsumption:       24443
% 11.25/1.99  res_orphan_elimination:                 0
% 11.25/1.99  res_tautology_del:                      151
% 11.25/1.99  res_num_eq_res_simplified:              0
% 11.25/1.99  res_num_sel_changes:                    0
% 11.25/1.99  res_moves_from_active_to_pass:          0
% 11.25/1.99  
% 11.25/1.99  ------ Superposition
% 11.25/1.99  
% 11.25/1.99  sup_time_total:                         0.
% 11.25/1.99  sup_time_generating:                    0.
% 11.25/1.99  sup_time_sim_full:                      0.
% 11.25/1.99  sup_time_sim_immed:                     0.
% 11.25/1.99  
% 11.25/1.99  sup_num_of_clauses:                     2233
% 11.25/1.99  sup_num_in_active:                      86
% 11.25/1.99  sup_num_in_passive:                     2147
% 11.25/1.99  sup_num_of_loops:                       125
% 11.25/1.99  sup_fw_superposition:                   1685
% 11.25/1.99  sup_bw_superposition:                   2787
% 11.25/1.99  sup_immediate_simplified:               956
% 11.25/1.99  sup_given_eliminated:                   0
% 11.25/1.99  comparisons_done:                       0
% 11.25/1.99  comparisons_avoided:                    268
% 11.25/1.99  
% 11.25/1.99  ------ Simplifications
% 11.25/1.99  
% 11.25/1.99  
% 11.25/1.99  sim_fw_subset_subsumed:                 597
% 11.25/1.99  sim_bw_subset_subsumed:                 32
% 11.25/1.99  sim_fw_subsumed:                        262
% 11.25/1.99  sim_bw_subsumed:                        40
% 11.25/1.99  sim_fw_subsumption_res:                 32
% 11.25/1.99  sim_bw_subsumption_res:                 9
% 11.25/1.99  sim_tautology_del:                      74
% 11.25/1.99  sim_eq_tautology_del:                   59
% 11.25/1.99  sim_eq_res_simp:                        8
% 11.25/1.99  sim_fw_demodulated:                     16
% 11.25/1.99  sim_bw_demodulated:                     37
% 11.25/1.99  sim_light_normalised:                   31
% 11.25/1.99  sim_joinable_taut:                      0
% 11.25/1.99  sim_joinable_simp:                      0
% 11.25/1.99  sim_ac_normalised:                      0
% 11.25/1.99  sim_smt_subsumption:                    0
% 11.25/1.99  
%------------------------------------------------------------------------------
