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
% DateTime   : Thu Dec  3 11:35:16 EST 2020

% Result     : Theorem 7.10s
% Output     : CNFRefutation 7.10s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 140 expanded)
%              Number of clauses        :   29 (  30 expanded)
%              Number of leaves         :   16 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :  342 ( 562 expanded)
%              Number of equality atoms :  213 ( 375 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
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
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).

fof(f48,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f48,f61])).

fof(f84,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f73])).

fof(f85,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f84])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X1
        & r2_hidden(X1,X2)
        & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X1
          & r2_hidden(X1,X2)
          & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r2_hidden(X1,X2)
      & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & r2_hidden(X1,X2)
        & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) )
   => ( sK3 != sK4
      & r2_hidden(sK4,sK5)
      & k3_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_tarski(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( sK3 != sK4
    & r2_hidden(sK4,sK5)
    & k3_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_tarski(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f18,f32])).

fof(f62,plain,(
    k3_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f65])).

fof(f83,plain,(
    k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f62,f65,f66])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))),X1) ),
    inference(definition_unfolding,[],[f44,f42])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f67,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f42,f42])).

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

fof(f14,plain,(
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

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f20])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f53,f65])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f82])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f54,f65])).

fof(f93,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f81])).

fof(f94,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f93])).

fof(f64,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,(
    r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_14,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_643,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_654,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_26,negated_conjecture,
    ( k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_9,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_648,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2006,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_648,c_8])).

cnf(c_2013,plain,
    ( r1_xboole_0(k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_2006])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_651,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_25562,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK3,sK3,sK3,sK3))) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2013,c_651])).

cnf(c_35308,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_654,c_25562])).

cnf(c_35534,plain,
    ( r2_hidden(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_643,c_35308])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_718,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(X0,X0,X0,X1))
    | sK4 = X0
    | sK4 = X1 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_719,plain,
    ( sK4 = X0
    | sK4 = X1
    | r2_hidden(sK4,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_721,plain,
    ( sK4 = sK3
    | r2_hidden(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_293,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_686,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_293])).

cnf(c_687,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_686])).

cnf(c_22,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_32,plain,
    ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_29,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,plain,
    ( r2_hidden(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35534,c_721,c_687,c_32,c_29,c_24,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:02:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.10/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.10/1.51  
% 7.10/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.10/1.51  
% 7.10/1.51  ------  iProver source info
% 7.10/1.51  
% 7.10/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.10/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.10/1.51  git: non_committed_changes: false
% 7.10/1.51  git: last_make_outside_of_git: false
% 7.10/1.51  
% 7.10/1.51  ------ 
% 7.10/1.51  
% 7.10/1.51  ------ Input Options
% 7.10/1.51  
% 7.10/1.51  --out_options                           all
% 7.10/1.51  --tptp_safe_out                         true
% 7.10/1.51  --problem_path                          ""
% 7.10/1.51  --include_path                          ""
% 7.10/1.51  --clausifier                            res/vclausify_rel
% 7.10/1.51  --clausifier_options                    ""
% 7.10/1.51  --stdin                                 false
% 7.10/1.51  --stats_out                             all
% 7.10/1.51  
% 7.10/1.51  ------ General Options
% 7.10/1.51  
% 7.10/1.51  --fof                                   false
% 7.10/1.51  --time_out_real                         305.
% 7.10/1.51  --time_out_virtual                      -1.
% 7.10/1.51  --symbol_type_check                     false
% 7.10/1.51  --clausify_out                          false
% 7.10/1.51  --sig_cnt_out                           false
% 7.10/1.51  --trig_cnt_out                          false
% 7.10/1.51  --trig_cnt_out_tolerance                1.
% 7.10/1.51  --trig_cnt_out_sk_spl                   false
% 7.10/1.51  --abstr_cl_out                          false
% 7.10/1.51  
% 7.10/1.51  ------ Global Options
% 7.10/1.51  
% 7.10/1.51  --schedule                              default
% 7.10/1.51  --add_important_lit                     false
% 7.10/1.51  --prop_solver_per_cl                    1000
% 7.10/1.51  --min_unsat_core                        false
% 7.10/1.51  --soft_assumptions                      false
% 7.10/1.51  --soft_lemma_size                       3
% 7.10/1.51  --prop_impl_unit_size                   0
% 7.10/1.51  --prop_impl_unit                        []
% 7.10/1.51  --share_sel_clauses                     true
% 7.10/1.51  --reset_solvers                         false
% 7.10/1.51  --bc_imp_inh                            [conj_cone]
% 7.10/1.51  --conj_cone_tolerance                   3.
% 7.10/1.51  --extra_neg_conj                        none
% 7.10/1.51  --large_theory_mode                     true
% 7.10/1.51  --prolific_symb_bound                   200
% 7.10/1.51  --lt_threshold                          2000
% 7.10/1.51  --clause_weak_htbl                      true
% 7.10/1.51  --gc_record_bc_elim                     false
% 7.10/1.51  
% 7.10/1.51  ------ Preprocessing Options
% 7.10/1.51  
% 7.10/1.51  --preprocessing_flag                    true
% 7.10/1.51  --time_out_prep_mult                    0.1
% 7.10/1.51  --splitting_mode                        input
% 7.10/1.51  --splitting_grd                         true
% 7.10/1.51  --splitting_cvd                         false
% 7.10/1.51  --splitting_cvd_svl                     false
% 7.10/1.51  --splitting_nvd                         32
% 7.10/1.51  --sub_typing                            true
% 7.10/1.51  --prep_gs_sim                           true
% 7.10/1.51  --prep_unflatten                        true
% 7.10/1.51  --prep_res_sim                          true
% 7.10/1.51  --prep_upred                            true
% 7.10/1.51  --prep_sem_filter                       exhaustive
% 7.10/1.51  --prep_sem_filter_out                   false
% 7.10/1.51  --pred_elim                             true
% 7.10/1.51  --res_sim_input                         true
% 7.10/1.51  --eq_ax_congr_red                       true
% 7.10/1.51  --pure_diseq_elim                       true
% 7.10/1.51  --brand_transform                       false
% 7.10/1.51  --non_eq_to_eq                          false
% 7.10/1.51  --prep_def_merge                        true
% 7.10/1.51  --prep_def_merge_prop_impl              false
% 7.10/1.51  --prep_def_merge_mbd                    true
% 7.10/1.51  --prep_def_merge_tr_red                 false
% 7.10/1.51  --prep_def_merge_tr_cl                  false
% 7.10/1.51  --smt_preprocessing                     true
% 7.10/1.51  --smt_ac_axioms                         fast
% 7.10/1.51  --preprocessed_out                      false
% 7.10/1.51  --preprocessed_stats                    false
% 7.10/1.51  
% 7.10/1.51  ------ Abstraction refinement Options
% 7.10/1.51  
% 7.10/1.51  --abstr_ref                             []
% 7.10/1.51  --abstr_ref_prep                        false
% 7.10/1.51  --abstr_ref_until_sat                   false
% 7.10/1.51  --abstr_ref_sig_restrict                funpre
% 7.10/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.10/1.51  --abstr_ref_under                       []
% 7.10/1.51  
% 7.10/1.51  ------ SAT Options
% 7.10/1.51  
% 7.10/1.51  --sat_mode                              false
% 7.10/1.51  --sat_fm_restart_options                ""
% 7.10/1.51  --sat_gr_def                            false
% 7.10/1.51  --sat_epr_types                         true
% 7.10/1.51  --sat_non_cyclic_types                  false
% 7.10/1.51  --sat_finite_models                     false
% 7.10/1.51  --sat_fm_lemmas                         false
% 7.10/1.51  --sat_fm_prep                           false
% 7.10/1.51  --sat_fm_uc_incr                        true
% 7.10/1.51  --sat_out_model                         small
% 7.10/1.51  --sat_out_clauses                       false
% 7.10/1.51  
% 7.10/1.51  ------ QBF Options
% 7.10/1.51  
% 7.10/1.51  --qbf_mode                              false
% 7.10/1.51  --qbf_elim_univ                         false
% 7.10/1.51  --qbf_dom_inst                          none
% 7.10/1.51  --qbf_dom_pre_inst                      false
% 7.10/1.51  --qbf_sk_in                             false
% 7.10/1.51  --qbf_pred_elim                         true
% 7.10/1.51  --qbf_split                             512
% 7.10/1.51  
% 7.10/1.51  ------ BMC1 Options
% 7.10/1.51  
% 7.10/1.51  --bmc1_incremental                      false
% 7.10/1.51  --bmc1_axioms                           reachable_all
% 7.10/1.51  --bmc1_min_bound                        0
% 7.10/1.51  --bmc1_max_bound                        -1
% 7.10/1.51  --bmc1_max_bound_default                -1
% 7.10/1.51  --bmc1_symbol_reachability              true
% 7.10/1.51  --bmc1_property_lemmas                  false
% 7.10/1.51  --bmc1_k_induction                      false
% 7.10/1.51  --bmc1_non_equiv_states                 false
% 7.10/1.51  --bmc1_deadlock                         false
% 7.10/1.51  --bmc1_ucm                              false
% 7.10/1.51  --bmc1_add_unsat_core                   none
% 7.10/1.51  --bmc1_unsat_core_children              false
% 7.10/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.10/1.51  --bmc1_out_stat                         full
% 7.10/1.51  --bmc1_ground_init                      false
% 7.10/1.51  --bmc1_pre_inst_next_state              false
% 7.10/1.51  --bmc1_pre_inst_state                   false
% 7.10/1.51  --bmc1_pre_inst_reach_state             false
% 7.10/1.51  --bmc1_out_unsat_core                   false
% 7.10/1.51  --bmc1_aig_witness_out                  false
% 7.10/1.51  --bmc1_verbose                          false
% 7.10/1.51  --bmc1_dump_clauses_tptp                false
% 7.10/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.10/1.51  --bmc1_dump_file                        -
% 7.10/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.10/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.10/1.51  --bmc1_ucm_extend_mode                  1
% 7.10/1.51  --bmc1_ucm_init_mode                    2
% 7.10/1.51  --bmc1_ucm_cone_mode                    none
% 7.10/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.10/1.51  --bmc1_ucm_relax_model                  4
% 7.10/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.10/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.10/1.51  --bmc1_ucm_layered_model                none
% 7.10/1.51  --bmc1_ucm_max_lemma_size               10
% 7.10/1.51  
% 7.10/1.51  ------ AIG Options
% 7.10/1.51  
% 7.10/1.51  --aig_mode                              false
% 7.10/1.51  
% 7.10/1.51  ------ Instantiation Options
% 7.10/1.51  
% 7.10/1.51  --instantiation_flag                    true
% 7.10/1.51  --inst_sos_flag                         true
% 7.10/1.51  --inst_sos_phase                        true
% 7.10/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.10/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.10/1.51  --inst_lit_sel_side                     num_symb
% 7.10/1.51  --inst_solver_per_active                1400
% 7.10/1.51  --inst_solver_calls_frac                1.
% 7.10/1.51  --inst_passive_queue_type               priority_queues
% 7.10/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.10/1.51  --inst_passive_queues_freq              [25;2]
% 7.10/1.51  --inst_dismatching                      true
% 7.10/1.51  --inst_eager_unprocessed_to_passive     true
% 7.10/1.51  --inst_prop_sim_given                   true
% 7.10/1.51  --inst_prop_sim_new                     false
% 7.10/1.51  --inst_subs_new                         false
% 7.10/1.51  --inst_eq_res_simp                      false
% 7.10/1.51  --inst_subs_given                       false
% 7.10/1.51  --inst_orphan_elimination               true
% 7.10/1.51  --inst_learning_loop_flag               true
% 7.10/1.51  --inst_learning_start                   3000
% 7.10/1.51  --inst_learning_factor                  2
% 7.10/1.51  --inst_start_prop_sim_after_learn       3
% 7.10/1.51  --inst_sel_renew                        solver
% 7.10/1.51  --inst_lit_activity_flag                true
% 7.10/1.51  --inst_restr_to_given                   false
% 7.10/1.51  --inst_activity_threshold               500
% 7.10/1.51  --inst_out_proof                        true
% 7.10/1.51  
% 7.10/1.51  ------ Resolution Options
% 7.10/1.51  
% 7.10/1.51  --resolution_flag                       true
% 7.10/1.51  --res_lit_sel                           adaptive
% 7.10/1.51  --res_lit_sel_side                      none
% 7.10/1.51  --res_ordering                          kbo
% 7.10/1.51  --res_to_prop_solver                    active
% 7.10/1.51  --res_prop_simpl_new                    false
% 7.10/1.51  --res_prop_simpl_given                  true
% 7.10/1.51  --res_passive_queue_type                priority_queues
% 7.10/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.10/1.51  --res_passive_queues_freq               [15;5]
% 7.10/1.51  --res_forward_subs                      full
% 7.10/1.51  --res_backward_subs                     full
% 7.10/1.51  --res_forward_subs_resolution           true
% 7.10/1.51  --res_backward_subs_resolution          true
% 7.10/1.51  --res_orphan_elimination                true
% 7.10/1.51  --res_time_limit                        2.
% 7.10/1.51  --res_out_proof                         true
% 7.10/1.51  
% 7.10/1.51  ------ Superposition Options
% 7.10/1.51  
% 7.10/1.51  --superposition_flag                    true
% 7.10/1.51  --sup_passive_queue_type                priority_queues
% 7.10/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.10/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.10/1.51  --demod_completeness_check              fast
% 7.10/1.51  --demod_use_ground                      true
% 7.10/1.51  --sup_to_prop_solver                    passive
% 7.10/1.51  --sup_prop_simpl_new                    true
% 7.10/1.51  --sup_prop_simpl_given                  true
% 7.10/1.51  --sup_fun_splitting                     true
% 7.10/1.51  --sup_smt_interval                      50000
% 7.10/1.51  
% 7.10/1.51  ------ Superposition Simplification Setup
% 7.10/1.51  
% 7.10/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.10/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.10/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.10/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.10/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.10/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.10/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.10/1.51  --sup_immed_triv                        [TrivRules]
% 7.10/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.10/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.10/1.51  --sup_immed_bw_main                     []
% 7.10/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.10/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.10/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.10/1.51  --sup_input_bw                          []
% 7.10/1.51  
% 7.10/1.51  ------ Combination Options
% 7.10/1.51  
% 7.10/1.51  --comb_res_mult                         3
% 7.10/1.51  --comb_sup_mult                         2
% 7.10/1.51  --comb_inst_mult                        10
% 7.10/1.51  
% 7.10/1.51  ------ Debug Options
% 7.10/1.51  
% 7.10/1.51  --dbg_backtrace                         false
% 7.10/1.51  --dbg_dump_prop_clauses                 false
% 7.10/1.51  --dbg_dump_prop_clauses_file            -
% 7.10/1.51  --dbg_out_stat                          false
% 7.10/1.51  ------ Parsing...
% 7.10/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.10/1.51  
% 7.10/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.10/1.51  
% 7.10/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.10/1.51  
% 7.10/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.10/1.51  ------ Proving...
% 7.10/1.51  ------ Problem Properties 
% 7.10/1.51  
% 7.10/1.51  
% 7.10/1.51  clauses                                 27
% 7.10/1.51  conjectures                             3
% 7.10/1.51  EPR                                     3
% 7.10/1.51  Horn                                    18
% 7.10/1.51  unary                                   11
% 7.10/1.51  binary                                  2
% 7.10/1.51  lits                                    61
% 7.10/1.51  lits eq                                 26
% 7.10/1.51  fd_pure                                 0
% 7.10/1.51  fd_pseudo                               0
% 7.10/1.51  fd_cond                                 0
% 7.10/1.51  fd_pseudo_cond                          7
% 7.10/1.51  AC symbols                              0
% 7.10/1.51  
% 7.10/1.51  ------ Schedule dynamic 5 is on 
% 7.10/1.51  
% 7.10/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.10/1.51  
% 7.10/1.51  
% 7.10/1.51  ------ 
% 7.10/1.51  Current options:
% 7.10/1.51  ------ 
% 7.10/1.51  
% 7.10/1.51  ------ Input Options
% 7.10/1.51  
% 7.10/1.51  --out_options                           all
% 7.10/1.51  --tptp_safe_out                         true
% 7.10/1.51  --problem_path                          ""
% 7.10/1.51  --include_path                          ""
% 7.10/1.51  --clausifier                            res/vclausify_rel
% 7.10/1.51  --clausifier_options                    ""
% 7.10/1.51  --stdin                                 false
% 7.10/1.51  --stats_out                             all
% 7.10/1.51  
% 7.10/1.51  ------ General Options
% 7.10/1.51  
% 7.10/1.51  --fof                                   false
% 7.10/1.51  --time_out_real                         305.
% 7.10/1.51  --time_out_virtual                      -1.
% 7.10/1.51  --symbol_type_check                     false
% 7.10/1.51  --clausify_out                          false
% 7.10/1.51  --sig_cnt_out                           false
% 7.10/1.51  --trig_cnt_out                          false
% 7.10/1.51  --trig_cnt_out_tolerance                1.
% 7.10/1.51  --trig_cnt_out_sk_spl                   false
% 7.10/1.51  --abstr_cl_out                          false
% 7.10/1.51  
% 7.10/1.51  ------ Global Options
% 7.10/1.51  
% 7.10/1.51  --schedule                              default
% 7.10/1.51  --add_important_lit                     false
% 7.10/1.51  --prop_solver_per_cl                    1000
% 7.10/1.51  --min_unsat_core                        false
% 7.10/1.51  --soft_assumptions                      false
% 7.10/1.51  --soft_lemma_size                       3
% 7.10/1.51  --prop_impl_unit_size                   0
% 7.10/1.51  --prop_impl_unit                        []
% 7.10/1.51  --share_sel_clauses                     true
% 7.10/1.51  --reset_solvers                         false
% 7.10/1.51  --bc_imp_inh                            [conj_cone]
% 7.10/1.51  --conj_cone_tolerance                   3.
% 7.10/1.51  --extra_neg_conj                        none
% 7.10/1.51  --large_theory_mode                     true
% 7.10/1.51  --prolific_symb_bound                   200
% 7.10/1.51  --lt_threshold                          2000
% 7.10/1.51  --clause_weak_htbl                      true
% 7.10/1.51  --gc_record_bc_elim                     false
% 7.10/1.51  
% 7.10/1.51  ------ Preprocessing Options
% 7.10/1.51  
% 7.10/1.51  --preprocessing_flag                    true
% 7.10/1.51  --time_out_prep_mult                    0.1
% 7.10/1.51  --splitting_mode                        input
% 7.10/1.51  --splitting_grd                         true
% 7.10/1.51  --splitting_cvd                         false
% 7.10/1.51  --splitting_cvd_svl                     false
% 7.10/1.51  --splitting_nvd                         32
% 7.10/1.51  --sub_typing                            true
% 7.10/1.51  --prep_gs_sim                           true
% 7.10/1.51  --prep_unflatten                        true
% 7.10/1.51  --prep_res_sim                          true
% 7.10/1.51  --prep_upred                            true
% 7.10/1.51  --prep_sem_filter                       exhaustive
% 7.10/1.51  --prep_sem_filter_out                   false
% 7.10/1.51  --pred_elim                             true
% 7.10/1.51  --res_sim_input                         true
% 7.10/1.51  --eq_ax_congr_red                       true
% 7.10/1.51  --pure_diseq_elim                       true
% 7.10/1.51  --brand_transform                       false
% 7.10/1.51  --non_eq_to_eq                          false
% 7.10/1.51  --prep_def_merge                        true
% 7.10/1.51  --prep_def_merge_prop_impl              false
% 7.10/1.51  --prep_def_merge_mbd                    true
% 7.10/1.51  --prep_def_merge_tr_red                 false
% 7.10/1.51  --prep_def_merge_tr_cl                  false
% 7.10/1.51  --smt_preprocessing                     true
% 7.10/1.51  --smt_ac_axioms                         fast
% 7.10/1.51  --preprocessed_out                      false
% 7.10/1.51  --preprocessed_stats                    false
% 7.10/1.51  
% 7.10/1.51  ------ Abstraction refinement Options
% 7.10/1.51  
% 7.10/1.51  --abstr_ref                             []
% 7.10/1.51  --abstr_ref_prep                        false
% 7.10/1.51  --abstr_ref_until_sat                   false
% 7.10/1.51  --abstr_ref_sig_restrict                funpre
% 7.10/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.10/1.51  --abstr_ref_under                       []
% 7.10/1.51  
% 7.10/1.51  ------ SAT Options
% 7.10/1.51  
% 7.10/1.51  --sat_mode                              false
% 7.10/1.51  --sat_fm_restart_options                ""
% 7.10/1.51  --sat_gr_def                            false
% 7.10/1.51  --sat_epr_types                         true
% 7.10/1.51  --sat_non_cyclic_types                  false
% 7.10/1.51  --sat_finite_models                     false
% 7.10/1.51  --sat_fm_lemmas                         false
% 7.10/1.51  --sat_fm_prep                           false
% 7.10/1.51  --sat_fm_uc_incr                        true
% 7.10/1.51  --sat_out_model                         small
% 7.10/1.51  --sat_out_clauses                       false
% 7.10/1.51  
% 7.10/1.51  ------ QBF Options
% 7.10/1.51  
% 7.10/1.51  --qbf_mode                              false
% 7.10/1.51  --qbf_elim_univ                         false
% 7.10/1.51  --qbf_dom_inst                          none
% 7.10/1.51  --qbf_dom_pre_inst                      false
% 7.10/1.51  --qbf_sk_in                             false
% 7.10/1.51  --qbf_pred_elim                         true
% 7.10/1.51  --qbf_split                             512
% 7.10/1.51  
% 7.10/1.51  ------ BMC1 Options
% 7.10/1.51  
% 7.10/1.51  --bmc1_incremental                      false
% 7.10/1.51  --bmc1_axioms                           reachable_all
% 7.10/1.51  --bmc1_min_bound                        0
% 7.10/1.51  --bmc1_max_bound                        -1
% 7.10/1.51  --bmc1_max_bound_default                -1
% 7.10/1.51  --bmc1_symbol_reachability              true
% 7.10/1.51  --bmc1_property_lemmas                  false
% 7.10/1.51  --bmc1_k_induction                      false
% 7.10/1.51  --bmc1_non_equiv_states                 false
% 7.10/1.51  --bmc1_deadlock                         false
% 7.10/1.51  --bmc1_ucm                              false
% 7.10/1.51  --bmc1_add_unsat_core                   none
% 7.10/1.51  --bmc1_unsat_core_children              false
% 7.10/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.10/1.51  --bmc1_out_stat                         full
% 7.10/1.51  --bmc1_ground_init                      false
% 7.10/1.51  --bmc1_pre_inst_next_state              false
% 7.10/1.51  --bmc1_pre_inst_state                   false
% 7.10/1.51  --bmc1_pre_inst_reach_state             false
% 7.10/1.51  --bmc1_out_unsat_core                   false
% 7.10/1.51  --bmc1_aig_witness_out                  false
% 7.10/1.51  --bmc1_verbose                          false
% 7.10/1.51  --bmc1_dump_clauses_tptp                false
% 7.10/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.10/1.51  --bmc1_dump_file                        -
% 7.10/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.10/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.10/1.51  --bmc1_ucm_extend_mode                  1
% 7.10/1.51  --bmc1_ucm_init_mode                    2
% 7.10/1.51  --bmc1_ucm_cone_mode                    none
% 7.10/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.10/1.51  --bmc1_ucm_relax_model                  4
% 7.10/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.10/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.10/1.51  --bmc1_ucm_layered_model                none
% 7.10/1.51  --bmc1_ucm_max_lemma_size               10
% 7.10/1.51  
% 7.10/1.51  ------ AIG Options
% 7.10/1.51  
% 7.10/1.51  --aig_mode                              false
% 7.10/1.51  
% 7.10/1.51  ------ Instantiation Options
% 7.10/1.51  
% 7.10/1.51  --instantiation_flag                    true
% 7.10/1.51  --inst_sos_flag                         true
% 7.10/1.51  --inst_sos_phase                        true
% 7.10/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.10/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.10/1.51  --inst_lit_sel_side                     none
% 7.10/1.51  --inst_solver_per_active                1400
% 7.10/1.51  --inst_solver_calls_frac                1.
% 7.10/1.51  --inst_passive_queue_type               priority_queues
% 7.10/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.10/1.51  --inst_passive_queues_freq              [25;2]
% 7.10/1.51  --inst_dismatching                      true
% 7.10/1.51  --inst_eager_unprocessed_to_passive     true
% 7.10/1.51  --inst_prop_sim_given                   true
% 7.10/1.51  --inst_prop_sim_new                     false
% 7.10/1.51  --inst_subs_new                         false
% 7.10/1.51  --inst_eq_res_simp                      false
% 7.10/1.51  --inst_subs_given                       false
% 7.10/1.51  --inst_orphan_elimination               true
% 7.10/1.51  --inst_learning_loop_flag               true
% 7.10/1.51  --inst_learning_start                   3000
% 7.10/1.51  --inst_learning_factor                  2
% 7.10/1.51  --inst_start_prop_sim_after_learn       3
% 7.10/1.51  --inst_sel_renew                        solver
% 7.10/1.51  --inst_lit_activity_flag                true
% 7.10/1.51  --inst_restr_to_given                   false
% 7.10/1.51  --inst_activity_threshold               500
% 7.10/1.51  --inst_out_proof                        true
% 7.10/1.51  
% 7.10/1.51  ------ Resolution Options
% 7.10/1.51  
% 7.10/1.51  --resolution_flag                       false
% 7.10/1.51  --res_lit_sel                           adaptive
% 7.10/1.51  --res_lit_sel_side                      none
% 7.10/1.51  --res_ordering                          kbo
% 7.10/1.51  --res_to_prop_solver                    active
% 7.10/1.51  --res_prop_simpl_new                    false
% 7.10/1.51  --res_prop_simpl_given                  true
% 7.10/1.51  --res_passive_queue_type                priority_queues
% 7.10/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.10/1.51  --res_passive_queues_freq               [15;5]
% 7.10/1.51  --res_forward_subs                      full
% 7.10/1.51  --res_backward_subs                     full
% 7.10/1.51  --res_forward_subs_resolution           true
% 7.10/1.51  --res_backward_subs_resolution          true
% 7.10/1.51  --res_orphan_elimination                true
% 7.10/1.51  --res_time_limit                        2.
% 7.10/1.51  --res_out_proof                         true
% 7.10/1.51  
% 7.10/1.51  ------ Superposition Options
% 7.10/1.51  
% 7.10/1.51  --superposition_flag                    true
% 7.10/1.51  --sup_passive_queue_type                priority_queues
% 7.10/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.10/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.10/1.51  --demod_completeness_check              fast
% 7.10/1.51  --demod_use_ground                      true
% 7.10/1.51  --sup_to_prop_solver                    passive
% 7.10/1.51  --sup_prop_simpl_new                    true
% 7.10/1.51  --sup_prop_simpl_given                  true
% 7.10/1.51  --sup_fun_splitting                     true
% 7.10/1.51  --sup_smt_interval                      50000
% 7.10/1.51  
% 7.10/1.51  ------ Superposition Simplification Setup
% 7.10/1.51  
% 7.10/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.10/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.10/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.10/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.10/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.10/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.10/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.10/1.51  --sup_immed_triv                        [TrivRules]
% 7.10/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.10/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.10/1.51  --sup_immed_bw_main                     []
% 7.10/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.10/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.10/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.10/1.51  --sup_input_bw                          []
% 7.10/1.51  
% 7.10/1.51  ------ Combination Options
% 7.10/1.51  
% 7.10/1.51  --comb_res_mult                         3
% 7.10/1.51  --comb_sup_mult                         2
% 7.10/1.51  --comb_inst_mult                        10
% 7.10/1.51  
% 7.10/1.51  ------ Debug Options
% 7.10/1.51  
% 7.10/1.51  --dbg_backtrace                         false
% 7.10/1.51  --dbg_dump_prop_clauses                 false
% 7.10/1.51  --dbg_dump_prop_clauses_file            -
% 7.10/1.51  --dbg_out_stat                          false
% 7.10/1.51  
% 7.10/1.51  
% 7.10/1.51  
% 7.10/1.51  
% 7.10/1.51  ------ Proving...
% 7.10/1.51  
% 7.10/1.51  
% 7.10/1.51  % SZS status Theorem for theBenchmark.p
% 7.10/1.51  
% 7.10/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.10/1.51  
% 7.10/1.51  fof(f7,axiom,(
% 7.10/1.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.10/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.10/1.51  
% 7.10/1.51  fof(f17,plain,(
% 7.10/1.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.10/1.51    inference(ennf_transformation,[],[f7])).
% 7.10/1.51  
% 7.10/1.51  fof(f22,plain,(
% 7.10/1.51    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.10/1.51    inference(nnf_transformation,[],[f17])).
% 7.10/1.51  
% 7.10/1.51  fof(f23,plain,(
% 7.10/1.51    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.10/1.51    inference(flattening,[],[f22])).
% 7.10/1.51  
% 7.10/1.51  fof(f24,plain,(
% 7.10/1.51    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.10/1.51    inference(rectify,[],[f23])).
% 7.10/1.51  
% 7.10/1.51  fof(f25,plain,(
% 7.10/1.51    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 7.10/1.51    introduced(choice_axiom,[])).
% 7.10/1.51  
% 7.10/1.51  fof(f26,plain,(
% 7.10/1.51    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.10/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).
% 7.10/1.51  
% 7.10/1.51  fof(f48,plain,(
% 7.10/1.51    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.10/1.51    inference(cnf_transformation,[],[f26])).
% 7.10/1.51  
% 7.10/1.51  fof(f11,axiom,(
% 7.10/1.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.10/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.10/1.51  
% 7.10/1.51  fof(f61,plain,(
% 7.10/1.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.10/1.51    inference(cnf_transformation,[],[f11])).
% 7.10/1.51  
% 7.10/1.51  fof(f73,plain,(
% 7.10/1.51    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 7.10/1.51    inference(definition_unfolding,[],[f48,f61])).
% 7.10/1.51  
% 7.10/1.51  fof(f84,plain,(
% 7.10/1.51    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 7.10/1.51    inference(equality_resolution,[],[f73])).
% 7.10/1.51  
% 7.10/1.51  fof(f85,plain,(
% 7.10/1.51    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 7.10/1.51    inference(equality_resolution,[],[f84])).
% 7.10/1.51  
% 7.10/1.51  fof(f2,axiom,(
% 7.10/1.51    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 7.10/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.10/1.51  
% 7.10/1.51  fof(f15,plain,(
% 7.10/1.51    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 7.10/1.51    inference(ennf_transformation,[],[f2])).
% 7.10/1.51  
% 7.10/1.51  fof(f19,plain,(
% 7.10/1.51    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 7.10/1.51    inference(nnf_transformation,[],[f15])).
% 7.10/1.51  
% 7.10/1.51  fof(f37,plain,(
% 7.10/1.51    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 7.10/1.51    inference(cnf_transformation,[],[f19])).
% 7.10/1.51  
% 7.10/1.51  fof(f12,conjecture,(
% 7.10/1.51    ! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0))),
% 7.10/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.10/1.51  
% 7.10/1.51  fof(f13,negated_conjecture,(
% 7.10/1.51    ~! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0))),
% 7.10/1.51    inference(negated_conjecture,[],[f12])).
% 7.10/1.51  
% 7.10/1.51  fof(f18,plain,(
% 7.10/1.51    ? [X0,X1,X2] : (X0 != X1 & r2_hidden(X1,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0))),
% 7.10/1.51    inference(ennf_transformation,[],[f13])).
% 7.10/1.51  
% 7.10/1.51  fof(f32,plain,(
% 7.10/1.51    ? [X0,X1,X2] : (X0 != X1 & r2_hidden(X1,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)) => (sK3 != sK4 & r2_hidden(sK4,sK5) & k3_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_tarski(sK3))),
% 7.10/1.51    introduced(choice_axiom,[])).
% 7.10/1.51  
% 7.10/1.51  fof(f33,plain,(
% 7.10/1.51    sK3 != sK4 & r2_hidden(sK4,sK5) & k3_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_tarski(sK3)),
% 7.10/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f18,f32])).
% 7.10/1.51  
% 7.10/1.51  fof(f62,plain,(
% 7.10/1.51    k3_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_tarski(sK3)),
% 7.10/1.51    inference(cnf_transformation,[],[f33])).
% 7.10/1.51  
% 7.10/1.51  fof(f9,axiom,(
% 7.10/1.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.10/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.10/1.51  
% 7.10/1.51  fof(f59,plain,(
% 7.10/1.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.10/1.51    inference(cnf_transformation,[],[f9])).
% 7.10/1.51  
% 7.10/1.51  fof(f10,axiom,(
% 7.10/1.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.10/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.10/1.51  
% 7.10/1.51  fof(f60,plain,(
% 7.10/1.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.10/1.51    inference(cnf_transformation,[],[f10])).
% 7.10/1.51  
% 7.10/1.51  fof(f65,plain,(
% 7.10/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.10/1.51    inference(definition_unfolding,[],[f60,f61])).
% 7.10/1.51  
% 7.10/1.51  fof(f66,plain,(
% 7.10/1.51    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.10/1.51    inference(definition_unfolding,[],[f59,f65])).
% 7.10/1.51  
% 7.10/1.51  fof(f83,plain,(
% 7.10/1.51    k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),sK5) = k2_enumset1(sK3,sK3,sK3,sK3)),
% 7.10/1.51    inference(definition_unfolding,[],[f62,f65,f66])).
% 7.10/1.51  
% 7.10/1.51  fof(f6,axiom,(
% 7.10/1.51    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 7.10/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.10/1.51  
% 7.10/1.51  fof(f44,plain,(
% 7.10/1.51    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 7.10/1.51    inference(cnf_transformation,[],[f6])).
% 7.10/1.51  
% 7.10/1.51  fof(f4,axiom,(
% 7.10/1.51    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.10/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.10/1.51  
% 7.10/1.51  fof(f42,plain,(
% 7.10/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.10/1.51    inference(cnf_transformation,[],[f4])).
% 7.10/1.51  
% 7.10/1.51  fof(f68,plain,(
% 7.10/1.51    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))),X1)) )),
% 7.10/1.51    inference(definition_unfolding,[],[f44,f42])).
% 7.10/1.51  
% 7.10/1.51  fof(f5,axiom,(
% 7.10/1.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.10/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.10/1.51  
% 7.10/1.51  fof(f43,plain,(
% 7.10/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.10/1.51    inference(cnf_transformation,[],[f5])).
% 7.10/1.51  
% 7.10/1.51  fof(f67,plain,(
% 7.10/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 7.10/1.51    inference(definition_unfolding,[],[f43,f42,f42])).
% 7.10/1.51  
% 7.10/1.51  fof(f3,axiom,(
% 7.10/1.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.10/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.10/1.51  
% 7.10/1.51  fof(f14,plain,(
% 7.10/1.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.10/1.51    inference(rectify,[],[f3])).
% 7.10/1.51  
% 7.10/1.51  fof(f16,plain,(
% 7.10/1.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.10/1.51    inference(ennf_transformation,[],[f14])).
% 7.10/1.51  
% 7.10/1.51  fof(f20,plain,(
% 7.10/1.51    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.10/1.51    introduced(choice_axiom,[])).
% 7.10/1.51  
% 7.10/1.51  fof(f21,plain,(
% 7.10/1.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.10/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f20])).
% 7.10/1.51  
% 7.10/1.51  fof(f41,plain,(
% 7.10/1.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.10/1.51    inference(cnf_transformation,[],[f21])).
% 7.10/1.51  
% 7.10/1.51  fof(f8,axiom,(
% 7.10/1.51    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.10/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.10/1.51  
% 7.10/1.51  fof(f27,plain,(
% 7.10/1.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.10/1.51    inference(nnf_transformation,[],[f8])).
% 7.10/1.51  
% 7.10/1.51  fof(f28,plain,(
% 7.10/1.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.10/1.51    inference(flattening,[],[f27])).
% 7.10/1.51  
% 7.10/1.51  fof(f29,plain,(
% 7.10/1.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.10/1.51    inference(rectify,[],[f28])).
% 7.10/1.51  
% 7.10/1.51  fof(f30,plain,(
% 7.10/1.51    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 7.10/1.51    introduced(choice_axiom,[])).
% 7.10/1.51  
% 7.10/1.51  fof(f31,plain,(
% 7.10/1.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.10/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 7.10/1.51  
% 7.10/1.51  fof(f53,plain,(
% 7.10/1.51    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 7.10/1.51    inference(cnf_transformation,[],[f31])).
% 7.10/1.51  
% 7.10/1.51  fof(f82,plain,(
% 7.10/1.51    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.10/1.51    inference(definition_unfolding,[],[f53,f65])).
% 7.10/1.51  
% 7.10/1.51  fof(f95,plain,(
% 7.10/1.51    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 7.10/1.51    inference(equality_resolution,[],[f82])).
% 7.10/1.51  
% 7.10/1.51  fof(f54,plain,(
% 7.10/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.10/1.51    inference(cnf_transformation,[],[f31])).
% 7.10/1.51  
% 7.10/1.51  fof(f81,plain,(
% 7.10/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.10/1.51    inference(definition_unfolding,[],[f54,f65])).
% 7.10/1.51  
% 7.10/1.51  fof(f93,plain,(
% 7.10/1.51    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 7.10/1.51    inference(equality_resolution,[],[f81])).
% 7.10/1.51  
% 7.10/1.51  fof(f94,plain,(
% 7.10/1.51    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 7.10/1.51    inference(equality_resolution,[],[f93])).
% 7.10/1.51  
% 7.10/1.51  fof(f64,plain,(
% 7.10/1.51    sK3 != sK4),
% 7.10/1.51    inference(cnf_transformation,[],[f33])).
% 7.10/1.51  
% 7.10/1.51  fof(f63,plain,(
% 7.10/1.51    r2_hidden(sK4,sK5)),
% 7.10/1.51    inference(cnf_transformation,[],[f33])).
% 7.10/1.51  
% 7.10/1.51  cnf(c_14,plain,
% 7.10/1.51      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 7.10/1.51      inference(cnf_transformation,[],[f85]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_643,plain,
% 7.10/1.51      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 7.10/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_2,plain,
% 7.10/1.51      ( ~ r2_hidden(X0,X1)
% 7.10/1.51      | r2_hidden(X0,X2)
% 7.10/1.51      | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 7.10/1.51      inference(cnf_transformation,[],[f37]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_654,plain,
% 7.10/1.51      ( r2_hidden(X0,X1) != iProver_top
% 7.10/1.51      | r2_hidden(X0,X2) = iProver_top
% 7.10/1.51      | r2_hidden(X0,k5_xboole_0(X1,X2)) = iProver_top ),
% 7.10/1.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_26,negated_conjecture,
% 7.10/1.51      ( k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),sK5) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 7.10/1.51      inference(cnf_transformation,[],[f83]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_9,plain,
% 7.10/1.51      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))),X1) ),
% 7.10/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_648,plain,
% 7.10/1.51      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))),X1) = iProver_top ),
% 7.10/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_8,plain,
% 7.10/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 7.10/1.51      inference(cnf_transformation,[],[f67]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_2006,plain,
% 7.10/1.51      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 7.10/1.51      inference(light_normalisation,[status(thm)],[c_648,c_8]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_2013,plain,
% 7.10/1.51      ( r1_xboole_0(k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK5) = iProver_top ),
% 7.10/1.51      inference(superposition,[status(thm)],[c_26,c_2006]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_5,plain,
% 7.10/1.51      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 7.10/1.51      inference(cnf_transformation,[],[f41]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_651,plain,
% 7.10/1.51      ( r1_xboole_0(X0,X1) != iProver_top
% 7.10/1.51      | r2_hidden(X2,X1) != iProver_top
% 7.10/1.51      | r2_hidden(X2,X0) != iProver_top ),
% 7.10/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_25562,plain,
% 7.10/1.51      ( r2_hidden(X0,k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK3,sK3,sK3,sK3))) != iProver_top
% 7.10/1.51      | r2_hidden(X0,sK5) != iProver_top ),
% 7.10/1.51      inference(superposition,[status(thm)],[c_2013,c_651]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_35308,plain,
% 7.10/1.51      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK4)) != iProver_top
% 7.10/1.51      | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
% 7.10/1.51      | r2_hidden(X0,sK5) != iProver_top ),
% 7.10/1.51      inference(superposition,[status(thm)],[c_654,c_25562]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_35534,plain,
% 7.10/1.51      ( r2_hidden(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
% 7.10/1.51      | r2_hidden(sK4,sK5) != iProver_top ),
% 7.10/1.51      inference(superposition,[status(thm)],[c_643,c_35308]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_23,plain,
% 7.10/1.51      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 7.10/1.51      inference(cnf_transformation,[],[f95]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_718,plain,
% 7.10/1.51      ( ~ r2_hidden(sK4,k2_enumset1(X0,X0,X0,X1)) | sK4 = X0 | sK4 = X1 ),
% 7.10/1.51      inference(instantiation,[status(thm)],[c_23]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_719,plain,
% 7.10/1.51      ( sK4 = X0
% 7.10/1.51      | sK4 = X1
% 7.10/1.51      | r2_hidden(sK4,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
% 7.10/1.51      inference(predicate_to_equality,[status(thm)],[c_718]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_721,plain,
% 7.10/1.51      ( sK4 = sK3
% 7.10/1.51      | r2_hidden(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 7.10/1.51      inference(instantiation,[status(thm)],[c_719]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_293,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_686,plain,
% 7.10/1.51      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 7.10/1.51      inference(instantiation,[status(thm)],[c_293]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_687,plain,
% 7.10/1.51      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 7.10/1.51      inference(instantiation,[status(thm)],[c_686]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_22,plain,
% 7.10/1.51      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 7.10/1.51      inference(cnf_transformation,[],[f94]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_32,plain,
% 7.10/1.51      ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 7.10/1.51      inference(instantiation,[status(thm)],[c_22]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_29,plain,
% 7.10/1.51      ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) | sK3 = sK3 ),
% 7.10/1.51      inference(instantiation,[status(thm)],[c_23]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_24,negated_conjecture,
% 7.10/1.51      ( sK3 != sK4 ),
% 7.10/1.51      inference(cnf_transformation,[],[f64]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_25,negated_conjecture,
% 7.10/1.51      ( r2_hidden(sK4,sK5) ),
% 7.10/1.51      inference(cnf_transformation,[],[f63]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(c_27,plain,
% 7.10/1.51      ( r2_hidden(sK4,sK5) = iProver_top ),
% 7.10/1.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.10/1.51  
% 7.10/1.51  cnf(contradiction,plain,
% 7.10/1.51      ( $false ),
% 7.10/1.51      inference(minisat,
% 7.10/1.51                [status(thm)],
% 7.10/1.51                [c_35534,c_721,c_687,c_32,c_29,c_24,c_27]) ).
% 7.10/1.51  
% 7.10/1.51  
% 7.10/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.10/1.51  
% 7.10/1.51  ------                               Statistics
% 7.10/1.51  
% 7.10/1.51  ------ General
% 7.10/1.51  
% 7.10/1.51  abstr_ref_over_cycles:                  0
% 7.10/1.51  abstr_ref_under_cycles:                 0
% 7.10/1.51  gc_basic_clause_elim:                   0
% 7.10/1.51  forced_gc_time:                         0
% 7.10/1.51  parsing_time:                           0.012
% 7.10/1.51  unif_index_cands_time:                  0.
% 7.10/1.51  unif_index_add_time:                    0.
% 7.10/1.51  orderings_time:                         0.
% 7.10/1.51  out_proof_time:                         0.008
% 7.10/1.51  total_time:                             0.905
% 7.10/1.51  num_of_symbols:                         42
% 7.10/1.51  num_of_terms:                           49577
% 7.10/1.51  
% 7.10/1.51  ------ Preprocessing
% 7.10/1.51  
% 7.10/1.51  num_of_splits:                          0
% 7.10/1.51  num_of_split_atoms:                     0
% 7.10/1.51  num_of_reused_defs:                     0
% 7.10/1.51  num_eq_ax_congr_red:                    22
% 7.10/1.51  num_of_sem_filtered_clauses:            1
% 7.10/1.51  num_of_subtypes:                        0
% 7.10/1.51  monotx_restored_types:                  0
% 7.10/1.51  sat_num_of_epr_types:                   0
% 7.10/1.51  sat_num_of_non_cyclic_types:            0
% 7.10/1.51  sat_guarded_non_collapsed_types:        0
% 7.10/1.51  num_pure_diseq_elim:                    0
% 7.10/1.51  simp_replaced_by:                       0
% 7.10/1.51  res_preprocessed:                       96
% 7.10/1.51  prep_upred:                             0
% 7.10/1.51  prep_unflattend:                        2
% 7.10/1.51  smt_new_axioms:                         0
% 7.10/1.51  pred_elim_cands:                        2
% 7.10/1.51  pred_elim:                              0
% 7.10/1.51  pred_elim_cl:                           0
% 7.10/1.51  pred_elim_cycles:                       1
% 7.10/1.51  merged_defs:                            0
% 7.10/1.51  merged_defs_ncl:                        0
% 7.10/1.51  bin_hyper_res:                          0
% 7.10/1.51  prep_cycles:                            3
% 7.10/1.51  pred_elim_time:                         0.001
% 7.10/1.51  splitting_time:                         0.
% 7.10/1.51  sem_filter_time:                        0.
% 7.10/1.51  monotx_time:                            0.
% 7.10/1.51  subtype_inf_time:                       0.
% 7.10/1.51  
% 7.10/1.51  ------ Problem properties
% 7.10/1.51  
% 7.10/1.51  clauses:                                27
% 7.10/1.51  conjectures:                            3
% 7.10/1.51  epr:                                    3
% 7.10/1.51  horn:                                   18
% 7.10/1.51  ground:                                 3
% 7.10/1.51  unary:                                  11
% 7.10/1.51  binary:                                 2
% 7.10/1.51  lits:                                   61
% 7.10/1.51  lits_eq:                                26
% 7.10/1.51  fd_pure:                                0
% 7.10/1.51  fd_pseudo:                              0
% 7.10/1.51  fd_cond:                                0
% 7.10/1.51  fd_pseudo_cond:                         7
% 7.10/1.51  ac_symbols:                             0
% 7.10/1.51  
% 7.10/1.51  ------ Propositional Solver
% 7.10/1.51  
% 7.10/1.51  prop_solver_calls:                      27
% 7.10/1.51  prop_fast_solver_calls:                 666
% 7.10/1.51  smt_solver_calls:                       0
% 7.10/1.51  smt_fast_solver_calls:                  0
% 7.10/1.51  prop_num_of_clauses:                    12390
% 7.10/1.51  prop_preprocess_simplified:             25040
% 7.10/1.51  prop_fo_subsumed:                       1
% 7.10/1.51  prop_solver_time:                       0.
% 7.10/1.51  smt_solver_time:                        0.
% 7.10/1.51  smt_fast_solver_time:                   0.
% 7.10/1.51  prop_fast_solver_time:                  0.
% 7.10/1.51  prop_unsat_core_time:                   0.001
% 7.10/1.51  
% 7.10/1.51  ------ QBF
% 7.10/1.51  
% 7.10/1.51  qbf_q_res:                              0
% 7.10/1.51  qbf_num_tautologies:                    0
% 7.10/1.51  qbf_prep_cycles:                        0
% 7.10/1.51  
% 7.10/1.51  ------ BMC1
% 7.10/1.51  
% 7.10/1.51  bmc1_current_bound:                     -1
% 7.10/1.51  bmc1_last_solved_bound:                 -1
% 7.10/1.51  bmc1_unsat_core_size:                   -1
% 7.10/1.51  bmc1_unsat_core_parents_size:           -1
% 7.10/1.51  bmc1_merge_next_fun:                    0
% 7.10/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.10/1.51  
% 7.10/1.51  ------ Instantiation
% 7.10/1.51  
% 7.10/1.51  inst_num_of_clauses:                    3357
% 7.10/1.51  inst_num_in_passive:                    1000
% 7.10/1.51  inst_num_in_active:                     720
% 7.10/1.51  inst_num_in_unprocessed:                1637
% 7.10/1.51  inst_num_of_loops:                      790
% 7.10/1.51  inst_num_of_learning_restarts:          0
% 7.10/1.51  inst_num_moves_active_passive:          70
% 7.10/1.51  inst_lit_activity:                      0
% 7.10/1.51  inst_lit_activity_moves:                1
% 7.10/1.51  inst_num_tautologies:                   0
% 7.10/1.51  inst_num_prop_implied:                  0
% 7.10/1.51  inst_num_existing_simplified:           0
% 7.10/1.51  inst_num_eq_res_simplified:             0
% 7.10/1.51  inst_num_child_elim:                    0
% 7.10/1.51  inst_num_of_dismatching_blockings:      9477
% 7.10/1.51  inst_num_of_non_proper_insts:           5116
% 7.10/1.51  inst_num_of_duplicates:                 0
% 7.10/1.51  inst_inst_num_from_inst_to_res:         0
% 7.10/1.51  inst_dismatching_checking_time:         0.
% 7.10/1.51  
% 7.10/1.51  ------ Resolution
% 7.10/1.51  
% 7.10/1.51  res_num_of_clauses:                     0
% 7.10/1.51  res_num_in_passive:                     0
% 7.10/1.51  res_num_in_active:                      0
% 7.10/1.51  res_num_of_loops:                       99
% 7.10/1.51  res_forward_subset_subsumed:            919
% 7.10/1.51  res_backward_subset_subsumed:           10
% 7.10/1.51  res_forward_subsumed:                   0
% 7.10/1.51  res_backward_subsumed:                  0
% 7.10/1.51  res_forward_subsumption_resolution:     0
% 7.10/1.51  res_backward_subsumption_resolution:    0
% 7.10/1.51  res_clause_to_clause_subsumption:       7073
% 7.10/1.51  res_orphan_elimination:                 0
% 7.10/1.51  res_tautology_del:                      17
% 7.10/1.51  res_num_eq_res_simplified:              0
% 7.10/1.51  res_num_sel_changes:                    0
% 7.10/1.51  res_moves_from_active_to_pass:          0
% 7.10/1.51  
% 7.10/1.51  ------ Superposition
% 7.10/1.51  
% 7.10/1.51  sup_time_total:                         0.
% 7.10/1.51  sup_time_generating:                    0.
% 7.10/1.51  sup_time_sim_full:                      0.
% 7.10/1.51  sup_time_sim_immed:                     0.
% 7.10/1.51  
% 7.10/1.51  sup_num_of_clauses:                     358
% 7.10/1.51  sup_num_in_active:                      156
% 7.10/1.51  sup_num_in_passive:                     202
% 7.10/1.51  sup_num_of_loops:                       157
% 7.10/1.51  sup_fw_superposition:                   979
% 7.10/1.51  sup_bw_superposition:                   45
% 7.10/1.51  sup_immediate_simplified:               31
% 7.10/1.51  sup_given_eliminated:                   0
% 7.10/1.51  comparisons_done:                       0
% 7.10/1.51  comparisons_avoided:                    10
% 7.10/1.51  
% 7.10/1.51  ------ Simplifications
% 7.10/1.51  
% 7.10/1.51  
% 7.10/1.51  sim_fw_subset_subsumed:                 5
% 7.10/1.51  sim_bw_subset_subsumed:                 1
% 7.10/1.51  sim_fw_subsumed:                        1
% 7.10/1.51  sim_bw_subsumed:                        2
% 7.10/1.51  sim_fw_subsumption_res:                 0
% 7.10/1.51  sim_bw_subsumption_res:                 0
% 7.10/1.51  sim_tautology_del:                      7
% 7.10/1.51  sim_eq_tautology_del:                   1
% 7.10/1.51  sim_eq_res_simp:                        0
% 7.10/1.51  sim_fw_demodulated:                     0
% 7.10/1.51  sim_bw_demodulated:                     0
% 7.10/1.51  sim_light_normalised:                   27
% 7.10/1.51  sim_joinable_taut:                      0
% 7.10/1.51  sim_joinable_simp:                      0
% 7.10/1.51  sim_ac_normalised:                      0
% 7.10/1.51  sim_smt_subsumption:                    0
% 7.10/1.51  
%------------------------------------------------------------------------------
