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
% DateTime   : Thu Dec  3 11:36:23 EST 2020

% Result     : Theorem 15.29s
% Output     : CNFRefutation 15.29s
% Verified   : 
% Statistics : Number of formulae       :  112 (1596 expanded)
%              Number of clauses        :   62 ( 316 expanded)
%              Number of leaves         :   11 ( 435 expanded)
%              Depth                    :   23
%              Number of atoms          :  456 (7675 expanded)
%              Number of equality atoms :  222 (3164 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) )
   => ( ( r2_hidden(sK3,sK4)
        | r2_hidden(sK2,sK4)
        | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3) )
      & ( ( ~ r2_hidden(sK3,sK4)
          & ~ r2_hidden(sK2,sK4) )
        | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ( r2_hidden(sK3,sK4)
      | r2_hidden(sK2,sK4)
      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3) )
    & ( ( ~ r2_hidden(sK3,sK4)
        & ~ r2_hidden(sK2,sK4) )
      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f21])).

fof(f39,plain,
    ( ~ r2_hidden(sK2,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f53,plain,
    ( ~ r2_hidden(sK2,sK4)
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) = k2_enumset1(sK2,sK2,sK2,sK3) ),
    inference(definition_unfolding,[],[f39,f42,f42])).

fof(f40,plain,
    ( ~ r2_hidden(sK3,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,
    ( ~ r2_hidden(sK3,sK4)
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) = k2_enumset1(sK2,sK2,sK2,sK3) ),
    inference(definition_unfolding,[],[f40,f42,f42])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
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

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f10])).

fof(f12,plain,(
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

fof(f13,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK2,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK2,sK4)
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) != k2_enumset1(sK2,sK2,sK2,sK3) ),
    inference(definition_unfolding,[],[f41,f42,f42])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

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
    inference(nnf_transformation,[],[f7])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).

fof(f29,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f29,f38])).

fof(f63,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f31,f38])).

fof(f59,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f48])).

fof(f60,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k2_enumset1(X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f59])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f32,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f57,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f47])).

fof(f58,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f57])).

fof(f30,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f30,f38])).

fof(f61,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f49])).

fof(f62,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f61])).

cnf(c_147,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_717,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k4_xboole_0(X3,X4))
    | X2 != X0
    | k4_xboole_0(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_1414,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X2))
    | ~ r2_hidden(sK3,X3)
    | X0 != sK3
    | k4_xboole_0(X1,X2) != X3 ),
    inference(instantiation,[status(thm)],[c_717])).

cnf(c_3434,plain,
    ( ~ r2_hidden(sK3,X0)
    | r2_hidden(sK3,k4_xboole_0(X1,X2))
    | k4_xboole_0(X1,X2) != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1414])).

cnf(c_8475,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(X0,X0,X1,sK3))
    | r2_hidden(sK3,k4_xboole_0(X2,X3))
    | k4_xboole_0(X2,X3) != k2_enumset1(X0,X0,X1,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3434])).

cnf(c_39768,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK2,sK2,sK2,sK3))
    | r2_hidden(sK3,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4))
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) != k2_enumset1(sK2,sK2,sK2,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_8475])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(sK2,sK4)
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) = k2_enumset1(sK2,sK2,sK2,sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(sK3,sK4)
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) = k2_enumset1(sK2,sK2,sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_144,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_958,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_147,c_144])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK3,sK4)
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) != k2_enumset1(sK2,sK2,sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_968,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),k2_enumset1(sK2,sK2,sK2,sK3))
    | r2_hidden(sK2,sK4)
    | r2_hidden(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_2,c_14])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1286,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK3,sK4)
    | sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)) = sK2
    | sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)) = sK3 ),
    inference(resolution,[status(thm)],[c_968,c_13])).

cnf(c_5222,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),X0)
    | ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,sK4)
    | r2_hidden(sK3,sK4)
    | sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)) = sK3 ),
    inference(resolution,[status(thm)],[c_958,c_1286])).

cnf(c_17,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) = k2_enumset1(sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) = k2_enumset1(sK2,sK2,sK2,sK3)
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_145,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_810,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_145,c_144])).

cnf(c_1350,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK3,sK4)
    | sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)) = sK3
    | sK2 = sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_1286,c_810])).

cnf(c_1351,plain,
    ( sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)) = sK3
    | sK2 = sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3))
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1350])).

cnf(c_2617,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_3090,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),k2_enumset1(sK2,sK2,sK2,sK3))
    | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),sK4)
    | r2_hidden(sK2,sK4)
    | r2_hidden(sK3,sK4)
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) = k2_enumset1(sK2,sK2,sK2,sK3) ),
    inference(resolution,[status(thm)],[c_0,c_968])).

cnf(c_613,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),k2_enumset1(sK2,sK2,sK2,sK3))
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) = k2_enumset1(sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_621,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),k2_enumset1(sK2,sK2,sK2,sK3))
    | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),sK4)
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) = k2_enumset1(sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3337,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),sK4)
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) = k2_enumset1(sK2,sK2,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3090,c_613,c_621])).

cnf(c_3353,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),sK4)
    | r2_hidden(sK2,sK4)
    | r2_hidden(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_3337,c_14])).

cnf(c_660,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),sK4)
    | X0 != sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3))
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_5880,plain,
    ( r2_hidden(X0,sK4)
    | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),sK4)
    | X0 != sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_660])).

cnf(c_5883,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),sK4)
    | r2_hidden(sK2,sK4)
    | sK2 != sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_5880])).

cnf(c_5978,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK3,sK4)
    | sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5222,c_17,c_18,c_14,c_1351,c_2617,c_3353,c_5883])).

cnf(c_6001,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK3,sK4)
    | X0 != sK3
    | sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)) = X0 ),
    inference(resolution,[status(thm)],[c_5978,c_145])).

cnf(c_783,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_788,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_145])).

cnf(c_1316,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_1372,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK3,sK4)
    | X0 != sK3
    | sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)) = X0
    | sK2 = sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_1350,c_145])).

cnf(c_2012,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK3,sK4)
    | X0 = sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3))
    | X0 != sK3
    | sK2 = sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_1372,c_810])).

cnf(c_2017,plain,
    ( X0 = sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3))
    | X0 != sK3
    | sK2 = sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3))
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2012])).

cnf(c_728,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK3,sK4)
    | sK4 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_5886,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(sK3,sK4)
    | sK4 != sK4
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_728])).

cnf(c_6215,plain,
    ( X0 != sK3
    | r2_hidden(sK3,sK4)
    | r2_hidden(sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6001,c_17,c_18,c_14,c_783,c_1316,c_2017,c_2617,c_3353,c_5880,c_5883,c_5886])).

cnf(c_6216,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK3,sK4)
    | X0 != sK3 ),
    inference(renaming,[status(thm)],[c_6215])).

cnf(c_6236,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK3,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_6216,c_5978])).

cnf(c_6297,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) = k2_enumset1(sK2,sK2,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_15,c_6236])).

cnf(c_6310,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK3))
    | r2_hidden(X1,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4))
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_6297,c_147])).

cnf(c_11,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_6723,plain,
    ( r2_hidden(X0,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4))
    | X0 != sK2 ),
    inference(resolution,[status(thm)],[c_6310,c_11])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_7738,plain,
    ( ~ r2_hidden(X0,sK4)
    | X0 != sK2 ),
    inference(resolution,[status(thm)],[c_6723,c_4])).

cnf(c_7740,plain,
    ( ~ r2_hidden(sK2,sK4)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_7738])).

cnf(c_1021,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(k2_enumset1(X2,X2,X3,X0),X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1771,plain,
    ( ~ r2_hidden(sK3,k4_xboole_0(k2_enumset1(X0,X0,X1,sK3),sK4))
    | ~ r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1021])).

cnf(c_1773,plain,
    ( ~ r2_hidden(sK3,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4))
    | ~ r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1771])).

cnf(c_10,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_748,plain,
    ( r2_hidden(sK3,k2_enumset1(X0,X0,X1,sK3)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_754,plain,
    ( r2_hidden(sK3,k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_748])).

cnf(c_12,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_24,plain,
    ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_21,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_39768,c_7740,c_6297,c_1773,c_783,c_754,c_24,c_21,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.29/2.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.29/2.50  
% 15.29/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.29/2.50  
% 15.29/2.50  ------  iProver source info
% 15.29/2.50  
% 15.29/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.29/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.29/2.50  git: non_committed_changes: false
% 15.29/2.50  git: last_make_outside_of_git: false
% 15.29/2.50  
% 15.29/2.50  ------ 
% 15.29/2.50  
% 15.29/2.50  ------ Input Options
% 15.29/2.50  
% 15.29/2.50  --out_options                           all
% 15.29/2.50  --tptp_safe_out                         true
% 15.29/2.50  --problem_path                          ""
% 15.29/2.50  --include_path                          ""
% 15.29/2.50  --clausifier                            res/vclausify_rel
% 15.29/2.50  --clausifier_options                    --mode clausify
% 15.29/2.50  --stdin                                 false
% 15.29/2.50  --stats_out                             sel
% 15.29/2.50  
% 15.29/2.50  ------ General Options
% 15.29/2.50  
% 15.29/2.50  --fof                                   false
% 15.29/2.50  --time_out_real                         604.99
% 15.29/2.50  --time_out_virtual                      -1.
% 15.29/2.50  --symbol_type_check                     false
% 15.29/2.50  --clausify_out                          false
% 15.29/2.50  --sig_cnt_out                           false
% 15.29/2.50  --trig_cnt_out                          false
% 15.29/2.50  --trig_cnt_out_tolerance                1.
% 15.29/2.50  --trig_cnt_out_sk_spl                   false
% 15.29/2.50  --abstr_cl_out                          false
% 15.29/2.50  
% 15.29/2.50  ------ Global Options
% 15.29/2.50  
% 15.29/2.50  --schedule                              none
% 15.29/2.50  --add_important_lit                     false
% 15.29/2.50  --prop_solver_per_cl                    1000
% 15.29/2.50  --min_unsat_core                        false
% 15.29/2.50  --soft_assumptions                      false
% 15.29/2.50  --soft_lemma_size                       3
% 15.29/2.50  --prop_impl_unit_size                   0
% 15.29/2.50  --prop_impl_unit                        []
% 15.29/2.50  --share_sel_clauses                     true
% 15.29/2.50  --reset_solvers                         false
% 15.29/2.50  --bc_imp_inh                            [conj_cone]
% 15.29/2.50  --conj_cone_tolerance                   3.
% 15.29/2.50  --extra_neg_conj                        none
% 15.29/2.50  --large_theory_mode                     true
% 15.29/2.50  --prolific_symb_bound                   200
% 15.29/2.50  --lt_threshold                          2000
% 15.29/2.50  --clause_weak_htbl                      true
% 15.29/2.50  --gc_record_bc_elim                     false
% 15.29/2.50  
% 15.29/2.50  ------ Preprocessing Options
% 15.29/2.50  
% 15.29/2.50  --preprocessing_flag                    true
% 15.29/2.50  --time_out_prep_mult                    0.1
% 15.29/2.50  --splitting_mode                        input
% 15.29/2.50  --splitting_grd                         true
% 15.29/2.50  --splitting_cvd                         false
% 15.29/2.50  --splitting_cvd_svl                     false
% 15.29/2.50  --splitting_nvd                         32
% 15.29/2.50  --sub_typing                            true
% 15.29/2.50  --prep_gs_sim                           false
% 15.29/2.50  --prep_unflatten                        true
% 15.29/2.50  --prep_res_sim                          true
% 15.29/2.50  --prep_upred                            true
% 15.29/2.50  --prep_sem_filter                       exhaustive
% 15.29/2.50  --prep_sem_filter_out                   false
% 15.29/2.50  --pred_elim                             false
% 15.29/2.50  --res_sim_input                         true
% 15.29/2.50  --eq_ax_congr_red                       true
% 15.29/2.50  --pure_diseq_elim                       true
% 15.29/2.50  --brand_transform                       false
% 15.29/2.50  --non_eq_to_eq                          false
% 15.29/2.50  --prep_def_merge                        true
% 15.29/2.50  --prep_def_merge_prop_impl              false
% 15.29/2.50  --prep_def_merge_mbd                    true
% 15.29/2.50  --prep_def_merge_tr_red                 false
% 15.29/2.50  --prep_def_merge_tr_cl                  false
% 15.29/2.50  --smt_preprocessing                     true
% 15.29/2.50  --smt_ac_axioms                         fast
% 15.29/2.50  --preprocessed_out                      false
% 15.29/2.50  --preprocessed_stats                    false
% 15.29/2.50  
% 15.29/2.50  ------ Abstraction refinement Options
% 15.29/2.50  
% 15.29/2.50  --abstr_ref                             []
% 15.29/2.50  --abstr_ref_prep                        false
% 15.29/2.50  --abstr_ref_until_sat                   false
% 15.29/2.50  --abstr_ref_sig_restrict                funpre
% 15.29/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.29/2.50  --abstr_ref_under                       []
% 15.29/2.50  
% 15.29/2.50  ------ SAT Options
% 15.29/2.50  
% 15.29/2.50  --sat_mode                              false
% 15.29/2.50  --sat_fm_restart_options                ""
% 15.29/2.50  --sat_gr_def                            false
% 15.29/2.50  --sat_epr_types                         true
% 15.29/2.50  --sat_non_cyclic_types                  false
% 15.29/2.50  --sat_finite_models                     false
% 15.29/2.50  --sat_fm_lemmas                         false
% 15.29/2.50  --sat_fm_prep                           false
% 15.29/2.50  --sat_fm_uc_incr                        true
% 15.29/2.50  --sat_out_model                         small
% 15.29/2.50  --sat_out_clauses                       false
% 15.29/2.50  
% 15.29/2.50  ------ QBF Options
% 15.29/2.50  
% 15.29/2.50  --qbf_mode                              false
% 15.29/2.50  --qbf_elim_univ                         false
% 15.29/2.50  --qbf_dom_inst                          none
% 15.29/2.50  --qbf_dom_pre_inst                      false
% 15.29/2.50  --qbf_sk_in                             false
% 15.29/2.50  --qbf_pred_elim                         true
% 15.29/2.50  --qbf_split                             512
% 15.29/2.50  
% 15.29/2.50  ------ BMC1 Options
% 15.29/2.50  
% 15.29/2.50  --bmc1_incremental                      false
% 15.29/2.50  --bmc1_axioms                           reachable_all
% 15.29/2.50  --bmc1_min_bound                        0
% 15.29/2.50  --bmc1_max_bound                        -1
% 15.29/2.50  --bmc1_max_bound_default                -1
% 15.29/2.50  --bmc1_symbol_reachability              true
% 15.29/2.50  --bmc1_property_lemmas                  false
% 15.29/2.50  --bmc1_k_induction                      false
% 15.29/2.50  --bmc1_non_equiv_states                 false
% 15.29/2.50  --bmc1_deadlock                         false
% 15.29/2.50  --bmc1_ucm                              false
% 15.29/2.50  --bmc1_add_unsat_core                   none
% 15.29/2.50  --bmc1_unsat_core_children              false
% 15.29/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.29/2.50  --bmc1_out_stat                         full
% 15.29/2.50  --bmc1_ground_init                      false
% 15.29/2.50  --bmc1_pre_inst_next_state              false
% 15.29/2.50  --bmc1_pre_inst_state                   false
% 15.29/2.50  --bmc1_pre_inst_reach_state             false
% 15.29/2.50  --bmc1_out_unsat_core                   false
% 15.29/2.50  --bmc1_aig_witness_out                  false
% 15.29/2.50  --bmc1_verbose                          false
% 15.29/2.50  --bmc1_dump_clauses_tptp                false
% 15.29/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.29/2.50  --bmc1_dump_file                        -
% 15.29/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.29/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.29/2.50  --bmc1_ucm_extend_mode                  1
% 15.29/2.50  --bmc1_ucm_init_mode                    2
% 15.29/2.50  --bmc1_ucm_cone_mode                    none
% 15.29/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.29/2.50  --bmc1_ucm_relax_model                  4
% 15.29/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.29/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.29/2.50  --bmc1_ucm_layered_model                none
% 15.29/2.50  --bmc1_ucm_max_lemma_size               10
% 15.29/2.50  
% 15.29/2.50  ------ AIG Options
% 15.29/2.50  
% 15.29/2.50  --aig_mode                              false
% 15.29/2.50  
% 15.29/2.50  ------ Instantiation Options
% 15.29/2.50  
% 15.29/2.50  --instantiation_flag                    true
% 15.29/2.50  --inst_sos_flag                         false
% 15.29/2.50  --inst_sos_phase                        true
% 15.29/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.29/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.29/2.50  --inst_lit_sel_side                     num_symb
% 15.29/2.50  --inst_solver_per_active                1400
% 15.29/2.50  --inst_solver_calls_frac                1.
% 15.29/2.50  --inst_passive_queue_type               priority_queues
% 15.29/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.29/2.50  --inst_passive_queues_freq              [25;2]
% 15.29/2.50  --inst_dismatching                      true
% 15.29/2.50  --inst_eager_unprocessed_to_passive     true
% 15.29/2.50  --inst_prop_sim_given                   true
% 15.29/2.50  --inst_prop_sim_new                     false
% 15.29/2.50  --inst_subs_new                         false
% 15.29/2.50  --inst_eq_res_simp                      false
% 15.29/2.50  --inst_subs_given                       false
% 15.29/2.50  --inst_orphan_elimination               true
% 15.29/2.50  --inst_learning_loop_flag               true
% 15.29/2.50  --inst_learning_start                   3000
% 15.29/2.50  --inst_learning_factor                  2
% 15.29/2.50  --inst_start_prop_sim_after_learn       3
% 15.29/2.50  --inst_sel_renew                        solver
% 15.29/2.50  --inst_lit_activity_flag                true
% 15.29/2.50  --inst_restr_to_given                   false
% 15.29/2.50  --inst_activity_threshold               500
% 15.29/2.50  --inst_out_proof                        true
% 15.29/2.50  
% 15.29/2.50  ------ Resolution Options
% 15.29/2.50  
% 15.29/2.50  --resolution_flag                       true
% 15.29/2.50  --res_lit_sel                           adaptive
% 15.29/2.50  --res_lit_sel_side                      none
% 15.29/2.50  --res_ordering                          kbo
% 15.29/2.50  --res_to_prop_solver                    active
% 15.29/2.50  --res_prop_simpl_new                    false
% 15.29/2.50  --res_prop_simpl_given                  true
% 15.29/2.50  --res_passive_queue_type                priority_queues
% 15.29/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.29/2.50  --res_passive_queues_freq               [15;5]
% 15.29/2.50  --res_forward_subs                      full
% 15.29/2.50  --res_backward_subs                     full
% 15.29/2.50  --res_forward_subs_resolution           true
% 15.29/2.50  --res_backward_subs_resolution          true
% 15.29/2.50  --res_orphan_elimination                true
% 15.29/2.50  --res_time_limit                        2.
% 15.29/2.50  --res_out_proof                         true
% 15.29/2.50  
% 15.29/2.50  ------ Superposition Options
% 15.29/2.50  
% 15.29/2.50  --superposition_flag                    true
% 15.29/2.50  --sup_passive_queue_type                priority_queues
% 15.29/2.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.29/2.50  --sup_passive_queues_freq               [1;4]
% 15.29/2.50  --demod_completeness_check              fast
% 15.29/2.50  --demod_use_ground                      true
% 15.29/2.50  --sup_to_prop_solver                    passive
% 15.29/2.50  --sup_prop_simpl_new                    true
% 15.29/2.50  --sup_prop_simpl_given                  true
% 15.29/2.50  --sup_fun_splitting                     false
% 15.29/2.50  --sup_smt_interval                      50000
% 15.29/2.50  
% 15.29/2.50  ------ Superposition Simplification Setup
% 15.29/2.50  
% 15.29/2.50  --sup_indices_passive                   []
% 15.29/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.29/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.29/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.29/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.29/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.29/2.50  --sup_full_bw                           [BwDemod]
% 15.29/2.50  --sup_immed_triv                        [TrivRules]
% 15.29/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.29/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.29/2.50  --sup_immed_bw_main                     []
% 15.29/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.29/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.29/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.29/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.29/2.50  
% 15.29/2.50  ------ Combination Options
% 15.29/2.50  
% 15.29/2.50  --comb_res_mult                         3
% 15.29/2.50  --comb_sup_mult                         2
% 15.29/2.50  --comb_inst_mult                        10
% 15.29/2.50  
% 15.29/2.50  ------ Debug Options
% 15.29/2.50  
% 15.29/2.50  --dbg_backtrace                         false
% 15.29/2.50  --dbg_dump_prop_clauses                 false
% 15.29/2.50  --dbg_dump_prop_clauses_file            -
% 15.29/2.50  --dbg_out_stat                          false
% 15.29/2.50  ------ Parsing...
% 15.29/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.29/2.50  
% 15.29/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.29/2.50  
% 15.29/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.29/2.50  
% 15.29/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.29/2.50  ------ Proving...
% 15.29/2.50  ------ Problem Properties 
% 15.29/2.50  
% 15.29/2.50  
% 15.29/2.50  clauses                                 17
% 15.29/2.50  conjectures                             3
% 15.29/2.50  EPR                                     0
% 15.29/2.50  Horn                                    10
% 15.29/2.50  unary                                   3
% 15.29/2.50  binary                                  4
% 15.29/2.50  lits                                    45
% 15.29/2.50  lits eq                                 19
% 15.29/2.50  fd_pure                                 0
% 15.29/2.50  fd_pseudo                               0
% 15.29/2.50  fd_cond                                 0
% 15.29/2.50  fd_pseudo_cond                          7
% 15.29/2.50  AC symbols                              0
% 15.29/2.50  
% 15.29/2.50  ------ Input Options Time Limit: Unbounded
% 15.29/2.50  
% 15.29/2.50  
% 15.29/2.50  ------ 
% 15.29/2.50  Current options:
% 15.29/2.50  ------ 
% 15.29/2.50  
% 15.29/2.50  ------ Input Options
% 15.29/2.50  
% 15.29/2.50  --out_options                           all
% 15.29/2.50  --tptp_safe_out                         true
% 15.29/2.50  --problem_path                          ""
% 15.29/2.50  --include_path                          ""
% 15.29/2.50  --clausifier                            res/vclausify_rel
% 15.29/2.50  --clausifier_options                    --mode clausify
% 15.29/2.50  --stdin                                 false
% 15.29/2.50  --stats_out                             sel
% 15.29/2.50  
% 15.29/2.50  ------ General Options
% 15.29/2.50  
% 15.29/2.50  --fof                                   false
% 15.29/2.50  --time_out_real                         604.99
% 15.29/2.50  --time_out_virtual                      -1.
% 15.29/2.50  --symbol_type_check                     false
% 15.29/2.50  --clausify_out                          false
% 15.29/2.50  --sig_cnt_out                           false
% 15.29/2.50  --trig_cnt_out                          false
% 15.29/2.50  --trig_cnt_out_tolerance                1.
% 15.29/2.50  --trig_cnt_out_sk_spl                   false
% 15.29/2.50  --abstr_cl_out                          false
% 15.29/2.50  
% 15.29/2.50  ------ Global Options
% 15.29/2.50  
% 15.29/2.50  --schedule                              none
% 15.29/2.50  --add_important_lit                     false
% 15.29/2.50  --prop_solver_per_cl                    1000
% 15.29/2.50  --min_unsat_core                        false
% 15.29/2.50  --soft_assumptions                      false
% 15.29/2.50  --soft_lemma_size                       3
% 15.29/2.50  --prop_impl_unit_size                   0
% 15.29/2.50  --prop_impl_unit                        []
% 15.29/2.50  --share_sel_clauses                     true
% 15.29/2.50  --reset_solvers                         false
% 15.29/2.50  --bc_imp_inh                            [conj_cone]
% 15.29/2.50  --conj_cone_tolerance                   3.
% 15.29/2.50  --extra_neg_conj                        none
% 15.29/2.50  --large_theory_mode                     true
% 15.29/2.50  --prolific_symb_bound                   200
% 15.29/2.50  --lt_threshold                          2000
% 15.29/2.50  --clause_weak_htbl                      true
% 15.29/2.50  --gc_record_bc_elim                     false
% 15.29/2.50  
% 15.29/2.50  ------ Preprocessing Options
% 15.29/2.50  
% 15.29/2.50  --preprocessing_flag                    true
% 15.29/2.50  --time_out_prep_mult                    0.1
% 15.29/2.50  --splitting_mode                        input
% 15.29/2.50  --splitting_grd                         true
% 15.29/2.50  --splitting_cvd                         false
% 15.29/2.50  --splitting_cvd_svl                     false
% 15.29/2.50  --splitting_nvd                         32
% 15.29/2.50  --sub_typing                            true
% 15.29/2.50  --prep_gs_sim                           false
% 15.29/2.50  --prep_unflatten                        true
% 15.29/2.50  --prep_res_sim                          true
% 15.29/2.50  --prep_upred                            true
% 15.29/2.50  --prep_sem_filter                       exhaustive
% 15.29/2.50  --prep_sem_filter_out                   false
% 15.29/2.50  --pred_elim                             false
% 15.29/2.50  --res_sim_input                         true
% 15.29/2.50  --eq_ax_congr_red                       true
% 15.29/2.50  --pure_diseq_elim                       true
% 15.29/2.50  --brand_transform                       false
% 15.29/2.50  --non_eq_to_eq                          false
% 15.29/2.50  --prep_def_merge                        true
% 15.29/2.50  --prep_def_merge_prop_impl              false
% 15.29/2.50  --prep_def_merge_mbd                    true
% 15.29/2.50  --prep_def_merge_tr_red                 false
% 15.29/2.50  --prep_def_merge_tr_cl                  false
% 15.29/2.50  --smt_preprocessing                     true
% 15.29/2.50  --smt_ac_axioms                         fast
% 15.29/2.50  --preprocessed_out                      false
% 15.29/2.50  --preprocessed_stats                    false
% 15.29/2.50  
% 15.29/2.50  ------ Abstraction refinement Options
% 15.29/2.50  
% 15.29/2.50  --abstr_ref                             []
% 15.29/2.50  --abstr_ref_prep                        false
% 15.29/2.50  --abstr_ref_until_sat                   false
% 15.29/2.50  --abstr_ref_sig_restrict                funpre
% 15.29/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.29/2.50  --abstr_ref_under                       []
% 15.29/2.50  
% 15.29/2.50  ------ SAT Options
% 15.29/2.50  
% 15.29/2.50  --sat_mode                              false
% 15.29/2.50  --sat_fm_restart_options                ""
% 15.29/2.50  --sat_gr_def                            false
% 15.29/2.50  --sat_epr_types                         true
% 15.29/2.50  --sat_non_cyclic_types                  false
% 15.29/2.50  --sat_finite_models                     false
% 15.29/2.50  --sat_fm_lemmas                         false
% 15.29/2.50  --sat_fm_prep                           false
% 15.29/2.50  --sat_fm_uc_incr                        true
% 15.29/2.50  --sat_out_model                         small
% 15.29/2.50  --sat_out_clauses                       false
% 15.29/2.50  
% 15.29/2.50  ------ QBF Options
% 15.29/2.50  
% 15.29/2.50  --qbf_mode                              false
% 15.29/2.50  --qbf_elim_univ                         false
% 15.29/2.50  --qbf_dom_inst                          none
% 15.29/2.50  --qbf_dom_pre_inst                      false
% 15.29/2.50  --qbf_sk_in                             false
% 15.29/2.50  --qbf_pred_elim                         true
% 15.29/2.50  --qbf_split                             512
% 15.29/2.50  
% 15.29/2.50  ------ BMC1 Options
% 15.29/2.50  
% 15.29/2.50  --bmc1_incremental                      false
% 15.29/2.50  --bmc1_axioms                           reachable_all
% 15.29/2.50  --bmc1_min_bound                        0
% 15.29/2.50  --bmc1_max_bound                        -1
% 15.29/2.50  --bmc1_max_bound_default                -1
% 15.29/2.50  --bmc1_symbol_reachability              true
% 15.29/2.50  --bmc1_property_lemmas                  false
% 15.29/2.50  --bmc1_k_induction                      false
% 15.29/2.50  --bmc1_non_equiv_states                 false
% 15.29/2.50  --bmc1_deadlock                         false
% 15.29/2.50  --bmc1_ucm                              false
% 15.29/2.50  --bmc1_add_unsat_core                   none
% 15.29/2.50  --bmc1_unsat_core_children              false
% 15.29/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.29/2.50  --bmc1_out_stat                         full
% 15.29/2.50  --bmc1_ground_init                      false
% 15.29/2.50  --bmc1_pre_inst_next_state              false
% 15.29/2.50  --bmc1_pre_inst_state                   false
% 15.29/2.50  --bmc1_pre_inst_reach_state             false
% 15.29/2.50  --bmc1_out_unsat_core                   false
% 15.29/2.50  --bmc1_aig_witness_out                  false
% 15.29/2.50  --bmc1_verbose                          false
% 15.29/2.50  --bmc1_dump_clauses_tptp                false
% 15.29/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.29/2.50  --bmc1_dump_file                        -
% 15.29/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.29/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.29/2.50  --bmc1_ucm_extend_mode                  1
% 15.29/2.50  --bmc1_ucm_init_mode                    2
% 15.29/2.50  --bmc1_ucm_cone_mode                    none
% 15.29/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.29/2.50  --bmc1_ucm_relax_model                  4
% 15.29/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.29/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.29/2.50  --bmc1_ucm_layered_model                none
% 15.29/2.50  --bmc1_ucm_max_lemma_size               10
% 15.29/2.50  
% 15.29/2.50  ------ AIG Options
% 15.29/2.50  
% 15.29/2.50  --aig_mode                              false
% 15.29/2.50  
% 15.29/2.50  ------ Instantiation Options
% 15.29/2.50  
% 15.29/2.50  --instantiation_flag                    true
% 15.29/2.50  --inst_sos_flag                         false
% 15.29/2.50  --inst_sos_phase                        true
% 15.29/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.29/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.29/2.50  --inst_lit_sel_side                     num_symb
% 15.29/2.50  --inst_solver_per_active                1400
% 15.29/2.50  --inst_solver_calls_frac                1.
% 15.29/2.50  --inst_passive_queue_type               priority_queues
% 15.29/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.29/2.50  --inst_passive_queues_freq              [25;2]
% 15.29/2.50  --inst_dismatching                      true
% 15.29/2.50  --inst_eager_unprocessed_to_passive     true
% 15.29/2.50  --inst_prop_sim_given                   true
% 15.29/2.50  --inst_prop_sim_new                     false
% 15.29/2.50  --inst_subs_new                         false
% 15.29/2.50  --inst_eq_res_simp                      false
% 15.29/2.50  --inst_subs_given                       false
% 15.29/2.50  --inst_orphan_elimination               true
% 15.29/2.50  --inst_learning_loop_flag               true
% 15.29/2.50  --inst_learning_start                   3000
% 15.29/2.50  --inst_learning_factor                  2
% 15.29/2.50  --inst_start_prop_sim_after_learn       3
% 15.29/2.50  --inst_sel_renew                        solver
% 15.29/2.50  --inst_lit_activity_flag                true
% 15.29/2.50  --inst_restr_to_given                   false
% 15.29/2.50  --inst_activity_threshold               500
% 15.29/2.50  --inst_out_proof                        true
% 15.29/2.50  
% 15.29/2.50  ------ Resolution Options
% 15.29/2.50  
% 15.29/2.50  --resolution_flag                       true
% 15.29/2.50  --res_lit_sel                           adaptive
% 15.29/2.50  --res_lit_sel_side                      none
% 15.29/2.50  --res_ordering                          kbo
% 15.29/2.50  --res_to_prop_solver                    active
% 15.29/2.50  --res_prop_simpl_new                    false
% 15.29/2.50  --res_prop_simpl_given                  true
% 15.29/2.50  --res_passive_queue_type                priority_queues
% 15.29/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.29/2.50  --res_passive_queues_freq               [15;5]
% 15.29/2.50  --res_forward_subs                      full
% 15.29/2.50  --res_backward_subs                     full
% 15.29/2.50  --res_forward_subs_resolution           true
% 15.29/2.50  --res_backward_subs_resolution          true
% 15.29/2.50  --res_orphan_elimination                true
% 15.29/2.50  --res_time_limit                        2.
% 15.29/2.50  --res_out_proof                         true
% 15.29/2.50  
% 15.29/2.50  ------ Superposition Options
% 15.29/2.50  
% 15.29/2.50  --superposition_flag                    true
% 15.29/2.50  --sup_passive_queue_type                priority_queues
% 15.29/2.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.29/2.50  --sup_passive_queues_freq               [1;4]
% 15.29/2.50  --demod_completeness_check              fast
% 15.29/2.50  --demod_use_ground                      true
% 15.29/2.50  --sup_to_prop_solver                    passive
% 15.29/2.50  --sup_prop_simpl_new                    true
% 15.29/2.50  --sup_prop_simpl_given                  true
% 15.29/2.50  --sup_fun_splitting                     false
% 15.29/2.50  --sup_smt_interval                      50000
% 15.29/2.50  
% 15.29/2.50  ------ Superposition Simplification Setup
% 15.29/2.50  
% 15.29/2.50  --sup_indices_passive                   []
% 15.29/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.29/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.29/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.29/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.29/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.29/2.50  --sup_full_bw                           [BwDemod]
% 15.29/2.50  --sup_immed_triv                        [TrivRules]
% 15.29/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.29/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.29/2.50  --sup_immed_bw_main                     []
% 15.29/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.29/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.29/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.29/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.29/2.50  
% 15.29/2.50  ------ Combination Options
% 15.29/2.50  
% 15.29/2.50  --comb_res_mult                         3
% 15.29/2.50  --comb_sup_mult                         2
% 15.29/2.50  --comb_inst_mult                        10
% 15.29/2.50  
% 15.29/2.50  ------ Debug Options
% 15.29/2.50  
% 15.29/2.50  --dbg_backtrace                         false
% 15.29/2.50  --dbg_dump_prop_clauses                 false
% 15.29/2.50  --dbg_dump_prop_clauses_file            -
% 15.29/2.50  --dbg_out_stat                          false
% 15.29/2.50  
% 15.29/2.50  
% 15.29/2.50  
% 15.29/2.50  
% 15.29/2.50  ------ Proving...
% 15.29/2.50  
% 15.29/2.50  
% 15.29/2.50  % SZS status Theorem for theBenchmark.p
% 15.29/2.50  
% 15.29/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.29/2.50  
% 15.29/2.50  fof(f5,conjecture,(
% 15.29/2.50    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 15.29/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.29/2.50  
% 15.29/2.50  fof(f6,negated_conjecture,(
% 15.29/2.50    ~! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 15.29/2.50    inference(negated_conjecture,[],[f5])).
% 15.29/2.50  
% 15.29/2.50  fof(f8,plain,(
% 15.29/2.50    ? [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 15.29/2.50    inference(ennf_transformation,[],[f6])).
% 15.29/2.50  
% 15.29/2.50  fof(f19,plain,(
% 15.29/2.50    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)))),
% 15.29/2.50    inference(nnf_transformation,[],[f8])).
% 15.29/2.50  
% 15.29/2.50  fof(f20,plain,(
% 15.29/2.50    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)))),
% 15.29/2.50    inference(flattening,[],[f19])).
% 15.29/2.50  
% 15.29/2.50  fof(f21,plain,(
% 15.29/2.50    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1))) => ((r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3)) & ((~r2_hidden(sK3,sK4) & ~r2_hidden(sK2,sK4)) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3)))),
% 15.29/2.50    introduced(choice_axiom,[])).
% 15.29/2.50  
% 15.29/2.50  fof(f22,plain,(
% 15.29/2.50    (r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3)) & ((~r2_hidden(sK3,sK4) & ~r2_hidden(sK2,sK4)) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3))),
% 15.29/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f21])).
% 15.29/2.50  
% 15.29/2.50  fof(f39,plain,(
% 15.29/2.50    ~r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3)),
% 15.29/2.50    inference(cnf_transformation,[],[f22])).
% 15.29/2.50  
% 15.29/2.50  fof(f3,axiom,(
% 15.29/2.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 15.29/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.29/2.50  
% 15.29/2.50  fof(f37,plain,(
% 15.29/2.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.29/2.50    inference(cnf_transformation,[],[f3])).
% 15.29/2.50  
% 15.29/2.50  fof(f4,axiom,(
% 15.29/2.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.29/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.29/2.50  
% 15.29/2.50  fof(f38,plain,(
% 15.29/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.29/2.50    inference(cnf_transformation,[],[f4])).
% 15.29/2.50  
% 15.29/2.50  fof(f42,plain,(
% 15.29/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 15.29/2.50    inference(definition_unfolding,[],[f37,f38])).
% 15.29/2.50  
% 15.29/2.50  fof(f53,plain,(
% 15.29/2.50    ~r2_hidden(sK2,sK4) | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) = k2_enumset1(sK2,sK2,sK2,sK3)),
% 15.29/2.50    inference(definition_unfolding,[],[f39,f42,f42])).
% 15.29/2.50  
% 15.29/2.50  fof(f40,plain,(
% 15.29/2.50    ~r2_hidden(sK3,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3)),
% 15.29/2.50    inference(cnf_transformation,[],[f22])).
% 15.29/2.50  
% 15.29/2.50  fof(f52,plain,(
% 15.29/2.50    ~r2_hidden(sK3,sK4) | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) = k2_enumset1(sK2,sK2,sK2,sK3)),
% 15.29/2.50    inference(definition_unfolding,[],[f40,f42,f42])).
% 15.29/2.50  
% 15.29/2.50  fof(f1,axiom,(
% 15.29/2.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 15.29/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.29/2.50  
% 15.29/2.50  fof(f9,plain,(
% 15.29/2.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.29/2.50    inference(nnf_transformation,[],[f1])).
% 15.29/2.50  
% 15.29/2.50  fof(f10,plain,(
% 15.29/2.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.29/2.50    inference(flattening,[],[f9])).
% 15.29/2.50  
% 15.29/2.50  fof(f11,plain,(
% 15.29/2.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.29/2.50    inference(rectify,[],[f10])).
% 15.29/2.50  
% 15.29/2.50  fof(f12,plain,(
% 15.29/2.50    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 15.29/2.50    introduced(choice_axiom,[])).
% 15.29/2.50  
% 15.29/2.50  fof(f13,plain,(
% 15.29/2.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.29/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).
% 15.29/2.50  
% 15.29/2.50  fof(f26,plain,(
% 15.29/2.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 15.29/2.50    inference(cnf_transformation,[],[f13])).
% 15.29/2.50  
% 15.29/2.50  fof(f41,plain,(
% 15.29/2.50    r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3)),
% 15.29/2.50    inference(cnf_transformation,[],[f22])).
% 15.29/2.50  
% 15.29/2.50  fof(f51,plain,(
% 15.29/2.50    r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) != k2_enumset1(sK2,sK2,sK2,sK3)),
% 15.29/2.50    inference(definition_unfolding,[],[f41,f42,f42])).
% 15.29/2.50  
% 15.29/2.50  fof(f2,axiom,(
% 15.29/2.50    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 15.29/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.29/2.50  
% 15.29/2.50  fof(f7,plain,(
% 15.29/2.50    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 15.29/2.50    inference(ennf_transformation,[],[f2])).
% 15.29/2.50  
% 15.29/2.50  fof(f14,plain,(
% 15.29/2.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.29/2.50    inference(nnf_transformation,[],[f7])).
% 15.29/2.50  
% 15.29/2.50  fof(f15,plain,(
% 15.29/2.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.29/2.50    inference(flattening,[],[f14])).
% 15.29/2.50  
% 15.29/2.50  fof(f16,plain,(
% 15.29/2.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.29/2.50    inference(rectify,[],[f15])).
% 15.29/2.50  
% 15.29/2.50  fof(f17,plain,(
% 15.29/2.50    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 15.29/2.50    introduced(choice_axiom,[])).
% 15.29/2.50  
% 15.29/2.50  fof(f18,plain,(
% 15.29/2.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.29/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).
% 15.29/2.50  
% 15.29/2.50  fof(f29,plain,(
% 15.29/2.50    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 15.29/2.50    inference(cnf_transformation,[],[f18])).
% 15.29/2.50  
% 15.29/2.50  fof(f50,plain,(
% 15.29/2.50    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 15.29/2.50    inference(definition_unfolding,[],[f29,f38])).
% 15.29/2.50  
% 15.29/2.50  fof(f63,plain,(
% 15.29/2.50    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 15.29/2.50    inference(equality_resolution,[],[f50])).
% 15.29/2.50  
% 15.29/2.50  fof(f28,plain,(
% 15.29/2.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 15.29/2.50    inference(cnf_transformation,[],[f13])).
% 15.29/2.50  
% 15.29/2.50  fof(f31,plain,(
% 15.29/2.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 15.29/2.50    inference(cnf_transformation,[],[f18])).
% 15.29/2.50  
% 15.29/2.50  fof(f48,plain,(
% 15.29/2.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 15.29/2.50    inference(definition_unfolding,[],[f31,f38])).
% 15.29/2.50  
% 15.29/2.50  fof(f59,plain,(
% 15.29/2.50    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X5,X2) != X3) )),
% 15.29/2.50    inference(equality_resolution,[],[f48])).
% 15.29/2.50  
% 15.29/2.50  fof(f60,plain,(
% 15.29/2.50    ( ! [X2,X0,X5] : (r2_hidden(X5,k2_enumset1(X0,X0,X5,X2))) )),
% 15.29/2.50    inference(equality_resolution,[],[f59])).
% 15.29/2.50  
% 15.29/2.50  fof(f24,plain,(
% 15.29/2.50    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 15.29/2.50    inference(cnf_transformation,[],[f13])).
% 15.29/2.50  
% 15.29/2.50  fof(f55,plain,(
% 15.29/2.50    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 15.29/2.50    inference(equality_resolution,[],[f24])).
% 15.29/2.50  
% 15.29/2.50  fof(f32,plain,(
% 15.29/2.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 15.29/2.50    inference(cnf_transformation,[],[f18])).
% 15.29/2.50  
% 15.29/2.50  fof(f47,plain,(
% 15.29/2.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 15.29/2.50    inference(definition_unfolding,[],[f32,f38])).
% 15.29/2.50  
% 15.29/2.50  fof(f57,plain,(
% 15.29/2.50    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 15.29/2.50    inference(equality_resolution,[],[f47])).
% 15.29/2.50  
% 15.29/2.50  fof(f58,plain,(
% 15.29/2.50    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 15.29/2.50    inference(equality_resolution,[],[f57])).
% 15.29/2.50  
% 15.29/2.50  fof(f30,plain,(
% 15.29/2.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 15.29/2.50    inference(cnf_transformation,[],[f18])).
% 15.29/2.50  
% 15.29/2.50  fof(f49,plain,(
% 15.29/2.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 15.29/2.50    inference(definition_unfolding,[],[f30,f38])).
% 15.29/2.50  
% 15.29/2.50  fof(f61,plain,(
% 15.29/2.50    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 15.29/2.50    inference(equality_resolution,[],[f49])).
% 15.29/2.50  
% 15.29/2.50  fof(f62,plain,(
% 15.29/2.50    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 15.29/2.50    inference(equality_resolution,[],[f61])).
% 15.29/2.50  
% 15.29/2.50  cnf(c_147,plain,
% 15.29/2.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.29/2.50      theory(equality) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_717,plain,
% 15.29/2.50      ( ~ r2_hidden(X0,X1)
% 15.29/2.50      | r2_hidden(X2,k4_xboole_0(X3,X4))
% 15.29/2.50      | X2 != X0
% 15.29/2.50      | k4_xboole_0(X3,X4) != X1 ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_147]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_1414,plain,
% 15.29/2.50      ( r2_hidden(X0,k4_xboole_0(X1,X2))
% 15.29/2.50      | ~ r2_hidden(sK3,X3)
% 15.29/2.50      | X0 != sK3
% 15.29/2.50      | k4_xboole_0(X1,X2) != X3 ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_717]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_3434,plain,
% 15.29/2.50      ( ~ r2_hidden(sK3,X0)
% 15.29/2.50      | r2_hidden(sK3,k4_xboole_0(X1,X2))
% 15.29/2.50      | k4_xboole_0(X1,X2) != X0
% 15.29/2.50      | sK3 != sK3 ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_1414]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_8475,plain,
% 15.29/2.50      ( ~ r2_hidden(sK3,k2_enumset1(X0,X0,X1,sK3))
% 15.29/2.50      | r2_hidden(sK3,k4_xboole_0(X2,X3))
% 15.29/2.50      | k4_xboole_0(X2,X3) != k2_enumset1(X0,X0,X1,sK3)
% 15.29/2.50      | sK3 != sK3 ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_3434]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_39768,plain,
% 15.29/2.50      ( ~ r2_hidden(sK3,k2_enumset1(sK2,sK2,sK2,sK3))
% 15.29/2.50      | r2_hidden(sK3,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4))
% 15.29/2.50      | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) != k2_enumset1(sK2,sK2,sK2,sK3)
% 15.29/2.50      | sK3 != sK3 ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_8475]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_16,negated_conjecture,
% 15.29/2.50      ( ~ r2_hidden(sK2,sK4)
% 15.29/2.50      | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) = k2_enumset1(sK2,sK2,sK2,sK3) ),
% 15.29/2.50      inference(cnf_transformation,[],[f53]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_15,negated_conjecture,
% 15.29/2.50      ( ~ r2_hidden(sK3,sK4)
% 15.29/2.50      | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) = k2_enumset1(sK2,sK2,sK2,sK3) ),
% 15.29/2.50      inference(cnf_transformation,[],[f52]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_144,plain,( X0 = X0 ),theory(equality) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_958,plain,
% 15.29/2.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 15.29/2.50      inference(resolution,[status(thm)],[c_147,c_144]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_2,plain,
% 15.29/2.50      ( r2_hidden(sK0(X0,X1,X2),X0)
% 15.29/2.50      | r2_hidden(sK0(X0,X1,X2),X2)
% 15.29/2.50      | k4_xboole_0(X0,X1) = X2 ),
% 15.29/2.50      inference(cnf_transformation,[],[f26]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_14,negated_conjecture,
% 15.29/2.50      ( r2_hidden(sK2,sK4)
% 15.29/2.50      | r2_hidden(sK3,sK4)
% 15.29/2.50      | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) != k2_enumset1(sK2,sK2,sK2,sK3) ),
% 15.29/2.50      inference(cnf_transformation,[],[f51]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_968,plain,
% 15.29/2.50      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),k2_enumset1(sK2,sK2,sK2,sK3))
% 15.29/2.50      | r2_hidden(sK2,sK4)
% 15.29/2.50      | r2_hidden(sK3,sK4) ),
% 15.29/2.50      inference(resolution,[status(thm)],[c_2,c_14]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_13,plain,
% 15.29/2.50      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 15.29/2.50      | X0 = X1
% 15.29/2.50      | X0 = X2
% 15.29/2.50      | X0 = X3 ),
% 15.29/2.50      inference(cnf_transformation,[],[f63]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_1286,plain,
% 15.29/2.50      ( r2_hidden(sK2,sK4)
% 15.29/2.50      | r2_hidden(sK3,sK4)
% 15.29/2.50      | sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)) = sK2
% 15.29/2.50      | sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)) = sK3 ),
% 15.29/2.50      inference(resolution,[status(thm)],[c_968,c_13]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_5222,plain,
% 15.29/2.50      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),X0)
% 15.29/2.50      | ~ r2_hidden(sK2,X0)
% 15.29/2.50      | r2_hidden(sK2,sK4)
% 15.29/2.50      | r2_hidden(sK3,sK4)
% 15.29/2.50      | sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)) = sK3 ),
% 15.29/2.50      inference(resolution,[status(thm)],[c_958,c_1286]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_17,plain,
% 15.29/2.50      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) = k2_enumset1(sK2,sK2,sK2,sK3)
% 15.29/2.50      | r2_hidden(sK2,sK4) != iProver_top ),
% 15.29/2.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_18,plain,
% 15.29/2.50      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) = k2_enumset1(sK2,sK2,sK2,sK3)
% 15.29/2.50      | r2_hidden(sK3,sK4) != iProver_top ),
% 15.29/2.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_145,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_810,plain,
% 15.29/2.50      ( X0 != X1 | X1 = X0 ),
% 15.29/2.50      inference(resolution,[status(thm)],[c_145,c_144]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_1350,plain,
% 15.29/2.50      ( r2_hidden(sK2,sK4)
% 15.29/2.50      | r2_hidden(sK3,sK4)
% 15.29/2.50      | sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)) = sK3
% 15.29/2.50      | sK2 = sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)) ),
% 15.29/2.50      inference(resolution,[status(thm)],[c_1286,c_810]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_1351,plain,
% 15.29/2.50      ( sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)) = sK3
% 15.29/2.50      | sK2 = sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3))
% 15.29/2.50      | r2_hidden(sK2,sK4) = iProver_top
% 15.29/2.50      | r2_hidden(sK3,sK4) = iProver_top ),
% 15.29/2.50      inference(predicate_to_equality,[status(thm)],[c_1350]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_2617,plain,
% 15.29/2.50      ( sK4 = sK4 ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_144]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_0,plain,
% 15.29/2.50      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 15.29/2.50      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 15.29/2.50      | r2_hidden(sK0(X0,X1,X2),X1)
% 15.29/2.50      | k4_xboole_0(X0,X1) = X2 ),
% 15.29/2.50      inference(cnf_transformation,[],[f28]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_3090,plain,
% 15.29/2.50      ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),k2_enumset1(sK2,sK2,sK2,sK3))
% 15.29/2.50      | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),sK4)
% 15.29/2.50      | r2_hidden(sK2,sK4)
% 15.29/2.50      | r2_hidden(sK3,sK4)
% 15.29/2.50      | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) = k2_enumset1(sK2,sK2,sK2,sK3) ),
% 15.29/2.50      inference(resolution,[status(thm)],[c_0,c_968]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_613,plain,
% 15.29/2.50      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),k2_enumset1(sK2,sK2,sK2,sK3))
% 15.29/2.50      | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) = k2_enumset1(sK2,sK2,sK2,sK3) ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_2]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_621,plain,
% 15.29/2.50      ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),k2_enumset1(sK2,sK2,sK2,sK3))
% 15.29/2.50      | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),sK4)
% 15.29/2.50      | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) = k2_enumset1(sK2,sK2,sK2,sK3) ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_0]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_3337,plain,
% 15.29/2.50      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),sK4)
% 15.29/2.50      | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) = k2_enumset1(sK2,sK2,sK2,sK3) ),
% 15.29/2.50      inference(global_propositional_subsumption,
% 15.29/2.50                [status(thm)],
% 15.29/2.50                [c_3090,c_613,c_621]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_3353,plain,
% 15.29/2.50      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),sK4)
% 15.29/2.50      | r2_hidden(sK2,sK4)
% 15.29/2.50      | r2_hidden(sK3,sK4) ),
% 15.29/2.50      inference(resolution,[status(thm)],[c_3337,c_14]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_660,plain,
% 15.29/2.50      ( r2_hidden(X0,X1)
% 15.29/2.50      | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),sK4)
% 15.29/2.50      | X0 != sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3))
% 15.29/2.50      | X1 != sK4 ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_147]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_5880,plain,
% 15.29/2.50      ( r2_hidden(X0,sK4)
% 15.29/2.50      | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),sK4)
% 15.29/2.50      | X0 != sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3))
% 15.29/2.50      | sK4 != sK4 ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_660]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_5883,plain,
% 15.29/2.50      ( ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)),sK4)
% 15.29/2.50      | r2_hidden(sK2,sK4)
% 15.29/2.50      | sK2 != sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3))
% 15.29/2.50      | sK4 != sK4 ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_5880]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_5978,plain,
% 15.29/2.50      ( r2_hidden(sK2,sK4)
% 15.29/2.50      | r2_hidden(sK3,sK4)
% 15.29/2.50      | sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)) = sK3 ),
% 15.29/2.50      inference(global_propositional_subsumption,
% 15.29/2.50                [status(thm)],
% 15.29/2.50                [c_5222,c_17,c_18,c_14,c_1351,c_2617,c_3353,c_5883]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_6001,plain,
% 15.29/2.50      ( r2_hidden(sK2,sK4)
% 15.29/2.50      | r2_hidden(sK3,sK4)
% 15.29/2.50      | X0 != sK3
% 15.29/2.50      | sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)) = X0 ),
% 15.29/2.50      inference(resolution,[status(thm)],[c_5978,c_145]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_783,plain,
% 15.29/2.50      ( sK3 = sK3 ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_144]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_788,plain,
% 15.29/2.50      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_145]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_1316,plain,
% 15.29/2.50      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_788]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_1372,plain,
% 15.29/2.50      ( r2_hidden(sK2,sK4)
% 15.29/2.50      | r2_hidden(sK3,sK4)
% 15.29/2.50      | X0 != sK3
% 15.29/2.50      | sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)) = X0
% 15.29/2.50      | sK2 = sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)) ),
% 15.29/2.50      inference(resolution,[status(thm)],[c_1350,c_145]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_2012,plain,
% 15.29/2.50      ( r2_hidden(sK2,sK4)
% 15.29/2.50      | r2_hidden(sK3,sK4)
% 15.29/2.50      | X0 = sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3))
% 15.29/2.50      | X0 != sK3
% 15.29/2.50      | sK2 = sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3)) ),
% 15.29/2.50      inference(resolution,[status(thm)],[c_1372,c_810]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_2017,plain,
% 15.29/2.50      ( X0 = sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3))
% 15.29/2.50      | X0 != sK3
% 15.29/2.50      | sK2 = sK0(k2_enumset1(sK2,sK2,sK2,sK3),sK4,k2_enumset1(sK2,sK2,sK2,sK3))
% 15.29/2.50      | r2_hidden(sK2,sK4) = iProver_top
% 15.29/2.50      | r2_hidden(sK3,sK4) = iProver_top ),
% 15.29/2.50      inference(predicate_to_equality,[status(thm)],[c_2012]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_728,plain,
% 15.29/2.50      ( ~ r2_hidden(X0,X1) | r2_hidden(sK3,sK4) | sK4 != X1 | sK3 != X0 ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_147]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_5886,plain,
% 15.29/2.50      ( ~ r2_hidden(X0,sK4)
% 15.29/2.50      | r2_hidden(sK3,sK4)
% 15.29/2.50      | sK4 != sK4
% 15.29/2.50      | sK3 != X0 ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_728]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_6215,plain,
% 15.29/2.50      ( X0 != sK3 | r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) ),
% 15.29/2.50      inference(global_propositional_subsumption,
% 15.29/2.50                [status(thm)],
% 15.29/2.50                [c_6001,c_17,c_18,c_14,c_783,c_1316,c_2017,c_2617,c_3353,
% 15.29/2.50                 c_5880,c_5883,c_5886]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_6216,plain,
% 15.29/2.50      ( r2_hidden(sK2,sK4) | r2_hidden(sK3,sK4) | X0 != sK3 ),
% 15.29/2.50      inference(renaming,[status(thm)],[c_6215]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_6236,plain,
% 15.29/2.50      ( r2_hidden(sK2,sK4) | r2_hidden(sK3,sK4) ),
% 15.29/2.50      inference(backward_subsumption_resolution,
% 15.29/2.50                [status(thm)],
% 15.29/2.50                [c_6216,c_5978]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_6297,negated_conjecture,
% 15.29/2.50      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4) = k2_enumset1(sK2,sK2,sK2,sK3) ),
% 15.29/2.50      inference(global_propositional_subsumption,
% 15.29/2.50                [status(thm)],
% 15.29/2.50                [c_16,c_15,c_6236]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_6310,plain,
% 15.29/2.50      ( ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK3))
% 15.29/2.50      | r2_hidden(X1,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4))
% 15.29/2.50      | X1 != X0 ),
% 15.29/2.50      inference(resolution,[status(thm)],[c_6297,c_147]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_11,plain,
% 15.29/2.50      ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
% 15.29/2.50      inference(cnf_transformation,[],[f60]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_6723,plain,
% 15.29/2.50      ( r2_hidden(X0,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4))
% 15.29/2.50      | X0 != sK2 ),
% 15.29/2.50      inference(resolution,[status(thm)],[c_6310,c_11]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_4,plain,
% 15.29/2.50      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 15.29/2.50      inference(cnf_transformation,[],[f55]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_7738,plain,
% 15.29/2.50      ( ~ r2_hidden(X0,sK4) | X0 != sK2 ),
% 15.29/2.50      inference(resolution,[status(thm)],[c_6723,c_4]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_7740,plain,
% 15.29/2.50      ( ~ r2_hidden(sK2,sK4) | sK2 != sK2 ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_7738]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_1021,plain,
% 15.29/2.50      ( ~ r2_hidden(X0,X1)
% 15.29/2.50      | ~ r2_hidden(X0,k4_xboole_0(k2_enumset1(X2,X2,X3,X0),X1)) ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_4]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_1771,plain,
% 15.29/2.50      ( ~ r2_hidden(sK3,k4_xboole_0(k2_enumset1(X0,X0,X1,sK3),sK4))
% 15.29/2.50      | ~ r2_hidden(sK3,sK4) ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_1021]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_1773,plain,
% 15.29/2.50      ( ~ r2_hidden(sK3,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4))
% 15.29/2.50      | ~ r2_hidden(sK3,sK4) ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_1771]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_10,plain,
% 15.29/2.50      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 15.29/2.50      inference(cnf_transformation,[],[f58]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_748,plain,
% 15.29/2.50      ( r2_hidden(sK3,k2_enumset1(X0,X0,X1,sK3)) ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_10]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_754,plain,
% 15.29/2.50      ( r2_hidden(sK3,k2_enumset1(sK2,sK2,sK2,sK3)) ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_748]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_12,plain,
% 15.29/2.50      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 15.29/2.50      inference(cnf_transformation,[],[f62]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_24,plain,
% 15.29/2.50      ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_12]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(c_21,plain,
% 15.29/2.50      ( ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) | sK2 = sK2 ),
% 15.29/2.50      inference(instantiation,[status(thm)],[c_13]) ).
% 15.29/2.50  
% 15.29/2.50  cnf(contradiction,plain,
% 15.29/2.50      ( $false ),
% 15.29/2.50      inference(minisat,
% 15.29/2.50                [status(thm)],
% 15.29/2.50                [c_39768,c_7740,c_6297,c_1773,c_783,c_754,c_24,c_21,c_14]) ).
% 15.29/2.50  
% 15.29/2.50  
% 15.29/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.29/2.50  
% 15.29/2.50  ------                               Statistics
% 15.29/2.50  
% 15.29/2.50  ------ Selected
% 15.29/2.50  
% 15.29/2.50  total_time:                             1.599
% 15.29/2.50  
%------------------------------------------------------------------------------
