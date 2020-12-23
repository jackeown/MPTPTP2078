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
% DateTime   : Thu Dec  3 11:35:57 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 374 expanded)
%              Number of clauses        :   38 (  68 expanded)
%              Number of leaves         :   12 (  97 expanded)
%              Depth                    :   14
%              Number of atoms          :  351 (1578 expanded)
%              Number of equality atoms :  178 ( 805 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
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
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f67,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f99,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f67,f77])).

fof(f118,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f99])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) )
        & ( ~ r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ) )
   => ( ( r2_hidden(sK4,sK5)
        | k4_xboole_0(k1_tarski(sK4),sK5) != k1_tarski(sK4) )
      & ( ~ r2_hidden(sK4,sK5)
        | k4_xboole_0(k1_tarski(sK4),sK5) = k1_tarski(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( r2_hidden(sK4,sK5)
      | k4_xboole_0(k1_tarski(sK4),sK5) != k1_tarski(sK4) )
    & ( ~ r2_hidden(sK4,sK5)
      | k4_xboole_0(k1_tarski(sK4),sK5) = k1_tarski(sK4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f42,f43])).

fof(f81,plain,
    ( r2_hidden(sK4,sK5)
    | k4_xboole_0(k1_tarski(sK4),sK5) != k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f76,f77])).

fof(f83,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f75,f82])).

fof(f102,plain,
    ( r2_hidden(sK4,sK5)
    | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f81,f83,f83])).

fof(f68,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f98,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f68,f77])).

fof(f116,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f98])).

fof(f117,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f116])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f78,f83])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f79,f83])).

fof(f80,plain,
    ( ~ r2_hidden(sK4,sK5)
    | k4_xboole_0(k1_tarski(sK4),sK5) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f103,plain,
    ( ~ r2_hidden(sK4,sK5)
    | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f80,f83,f83])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f108,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_551,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1878,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5)
    | X0 != sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4))
    | X1 != sK5 ),
    inference(instantiation,[status(thm)],[c_551])).

cnf(c_10429,plain,
    ( r2_hidden(X0,k4_xboole_0(sK5,k2_enumset1(X1,X1,X1,X1)))
    | ~ r2_hidden(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5)
    | X0 != sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4))
    | k4_xboole_0(sK5,k2_enumset1(X1,X1,X1,X1)) != sK5 ),
    inference(instantiation,[status(thm)],[c_1878])).

cnf(c_10432,plain,
    ( ~ r2_hidden(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5)
    | r2_hidden(sK4,k4_xboole_0(sK5,k2_enumset1(sK4,sK4,sK4,sK4)))
    | k4_xboole_0(sK5,k2_enumset1(sK4,sK4,sK4,sK4)) != sK5
    | sK4 != sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_10429])).

cnf(c_548,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5862,plain,
    ( X0 != X1
    | X0 = sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4))
    | sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) != X1 ),
    inference(instantiation,[status(thm)],[c_548])).

cnf(c_5863,plain,
    ( sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) != sK4
    | sK4 = sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_5862])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_14,plain,
    ( r2_hidden(sK2(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_31,negated_conjecture,
    ( r2_hidden(sK4,sK5)
    | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_3257,plain,
    ( r2_hidden(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK4,sK5) ),
    inference(resolution,[status(thm)],[c_14,c_31])).

cnf(c_42,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_27,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_45,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1541,plain,
    ( r2_hidden(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_30,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) != X1 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1603,plain,
    ( ~ r2_hidden(sK4,sK5)
    | k4_xboole_0(sK5,k2_enumset1(sK4,sK4,sK4,sK4)) != sK5 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_29,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1153,plain,
    ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_32,negated_conjecture,
    ( ~ r2_hidden(sK4,sK5)
    | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1150,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(sK4,sK4,sK4,sK4)
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2179,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(sK4,sK4,sK4,sK4)
    | k4_xboole_0(sK5,k2_enumset1(sK4,sK4,sK4,sK4)) = sK5 ),
    inference(superposition,[status(thm)],[c_1153,c_1150])).

cnf(c_1535,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X3,X3,X2,X4))
    | X0 != X2
    | X1 != k2_enumset1(X3,X3,X2,X4) ),
    inference(instantiation,[status(thm)],[c_551])).

cnf(c_2470,plain,
    ( r2_hidden(X0,k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5))
    | ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | X0 != sK4
    | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1535])).

cnf(c_2472,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK4,k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5))
    | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) != k2_enumset1(sK4,sK4,sK4,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2470])).

cnf(c_2579,plain,
    ( r2_hidden(sK4,sK5)
    | k4_xboole_0(sK5,k2_enumset1(sK4,sK4,sK4,sK4)) = sK5 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1605,plain,
    ( ~ r2_hidden(sK4,k4_xboole_0(X0,sK5))
    | ~ r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2584,plain,
    ( ~ r2_hidden(sK4,k4_xboole_0(k2_enumset1(X0,X0,X1,sK4),sK5))
    | ~ r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1605])).

cnf(c_2587,plain,
    ( ~ r2_hidden(sK4,k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5))
    | ~ r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2584])).

cnf(c_3364,plain,
    ( r2_hidden(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3257,c_31,c_42,c_45,c_1541,c_1603,c_2179,c_2472,c_2579,c_2587])).

cnf(c_5666,plain,
    ( sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) = sK4 ),
    inference(resolution,[status(thm)],[c_28,c_3364])).

cnf(c_1411,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
    | ~ r2_hidden(X0,k4_xboole_0(X3,k2_enumset1(X1,X1,X2,X0))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2661,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(X0,X0,X1,sK4))
    | ~ r2_hidden(sK4,k4_xboole_0(sK5,k2_enumset1(X0,X0,X1,sK4))) ),
    inference(instantiation,[status(thm)],[c_1411])).

cnf(c_2665,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK4,k4_xboole_0(sK5,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(instantiation,[status(thm)],[c_2661])).

cnf(c_12,plain,
    ( ~ r2_hidden(sK2(X0,X1,X2),X0)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | r2_hidden(sK2(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1569,plain,
    ( ~ r2_hidden(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5)
    | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10432,c_5863,c_5666,c_2665,c_2587,c_2579,c_2472,c_2179,c_1603,c_1569,c_1541,c_45,c_42,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:40:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.24/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.04  
% 3.24/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.24/1.04  
% 3.24/1.04  ------  iProver source info
% 3.24/1.04  
% 3.24/1.04  git: date: 2020-06-30 10:37:57 +0100
% 3.24/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.24/1.04  git: non_committed_changes: false
% 3.24/1.04  git: last_make_outside_of_git: false
% 3.24/1.04  
% 3.24/1.04  ------ 
% 3.24/1.04  
% 3.24/1.04  ------ Input Options
% 3.24/1.04  
% 3.24/1.04  --out_options                           all
% 3.24/1.04  --tptp_safe_out                         true
% 3.24/1.04  --problem_path                          ""
% 3.24/1.04  --include_path                          ""
% 3.24/1.04  --clausifier                            res/vclausify_rel
% 3.24/1.04  --clausifier_options                    --mode clausify
% 3.24/1.04  --stdin                                 false
% 3.24/1.04  --stats_out                             sel
% 3.24/1.04  
% 3.24/1.04  ------ General Options
% 3.24/1.04  
% 3.24/1.04  --fof                                   false
% 3.24/1.04  --time_out_real                         604.98
% 3.24/1.04  --time_out_virtual                      -1.
% 3.24/1.04  --symbol_type_check                     false
% 3.24/1.04  --clausify_out                          false
% 3.24/1.04  --sig_cnt_out                           false
% 3.24/1.04  --trig_cnt_out                          false
% 3.24/1.04  --trig_cnt_out_tolerance                1.
% 3.24/1.04  --trig_cnt_out_sk_spl                   false
% 3.24/1.04  --abstr_cl_out                          false
% 3.24/1.04  
% 3.24/1.04  ------ Global Options
% 3.24/1.04  
% 3.24/1.04  --schedule                              none
% 3.24/1.04  --add_important_lit                     false
% 3.24/1.04  --prop_solver_per_cl                    1000
% 3.24/1.04  --min_unsat_core                        false
% 3.24/1.04  --soft_assumptions                      false
% 3.24/1.04  --soft_lemma_size                       3
% 3.24/1.04  --prop_impl_unit_size                   0
% 3.24/1.04  --prop_impl_unit                        []
% 3.24/1.04  --share_sel_clauses                     true
% 3.24/1.04  --reset_solvers                         false
% 3.24/1.04  --bc_imp_inh                            [conj_cone]
% 3.24/1.04  --conj_cone_tolerance                   3.
% 3.24/1.04  --extra_neg_conj                        none
% 3.24/1.04  --large_theory_mode                     true
% 3.24/1.04  --prolific_symb_bound                   200
% 3.24/1.04  --lt_threshold                          2000
% 3.24/1.04  --clause_weak_htbl                      true
% 3.24/1.04  --gc_record_bc_elim                     false
% 3.24/1.04  
% 3.24/1.04  ------ Preprocessing Options
% 3.24/1.04  
% 3.24/1.04  --preprocessing_flag                    true
% 3.24/1.04  --time_out_prep_mult                    0.1
% 3.24/1.04  --splitting_mode                        input
% 3.24/1.04  --splitting_grd                         true
% 3.24/1.04  --splitting_cvd                         false
% 3.24/1.04  --splitting_cvd_svl                     false
% 3.24/1.04  --splitting_nvd                         32
% 3.24/1.04  --sub_typing                            true
% 3.24/1.04  --prep_gs_sim                           false
% 3.24/1.04  --prep_unflatten                        true
% 3.24/1.04  --prep_res_sim                          true
% 3.24/1.04  --prep_upred                            true
% 3.24/1.04  --prep_sem_filter                       exhaustive
% 3.24/1.04  --prep_sem_filter_out                   false
% 3.24/1.04  --pred_elim                             false
% 3.24/1.04  --res_sim_input                         true
% 3.24/1.04  --eq_ax_congr_red                       true
% 3.24/1.04  --pure_diseq_elim                       true
% 3.24/1.04  --brand_transform                       false
% 3.24/1.04  --non_eq_to_eq                          false
% 3.24/1.04  --prep_def_merge                        true
% 3.24/1.04  --prep_def_merge_prop_impl              false
% 3.24/1.04  --prep_def_merge_mbd                    true
% 3.24/1.04  --prep_def_merge_tr_red                 false
% 3.24/1.04  --prep_def_merge_tr_cl                  false
% 3.24/1.04  --smt_preprocessing                     true
% 3.24/1.04  --smt_ac_axioms                         fast
% 3.24/1.04  --preprocessed_out                      false
% 3.24/1.04  --preprocessed_stats                    false
% 3.24/1.04  
% 3.24/1.04  ------ Abstraction refinement Options
% 3.24/1.04  
% 3.24/1.04  --abstr_ref                             []
% 3.24/1.04  --abstr_ref_prep                        false
% 3.24/1.04  --abstr_ref_until_sat                   false
% 3.24/1.04  --abstr_ref_sig_restrict                funpre
% 3.24/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.24/1.04  --abstr_ref_under                       []
% 3.24/1.04  
% 3.24/1.04  ------ SAT Options
% 3.24/1.04  
% 3.24/1.04  --sat_mode                              false
% 3.24/1.04  --sat_fm_restart_options                ""
% 3.24/1.04  --sat_gr_def                            false
% 3.24/1.04  --sat_epr_types                         true
% 3.24/1.04  --sat_non_cyclic_types                  false
% 3.24/1.04  --sat_finite_models                     false
% 3.24/1.04  --sat_fm_lemmas                         false
% 3.24/1.04  --sat_fm_prep                           false
% 3.24/1.04  --sat_fm_uc_incr                        true
% 3.24/1.04  --sat_out_model                         small
% 3.24/1.04  --sat_out_clauses                       false
% 3.24/1.04  
% 3.24/1.04  ------ QBF Options
% 3.24/1.04  
% 3.24/1.04  --qbf_mode                              false
% 3.24/1.04  --qbf_elim_univ                         false
% 3.24/1.04  --qbf_dom_inst                          none
% 3.24/1.04  --qbf_dom_pre_inst                      false
% 3.24/1.04  --qbf_sk_in                             false
% 3.24/1.04  --qbf_pred_elim                         true
% 3.24/1.04  --qbf_split                             512
% 3.24/1.04  
% 3.24/1.04  ------ BMC1 Options
% 3.24/1.04  
% 3.24/1.04  --bmc1_incremental                      false
% 3.24/1.04  --bmc1_axioms                           reachable_all
% 3.24/1.04  --bmc1_min_bound                        0
% 3.24/1.04  --bmc1_max_bound                        -1
% 3.24/1.04  --bmc1_max_bound_default                -1
% 3.24/1.04  --bmc1_symbol_reachability              true
% 3.24/1.04  --bmc1_property_lemmas                  false
% 3.24/1.04  --bmc1_k_induction                      false
% 3.24/1.04  --bmc1_non_equiv_states                 false
% 3.24/1.04  --bmc1_deadlock                         false
% 3.24/1.04  --bmc1_ucm                              false
% 3.24/1.04  --bmc1_add_unsat_core                   none
% 3.24/1.04  --bmc1_unsat_core_children              false
% 3.24/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.24/1.04  --bmc1_out_stat                         full
% 3.24/1.04  --bmc1_ground_init                      false
% 3.24/1.04  --bmc1_pre_inst_next_state              false
% 3.24/1.04  --bmc1_pre_inst_state                   false
% 3.24/1.04  --bmc1_pre_inst_reach_state             false
% 3.24/1.04  --bmc1_out_unsat_core                   false
% 3.24/1.04  --bmc1_aig_witness_out                  false
% 3.24/1.04  --bmc1_verbose                          false
% 3.24/1.04  --bmc1_dump_clauses_tptp                false
% 3.24/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.24/1.04  --bmc1_dump_file                        -
% 3.24/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.24/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.24/1.04  --bmc1_ucm_extend_mode                  1
% 3.24/1.04  --bmc1_ucm_init_mode                    2
% 3.24/1.04  --bmc1_ucm_cone_mode                    none
% 3.24/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.24/1.04  --bmc1_ucm_relax_model                  4
% 3.24/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.24/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.24/1.04  --bmc1_ucm_layered_model                none
% 3.24/1.04  --bmc1_ucm_max_lemma_size               10
% 3.24/1.04  
% 3.24/1.04  ------ AIG Options
% 3.24/1.04  
% 3.24/1.04  --aig_mode                              false
% 3.24/1.04  
% 3.24/1.04  ------ Instantiation Options
% 3.24/1.04  
% 3.24/1.04  --instantiation_flag                    true
% 3.24/1.04  --inst_sos_flag                         false
% 3.24/1.04  --inst_sos_phase                        true
% 3.24/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.24/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.24/1.04  --inst_lit_sel_side                     num_symb
% 3.24/1.04  --inst_solver_per_active                1400
% 3.24/1.04  --inst_solver_calls_frac                1.
% 3.24/1.04  --inst_passive_queue_type               priority_queues
% 3.24/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.24/1.04  --inst_passive_queues_freq              [25;2]
% 3.24/1.04  --inst_dismatching                      true
% 3.24/1.04  --inst_eager_unprocessed_to_passive     true
% 3.24/1.04  --inst_prop_sim_given                   true
% 3.24/1.04  --inst_prop_sim_new                     false
% 3.24/1.04  --inst_subs_new                         false
% 3.24/1.04  --inst_eq_res_simp                      false
% 3.24/1.04  --inst_subs_given                       false
% 3.24/1.04  --inst_orphan_elimination               true
% 3.24/1.04  --inst_learning_loop_flag               true
% 3.24/1.04  --inst_learning_start                   3000
% 3.24/1.04  --inst_learning_factor                  2
% 3.24/1.04  --inst_start_prop_sim_after_learn       3
% 3.24/1.04  --inst_sel_renew                        solver
% 3.24/1.04  --inst_lit_activity_flag                true
% 3.24/1.04  --inst_restr_to_given                   false
% 3.24/1.04  --inst_activity_threshold               500
% 3.24/1.04  --inst_out_proof                        true
% 3.24/1.04  
% 3.24/1.04  ------ Resolution Options
% 3.24/1.04  
% 3.24/1.04  --resolution_flag                       true
% 3.24/1.04  --res_lit_sel                           adaptive
% 3.24/1.04  --res_lit_sel_side                      none
% 3.24/1.04  --res_ordering                          kbo
% 3.24/1.04  --res_to_prop_solver                    active
% 3.24/1.04  --res_prop_simpl_new                    false
% 3.24/1.04  --res_prop_simpl_given                  true
% 3.24/1.04  --res_passive_queue_type                priority_queues
% 3.24/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.24/1.04  --res_passive_queues_freq               [15;5]
% 3.24/1.04  --res_forward_subs                      full
% 3.24/1.04  --res_backward_subs                     full
% 3.24/1.04  --res_forward_subs_resolution           true
% 3.24/1.04  --res_backward_subs_resolution          true
% 3.24/1.04  --res_orphan_elimination                true
% 3.24/1.04  --res_time_limit                        2.
% 3.24/1.04  --res_out_proof                         true
% 3.24/1.04  
% 3.24/1.04  ------ Superposition Options
% 3.24/1.04  
% 3.24/1.04  --superposition_flag                    true
% 3.24/1.04  --sup_passive_queue_type                priority_queues
% 3.24/1.04  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.24/1.04  --sup_passive_queues_freq               [1;4]
% 3.24/1.04  --demod_completeness_check              fast
% 3.24/1.04  --demod_use_ground                      true
% 3.24/1.04  --sup_to_prop_solver                    passive
% 3.24/1.04  --sup_prop_simpl_new                    true
% 3.24/1.04  --sup_prop_simpl_given                  true
% 3.24/1.04  --sup_fun_splitting                     false
% 3.24/1.04  --sup_smt_interval                      50000
% 3.24/1.04  
% 3.24/1.04  ------ Superposition Simplification Setup
% 3.24/1.04  
% 3.24/1.04  --sup_indices_passive                   []
% 3.24/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.24/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.04  --sup_full_bw                           [BwDemod]
% 3.24/1.04  --sup_immed_triv                        [TrivRules]
% 3.24/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.24/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.04  --sup_immed_bw_main                     []
% 3.24/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.24/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.04  
% 3.24/1.04  ------ Combination Options
% 3.24/1.04  
% 3.24/1.04  --comb_res_mult                         3
% 3.24/1.04  --comb_sup_mult                         2
% 3.24/1.04  --comb_inst_mult                        10
% 3.24/1.04  
% 3.24/1.04  ------ Debug Options
% 3.24/1.04  
% 3.24/1.04  --dbg_backtrace                         false
% 3.24/1.04  --dbg_dump_prop_clauses                 false
% 3.24/1.04  --dbg_dump_prop_clauses_file            -
% 3.24/1.04  --dbg_out_stat                          false
% 3.24/1.04  ------ Parsing...
% 3.24/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.24/1.04  
% 3.24/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.24/1.04  
% 3.24/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.24/1.04  
% 3.24/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.24/1.04  ------ Proving...
% 3.24/1.04  ------ Problem Properties 
% 3.24/1.04  
% 3.24/1.04  
% 3.24/1.04  clauses                                 32
% 3.24/1.04  conjectures                             2
% 3.24/1.04  EPR                                     4
% 3.24/1.04  Horn                                    22
% 3.24/1.04  unary                                   6
% 3.24/1.04  binary                                  11
% 3.24/1.04  lits                                    78
% 3.24/1.04  lits eq                                 26
% 3.24/1.04  fd_pure                                 0
% 3.24/1.04  fd_pseudo                               0
% 3.24/1.04  fd_cond                                 0
% 3.24/1.04  fd_pseudo_cond                          11
% 3.24/1.04  AC symbols                              0
% 3.24/1.04  
% 3.24/1.04  ------ Input Options Time Limit: Unbounded
% 3.24/1.04  
% 3.24/1.04  
% 3.24/1.04  ------ 
% 3.24/1.04  Current options:
% 3.24/1.04  ------ 
% 3.24/1.04  
% 3.24/1.04  ------ Input Options
% 3.24/1.04  
% 3.24/1.04  --out_options                           all
% 3.24/1.04  --tptp_safe_out                         true
% 3.24/1.04  --problem_path                          ""
% 3.24/1.04  --include_path                          ""
% 3.24/1.04  --clausifier                            res/vclausify_rel
% 3.24/1.04  --clausifier_options                    --mode clausify
% 3.24/1.04  --stdin                                 false
% 3.24/1.04  --stats_out                             sel
% 3.24/1.04  
% 3.24/1.04  ------ General Options
% 3.24/1.04  
% 3.24/1.04  --fof                                   false
% 3.24/1.04  --time_out_real                         604.98
% 3.24/1.04  --time_out_virtual                      -1.
% 3.24/1.04  --symbol_type_check                     false
% 3.24/1.04  --clausify_out                          false
% 3.24/1.04  --sig_cnt_out                           false
% 3.24/1.04  --trig_cnt_out                          false
% 3.24/1.04  --trig_cnt_out_tolerance                1.
% 3.24/1.04  --trig_cnt_out_sk_spl                   false
% 3.24/1.04  --abstr_cl_out                          false
% 3.24/1.04  
% 3.24/1.04  ------ Global Options
% 3.24/1.04  
% 3.24/1.04  --schedule                              none
% 3.24/1.04  --add_important_lit                     false
% 3.24/1.04  --prop_solver_per_cl                    1000
% 3.24/1.04  --min_unsat_core                        false
% 3.24/1.04  --soft_assumptions                      false
% 3.24/1.04  --soft_lemma_size                       3
% 3.24/1.04  --prop_impl_unit_size                   0
% 3.24/1.04  --prop_impl_unit                        []
% 3.24/1.04  --share_sel_clauses                     true
% 3.24/1.04  --reset_solvers                         false
% 3.24/1.04  --bc_imp_inh                            [conj_cone]
% 3.24/1.04  --conj_cone_tolerance                   3.
% 3.24/1.04  --extra_neg_conj                        none
% 3.24/1.04  --large_theory_mode                     true
% 3.24/1.04  --prolific_symb_bound                   200
% 3.24/1.04  --lt_threshold                          2000
% 3.24/1.04  --clause_weak_htbl                      true
% 3.24/1.04  --gc_record_bc_elim                     false
% 3.24/1.04  
% 3.24/1.04  ------ Preprocessing Options
% 3.24/1.04  
% 3.24/1.04  --preprocessing_flag                    true
% 3.24/1.04  --time_out_prep_mult                    0.1
% 3.24/1.04  --splitting_mode                        input
% 3.24/1.04  --splitting_grd                         true
% 3.24/1.04  --splitting_cvd                         false
% 3.24/1.04  --splitting_cvd_svl                     false
% 3.24/1.04  --splitting_nvd                         32
% 3.24/1.04  --sub_typing                            true
% 3.24/1.04  --prep_gs_sim                           false
% 3.24/1.04  --prep_unflatten                        true
% 3.24/1.04  --prep_res_sim                          true
% 3.24/1.04  --prep_upred                            true
% 3.24/1.04  --prep_sem_filter                       exhaustive
% 3.24/1.04  --prep_sem_filter_out                   false
% 3.24/1.04  --pred_elim                             false
% 3.24/1.04  --res_sim_input                         true
% 3.24/1.04  --eq_ax_congr_red                       true
% 3.24/1.04  --pure_diseq_elim                       true
% 3.24/1.04  --brand_transform                       false
% 3.24/1.04  --non_eq_to_eq                          false
% 3.24/1.04  --prep_def_merge                        true
% 3.24/1.04  --prep_def_merge_prop_impl              false
% 3.24/1.04  --prep_def_merge_mbd                    true
% 3.24/1.04  --prep_def_merge_tr_red                 false
% 3.24/1.04  --prep_def_merge_tr_cl                  false
% 3.24/1.04  --smt_preprocessing                     true
% 3.24/1.04  --smt_ac_axioms                         fast
% 3.24/1.04  --preprocessed_out                      false
% 3.24/1.04  --preprocessed_stats                    false
% 3.24/1.04  
% 3.24/1.04  ------ Abstraction refinement Options
% 3.24/1.04  
% 3.24/1.04  --abstr_ref                             []
% 3.24/1.04  --abstr_ref_prep                        false
% 3.24/1.04  --abstr_ref_until_sat                   false
% 3.24/1.04  --abstr_ref_sig_restrict                funpre
% 3.24/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.24/1.04  --abstr_ref_under                       []
% 3.24/1.04  
% 3.24/1.04  ------ SAT Options
% 3.24/1.04  
% 3.24/1.04  --sat_mode                              false
% 3.24/1.04  --sat_fm_restart_options                ""
% 3.24/1.04  --sat_gr_def                            false
% 3.24/1.04  --sat_epr_types                         true
% 3.24/1.04  --sat_non_cyclic_types                  false
% 3.24/1.04  --sat_finite_models                     false
% 3.24/1.04  --sat_fm_lemmas                         false
% 3.24/1.04  --sat_fm_prep                           false
% 3.24/1.04  --sat_fm_uc_incr                        true
% 3.24/1.04  --sat_out_model                         small
% 3.24/1.04  --sat_out_clauses                       false
% 3.24/1.04  
% 3.24/1.04  ------ QBF Options
% 3.24/1.04  
% 3.24/1.04  --qbf_mode                              false
% 3.24/1.04  --qbf_elim_univ                         false
% 3.24/1.04  --qbf_dom_inst                          none
% 3.24/1.04  --qbf_dom_pre_inst                      false
% 3.24/1.04  --qbf_sk_in                             false
% 3.24/1.04  --qbf_pred_elim                         true
% 3.24/1.04  --qbf_split                             512
% 3.24/1.04  
% 3.24/1.04  ------ BMC1 Options
% 3.24/1.04  
% 3.24/1.04  --bmc1_incremental                      false
% 3.24/1.04  --bmc1_axioms                           reachable_all
% 3.24/1.04  --bmc1_min_bound                        0
% 3.24/1.04  --bmc1_max_bound                        -1
% 3.24/1.04  --bmc1_max_bound_default                -1
% 3.24/1.04  --bmc1_symbol_reachability              true
% 3.24/1.04  --bmc1_property_lemmas                  false
% 3.24/1.04  --bmc1_k_induction                      false
% 3.24/1.04  --bmc1_non_equiv_states                 false
% 3.24/1.04  --bmc1_deadlock                         false
% 3.24/1.04  --bmc1_ucm                              false
% 3.24/1.04  --bmc1_add_unsat_core                   none
% 3.24/1.04  --bmc1_unsat_core_children              false
% 3.24/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.24/1.04  --bmc1_out_stat                         full
% 3.24/1.04  --bmc1_ground_init                      false
% 3.24/1.04  --bmc1_pre_inst_next_state              false
% 3.24/1.04  --bmc1_pre_inst_state                   false
% 3.24/1.04  --bmc1_pre_inst_reach_state             false
% 3.24/1.04  --bmc1_out_unsat_core                   false
% 3.24/1.04  --bmc1_aig_witness_out                  false
% 3.24/1.04  --bmc1_verbose                          false
% 3.24/1.04  --bmc1_dump_clauses_tptp                false
% 3.24/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.24/1.04  --bmc1_dump_file                        -
% 3.24/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.24/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.24/1.04  --bmc1_ucm_extend_mode                  1
% 3.24/1.04  --bmc1_ucm_init_mode                    2
% 3.24/1.04  --bmc1_ucm_cone_mode                    none
% 3.24/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.24/1.04  --bmc1_ucm_relax_model                  4
% 3.24/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.24/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.24/1.04  --bmc1_ucm_layered_model                none
% 3.24/1.04  --bmc1_ucm_max_lemma_size               10
% 3.24/1.04  
% 3.24/1.04  ------ AIG Options
% 3.24/1.04  
% 3.24/1.04  --aig_mode                              false
% 3.24/1.04  
% 3.24/1.04  ------ Instantiation Options
% 3.24/1.04  
% 3.24/1.04  --instantiation_flag                    true
% 3.24/1.04  --inst_sos_flag                         false
% 3.24/1.04  --inst_sos_phase                        true
% 3.24/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.24/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.24/1.04  --inst_lit_sel_side                     num_symb
% 3.24/1.04  --inst_solver_per_active                1400
% 3.24/1.04  --inst_solver_calls_frac                1.
% 3.24/1.04  --inst_passive_queue_type               priority_queues
% 3.24/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.24/1.04  --inst_passive_queues_freq              [25;2]
% 3.24/1.04  --inst_dismatching                      true
% 3.24/1.04  --inst_eager_unprocessed_to_passive     true
% 3.24/1.04  --inst_prop_sim_given                   true
% 3.24/1.04  --inst_prop_sim_new                     false
% 3.24/1.04  --inst_subs_new                         false
% 3.24/1.04  --inst_eq_res_simp                      false
% 3.24/1.04  --inst_subs_given                       false
% 3.24/1.04  --inst_orphan_elimination               true
% 3.24/1.04  --inst_learning_loop_flag               true
% 3.24/1.04  --inst_learning_start                   3000
% 3.24/1.04  --inst_learning_factor                  2
% 3.24/1.04  --inst_start_prop_sim_after_learn       3
% 3.24/1.04  --inst_sel_renew                        solver
% 3.24/1.04  --inst_lit_activity_flag                true
% 3.24/1.04  --inst_restr_to_given                   false
% 3.24/1.04  --inst_activity_threshold               500
% 3.24/1.04  --inst_out_proof                        true
% 3.24/1.04  
% 3.24/1.04  ------ Resolution Options
% 3.24/1.04  
% 3.24/1.04  --resolution_flag                       true
% 3.24/1.04  --res_lit_sel                           adaptive
% 3.24/1.04  --res_lit_sel_side                      none
% 3.24/1.04  --res_ordering                          kbo
% 3.24/1.04  --res_to_prop_solver                    active
% 3.24/1.04  --res_prop_simpl_new                    false
% 3.24/1.04  --res_prop_simpl_given                  true
% 3.24/1.04  --res_passive_queue_type                priority_queues
% 3.24/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.24/1.04  --res_passive_queues_freq               [15;5]
% 3.24/1.04  --res_forward_subs                      full
% 3.24/1.04  --res_backward_subs                     full
% 3.24/1.04  --res_forward_subs_resolution           true
% 3.24/1.04  --res_backward_subs_resolution          true
% 3.24/1.04  --res_orphan_elimination                true
% 3.24/1.04  --res_time_limit                        2.
% 3.24/1.04  --res_out_proof                         true
% 3.24/1.04  
% 3.24/1.04  ------ Superposition Options
% 3.24/1.04  
% 3.24/1.04  --superposition_flag                    true
% 3.24/1.04  --sup_passive_queue_type                priority_queues
% 3.24/1.04  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.24/1.04  --sup_passive_queues_freq               [1;4]
% 3.24/1.04  --demod_completeness_check              fast
% 3.24/1.04  --demod_use_ground                      true
% 3.24/1.04  --sup_to_prop_solver                    passive
% 3.24/1.04  --sup_prop_simpl_new                    true
% 3.24/1.04  --sup_prop_simpl_given                  true
% 3.24/1.04  --sup_fun_splitting                     false
% 3.24/1.04  --sup_smt_interval                      50000
% 3.24/1.04  
% 3.24/1.04  ------ Superposition Simplification Setup
% 3.24/1.04  
% 3.24/1.04  --sup_indices_passive                   []
% 3.24/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.24/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.04  --sup_full_bw                           [BwDemod]
% 3.24/1.04  --sup_immed_triv                        [TrivRules]
% 3.24/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.24/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.04  --sup_immed_bw_main                     []
% 3.24/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.24/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.04  
% 3.24/1.04  ------ Combination Options
% 3.24/1.04  
% 3.24/1.04  --comb_res_mult                         3
% 3.24/1.04  --comb_sup_mult                         2
% 3.24/1.04  --comb_inst_mult                        10
% 3.24/1.04  
% 3.24/1.04  ------ Debug Options
% 3.24/1.04  
% 3.24/1.04  --dbg_backtrace                         false
% 3.24/1.04  --dbg_dump_prop_clauses                 false
% 3.24/1.04  --dbg_dump_prop_clauses_file            -
% 3.24/1.04  --dbg_out_stat                          false
% 3.24/1.04  
% 3.24/1.04  
% 3.24/1.04  
% 3.24/1.04  
% 3.24/1.04  ------ Proving...
% 3.24/1.04  
% 3.24/1.04  
% 3.24/1.04  % SZS status Theorem for theBenchmark.p
% 3.24/1.04  
% 3.24/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 3.24/1.04  
% 3.24/1.04  fof(f9,axiom,(
% 3.24/1.04    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.24/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.04  
% 3.24/1.04  fof(f18,plain,(
% 3.24/1.04    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.24/1.04    inference(ennf_transformation,[],[f9])).
% 3.24/1.04  
% 3.24/1.04  fof(f36,plain,(
% 3.24/1.04    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.24/1.04    inference(nnf_transformation,[],[f18])).
% 3.24/1.04  
% 3.24/1.04  fof(f37,plain,(
% 3.24/1.04    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.24/1.04    inference(flattening,[],[f36])).
% 3.24/1.04  
% 3.24/1.04  fof(f38,plain,(
% 3.24/1.04    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.24/1.04    inference(rectify,[],[f37])).
% 3.24/1.04  
% 3.24/1.04  fof(f39,plain,(
% 3.24/1.04    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 3.24/1.04    introduced(choice_axiom,[])).
% 3.24/1.04  
% 3.24/1.04  fof(f40,plain,(
% 3.24/1.04    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.24/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 3.24/1.04  
% 3.24/1.04  fof(f67,plain,(
% 3.24/1.04    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.24/1.04    inference(cnf_transformation,[],[f40])).
% 3.24/1.04  
% 3.24/1.04  fof(f12,axiom,(
% 3.24/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.24/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.04  
% 3.24/1.04  fof(f77,plain,(
% 3.24/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.24/1.04    inference(cnf_transformation,[],[f12])).
% 3.24/1.04  
% 3.24/1.04  fof(f99,plain,(
% 3.24/1.04    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.24/1.04    inference(definition_unfolding,[],[f67,f77])).
% 3.24/1.04  
% 3.24/1.04  fof(f118,plain,(
% 3.24/1.04    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 3.24/1.04    inference(equality_resolution,[],[f99])).
% 3.24/1.04  
% 3.24/1.04  fof(f5,axiom,(
% 3.24/1.04    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.24/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.04  
% 3.24/1.04  fof(f29,plain,(
% 3.24/1.04    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.24/1.04    inference(nnf_transformation,[],[f5])).
% 3.24/1.04  
% 3.24/1.04  fof(f30,plain,(
% 3.24/1.04    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.24/1.04    inference(flattening,[],[f29])).
% 3.24/1.04  
% 3.24/1.04  fof(f31,plain,(
% 3.24/1.04    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.24/1.04    inference(rectify,[],[f30])).
% 3.24/1.04  
% 3.24/1.04  fof(f32,plain,(
% 3.24/1.04    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.24/1.04    introduced(choice_axiom,[])).
% 3.24/1.04  
% 3.24/1.04  fof(f33,plain,(
% 3.24/1.04    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.24/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 3.24/1.04  
% 3.24/1.04  fof(f59,plain,(
% 3.24/1.04    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.24/1.04    inference(cnf_transformation,[],[f33])).
% 3.24/1.04  
% 3.24/1.04  fof(f14,conjecture,(
% 3.24/1.04    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 3.24/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.04  
% 3.24/1.04  fof(f15,negated_conjecture,(
% 3.24/1.04    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 3.24/1.04    inference(negated_conjecture,[],[f14])).
% 3.24/1.04  
% 3.24/1.04  fof(f19,plain,(
% 3.24/1.04    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <~> ~r2_hidden(X0,X1))),
% 3.24/1.04    inference(ennf_transformation,[],[f15])).
% 3.24/1.04  
% 3.24/1.04  fof(f42,plain,(
% 3.24/1.04    ? [X0,X1] : ((r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)) & (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)))),
% 3.24/1.04    inference(nnf_transformation,[],[f19])).
% 3.24/1.04  
% 3.24/1.04  fof(f43,plain,(
% 3.24/1.04    ? [X0,X1] : ((r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)) & (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0))) => ((r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) != k1_tarski(sK4)) & (~r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) = k1_tarski(sK4)))),
% 3.24/1.04    introduced(choice_axiom,[])).
% 3.24/1.04  
% 3.24/1.04  fof(f44,plain,(
% 3.24/1.04    (r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) != k1_tarski(sK4)) & (~r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) = k1_tarski(sK4))),
% 3.24/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f42,f43])).
% 3.24/1.04  
% 3.24/1.04  fof(f81,plain,(
% 3.24/1.04    r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) != k1_tarski(sK4)),
% 3.24/1.04    inference(cnf_transformation,[],[f44])).
% 3.24/1.04  
% 3.24/1.04  fof(f10,axiom,(
% 3.24/1.04    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.24/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.04  
% 3.24/1.04  fof(f75,plain,(
% 3.24/1.04    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.24/1.04    inference(cnf_transformation,[],[f10])).
% 3.24/1.04  
% 3.24/1.04  fof(f11,axiom,(
% 3.24/1.04    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.24/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.04  
% 3.24/1.04  fof(f76,plain,(
% 3.24/1.04    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.24/1.04    inference(cnf_transformation,[],[f11])).
% 3.24/1.04  
% 3.24/1.04  fof(f82,plain,(
% 3.24/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.24/1.04    inference(definition_unfolding,[],[f76,f77])).
% 3.24/1.04  
% 3.24/1.04  fof(f83,plain,(
% 3.24/1.04    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.24/1.04    inference(definition_unfolding,[],[f75,f82])).
% 3.24/1.04  
% 3.24/1.04  fof(f102,plain,(
% 3.24/1.04    r2_hidden(sK4,sK5) | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) != k2_enumset1(sK4,sK4,sK4,sK4)),
% 3.24/1.04    inference(definition_unfolding,[],[f81,f83,f83])).
% 3.24/1.04  
% 3.24/1.04  fof(f68,plain,(
% 3.24/1.04    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.24/1.04    inference(cnf_transformation,[],[f40])).
% 3.24/1.04  
% 3.24/1.04  fof(f98,plain,(
% 3.24/1.04    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.24/1.04    inference(definition_unfolding,[],[f68,f77])).
% 3.24/1.04  
% 3.24/1.04  fof(f116,plain,(
% 3.24/1.04    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 3.24/1.04    inference(equality_resolution,[],[f98])).
% 3.24/1.04  
% 3.24/1.04  fof(f117,plain,(
% 3.24/1.04    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 3.24/1.04    inference(equality_resolution,[],[f116])).
% 3.24/1.04  
% 3.24/1.04  fof(f13,axiom,(
% 3.24/1.04    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.24/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.24/1.04  
% 3.24/1.04  fof(f41,plain,(
% 3.24/1.04    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 3.24/1.04    inference(nnf_transformation,[],[f13])).
% 3.24/1.04  
% 3.24/1.04  fof(f78,plain,(
% 3.24/1.04    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 3.24/1.04    inference(cnf_transformation,[],[f41])).
% 3.24/1.04  
% 3.24/1.04  fof(f101,plain,(
% 3.24/1.04    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0) )),
% 3.24/1.04    inference(definition_unfolding,[],[f78,f83])).
% 3.24/1.04  
% 3.24/1.04  fof(f79,plain,(
% 3.24/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 3.24/1.04    inference(cnf_transformation,[],[f41])).
% 3.24/1.04  
% 3.24/1.04  fof(f100,plain,(
% 3.24/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 3.24/1.04    inference(definition_unfolding,[],[f79,f83])).
% 3.24/1.04  
% 3.24/1.04  fof(f80,plain,(
% 3.24/1.04    ~r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) = k1_tarski(sK4)),
% 3.24/1.04    inference(cnf_transformation,[],[f44])).
% 3.24/1.04  
% 3.24/1.04  fof(f103,plain,(
% 3.24/1.04    ~r2_hidden(sK4,sK5) | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(sK4,sK4,sK4,sK4)),
% 3.24/1.04    inference(definition_unfolding,[],[f80,f83,f83])).
% 3.24/1.04  
% 3.24/1.04  fof(f57,plain,(
% 3.24/1.04    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.24/1.04    inference(cnf_transformation,[],[f33])).
% 3.24/1.04  
% 3.24/1.04  fof(f108,plain,(
% 3.24/1.04    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.24/1.04    inference(equality_resolution,[],[f57])).
% 3.24/1.04  
% 3.24/1.04  fof(f61,plain,(
% 3.24/1.04    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.24/1.04    inference(cnf_transformation,[],[f33])).
% 3.24/1.04  
% 3.24/1.04  cnf(c_551,plain,
% 3.24/1.04      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.24/1.04      theory(equality) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_1878,plain,
% 3.24/1.04      ( r2_hidden(X0,X1)
% 3.24/1.04      | ~ r2_hidden(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5)
% 3.24/1.04      | X0 != sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4))
% 3.24/1.04      | X1 != sK5 ),
% 3.24/1.04      inference(instantiation,[status(thm)],[c_551]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_10429,plain,
% 3.24/1.04      ( r2_hidden(X0,k4_xboole_0(sK5,k2_enumset1(X1,X1,X1,X1)))
% 3.24/1.04      | ~ r2_hidden(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5)
% 3.24/1.04      | X0 != sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4))
% 3.24/1.04      | k4_xboole_0(sK5,k2_enumset1(X1,X1,X1,X1)) != sK5 ),
% 3.24/1.04      inference(instantiation,[status(thm)],[c_1878]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_10432,plain,
% 3.24/1.04      ( ~ r2_hidden(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5)
% 3.24/1.04      | r2_hidden(sK4,k4_xboole_0(sK5,k2_enumset1(sK4,sK4,sK4,sK4)))
% 3.24/1.04      | k4_xboole_0(sK5,k2_enumset1(sK4,sK4,sK4,sK4)) != sK5
% 3.24/1.04      | sK4 != sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 3.24/1.04      inference(instantiation,[status(thm)],[c_10429]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_548,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_5862,plain,
% 3.24/1.04      ( X0 != X1
% 3.24/1.04      | X0 = sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4))
% 3.24/1.04      | sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) != X1 ),
% 3.24/1.04      inference(instantiation,[status(thm)],[c_548]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_5863,plain,
% 3.24/1.04      ( sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) != sK4
% 3.24/1.04      | sK4 = sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4))
% 3.24/1.04      | sK4 != sK4 ),
% 3.24/1.04      inference(instantiation,[status(thm)],[c_5862]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_28,plain,
% 3.24/1.04      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 3.24/1.04      | X0 = X1
% 3.24/1.04      | X0 = X2
% 3.24/1.04      | X0 = X3 ),
% 3.24/1.04      inference(cnf_transformation,[],[f118]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_14,plain,
% 3.24/1.04      ( r2_hidden(sK2(X0,X1,X2),X0)
% 3.24/1.04      | r2_hidden(sK2(X0,X1,X2),X2)
% 3.24/1.04      | k4_xboole_0(X0,X1) = X2 ),
% 3.24/1.04      inference(cnf_transformation,[],[f59]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_31,negated_conjecture,
% 3.24/1.04      ( r2_hidden(sK4,sK5)
% 3.24/1.04      | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 3.24/1.04      inference(cnf_transformation,[],[f102]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_3257,plain,
% 3.24/1.04      ( r2_hidden(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 3.24/1.04      | r2_hidden(sK4,sK5) ),
% 3.24/1.04      inference(resolution,[status(thm)],[c_14,c_31]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_42,plain,
% 3.24/1.04      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) | sK4 = sK4 ),
% 3.24/1.04      inference(instantiation,[status(thm)],[c_28]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_27,plain,
% 3.24/1.04      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 3.24/1.04      inference(cnf_transformation,[],[f117]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_45,plain,
% 3.24/1.04      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 3.24/1.04      inference(instantiation,[status(thm)],[c_27]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_1541,plain,
% 3.24/1.04      ( r2_hidden(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 3.24/1.04      | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 3.24/1.04      inference(instantiation,[status(thm)],[c_14]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_30,plain,
% 3.24/1.04      ( ~ r2_hidden(X0,X1)
% 3.24/1.04      | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) != X1 ),
% 3.24/1.04      inference(cnf_transformation,[],[f101]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_1603,plain,
% 3.24/1.04      ( ~ r2_hidden(sK4,sK5)
% 3.24/1.04      | k4_xboole_0(sK5,k2_enumset1(sK4,sK4,sK4,sK4)) != sK5 ),
% 3.24/1.04      inference(instantiation,[status(thm)],[c_30]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_29,plain,
% 3.24/1.04      ( r2_hidden(X0,X1)
% 3.24/1.04      | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
% 3.24/1.04      inference(cnf_transformation,[],[f100]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_1153,plain,
% 3.24/1.04      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
% 3.24/1.04      | r2_hidden(X1,X0) = iProver_top ),
% 3.24/1.04      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_32,negated_conjecture,
% 3.24/1.04      ( ~ r2_hidden(sK4,sK5)
% 3.24/1.04      | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 3.24/1.04      inference(cnf_transformation,[],[f103]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_1150,plain,
% 3.24/1.04      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(sK4,sK4,sK4,sK4)
% 3.24/1.04      | r2_hidden(sK4,sK5) != iProver_top ),
% 3.24/1.04      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_2179,plain,
% 3.24/1.04      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(sK4,sK4,sK4,sK4)
% 3.24/1.04      | k4_xboole_0(sK5,k2_enumset1(sK4,sK4,sK4,sK4)) = sK5 ),
% 3.24/1.04      inference(superposition,[status(thm)],[c_1153,c_1150]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_1535,plain,
% 3.24/1.04      ( r2_hidden(X0,X1)
% 3.24/1.04      | ~ r2_hidden(X2,k2_enumset1(X3,X3,X2,X4))
% 3.24/1.04      | X0 != X2
% 3.24/1.04      | X1 != k2_enumset1(X3,X3,X2,X4) ),
% 3.24/1.04      inference(instantiation,[status(thm)],[c_551]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_2470,plain,
% 3.24/1.04      ( r2_hidden(X0,k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5))
% 3.24/1.04      | ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
% 3.24/1.04      | X0 != sK4
% 3.24/1.04      | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 3.24/1.04      inference(instantiation,[status(thm)],[c_1535]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_2472,plain,
% 3.24/1.04      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
% 3.24/1.04      | r2_hidden(sK4,k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5))
% 3.24/1.04      | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) != k2_enumset1(sK4,sK4,sK4,sK4)
% 3.24/1.04      | sK4 != sK4 ),
% 3.24/1.04      inference(instantiation,[status(thm)],[c_2470]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_2579,plain,
% 3.24/1.04      ( r2_hidden(sK4,sK5)
% 3.24/1.04      | k4_xboole_0(sK5,k2_enumset1(sK4,sK4,sK4,sK4)) = sK5 ),
% 3.24/1.04      inference(instantiation,[status(thm)],[c_29]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_16,plain,
% 3.24/1.04      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.24/1.04      inference(cnf_transformation,[],[f108]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_1605,plain,
% 3.24/1.04      ( ~ r2_hidden(sK4,k4_xboole_0(X0,sK5)) | ~ r2_hidden(sK4,sK5) ),
% 3.24/1.04      inference(instantiation,[status(thm)],[c_16]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_2584,plain,
% 3.24/1.04      ( ~ r2_hidden(sK4,k4_xboole_0(k2_enumset1(X0,X0,X1,sK4),sK5))
% 3.24/1.04      | ~ r2_hidden(sK4,sK5) ),
% 3.24/1.04      inference(instantiation,[status(thm)],[c_1605]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_2587,plain,
% 3.24/1.04      ( ~ r2_hidden(sK4,k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5))
% 3.24/1.04      | ~ r2_hidden(sK4,sK5) ),
% 3.24/1.04      inference(instantiation,[status(thm)],[c_2584]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_3364,plain,
% 3.24/1.04      ( r2_hidden(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 3.24/1.04      inference(global_propositional_subsumption,
% 3.24/1.04                [status(thm)],
% 3.24/1.04                [c_3257,c_31,c_42,c_45,c_1541,c_1603,c_2179,c_2472,
% 3.24/1.04                 c_2579,c_2587]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_5666,plain,
% 3.24/1.04      ( sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) = sK4 ),
% 3.24/1.04      inference(resolution,[status(thm)],[c_28,c_3364]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_1411,plain,
% 3.24/1.04      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
% 3.24/1.04      | ~ r2_hidden(X0,k4_xboole_0(X3,k2_enumset1(X1,X1,X2,X0))) ),
% 3.24/1.04      inference(instantiation,[status(thm)],[c_16]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_2661,plain,
% 3.24/1.04      ( ~ r2_hidden(sK4,k2_enumset1(X0,X0,X1,sK4))
% 3.24/1.04      | ~ r2_hidden(sK4,k4_xboole_0(sK5,k2_enumset1(X0,X0,X1,sK4))) ),
% 3.24/1.04      inference(instantiation,[status(thm)],[c_1411]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_2665,plain,
% 3.24/1.04      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
% 3.24/1.04      | ~ r2_hidden(sK4,k4_xboole_0(sK5,k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 3.24/1.04      inference(instantiation,[status(thm)],[c_2661]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_12,plain,
% 3.24/1.04      ( ~ r2_hidden(sK2(X0,X1,X2),X0)
% 3.24/1.04      | ~ r2_hidden(sK2(X0,X1,X2),X2)
% 3.24/1.04      | r2_hidden(sK2(X0,X1,X2),X1)
% 3.24/1.04      | k4_xboole_0(X0,X1) = X2 ),
% 3.24/1.04      inference(cnf_transformation,[],[f61]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(c_1569,plain,
% 3.24/1.04      ( ~ r2_hidden(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 3.24/1.04      | r2_hidden(sK2(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5)
% 3.24/1.04      | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 3.24/1.04      inference(instantiation,[status(thm)],[c_12]) ).
% 3.24/1.04  
% 3.24/1.04  cnf(contradiction,plain,
% 3.24/1.04      ( $false ),
% 3.24/1.04      inference(minisat,
% 3.24/1.04                [status(thm)],
% 3.24/1.04                [c_10432,c_5863,c_5666,c_2665,c_2587,c_2579,c_2472,
% 3.24/1.04                 c_2179,c_1603,c_1569,c_1541,c_45,c_42,c_31]) ).
% 3.24/1.04  
% 3.24/1.04  
% 3.24/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 3.24/1.04  
% 3.24/1.04  ------                               Statistics
% 3.24/1.04  
% 3.24/1.04  ------ Selected
% 3.24/1.04  
% 3.24/1.04  total_time:                             0.449
% 3.24/1.04  
%------------------------------------------------------------------------------
