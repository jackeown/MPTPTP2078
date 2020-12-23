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
% DateTime   : Thu Dec  3 11:32:28 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  134 (1271 expanded)
%              Number of clauses        :   54 (  98 expanded)
%              Number of leaves         :   22 ( 395 expanded)
%              Depth                    :   20
%              Number of atoms          :  422 (2559 expanded)
%              Number of equality atoms :  271 (2120 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f27])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK5
        | k1_tarski(sK3) != sK4 )
      & ( k1_tarski(sK3) != sK5
        | k1_xboole_0 != sK4 )
      & ( k1_tarski(sK3) != sK5
        | k1_tarski(sK3) != sK4 )
      & k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( k1_xboole_0 != sK5
      | k1_tarski(sK3) != sK4 )
    & ( k1_tarski(sK3) != sK5
      | k1_xboole_0 != sK4 )
    & ( k1_tarski(sK3) != sK5
      | k1_tarski(sK3) != sK4 )
    & k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f21,f38])).

fof(f70,plain,(
    k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f66,f78])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f60,f74])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f59,f75])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f76])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f77])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f78])).

fof(f104,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
    inference(definition_unfolding,[],[f70,f79,f80])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f88,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f49,f79])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f79])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f41,f79])).

fof(f106,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f50,f78])).

fof(f112,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f94])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK2(X0,X1,X2) != X0
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
      | sK2(X0,X1,X2) != X0
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f54,f78])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f42,f79])).

fof(f105,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f84])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK2(X0,X1,X2) = X1
      | sK2(X0,X1,X2) = X0
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
      | sK2(X0,X1,X2) = X1
      | sK2(X0,X1,X2) = X0
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f53,f78])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f34])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f63,f80,f80])).

fof(f73,plain,
    ( k1_xboole_0 != sK5
    | k1_tarski(sK3) != sK4 ),
    inference(cnf_transformation,[],[f39])).

fof(f101,plain,
    ( k1_xboole_0 != sK5
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4 ),
    inference(definition_unfolding,[],[f73,f80])).

fof(f71,plain,
    ( k1_tarski(sK3) != sK5
    | k1_tarski(sK3) != sK4 ),
    inference(cnf_transformation,[],[f39])).

fof(f103,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4 ),
    inference(definition_unfolding,[],[f71,f80,f80])).

fof(f72,plain,
    ( k1_tarski(sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f39])).

fof(f102,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(definition_unfolding,[],[f72,f80])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_760,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_25,negated_conjecture,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_9,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_757,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1069,plain,
    ( r1_tarski(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_757])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_759,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1334,plain,
    ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_1069,c_759])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_762,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1669,plain,
    ( r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1334,c_762])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_751,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1923,plain,
    ( sK3 = X0
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1669,c_751])).

cnf(c_2582,plain,
    ( sK1(sK4) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_760,c_1923])).

cnf(c_11,plain,
    ( ~ r2_hidden(sK2(X0,X1,X2),X2)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
    | sK2(X0,X1,X2) != X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_845,plain,
    ( ~ r2_hidden(sK2(sK3,sK3,sK5),sK5)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
    | sK2(sK3,sK3,sK5) != sK3 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_763,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1777,plain,
    ( r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_763])).

cnf(c_1922,plain,
    ( sK3 = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1777,c_751])).

cnf(c_2289,plain,
    ( sK1(sK5) = sK3
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_760,c_1922])).

cnf(c_2374,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2289,c_760])).

cnf(c_2375,plain,
    ( r2_hidden(sK3,sK5)
    | sK5 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2374])).

cnf(c_12,plain,
    ( r2_hidden(sK2(X0,X1,X2),X2)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
    | sK2(X0,X1,X2) = X1
    | sK2(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_754,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
    | sK2(X0,X1,X2) = X1
    | sK2(X0,X1,X2) = X0
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3213,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = sK5
    | sK2(X0,X1,sK5) = X1
    | sK2(X0,X1,sK5) = X0
    | sK2(X0,X1,sK5) = sK3 ),
    inference(superposition,[status(thm)],[c_754,c_1922])).

cnf(c_3223,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
    | sK2(sK3,sK3,sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_3213])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_748,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2829,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1069,c_748])).

cnf(c_22,negated_conjecture,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3462,plain,
    ( sK4 = k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2829,c_22])).

cnf(c_24,negated_conjecture,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3460,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2829,c_24])).

cnf(c_23,negated_conjecture,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_803,plain,
    ( ~ r1_tarski(sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK4
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_808,plain,
    ( ~ r1_tarski(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_1070,plain,
    ( r1_tarski(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1069])).

cnf(c_3950,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3460,c_24,c_23,c_808,c_1070])).

cnf(c_411,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3971,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_411])).

cnf(c_415,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2637,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2(sK3,sK3,sK5),sK5)
    | sK2(sK3,sK3,sK5) != X0
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_4185,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK2(sK3,sK3,sK5),sK5)
    | sK2(sK3,sK3,sK5) != X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2637])).

cnf(c_4187,plain,
    ( r2_hidden(sK2(sK3,sK3,sK5),sK5)
    | ~ r2_hidden(sK3,sK5)
    | sK2(sK3,sK3,sK5) != sK3
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_4185])).

cnf(c_4353,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2582,c_24,c_23,c_808,c_845,c_1070,c_2375,c_3223,c_3462,c_3971,c_4187])).

cnf(c_4365,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK5)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_4353,c_25])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_758,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1332,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_758,c_759])).

cnf(c_4367,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5 ),
    inference(demodulation,[status(thm)],[c_4365,c_1332])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4367,c_3950])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:40:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.59/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.00  
% 3.59/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.59/1.00  
% 3.59/1.00  ------  iProver source info
% 3.59/1.00  
% 3.59/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.59/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.59/1.00  git: non_committed_changes: false
% 3.59/1.00  git: last_make_outside_of_git: false
% 3.59/1.00  
% 3.59/1.00  ------ 
% 3.59/1.00  
% 3.59/1.00  ------ Input Options
% 3.59/1.00  
% 3.59/1.00  --out_options                           all
% 3.59/1.00  --tptp_safe_out                         true
% 3.59/1.00  --problem_path                          ""
% 3.59/1.00  --include_path                          ""
% 3.59/1.00  --clausifier                            res/vclausify_rel
% 3.59/1.00  --clausifier_options                    ""
% 3.59/1.00  --stdin                                 false
% 3.59/1.00  --stats_out                             all
% 3.59/1.00  
% 3.59/1.00  ------ General Options
% 3.59/1.00  
% 3.59/1.00  --fof                                   false
% 3.59/1.00  --time_out_real                         305.
% 3.59/1.00  --time_out_virtual                      -1.
% 3.59/1.00  --symbol_type_check                     false
% 3.59/1.00  --clausify_out                          false
% 3.59/1.00  --sig_cnt_out                           false
% 3.59/1.00  --trig_cnt_out                          false
% 3.59/1.00  --trig_cnt_out_tolerance                1.
% 3.59/1.00  --trig_cnt_out_sk_spl                   false
% 3.59/1.00  --abstr_cl_out                          false
% 3.59/1.00  
% 3.59/1.00  ------ Global Options
% 3.59/1.00  
% 3.59/1.00  --schedule                              default
% 3.59/1.00  --add_important_lit                     false
% 3.59/1.00  --prop_solver_per_cl                    1000
% 3.59/1.00  --min_unsat_core                        false
% 3.59/1.00  --soft_assumptions                      false
% 3.59/1.00  --soft_lemma_size                       3
% 3.59/1.00  --prop_impl_unit_size                   0
% 3.59/1.00  --prop_impl_unit                        []
% 3.59/1.00  --share_sel_clauses                     true
% 3.59/1.00  --reset_solvers                         false
% 3.59/1.00  --bc_imp_inh                            [conj_cone]
% 3.59/1.00  --conj_cone_tolerance                   3.
% 3.59/1.00  --extra_neg_conj                        none
% 3.59/1.00  --large_theory_mode                     true
% 3.59/1.00  --prolific_symb_bound                   200
% 3.59/1.00  --lt_threshold                          2000
% 3.59/1.00  --clause_weak_htbl                      true
% 3.59/1.00  --gc_record_bc_elim                     false
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing Options
% 3.59/1.00  
% 3.59/1.00  --preprocessing_flag                    true
% 3.59/1.00  --time_out_prep_mult                    0.1
% 3.59/1.00  --splitting_mode                        input
% 3.59/1.00  --splitting_grd                         true
% 3.59/1.00  --splitting_cvd                         false
% 3.59/1.00  --splitting_cvd_svl                     false
% 3.59/1.00  --splitting_nvd                         32
% 3.59/1.00  --sub_typing                            true
% 3.59/1.00  --prep_gs_sim                           true
% 3.59/1.00  --prep_unflatten                        true
% 3.59/1.00  --prep_res_sim                          true
% 3.59/1.00  --prep_upred                            true
% 3.59/1.00  --prep_sem_filter                       exhaustive
% 3.59/1.00  --prep_sem_filter_out                   false
% 3.59/1.00  --pred_elim                             true
% 3.59/1.00  --res_sim_input                         true
% 3.59/1.00  --eq_ax_congr_red                       true
% 3.59/1.00  --pure_diseq_elim                       true
% 3.59/1.00  --brand_transform                       false
% 3.59/1.00  --non_eq_to_eq                          false
% 3.59/1.00  --prep_def_merge                        true
% 3.59/1.00  --prep_def_merge_prop_impl              false
% 3.59/1.00  --prep_def_merge_mbd                    true
% 3.59/1.00  --prep_def_merge_tr_red                 false
% 3.59/1.00  --prep_def_merge_tr_cl                  false
% 3.59/1.00  --smt_preprocessing                     true
% 3.59/1.00  --smt_ac_axioms                         fast
% 3.59/1.00  --preprocessed_out                      false
% 3.59/1.00  --preprocessed_stats                    false
% 3.59/1.00  
% 3.59/1.00  ------ Abstraction refinement Options
% 3.59/1.00  
% 3.59/1.00  --abstr_ref                             []
% 3.59/1.00  --abstr_ref_prep                        false
% 3.59/1.00  --abstr_ref_until_sat                   false
% 3.59/1.00  --abstr_ref_sig_restrict                funpre
% 3.59/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/1.00  --abstr_ref_under                       []
% 3.59/1.00  
% 3.59/1.00  ------ SAT Options
% 3.59/1.00  
% 3.59/1.00  --sat_mode                              false
% 3.59/1.00  --sat_fm_restart_options                ""
% 3.59/1.00  --sat_gr_def                            false
% 3.59/1.00  --sat_epr_types                         true
% 3.59/1.00  --sat_non_cyclic_types                  false
% 3.59/1.00  --sat_finite_models                     false
% 3.59/1.00  --sat_fm_lemmas                         false
% 3.59/1.00  --sat_fm_prep                           false
% 3.59/1.00  --sat_fm_uc_incr                        true
% 3.59/1.00  --sat_out_model                         small
% 3.59/1.00  --sat_out_clauses                       false
% 3.59/1.00  
% 3.59/1.00  ------ QBF Options
% 3.59/1.00  
% 3.59/1.00  --qbf_mode                              false
% 3.59/1.00  --qbf_elim_univ                         false
% 3.59/1.00  --qbf_dom_inst                          none
% 3.59/1.00  --qbf_dom_pre_inst                      false
% 3.59/1.00  --qbf_sk_in                             false
% 3.59/1.00  --qbf_pred_elim                         true
% 3.59/1.00  --qbf_split                             512
% 3.59/1.00  
% 3.59/1.00  ------ BMC1 Options
% 3.59/1.00  
% 3.59/1.00  --bmc1_incremental                      false
% 3.59/1.00  --bmc1_axioms                           reachable_all
% 3.59/1.00  --bmc1_min_bound                        0
% 3.59/1.00  --bmc1_max_bound                        -1
% 3.59/1.00  --bmc1_max_bound_default                -1
% 3.59/1.00  --bmc1_symbol_reachability              true
% 3.59/1.00  --bmc1_property_lemmas                  false
% 3.59/1.00  --bmc1_k_induction                      false
% 3.59/1.00  --bmc1_non_equiv_states                 false
% 3.59/1.00  --bmc1_deadlock                         false
% 3.59/1.00  --bmc1_ucm                              false
% 3.59/1.00  --bmc1_add_unsat_core                   none
% 3.59/1.00  --bmc1_unsat_core_children              false
% 3.59/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/1.00  --bmc1_out_stat                         full
% 3.59/1.00  --bmc1_ground_init                      false
% 3.59/1.00  --bmc1_pre_inst_next_state              false
% 3.59/1.00  --bmc1_pre_inst_state                   false
% 3.59/1.00  --bmc1_pre_inst_reach_state             false
% 3.59/1.00  --bmc1_out_unsat_core                   false
% 3.59/1.00  --bmc1_aig_witness_out                  false
% 3.59/1.00  --bmc1_verbose                          false
% 3.59/1.00  --bmc1_dump_clauses_tptp                false
% 3.59/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.59/1.00  --bmc1_dump_file                        -
% 3.59/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.59/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.59/1.00  --bmc1_ucm_extend_mode                  1
% 3.59/1.00  --bmc1_ucm_init_mode                    2
% 3.59/1.00  --bmc1_ucm_cone_mode                    none
% 3.59/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.59/1.00  --bmc1_ucm_relax_model                  4
% 3.59/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.59/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/1.00  --bmc1_ucm_layered_model                none
% 3.59/1.00  --bmc1_ucm_max_lemma_size               10
% 3.59/1.00  
% 3.59/1.00  ------ AIG Options
% 3.59/1.00  
% 3.59/1.00  --aig_mode                              false
% 3.59/1.00  
% 3.59/1.00  ------ Instantiation Options
% 3.59/1.00  
% 3.59/1.00  --instantiation_flag                    true
% 3.59/1.00  --inst_sos_flag                         true
% 3.59/1.00  --inst_sos_phase                        true
% 3.59/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/1.00  --inst_lit_sel_side                     num_symb
% 3.59/1.00  --inst_solver_per_active                1400
% 3.59/1.00  --inst_solver_calls_frac                1.
% 3.59/1.00  --inst_passive_queue_type               priority_queues
% 3.59/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/1.00  --inst_passive_queues_freq              [25;2]
% 3.59/1.00  --inst_dismatching                      true
% 3.59/1.00  --inst_eager_unprocessed_to_passive     true
% 3.59/1.00  --inst_prop_sim_given                   true
% 3.59/1.00  --inst_prop_sim_new                     false
% 3.59/1.00  --inst_subs_new                         false
% 3.59/1.00  --inst_eq_res_simp                      false
% 3.59/1.00  --inst_subs_given                       false
% 3.59/1.00  --inst_orphan_elimination               true
% 3.59/1.00  --inst_learning_loop_flag               true
% 3.59/1.00  --inst_learning_start                   3000
% 3.59/1.00  --inst_learning_factor                  2
% 3.59/1.00  --inst_start_prop_sim_after_learn       3
% 3.59/1.00  --inst_sel_renew                        solver
% 3.59/1.00  --inst_lit_activity_flag                true
% 3.59/1.00  --inst_restr_to_given                   false
% 3.59/1.00  --inst_activity_threshold               500
% 3.59/1.00  --inst_out_proof                        true
% 3.59/1.00  
% 3.59/1.00  ------ Resolution Options
% 3.59/1.00  
% 3.59/1.00  --resolution_flag                       true
% 3.59/1.00  --res_lit_sel                           adaptive
% 3.59/1.00  --res_lit_sel_side                      none
% 3.59/1.00  --res_ordering                          kbo
% 3.59/1.00  --res_to_prop_solver                    active
% 3.59/1.00  --res_prop_simpl_new                    false
% 3.59/1.00  --res_prop_simpl_given                  true
% 3.59/1.00  --res_passive_queue_type                priority_queues
% 3.59/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/1.01  --res_passive_queues_freq               [15;5]
% 3.59/1.01  --res_forward_subs                      full
% 3.59/1.01  --res_backward_subs                     full
% 3.59/1.01  --res_forward_subs_resolution           true
% 3.59/1.01  --res_backward_subs_resolution          true
% 3.59/1.01  --res_orphan_elimination                true
% 3.59/1.01  --res_time_limit                        2.
% 3.59/1.01  --res_out_proof                         true
% 3.59/1.01  
% 3.59/1.01  ------ Superposition Options
% 3.59/1.01  
% 3.59/1.01  --superposition_flag                    true
% 3.59/1.01  --sup_passive_queue_type                priority_queues
% 3.59/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.59/1.01  --demod_completeness_check              fast
% 3.59/1.01  --demod_use_ground                      true
% 3.59/1.01  --sup_to_prop_solver                    passive
% 3.59/1.01  --sup_prop_simpl_new                    true
% 3.59/1.01  --sup_prop_simpl_given                  true
% 3.59/1.01  --sup_fun_splitting                     true
% 3.59/1.01  --sup_smt_interval                      50000
% 3.59/1.01  
% 3.59/1.01  ------ Superposition Simplification Setup
% 3.59/1.01  
% 3.59/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.59/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.59/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.59/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.59/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.59/1.01  --sup_immed_triv                        [TrivRules]
% 3.59/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/1.01  --sup_immed_bw_main                     []
% 3.59/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.59/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/1.01  --sup_input_bw                          []
% 3.59/1.01  
% 3.59/1.01  ------ Combination Options
% 3.59/1.01  
% 3.59/1.01  --comb_res_mult                         3
% 3.59/1.01  --comb_sup_mult                         2
% 3.59/1.01  --comb_inst_mult                        10
% 3.59/1.01  
% 3.59/1.01  ------ Debug Options
% 3.59/1.01  
% 3.59/1.01  --dbg_backtrace                         false
% 3.59/1.01  --dbg_dump_prop_clauses                 false
% 3.59/1.01  --dbg_dump_prop_clauses_file            -
% 3.59/1.01  --dbg_out_stat                          false
% 3.59/1.01  ------ Parsing...
% 3.59/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.59/1.01  
% 3.59/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.59/1.01  
% 3.59/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.59/1.01  
% 3.59/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.59/1.01  ------ Proving...
% 3.59/1.01  ------ Problem Properties 
% 3.59/1.01  
% 3.59/1.01  
% 3.59/1.01  clauses                                 26
% 3.59/1.01  conjectures                             4
% 3.59/1.01  EPR                                     1
% 3.59/1.01  Horn                                    20
% 3.59/1.01  unary                                   7
% 3.59/1.01  binary                                  9
% 3.59/1.01  lits                                    57
% 3.59/1.01  lits eq                                 23
% 3.59/1.01  fd_pure                                 0
% 3.59/1.01  fd_pseudo                               0
% 3.59/1.01  fd_cond                                 1
% 3.59/1.01  fd_pseudo_cond                          7
% 3.59/1.01  AC symbols                              0
% 3.59/1.01  
% 3.59/1.01  ------ Schedule dynamic 5 is on 
% 3.59/1.01  
% 3.59/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.59/1.01  
% 3.59/1.01  
% 3.59/1.01  ------ 
% 3.59/1.01  Current options:
% 3.59/1.01  ------ 
% 3.59/1.01  
% 3.59/1.01  ------ Input Options
% 3.59/1.01  
% 3.59/1.01  --out_options                           all
% 3.59/1.01  --tptp_safe_out                         true
% 3.59/1.01  --problem_path                          ""
% 3.59/1.01  --include_path                          ""
% 3.59/1.01  --clausifier                            res/vclausify_rel
% 3.59/1.01  --clausifier_options                    ""
% 3.59/1.01  --stdin                                 false
% 3.59/1.01  --stats_out                             all
% 3.59/1.01  
% 3.59/1.01  ------ General Options
% 3.59/1.01  
% 3.59/1.01  --fof                                   false
% 3.59/1.01  --time_out_real                         305.
% 3.59/1.01  --time_out_virtual                      -1.
% 3.59/1.01  --symbol_type_check                     false
% 3.59/1.01  --clausify_out                          false
% 3.59/1.01  --sig_cnt_out                           false
% 3.59/1.01  --trig_cnt_out                          false
% 3.59/1.01  --trig_cnt_out_tolerance                1.
% 3.59/1.01  --trig_cnt_out_sk_spl                   false
% 3.59/1.01  --abstr_cl_out                          false
% 3.59/1.01  
% 3.59/1.01  ------ Global Options
% 3.59/1.01  
% 3.59/1.01  --schedule                              default
% 3.59/1.01  --add_important_lit                     false
% 3.59/1.01  --prop_solver_per_cl                    1000
% 3.59/1.01  --min_unsat_core                        false
% 3.59/1.01  --soft_assumptions                      false
% 3.59/1.01  --soft_lemma_size                       3
% 3.59/1.01  --prop_impl_unit_size                   0
% 3.59/1.01  --prop_impl_unit                        []
% 3.59/1.01  --share_sel_clauses                     true
% 3.59/1.01  --reset_solvers                         false
% 3.59/1.01  --bc_imp_inh                            [conj_cone]
% 3.59/1.01  --conj_cone_tolerance                   3.
% 3.59/1.01  --extra_neg_conj                        none
% 3.59/1.01  --large_theory_mode                     true
% 3.59/1.01  --prolific_symb_bound                   200
% 3.59/1.01  --lt_threshold                          2000
% 3.59/1.01  --clause_weak_htbl                      true
% 3.59/1.01  --gc_record_bc_elim                     false
% 3.59/1.01  
% 3.59/1.01  ------ Preprocessing Options
% 3.59/1.01  
% 3.59/1.01  --preprocessing_flag                    true
% 3.59/1.01  --time_out_prep_mult                    0.1
% 3.59/1.01  --splitting_mode                        input
% 3.59/1.01  --splitting_grd                         true
% 3.59/1.01  --splitting_cvd                         false
% 3.59/1.01  --splitting_cvd_svl                     false
% 3.59/1.01  --splitting_nvd                         32
% 3.59/1.01  --sub_typing                            true
% 3.59/1.01  --prep_gs_sim                           true
% 3.59/1.01  --prep_unflatten                        true
% 3.59/1.01  --prep_res_sim                          true
% 3.59/1.01  --prep_upred                            true
% 3.59/1.01  --prep_sem_filter                       exhaustive
% 3.59/1.01  --prep_sem_filter_out                   false
% 3.59/1.01  --pred_elim                             true
% 3.59/1.01  --res_sim_input                         true
% 3.59/1.01  --eq_ax_congr_red                       true
% 3.59/1.01  --pure_diseq_elim                       true
% 3.59/1.01  --brand_transform                       false
% 3.59/1.01  --non_eq_to_eq                          false
% 3.59/1.01  --prep_def_merge                        true
% 3.59/1.01  --prep_def_merge_prop_impl              false
% 3.59/1.01  --prep_def_merge_mbd                    true
% 3.59/1.01  --prep_def_merge_tr_red                 false
% 3.59/1.01  --prep_def_merge_tr_cl                  false
% 3.59/1.01  --smt_preprocessing                     true
% 3.59/1.01  --smt_ac_axioms                         fast
% 3.59/1.01  --preprocessed_out                      false
% 3.59/1.01  --preprocessed_stats                    false
% 3.59/1.01  
% 3.59/1.01  ------ Abstraction refinement Options
% 3.59/1.01  
% 3.59/1.01  --abstr_ref                             []
% 3.59/1.01  --abstr_ref_prep                        false
% 3.59/1.01  --abstr_ref_until_sat                   false
% 3.59/1.01  --abstr_ref_sig_restrict                funpre
% 3.59/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/1.01  --abstr_ref_under                       []
% 3.59/1.01  
% 3.59/1.01  ------ SAT Options
% 3.59/1.01  
% 3.59/1.01  --sat_mode                              false
% 3.59/1.01  --sat_fm_restart_options                ""
% 3.59/1.01  --sat_gr_def                            false
% 3.59/1.01  --sat_epr_types                         true
% 3.59/1.01  --sat_non_cyclic_types                  false
% 3.59/1.01  --sat_finite_models                     false
% 3.59/1.01  --sat_fm_lemmas                         false
% 3.59/1.01  --sat_fm_prep                           false
% 3.59/1.01  --sat_fm_uc_incr                        true
% 3.59/1.01  --sat_out_model                         small
% 3.59/1.01  --sat_out_clauses                       false
% 3.59/1.01  
% 3.59/1.01  ------ QBF Options
% 3.59/1.01  
% 3.59/1.01  --qbf_mode                              false
% 3.59/1.01  --qbf_elim_univ                         false
% 3.59/1.01  --qbf_dom_inst                          none
% 3.59/1.01  --qbf_dom_pre_inst                      false
% 3.59/1.01  --qbf_sk_in                             false
% 3.59/1.01  --qbf_pred_elim                         true
% 3.59/1.01  --qbf_split                             512
% 3.59/1.01  
% 3.59/1.01  ------ BMC1 Options
% 3.59/1.01  
% 3.59/1.01  --bmc1_incremental                      false
% 3.59/1.01  --bmc1_axioms                           reachable_all
% 3.59/1.01  --bmc1_min_bound                        0
% 3.59/1.01  --bmc1_max_bound                        -1
% 3.59/1.01  --bmc1_max_bound_default                -1
% 3.59/1.01  --bmc1_symbol_reachability              true
% 3.59/1.01  --bmc1_property_lemmas                  false
% 3.59/1.01  --bmc1_k_induction                      false
% 3.59/1.01  --bmc1_non_equiv_states                 false
% 3.59/1.01  --bmc1_deadlock                         false
% 3.59/1.01  --bmc1_ucm                              false
% 3.59/1.01  --bmc1_add_unsat_core                   none
% 3.59/1.01  --bmc1_unsat_core_children              false
% 3.59/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/1.01  --bmc1_out_stat                         full
% 3.59/1.01  --bmc1_ground_init                      false
% 3.59/1.01  --bmc1_pre_inst_next_state              false
% 3.59/1.01  --bmc1_pre_inst_state                   false
% 3.59/1.01  --bmc1_pre_inst_reach_state             false
% 3.59/1.01  --bmc1_out_unsat_core                   false
% 3.59/1.01  --bmc1_aig_witness_out                  false
% 3.59/1.01  --bmc1_verbose                          false
% 3.59/1.01  --bmc1_dump_clauses_tptp                false
% 3.59/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.59/1.01  --bmc1_dump_file                        -
% 3.59/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.59/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.59/1.01  --bmc1_ucm_extend_mode                  1
% 3.59/1.01  --bmc1_ucm_init_mode                    2
% 3.59/1.01  --bmc1_ucm_cone_mode                    none
% 3.59/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.59/1.01  --bmc1_ucm_relax_model                  4
% 3.59/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.59/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/1.01  --bmc1_ucm_layered_model                none
% 3.59/1.01  --bmc1_ucm_max_lemma_size               10
% 3.59/1.01  
% 3.59/1.01  ------ AIG Options
% 3.59/1.01  
% 3.59/1.01  --aig_mode                              false
% 3.59/1.01  
% 3.59/1.01  ------ Instantiation Options
% 3.59/1.01  
% 3.59/1.01  --instantiation_flag                    true
% 3.59/1.01  --inst_sos_flag                         true
% 3.59/1.01  --inst_sos_phase                        true
% 3.59/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/1.01  --inst_lit_sel_side                     none
% 3.59/1.01  --inst_solver_per_active                1400
% 3.59/1.01  --inst_solver_calls_frac                1.
% 3.59/1.01  --inst_passive_queue_type               priority_queues
% 3.59/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/1.01  --inst_passive_queues_freq              [25;2]
% 3.59/1.01  --inst_dismatching                      true
% 3.59/1.01  --inst_eager_unprocessed_to_passive     true
% 3.59/1.01  --inst_prop_sim_given                   true
% 3.59/1.01  --inst_prop_sim_new                     false
% 3.59/1.01  --inst_subs_new                         false
% 3.59/1.01  --inst_eq_res_simp                      false
% 3.59/1.01  --inst_subs_given                       false
% 3.59/1.01  --inst_orphan_elimination               true
% 3.59/1.01  --inst_learning_loop_flag               true
% 3.59/1.01  --inst_learning_start                   3000
% 3.59/1.01  --inst_learning_factor                  2
% 3.59/1.01  --inst_start_prop_sim_after_learn       3
% 3.59/1.01  --inst_sel_renew                        solver
% 3.59/1.01  --inst_lit_activity_flag                true
% 3.59/1.01  --inst_restr_to_given                   false
% 3.59/1.01  --inst_activity_threshold               500
% 3.59/1.01  --inst_out_proof                        true
% 3.59/1.01  
% 3.59/1.01  ------ Resolution Options
% 3.59/1.01  
% 3.59/1.01  --resolution_flag                       false
% 3.59/1.01  --res_lit_sel                           adaptive
% 3.59/1.01  --res_lit_sel_side                      none
% 3.59/1.01  --res_ordering                          kbo
% 3.59/1.01  --res_to_prop_solver                    active
% 3.59/1.01  --res_prop_simpl_new                    false
% 3.59/1.01  --res_prop_simpl_given                  true
% 3.59/1.01  --res_passive_queue_type                priority_queues
% 3.59/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/1.01  --res_passive_queues_freq               [15;5]
% 3.59/1.01  --res_forward_subs                      full
% 3.59/1.01  --res_backward_subs                     full
% 3.59/1.01  --res_forward_subs_resolution           true
% 3.59/1.01  --res_backward_subs_resolution          true
% 3.59/1.01  --res_orphan_elimination                true
% 3.59/1.01  --res_time_limit                        2.
% 3.59/1.01  --res_out_proof                         true
% 3.59/1.01  
% 3.59/1.01  ------ Superposition Options
% 3.59/1.01  
% 3.59/1.01  --superposition_flag                    true
% 3.59/1.01  --sup_passive_queue_type                priority_queues
% 3.59/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.59/1.01  --demod_completeness_check              fast
% 3.59/1.01  --demod_use_ground                      true
% 3.59/1.01  --sup_to_prop_solver                    passive
% 3.59/1.01  --sup_prop_simpl_new                    true
% 3.59/1.01  --sup_prop_simpl_given                  true
% 3.59/1.01  --sup_fun_splitting                     true
% 3.59/1.01  --sup_smt_interval                      50000
% 3.59/1.01  
% 3.59/1.01  ------ Superposition Simplification Setup
% 3.59/1.01  
% 3.59/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.59/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.59/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.59/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.59/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.59/1.01  --sup_immed_triv                        [TrivRules]
% 3.59/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/1.01  --sup_immed_bw_main                     []
% 3.59/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.59/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/1.01  --sup_input_bw                          []
% 3.59/1.01  
% 3.59/1.01  ------ Combination Options
% 3.59/1.01  
% 3.59/1.01  --comb_res_mult                         3
% 3.59/1.01  --comb_sup_mult                         2
% 3.59/1.01  --comb_inst_mult                        10
% 3.59/1.01  
% 3.59/1.01  ------ Debug Options
% 3.59/1.01  
% 3.59/1.01  --dbg_backtrace                         false
% 3.59/1.01  --dbg_dump_prop_clauses                 false
% 3.59/1.01  --dbg_dump_prop_clauses_file            -
% 3.59/1.01  --dbg_out_stat                          false
% 3.59/1.01  
% 3.59/1.01  
% 3.59/1.01  
% 3.59/1.01  
% 3.59/1.01  ------ Proving...
% 3.59/1.01  
% 3.59/1.01  
% 3.59/1.01  % SZS status Theorem for theBenchmark.p
% 3.59/1.01  
% 3.59/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.59/1.01  
% 3.59/1.01  fof(f2,axiom,(
% 3.59/1.01    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f19,plain,(
% 3.59/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.59/1.01    inference(ennf_transformation,[],[f2])).
% 3.59/1.01  
% 3.59/1.01  fof(f27,plain,(
% 3.59/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.59/1.01    introduced(choice_axiom,[])).
% 3.59/1.01  
% 3.59/1.01  fof(f28,plain,(
% 3.59/1.01    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 3.59/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f27])).
% 3.59/1.01  
% 3.59/1.01  fof(f46,plain,(
% 3.59/1.01    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.59/1.01    inference(cnf_transformation,[],[f28])).
% 3.59/1.01  
% 3.59/1.01  fof(f17,conjecture,(
% 3.59/1.01    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f18,negated_conjecture,(
% 3.59/1.01    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.59/1.01    inference(negated_conjecture,[],[f17])).
% 3.59/1.01  
% 3.59/1.01  fof(f21,plain,(
% 3.59/1.01    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.59/1.01    inference(ennf_transformation,[],[f18])).
% 3.59/1.01  
% 3.59/1.01  fof(f38,plain,(
% 3.59/1.01    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4) & (k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4) & (k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4) & k2_xboole_0(sK4,sK5) = k1_tarski(sK3))),
% 3.59/1.01    introduced(choice_axiom,[])).
% 3.59/1.01  
% 3.59/1.01  fof(f39,plain,(
% 3.59/1.01    (k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4) & (k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4) & (k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4) & k2_xboole_0(sK4,sK5) = k1_tarski(sK3)),
% 3.59/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f21,f38])).
% 3.59/1.01  
% 3.59/1.01  fof(f70,plain,(
% 3.59/1.01    k2_xboole_0(sK4,sK5) = k1_tarski(sK3)),
% 3.59/1.01    inference(cnf_transformation,[],[f39])).
% 3.59/1.01  
% 3.59/1.01  fof(f15,axiom,(
% 3.59/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f66,plain,(
% 3.59/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.59/1.01    inference(cnf_transformation,[],[f15])).
% 3.59/1.01  
% 3.59/1.01  fof(f79,plain,(
% 3.59/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.59/1.01    inference(definition_unfolding,[],[f66,f78])).
% 3.59/1.01  
% 3.59/1.01  fof(f7,axiom,(
% 3.59/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f56,plain,(
% 3.59/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f7])).
% 3.59/1.01  
% 3.59/1.01  fof(f8,axiom,(
% 3.59/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f57,plain,(
% 3.59/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f8])).
% 3.59/1.01  
% 3.59/1.01  fof(f9,axiom,(
% 3.59/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f58,plain,(
% 3.59/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f9])).
% 3.59/1.01  
% 3.59/1.01  fof(f10,axiom,(
% 3.59/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f59,plain,(
% 3.59/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f10])).
% 3.59/1.01  
% 3.59/1.01  fof(f11,axiom,(
% 3.59/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f60,plain,(
% 3.59/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f11])).
% 3.59/1.01  
% 3.59/1.01  fof(f12,axiom,(
% 3.59/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f61,plain,(
% 3.59/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f12])).
% 3.59/1.01  
% 3.59/1.01  fof(f13,axiom,(
% 3.59/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f62,plain,(
% 3.59/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f13])).
% 3.59/1.01  
% 3.59/1.01  fof(f74,plain,(
% 3.59/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.59/1.01    inference(definition_unfolding,[],[f61,f62])).
% 3.59/1.01  
% 3.59/1.01  fof(f75,plain,(
% 3.59/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.59/1.01    inference(definition_unfolding,[],[f60,f74])).
% 3.59/1.01  
% 3.59/1.01  fof(f76,plain,(
% 3.59/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.59/1.01    inference(definition_unfolding,[],[f59,f75])).
% 3.59/1.01  
% 3.59/1.01  fof(f77,plain,(
% 3.59/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.59/1.01    inference(definition_unfolding,[],[f58,f76])).
% 3.59/1.01  
% 3.59/1.01  fof(f78,plain,(
% 3.59/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.59/1.01    inference(definition_unfolding,[],[f57,f77])).
% 3.59/1.01  
% 3.59/1.01  fof(f80,plain,(
% 3.59/1.01    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.59/1.01    inference(definition_unfolding,[],[f56,f78])).
% 3.59/1.01  
% 3.59/1.01  fof(f104,plain,(
% 3.59/1.01    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),
% 3.59/1.01    inference(definition_unfolding,[],[f70,f79,f80])).
% 3.59/1.01  
% 3.59/1.01  fof(f5,axiom,(
% 3.59/1.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f49,plain,(
% 3.59/1.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.59/1.01    inference(cnf_transformation,[],[f5])).
% 3.59/1.01  
% 3.59/1.01  fof(f88,plain,(
% 3.59/1.01    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.59/1.01    inference(definition_unfolding,[],[f49,f79])).
% 3.59/1.01  
% 3.59/1.01  fof(f3,axiom,(
% 3.59/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f20,plain,(
% 3.59/1.01    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.59/1.01    inference(ennf_transformation,[],[f3])).
% 3.59/1.01  
% 3.59/1.01  fof(f47,plain,(
% 3.59/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f20])).
% 3.59/1.01  
% 3.59/1.01  fof(f87,plain,(
% 3.59/1.01    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.59/1.01    inference(definition_unfolding,[],[f47,f79])).
% 3.59/1.01  
% 3.59/1.01  fof(f1,axiom,(
% 3.59/1.01    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f22,plain,(
% 3.59/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.59/1.01    inference(nnf_transformation,[],[f1])).
% 3.59/1.01  
% 3.59/1.01  fof(f23,plain,(
% 3.59/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.59/1.01    inference(flattening,[],[f22])).
% 3.59/1.01  
% 3.59/1.01  fof(f24,plain,(
% 3.59/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.59/1.01    inference(rectify,[],[f23])).
% 3.59/1.01  
% 3.59/1.01  fof(f25,plain,(
% 3.59/1.01    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.59/1.01    introduced(choice_axiom,[])).
% 3.59/1.01  
% 3.59/1.01  fof(f26,plain,(
% 3.59/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.59/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 3.59/1.01  
% 3.59/1.01  fof(f41,plain,(
% 3.59/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.59/1.01    inference(cnf_transformation,[],[f26])).
% 3.59/1.01  
% 3.59/1.01  fof(f85,plain,(
% 3.59/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.59/1.01    inference(definition_unfolding,[],[f41,f79])).
% 3.59/1.01  
% 3.59/1.01  fof(f106,plain,(
% 3.59/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 3.59/1.01    inference(equality_resolution,[],[f85])).
% 3.59/1.01  
% 3.59/1.01  fof(f6,axiom,(
% 3.59/1.01    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f29,plain,(
% 3.59/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.59/1.01    inference(nnf_transformation,[],[f6])).
% 3.59/1.01  
% 3.59/1.01  fof(f30,plain,(
% 3.59/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.59/1.01    inference(flattening,[],[f29])).
% 3.59/1.01  
% 3.59/1.01  fof(f31,plain,(
% 3.59/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.59/1.01    inference(rectify,[],[f30])).
% 3.59/1.01  
% 3.59/1.01  fof(f32,plain,(
% 3.59/1.01    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.59/1.01    introduced(choice_axiom,[])).
% 3.59/1.01  
% 3.59/1.01  fof(f33,plain,(
% 3.59/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.59/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 3.59/1.01  
% 3.59/1.01  fof(f50,plain,(
% 3.59/1.01    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.59/1.01    inference(cnf_transformation,[],[f33])).
% 3.59/1.01  
% 3.59/1.01  fof(f94,plain,(
% 3.59/1.01    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 3.59/1.01    inference(definition_unfolding,[],[f50,f78])).
% 3.59/1.01  
% 3.59/1.01  fof(f112,plain,(
% 3.59/1.01    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.59/1.01    inference(equality_resolution,[],[f94])).
% 3.59/1.01  
% 3.59/1.01  fof(f54,plain,(
% 3.59/1.01    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK2(X0,X1,X2) != X0 | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f33])).
% 3.59/1.01  
% 3.59/1.01  fof(f90,plain,(
% 3.59/1.01    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2 | sK2(X0,X1,X2) != X0 | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.59/1.01    inference(definition_unfolding,[],[f54,f78])).
% 3.59/1.01  
% 3.59/1.01  fof(f42,plain,(
% 3.59/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.59/1.01    inference(cnf_transformation,[],[f26])).
% 3.59/1.01  
% 3.59/1.01  fof(f84,plain,(
% 3.59/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.59/1.01    inference(definition_unfolding,[],[f42,f79])).
% 3.59/1.01  
% 3.59/1.01  fof(f105,plain,(
% 3.59/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 3.59/1.01    inference(equality_resolution,[],[f84])).
% 3.59/1.01  
% 3.59/1.01  fof(f53,plain,(
% 3.59/1.01    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f33])).
% 3.59/1.01  
% 3.59/1.01  fof(f91,plain,(
% 3.59/1.01    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2 | sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.59/1.01    inference(definition_unfolding,[],[f53,f78])).
% 3.59/1.01  
% 3.59/1.01  fof(f14,axiom,(
% 3.59/1.01    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f34,plain,(
% 3.59/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.59/1.01    inference(nnf_transformation,[],[f14])).
% 3.59/1.01  
% 3.59/1.01  fof(f35,plain,(
% 3.59/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.59/1.01    inference(flattening,[],[f34])).
% 3.59/1.01  
% 3.59/1.01  fof(f63,plain,(
% 3.59/1.01    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.59/1.01    inference(cnf_transformation,[],[f35])).
% 3.59/1.01  
% 3.59/1.01  fof(f97,plain,(
% 3.59/1.01    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 3.59/1.01    inference(definition_unfolding,[],[f63,f80,f80])).
% 3.59/1.01  
% 3.59/1.01  fof(f73,plain,(
% 3.59/1.01    k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4),
% 3.59/1.01    inference(cnf_transformation,[],[f39])).
% 3.59/1.01  
% 3.59/1.01  fof(f101,plain,(
% 3.59/1.01    k1_xboole_0 != sK5 | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4),
% 3.59/1.01    inference(definition_unfolding,[],[f73,f80])).
% 3.59/1.01  
% 3.59/1.01  fof(f71,plain,(
% 3.59/1.01    k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4),
% 3.59/1.01    inference(cnf_transformation,[],[f39])).
% 3.59/1.01  
% 3.59/1.01  fof(f103,plain,(
% 3.59/1.01    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5 | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4),
% 3.59/1.01    inference(definition_unfolding,[],[f71,f80,f80])).
% 3.59/1.01  
% 3.59/1.01  fof(f72,plain,(
% 3.59/1.01    k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4),
% 3.59/1.01    inference(cnf_transformation,[],[f39])).
% 3.59/1.01  
% 3.59/1.01  fof(f102,plain,(
% 3.59/1.01    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5 | k1_xboole_0 != sK4),
% 3.59/1.01    inference(definition_unfolding,[],[f72,f80])).
% 3.59/1.01  
% 3.59/1.01  fof(f4,axiom,(
% 3.59/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f48,plain,(
% 3.59/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f4])).
% 3.59/1.01  
% 3.59/1.01  cnf(c_6,plain,
% 3.59/1.01      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.59/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_760,plain,
% 3.59/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_25,negated_conjecture,
% 3.59/1.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
% 3.59/1.01      inference(cnf_transformation,[],[f104]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_9,plain,
% 3.59/1.01      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 3.59/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_757,plain,
% 3.59/1.01      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1069,plain,
% 3.59/1.01      ( r1_tarski(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_25,c_757]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_7,plain,
% 3.59/1.01      ( ~ r1_tarski(X0,X1)
% 3.59/1.01      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
% 3.59/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_759,plain,
% 3.59/1.01      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
% 3.59/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1334,plain,
% 3.59/1.01      ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_1069,c_759]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_4,plain,
% 3.59/1.01      ( ~ r2_hidden(X0,X1)
% 3.59/1.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 3.59/1.01      inference(cnf_transformation,[],[f106]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_762,plain,
% 3.59/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.59/1.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1669,plain,
% 3.59/1.01      ( r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top
% 3.59/1.01      | r2_hidden(X0,sK4) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_1334,c_762]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_15,plain,
% 3.59/1.01      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 3.59/1.01      | X0 = X1
% 3.59/1.01      | X0 = X2 ),
% 3.59/1.01      inference(cnf_transformation,[],[f112]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_751,plain,
% 3.59/1.01      ( X0 = X1
% 3.59/1.01      | X0 = X2
% 3.59/1.01      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) != iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1923,plain,
% 3.59/1.01      ( sK3 = X0 | r2_hidden(X0,sK4) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_1669,c_751]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_2582,plain,
% 3.59/1.01      ( sK1(sK4) = sK3 | sK4 = k1_xboole_0 ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_760,c_1923]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_11,plain,
% 3.59/1.01      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
% 3.59/1.01      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
% 3.59/1.01      | sK2(X0,X1,X2) != X0 ),
% 3.59/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_845,plain,
% 3.59/1.01      ( ~ r2_hidden(sK2(sK3,sK3,sK5),sK5)
% 3.59/1.01      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
% 3.59/1.01      | sK2(sK3,sK3,sK5) != sK3 ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_3,plain,
% 3.59/1.01      ( ~ r2_hidden(X0,X1)
% 3.59/1.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 3.59/1.01      inference(cnf_transformation,[],[f105]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_763,plain,
% 3.59/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.59/1.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1777,plain,
% 3.59/1.01      ( r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top
% 3.59/1.01      | r2_hidden(X0,sK5) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_25,c_763]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1922,plain,
% 3.59/1.01      ( sK3 = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_1777,c_751]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_2289,plain,
% 3.59/1.01      ( sK1(sK5) = sK3 | sK5 = k1_xboole_0 ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_760,c_1922]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_2374,plain,
% 3.59/1.01      ( sK5 = k1_xboole_0 | r2_hidden(sK3,sK5) = iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_2289,c_760]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_2375,plain,
% 3.59/1.01      ( r2_hidden(sK3,sK5) | sK5 = k1_xboole_0 ),
% 3.59/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_2374]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_12,plain,
% 3.59/1.01      ( r2_hidden(sK2(X0,X1,X2),X2)
% 3.59/1.01      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
% 3.59/1.01      | sK2(X0,X1,X2) = X1
% 3.59/1.01      | sK2(X0,X1,X2) = X0 ),
% 3.59/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_754,plain,
% 3.59/1.01      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
% 3.59/1.01      | sK2(X0,X1,X2) = X1
% 3.59/1.01      | sK2(X0,X1,X2) = X0
% 3.59/1.01      | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_3213,plain,
% 3.59/1.01      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = sK5
% 3.59/1.01      | sK2(X0,X1,sK5) = X1
% 3.59/1.01      | sK2(X0,X1,sK5) = X0
% 3.59/1.01      | sK2(X0,X1,sK5) = sK3 ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_754,c_1922]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_3223,plain,
% 3.59/1.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
% 3.59/1.01      | sK2(sK3,sK3,sK5) = sK3 ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_3213]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_18,plain,
% 3.59/1.01      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 3.59/1.01      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 3.59/1.01      | k1_xboole_0 = X0 ),
% 3.59/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_748,plain,
% 3.59/1.01      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 3.59/1.01      | k1_xboole_0 = X1
% 3.59/1.01      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_2829,plain,
% 3.59/1.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4
% 3.59/1.01      | sK4 = k1_xboole_0 ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_1069,c_748]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_22,negated_conjecture,
% 3.59/1.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4
% 3.59/1.01      | k1_xboole_0 != sK5 ),
% 3.59/1.01      inference(cnf_transformation,[],[f101]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_3462,plain,
% 3.59/1.01      ( sK4 = k1_xboole_0 | sK5 != k1_xboole_0 ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_2829,c_22]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_24,negated_conjecture,
% 3.59/1.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4
% 3.59/1.01      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5 ),
% 3.59/1.01      inference(cnf_transformation,[],[f103]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_3460,plain,
% 3.59/1.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5
% 3.59/1.01      | sK4 = k1_xboole_0 ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_2829,c_24]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_23,negated_conjecture,
% 3.59/1.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5
% 3.59/1.01      | k1_xboole_0 != sK4 ),
% 3.59/1.01      inference(cnf_transformation,[],[f102]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_803,plain,
% 3.59/1.01      ( ~ r1_tarski(sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.59/1.01      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK4
% 3.59/1.01      | k1_xboole_0 = sK4 ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_18]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_808,plain,
% 3.59/1.01      ( ~ r1_tarski(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
% 3.59/1.01      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4
% 3.59/1.01      | k1_xboole_0 = sK4 ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_803]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1070,plain,
% 3.59/1.01      ( r1_tarski(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
% 3.59/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1069]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_3950,plain,
% 3.59/1.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5 ),
% 3.59/1.01      inference(global_propositional_subsumption,
% 3.59/1.01                [status(thm)],
% 3.59/1.01                [c_3460,c_24,c_23,c_808,c_1070]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_411,plain,( X0 = X0 ),theory(equality) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_3971,plain,
% 3.59/1.01      ( sK5 = sK5 ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_411]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_415,plain,
% 3.59/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.59/1.01      theory(equality) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_2637,plain,
% 3.59/1.01      ( ~ r2_hidden(X0,X1)
% 3.59/1.01      | r2_hidden(sK2(sK3,sK3,sK5),sK5)
% 3.59/1.01      | sK2(sK3,sK3,sK5) != X0
% 3.59/1.01      | sK5 != X1 ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_415]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_4185,plain,
% 3.59/1.01      ( ~ r2_hidden(X0,sK5)
% 3.59/1.01      | r2_hidden(sK2(sK3,sK3,sK5),sK5)
% 3.59/1.01      | sK2(sK3,sK3,sK5) != X0
% 3.59/1.01      | sK5 != sK5 ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_2637]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_4187,plain,
% 3.59/1.01      ( r2_hidden(sK2(sK3,sK3,sK5),sK5)
% 3.59/1.01      | ~ r2_hidden(sK3,sK5)
% 3.59/1.01      | sK2(sK3,sK3,sK5) != sK3
% 3.59/1.01      | sK5 != sK5 ),
% 3.59/1.01      inference(instantiation,[status(thm)],[c_4185]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_4353,plain,
% 3.59/1.01      ( sK4 = k1_xboole_0 ),
% 3.59/1.01      inference(global_propositional_subsumption,
% 3.59/1.01                [status(thm)],
% 3.59/1.01                [c_2582,c_24,c_23,c_808,c_845,c_1070,c_2375,c_3223,
% 3.59/1.01                 c_3462,c_3971,c_4187]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_4365,plain,
% 3.59/1.01      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK5)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 3.59/1.01      inference(demodulation,[status(thm)],[c_4353,c_25]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_8,plain,
% 3.59/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 3.59/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_758,plain,
% 3.59/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_1332,plain,
% 3.59/1.01      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_758,c_759]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_4367,plain,
% 3.59/1.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5 ),
% 3.59/1.01      inference(demodulation,[status(thm)],[c_4365,c_1332]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(contradiction,plain,
% 3.59/1.01      ( $false ),
% 3.59/1.01      inference(minisat,[status(thm)],[c_4367,c_3950]) ).
% 3.59/1.01  
% 3.59/1.01  
% 3.59/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.59/1.01  
% 3.59/1.01  ------                               Statistics
% 3.59/1.01  
% 3.59/1.01  ------ General
% 3.59/1.01  
% 3.59/1.01  abstr_ref_over_cycles:                  0
% 3.59/1.01  abstr_ref_under_cycles:                 0
% 3.59/1.01  gc_basic_clause_elim:                   0
% 3.59/1.01  forced_gc_time:                         0
% 3.59/1.01  parsing_time:                           0.012
% 3.59/1.01  unif_index_cands_time:                  0.
% 3.59/1.01  unif_index_add_time:                    0.
% 3.59/1.01  orderings_time:                         0.
% 3.59/1.01  out_proof_time:                         0.017
% 3.59/1.01  total_time:                             0.224
% 3.59/1.01  num_of_symbols:                         39
% 3.59/1.01  num_of_terms:                           5037
% 3.59/1.01  
% 3.59/1.01  ------ Preprocessing
% 3.59/1.01  
% 3.59/1.01  num_of_splits:                          0
% 3.59/1.01  num_of_split_atoms:                     0
% 3.59/1.01  num_of_reused_defs:                     0
% 3.59/1.01  num_eq_ax_congr_red:                    14
% 3.59/1.01  num_of_sem_filtered_clauses:            1
% 3.59/1.01  num_of_subtypes:                        0
% 3.59/1.01  monotx_restored_types:                  0
% 3.59/1.01  sat_num_of_epr_types:                   0
% 3.59/1.01  sat_num_of_non_cyclic_types:            0
% 3.59/1.01  sat_guarded_non_collapsed_types:        0
% 3.59/1.01  num_pure_diseq_elim:                    0
% 3.59/1.01  simp_replaced_by:                       0
% 3.59/1.01  res_preprocessed:                       91
% 3.59/1.01  prep_upred:                             0
% 3.59/1.01  prep_unflattend:                        27
% 3.59/1.01  smt_new_axioms:                         0
% 3.59/1.01  pred_elim_cands:                        2
% 3.59/1.01  pred_elim:                              0
% 3.59/1.01  pred_elim_cl:                           0
% 3.59/1.01  pred_elim_cycles:                       1
% 3.59/1.01  merged_defs:                            0
% 3.59/1.01  merged_defs_ncl:                        0
% 3.59/1.01  bin_hyper_res:                          0
% 3.59/1.01  prep_cycles:                            3
% 3.59/1.01  pred_elim_time:                         0.002
% 3.59/1.01  splitting_time:                         0.
% 3.59/1.01  sem_filter_time:                        0.
% 3.59/1.01  monotx_time:                            0.
% 3.59/1.01  subtype_inf_time:                       0.
% 3.59/1.01  
% 3.59/1.01  ------ Problem properties
% 3.59/1.01  
% 3.59/1.01  clauses:                                26
% 3.59/1.01  conjectures:                            4
% 3.59/1.01  epr:                                    1
% 3.59/1.01  horn:                                   20
% 3.59/1.01  ground:                                 4
% 3.59/1.01  unary:                                  7
% 3.59/1.01  binary:                                 9
% 3.59/1.01  lits:                                   57
% 3.59/1.01  lits_eq:                                23
% 3.59/1.01  fd_pure:                                0
% 3.59/1.01  fd_pseudo:                              0
% 3.59/1.01  fd_cond:                                1
% 3.59/1.01  fd_pseudo_cond:                         7
% 3.59/1.01  ac_symbols:                             0
% 3.59/1.01  
% 3.59/1.01  ------ Propositional Solver
% 3.59/1.01  
% 3.59/1.01  prop_solver_calls:                      26
% 3.59/1.01  prop_fast_solver_calls:                 576
% 3.59/1.01  smt_solver_calls:                       0
% 3.59/1.01  smt_fast_solver_calls:                  0
% 3.59/1.01  prop_num_of_clauses:                    2123
% 3.59/1.01  prop_preprocess_simplified:             6072
% 3.59/1.01  prop_fo_subsumed:                       3
% 3.59/1.01  prop_solver_time:                       0.
% 3.59/1.01  smt_solver_time:                        0.
% 3.59/1.01  smt_fast_solver_time:                   0.
% 3.59/1.01  prop_fast_solver_time:                  0.
% 3.59/1.01  prop_unsat_core_time:                   0.
% 3.59/1.01  
% 3.59/1.01  ------ QBF
% 3.59/1.01  
% 3.59/1.01  qbf_q_res:                              0
% 3.59/1.01  qbf_num_tautologies:                    0
% 3.59/1.01  qbf_prep_cycles:                        0
% 3.59/1.01  
% 3.59/1.01  ------ BMC1
% 3.59/1.01  
% 3.59/1.01  bmc1_current_bound:                     -1
% 3.59/1.01  bmc1_last_solved_bound:                 -1
% 3.59/1.01  bmc1_unsat_core_size:                   -1
% 3.59/1.01  bmc1_unsat_core_parents_size:           -1
% 3.59/1.01  bmc1_merge_next_fun:                    0
% 3.59/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.59/1.01  
% 3.59/1.01  ------ Instantiation
% 3.59/1.01  
% 3.59/1.01  inst_num_of_clauses:                    521
% 3.59/1.01  inst_num_in_passive:                    304
% 3.59/1.01  inst_num_in_active:                     172
% 3.59/1.01  inst_num_in_unprocessed:                45
% 3.59/1.01  inst_num_of_loops:                      250
% 3.59/1.01  inst_num_of_learning_restarts:          0
% 3.59/1.01  inst_num_moves_active_passive:          76
% 3.59/1.01  inst_lit_activity:                      0
% 3.59/1.01  inst_lit_activity_moves:                0
% 3.59/1.01  inst_num_tautologies:                   0
% 3.59/1.01  inst_num_prop_implied:                  0
% 3.59/1.01  inst_num_existing_simplified:           0
% 3.59/1.01  inst_num_eq_res_simplified:             0
% 3.59/1.01  inst_num_child_elim:                    0
% 3.59/1.01  inst_num_of_dismatching_blockings:      188
% 3.59/1.01  inst_num_of_non_proper_insts:           550
% 3.59/1.01  inst_num_of_duplicates:                 0
% 3.59/1.01  inst_inst_num_from_inst_to_res:         0
% 3.59/1.01  inst_dismatching_checking_time:         0.
% 3.59/1.01  
% 3.59/1.01  ------ Resolution
% 3.59/1.01  
% 3.59/1.01  res_num_of_clauses:                     0
% 3.59/1.01  res_num_in_passive:                     0
% 3.59/1.01  res_num_in_active:                      0
% 3.59/1.01  res_num_of_loops:                       94
% 3.59/1.01  res_forward_subset_subsumed:            37
% 3.59/1.01  res_backward_subset_subsumed:           0
% 3.59/1.01  res_forward_subsumed:                   3
% 3.59/1.01  res_backward_subsumed:                  0
% 3.59/1.01  res_forward_subsumption_resolution:     0
% 3.59/1.01  res_backward_subsumption_resolution:    0
% 3.59/1.01  res_clause_to_clause_subsumption:       436
% 3.59/1.01  res_orphan_elimination:                 0
% 3.59/1.01  res_tautology_del:                      29
% 3.59/1.01  res_num_eq_res_simplified:              0
% 3.59/1.01  res_num_sel_changes:                    0
% 3.59/1.01  res_moves_from_active_to_pass:          0
% 3.59/1.01  
% 3.59/1.01  ------ Superposition
% 3.59/1.01  
% 3.59/1.01  sup_time_total:                         0.
% 3.59/1.01  sup_time_generating:                    0.
% 3.59/1.01  sup_time_sim_full:                      0.
% 3.59/1.01  sup_time_sim_immed:                     0.
% 3.59/1.01  
% 3.59/1.01  sup_num_of_clauses:                     89
% 3.59/1.01  sup_num_in_active:                      31
% 3.59/1.01  sup_num_in_passive:                     58
% 3.59/1.01  sup_num_of_loops:                       48
% 3.59/1.01  sup_fw_superposition:                   51
% 3.59/1.01  sup_bw_superposition:                   77
% 3.59/1.01  sup_immediate_simplified:               18
% 3.59/1.01  sup_given_eliminated:                   0
% 3.59/1.01  comparisons_done:                       0
% 3.59/1.01  comparisons_avoided:                    10
% 3.59/1.01  
% 3.59/1.01  ------ Simplifications
% 3.59/1.01  
% 3.59/1.01  
% 3.59/1.01  sim_fw_subset_subsumed:                 7
% 3.59/1.01  sim_bw_subset_subsumed:                 12
% 3.59/1.01  sim_fw_subsumed:                        8
% 3.59/1.01  sim_bw_subsumed:                        2
% 3.59/1.01  sim_fw_subsumption_res:                 0
% 3.59/1.01  sim_bw_subsumption_res:                 0
% 3.59/1.01  sim_tautology_del:                      21
% 3.59/1.01  sim_eq_tautology_del:                   6
% 3.59/1.01  sim_eq_res_simp:                        6
% 3.59/1.01  sim_fw_demodulated:                     8
% 3.59/1.01  sim_bw_demodulated:                     13
% 3.59/1.01  sim_light_normalised:                   0
% 3.59/1.01  sim_joinable_taut:                      0
% 3.59/1.01  sim_joinable_simp:                      0
% 3.59/1.01  sim_ac_normalised:                      0
% 3.59/1.01  sim_smt_subsumption:                    0
% 3.59/1.01  
%------------------------------------------------------------------------------
