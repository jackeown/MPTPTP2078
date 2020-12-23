%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:32 EST 2020

% Result     : Theorem 7.55s
% Output     : CNFRefutation 7.55s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 303 expanded)
%              Number of clauses        :   56 (  59 expanded)
%              Number of leaves         :   21 (  80 expanded)
%              Depth                    :   16
%              Number of atoms          :  380 ( 780 expanded)
%              Number of equality atoms :  230 ( 547 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f46])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f98,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f86,f87])).

fof(f99,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f85,f98])).

fof(f100,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f84,f99])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f88,f100,f100])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f102,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f54,f73,f73])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f101,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f70,f73])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
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

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f77,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f116,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f77,f98])).

fof(f137,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f116])).

fof(f138,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f137])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f49])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f95,f99])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f51,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f52,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK5,sK4)
        | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4 )
      & ( ~ r2_hidden(sK5,sK4)
        | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4 ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( r2_hidden(sK5,sK4)
      | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4 )
    & ( ~ r2_hidden(sK5,sK4)
      | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f51,f52])).

fof(f97,plain,
    ( r2_hidden(sK5,sK4)
    | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4 ),
    inference(cnf_transformation,[],[f53])).

fof(f126,plain,
    ( r2_hidden(sK5,sK4)
    | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4 ),
    inference(definition_unfolding,[],[f97,f100])).

fof(f12,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

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

fof(f23,plain,(
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

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f34])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f94,f99])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) = k3_enumset1(X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f92,f100,f100,f100])).

fof(f91,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f122,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) != k3_enumset1(X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f91,f100,f100,f100])).

fof(f142,plain,(
    ! [X1] : k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)) != k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f122])).

fof(f96,plain,
    ( ~ r2_hidden(sK5,sK4)
    | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4 ),
    inference(cnf_transformation,[],[f53])).

fof(f127,plain,
    ( ~ r2_hidden(sK5,sK4)
    | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = sK4 ),
    inference(definition_unfolding,[],[f96,f100])).

cnf(c_18,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1582,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_31,plain,
    ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1570,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5110,plain,
    ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k3_enumset1(X0,X0,X0,X0,X0)
    | k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1582,c_1570])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2077,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_30946,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1))) = k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5110,c_2077])).

cnf(c_19,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_27,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_1574,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_34,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1569,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1585,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3403,plain,
    ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k1_xboole_0
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1569,c_1585])).

cnf(c_14433,plain,
    ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X0,X0,X0,X2,X3)) = k1_xboole_0
    | r2_hidden(X1,k3_enumset1(X0,X0,X0,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1574,c_3403])).

cnf(c_24595,plain,
    ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X1,X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1574,c_14433])).

cnf(c_31363,plain,
    ( k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0
    | k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_30946,c_19,c_24595])).

cnf(c_37,negated_conjecture,
    ( r2_hidden(sK5,sK4)
    | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_1566,plain,
    ( k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4
    | r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_32008,plain,
    ( k4_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4) = k1_xboole_0
    | r2_hidden(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_31363,c_1566])).

cnf(c_20,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2248,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X2,X3)),k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_26141,plain,
    ( r1_xboole_0(k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_2248])).

cnf(c_26142,plain,
    ( r1_xboole_0(k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26141])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2205,plain,
    ( ~ r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,k4_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_13076,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)),k3_enumset1(sK5,sK5,sK5,sK5,sK5))
    | ~ r2_hidden(X0,k3_enumset1(sK5,sK5,sK5,sK5,sK5))
    | ~ r2_hidden(X0,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) ),
    inference(instantiation,[status(thm)],[c_2205])).

cnf(c_13077,plain,
    ( r1_xboole_0(k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(X0,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(X0,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13076])).

cnf(c_13079,plain,
    ( r1_xboole_0(k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(sK5,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13077])).

cnf(c_16,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1851,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
    | k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_4826,plain,
    ( r1_tarski(k3_enumset1(sK5,sK5,sK5,sK5,X0),sK4)
    | k4_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,X0),sK4) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1851])).

cnf(c_4828,plain,
    ( k4_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,X0),sK4) != k1_xboole_0
    | r1_tarski(k3_enumset1(sK5,sK5,sK5,sK5,X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4826])).

cnf(c_4830,plain,
    ( k4_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4) != k1_xboole_0
    | r1_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4828])).

cnf(c_843,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1933,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK5,sK4)
    | X1 != sK4
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_2594,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X2))
    | ~ r2_hidden(sK5,sK4)
    | X0 != sK5
    | k4_xboole_0(X1,X2) != sK4 ),
    inference(instantiation,[status(thm)],[c_1933])).

cnf(c_3180,plain,
    ( r2_hidden(X0,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)))
    | ~ r2_hidden(sK5,sK4)
    | X0 != sK5
    | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4 ),
    inference(instantiation,[status(thm)],[c_2594])).

cnf(c_3181,plain,
    ( X0 != sK5
    | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4
    | r2_hidden(X0,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) = iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3180])).

cnf(c_3183,plain,
    ( k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4
    | sK5 != sK5
    | r2_hidden(sK5,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) = iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3181])).

cnf(c_35,plain,
    ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
    | r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_2229,plain,
    ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,sK5),sK4)
    | r2_hidden(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_2230,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,sK5),sK4) != iProver_top
    | r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2229])).

cnf(c_2232,plain,
    ( r1_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4) != iProver_top
    | r2_hidden(sK5,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2230])).

cnf(c_62,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_64,plain,
    ( r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_32,plain,
    ( X0 = X1
    | k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X0,X0,X0,X0,X0)) = k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_49,plain,
    ( k4_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = k3_enumset1(sK5,sK5,sK5,sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_33,plain,
    ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0)) != k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_48,plain,
    ( k4_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != k3_enumset1(sK5,sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_38,negated_conjecture,
    ( ~ r2_hidden(sK5,sK4)
    | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = sK4 ),
    inference(cnf_transformation,[],[f127])).

cnf(c_39,plain,
    ( k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = sK4
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32008,c_26142,c_13079,c_4830,c_3183,c_2232,c_64,c_49,c_48,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:37:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.55/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.55/1.49  
% 7.55/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.55/1.49  
% 7.55/1.49  ------  iProver source info
% 7.55/1.49  
% 7.55/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.55/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.55/1.49  git: non_committed_changes: false
% 7.55/1.49  git: last_make_outside_of_git: false
% 7.55/1.49  
% 7.55/1.49  ------ 
% 7.55/1.49  
% 7.55/1.49  ------ Input Options
% 7.55/1.49  
% 7.55/1.49  --out_options                           all
% 7.55/1.49  --tptp_safe_out                         true
% 7.55/1.49  --problem_path                          ""
% 7.55/1.49  --include_path                          ""
% 7.55/1.49  --clausifier                            res/vclausify_rel
% 7.55/1.49  --clausifier_options                    --mode clausify
% 7.55/1.49  --stdin                                 false
% 7.55/1.49  --stats_out                             all
% 7.55/1.49  
% 7.55/1.49  ------ General Options
% 7.55/1.49  
% 7.55/1.49  --fof                                   false
% 7.55/1.49  --time_out_real                         305.
% 7.55/1.49  --time_out_virtual                      -1.
% 7.55/1.49  --symbol_type_check                     false
% 7.55/1.49  --clausify_out                          false
% 7.55/1.49  --sig_cnt_out                           false
% 7.55/1.49  --trig_cnt_out                          false
% 7.55/1.49  --trig_cnt_out_tolerance                1.
% 7.55/1.49  --trig_cnt_out_sk_spl                   false
% 7.55/1.49  --abstr_cl_out                          false
% 7.55/1.49  
% 7.55/1.49  ------ Global Options
% 7.55/1.49  
% 7.55/1.49  --schedule                              default
% 7.55/1.49  --add_important_lit                     false
% 7.55/1.49  --prop_solver_per_cl                    1000
% 7.55/1.49  --min_unsat_core                        false
% 7.55/1.49  --soft_assumptions                      false
% 7.55/1.49  --soft_lemma_size                       3
% 7.55/1.49  --prop_impl_unit_size                   0
% 7.55/1.49  --prop_impl_unit                        []
% 7.55/1.49  --share_sel_clauses                     true
% 7.55/1.49  --reset_solvers                         false
% 7.55/1.49  --bc_imp_inh                            [conj_cone]
% 7.55/1.49  --conj_cone_tolerance                   3.
% 7.55/1.49  --extra_neg_conj                        none
% 7.55/1.49  --large_theory_mode                     true
% 7.55/1.49  --prolific_symb_bound                   200
% 7.55/1.49  --lt_threshold                          2000
% 7.55/1.49  --clause_weak_htbl                      true
% 7.55/1.49  --gc_record_bc_elim                     false
% 7.55/1.49  
% 7.55/1.49  ------ Preprocessing Options
% 7.55/1.49  
% 7.55/1.49  --preprocessing_flag                    true
% 7.55/1.49  --time_out_prep_mult                    0.1
% 7.55/1.49  --splitting_mode                        input
% 7.55/1.49  --splitting_grd                         true
% 7.55/1.49  --splitting_cvd                         false
% 7.55/1.49  --splitting_cvd_svl                     false
% 7.55/1.49  --splitting_nvd                         32
% 7.55/1.49  --sub_typing                            true
% 7.55/1.49  --prep_gs_sim                           true
% 7.55/1.49  --prep_unflatten                        true
% 7.55/1.49  --prep_res_sim                          true
% 7.55/1.49  --prep_upred                            true
% 7.55/1.49  --prep_sem_filter                       exhaustive
% 7.55/1.49  --prep_sem_filter_out                   false
% 7.55/1.49  --pred_elim                             true
% 7.55/1.49  --res_sim_input                         true
% 7.55/1.49  --eq_ax_congr_red                       true
% 7.55/1.49  --pure_diseq_elim                       true
% 7.55/1.49  --brand_transform                       false
% 7.55/1.49  --non_eq_to_eq                          false
% 7.55/1.49  --prep_def_merge                        true
% 7.55/1.49  --prep_def_merge_prop_impl              false
% 7.55/1.49  --prep_def_merge_mbd                    true
% 7.55/1.49  --prep_def_merge_tr_red                 false
% 7.55/1.49  --prep_def_merge_tr_cl                  false
% 7.55/1.49  --smt_preprocessing                     true
% 7.55/1.49  --smt_ac_axioms                         fast
% 7.55/1.49  --preprocessed_out                      false
% 7.55/1.49  --preprocessed_stats                    false
% 7.55/1.49  
% 7.55/1.49  ------ Abstraction refinement Options
% 7.55/1.49  
% 7.55/1.49  --abstr_ref                             []
% 7.55/1.49  --abstr_ref_prep                        false
% 7.55/1.49  --abstr_ref_until_sat                   false
% 7.55/1.49  --abstr_ref_sig_restrict                funpre
% 7.55/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.55/1.49  --abstr_ref_under                       []
% 7.55/1.49  
% 7.55/1.49  ------ SAT Options
% 7.55/1.49  
% 7.55/1.49  --sat_mode                              false
% 7.55/1.49  --sat_fm_restart_options                ""
% 7.55/1.49  --sat_gr_def                            false
% 7.55/1.49  --sat_epr_types                         true
% 7.55/1.49  --sat_non_cyclic_types                  false
% 7.55/1.49  --sat_finite_models                     false
% 7.55/1.49  --sat_fm_lemmas                         false
% 7.55/1.49  --sat_fm_prep                           false
% 7.55/1.49  --sat_fm_uc_incr                        true
% 7.55/1.49  --sat_out_model                         small
% 7.55/1.49  --sat_out_clauses                       false
% 7.55/1.49  
% 7.55/1.49  ------ QBF Options
% 7.55/1.49  
% 7.55/1.49  --qbf_mode                              false
% 7.55/1.49  --qbf_elim_univ                         false
% 7.55/1.49  --qbf_dom_inst                          none
% 7.55/1.49  --qbf_dom_pre_inst                      false
% 7.55/1.49  --qbf_sk_in                             false
% 7.55/1.49  --qbf_pred_elim                         true
% 7.55/1.49  --qbf_split                             512
% 7.55/1.49  
% 7.55/1.49  ------ BMC1 Options
% 7.55/1.49  
% 7.55/1.49  --bmc1_incremental                      false
% 7.55/1.49  --bmc1_axioms                           reachable_all
% 7.55/1.49  --bmc1_min_bound                        0
% 7.55/1.49  --bmc1_max_bound                        -1
% 7.55/1.49  --bmc1_max_bound_default                -1
% 7.55/1.49  --bmc1_symbol_reachability              true
% 7.55/1.49  --bmc1_property_lemmas                  false
% 7.55/1.49  --bmc1_k_induction                      false
% 7.55/1.49  --bmc1_non_equiv_states                 false
% 7.55/1.49  --bmc1_deadlock                         false
% 7.55/1.49  --bmc1_ucm                              false
% 7.55/1.49  --bmc1_add_unsat_core                   none
% 7.55/1.49  --bmc1_unsat_core_children              false
% 7.55/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.55/1.49  --bmc1_out_stat                         full
% 7.55/1.49  --bmc1_ground_init                      false
% 7.55/1.49  --bmc1_pre_inst_next_state              false
% 7.55/1.49  --bmc1_pre_inst_state                   false
% 7.55/1.49  --bmc1_pre_inst_reach_state             false
% 7.55/1.49  --bmc1_out_unsat_core                   false
% 7.55/1.49  --bmc1_aig_witness_out                  false
% 7.55/1.49  --bmc1_verbose                          false
% 7.55/1.49  --bmc1_dump_clauses_tptp                false
% 7.55/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.55/1.49  --bmc1_dump_file                        -
% 7.55/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.55/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.55/1.49  --bmc1_ucm_extend_mode                  1
% 7.55/1.49  --bmc1_ucm_init_mode                    2
% 7.55/1.49  --bmc1_ucm_cone_mode                    none
% 7.55/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.55/1.49  --bmc1_ucm_relax_model                  4
% 7.55/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.55/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.55/1.49  --bmc1_ucm_layered_model                none
% 7.55/1.49  --bmc1_ucm_max_lemma_size               10
% 7.55/1.49  
% 7.55/1.49  ------ AIG Options
% 7.55/1.49  
% 7.55/1.49  --aig_mode                              false
% 7.55/1.49  
% 7.55/1.49  ------ Instantiation Options
% 7.55/1.49  
% 7.55/1.49  --instantiation_flag                    true
% 7.55/1.49  --inst_sos_flag                         false
% 7.55/1.49  --inst_sos_phase                        true
% 7.55/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.55/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.55/1.49  --inst_lit_sel_side                     num_symb
% 7.55/1.49  --inst_solver_per_active                1400
% 7.55/1.49  --inst_solver_calls_frac                1.
% 7.55/1.49  --inst_passive_queue_type               priority_queues
% 7.55/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.55/1.49  --inst_passive_queues_freq              [25;2]
% 7.55/1.49  --inst_dismatching                      true
% 7.55/1.49  --inst_eager_unprocessed_to_passive     true
% 7.55/1.49  --inst_prop_sim_given                   true
% 7.55/1.49  --inst_prop_sim_new                     false
% 7.55/1.49  --inst_subs_new                         false
% 7.55/1.49  --inst_eq_res_simp                      false
% 7.55/1.49  --inst_subs_given                       false
% 7.55/1.49  --inst_orphan_elimination               true
% 7.55/1.49  --inst_learning_loop_flag               true
% 7.55/1.49  --inst_learning_start                   3000
% 7.55/1.49  --inst_learning_factor                  2
% 7.55/1.49  --inst_start_prop_sim_after_learn       3
% 7.55/1.49  --inst_sel_renew                        solver
% 7.55/1.49  --inst_lit_activity_flag                true
% 7.55/1.49  --inst_restr_to_given                   false
% 7.55/1.49  --inst_activity_threshold               500
% 7.55/1.49  --inst_out_proof                        true
% 7.55/1.49  
% 7.55/1.49  ------ Resolution Options
% 7.55/1.49  
% 7.55/1.49  --resolution_flag                       true
% 7.55/1.49  --res_lit_sel                           adaptive
% 7.55/1.49  --res_lit_sel_side                      none
% 7.55/1.49  --res_ordering                          kbo
% 7.55/1.49  --res_to_prop_solver                    active
% 7.55/1.49  --res_prop_simpl_new                    false
% 7.55/1.49  --res_prop_simpl_given                  true
% 7.55/1.49  --res_passive_queue_type                priority_queues
% 7.55/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.55/1.49  --res_passive_queues_freq               [15;5]
% 7.55/1.49  --res_forward_subs                      full
% 7.55/1.49  --res_backward_subs                     full
% 7.55/1.49  --res_forward_subs_resolution           true
% 7.55/1.49  --res_backward_subs_resolution          true
% 7.55/1.49  --res_orphan_elimination                true
% 7.55/1.49  --res_time_limit                        2.
% 7.55/1.49  --res_out_proof                         true
% 7.55/1.49  
% 7.55/1.49  ------ Superposition Options
% 7.55/1.49  
% 7.55/1.49  --superposition_flag                    true
% 7.55/1.49  --sup_passive_queue_type                priority_queues
% 7.55/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.55/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.55/1.49  --demod_completeness_check              fast
% 7.55/1.49  --demod_use_ground                      true
% 7.55/1.49  --sup_to_prop_solver                    passive
% 7.55/1.49  --sup_prop_simpl_new                    true
% 7.55/1.49  --sup_prop_simpl_given                  true
% 7.55/1.49  --sup_fun_splitting                     false
% 7.55/1.49  --sup_smt_interval                      50000
% 7.55/1.49  
% 7.55/1.49  ------ Superposition Simplification Setup
% 7.55/1.49  
% 7.55/1.49  --sup_indices_passive                   []
% 7.55/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.55/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.49  --sup_full_bw                           [BwDemod]
% 7.55/1.49  --sup_immed_triv                        [TrivRules]
% 7.55/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.55/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.49  --sup_immed_bw_main                     []
% 7.55/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.55/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.55/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.55/1.49  
% 7.55/1.49  ------ Combination Options
% 7.55/1.49  
% 7.55/1.49  --comb_res_mult                         3
% 7.55/1.49  --comb_sup_mult                         2
% 7.55/1.49  --comb_inst_mult                        10
% 7.55/1.49  
% 7.55/1.49  ------ Debug Options
% 7.55/1.49  
% 7.55/1.49  --dbg_backtrace                         false
% 7.55/1.49  --dbg_dump_prop_clauses                 false
% 7.55/1.49  --dbg_dump_prop_clauses_file            -
% 7.55/1.49  --dbg_out_stat                          false
% 7.55/1.49  ------ Parsing...
% 7.55/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.55/1.49  
% 7.55/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.55/1.49  
% 7.55/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.55/1.49  
% 7.55/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.55/1.49  ------ Proving...
% 7.55/1.49  ------ Problem Properties 
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  clauses                                 38
% 7.55/1.49  conjectures                             2
% 7.55/1.49  EPR                                     3
% 7.55/1.49  Horn                                    29
% 7.55/1.49  unary                                   12
% 7.55/1.49  binary                                  13
% 7.55/1.49  lits                                    81
% 7.55/1.49  lits eq                                 31
% 7.55/1.49  fd_pure                                 0
% 7.55/1.49  fd_pseudo                               0
% 7.55/1.49  fd_cond                                 1
% 7.55/1.49  fd_pseudo_cond                          10
% 7.55/1.49  AC symbols                              0
% 7.55/1.49  
% 7.55/1.49  ------ Schedule dynamic 5 is on 
% 7.55/1.49  
% 7.55/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  ------ 
% 7.55/1.49  Current options:
% 7.55/1.49  ------ 
% 7.55/1.49  
% 7.55/1.49  ------ Input Options
% 7.55/1.49  
% 7.55/1.49  --out_options                           all
% 7.55/1.49  --tptp_safe_out                         true
% 7.55/1.49  --problem_path                          ""
% 7.55/1.49  --include_path                          ""
% 7.55/1.49  --clausifier                            res/vclausify_rel
% 7.55/1.49  --clausifier_options                    --mode clausify
% 7.55/1.49  --stdin                                 false
% 7.55/1.49  --stats_out                             all
% 7.55/1.49  
% 7.55/1.49  ------ General Options
% 7.55/1.49  
% 7.55/1.49  --fof                                   false
% 7.55/1.49  --time_out_real                         305.
% 7.55/1.49  --time_out_virtual                      -1.
% 7.55/1.49  --symbol_type_check                     false
% 7.55/1.49  --clausify_out                          false
% 7.55/1.49  --sig_cnt_out                           false
% 7.55/1.49  --trig_cnt_out                          false
% 7.55/1.49  --trig_cnt_out_tolerance                1.
% 7.55/1.49  --trig_cnt_out_sk_spl                   false
% 7.55/1.49  --abstr_cl_out                          false
% 7.55/1.49  
% 7.55/1.49  ------ Global Options
% 7.55/1.49  
% 7.55/1.49  --schedule                              default
% 7.55/1.49  --add_important_lit                     false
% 7.55/1.49  --prop_solver_per_cl                    1000
% 7.55/1.49  --min_unsat_core                        false
% 7.55/1.49  --soft_assumptions                      false
% 7.55/1.49  --soft_lemma_size                       3
% 7.55/1.49  --prop_impl_unit_size                   0
% 7.55/1.49  --prop_impl_unit                        []
% 7.55/1.49  --share_sel_clauses                     true
% 7.55/1.49  --reset_solvers                         false
% 7.55/1.49  --bc_imp_inh                            [conj_cone]
% 7.55/1.49  --conj_cone_tolerance                   3.
% 7.55/1.49  --extra_neg_conj                        none
% 7.55/1.49  --large_theory_mode                     true
% 7.55/1.49  --prolific_symb_bound                   200
% 7.55/1.49  --lt_threshold                          2000
% 7.55/1.49  --clause_weak_htbl                      true
% 7.55/1.49  --gc_record_bc_elim                     false
% 7.55/1.49  
% 7.55/1.49  ------ Preprocessing Options
% 7.55/1.49  
% 7.55/1.49  --preprocessing_flag                    true
% 7.55/1.49  --time_out_prep_mult                    0.1
% 7.55/1.49  --splitting_mode                        input
% 7.55/1.49  --splitting_grd                         true
% 7.55/1.49  --splitting_cvd                         false
% 7.55/1.49  --splitting_cvd_svl                     false
% 7.55/1.49  --splitting_nvd                         32
% 7.55/1.49  --sub_typing                            true
% 7.55/1.49  --prep_gs_sim                           true
% 7.55/1.49  --prep_unflatten                        true
% 7.55/1.49  --prep_res_sim                          true
% 7.55/1.49  --prep_upred                            true
% 7.55/1.49  --prep_sem_filter                       exhaustive
% 7.55/1.49  --prep_sem_filter_out                   false
% 7.55/1.49  --pred_elim                             true
% 7.55/1.49  --res_sim_input                         true
% 7.55/1.49  --eq_ax_congr_red                       true
% 7.55/1.49  --pure_diseq_elim                       true
% 7.55/1.49  --brand_transform                       false
% 7.55/1.49  --non_eq_to_eq                          false
% 7.55/1.49  --prep_def_merge                        true
% 7.55/1.49  --prep_def_merge_prop_impl              false
% 7.55/1.49  --prep_def_merge_mbd                    true
% 7.55/1.49  --prep_def_merge_tr_red                 false
% 7.55/1.49  --prep_def_merge_tr_cl                  false
% 7.55/1.49  --smt_preprocessing                     true
% 7.55/1.49  --smt_ac_axioms                         fast
% 7.55/1.49  --preprocessed_out                      false
% 7.55/1.49  --preprocessed_stats                    false
% 7.55/1.49  
% 7.55/1.49  ------ Abstraction refinement Options
% 7.55/1.49  
% 7.55/1.49  --abstr_ref                             []
% 7.55/1.49  --abstr_ref_prep                        false
% 7.55/1.49  --abstr_ref_until_sat                   false
% 7.55/1.49  --abstr_ref_sig_restrict                funpre
% 7.55/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.55/1.49  --abstr_ref_under                       []
% 7.55/1.49  
% 7.55/1.49  ------ SAT Options
% 7.55/1.49  
% 7.55/1.49  --sat_mode                              false
% 7.55/1.49  --sat_fm_restart_options                ""
% 7.55/1.49  --sat_gr_def                            false
% 7.55/1.49  --sat_epr_types                         true
% 7.55/1.49  --sat_non_cyclic_types                  false
% 7.55/1.49  --sat_finite_models                     false
% 7.55/1.49  --sat_fm_lemmas                         false
% 7.55/1.49  --sat_fm_prep                           false
% 7.55/1.49  --sat_fm_uc_incr                        true
% 7.55/1.49  --sat_out_model                         small
% 7.55/1.49  --sat_out_clauses                       false
% 7.55/1.49  
% 7.55/1.49  ------ QBF Options
% 7.55/1.49  
% 7.55/1.49  --qbf_mode                              false
% 7.55/1.49  --qbf_elim_univ                         false
% 7.55/1.49  --qbf_dom_inst                          none
% 7.55/1.49  --qbf_dom_pre_inst                      false
% 7.55/1.49  --qbf_sk_in                             false
% 7.55/1.49  --qbf_pred_elim                         true
% 7.55/1.49  --qbf_split                             512
% 7.55/1.49  
% 7.55/1.49  ------ BMC1 Options
% 7.55/1.49  
% 7.55/1.49  --bmc1_incremental                      false
% 7.55/1.49  --bmc1_axioms                           reachable_all
% 7.55/1.49  --bmc1_min_bound                        0
% 7.55/1.49  --bmc1_max_bound                        -1
% 7.55/1.49  --bmc1_max_bound_default                -1
% 7.55/1.49  --bmc1_symbol_reachability              true
% 7.55/1.49  --bmc1_property_lemmas                  false
% 7.55/1.49  --bmc1_k_induction                      false
% 7.55/1.49  --bmc1_non_equiv_states                 false
% 7.55/1.49  --bmc1_deadlock                         false
% 7.55/1.49  --bmc1_ucm                              false
% 7.55/1.49  --bmc1_add_unsat_core                   none
% 7.55/1.49  --bmc1_unsat_core_children              false
% 7.55/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.55/1.49  --bmc1_out_stat                         full
% 7.55/1.49  --bmc1_ground_init                      false
% 7.55/1.49  --bmc1_pre_inst_next_state              false
% 7.55/1.49  --bmc1_pre_inst_state                   false
% 7.55/1.49  --bmc1_pre_inst_reach_state             false
% 7.55/1.49  --bmc1_out_unsat_core                   false
% 7.55/1.49  --bmc1_aig_witness_out                  false
% 7.55/1.49  --bmc1_verbose                          false
% 7.55/1.49  --bmc1_dump_clauses_tptp                false
% 7.55/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.55/1.49  --bmc1_dump_file                        -
% 7.55/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.55/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.55/1.49  --bmc1_ucm_extend_mode                  1
% 7.55/1.49  --bmc1_ucm_init_mode                    2
% 7.55/1.49  --bmc1_ucm_cone_mode                    none
% 7.55/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.55/1.49  --bmc1_ucm_relax_model                  4
% 7.55/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.55/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.55/1.49  --bmc1_ucm_layered_model                none
% 7.55/1.49  --bmc1_ucm_max_lemma_size               10
% 7.55/1.49  
% 7.55/1.49  ------ AIG Options
% 7.55/1.49  
% 7.55/1.49  --aig_mode                              false
% 7.55/1.49  
% 7.55/1.49  ------ Instantiation Options
% 7.55/1.49  
% 7.55/1.49  --instantiation_flag                    true
% 7.55/1.49  --inst_sos_flag                         false
% 7.55/1.49  --inst_sos_phase                        true
% 7.55/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.55/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.55/1.49  --inst_lit_sel_side                     none
% 7.55/1.49  --inst_solver_per_active                1400
% 7.55/1.49  --inst_solver_calls_frac                1.
% 7.55/1.49  --inst_passive_queue_type               priority_queues
% 7.55/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.55/1.49  --inst_passive_queues_freq              [25;2]
% 7.55/1.49  --inst_dismatching                      true
% 7.55/1.49  --inst_eager_unprocessed_to_passive     true
% 7.55/1.49  --inst_prop_sim_given                   true
% 7.55/1.49  --inst_prop_sim_new                     false
% 7.55/1.49  --inst_subs_new                         false
% 7.55/1.49  --inst_eq_res_simp                      false
% 7.55/1.49  --inst_subs_given                       false
% 7.55/1.49  --inst_orphan_elimination               true
% 7.55/1.49  --inst_learning_loop_flag               true
% 7.55/1.49  --inst_learning_start                   3000
% 7.55/1.49  --inst_learning_factor                  2
% 7.55/1.49  --inst_start_prop_sim_after_learn       3
% 7.55/1.49  --inst_sel_renew                        solver
% 7.55/1.49  --inst_lit_activity_flag                true
% 7.55/1.49  --inst_restr_to_given                   false
% 7.55/1.49  --inst_activity_threshold               500
% 7.55/1.49  --inst_out_proof                        true
% 7.55/1.49  
% 7.55/1.49  ------ Resolution Options
% 7.55/1.49  
% 7.55/1.49  --resolution_flag                       false
% 7.55/1.49  --res_lit_sel                           adaptive
% 7.55/1.49  --res_lit_sel_side                      none
% 7.55/1.49  --res_ordering                          kbo
% 7.55/1.49  --res_to_prop_solver                    active
% 7.55/1.49  --res_prop_simpl_new                    false
% 7.55/1.49  --res_prop_simpl_given                  true
% 7.55/1.49  --res_passive_queue_type                priority_queues
% 7.55/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.55/1.49  --res_passive_queues_freq               [15;5]
% 7.55/1.49  --res_forward_subs                      full
% 7.55/1.49  --res_backward_subs                     full
% 7.55/1.49  --res_forward_subs_resolution           true
% 7.55/1.49  --res_backward_subs_resolution          true
% 7.55/1.49  --res_orphan_elimination                true
% 7.55/1.49  --res_time_limit                        2.
% 7.55/1.49  --res_out_proof                         true
% 7.55/1.49  
% 7.55/1.49  ------ Superposition Options
% 7.55/1.49  
% 7.55/1.49  --superposition_flag                    true
% 7.55/1.49  --sup_passive_queue_type                priority_queues
% 7.55/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.55/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.55/1.49  --demod_completeness_check              fast
% 7.55/1.49  --demod_use_ground                      true
% 7.55/1.49  --sup_to_prop_solver                    passive
% 7.55/1.49  --sup_prop_simpl_new                    true
% 7.55/1.49  --sup_prop_simpl_given                  true
% 7.55/1.49  --sup_fun_splitting                     false
% 7.55/1.49  --sup_smt_interval                      50000
% 7.55/1.49  
% 7.55/1.49  ------ Superposition Simplification Setup
% 7.55/1.49  
% 7.55/1.49  --sup_indices_passive                   []
% 7.55/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.55/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.49  --sup_full_bw                           [BwDemod]
% 7.55/1.49  --sup_immed_triv                        [TrivRules]
% 7.55/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.55/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.49  --sup_immed_bw_main                     []
% 7.55/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.55/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.55/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.55/1.49  
% 7.55/1.49  ------ Combination Options
% 7.55/1.49  
% 7.55/1.49  --comb_res_mult                         3
% 7.55/1.49  --comb_sup_mult                         2
% 7.55/1.49  --comb_inst_mult                        10
% 7.55/1.49  
% 7.55/1.49  ------ Debug Options
% 7.55/1.49  
% 7.55/1.49  --dbg_backtrace                         false
% 7.55/1.49  --dbg_dump_prop_clauses                 false
% 7.55/1.49  --dbg_dump_prop_clauses_file            -
% 7.55/1.49  --dbg_out_stat                          false
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  ------ Proving...
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  % SZS status Theorem for theBenchmark.p
% 7.55/1.49  
% 7.55/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.55/1.49  
% 7.55/1.49  fof(f9,axiom,(
% 7.55/1.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.55/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f72,plain,(
% 7.55/1.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f9])).
% 7.55/1.49  
% 7.55/1.49  fof(f18,axiom,(
% 7.55/1.49    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.55/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f46,plain,(
% 7.55/1.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.55/1.49    inference(nnf_transformation,[],[f18])).
% 7.55/1.49  
% 7.55/1.49  fof(f47,plain,(
% 7.55/1.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.55/1.49    inference(flattening,[],[f46])).
% 7.55/1.49  
% 7.55/1.49  fof(f88,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 7.55/1.49    inference(cnf_transformation,[],[f47])).
% 7.55/1.49  
% 7.55/1.49  fof(f14,axiom,(
% 7.55/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.55/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f84,plain,(
% 7.55/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f14])).
% 7.55/1.49  
% 7.55/1.49  fof(f15,axiom,(
% 7.55/1.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.55/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f85,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f15])).
% 7.55/1.49  
% 7.55/1.49  fof(f16,axiom,(
% 7.55/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.55/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f86,plain,(
% 7.55/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f16])).
% 7.55/1.49  
% 7.55/1.49  fof(f17,axiom,(
% 7.55/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.55/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f87,plain,(
% 7.55/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f17])).
% 7.55/1.49  
% 7.55/1.49  fof(f98,plain,(
% 7.55/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 7.55/1.49    inference(definition_unfolding,[],[f86,f87])).
% 7.55/1.49  
% 7.55/1.49  fof(f99,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 7.55/1.49    inference(definition_unfolding,[],[f85,f98])).
% 7.55/1.49  
% 7.55/1.49  fof(f100,plain,(
% 7.55/1.49    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 7.55/1.49    inference(definition_unfolding,[],[f84,f99])).
% 7.55/1.49  
% 7.55/1.49  fof(f120,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))) )),
% 7.55/1.49    inference(definition_unfolding,[],[f88,f100,f100])).
% 7.55/1.49  
% 7.55/1.49  fof(f1,axiom,(
% 7.55/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.55/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f54,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f1])).
% 7.55/1.49  
% 7.55/1.49  fof(f10,axiom,(
% 7.55/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.55/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f73,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.55/1.49    inference(cnf_transformation,[],[f10])).
% 7.55/1.49  
% 7.55/1.49  fof(f102,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.55/1.49    inference(definition_unfolding,[],[f54,f73,f73])).
% 7.55/1.49  
% 7.55/1.49  fof(f7,axiom,(
% 7.55/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.55/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f70,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.55/1.49    inference(cnf_transformation,[],[f7])).
% 7.55/1.49  
% 7.55/1.49  fof(f101,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.55/1.49    inference(definition_unfolding,[],[f70,f73])).
% 7.55/1.49  
% 7.55/1.49  fof(f11,axiom,(
% 7.55/1.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.55/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f74,plain,(
% 7.55/1.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.55/1.49    inference(cnf_transformation,[],[f11])).
% 7.55/1.49  
% 7.55/1.49  fof(f13,axiom,(
% 7.55/1.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.55/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f27,plain,(
% 7.55/1.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.55/1.49    inference(ennf_transformation,[],[f13])).
% 7.55/1.49  
% 7.55/1.49  fof(f41,plain,(
% 7.55/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.55/1.49    inference(nnf_transformation,[],[f27])).
% 7.55/1.49  
% 7.55/1.49  fof(f42,plain,(
% 7.55/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.55/1.49    inference(flattening,[],[f41])).
% 7.55/1.49  
% 7.55/1.49  fof(f43,plain,(
% 7.55/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.55/1.49    inference(rectify,[],[f42])).
% 7.55/1.49  
% 7.55/1.49  fof(f44,plain,(
% 7.55/1.49    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 7.55/1.49    introduced(choice_axiom,[])).
% 7.55/1.49  
% 7.55/1.49  fof(f45,plain,(
% 7.55/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.55/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 7.55/1.49  
% 7.55/1.49  fof(f77,plain,(
% 7.55/1.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.55/1.49    inference(cnf_transformation,[],[f45])).
% 7.55/1.49  
% 7.55/1.49  fof(f116,plain,(
% 7.55/1.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 7.55/1.49    inference(definition_unfolding,[],[f77,f98])).
% 7.55/1.49  
% 7.55/1.49  fof(f137,plain,(
% 7.55/1.49    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 7.55/1.49    inference(equality_resolution,[],[f116])).
% 7.55/1.49  
% 7.55/1.49  fof(f138,plain,(
% 7.55/1.49    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 7.55/1.49    inference(equality_resolution,[],[f137])).
% 7.55/1.49  
% 7.55/1.49  fof(f20,axiom,(
% 7.55/1.49    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 7.55/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f49,plain,(
% 7.55/1.49    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.55/1.49    inference(nnf_transformation,[],[f20])).
% 7.55/1.49  
% 7.55/1.49  fof(f50,plain,(
% 7.55/1.49    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.55/1.49    inference(flattening,[],[f49])).
% 7.55/1.49  
% 7.55/1.49  fof(f95,plain,(
% 7.55/1.49    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f50])).
% 7.55/1.49  
% 7.55/1.49  fof(f123,plain,(
% 7.55/1.49    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 7.55/1.49    inference(definition_unfolding,[],[f95,f99])).
% 7.55/1.49  
% 7.55/1.49  fof(f6,axiom,(
% 7.55/1.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 7.55/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f40,plain,(
% 7.55/1.49    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 7.55/1.49    inference(nnf_transformation,[],[f6])).
% 7.55/1.49  
% 7.55/1.49  fof(f69,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f40])).
% 7.55/1.49  
% 7.55/1.49  fof(f21,conjecture,(
% 7.55/1.49    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 7.55/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f22,negated_conjecture,(
% 7.55/1.49    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 7.55/1.49    inference(negated_conjecture,[],[f21])).
% 7.55/1.49  
% 7.55/1.49  fof(f28,plain,(
% 7.55/1.49    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 7.55/1.49    inference(ennf_transformation,[],[f22])).
% 7.55/1.49  
% 7.55/1.49  fof(f51,plain,(
% 7.55/1.49    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 7.55/1.49    inference(nnf_transformation,[],[f28])).
% 7.55/1.49  
% 7.55/1.49  fof(f52,plain,(
% 7.55/1.49    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4) & (~r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4))),
% 7.55/1.49    introduced(choice_axiom,[])).
% 7.55/1.49  
% 7.55/1.49  fof(f53,plain,(
% 7.55/1.49    (r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4) & (~r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4)),
% 7.55/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f51,f52])).
% 7.55/1.49  
% 7.55/1.49  fof(f97,plain,(
% 7.55/1.49    r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4),
% 7.55/1.49    inference(cnf_transformation,[],[f53])).
% 7.55/1.49  
% 7.55/1.49  fof(f126,plain,(
% 7.55/1.49    r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4),
% 7.55/1.49    inference(definition_unfolding,[],[f97,f100])).
% 7.55/1.49  
% 7.55/1.49  fof(f12,axiom,(
% 7.55/1.49    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 7.55/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f75,plain,(
% 7.55/1.49    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f12])).
% 7.55/1.49  
% 7.55/1.49  fof(f3,axiom,(
% 7.55/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.55/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f23,plain,(
% 7.55/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.55/1.49    inference(rectify,[],[f3])).
% 7.55/1.49  
% 7.55/1.49  fof(f24,plain,(
% 7.55/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.55/1.49    inference(ennf_transformation,[],[f23])).
% 7.55/1.49  
% 7.55/1.49  fof(f34,plain,(
% 7.55/1.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.55/1.49    introduced(choice_axiom,[])).
% 7.55/1.49  
% 7.55/1.49  fof(f35,plain,(
% 7.55/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.55/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f34])).
% 7.55/1.49  
% 7.55/1.49  fof(f63,plain,(
% 7.55/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f35])).
% 7.55/1.49  
% 7.55/1.49  fof(f68,plain,(
% 7.55/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f40])).
% 7.55/1.49  
% 7.55/1.49  fof(f94,plain,(
% 7.55/1.49    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f50])).
% 7.55/1.49  
% 7.55/1.49  fof(f124,plain,(
% 7.55/1.49    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)) )),
% 7.55/1.49    inference(definition_unfolding,[],[f94,f99])).
% 7.55/1.49  
% 7.55/1.49  fof(f19,axiom,(
% 7.55/1.49    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 7.55/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f48,plain,(
% 7.55/1.49    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 7.55/1.49    inference(nnf_transformation,[],[f19])).
% 7.55/1.49  
% 7.55/1.49  fof(f92,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 7.55/1.49    inference(cnf_transformation,[],[f48])).
% 7.55/1.49  
% 7.55/1.49  fof(f121,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) = k3_enumset1(X0,X0,X0,X0,X0) | X0 = X1) )),
% 7.55/1.49    inference(definition_unfolding,[],[f92,f100,f100,f100])).
% 7.55/1.49  
% 7.55/1.49  fof(f91,plain,(
% 7.55/1.49    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f48])).
% 7.55/1.49  
% 7.55/1.49  fof(f122,plain,(
% 7.55/1.49    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) != k3_enumset1(X0,X0,X0,X0,X0)) )),
% 7.55/1.49    inference(definition_unfolding,[],[f91,f100,f100,f100])).
% 7.55/1.49  
% 7.55/1.49  fof(f142,plain,(
% 7.55/1.49    ( ! [X1] : (k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)) != k3_enumset1(X1,X1,X1,X1,X1)) )),
% 7.55/1.49    inference(equality_resolution,[],[f122])).
% 7.55/1.49  
% 7.55/1.49  fof(f96,plain,(
% 7.55/1.49    ~r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4),
% 7.55/1.49    inference(cnf_transformation,[],[f53])).
% 7.55/1.49  
% 7.55/1.49  fof(f127,plain,(
% 7.55/1.49    ~r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = sK4),
% 7.55/1.49    inference(definition_unfolding,[],[f96,f100])).
% 7.55/1.49  
% 7.55/1.49  cnf(c_18,plain,
% 7.55/1.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.55/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1582,plain,
% 7.55/1.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_31,plain,
% 7.55/1.49      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
% 7.55/1.49      | k3_enumset1(X1,X1,X1,X1,X1) = X0
% 7.55/1.49      | k1_xboole_0 = X0 ),
% 7.55/1.49      inference(cnf_transformation,[],[f120]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1570,plain,
% 7.55/1.49      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 7.55/1.49      | k1_xboole_0 = X1
% 7.55/1.49      | r1_tarski(X1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_5110,plain,
% 7.55/1.49      ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k3_enumset1(X0,X0,X0,X0,X0)
% 7.55/1.49      | k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k1_xboole_0 ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_1582,c_1570]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1,plain,
% 7.55/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.55/1.49      inference(cnf_transformation,[],[f102]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_0,plain,
% 7.55/1.49      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.55/1.49      inference(cnf_transformation,[],[f101]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_2077,plain,
% 7.55/1.49      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_30946,plain,
% 7.55/1.49      ( k5_xboole_0(X0,k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1))) = k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1))
% 7.55/1.49      | k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X0) = k1_xboole_0 ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_5110,c_2077]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_19,plain,
% 7.55/1.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.55/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_27,plain,
% 7.55/1.49      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
% 7.55/1.49      inference(cnf_transformation,[],[f138]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1574,plain,
% 7.55/1.49      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) = iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_34,plain,
% 7.55/1.49      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
% 7.55/1.49      | ~ r2_hidden(X0,X2)
% 7.55/1.49      | ~ r2_hidden(X1,X2) ),
% 7.55/1.49      inference(cnf_transformation,[],[f123]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1569,plain,
% 7.55/1.49      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) = iProver_top
% 7.55/1.49      | r2_hidden(X0,X2) != iProver_top
% 7.55/1.49      | r2_hidden(X1,X2) != iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_15,plain,
% 7.55/1.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.55/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1585,plain,
% 7.55/1.49      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 7.55/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_3403,plain,
% 7.55/1.49      ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k1_xboole_0
% 7.55/1.49      | r2_hidden(X1,X2) != iProver_top
% 7.55/1.49      | r2_hidden(X0,X2) != iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_1569,c_1585]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_14433,plain,
% 7.55/1.49      ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X0,X0,X0,X2,X3)) = k1_xboole_0
% 7.55/1.49      | r2_hidden(X1,k3_enumset1(X0,X0,X0,X2,X3)) != iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_1574,c_3403]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_24595,plain,
% 7.55/1.49      ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X1,X2)) = k1_xboole_0 ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_1574,c_14433]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_31363,plain,
% 7.55/1.49      ( k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0
% 7.55/1.49      | k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X0) = k1_xboole_0 ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_30946,c_19,c_24595]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_37,negated_conjecture,
% 7.55/1.49      ( r2_hidden(sK5,sK4)
% 7.55/1.49      | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4 ),
% 7.55/1.49      inference(cnf_transformation,[],[f126]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1566,plain,
% 7.55/1.49      ( k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4
% 7.55/1.49      | r2_hidden(sK5,sK4) = iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_32008,plain,
% 7.55/1.49      ( k4_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4) = k1_xboole_0
% 7.55/1.49      | r2_hidden(sK5,sK4) = iProver_top ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_31363,c_1566]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_20,plain,
% 7.55/1.49      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 7.55/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_2248,plain,
% 7.55/1.49      ( r1_xboole_0(k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X2,X3)),k3_enumset1(X1,X1,X1,X2,X3)) ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_20]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_26141,plain,
% 7.55/1.49      ( r1_xboole_0(k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_2248]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_26142,plain,
% 7.55/1.49      ( r1_xboole_0(k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_26141]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_8,plain,
% 7.55/1.49      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 7.55/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_2205,plain,
% 7.55/1.49      ( ~ r1_xboole_0(k4_xboole_0(X0,X1),X1)
% 7.55/1.49      | ~ r2_hidden(X2,X1)
% 7.55/1.49      | ~ r2_hidden(X2,k4_xboole_0(X0,X1)) ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_13076,plain,
% 7.55/1.49      ( ~ r1_xboole_0(k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)),k3_enumset1(sK5,sK5,sK5,sK5,sK5))
% 7.55/1.49      | ~ r2_hidden(X0,k3_enumset1(sK5,sK5,sK5,sK5,sK5))
% 7.55/1.49      | ~ r2_hidden(X0,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_2205]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_13077,plain,
% 7.55/1.49      ( r1_xboole_0(k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != iProver_top
% 7.55/1.49      | r2_hidden(X0,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != iProver_top
% 7.55/1.49      | r2_hidden(X0,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) != iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_13076]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_13079,plain,
% 7.55/1.49      ( r1_xboole_0(k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != iProver_top
% 7.55/1.49      | r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != iProver_top
% 7.55/1.49      | r2_hidden(sK5,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) != iProver_top ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_13077]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_16,plain,
% 7.55/1.49      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.55/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1851,plain,
% 7.55/1.49      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
% 7.55/1.49      | k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) != k1_xboole_0 ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_16]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_4826,plain,
% 7.55/1.49      ( r1_tarski(k3_enumset1(sK5,sK5,sK5,sK5,X0),sK4)
% 7.55/1.49      | k4_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,X0),sK4) != k1_xboole_0 ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_1851]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_4828,plain,
% 7.55/1.49      ( k4_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,X0),sK4) != k1_xboole_0
% 7.55/1.49      | r1_tarski(k3_enumset1(sK5,sK5,sK5,sK5,X0),sK4) = iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_4826]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_4830,plain,
% 7.55/1.49      ( k4_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4) != k1_xboole_0
% 7.55/1.49      | r1_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4) = iProver_top ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_4828]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_843,plain,
% 7.55/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.55/1.49      theory(equality) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1933,plain,
% 7.55/1.49      ( r2_hidden(X0,X1) | ~ r2_hidden(sK5,sK4) | X1 != sK4 | X0 != sK5 ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_843]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_2594,plain,
% 7.55/1.49      ( r2_hidden(X0,k4_xboole_0(X1,X2))
% 7.55/1.49      | ~ r2_hidden(sK5,sK4)
% 7.55/1.49      | X0 != sK5
% 7.55/1.49      | k4_xboole_0(X1,X2) != sK4 ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_1933]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_3180,plain,
% 7.55/1.49      ( r2_hidden(X0,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)))
% 7.55/1.49      | ~ r2_hidden(sK5,sK4)
% 7.55/1.49      | X0 != sK5
% 7.55/1.49      | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4 ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_2594]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_3181,plain,
% 7.55/1.49      ( X0 != sK5
% 7.55/1.49      | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4
% 7.55/1.49      | r2_hidden(X0,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) = iProver_top
% 7.55/1.49      | r2_hidden(sK5,sK4) != iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_3180]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_3183,plain,
% 7.55/1.49      ( k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4
% 7.55/1.49      | sK5 != sK5
% 7.55/1.49      | r2_hidden(sK5,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) = iProver_top
% 7.55/1.49      | r2_hidden(sK5,sK4) != iProver_top ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_3181]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_35,plain,
% 7.55/1.49      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2) ),
% 7.55/1.49      inference(cnf_transformation,[],[f124]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_2229,plain,
% 7.55/1.49      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,sK5),sK4)
% 7.55/1.49      | r2_hidden(sK5,sK4) ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_35]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_2230,plain,
% 7.55/1.49      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,sK5),sK4) != iProver_top
% 7.55/1.49      | r2_hidden(sK5,sK4) = iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_2229]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_2232,plain,
% 7.55/1.49      ( r1_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4) != iProver_top
% 7.55/1.49      | r2_hidden(sK5,sK4) = iProver_top ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_2230]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_62,plain,
% 7.55/1.49      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) = iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_64,plain,
% 7.55/1.49      ( r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_62]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_32,plain,
% 7.55/1.49      ( X0 = X1
% 7.55/1.49      | k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X0,X0,X0,X0,X0)) = k3_enumset1(X1,X1,X1,X1,X1) ),
% 7.55/1.49      inference(cnf_transformation,[],[f121]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_49,plain,
% 7.55/1.49      ( k4_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = k3_enumset1(sK5,sK5,sK5,sK5,sK5)
% 7.55/1.49      | sK5 = sK5 ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_32]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_33,plain,
% 7.55/1.49      ( k4_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0)) != k3_enumset1(X0,X0,X0,X0,X0) ),
% 7.55/1.49      inference(cnf_transformation,[],[f142]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_48,plain,
% 7.55/1.49      ( k4_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != k3_enumset1(sK5,sK5,sK5,sK5,sK5) ),
% 7.55/1.49      inference(instantiation,[status(thm)],[c_33]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_38,negated_conjecture,
% 7.55/1.49      ( ~ r2_hidden(sK5,sK4)
% 7.55/1.49      | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = sK4 ),
% 7.55/1.49      inference(cnf_transformation,[],[f127]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_39,plain,
% 7.55/1.49      ( k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = sK4
% 7.55/1.49      | r2_hidden(sK5,sK4) != iProver_top ),
% 7.55/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(contradiction,plain,
% 7.55/1.49      ( $false ),
% 7.55/1.49      inference(minisat,
% 7.55/1.49                [status(thm)],
% 7.55/1.49                [c_32008,c_26142,c_13079,c_4830,c_3183,c_2232,c_64,c_49,
% 7.55/1.49                 c_48,c_39]) ).
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.55/1.49  
% 7.55/1.49  ------                               Statistics
% 7.55/1.49  
% 7.55/1.49  ------ General
% 7.55/1.49  
% 7.55/1.49  abstr_ref_over_cycles:                  0
% 7.55/1.49  abstr_ref_under_cycles:                 0
% 7.55/1.49  gc_basic_clause_elim:                   0
% 7.55/1.49  forced_gc_time:                         0
% 7.55/1.49  parsing_time:                           0.01
% 7.55/1.49  unif_index_cands_time:                  0.
% 7.55/1.49  unif_index_add_time:                    0.
% 7.55/1.49  orderings_time:                         0.
% 7.55/1.49  out_proof_time:                         0.008
% 7.55/1.49  total_time:                             0.818
% 7.55/1.49  num_of_symbols:                         44
% 7.55/1.49  num_of_terms:                           35040
% 7.55/1.49  
% 7.55/1.49  ------ Preprocessing
% 7.55/1.49  
% 7.55/1.49  num_of_splits:                          0
% 7.55/1.49  num_of_split_atoms:                     0
% 7.55/1.49  num_of_reused_defs:                     0
% 7.55/1.49  num_eq_ax_congr_red:                    36
% 7.55/1.49  num_of_sem_filtered_clauses:            1
% 7.55/1.49  num_of_subtypes:                        0
% 7.55/1.49  monotx_restored_types:                  0
% 7.55/1.49  sat_num_of_epr_types:                   0
% 7.55/1.49  sat_num_of_non_cyclic_types:            0
% 7.55/1.49  sat_guarded_non_collapsed_types:        0
% 7.55/1.49  num_pure_diseq_elim:                    0
% 7.55/1.49  simp_replaced_by:                       0
% 7.55/1.49  res_preprocessed:                       169
% 7.55/1.49  prep_upred:                             0
% 7.55/1.49  prep_unflattend:                        4
% 7.55/1.49  smt_new_axioms:                         0
% 7.55/1.49  pred_elim_cands:                        3
% 7.55/1.49  pred_elim:                              0
% 7.55/1.49  pred_elim_cl:                           0
% 7.55/1.49  pred_elim_cycles:                       2
% 7.55/1.49  merged_defs:                            16
% 7.55/1.49  merged_defs_ncl:                        0
% 7.55/1.49  bin_hyper_res:                          16
% 7.55/1.49  prep_cycles:                            4
% 7.55/1.49  pred_elim_time:                         0.002
% 7.55/1.49  splitting_time:                         0.
% 7.55/1.49  sem_filter_time:                        0.
% 7.55/1.49  monotx_time:                            0.
% 7.55/1.49  subtype_inf_time:                       0.
% 7.55/1.49  
% 7.55/1.49  ------ Problem properties
% 7.55/1.49  
% 7.55/1.49  clauses:                                38
% 7.55/1.49  conjectures:                            2
% 7.55/1.49  epr:                                    3
% 7.55/1.49  horn:                                   29
% 7.55/1.49  ground:                                 2
% 7.55/1.49  unary:                                  12
% 7.55/1.49  binary:                                 13
% 7.55/1.49  lits:                                   81
% 7.55/1.49  lits_eq:                                31
% 7.55/1.49  fd_pure:                                0
% 7.55/1.49  fd_pseudo:                              0
% 7.55/1.49  fd_cond:                                1
% 7.55/1.49  fd_pseudo_cond:                         10
% 7.55/1.49  ac_symbols:                             0
% 7.55/1.49  
% 7.55/1.49  ------ Propositional Solver
% 7.55/1.49  
% 7.55/1.49  prop_solver_calls:                      29
% 7.55/1.49  prop_fast_solver_calls:                 1134
% 7.55/1.49  smt_solver_calls:                       0
% 7.55/1.49  smt_fast_solver_calls:                  0
% 7.55/1.49  prop_num_of_clauses:                    8250
% 7.55/1.49  prop_preprocess_simplified:             19634
% 7.55/1.49  prop_fo_subsumed:                       7
% 7.55/1.49  prop_solver_time:                       0.
% 7.55/1.49  smt_solver_time:                        0.
% 7.55/1.49  smt_fast_solver_time:                   0.
% 7.55/1.49  prop_fast_solver_time:                  0.
% 7.55/1.49  prop_unsat_core_time:                   0.
% 7.55/1.49  
% 7.55/1.49  ------ QBF
% 7.55/1.49  
% 7.55/1.49  qbf_q_res:                              0
% 7.55/1.49  qbf_num_tautologies:                    0
% 7.55/1.49  qbf_prep_cycles:                        0
% 7.55/1.49  
% 7.55/1.49  ------ BMC1
% 7.55/1.49  
% 7.55/1.49  bmc1_current_bound:                     -1
% 7.55/1.49  bmc1_last_solved_bound:                 -1
% 7.55/1.49  bmc1_unsat_core_size:                   -1
% 7.55/1.49  bmc1_unsat_core_parents_size:           -1
% 7.55/1.49  bmc1_merge_next_fun:                    0
% 7.55/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.55/1.49  
% 7.55/1.49  ------ Instantiation
% 7.55/1.49  
% 7.55/1.49  inst_num_of_clauses:                    2014
% 7.55/1.49  inst_num_in_passive:                    1082
% 7.55/1.49  inst_num_in_active:                     610
% 7.55/1.49  inst_num_in_unprocessed:                328
% 7.55/1.49  inst_num_of_loops:                      870
% 7.55/1.49  inst_num_of_learning_restarts:          0
% 7.55/1.49  inst_num_moves_active_passive:          257
% 7.55/1.49  inst_lit_activity:                      0
% 7.55/1.49  inst_lit_activity_moves:                0
% 7.55/1.49  inst_num_tautologies:                   0
% 7.55/1.49  inst_num_prop_implied:                  0
% 7.55/1.49  inst_num_existing_simplified:           0
% 7.55/1.49  inst_num_eq_res_simplified:             0
% 7.55/1.49  inst_num_child_elim:                    0
% 7.55/1.49  inst_num_of_dismatching_blockings:      2250
% 7.55/1.49  inst_num_of_non_proper_insts:           2596
% 7.55/1.49  inst_num_of_duplicates:                 0
% 7.55/1.49  inst_inst_num_from_inst_to_res:         0
% 7.55/1.49  inst_dismatching_checking_time:         0.
% 7.55/1.49  
% 7.55/1.49  ------ Resolution
% 7.55/1.49  
% 7.55/1.49  res_num_of_clauses:                     0
% 7.55/1.49  res_num_in_passive:                     0
% 7.55/1.49  res_num_in_active:                      0
% 7.55/1.49  res_num_of_loops:                       173
% 7.55/1.49  res_forward_subset_subsumed:            530
% 7.55/1.49  res_backward_subset_subsumed:           20
% 7.55/1.49  res_forward_subsumed:                   0
% 7.55/1.49  res_backward_subsumed:                  0
% 7.55/1.49  res_forward_subsumption_resolution:     0
% 7.55/1.49  res_backward_subsumption_resolution:    0
% 7.55/1.49  res_clause_to_clause_subsumption:       9321
% 7.55/1.49  res_orphan_elimination:                 0
% 7.55/1.49  res_tautology_del:                      107
% 7.55/1.49  res_num_eq_res_simplified:              0
% 7.55/1.49  res_num_sel_changes:                    0
% 7.55/1.49  res_moves_from_active_to_pass:          0
% 7.55/1.49  
% 7.55/1.49  ------ Superposition
% 7.55/1.49  
% 7.55/1.49  sup_time_total:                         0.
% 7.55/1.49  sup_time_generating:                    0.
% 7.55/1.49  sup_time_sim_full:                      0.
% 7.55/1.49  sup_time_sim_immed:                     0.
% 7.55/1.49  
% 7.55/1.49  sup_num_of_clauses:                     663
% 7.55/1.49  sup_num_in_active:                      168
% 7.55/1.49  sup_num_in_passive:                     495
% 7.55/1.49  sup_num_of_loops:                       172
% 7.55/1.49  sup_fw_superposition:                   1974
% 7.55/1.49  sup_bw_superposition:                   2863
% 7.55/1.49  sup_immediate_simplified:               3145
% 7.55/1.49  sup_given_eliminated:                   1
% 7.55/1.49  comparisons_done:                       0
% 7.55/1.49  comparisons_avoided:                    19
% 7.55/1.49  
% 7.55/1.49  ------ Simplifications
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  sim_fw_subset_subsumed:                 262
% 7.55/1.49  sim_bw_subset_subsumed:                 7
% 7.55/1.49  sim_fw_subsumed:                        994
% 7.55/1.49  sim_bw_subsumed:                        10
% 7.55/1.49  sim_fw_subsumption_res:                 0
% 7.55/1.49  sim_bw_subsumption_res:                 0
% 7.55/1.49  sim_tautology_del:                      106
% 7.55/1.49  sim_eq_tautology_del:                   566
% 7.55/1.49  sim_eq_res_simp:                        20
% 7.55/1.49  sim_fw_demodulated:                     2053
% 7.55/1.49  sim_bw_demodulated:                     23
% 7.55/1.49  sim_light_normalised:                   837
% 7.55/1.49  sim_joinable_taut:                      0
% 7.55/1.49  sim_joinable_simp:                      0
% 7.55/1.49  sim_ac_normalised:                      0
% 7.55/1.49  sim_smt_subsumption:                    0
% 7.55/1.49  
%------------------------------------------------------------------------------
