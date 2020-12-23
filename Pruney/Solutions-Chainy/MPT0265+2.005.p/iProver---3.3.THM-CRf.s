%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:21 EST 2020

% Result     : Theorem 7.92s
% Output     : CNFRefutation 7.92s
% Verified   : 
% Statistics : Number of formulae       :  105 (1265 expanded)
%              Number of clauses        :   48 ( 259 expanded)
%              Number of leaves         :   15 ( 363 expanded)
%              Depth                    :   21
%              Number of atoms          :  443 (5566 expanded)
%              Number of equality atoms :  229 (2556 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,X1)
       => ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
          | ( X0 != X2
            & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
        & ( X0 = X2
          | ~ r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) )
   => ( k3_xboole_0(k2_tarski(sK3,sK5),sK4) != k1_tarski(sK3)
      & ( sK3 = sK5
        | ~ r2_hidden(sK5,sK4) )
      & r2_hidden(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( k3_xboole_0(k2_tarski(sK3,sK5),sK4) != k1_tarski(sK3)
    & ( sK3 = sK5
      | ~ r2_hidden(sK5,sK4) )
    & r2_hidden(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f12,f27])).

fof(f53,plain,(
    k3_xboole_0(k2_tarski(sK3,sK5),sK4) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f54])).

fof(f68,plain,(
    k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),sK4) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f53,f54,f55])).

fof(f51,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,
    ( sK3 = sK5
    | ~ r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

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
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f44,f55])).

fof(f81,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f45,f55])).

fof(f79,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f66])).

fof(f80,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f79])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).

fof(f36,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f36,f50])).

fof(f78,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f38,f50])).

fof(f74,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f61])).

fof(f75,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k2_enumset1(X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f74])).

fof(f39,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f39,f50])).

fof(f72,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f60])).

fof(f73,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f72])).

cnf(c_218,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_217,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5873,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X2,X3,X4))
    | r2_hidden(X5,k2_enumset1(X6,X7,X8,X9))
    | X6 != X1
    | X7 != X2
    | X8 != X3
    | X9 != X4
    | X5 != X0 ),
    inference(resolution,[status(thm)],[c_218,c_217])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_19,negated_conjecture,
    ( k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),sK4) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1152,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK5))
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(resolution,[status(thm)],[c_3,c_19])).

cnf(c_17844,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X2,X3,X4))
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | X0 != sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3))
    | X4 != sK5
    | X1 != sK3
    | X2 != sK3
    | X3 != sK3 ),
    inference(resolution,[status(thm)],[c_5873,c_1152])).

cnf(c_214,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_17951,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(X0,X1,X2,X3))
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | X3 != sK5
    | X0 != sK3
    | X1 != sK3
    | X2 != sK3 ),
    inference(resolution,[status(thm)],[c_17844,c_214])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( ~ r2_hidden(sK5,sK4)
    | sK3 = sK5 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_25,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_28,plain,
    ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_669,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK5))
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),sK4) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_840,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_1015,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_217,c_214])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1025,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4) ),
    inference(resolution,[status(thm)],[c_2,c_19])).

cnf(c_1182,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
    inference(resolution,[status(thm)],[c_1025,c_18])).

cnf(c_7515,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),X0)
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | ~ r2_hidden(sK3,X0) ),
    inference(resolution,[status(thm)],[c_1015,c_1182])).

cnf(c_7940,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | ~ r2_hidden(sK3,sK4) ),
    inference(factoring,[status(thm)],[c_7515])).

cnf(c_215,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1002,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_215,c_214])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2819,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK5
    | sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
    inference(resolution,[status(thm)],[c_14,c_1152])).

cnf(c_3172,plain,
    ( sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK5
    | sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2819,c_18])).

cnf(c_7233,plain,
    ( sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3
    | sK5 = sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(resolution,[status(thm)],[c_1002,c_3172])).

cnf(c_8102,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),X0)
    | ~ r2_hidden(sK3,X0)
    | sK5 = sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(resolution,[status(thm)],[c_7233,c_1015])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_10358,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK5))
    | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),sK4) = k2_enumset1(sK3,sK3,sK3,sK3)
    | sK5 = sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(resolution,[status(thm)],[c_8102,c_1])).

cnf(c_1397,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | X0 != sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3))
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_217])).

cnf(c_4934,plain,
    ( r2_hidden(X0,sK4)
    | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | X0 != sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1397])).

cnf(c_15582,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | r2_hidden(sK5,sK4)
    | sK4 != sK4
    | sK5 != sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_4934])).

cnf(c_17953,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | sK3 != sK5
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_17951])).

cnf(c_18009,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17951,c_21,c_20,c_19,c_25,c_28,c_669,c_840,c_7940,c_10358,c_15582,c_17953])).

cnf(c_18410,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK5))
    | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),sK4) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(resolution,[status(thm)],[c_18009,c_1])).

cnf(c_690,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK5))
    | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),sK4) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_20612,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18410,c_21,c_20,c_19,c_25,c_28,c_669,c_690,c_840,c_7940,c_10358,c_15582,c_17953])).

cnf(c_7533,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),X0)
    | ~ r2_hidden(sK5,X0)
    | sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
    inference(resolution,[status(thm)],[c_1015,c_3172])).

cnf(c_8292,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),X0)
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),X1)
    | ~ r2_hidden(sK5,X0)
    | ~ r2_hidden(sK3,X1) ),
    inference(resolution,[status(thm)],[c_7533,c_1015])).

cnf(c_20630,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),X0)
    | ~ r2_hidden(sK5,X0)
    | ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK5)) ),
    inference(resolution,[status(thm)],[c_20612,c_8292])).

cnf(c_12,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_20812,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),X0)
    | ~ r2_hidden(sK5,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_20630,c_12])).

cnf(c_21170,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(sK3,sK3,sK3,sK5)) ),
    inference(resolution,[status(thm)],[c_20812,c_20612])).

cnf(c_11,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_22184,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_21170,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:21:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.92/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.92/1.49  
% 7.92/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.92/1.49  
% 7.92/1.49  ------  iProver source info
% 7.92/1.49  
% 7.92/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.92/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.92/1.49  git: non_committed_changes: false
% 7.92/1.49  git: last_make_outside_of_git: false
% 7.92/1.49  
% 7.92/1.49  ------ 
% 7.92/1.49  ------ Parsing...
% 7.92/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.92/1.49  
% 7.92/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.92/1.49  
% 7.92/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.92/1.49  
% 7.92/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.92/1.49  ------ Proving...
% 7.92/1.49  ------ Problem Properties 
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  clauses                                 22
% 7.92/1.49  conjectures                             3
% 7.92/1.49  EPR                                     2
% 7.92/1.49  Horn                                    17
% 7.92/1.49  unary                                   7
% 7.92/1.49  binary                                  4
% 7.92/1.49  lits                                    52
% 7.92/1.49  lits eq                                 24
% 7.92/1.49  fd_pure                                 0
% 7.92/1.49  fd_pseudo                               0
% 7.92/1.49  fd_cond                                 0
% 7.92/1.49  fd_pseudo_cond                          9
% 7.92/1.49  AC symbols                              0
% 7.92/1.49  
% 7.92/1.49  ------ Input Options Time Limit: Unbounded
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  ------ 
% 7.92/1.49  Current options:
% 7.92/1.49  ------ 
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  ------ Proving...
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  % SZS status Theorem for theBenchmark.p
% 7.92/1.49  
% 7.92/1.49   Resolution empty clause
% 7.92/1.49  
% 7.92/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.92/1.49  
% 7.92/1.49  fof(f2,axiom,(
% 7.92/1.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f13,plain,(
% 7.92/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.92/1.49    inference(nnf_transformation,[],[f2])).
% 7.92/1.49  
% 7.92/1.49  fof(f14,plain,(
% 7.92/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.92/1.49    inference(flattening,[],[f13])).
% 7.92/1.49  
% 7.92/1.49  fof(f15,plain,(
% 7.92/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.92/1.49    inference(rectify,[],[f14])).
% 7.92/1.49  
% 7.92/1.49  fof(f16,plain,(
% 7.92/1.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.92/1.49    introduced(choice_axiom,[])).
% 7.92/1.49  
% 7.92/1.49  fof(f17,plain,(
% 7.92/1.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.92/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 7.92/1.49  
% 7.92/1.49  fof(f33,plain,(
% 7.92/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f17])).
% 7.92/1.49  
% 7.92/1.49  fof(f8,conjecture,(
% 7.92/1.49    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0) | (X0 != X2 & r2_hidden(X2,X1))))),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f9,negated_conjecture,(
% 7.92/1.49    ~! [X0,X1,X2] : (r2_hidden(X0,X1) => (k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0) | (X0 != X2 & r2_hidden(X2,X1))))),
% 7.92/1.49    inference(negated_conjecture,[],[f8])).
% 7.92/1.49  
% 7.92/1.49  fof(f11,plain,(
% 7.92/1.49    ? [X0,X1,X2] : ((k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) & (X0 = X2 | ~r2_hidden(X2,X1))) & r2_hidden(X0,X1))),
% 7.92/1.49    inference(ennf_transformation,[],[f9])).
% 7.92/1.49  
% 7.92/1.49  fof(f12,plain,(
% 7.92/1.49    ? [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 7.92/1.49    inference(flattening,[],[f11])).
% 7.92/1.49  
% 7.92/1.49  fof(f27,plain,(
% 7.92/1.49    ? [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1)) => (k3_xboole_0(k2_tarski(sK3,sK5),sK4) != k1_tarski(sK3) & (sK3 = sK5 | ~r2_hidden(sK5,sK4)) & r2_hidden(sK3,sK4))),
% 7.92/1.49    introduced(choice_axiom,[])).
% 7.92/1.49  
% 7.92/1.49  fof(f28,plain,(
% 7.92/1.49    k3_xboole_0(k2_tarski(sK3,sK5),sK4) != k1_tarski(sK3) & (sK3 = sK5 | ~r2_hidden(sK5,sK4)) & r2_hidden(sK3,sK4)),
% 7.92/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f12,f27])).
% 7.92/1.49  
% 7.92/1.49  fof(f53,plain,(
% 7.92/1.49    k3_xboole_0(k2_tarski(sK3,sK5),sK4) != k1_tarski(sK3)),
% 7.92/1.49    inference(cnf_transformation,[],[f28])).
% 7.92/1.49  
% 7.92/1.49  fof(f5,axiom,(
% 7.92/1.49    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f48,plain,(
% 7.92/1.49    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f5])).
% 7.92/1.49  
% 7.92/1.49  fof(f6,axiom,(
% 7.92/1.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f49,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f6])).
% 7.92/1.49  
% 7.92/1.49  fof(f7,axiom,(
% 7.92/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f50,plain,(
% 7.92/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f7])).
% 7.92/1.49  
% 7.92/1.49  fof(f54,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.92/1.49    inference(definition_unfolding,[],[f49,f50])).
% 7.92/1.49  
% 7.92/1.49  fof(f55,plain,(
% 7.92/1.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.92/1.49    inference(definition_unfolding,[],[f48,f54])).
% 7.92/1.49  
% 7.92/1.49  fof(f68,plain,(
% 7.92/1.49    k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),sK4) != k2_enumset1(sK3,sK3,sK3,sK3)),
% 7.92/1.49    inference(definition_unfolding,[],[f53,f54,f55])).
% 7.92/1.49  
% 7.92/1.49  fof(f51,plain,(
% 7.92/1.49    r2_hidden(sK3,sK4)),
% 7.92/1.49    inference(cnf_transformation,[],[f28])).
% 7.92/1.49  
% 7.92/1.49  fof(f52,plain,(
% 7.92/1.49    sK3 = sK5 | ~r2_hidden(sK5,sK4)),
% 7.92/1.49    inference(cnf_transformation,[],[f28])).
% 7.92/1.49  
% 7.92/1.49  fof(f4,axiom,(
% 7.92/1.49    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f23,plain,(
% 7.92/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.92/1.49    inference(nnf_transformation,[],[f4])).
% 7.92/1.49  
% 7.92/1.49  fof(f24,plain,(
% 7.92/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.92/1.49    inference(rectify,[],[f23])).
% 7.92/1.49  
% 7.92/1.49  fof(f25,plain,(
% 7.92/1.49    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 7.92/1.49    introduced(choice_axiom,[])).
% 7.92/1.49  
% 7.92/1.49  fof(f26,plain,(
% 7.92/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.92/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 7.92/1.49  
% 7.92/1.49  fof(f44,plain,(
% 7.92/1.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.92/1.49    inference(cnf_transformation,[],[f26])).
% 7.92/1.49  
% 7.92/1.49  fof(f67,plain,(
% 7.92/1.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 7.92/1.49    inference(definition_unfolding,[],[f44,f55])).
% 7.92/1.49  
% 7.92/1.49  fof(f81,plain,(
% 7.92/1.49    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 7.92/1.49    inference(equality_resolution,[],[f67])).
% 7.92/1.49  
% 7.92/1.49  fof(f45,plain,(
% 7.92/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.92/1.49    inference(cnf_transformation,[],[f26])).
% 7.92/1.49  
% 7.92/1.49  fof(f66,plain,(
% 7.92/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 7.92/1.49    inference(definition_unfolding,[],[f45,f55])).
% 7.92/1.49  
% 7.92/1.49  fof(f79,plain,(
% 7.92/1.49    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 7.92/1.49    inference(equality_resolution,[],[f66])).
% 7.92/1.49  
% 7.92/1.49  fof(f80,plain,(
% 7.92/1.49    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 7.92/1.49    inference(equality_resolution,[],[f79])).
% 7.92/1.49  
% 7.92/1.49  fof(f34,plain,(
% 7.92/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f17])).
% 7.92/1.49  
% 7.92/1.49  fof(f3,axiom,(
% 7.92/1.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f10,plain,(
% 7.92/1.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.92/1.49    inference(ennf_transformation,[],[f3])).
% 7.92/1.49  
% 7.92/1.49  fof(f18,plain,(
% 7.92/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.92/1.49    inference(nnf_transformation,[],[f10])).
% 7.92/1.49  
% 7.92/1.49  fof(f19,plain,(
% 7.92/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.92/1.49    inference(flattening,[],[f18])).
% 7.92/1.49  
% 7.92/1.49  fof(f20,plain,(
% 7.92/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.92/1.49    inference(rectify,[],[f19])).
% 7.92/1.49  
% 7.92/1.49  fof(f21,plain,(
% 7.92/1.49    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 7.92/1.49    introduced(choice_axiom,[])).
% 7.92/1.49  
% 7.92/1.49  fof(f22,plain,(
% 7.92/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.92/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).
% 7.92/1.49  
% 7.92/1.49  fof(f36,plain,(
% 7.92/1.49    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 7.92/1.49    inference(cnf_transformation,[],[f22])).
% 7.92/1.49  
% 7.92/1.49  fof(f63,plain,(
% 7.92/1.49    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 7.92/1.49    inference(definition_unfolding,[],[f36,f50])).
% 7.92/1.49  
% 7.92/1.49  fof(f78,plain,(
% 7.92/1.49    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 7.92/1.49    inference(equality_resolution,[],[f63])).
% 7.92/1.49  
% 7.92/1.49  fof(f35,plain,(
% 7.92/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f17])).
% 7.92/1.49  
% 7.92/1.49  fof(f38,plain,(
% 7.92/1.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.92/1.49    inference(cnf_transformation,[],[f22])).
% 7.92/1.49  
% 7.92/1.49  fof(f61,plain,(
% 7.92/1.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 7.92/1.49    inference(definition_unfolding,[],[f38,f50])).
% 7.92/1.49  
% 7.92/1.49  fof(f74,plain,(
% 7.92/1.49    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X5,X2) != X3) )),
% 7.92/1.49    inference(equality_resolution,[],[f61])).
% 7.92/1.49  
% 7.92/1.49  fof(f75,plain,(
% 7.92/1.49    ( ! [X2,X0,X5] : (r2_hidden(X5,k2_enumset1(X0,X0,X5,X2))) )),
% 7.92/1.49    inference(equality_resolution,[],[f74])).
% 7.92/1.49  
% 7.92/1.49  fof(f39,plain,(
% 7.92/1.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.92/1.49    inference(cnf_transformation,[],[f22])).
% 7.92/1.49  
% 7.92/1.49  fof(f60,plain,(
% 7.92/1.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 7.92/1.49    inference(definition_unfolding,[],[f39,f50])).
% 7.92/1.49  
% 7.92/1.49  fof(f72,plain,(
% 7.92/1.49    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 7.92/1.49    inference(equality_resolution,[],[f60])).
% 7.92/1.49  
% 7.92/1.49  fof(f73,plain,(
% 7.92/1.49    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 7.92/1.49    inference(equality_resolution,[],[f72])).
% 7.92/1.49  
% 7.92/1.49  cnf(c_218,plain,
% 7.92/1.49      ( X0 != X1
% 7.92/1.49      | X2 != X3
% 7.92/1.49      | X4 != X5
% 7.92/1.49      | X6 != X7
% 7.92/1.49      | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
% 7.92/1.49      theory(equality) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_217,plain,
% 7.92/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.92/1.49      theory(equality) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_5873,plain,
% 7.92/1.49      ( ~ r2_hidden(X0,k2_enumset1(X1,X2,X3,X4))
% 7.92/1.49      | r2_hidden(X5,k2_enumset1(X6,X7,X8,X9))
% 7.92/1.49      | X6 != X1
% 7.92/1.49      | X7 != X2
% 7.92/1.49      | X8 != X3
% 7.92/1.49      | X9 != X4
% 7.92/1.49      | X5 != X0 ),
% 7.92/1.49      inference(resolution,[status(thm)],[c_218,c_217]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3,plain,
% 7.92/1.49      ( r2_hidden(sK0(X0,X1,X2),X0)
% 7.92/1.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.92/1.49      | k3_xboole_0(X0,X1) = X2 ),
% 7.92/1.49      inference(cnf_transformation,[],[f33]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_19,negated_conjecture,
% 7.92/1.49      ( k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),sK4) != k2_enumset1(sK3,sK3,sK3,sK3) ),
% 7.92/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1152,plain,
% 7.92/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK5))
% 7.92/1.49      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 7.92/1.49      inference(resolution,[status(thm)],[c_3,c_19]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_17844,plain,
% 7.92/1.49      ( r2_hidden(X0,k2_enumset1(X1,X2,X3,X4))
% 7.92/1.49      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 7.92/1.49      | X0 != sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3))
% 7.92/1.49      | X4 != sK5
% 7.92/1.49      | X1 != sK3
% 7.92/1.49      | X2 != sK3
% 7.92/1.49      | X3 != sK3 ),
% 7.92/1.49      inference(resolution,[status(thm)],[c_5873,c_1152]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_214,plain,( X0 = X0 ),theory(equality) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_17951,plain,
% 7.92/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(X0,X1,X2,X3))
% 7.92/1.49      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 7.92/1.49      | X3 != sK5
% 7.92/1.49      | X0 != sK3
% 7.92/1.49      | X1 != sK3
% 7.92/1.49      | X2 != sK3 ),
% 7.92/1.49      inference(resolution,[status(thm)],[c_17844,c_214]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_21,negated_conjecture,
% 7.92/1.49      ( r2_hidden(sK3,sK4) ),
% 7.92/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_20,negated_conjecture,
% 7.92/1.49      ( ~ r2_hidden(sK5,sK4) | sK3 = sK5 ),
% 7.92/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_18,plain,
% 7.92/1.49      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 7.92/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_25,plain,
% 7.92/1.49      ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) | sK3 = sK3 ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_18]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_17,plain,
% 7.92/1.49      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 7.92/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_28,plain,
% 7.92/1.49      ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_669,plain,
% 7.92/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK5))
% 7.92/1.49      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 7.92/1.49      | k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),sK4) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_840,plain,
% 7.92/1.49      ( sK4 = sK4 ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_214]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1015,plain,
% 7.92/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 7.92/1.49      inference(resolution,[status(thm)],[c_217,c_214]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_2,plain,
% 7.92/1.49      ( r2_hidden(sK0(X0,X1,X2),X1)
% 7.92/1.49      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.92/1.49      | k3_xboole_0(X0,X1) = X2 ),
% 7.92/1.49      inference(cnf_transformation,[],[f34]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1025,plain,
% 7.92/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 7.92/1.49      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4) ),
% 7.92/1.49      inference(resolution,[status(thm)],[c_2,c_19]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1182,plain,
% 7.92/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 7.92/1.49      | sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
% 7.92/1.49      inference(resolution,[status(thm)],[c_1025,c_18]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_7515,plain,
% 7.92/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),X0)
% 7.92/1.49      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 7.92/1.49      | ~ r2_hidden(sK3,X0) ),
% 7.92/1.49      inference(resolution,[status(thm)],[c_1015,c_1182]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_7940,plain,
% 7.92/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 7.92/1.49      | ~ r2_hidden(sK3,sK4) ),
% 7.92/1.49      inference(factoring,[status(thm)],[c_7515]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_215,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1002,plain,
% 7.92/1.49      ( X0 != X1 | X1 = X0 ),
% 7.92/1.49      inference(resolution,[status(thm)],[c_215,c_214]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_14,plain,
% 7.92/1.49      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 7.92/1.49      | X0 = X1
% 7.92/1.49      | X0 = X2
% 7.92/1.49      | X0 = X3 ),
% 7.92/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_2819,plain,
% 7.92/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 7.92/1.49      | sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK5
% 7.92/1.49      | sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
% 7.92/1.49      inference(resolution,[status(thm)],[c_14,c_1152]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3172,plain,
% 7.92/1.49      ( sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK5
% 7.92/1.49      | sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
% 7.92/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_2819,c_18]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_7233,plain,
% 7.92/1.49      ( sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3
% 7.92/1.49      | sK5 = sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 7.92/1.49      inference(resolution,[status(thm)],[c_1002,c_3172]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_8102,plain,
% 7.92/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),X0)
% 7.92/1.49      | ~ r2_hidden(sK3,X0)
% 7.92/1.49      | sK5 = sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 7.92/1.49      inference(resolution,[status(thm)],[c_7233,c_1015]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1,plain,
% 7.92/1.49      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 7.92/1.49      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 7.92/1.49      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 7.92/1.49      | k3_xboole_0(X0,X1) = X2 ),
% 7.92/1.49      inference(cnf_transformation,[],[f35]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_10358,plain,
% 7.92/1.49      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK5))
% 7.92/1.49      | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 7.92/1.49      | ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
% 7.92/1.49      | k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),sK4) = k2_enumset1(sK3,sK3,sK3,sK3)
% 7.92/1.49      | sK5 = sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 7.92/1.49      inference(resolution,[status(thm)],[c_8102,c_1]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1397,plain,
% 7.92/1.49      ( r2_hidden(X0,X1)
% 7.92/1.49      | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 7.92/1.49      | X0 != sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3))
% 7.92/1.49      | X1 != sK4 ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_217]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_4934,plain,
% 7.92/1.49      ( r2_hidden(X0,sK4)
% 7.92/1.49      | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 7.92/1.49      | X0 != sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3))
% 7.92/1.49      | sK4 != sK4 ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_1397]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_15582,plain,
% 7.92/1.49      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 7.92/1.49      | r2_hidden(sK5,sK4)
% 7.92/1.49      | sK4 != sK4
% 7.92/1.49      | sK5 != sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_4934]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_17953,plain,
% 7.92/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 7.92/1.49      | sK3 != sK5
% 7.92/1.49      | sK3 != sK3 ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_17951]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_18009,plain,
% 7.92/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 7.92/1.49      inference(global_propositional_subsumption,
% 7.92/1.49                [status(thm)],
% 7.92/1.49                [c_17951,c_21,c_20,c_19,c_25,c_28,c_669,c_840,c_7940,c_10358,
% 7.92/1.49                 c_15582,c_17953]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_18410,plain,
% 7.92/1.49      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK5))
% 7.92/1.49      | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 7.92/1.49      | k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),sK4) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 7.92/1.49      inference(resolution,[status(thm)],[c_18009,c_1]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_690,plain,
% 7.92/1.49      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK5))
% 7.92/1.49      | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 7.92/1.49      | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 7.92/1.49      | k3_xboole_0(k2_enumset1(sK3,sK3,sK3,sK5),sK4) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 7.92/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_20612,plain,
% 7.92/1.49      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK5)) ),
% 7.92/1.49      inference(global_propositional_subsumption,
% 7.92/1.49                [status(thm)],
% 7.92/1.49                [c_18410,c_21,c_20,c_19,c_25,c_28,c_669,c_690,c_840,c_7940,
% 7.92/1.49                 c_10358,c_15582,c_17953]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_7533,plain,
% 7.92/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),X0)
% 7.92/1.49      | ~ r2_hidden(sK5,X0)
% 7.92/1.49      | sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
% 7.92/1.49      inference(resolution,[status(thm)],[c_1015,c_3172]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_8292,plain,
% 7.92/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),X0)
% 7.92/1.49      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),X1)
% 7.92/1.49      | ~ r2_hidden(sK5,X0)
% 7.92/1.49      | ~ r2_hidden(sK3,X1) ),
% 7.92/1.49      inference(resolution,[status(thm)],[c_7533,c_1015]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_20630,plain,
% 7.92/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),X0)
% 7.92/1.49      | ~ r2_hidden(sK5,X0)
% 7.92/1.49      | ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK5)) ),
% 7.92/1.49      inference(resolution,[status(thm)],[c_20612,c_8292]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_12,plain,
% 7.92/1.49      ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
% 7.92/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_20812,plain,
% 7.92/1.49      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK5),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),X0)
% 7.92/1.49      | ~ r2_hidden(sK5,X0) ),
% 7.92/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_20630,c_12]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_21170,plain,
% 7.92/1.49      ( ~ r2_hidden(sK5,k2_enumset1(sK3,sK3,sK3,sK5)) ),
% 7.92/1.49      inference(resolution,[status(thm)],[c_20812,c_20612]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_11,plain,
% 7.92/1.49      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 7.92/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_22184,plain,
% 7.92/1.49      ( $false ),
% 7.92/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_21170,c_11]) ).
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.92/1.49  
% 7.92/1.49  ------                               Statistics
% 7.92/1.49  
% 7.92/1.49  ------ Selected
% 7.92/1.49  
% 7.92/1.49  total_time:                             0.938
% 7.92/1.49  
%------------------------------------------------------------------------------
