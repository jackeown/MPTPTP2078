%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:34 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 355 expanded)
%              Number of clauses        :   40 (  85 expanded)
%              Number of leaves         :   22 (  94 expanded)
%              Depth                    :   18
%              Number of atoms          :  349 ( 747 expanded)
%              Number of equality atoms :  189 ( 402 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f67,f73])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f74])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f75])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f76])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f63,f77])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f78])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f32])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f30])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f40,plain,
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

fof(f41,plain,
    ( ( r2_hidden(sK5,sK4)
      | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4 )
    & ( ~ r2_hidden(sK5,sK4)
      | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f39,f40])).

fof(f71,plain,
    ( ~ r2_hidden(sK5,sK4)
    | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4 ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f90,plain,
    ( ~ r2_hidden(sK5,sK4)
    | k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = sK4 ),
    inference(definition_unfolding,[],[f71,f52,f78])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f79,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f54,f52])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f72,plain,
    ( r2_hidden(sK5,sK4)
    | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4 ),
    inference(cnf_transformation,[],[f41])).

fof(f89,plain,
    ( r2_hidden(sK5,sK4)
    | k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != sK4 ),
    inference(definition_unfolding,[],[f72,f52,f78])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(rectify,[],[f35])).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f56,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f56,f76])).

fof(f98,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f86])).

fof(f99,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f98])).

cnf(c_20,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_808,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_9,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_818,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_820,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1411,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_818,c_820])).

cnf(c_1478,plain,
    ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = k1_xboole_0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_808,c_1411])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(sK5,sK4)
    | k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = sK4 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_806,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = sK4
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_11042,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = sK4
    | k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1478,c_806])).

cnf(c_11,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_817,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1477,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_817,c_1411])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1503,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1477,c_0])).

cnf(c_11642,plain,
    ( k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11042,c_1503])).

cnf(c_11834,plain,
    ( k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11642,c_0])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK5,sK4)
    | k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != sK4 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_807,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != sK4
    | r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_12045,plain,
    ( k5_xboole_0(sK4,k1_xboole_0) != sK4
    | r2_hidden(sK5,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11834,c_807])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_12052,plain,
    ( sK4 != sK4
    | r2_hidden(sK5,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12045,c_10])).

cnf(c_12053,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_12052])).

cnf(c_1016,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_817])).

cnf(c_1479,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1016,c_1411])).

cnf(c_1706,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X1,k3_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1479,c_1016])).

cnf(c_1717,plain,
    ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1706,c_10])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_823,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1412,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_820])).

cnf(c_2625,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_823,c_1412])).

cnf(c_4283,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1717,c_2625])).

cnf(c_11851,plain,
    ( r2_hidden(X0,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(X0,k5_xboole_0(sK4,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11642,c_4283])).

cnf(c_11879,plain,
    ( r2_hidden(X0,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11851,c_10])).

cnf(c_12023,plain,
    ( r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11879])).

cnf(c_18,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_31,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_33,plain,
    ( r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12053,c_12023,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n021.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 12:14:34 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.20/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/0.98  
% 3.20/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.20/0.98  
% 3.20/0.98  ------  iProver source info
% 3.20/0.98  
% 3.20/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.20/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.20/0.98  git: non_committed_changes: false
% 3.20/0.98  git: last_make_outside_of_git: false
% 3.20/0.98  
% 3.20/0.98  ------ 
% 3.20/0.98  
% 3.20/0.98  ------ Input Options
% 3.20/0.98  
% 3.20/0.98  --out_options                           all
% 3.20/0.98  --tptp_safe_out                         true
% 3.20/0.98  --problem_path                          ""
% 3.20/0.98  --include_path                          ""
% 3.20/0.98  --clausifier                            res/vclausify_rel
% 3.20/0.98  --clausifier_options                    --mode clausify
% 3.20/0.98  --stdin                                 false
% 3.20/0.98  --stats_out                             all
% 3.20/0.98  
% 3.20/0.98  ------ General Options
% 3.20/0.98  
% 3.20/0.98  --fof                                   false
% 3.20/0.98  --time_out_real                         305.
% 3.20/0.98  --time_out_virtual                      -1.
% 3.20/0.98  --symbol_type_check                     false
% 3.20/0.98  --clausify_out                          false
% 3.20/0.98  --sig_cnt_out                           false
% 3.20/0.98  --trig_cnt_out                          false
% 3.20/0.98  --trig_cnt_out_tolerance                1.
% 3.20/0.98  --trig_cnt_out_sk_spl                   false
% 3.20/0.98  --abstr_cl_out                          false
% 3.20/0.98  
% 3.20/0.98  ------ Global Options
% 3.20/0.98  
% 3.20/0.98  --schedule                              default
% 3.20/0.98  --add_important_lit                     false
% 3.20/0.98  --prop_solver_per_cl                    1000
% 3.20/0.98  --min_unsat_core                        false
% 3.20/0.98  --soft_assumptions                      false
% 3.20/0.98  --soft_lemma_size                       3
% 3.20/0.98  --prop_impl_unit_size                   0
% 3.20/0.98  --prop_impl_unit                        []
% 3.20/0.98  --share_sel_clauses                     true
% 3.20/0.98  --reset_solvers                         false
% 3.20/0.98  --bc_imp_inh                            [conj_cone]
% 3.20/0.98  --conj_cone_tolerance                   3.
% 3.20/0.98  --extra_neg_conj                        none
% 3.20/0.98  --large_theory_mode                     true
% 3.20/0.98  --prolific_symb_bound                   200
% 3.20/0.98  --lt_threshold                          2000
% 3.20/0.98  --clause_weak_htbl                      true
% 3.20/0.98  --gc_record_bc_elim                     false
% 3.20/0.98  
% 3.20/0.98  ------ Preprocessing Options
% 3.20/0.98  
% 3.20/0.98  --preprocessing_flag                    true
% 3.20/0.98  --time_out_prep_mult                    0.1
% 3.20/0.98  --splitting_mode                        input
% 3.20/0.98  --splitting_grd                         true
% 3.20/0.98  --splitting_cvd                         false
% 3.20/0.98  --splitting_cvd_svl                     false
% 3.20/0.98  --splitting_nvd                         32
% 3.20/0.98  --sub_typing                            true
% 3.20/0.98  --prep_gs_sim                           true
% 3.20/0.98  --prep_unflatten                        true
% 3.20/0.98  --prep_res_sim                          true
% 3.20/0.98  --prep_upred                            true
% 3.20/0.98  --prep_sem_filter                       exhaustive
% 3.20/0.98  --prep_sem_filter_out                   false
% 3.20/0.98  --pred_elim                             true
% 3.20/0.98  --res_sim_input                         true
% 3.20/0.98  --eq_ax_congr_red                       true
% 3.20/0.98  --pure_diseq_elim                       true
% 3.20/0.98  --brand_transform                       false
% 3.20/0.98  --non_eq_to_eq                          false
% 3.20/0.98  --prep_def_merge                        true
% 3.20/0.98  --prep_def_merge_prop_impl              false
% 3.20/0.98  --prep_def_merge_mbd                    true
% 3.20/0.98  --prep_def_merge_tr_red                 false
% 3.20/0.98  --prep_def_merge_tr_cl                  false
% 3.20/0.98  --smt_preprocessing                     true
% 3.20/0.98  --smt_ac_axioms                         fast
% 3.20/0.98  --preprocessed_out                      false
% 3.20/0.98  --preprocessed_stats                    false
% 3.20/0.98  
% 3.20/0.98  ------ Abstraction refinement Options
% 3.20/0.98  
% 3.20/0.98  --abstr_ref                             []
% 3.20/0.98  --abstr_ref_prep                        false
% 3.20/0.98  --abstr_ref_until_sat                   false
% 3.20/0.98  --abstr_ref_sig_restrict                funpre
% 3.20/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/0.98  --abstr_ref_under                       []
% 3.20/0.98  
% 3.20/0.98  ------ SAT Options
% 3.20/0.98  
% 3.20/0.98  --sat_mode                              false
% 3.20/0.98  --sat_fm_restart_options                ""
% 3.20/0.98  --sat_gr_def                            false
% 3.20/0.98  --sat_epr_types                         true
% 3.20/0.98  --sat_non_cyclic_types                  false
% 3.20/0.98  --sat_finite_models                     false
% 3.20/0.98  --sat_fm_lemmas                         false
% 3.20/0.98  --sat_fm_prep                           false
% 3.20/0.98  --sat_fm_uc_incr                        true
% 3.20/0.98  --sat_out_model                         small
% 3.20/0.98  --sat_out_clauses                       false
% 3.20/0.98  
% 3.20/0.98  ------ QBF Options
% 3.20/0.98  
% 3.20/0.98  --qbf_mode                              false
% 3.20/0.98  --qbf_elim_univ                         false
% 3.20/0.98  --qbf_dom_inst                          none
% 3.20/0.98  --qbf_dom_pre_inst                      false
% 3.20/0.98  --qbf_sk_in                             false
% 3.20/0.98  --qbf_pred_elim                         true
% 3.20/0.98  --qbf_split                             512
% 3.20/0.98  
% 3.20/0.98  ------ BMC1 Options
% 3.20/0.98  
% 3.20/0.98  --bmc1_incremental                      false
% 3.20/0.98  --bmc1_axioms                           reachable_all
% 3.20/0.98  --bmc1_min_bound                        0
% 3.20/0.98  --bmc1_max_bound                        -1
% 3.20/0.98  --bmc1_max_bound_default                -1
% 3.20/0.98  --bmc1_symbol_reachability              true
% 3.20/0.98  --bmc1_property_lemmas                  false
% 3.20/0.98  --bmc1_k_induction                      false
% 3.20/0.98  --bmc1_non_equiv_states                 false
% 3.20/0.98  --bmc1_deadlock                         false
% 3.20/0.98  --bmc1_ucm                              false
% 3.20/0.98  --bmc1_add_unsat_core                   none
% 3.20/0.98  --bmc1_unsat_core_children              false
% 3.20/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/0.98  --bmc1_out_stat                         full
% 3.20/0.98  --bmc1_ground_init                      false
% 3.20/0.98  --bmc1_pre_inst_next_state              false
% 3.20/0.98  --bmc1_pre_inst_state                   false
% 3.20/0.98  --bmc1_pre_inst_reach_state             false
% 3.20/0.98  --bmc1_out_unsat_core                   false
% 3.20/0.98  --bmc1_aig_witness_out                  false
% 3.20/0.98  --bmc1_verbose                          false
% 3.20/0.98  --bmc1_dump_clauses_tptp                false
% 3.20/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.20/0.98  --bmc1_dump_file                        -
% 3.20/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.20/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.20/0.98  --bmc1_ucm_extend_mode                  1
% 3.20/0.98  --bmc1_ucm_init_mode                    2
% 3.20/0.98  --bmc1_ucm_cone_mode                    none
% 3.20/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.20/0.98  --bmc1_ucm_relax_model                  4
% 3.20/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.20/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/0.98  --bmc1_ucm_layered_model                none
% 3.20/0.98  --bmc1_ucm_max_lemma_size               10
% 3.20/0.98  
% 3.20/0.98  ------ AIG Options
% 3.20/0.98  
% 3.20/0.98  --aig_mode                              false
% 3.20/0.98  
% 3.20/0.98  ------ Instantiation Options
% 3.20/0.98  
% 3.20/0.98  --instantiation_flag                    true
% 3.20/0.98  --inst_sos_flag                         false
% 3.20/0.98  --inst_sos_phase                        true
% 3.20/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/0.98  --inst_lit_sel_side                     num_symb
% 3.20/0.98  --inst_solver_per_active                1400
% 3.20/0.98  --inst_solver_calls_frac                1.
% 3.20/0.98  --inst_passive_queue_type               priority_queues
% 3.20/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/0.98  --inst_passive_queues_freq              [25;2]
% 3.20/0.98  --inst_dismatching                      true
% 3.20/0.98  --inst_eager_unprocessed_to_passive     true
% 3.20/0.98  --inst_prop_sim_given                   true
% 3.20/0.98  --inst_prop_sim_new                     false
% 3.20/0.98  --inst_subs_new                         false
% 3.20/0.98  --inst_eq_res_simp                      false
% 3.20/0.98  --inst_subs_given                       false
% 3.20/0.98  --inst_orphan_elimination               true
% 3.20/0.98  --inst_learning_loop_flag               true
% 3.20/0.98  --inst_learning_start                   3000
% 3.20/0.98  --inst_learning_factor                  2
% 3.20/0.98  --inst_start_prop_sim_after_learn       3
% 3.20/0.98  --inst_sel_renew                        solver
% 3.20/0.98  --inst_lit_activity_flag                true
% 3.20/0.98  --inst_restr_to_given                   false
% 3.20/0.98  --inst_activity_threshold               500
% 3.20/0.98  --inst_out_proof                        true
% 3.20/0.98  
% 3.20/0.98  ------ Resolution Options
% 3.20/0.98  
% 3.20/0.98  --resolution_flag                       true
% 3.20/0.98  --res_lit_sel                           adaptive
% 3.20/0.98  --res_lit_sel_side                      none
% 3.20/0.98  --res_ordering                          kbo
% 3.20/0.98  --res_to_prop_solver                    active
% 3.20/0.98  --res_prop_simpl_new                    false
% 3.20/0.98  --res_prop_simpl_given                  true
% 3.20/0.98  --res_passive_queue_type                priority_queues
% 3.20/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/0.98  --res_passive_queues_freq               [15;5]
% 3.20/0.98  --res_forward_subs                      full
% 3.20/0.98  --res_backward_subs                     full
% 3.20/0.98  --res_forward_subs_resolution           true
% 3.20/0.98  --res_backward_subs_resolution          true
% 3.20/0.98  --res_orphan_elimination                true
% 3.20/0.98  --res_time_limit                        2.
% 3.20/0.98  --res_out_proof                         true
% 3.20/0.98  
% 3.20/0.98  ------ Superposition Options
% 3.20/0.98  
% 3.20/0.98  --superposition_flag                    true
% 3.20/0.98  --sup_passive_queue_type                priority_queues
% 3.20/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.20/0.98  --demod_completeness_check              fast
% 3.20/0.98  --demod_use_ground                      true
% 3.20/0.98  --sup_to_prop_solver                    passive
% 3.20/0.98  --sup_prop_simpl_new                    true
% 3.20/0.98  --sup_prop_simpl_given                  true
% 3.20/0.98  --sup_fun_splitting                     false
% 3.20/0.98  --sup_smt_interval                      50000
% 3.20/0.98  
% 3.20/0.98  ------ Superposition Simplification Setup
% 3.20/0.98  
% 3.20/0.98  --sup_indices_passive                   []
% 3.20/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.98  --sup_full_bw                           [BwDemod]
% 3.20/0.98  --sup_immed_triv                        [TrivRules]
% 3.20/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.98  --sup_immed_bw_main                     []
% 3.20/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.98  
% 3.20/0.98  ------ Combination Options
% 3.20/0.98  
% 3.20/0.98  --comb_res_mult                         3
% 3.20/0.98  --comb_sup_mult                         2
% 3.20/0.98  --comb_inst_mult                        10
% 3.20/0.98  
% 3.20/0.98  ------ Debug Options
% 3.20/0.98  
% 3.20/0.98  --dbg_backtrace                         false
% 3.20/0.98  --dbg_dump_prop_clauses                 false
% 3.20/0.98  --dbg_dump_prop_clauses_file            -
% 3.20/0.98  --dbg_out_stat                          false
% 3.20/0.98  ------ Parsing...
% 3.20/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.20/0.98  
% 3.20/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.20/0.98  
% 3.20/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.20/0.98  
% 3.20/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.20/0.98  ------ Proving...
% 3.20/0.98  ------ Problem Properties 
% 3.20/0.98  
% 3.20/0.98  
% 3.20/0.98  clauses                                 23
% 3.20/0.98  conjectures                             2
% 3.20/0.98  EPR                                     0
% 3.20/0.98  Horn                                    16
% 3.20/0.98  unary                                   6
% 3.20/0.98  binary                                  8
% 3.20/0.98  lits                                    53
% 3.20/0.98  lits eq                                 21
% 3.20/0.98  fd_pure                                 0
% 3.20/0.98  fd_pseudo                               0
% 3.20/0.98  fd_cond                                 1
% 3.20/0.98  fd_pseudo_cond                          7
% 3.20/0.98  AC symbols                              0
% 3.20/0.98  
% 3.20/0.98  ------ Schedule dynamic 5 is on 
% 3.20/0.98  
% 3.20/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.20/0.98  
% 3.20/0.98  
% 3.20/0.98  ------ 
% 3.20/0.98  Current options:
% 3.20/0.98  ------ 
% 3.20/0.98  
% 3.20/0.98  ------ Input Options
% 3.20/0.98  
% 3.20/0.98  --out_options                           all
% 3.20/0.98  --tptp_safe_out                         true
% 3.20/0.98  --problem_path                          ""
% 3.20/0.98  --include_path                          ""
% 3.20/0.98  --clausifier                            res/vclausify_rel
% 3.20/0.98  --clausifier_options                    --mode clausify
% 3.20/0.98  --stdin                                 false
% 3.20/0.98  --stats_out                             all
% 3.20/0.98  
% 3.20/0.98  ------ General Options
% 3.20/0.98  
% 3.20/0.98  --fof                                   false
% 3.20/0.98  --time_out_real                         305.
% 3.20/0.98  --time_out_virtual                      -1.
% 3.20/0.98  --symbol_type_check                     false
% 3.20/0.98  --clausify_out                          false
% 3.20/0.98  --sig_cnt_out                           false
% 3.20/0.98  --trig_cnt_out                          false
% 3.20/0.98  --trig_cnt_out_tolerance                1.
% 3.20/0.98  --trig_cnt_out_sk_spl                   false
% 3.20/0.98  --abstr_cl_out                          false
% 3.20/0.98  
% 3.20/0.98  ------ Global Options
% 3.20/0.98  
% 3.20/0.98  --schedule                              default
% 3.20/0.98  --add_important_lit                     false
% 3.20/0.98  --prop_solver_per_cl                    1000
% 3.20/0.98  --min_unsat_core                        false
% 3.20/0.98  --soft_assumptions                      false
% 3.20/0.98  --soft_lemma_size                       3
% 3.20/0.98  --prop_impl_unit_size                   0
% 3.20/0.98  --prop_impl_unit                        []
% 3.20/0.98  --share_sel_clauses                     true
% 3.20/0.98  --reset_solvers                         false
% 3.20/0.98  --bc_imp_inh                            [conj_cone]
% 3.20/0.98  --conj_cone_tolerance                   3.
% 3.20/0.98  --extra_neg_conj                        none
% 3.20/0.98  --large_theory_mode                     true
% 3.20/0.98  --prolific_symb_bound                   200
% 3.20/0.98  --lt_threshold                          2000
% 3.20/0.98  --clause_weak_htbl                      true
% 3.20/0.98  --gc_record_bc_elim                     false
% 3.20/0.98  
% 3.20/0.98  ------ Preprocessing Options
% 3.20/0.98  
% 3.20/0.98  --preprocessing_flag                    true
% 3.20/0.98  --time_out_prep_mult                    0.1
% 3.20/0.98  --splitting_mode                        input
% 3.20/0.98  --splitting_grd                         true
% 3.20/0.98  --splitting_cvd                         false
% 3.20/0.98  --splitting_cvd_svl                     false
% 3.20/0.98  --splitting_nvd                         32
% 3.20/0.98  --sub_typing                            true
% 3.20/0.98  --prep_gs_sim                           true
% 3.20/0.98  --prep_unflatten                        true
% 3.20/0.98  --prep_res_sim                          true
% 3.20/0.98  --prep_upred                            true
% 3.20/0.98  --prep_sem_filter                       exhaustive
% 3.20/0.98  --prep_sem_filter_out                   false
% 3.20/0.98  --pred_elim                             true
% 3.20/0.98  --res_sim_input                         true
% 3.20/0.98  --eq_ax_congr_red                       true
% 3.20/0.98  --pure_diseq_elim                       true
% 3.20/0.98  --brand_transform                       false
% 3.20/0.98  --non_eq_to_eq                          false
% 3.20/0.98  --prep_def_merge                        true
% 3.20/0.98  --prep_def_merge_prop_impl              false
% 3.20/0.98  --prep_def_merge_mbd                    true
% 3.20/0.98  --prep_def_merge_tr_red                 false
% 3.20/0.98  --prep_def_merge_tr_cl                  false
% 3.20/0.98  --smt_preprocessing                     true
% 3.20/0.98  --smt_ac_axioms                         fast
% 3.20/0.98  --preprocessed_out                      false
% 3.20/0.98  --preprocessed_stats                    false
% 3.20/0.98  
% 3.20/0.98  ------ Abstraction refinement Options
% 3.20/0.98  
% 3.20/0.98  --abstr_ref                             []
% 3.20/0.98  --abstr_ref_prep                        false
% 3.20/0.98  --abstr_ref_until_sat                   false
% 3.20/0.98  --abstr_ref_sig_restrict                funpre
% 3.20/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/0.98  --abstr_ref_under                       []
% 3.20/0.98  
% 3.20/0.98  ------ SAT Options
% 3.20/0.98  
% 3.20/0.98  --sat_mode                              false
% 3.20/0.98  --sat_fm_restart_options                ""
% 3.20/0.98  --sat_gr_def                            false
% 3.20/0.98  --sat_epr_types                         true
% 3.20/0.98  --sat_non_cyclic_types                  false
% 3.20/0.98  --sat_finite_models                     false
% 3.20/0.98  --sat_fm_lemmas                         false
% 3.20/0.98  --sat_fm_prep                           false
% 3.20/0.98  --sat_fm_uc_incr                        true
% 3.20/0.98  --sat_out_model                         small
% 3.20/0.98  --sat_out_clauses                       false
% 3.20/0.98  
% 3.20/0.98  ------ QBF Options
% 3.20/0.98  
% 3.20/0.98  --qbf_mode                              false
% 3.20/0.98  --qbf_elim_univ                         false
% 3.20/0.98  --qbf_dom_inst                          none
% 3.20/0.98  --qbf_dom_pre_inst                      false
% 3.20/0.98  --qbf_sk_in                             false
% 3.20/0.98  --qbf_pred_elim                         true
% 3.20/0.98  --qbf_split                             512
% 3.20/0.98  
% 3.20/0.98  ------ BMC1 Options
% 3.20/0.98  
% 3.20/0.98  --bmc1_incremental                      false
% 3.20/0.98  --bmc1_axioms                           reachable_all
% 3.20/0.98  --bmc1_min_bound                        0
% 3.20/0.98  --bmc1_max_bound                        -1
% 3.20/0.98  --bmc1_max_bound_default                -1
% 3.20/0.98  --bmc1_symbol_reachability              true
% 3.20/0.98  --bmc1_property_lemmas                  false
% 3.20/0.98  --bmc1_k_induction                      false
% 3.20/0.98  --bmc1_non_equiv_states                 false
% 3.20/0.98  --bmc1_deadlock                         false
% 3.20/0.98  --bmc1_ucm                              false
% 3.20/0.98  --bmc1_add_unsat_core                   none
% 3.20/0.98  --bmc1_unsat_core_children              false
% 3.20/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/0.98  --bmc1_out_stat                         full
% 3.20/0.98  --bmc1_ground_init                      false
% 3.20/0.98  --bmc1_pre_inst_next_state              false
% 3.20/0.98  --bmc1_pre_inst_state                   false
% 3.20/0.98  --bmc1_pre_inst_reach_state             false
% 3.20/0.98  --bmc1_out_unsat_core                   false
% 3.20/0.98  --bmc1_aig_witness_out                  false
% 3.20/0.98  --bmc1_verbose                          false
% 3.20/0.98  --bmc1_dump_clauses_tptp                false
% 3.20/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.20/0.98  --bmc1_dump_file                        -
% 3.20/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.20/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.20/0.98  --bmc1_ucm_extend_mode                  1
% 3.20/0.98  --bmc1_ucm_init_mode                    2
% 3.20/0.98  --bmc1_ucm_cone_mode                    none
% 3.20/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.20/0.98  --bmc1_ucm_relax_model                  4
% 3.20/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.20/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/0.98  --bmc1_ucm_layered_model                none
% 3.20/0.98  --bmc1_ucm_max_lemma_size               10
% 3.20/0.98  
% 3.20/0.98  ------ AIG Options
% 3.20/0.98  
% 3.20/0.98  --aig_mode                              false
% 3.20/0.98  
% 3.20/0.98  ------ Instantiation Options
% 3.20/0.98  
% 3.20/0.98  --instantiation_flag                    true
% 3.20/0.98  --inst_sos_flag                         false
% 3.20/0.98  --inst_sos_phase                        true
% 3.20/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/0.98  --inst_lit_sel_side                     none
% 3.20/0.98  --inst_solver_per_active                1400
% 3.20/0.98  --inst_solver_calls_frac                1.
% 3.20/0.98  --inst_passive_queue_type               priority_queues
% 3.20/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/0.98  --inst_passive_queues_freq              [25;2]
% 3.20/0.98  --inst_dismatching                      true
% 3.20/0.98  --inst_eager_unprocessed_to_passive     true
% 3.20/0.98  --inst_prop_sim_given                   true
% 3.20/0.98  --inst_prop_sim_new                     false
% 3.20/0.98  --inst_subs_new                         false
% 3.20/0.98  --inst_eq_res_simp                      false
% 3.20/0.98  --inst_subs_given                       false
% 3.20/0.98  --inst_orphan_elimination               true
% 3.20/0.98  --inst_learning_loop_flag               true
% 3.20/0.98  --inst_learning_start                   3000
% 3.20/0.98  --inst_learning_factor                  2
% 3.20/0.98  --inst_start_prop_sim_after_learn       3
% 3.20/0.98  --inst_sel_renew                        solver
% 3.20/0.98  --inst_lit_activity_flag                true
% 3.20/0.98  --inst_restr_to_given                   false
% 3.20/0.98  --inst_activity_threshold               500
% 3.20/0.98  --inst_out_proof                        true
% 3.20/0.98  
% 3.20/0.98  ------ Resolution Options
% 3.20/0.98  
% 3.20/0.98  --resolution_flag                       false
% 3.20/0.98  --res_lit_sel                           adaptive
% 3.20/0.98  --res_lit_sel_side                      none
% 3.20/0.98  --res_ordering                          kbo
% 3.20/0.98  --res_to_prop_solver                    active
% 3.20/0.98  --res_prop_simpl_new                    false
% 3.20/0.98  --res_prop_simpl_given                  true
% 3.20/0.98  --res_passive_queue_type                priority_queues
% 3.20/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/0.98  --res_passive_queues_freq               [15;5]
% 3.20/0.98  --res_forward_subs                      full
% 3.20/0.98  --res_backward_subs                     full
% 3.20/0.98  --res_forward_subs_resolution           true
% 3.20/0.98  --res_backward_subs_resolution          true
% 3.20/0.98  --res_orphan_elimination                true
% 3.20/0.98  --res_time_limit                        2.
% 3.20/0.98  --res_out_proof                         true
% 3.20/0.98  
% 3.20/0.98  ------ Superposition Options
% 3.20/0.98  
% 3.20/0.98  --superposition_flag                    true
% 3.20/0.98  --sup_passive_queue_type                priority_queues
% 3.20/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.20/0.98  --demod_completeness_check              fast
% 3.20/0.98  --demod_use_ground                      true
% 3.20/0.98  --sup_to_prop_solver                    passive
% 3.20/0.98  --sup_prop_simpl_new                    true
% 3.20/0.98  --sup_prop_simpl_given                  true
% 3.20/0.98  --sup_fun_splitting                     false
% 3.20/0.98  --sup_smt_interval                      50000
% 3.20/0.98  
% 3.20/0.98  ------ Superposition Simplification Setup
% 3.20/0.98  
% 3.20/0.98  --sup_indices_passive                   []
% 3.20/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.98  --sup_full_bw                           [BwDemod]
% 3.20/0.98  --sup_immed_triv                        [TrivRules]
% 3.20/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.98  --sup_immed_bw_main                     []
% 3.20/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.98  
% 3.20/0.98  ------ Combination Options
% 3.20/0.98  
% 3.20/0.98  --comb_res_mult                         3
% 3.20/0.98  --comb_sup_mult                         2
% 3.20/0.98  --comb_inst_mult                        10
% 3.20/0.98  
% 3.20/0.98  ------ Debug Options
% 3.20/0.98  
% 3.20/0.98  --dbg_backtrace                         false
% 3.20/0.98  --dbg_dump_prop_clauses                 false
% 3.20/0.98  --dbg_dump_prop_clauses_file            -
% 3.20/0.98  --dbg_out_stat                          false
% 3.20/0.98  
% 3.20/0.98  
% 3.20/0.98  
% 3.20/0.98  
% 3.20/0.98  ------ Proving...
% 3.20/0.98  
% 3.20/0.98  
% 3.20/0.98  % SZS status Theorem for theBenchmark.p
% 3.20/0.98  
% 3.20/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.20/0.98  
% 3.20/0.98  fof(f16,axiom,(
% 3.20/0.98    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 3.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f23,plain,(
% 3.20/0.98    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 3.20/0.98    inference(ennf_transformation,[],[f16])).
% 3.20/0.98  
% 3.20/0.98  fof(f70,plain,(
% 3.20/0.98    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f23])).
% 3.20/0.98  
% 3.20/0.98  fof(f9,axiom,(
% 3.20/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f63,plain,(
% 3.20/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f9])).
% 3.20/0.98  
% 3.20/0.98  fof(f10,axiom,(
% 3.20/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f64,plain,(
% 3.20/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f10])).
% 3.20/0.98  
% 3.20/0.98  fof(f11,axiom,(
% 3.20/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f65,plain,(
% 3.20/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f11])).
% 3.20/0.98  
% 3.20/0.98  fof(f12,axiom,(
% 3.20/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f66,plain,(
% 3.20/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f12])).
% 3.20/0.98  
% 3.20/0.98  fof(f13,axiom,(
% 3.20/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f67,plain,(
% 3.20/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f13])).
% 3.20/0.98  
% 3.20/0.98  fof(f14,axiom,(
% 3.20/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f68,plain,(
% 3.20/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f14])).
% 3.20/0.98  
% 3.20/0.98  fof(f15,axiom,(
% 3.20/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f69,plain,(
% 3.20/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f15])).
% 3.20/0.98  
% 3.20/0.98  fof(f73,plain,(
% 3.20/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.20/0.98    inference(definition_unfolding,[],[f68,f69])).
% 3.20/0.98  
% 3.20/0.98  fof(f74,plain,(
% 3.20/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.20/0.98    inference(definition_unfolding,[],[f67,f73])).
% 3.20/0.98  
% 3.20/0.98  fof(f75,plain,(
% 3.20/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.20/0.98    inference(definition_unfolding,[],[f66,f74])).
% 3.20/0.98  
% 3.20/0.98  fof(f76,plain,(
% 3.20/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.20/0.98    inference(definition_unfolding,[],[f65,f75])).
% 3.20/0.98  
% 3.20/0.98  fof(f77,plain,(
% 3.20/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.20/0.98    inference(definition_unfolding,[],[f64,f76])).
% 3.20/0.98  
% 3.20/0.98  fof(f78,plain,(
% 3.20/0.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.20/0.98    inference(definition_unfolding,[],[f63,f77])).
% 3.20/0.98  
% 3.20/0.98  fof(f88,plain,(
% 3.20/0.98    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 3.20/0.98    inference(definition_unfolding,[],[f70,f78])).
% 3.20/0.98  
% 3.20/0.98  fof(f4,axiom,(
% 3.20/0.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f21,plain,(
% 3.20/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.20/0.98    inference(ennf_transformation,[],[f4])).
% 3.20/0.98  
% 3.20/0.98  fof(f32,plain,(
% 3.20/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 3.20/0.98    introduced(choice_axiom,[])).
% 3.20/0.98  
% 3.20/0.98  fof(f33,plain,(
% 3.20/0.98    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 3.20/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f32])).
% 3.20/0.98  
% 3.20/0.98  fof(f51,plain,(
% 3.20/0.98    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 3.20/0.98    inference(cnf_transformation,[],[f33])).
% 3.20/0.98  
% 3.20/0.98  fof(f3,axiom,(
% 3.20/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f19,plain,(
% 3.20/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.20/0.98    inference(rectify,[],[f3])).
% 3.20/0.98  
% 3.20/0.98  fof(f20,plain,(
% 3.20/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.20/0.98    inference(ennf_transformation,[],[f19])).
% 3.20/0.98  
% 3.20/0.98  fof(f30,plain,(
% 3.20/0.98    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 3.20/0.98    introduced(choice_axiom,[])).
% 3.20/0.98  
% 3.20/0.98  fof(f31,plain,(
% 3.20/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.20/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f30])).
% 3.20/0.98  
% 3.20/0.98  fof(f50,plain,(
% 3.20/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.20/0.98    inference(cnf_transformation,[],[f31])).
% 3.20/0.98  
% 3.20/0.98  fof(f17,conjecture,(
% 3.20/0.98    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f18,negated_conjecture,(
% 3.20/0.98    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.20/0.98    inference(negated_conjecture,[],[f17])).
% 3.20/0.98  
% 3.20/0.98  fof(f24,plain,(
% 3.20/0.98    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 3.20/0.98    inference(ennf_transformation,[],[f18])).
% 3.20/0.98  
% 3.20/0.98  fof(f39,plain,(
% 3.20/0.98    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 3.20/0.98    inference(nnf_transformation,[],[f24])).
% 3.20/0.98  
% 3.20/0.98  fof(f40,plain,(
% 3.20/0.98    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4) & (~r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4))),
% 3.20/0.98    introduced(choice_axiom,[])).
% 3.20/0.98  
% 3.20/0.98  fof(f41,plain,(
% 3.20/0.98    (r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4) & (~r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4)),
% 3.20/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f39,f40])).
% 3.20/0.98  
% 3.20/0.98  fof(f71,plain,(
% 3.20/0.98    ~r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4),
% 3.20/0.98    inference(cnf_transformation,[],[f41])).
% 3.20/0.98  
% 3.20/0.98  fof(f5,axiom,(
% 3.20/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f52,plain,(
% 3.20/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.20/0.98    inference(cnf_transformation,[],[f5])).
% 3.20/0.98  
% 3.20/0.98  fof(f90,plain,(
% 3.20/0.98    ~r2_hidden(sK5,sK4) | k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = sK4),
% 3.20/0.98    inference(definition_unfolding,[],[f71,f52,f78])).
% 3.20/0.98  
% 3.20/0.98  fof(f7,axiom,(
% 3.20/0.98    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f54,plain,(
% 3.20/0.98    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f7])).
% 3.20/0.98  
% 3.20/0.98  fof(f79,plain,(
% 3.20/0.98    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 3.20/0.98    inference(definition_unfolding,[],[f54,f52])).
% 3.20/0.98  
% 3.20/0.98  fof(f1,axiom,(
% 3.20/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f42,plain,(
% 3.20/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f1])).
% 3.20/0.98  
% 3.20/0.98  fof(f72,plain,(
% 3.20/0.98    r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4),
% 3.20/0.98    inference(cnf_transformation,[],[f41])).
% 3.20/0.98  
% 3.20/0.98  fof(f89,plain,(
% 3.20/0.98    r2_hidden(sK5,sK4) | k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != sK4),
% 3.20/0.98    inference(definition_unfolding,[],[f72,f52,f78])).
% 3.20/0.98  
% 3.20/0.98  fof(f6,axiom,(
% 3.20/0.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f53,plain,(
% 3.20/0.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.20/0.98    inference(cnf_transformation,[],[f6])).
% 3.20/0.98  
% 3.20/0.98  fof(f2,axiom,(
% 3.20/0.98    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f25,plain,(
% 3.20/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.20/0.98    inference(nnf_transformation,[],[f2])).
% 3.20/0.98  
% 3.20/0.98  fof(f26,plain,(
% 3.20/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.20/0.98    inference(flattening,[],[f25])).
% 3.20/0.98  
% 3.20/0.98  fof(f27,plain,(
% 3.20/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.20/0.98    inference(rectify,[],[f26])).
% 3.20/0.98  
% 3.20/0.98  fof(f28,plain,(
% 3.20/0.98    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.20/0.98    introduced(choice_axiom,[])).
% 3.20/0.98  
% 3.20/0.98  fof(f29,plain,(
% 3.20/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.20/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 3.20/0.98  
% 3.20/0.98  fof(f45,plain,(
% 3.20/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 3.20/0.98    inference(cnf_transformation,[],[f29])).
% 3.20/0.98  
% 3.20/0.98  fof(f91,plain,(
% 3.20/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.20/0.98    inference(equality_resolution,[],[f45])).
% 3.20/0.98  
% 3.20/0.98  fof(f8,axiom,(
% 3.20/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.20/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f22,plain,(
% 3.20/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.20/0.98    inference(ennf_transformation,[],[f8])).
% 3.20/0.98  
% 3.20/0.98  fof(f34,plain,(
% 3.20/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.20/0.98    inference(nnf_transformation,[],[f22])).
% 3.20/0.98  
% 3.20/0.98  fof(f35,plain,(
% 3.20/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.20/0.98    inference(flattening,[],[f34])).
% 3.20/0.98  
% 3.20/0.98  fof(f36,plain,(
% 3.20/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.20/0.98    inference(rectify,[],[f35])).
% 3.20/0.98  
% 3.20/0.98  fof(f37,plain,(
% 3.20/0.98    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 3.20/0.98    introduced(choice_axiom,[])).
% 3.20/0.98  
% 3.20/0.98  fof(f38,plain,(
% 3.20/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.20/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 3.20/0.98  
% 3.20/0.98  fof(f56,plain,(
% 3.20/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f86,plain,(
% 3.20/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.20/0.98    inference(definition_unfolding,[],[f56,f76])).
% 3.20/0.98  
% 3.20/0.98  fof(f98,plain,(
% 3.20/0.98    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 3.20/0.98    inference(equality_resolution,[],[f86])).
% 3.20/0.98  
% 3.20/0.98  fof(f99,plain,(
% 3.20/0.98    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 3.20/0.98    inference(equality_resolution,[],[f98])).
% 3.20/0.98  
% 3.20/0.98  cnf(c_20,plain,
% 3.20/0.98      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 3.20/0.98      | r2_hidden(X0,X1) ),
% 3.20/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_808,plain,
% 3.20/0.98      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
% 3.20/0.98      | r2_hidden(X0,X1) = iProver_top ),
% 3.20/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_9,plain,
% 3.20/0.98      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 3.20/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_818,plain,
% 3.20/0.98      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 3.20/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_7,plain,
% 3.20/0.98      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 3.20/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_820,plain,
% 3.20/0.98      ( r1_xboole_0(X0,X1) != iProver_top
% 3.20/0.98      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 3.20/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_1411,plain,
% 3.20/0.98      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 3.20/0.98      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.20/0.98      inference(superposition,[status(thm)],[c_818,c_820]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_1478,plain,
% 3.20/0.98      ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = k1_xboole_0
% 3.20/0.98      | r2_hidden(X0,X1) = iProver_top ),
% 3.20/0.98      inference(superposition,[status(thm)],[c_808,c_1411]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_22,negated_conjecture,
% 3.20/0.98      ( ~ r2_hidden(sK5,sK4)
% 3.20/0.98      | k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = sK4 ),
% 3.20/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_806,plain,
% 3.20/0.98      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = sK4
% 3.20/0.98      | r2_hidden(sK5,sK4) != iProver_top ),
% 3.20/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_11042,plain,
% 3.20/0.98      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = sK4
% 3.20/0.98      | k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) = k1_xboole_0 ),
% 3.20/0.98      inference(superposition,[status(thm)],[c_1478,c_806]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_11,plain,
% 3.20/0.98      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 3.20/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_817,plain,
% 3.20/0.98      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 3.20/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_1477,plain,
% 3.20/0.98      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 3.20/0.98      inference(superposition,[status(thm)],[c_817,c_1411]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_0,plain,
% 3.20/0.98      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.20/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_1503,plain,
% 3.20/0.98      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
% 3.20/0.98      inference(superposition,[status(thm)],[c_1477,c_0]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_11642,plain,
% 3.20/0.98      ( k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) = k1_xboole_0 ),
% 3.20/0.98      inference(superposition,[status(thm)],[c_11042,c_1503]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_11834,plain,
% 3.20/0.98      ( k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k1_xboole_0 ),
% 3.20/0.98      inference(superposition,[status(thm)],[c_11642,c_0]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_21,negated_conjecture,
% 3.20/0.98      ( r2_hidden(sK5,sK4)
% 3.20/0.98      | k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != sK4 ),
% 3.20/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_807,plain,
% 3.20/0.98      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != sK4
% 3.20/0.98      | r2_hidden(sK5,sK4) = iProver_top ),
% 3.20/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_12045,plain,
% 3.20/0.98      ( k5_xboole_0(sK4,k1_xboole_0) != sK4
% 3.20/0.98      | r2_hidden(sK5,sK4) = iProver_top ),
% 3.20/0.98      inference(demodulation,[status(thm)],[c_11834,c_807]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_10,plain,
% 3.20/0.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.20/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_12052,plain,
% 3.20/0.98      ( sK4 != sK4 | r2_hidden(sK5,sK4) = iProver_top ),
% 3.20/0.98      inference(demodulation,[status(thm)],[c_12045,c_10]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_12053,plain,
% 3.20/0.98      ( r2_hidden(sK5,sK4) = iProver_top ),
% 3.20/0.98      inference(equality_resolution_simp,[status(thm)],[c_12052]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_1016,plain,
% 3.20/0.98      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = iProver_top ),
% 3.20/0.98      inference(superposition,[status(thm)],[c_0,c_817]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_1479,plain,
% 3.20/0.98      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = k1_xboole_0 ),
% 3.20/0.98      inference(superposition,[status(thm)],[c_1016,c_1411]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_1706,plain,
% 3.20/0.98      ( r1_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X1,k3_xboole_0(X0,X1))) = iProver_top ),
% 3.20/0.98      inference(superposition,[status(thm)],[c_1479,c_1016]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_1717,plain,
% 3.20/0.98      ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = iProver_top ),
% 3.20/0.98      inference(light_normalisation,[status(thm)],[c_1706,c_10]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_4,plain,
% 3.20/0.98      ( ~ r2_hidden(X0,X1)
% 3.20/0.98      | ~ r2_hidden(X0,X2)
% 3.20/0.98      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 3.20/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_823,plain,
% 3.20/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.20/0.98      | r2_hidden(X0,X2) != iProver_top
% 3.20/0.98      | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
% 3.20/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_1412,plain,
% 3.20/0.98      ( r1_xboole_0(X0,X1) != iProver_top
% 3.20/0.98      | r2_hidden(X2,k3_xboole_0(X1,X0)) != iProver_top ),
% 3.20/0.98      inference(superposition,[status(thm)],[c_0,c_820]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_2625,plain,
% 3.20/0.98      ( r1_xboole_0(X0,X1) != iProver_top
% 3.20/0.98      | r2_hidden(X2,X0) != iProver_top
% 3.20/0.98      | r2_hidden(X2,X1) != iProver_top ),
% 3.20/0.98      inference(superposition,[status(thm)],[c_823,c_1412]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_4283,plain,
% 3.20/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.20/0.98      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X1,X2))) != iProver_top ),
% 3.20/0.98      inference(superposition,[status(thm)],[c_1717,c_2625]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_11851,plain,
% 3.20/0.98      ( r2_hidden(X0,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top
% 3.20/0.98      | r2_hidden(X0,k5_xboole_0(sK4,k1_xboole_0)) != iProver_top ),
% 3.20/0.98      inference(superposition,[status(thm)],[c_11642,c_4283]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_11879,plain,
% 3.20/0.98      ( r2_hidden(X0,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top
% 3.20/0.98      | r2_hidden(X0,sK4) != iProver_top ),
% 3.20/0.98      inference(demodulation,[status(thm)],[c_11851,c_10]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_12023,plain,
% 3.20/0.98      ( r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top
% 3.20/0.98      | r2_hidden(sK5,sK4) != iProver_top ),
% 3.20/0.98      inference(instantiation,[status(thm)],[c_11879]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_18,plain,
% 3.20/0.98      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 3.20/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_31,plain,
% 3.20/0.98      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 3.20/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(c_33,plain,
% 3.20/0.98      ( r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
% 3.20/0.98      inference(instantiation,[status(thm)],[c_31]) ).
% 3.20/0.98  
% 3.20/0.98  cnf(contradiction,plain,
% 3.20/0.98      ( $false ),
% 3.20/0.98      inference(minisat,[status(thm)],[c_12053,c_12023,c_33]) ).
% 3.20/0.98  
% 3.20/0.98  
% 3.20/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.20/0.98  
% 3.20/0.98  ------                               Statistics
% 3.20/0.98  
% 3.20/0.98  ------ General
% 3.20/0.98  
% 3.20/0.98  abstr_ref_over_cycles:                  0
% 3.20/0.98  abstr_ref_under_cycles:                 0
% 3.20/0.98  gc_basic_clause_elim:                   0
% 3.20/0.98  forced_gc_time:                         0
% 3.20/0.98  parsing_time:                           0.01
% 3.20/0.98  unif_index_cands_time:                  0.
% 3.20/0.98  unif_index_add_time:                    0.
% 3.20/0.98  orderings_time:                         0.
% 3.20/0.98  out_proof_time:                         0.007
% 3.20/0.98  total_time:                             0.373
% 3.20/0.98  num_of_symbols:                         43
% 3.20/0.98  num_of_terms:                           14571
% 3.20/0.98  
% 3.20/0.98  ------ Preprocessing
% 3.20/0.98  
% 3.20/0.98  num_of_splits:                          0
% 3.20/0.98  num_of_split_atoms:                     0
% 3.20/0.98  num_of_reused_defs:                     0
% 3.20/0.98  num_eq_ax_congr_red:                    22
% 3.20/0.98  num_of_sem_filtered_clauses:            1
% 3.20/0.98  num_of_subtypes:                        0
% 3.20/0.98  monotx_restored_types:                  0
% 3.20/0.98  sat_num_of_epr_types:                   0
% 3.20/0.98  sat_num_of_non_cyclic_types:            0
% 3.20/0.98  sat_guarded_non_collapsed_types:        0
% 3.20/0.98  num_pure_diseq_elim:                    0
% 3.20/0.98  simp_replaced_by:                       0
% 3.20/0.98  res_preprocessed:                       84
% 3.20/0.98  prep_upred:                             0
% 3.20/0.98  prep_unflattend:                        4
% 3.20/0.98  smt_new_axioms:                         0
% 3.20/0.98  pred_elim_cands:                        2
% 3.20/0.98  pred_elim:                              0
% 3.20/0.98  pred_elim_cl:                           0
% 3.20/0.98  pred_elim_cycles:                       1
% 3.20/0.98  merged_defs:                            6
% 3.20/0.98  merged_defs_ncl:                        0
% 3.20/0.98  bin_hyper_res:                          6
% 3.20/0.98  prep_cycles:                            3
% 3.20/0.98  pred_elim_time:                         0.001
% 3.20/0.98  splitting_time:                         0.
% 3.20/0.98  sem_filter_time:                        0.
% 3.20/0.98  monotx_time:                            0.001
% 3.20/0.98  subtype_inf_time:                       0.
% 3.20/0.98  
% 3.20/0.98  ------ Problem properties
% 3.20/0.98  
% 3.20/0.98  clauses:                                23
% 3.20/0.98  conjectures:                            2
% 3.20/0.98  epr:                                    0
% 3.20/0.98  horn:                                   16
% 3.20/0.98  ground:                                 2
% 3.20/0.98  unary:                                  6
% 3.20/0.98  binary:                                 8
% 3.20/0.98  lits:                                   53
% 3.20/0.98  lits_eq:                                21
% 3.20/0.98  fd_pure:                                0
% 3.20/0.98  fd_pseudo:                              0
% 3.20/0.98  fd_cond:                                1
% 3.20/0.98  fd_pseudo_cond:                         7
% 3.20/0.98  ac_symbols:                             0
% 3.20/0.98  
% 3.20/0.98  ------ Propositional Solver
% 3.20/0.98  
% 3.20/0.98  prop_solver_calls:                      24
% 3.20/0.98  prop_fast_solver_calls:                 617
% 3.20/0.98  smt_solver_calls:                       0
% 3.20/0.98  smt_fast_solver_calls:                  0
% 3.20/0.98  prop_num_of_clauses:                    3812
% 3.20/0.98  prop_preprocess_simplified:             8880
% 3.20/0.98  prop_fo_subsumed:                       4
% 3.20/0.98  prop_solver_time:                       0.
% 3.20/0.98  smt_solver_time:                        0.
% 3.20/0.98  smt_fast_solver_time:                   0.
% 3.20/0.98  prop_fast_solver_time:                  0.
% 3.20/0.98  prop_unsat_core_time:                   0.
% 3.20/0.98  
% 3.20/0.98  ------ QBF
% 3.20/0.98  
% 3.20/0.98  qbf_q_res:                              0
% 3.20/0.98  qbf_num_tautologies:                    0
% 3.20/0.98  qbf_prep_cycles:                        0
% 3.20/0.98  
% 3.20/0.98  ------ BMC1
% 3.20/0.98  
% 3.20/0.98  bmc1_current_bound:                     -1
% 3.20/0.98  bmc1_last_solved_bound:                 -1
% 3.20/0.98  bmc1_unsat_core_size:                   -1
% 3.20/0.98  bmc1_unsat_core_parents_size:           -1
% 3.20/0.98  bmc1_merge_next_fun:                    0
% 3.20/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.20/0.98  
% 3.20/0.98  ------ Instantiation
% 3.20/0.98  
% 3.20/0.98  inst_num_of_clauses:                    943
% 3.20/0.98  inst_num_in_passive:                    252
% 3.20/0.98  inst_num_in_active:                     352
% 3.20/0.98  inst_num_in_unprocessed:                349
% 3.20/0.98  inst_num_of_loops:                      430
% 3.20/0.98  inst_num_of_learning_restarts:          0
% 3.20/0.98  inst_num_moves_active_passive:          76
% 3.20/0.98  inst_lit_activity:                      0
% 3.20/0.98  inst_lit_activity_moves:                0
% 3.20/0.98  inst_num_tautologies:                   0
% 3.20/0.98  inst_num_prop_implied:                  0
% 3.20/0.98  inst_num_existing_simplified:           0
% 3.20/0.98  inst_num_eq_res_simplified:             0
% 3.20/0.98  inst_num_child_elim:                    0
% 3.20/0.98  inst_num_of_dismatching_blockings:      820
% 3.20/0.98  inst_num_of_non_proper_insts:           970
% 3.20/0.98  inst_num_of_duplicates:                 0
% 3.20/0.98  inst_inst_num_from_inst_to_res:         0
% 3.20/0.98  inst_dismatching_checking_time:         0.
% 3.20/0.98  
% 3.20/0.98  ------ Resolution
% 3.20/0.98  
% 3.20/0.98  res_num_of_clauses:                     0
% 3.20/0.98  res_num_in_passive:                     0
% 3.20/0.98  res_num_in_active:                      0
% 3.20/0.98  res_num_of_loops:                       87
% 3.20/0.98  res_forward_subset_subsumed:            155
% 3.20/0.98  res_backward_subset_subsumed:           24
% 3.20/0.98  res_forward_subsumed:                   0
% 3.20/0.98  res_backward_subsumed:                  0
% 3.20/0.98  res_forward_subsumption_resolution:     0
% 3.20/0.98  res_backward_subsumption_resolution:    0
% 3.20/0.98  res_clause_to_clause_subsumption:       2334
% 3.20/0.98  res_orphan_elimination:                 0
% 3.20/0.98  res_tautology_del:                      22
% 3.20/0.98  res_num_eq_res_simplified:              0
% 3.20/0.98  res_num_sel_changes:                    0
% 3.20/0.98  res_moves_from_active_to_pass:          0
% 3.20/0.98  
% 3.20/0.98  ------ Superposition
% 3.20/0.98  
% 3.20/0.98  sup_time_total:                         0.
% 3.20/0.98  sup_time_generating:                    0.
% 3.20/0.98  sup_time_sim_full:                      0.
% 3.20/0.98  sup_time_sim_immed:                     0.
% 3.20/0.98  
% 3.20/0.98  sup_num_of_clauses:                     257
% 3.20/0.98  sup_num_in_active:                      82
% 3.20/0.98  sup_num_in_passive:                     175
% 3.20/0.98  sup_num_of_loops:                       85
% 3.20/0.98  sup_fw_superposition:                   596
% 3.20/0.98  sup_bw_superposition:                   325
% 3.20/0.98  sup_immediate_simplified:               379
% 3.20/0.98  sup_given_eliminated:                   1
% 3.20/0.98  comparisons_done:                       0
% 3.20/0.98  comparisons_avoided:                    9
% 3.20/0.98  
% 3.20/0.98  ------ Simplifications
% 3.20/0.98  
% 3.20/0.98  
% 3.20/0.98  sim_fw_subset_subsumed:                 94
% 3.20/0.98  sim_bw_subset_subsumed:                 8
% 3.20/0.98  sim_fw_subsumed:                        65
% 3.20/0.98  sim_bw_subsumed:                        3
% 3.20/0.98  sim_fw_subsumption_res:                 2
% 3.20/0.98  sim_bw_subsumption_res:                 0
% 3.20/0.98  sim_tautology_del:                      13
% 3.20/0.98  sim_eq_tautology_del:                   36
% 3.20/0.98  sim_eq_res_simp:                        3
% 3.20/0.98  sim_fw_demodulated:                     206
% 3.20/0.98  sim_bw_demodulated:                     8
% 3.20/0.98  sim_light_normalised:                   88
% 3.20/0.98  sim_joinable_taut:                      0
% 3.20/0.98  sim_joinable_simp:                      0
% 3.20/0.98  sim_ac_normalised:                      0
% 3.20/0.98  sim_smt_subsumption:                    0
% 3.20/0.98  
%------------------------------------------------------------------------------
