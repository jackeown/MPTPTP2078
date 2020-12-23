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
% DateTime   : Thu Dec  3 11:36:23 EST 2020

% Result     : Theorem 47.59s
% Output     : CNFRefutation 47.59s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 527 expanded)
%              Number of clauses        :   69 (  80 expanded)
%              Number of leaves         :   21 ( 145 expanded)
%              Depth                    :   14
%              Number of atoms          :  454 (1482 expanded)
%              Number of equality atoms :  231 ( 965 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f62,f70])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f61,f71])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f60,f72])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f73])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f66,f74,f74])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f50,f48])).

fof(f4,axiom,(
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

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f28])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f53,f73])).

fof(f91,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f81])).

fof(f92,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f91])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,
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

fof(f38,plain,
    ( ( r2_hidden(sK3,sK4)
      | r2_hidden(sK2,sK4)
      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3) )
    & ( ( ~ r2_hidden(sK3,sK4)
        & ~ r2_hidden(sK2,sK4) )
      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f37])).

fof(f69,plain,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK2,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK2,sK4)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(definition_unfolding,[],[f69,f48,f74,f74])).

fof(f54,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f54,f73])).

fof(f89,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f80])).

fof(f90,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f89])).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f82,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f52,f73])).

fof(f93,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f82])).

fof(f94,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f93])).

fof(f51,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f51,f73])).

fof(f95,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f83])).

fof(f68,plain,
    ( ~ r2_hidden(sK3,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,
    ( ~ r2_hidden(sK3,sK4)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(definition_unfolding,[],[f68,f48,f74,f74])).

fof(f67,plain,
    ( ~ r2_hidden(sK2,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f88,plain,
    ( ~ r2_hidden(sK2,sK4)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(definition_unfolding,[],[f67,f48,f74,f74])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_20615,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,k5_xboole_0(X0,sK4))
    | r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_144402,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3))
    | r2_hidden(sK2,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4))
    | r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_20615])).

cnf(c_144409,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
    | r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_144402])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_7328,plain,
    ( ~ r2_hidden(sK2,X0)
    | ~ r2_hidden(sK3,X0)
    | k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),X0) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_29660,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(X0,sK4))
    | ~ r2_hidden(sK3,k5_xboole_0(X0,sK4))
    | k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(X0,sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_7328])).

cnf(c_140073,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4))
    | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4))
    | k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_29660])).

cnf(c_140080,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
    | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
    | k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_140073])).

cnf(c_10,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_11390,plain,
    ( r1_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),X2)),X2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_54878,plain,
    ( r1_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_11390])).

cnf(c_54883,plain,
    ( r1_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54878])).

cnf(c_54885,plain,
    ( r1_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_54883])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1190,plain,
    ( ~ r1_xboole_0(k5_xboole_0(X0,X1),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,k5_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3209,plain,
    ( ~ r1_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),X2),X3)
    | ~ r2_hidden(sK3,X3)
    | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),X2)) ),
    inference(instantiation,[status(thm)],[c_1190])).

cnf(c_44775,plain,
    ( ~ r1_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),X2),sK4)
    | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),X2))
    | ~ r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_3209])).

cnf(c_54877,plain,
    ( ~ r1_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4)),sK4)
    | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4)))
    | ~ r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_44775])).

cnf(c_54879,plain,
    ( r1_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4)),sK4) != iProver_top
    | r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4))) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54877])).

cnf(c_54881,plain,
    ( r1_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4) != iProver_top
    | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_54879])).

cnf(c_714,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X0))
    | r2_hidden(X0,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X0),X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1369,plain,
    ( r2_hidden(sK3,X0)
    | ~ r2_hidden(sK3,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,sK3))
    | r2_hidden(sK3,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,sK3),X0)) ),
    inference(instantiation,[status(thm)],[c_714])).

cnf(c_33467,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3))
    | r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4))
    | r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1369])).

cnf(c_33469,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
    | r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_33467])).

cnf(c_185,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_713,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2))
    | X0 != X2
    | X1 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2) ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(c_13219,plain,
    ( r2_hidden(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | ~ r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | X0 != sK3
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_713])).

cnf(c_32564,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_13219])).

cnf(c_32565,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | sK3 != sK3
    | r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
    | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32564])).

cnf(c_855,plain,
    ( ~ r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_31098,plain,
    ( ~ r1_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4)
    | ~ r2_hidden(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | ~ r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_855])).

cnf(c_31099,plain,
    ( r1_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4) != iProver_top
    | r2_hidden(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31098])).

cnf(c_31101,plain,
    ( r1_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4) != iProver_top
    | r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != iProver_top
    | r2_hidden(sK2,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_31099])).

cnf(c_16,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_964,plain,
    ( r2_hidden(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,sK2,X1)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_20097,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_964])).

cnf(c_20098,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20097])).

cnf(c_181,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_14059,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_181])).

cnf(c_1855,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k5_xboole_0(X3,X4))
    | X2 != X0
    | k5_xboole_0(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(c_5649,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | X2 != X0
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != X1 ),
    inference(instantiation,[status(thm)],[c_1855])).

cnf(c_9934,plain,
    ( ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | r2_hidden(X1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | X1 != X0
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_5649])).

cnf(c_9935,plain,
    ( X0 != X1
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(X1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
    | r2_hidden(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9934])).

cnf(c_9937,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | sK2 != sK2
    | r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
    | r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_9935])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_9,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1071,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_9])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK3,sK4)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_487,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_774,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_487])).

cnf(c_1535,plain,
    ( k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1071,c_774])).

cnf(c_1665,plain,
    ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1535])).

cnf(c_1667,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK3,sK4)
    | k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1665])).

cnf(c_15,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_926,plain,
    ( r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_931,plain,
    ( r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_926])).

cnf(c_933,plain,
    ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_931])).

cnf(c_932,plain,
    ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_926])).

cnf(c_17,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_35,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_32,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_26,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(sK3,sK4)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(sK2,sK4)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_24,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_144409,c_140080,c_54885,c_54881,c_33469,c_32565,c_31101,c_20098,c_20097,c_14059,c_9937,c_1667,c_933,c_932,c_35,c_32,c_26,c_22,c_24,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 18:45:42 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 47.59/6.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 47.59/6.48  
% 47.59/6.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 47.59/6.48  
% 47.59/6.48  ------  iProver source info
% 47.59/6.48  
% 47.59/6.48  git: date: 2020-06-30 10:37:57 +0100
% 47.59/6.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 47.59/6.48  git: non_committed_changes: false
% 47.59/6.48  git: last_make_outside_of_git: false
% 47.59/6.48  
% 47.59/6.48  ------ 
% 47.59/6.48  ------ Parsing...
% 47.59/6.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 47.59/6.48  
% 47.59/6.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 47.59/6.48  
% 47.59/6.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 47.59/6.48  
% 47.59/6.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.59/6.48  ------ Proving...
% 47.59/6.48  ------ Problem Properties 
% 47.59/6.48  
% 47.59/6.48  
% 47.59/6.48  clauses                                 24
% 47.59/6.48  conjectures                             3
% 47.59/6.48  EPR                                     1
% 47.59/6.48  Horn                                    16
% 47.59/6.48  unary                                   8
% 47.59/6.48  binary                                  4
% 47.59/6.48  lits                                    55
% 47.59/6.48  lits eq                                 21
% 47.59/6.48  fd_pure                                 0
% 47.59/6.48  fd_pseudo                               0
% 47.59/6.48  fd_cond                                 0
% 47.59/6.48  fd_pseudo_cond                          4
% 47.59/6.48  AC symbols                              0
% 47.59/6.48  
% 47.59/6.48  ------ Input Options Time Limit: Unbounded
% 47.59/6.48  
% 47.59/6.48  
% 47.59/6.48  ------ 
% 47.59/6.48  Current options:
% 47.59/6.48  ------ 
% 47.59/6.48  
% 47.59/6.48  
% 47.59/6.48  
% 47.59/6.48  
% 47.59/6.48  ------ Proving...
% 47.59/6.48  
% 47.59/6.48  
% 47.59/6.48  % SZS status Theorem for theBenchmark.p
% 47.59/6.48  
% 47.59/6.48  % SZS output start CNFRefutation for theBenchmark.p
% 47.59/6.48  
% 47.59/6.48  fof(f3,axiom,(
% 47.59/6.48    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 47.59/6.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.59/6.48  
% 47.59/6.48  fof(f21,plain,(
% 47.59/6.48    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 47.59/6.48    inference(ennf_transformation,[],[f3])).
% 47.59/6.48  
% 47.59/6.48  fof(f27,plain,(
% 47.59/6.48    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 47.59/6.48    inference(nnf_transformation,[],[f21])).
% 47.59/6.48  
% 47.59/6.48  fof(f43,plain,(
% 47.59/6.48    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 47.59/6.48    inference(cnf_transformation,[],[f27])).
% 47.59/6.48  
% 47.59/6.48  fof(f16,axiom,(
% 47.59/6.48    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2))),
% 47.59/6.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.59/6.48  
% 47.59/6.48  fof(f24,plain,(
% 47.59/6.48    ! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 47.59/6.48    inference(ennf_transformation,[],[f16])).
% 47.59/6.48  
% 47.59/6.48  fof(f25,plain,(
% 47.59/6.48    ! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 47.59/6.48    inference(flattening,[],[f24])).
% 47.59/6.48  
% 47.59/6.48  fof(f66,plain,(
% 47.59/6.48    ( ! [X2,X0,X1] : (k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 47.59/6.48    inference(cnf_transformation,[],[f25])).
% 47.59/6.48  
% 47.59/6.48  fof(f9,axiom,(
% 47.59/6.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 47.59/6.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.59/6.48  
% 47.59/6.48  fof(f59,plain,(
% 47.59/6.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 47.59/6.48    inference(cnf_transformation,[],[f9])).
% 47.59/6.48  
% 47.59/6.48  fof(f10,axiom,(
% 47.59/6.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 47.59/6.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.59/6.48  
% 47.59/6.48  fof(f60,plain,(
% 47.59/6.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 47.59/6.48    inference(cnf_transformation,[],[f10])).
% 47.59/6.48  
% 47.59/6.48  fof(f11,axiom,(
% 47.59/6.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 47.59/6.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.59/6.48  
% 47.59/6.48  fof(f61,plain,(
% 47.59/6.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 47.59/6.48    inference(cnf_transformation,[],[f11])).
% 47.59/6.48  
% 47.59/6.48  fof(f12,axiom,(
% 47.59/6.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 47.59/6.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.59/6.48  
% 47.59/6.48  fof(f62,plain,(
% 47.59/6.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 47.59/6.48    inference(cnf_transformation,[],[f12])).
% 47.59/6.48  
% 47.59/6.48  fof(f13,axiom,(
% 47.59/6.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 47.59/6.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.59/6.48  
% 47.59/6.48  fof(f63,plain,(
% 47.59/6.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 47.59/6.48    inference(cnf_transformation,[],[f13])).
% 47.59/6.48  
% 47.59/6.48  fof(f14,axiom,(
% 47.59/6.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 47.59/6.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.59/6.48  
% 47.59/6.48  fof(f64,plain,(
% 47.59/6.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 47.59/6.48    inference(cnf_transformation,[],[f14])).
% 47.59/6.48  
% 47.59/6.48  fof(f70,plain,(
% 47.59/6.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 47.59/6.48    inference(definition_unfolding,[],[f63,f64])).
% 47.59/6.48  
% 47.59/6.48  fof(f71,plain,(
% 47.59/6.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 47.59/6.48    inference(definition_unfolding,[],[f62,f70])).
% 47.59/6.48  
% 47.59/6.48  fof(f72,plain,(
% 47.59/6.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 47.59/6.48    inference(definition_unfolding,[],[f61,f71])).
% 47.59/6.48  
% 47.59/6.48  fof(f73,plain,(
% 47.59/6.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 47.59/6.48    inference(definition_unfolding,[],[f60,f72])).
% 47.59/6.48  
% 47.59/6.48  fof(f74,plain,(
% 47.59/6.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 47.59/6.48    inference(definition_unfolding,[],[f59,f73])).
% 47.59/6.48  
% 47.59/6.48  fof(f85,plain,(
% 47.59/6.48    ( ! [X2,X0,X1] : (k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 47.59/6.48    inference(definition_unfolding,[],[f66,f74,f74])).
% 47.59/6.48  
% 47.59/6.48  fof(f7,axiom,(
% 47.59/6.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 47.59/6.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.59/6.48  
% 47.59/6.48  fof(f50,plain,(
% 47.59/6.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 47.59/6.48    inference(cnf_transformation,[],[f7])).
% 47.59/6.48  
% 47.59/6.48  fof(f5,axiom,(
% 47.59/6.48    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 47.59/6.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.59/6.48  
% 47.59/6.48  fof(f48,plain,(
% 47.59/6.48    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 47.59/6.48    inference(cnf_transformation,[],[f5])).
% 47.59/6.48  
% 47.59/6.48  fof(f75,plain,(
% 47.59/6.48    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 47.59/6.48    inference(definition_unfolding,[],[f50,f48])).
% 47.59/6.48  
% 47.59/6.48  fof(f4,axiom,(
% 47.59/6.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 47.59/6.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.59/6.48  
% 47.59/6.48  fof(f20,plain,(
% 47.59/6.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 47.59/6.48    inference(rectify,[],[f4])).
% 47.59/6.48  
% 47.59/6.48  fof(f22,plain,(
% 47.59/6.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 47.59/6.48    inference(ennf_transformation,[],[f20])).
% 47.59/6.48  
% 47.59/6.48  fof(f28,plain,(
% 47.59/6.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 47.59/6.48    introduced(choice_axiom,[])).
% 47.59/6.48  
% 47.59/6.48  fof(f29,plain,(
% 47.59/6.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 47.59/6.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f28])).
% 47.59/6.48  
% 47.59/6.48  fof(f47,plain,(
% 47.59/6.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 47.59/6.48    inference(cnf_transformation,[],[f29])).
% 47.59/6.48  
% 47.59/6.48  fof(f8,axiom,(
% 47.59/6.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 47.59/6.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.59/6.48  
% 47.59/6.48  fof(f23,plain,(
% 47.59/6.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 47.59/6.48    inference(ennf_transformation,[],[f8])).
% 47.59/6.48  
% 47.59/6.48  fof(f30,plain,(
% 47.59/6.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 47.59/6.48    inference(nnf_transformation,[],[f23])).
% 47.59/6.48  
% 47.59/6.48  fof(f31,plain,(
% 47.59/6.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 47.59/6.48    inference(flattening,[],[f30])).
% 47.59/6.48  
% 47.59/6.48  fof(f32,plain,(
% 47.59/6.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 47.59/6.48    inference(rectify,[],[f31])).
% 47.59/6.48  
% 47.59/6.48  fof(f33,plain,(
% 47.59/6.48    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 47.59/6.48    introduced(choice_axiom,[])).
% 47.59/6.48  
% 47.59/6.48  fof(f34,plain,(
% 47.59/6.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 47.59/6.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 47.59/6.48  
% 47.59/6.48  fof(f53,plain,(
% 47.59/6.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 47.59/6.48    inference(cnf_transformation,[],[f34])).
% 47.59/6.48  
% 47.59/6.48  fof(f81,plain,(
% 47.59/6.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 47.59/6.48    inference(definition_unfolding,[],[f53,f73])).
% 47.59/6.48  
% 47.59/6.48  fof(f91,plain,(
% 47.59/6.48    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 47.59/6.48    inference(equality_resolution,[],[f81])).
% 47.59/6.48  
% 47.59/6.48  fof(f92,plain,(
% 47.59/6.48    ( ! [X2,X0,X5] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2))) )),
% 47.59/6.48    inference(equality_resolution,[],[f91])).
% 47.59/6.48  
% 47.59/6.48  fof(f1,axiom,(
% 47.59/6.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 47.59/6.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.59/6.48  
% 47.59/6.48  fof(f39,plain,(
% 47.59/6.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 47.59/6.48    inference(cnf_transformation,[],[f1])).
% 47.59/6.48  
% 47.59/6.48  fof(f2,axiom,(
% 47.59/6.48    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 47.59/6.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.59/6.48  
% 47.59/6.48  fof(f19,plain,(
% 47.59/6.48    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 47.59/6.48    inference(rectify,[],[f2])).
% 47.59/6.48  
% 47.59/6.48  fof(f40,plain,(
% 47.59/6.48    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 47.59/6.48    inference(cnf_transformation,[],[f19])).
% 47.59/6.48  
% 47.59/6.48  fof(f6,axiom,(
% 47.59/6.48    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 47.59/6.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.59/6.48  
% 47.59/6.48  fof(f49,plain,(
% 47.59/6.48    ( ! [X2,X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))) )),
% 47.59/6.48    inference(cnf_transformation,[],[f6])).
% 47.59/6.48  
% 47.59/6.48  fof(f17,conjecture,(
% 47.59/6.48    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 47.59/6.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.59/6.48  
% 47.59/6.48  fof(f18,negated_conjecture,(
% 47.59/6.48    ~! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 47.59/6.48    inference(negated_conjecture,[],[f17])).
% 47.59/6.48  
% 47.59/6.48  fof(f26,plain,(
% 47.59/6.48    ? [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 47.59/6.48    inference(ennf_transformation,[],[f18])).
% 47.59/6.48  
% 47.59/6.48  fof(f35,plain,(
% 47.59/6.48    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)))),
% 47.59/6.48    inference(nnf_transformation,[],[f26])).
% 47.59/6.48  
% 47.59/6.48  fof(f36,plain,(
% 47.59/6.48    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)))),
% 47.59/6.48    inference(flattening,[],[f35])).
% 47.59/6.48  
% 47.59/6.48  fof(f37,plain,(
% 47.59/6.48    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1))) => ((r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3)) & ((~r2_hidden(sK3,sK4) & ~r2_hidden(sK2,sK4)) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3)))),
% 47.59/6.48    introduced(choice_axiom,[])).
% 47.59/6.48  
% 47.59/6.48  fof(f38,plain,(
% 47.59/6.48    (r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3)) & ((~r2_hidden(sK3,sK4) & ~r2_hidden(sK2,sK4)) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3))),
% 47.59/6.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f37])).
% 47.59/6.48  
% 47.59/6.48  fof(f69,plain,(
% 47.59/6.48    r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3)),
% 47.59/6.48    inference(cnf_transformation,[],[f38])).
% 47.59/6.48  
% 47.59/6.48  fof(f86,plain,(
% 47.59/6.48    r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)),
% 47.59/6.48    inference(definition_unfolding,[],[f69,f48,f74,f74])).
% 47.59/6.48  
% 47.59/6.48  fof(f54,plain,(
% 47.59/6.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 47.59/6.48    inference(cnf_transformation,[],[f34])).
% 47.59/6.48  
% 47.59/6.48  fof(f80,plain,(
% 47.59/6.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 47.59/6.48    inference(definition_unfolding,[],[f54,f73])).
% 47.59/6.48  
% 47.59/6.48  fof(f89,plain,(
% 47.59/6.48    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 47.59/6.48    inference(equality_resolution,[],[f80])).
% 47.59/6.48  
% 47.59/6.48  fof(f90,plain,(
% 47.59/6.48    ( ! [X0,X5,X1] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5))) )),
% 47.59/6.48    inference(equality_resolution,[],[f89])).
% 47.59/6.48  
% 47.59/6.48  fof(f52,plain,(
% 47.59/6.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 47.59/6.48    inference(cnf_transformation,[],[f34])).
% 47.59/6.48  
% 47.59/6.48  fof(f82,plain,(
% 47.59/6.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 47.59/6.48    inference(definition_unfolding,[],[f52,f73])).
% 47.59/6.48  
% 47.59/6.48  fof(f93,plain,(
% 47.59/6.48    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 47.59/6.48    inference(equality_resolution,[],[f82])).
% 47.59/6.48  
% 47.59/6.48  fof(f94,plain,(
% 47.59/6.48    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 47.59/6.48    inference(equality_resolution,[],[f93])).
% 47.59/6.48  
% 47.59/6.48  fof(f51,plain,(
% 47.59/6.48    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 47.59/6.48    inference(cnf_transformation,[],[f34])).
% 47.59/6.48  
% 47.59/6.48  fof(f83,plain,(
% 47.59/6.48    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 47.59/6.48    inference(definition_unfolding,[],[f51,f73])).
% 47.59/6.48  
% 47.59/6.48  fof(f95,plain,(
% 47.59/6.48    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 47.59/6.48    inference(equality_resolution,[],[f83])).
% 47.59/6.48  
% 47.59/6.48  fof(f68,plain,(
% 47.59/6.48    ~r2_hidden(sK3,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3)),
% 47.59/6.48    inference(cnf_transformation,[],[f38])).
% 47.59/6.48  
% 47.59/6.48  fof(f87,plain,(
% 47.59/6.48    ~r2_hidden(sK3,sK4) | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)),
% 47.59/6.48    inference(definition_unfolding,[],[f68,f48,f74,f74])).
% 47.59/6.48  
% 47.59/6.48  fof(f67,plain,(
% 47.59/6.48    ~r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3)),
% 47.59/6.48    inference(cnf_transformation,[],[f38])).
% 47.59/6.48  
% 47.59/6.48  fof(f88,plain,(
% 47.59/6.48    ~r2_hidden(sK2,sK4) | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)),
% 47.59/6.48    inference(definition_unfolding,[],[f67,f48,f74,f74])).
% 47.59/6.48  
% 47.59/6.48  cnf(c_3,plain,
% 47.59/6.48      ( ~ r2_hidden(X0,X1)
% 47.59/6.48      | r2_hidden(X0,X2)
% 47.59/6.48      | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 47.59/6.48      inference(cnf_transformation,[],[f43]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_20615,plain,
% 47.59/6.48      ( ~ r2_hidden(sK2,X0)
% 47.59/6.48      | r2_hidden(sK2,k5_xboole_0(X0,sK4))
% 47.59/6.48      | r2_hidden(sK2,sK4) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_3]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_144402,plain,
% 47.59/6.48      ( ~ r2_hidden(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3))
% 47.59/6.48      | r2_hidden(sK2,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4))
% 47.59/6.48      | r2_hidden(sK2,sK4) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_20615]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_144409,plain,
% 47.59/6.48      ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 47.59/6.48      | r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
% 47.59/6.48      | r2_hidden(sK2,sK4) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_144402]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_20,plain,
% 47.59/6.48      ( ~ r2_hidden(X0,X1)
% 47.59/6.48      | ~ r2_hidden(X2,X1)
% 47.59/6.48      | k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) ),
% 47.59/6.48      inference(cnf_transformation,[],[f85]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_7328,plain,
% 47.59/6.48      ( ~ r2_hidden(sK2,X0)
% 47.59/6.48      | ~ r2_hidden(sK3,X0)
% 47.59/6.48      | k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),X0) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_20]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_29660,plain,
% 47.59/6.48      ( ~ r2_hidden(sK2,k5_xboole_0(X0,sK4))
% 47.59/6.48      | ~ r2_hidden(sK3,k5_xboole_0(X0,sK4))
% 47.59/6.48      | k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(X0,sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_7328]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_140073,plain,
% 47.59/6.48      ( ~ r2_hidden(sK2,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4))
% 47.59/6.48      | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4))
% 47.59/6.48      | k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_29660]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_140080,plain,
% 47.59/6.48      ( ~ r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
% 47.59/6.48      | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
% 47.59/6.48      | k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_140073]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_10,plain,
% 47.59/6.48      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 47.59/6.48      inference(cnf_transformation,[],[f75]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_11390,plain,
% 47.59/6.48      ( r1_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),X2)),X2) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_10]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_54878,plain,
% 47.59/6.48      ( r1_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4)),sK4) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_11390]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_54883,plain,
% 47.59/6.48      ( r1_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4)),sK4) = iProver_top ),
% 47.59/6.48      inference(predicate_to_equality,[status(thm)],[c_54878]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_54885,plain,
% 47.59/6.48      ( r1_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4) = iProver_top ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_54883]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_6,plain,
% 47.59/6.48      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 47.59/6.48      inference(cnf_transformation,[],[f47]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_1190,plain,
% 47.59/6.48      ( ~ r1_xboole_0(k5_xboole_0(X0,X1),X2)
% 47.59/6.48      | ~ r2_hidden(X3,X2)
% 47.59/6.48      | ~ r2_hidden(X3,k5_xboole_0(X0,X1)) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_6]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_3209,plain,
% 47.59/6.48      ( ~ r1_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),X2),X3)
% 47.59/6.48      | ~ r2_hidden(sK3,X3)
% 47.59/6.48      | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),X2)) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_1190]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_44775,plain,
% 47.59/6.48      ( ~ r1_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),X2),sK4)
% 47.59/6.48      | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),X2))
% 47.59/6.48      | ~ r2_hidden(sK3,sK4) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_3209]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_54877,plain,
% 47.59/6.48      ( ~ r1_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4)),sK4)
% 47.59/6.48      | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4)))
% 47.59/6.48      | ~ r2_hidden(sK3,sK4) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_44775]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_54879,plain,
% 47.59/6.48      ( r1_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4)),sK4) != iProver_top
% 47.59/6.48      | r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4))) != iProver_top
% 47.59/6.48      | r2_hidden(sK3,sK4) != iProver_top ),
% 47.59/6.48      inference(predicate_to_equality,[status(thm)],[c_54877]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_54881,plain,
% 47.59/6.48      ( r1_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4) != iProver_top
% 47.59/6.48      | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != iProver_top
% 47.59/6.48      | r2_hidden(sK3,sK4) != iProver_top ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_54879]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_714,plain,
% 47.59/6.48      ( r2_hidden(X0,X1)
% 47.59/6.48      | ~ r2_hidden(X0,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X0))
% 47.59/6.48      | r2_hidden(X0,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X0),X1)) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_3]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_1369,plain,
% 47.59/6.48      ( r2_hidden(sK3,X0)
% 47.59/6.48      | ~ r2_hidden(sK3,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,sK3))
% 47.59/6.48      | r2_hidden(sK3,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,sK3),X0)) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_714]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_33467,plain,
% 47.59/6.48      ( ~ r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3))
% 47.59/6.48      | r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4))
% 47.59/6.48      | r2_hidden(sK3,sK4) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_1369]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_33469,plain,
% 47.59/6.48      ( ~ r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 47.59/6.48      | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
% 47.59/6.48      | r2_hidden(sK3,sK4) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_33467]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_185,plain,
% 47.59/6.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 47.59/6.48      theory(equality) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_713,plain,
% 47.59/6.48      ( r2_hidden(X0,X1)
% 47.59/6.48      | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2))
% 47.59/6.48      | X0 != X2
% 47.59/6.48      | X1 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_185]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_13219,plain,
% 47.59/6.48      ( r2_hidden(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 47.59/6.48      | ~ r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 47.59/6.48      | X0 != sK3
% 47.59/6.48      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_713]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_32564,plain,
% 47.59/6.48      ( ~ r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 47.59/6.48      | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 47.59/6.48      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 47.59/6.48      | sK3 != sK3 ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_13219]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_32565,plain,
% 47.59/6.48      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 47.59/6.48      | sK3 != sK3
% 47.59/6.48      | r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
% 47.59/6.48      | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = iProver_top ),
% 47.59/6.48      inference(predicate_to_equality,[status(thm)],[c_32564]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_855,plain,
% 47.59/6.48      ( ~ r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)
% 47.59/6.48      | ~ r2_hidden(X2,X1)
% 47.59/6.48      | ~ r2_hidden(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_6]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_31098,plain,
% 47.59/6.48      ( ~ r1_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4)
% 47.59/6.48      | ~ r2_hidden(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 47.59/6.48      | ~ r2_hidden(X0,sK4) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_855]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_31099,plain,
% 47.59/6.48      ( r1_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4) != iProver_top
% 47.59/6.48      | r2_hidden(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != iProver_top
% 47.59/6.48      | r2_hidden(X0,sK4) != iProver_top ),
% 47.59/6.48      inference(predicate_to_equality,[status(thm)],[c_31098]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_31101,plain,
% 47.59/6.48      ( r1_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4) != iProver_top
% 47.59/6.48      | r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != iProver_top
% 47.59/6.48      | r2_hidden(sK2,sK4) != iProver_top ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_31099]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_16,plain,
% 47.59/6.48      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) ),
% 47.59/6.48      inference(cnf_transformation,[],[f92]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_964,plain,
% 47.59/6.48      ( r2_hidden(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,sK2,X1)) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_16]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_20097,plain,
% 47.59/6.48      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_964]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_20098,plain,
% 47.59/6.48      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top ),
% 47.59/6.48      inference(predicate_to_equality,[status(thm)],[c_20097]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_181,plain,( X0 = X0 ),theory(equality) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_14059,plain,
% 47.59/6.48      ( sK3 = sK3 ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_181]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_1855,plain,
% 47.59/6.48      ( ~ r2_hidden(X0,X1)
% 47.59/6.48      | r2_hidden(X2,k5_xboole_0(X3,X4))
% 47.59/6.48      | X2 != X0
% 47.59/6.48      | k5_xboole_0(X3,X4) != X1 ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_185]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_5649,plain,
% 47.59/6.48      ( ~ r2_hidden(X0,X1)
% 47.59/6.48      | r2_hidden(X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 47.59/6.48      | X2 != X0
% 47.59/6.48      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != X1 ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_1855]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_9934,plain,
% 47.59/6.48      ( ~ r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 47.59/6.48      | r2_hidden(X1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 47.59/6.48      | X1 != X0
% 47.59/6.48      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_5649]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_9935,plain,
% 47.59/6.48      ( X0 != X1
% 47.59/6.48      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 47.59/6.48      | r2_hidden(X1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
% 47.59/6.48      | r2_hidden(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = iProver_top ),
% 47.59/6.48      inference(predicate_to_equality,[status(thm)],[c_9934]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_9937,plain,
% 47.59/6.48      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 47.59/6.48      | sK2 != sK2
% 47.59/6.48      | r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
% 47.59/6.48      | r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = iProver_top ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_9935]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_0,plain,
% 47.59/6.48      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 47.59/6.48      inference(cnf_transformation,[],[f39]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_1,plain,
% 47.59/6.48      ( k3_xboole_0(X0,X0) = X0 ),
% 47.59/6.48      inference(cnf_transformation,[],[f40]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_9,plain,
% 47.59/6.48      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
% 47.59/6.48      inference(cnf_transformation,[],[f49]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_1071,plain,
% 47.59/6.48      ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
% 47.59/6.48      inference(superposition,[status(thm)],[c_1,c_9]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_21,negated_conjecture,
% 47.59/6.48      ( r2_hidden(sK2,sK4)
% 47.59/6.48      | r2_hidden(sK3,sK4)
% 47.59/6.48      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 47.59/6.48      inference(cnf_transformation,[],[f86]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_487,plain,
% 47.59/6.48      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 47.59/6.48      | r2_hidden(sK2,sK4) = iProver_top
% 47.59/6.48      | r2_hidden(sK3,sK4) = iProver_top ),
% 47.59/6.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_774,plain,
% 47.59/6.48      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 47.59/6.48      | r2_hidden(sK2,sK4) = iProver_top
% 47.59/6.48      | r2_hidden(sK3,sK4) = iProver_top ),
% 47.59/6.48      inference(demodulation,[status(thm)],[c_0,c_487]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_1535,plain,
% 47.59/6.48      ( k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 47.59/6.48      | r2_hidden(sK2,sK4) = iProver_top
% 47.59/6.48      | r2_hidden(sK3,sK4) = iProver_top ),
% 47.59/6.48      inference(demodulation,[status(thm)],[c_1071,c_774]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_1665,plain,
% 47.59/6.48      ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 47.59/6.48      | r2_hidden(sK2,sK4) = iProver_top
% 47.59/6.48      | r2_hidden(sK3,sK4) = iProver_top ),
% 47.59/6.48      inference(superposition,[status(thm)],[c_0,c_1535]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_1667,plain,
% 47.59/6.48      ( r2_hidden(sK2,sK4)
% 47.59/6.48      | r2_hidden(sK3,sK4)
% 47.59/6.48      | k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 47.59/6.48      inference(predicate_to_equality_rev,[status(thm)],[c_1665]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_15,plain,
% 47.59/6.48      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
% 47.59/6.48      inference(cnf_transformation,[],[f90]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_926,plain,
% 47.59/6.48      ( r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3)) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_15]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_931,plain,
% 47.59/6.48      ( r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3)) = iProver_top ),
% 47.59/6.48      inference(predicate_to_equality,[status(thm)],[c_926]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_933,plain,
% 47.59/6.48      ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_931]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_932,plain,
% 47.59/6.48      ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_926]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_17,plain,
% 47.59/6.48      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 47.59/6.48      inference(cnf_transformation,[],[f94]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_35,plain,
% 47.59/6.48      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_17]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_18,plain,
% 47.59/6.48      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
% 47.59/6.48      | X0 = X1
% 47.59/6.48      | X0 = X2
% 47.59/6.48      | X0 = X3 ),
% 47.59/6.48      inference(cnf_transformation,[],[f95]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_32,plain,
% 47.59/6.48      ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 47.59/6.48      | sK2 = sK2 ),
% 47.59/6.48      inference(instantiation,[status(thm)],[c_18]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_26,plain,
% 47.59/6.48      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 47.59/6.48      | r2_hidden(sK2,sK4) = iProver_top
% 47.59/6.48      | r2_hidden(sK3,sK4) = iProver_top ),
% 47.59/6.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_22,negated_conjecture,
% 47.59/6.48      ( ~ r2_hidden(sK3,sK4)
% 47.59/6.48      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 47.59/6.48      inference(cnf_transformation,[],[f87]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_23,negated_conjecture,
% 47.59/6.48      ( ~ r2_hidden(sK2,sK4)
% 47.59/6.48      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 47.59/6.48      inference(cnf_transformation,[],[f88]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(c_24,plain,
% 47.59/6.48      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 47.59/6.48      | r2_hidden(sK2,sK4) != iProver_top ),
% 47.59/6.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 47.59/6.48  
% 47.59/6.48  cnf(contradiction,plain,
% 47.59/6.48      ( $false ),
% 47.59/6.48      inference(minisat,
% 47.59/6.48                [status(thm)],
% 47.59/6.48                [c_144409,c_140080,c_54885,c_54881,c_33469,c_32565,
% 47.59/6.48                 c_31101,c_20098,c_20097,c_14059,c_9937,c_1667,c_933,
% 47.59/6.48                 c_932,c_35,c_32,c_26,c_22,c_24,c_23]) ).
% 47.59/6.48  
% 47.59/6.48  
% 47.59/6.48  % SZS output end CNFRefutation for theBenchmark.p
% 47.59/6.48  
% 47.59/6.48  ------                               Statistics
% 47.59/6.48  
% 47.59/6.48  ------ Selected
% 47.59/6.48  
% 47.59/6.48  total_time:                             5.674
% 47.59/6.48  
%------------------------------------------------------------------------------
