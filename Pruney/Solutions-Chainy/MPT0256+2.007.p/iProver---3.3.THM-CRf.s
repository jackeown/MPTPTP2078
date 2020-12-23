%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:34:49 EST 2020

% Result     : Theorem 11.88s
% Output     : CNFRefutation 11.88s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 184 expanded)
%              Number of clauses        :   28 (  32 expanded)
%              Number of leaves         :   20 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :  260 ( 358 expanded)
%              Number of equality atoms :  145 ( 237 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1)
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1)
       => r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      & k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        & k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1) )
   => ( ~ r2_hidden(sK3,sK2)
      & k3_xboole_0(sK2,k1_tarski(sK3)) = k1_tarski(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ~ r2_hidden(sK3,sK2)
    & k3_xboole_0(sK2,k1_tarski(sK3)) = k1_tarski(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f27,f36])).

fof(f69,plain,(
    k3_xboole_0(sK2,k1_tarski(sK3)) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f67,f75])).

fof(f77,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f51,f76])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f64,f71])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f63,f72])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f73])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f74])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f60,f75])).

fof(f91,plain,(
    k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f69,f77,f79,f79])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f78,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f47,f77])).

fof(f81,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X1) ),
    inference(definition_unfolding,[],[f48,f78])).

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
    inference(rectify,[],[f4])).

fof(f25,plain,(
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

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f29])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

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
    inference(nnf_transformation,[],[f26])).

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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f88,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f53,f74])).

fof(f96,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f88])).

fof(f97,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f96])).

fof(f70,plain,(
    ~ r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_22,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_238,negated_conjecture,
    ( k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(theory_normalisation,[status(thm)],[c_22,c_10,c_0])).

cnf(c_931,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),X0)) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0) ),
    inference(superposition,[status(thm)],[c_238,c_10])).

cnf(c_952,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0) ),
    inference(superposition,[status(thm)],[c_0,c_931])).

cnf(c_9,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_239,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))),X1) ),
    inference(theory_normalisation,[status(thm)],[c_9,c_10,c_0])).

cnf(c_545,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_239])).

cnf(c_38471,plain,
    ( r1_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_952,c_545])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1672,plain,
    ( ~ r1_xboole_0(k5_xboole_0(X0,X1),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,k5_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2457,plain,
    ( ~ r1_xboole_0(k5_xboole_0(X0,sK2),X1)
    | ~ r2_hidden(sK3,X1)
    | ~ r2_hidden(sK3,k5_xboole_0(X0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1672])).

cnf(c_8286,plain,
    ( ~ r1_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X0,X1),sK2),X2)
    | ~ r2_hidden(sK3,X2)
    | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X0,X1),sK2)) ),
    inference(instantiation,[status(thm)],[c_2457])).

cnf(c_14608,plain,
    ( ~ r1_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X0,X1),sK2),k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4))
    | ~ r2_hidden(sK3,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4))
    | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X0,X1),sK2)) ),
    inference(instantiation,[status(thm)],[c_8286])).

cnf(c_14609,plain,
    ( r1_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X0,X1),sK2),k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4)) != iProver_top
    | r2_hidden(sK3,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4)) != iProver_top
    | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X0,X1),sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14608])).

cnf(c_14611,plain,
    ( r1_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14609])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_710,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X0))
    | r2_hidden(X0,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X0),X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_896,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3))
    | r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK2))
    | r2_hidden(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_897,plain,
    ( r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3)) != iProver_top
    | r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK2)) = iProver_top
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_896])).

cnf(c_899,plain,
    ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK2)) = iProver_top
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_897])).

cnf(c_18,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_28,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_30,plain,
    ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_23,plain,
    ( r2_hidden(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_38471,c_14611,c_899,c_30,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:31:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.88/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.88/1.99  
% 11.88/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.88/1.99  
% 11.88/1.99  ------  iProver source info
% 11.88/1.99  
% 11.88/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.88/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.88/1.99  git: non_committed_changes: false
% 11.88/1.99  git: last_make_outside_of_git: false
% 11.88/1.99  
% 11.88/1.99  ------ 
% 11.88/1.99  ------ Parsing...
% 11.88/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.88/1.99  
% 11.88/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.88/1.99  
% 11.88/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.88/1.99  
% 11.88/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.88/1.99  ------ Proving...
% 11.88/1.99  ------ Problem Properties 
% 11.88/1.99  
% 11.88/1.99  
% 11.88/1.99  clauses                                 23
% 11.88/1.99  conjectures                             2
% 11.88/1.99  EPR                                     2
% 11.88/1.99  Horn                                    16
% 11.88/1.99  unary                                   11
% 11.88/1.99  binary                                  2
% 11.88/1.99  lits                                    48
% 11.88/1.99  lits eq                                 19
% 11.88/1.99  fd_pure                                 0
% 11.88/1.99  fd_pseudo                               0
% 11.88/1.99  fd_cond                                 0
% 11.88/1.99  fd_pseudo_cond                          4
% 11.88/1.99  AC symbols                              1
% 11.88/1.99  
% 11.88/1.99  ------ Input Options Time Limit: Unbounded
% 11.88/1.99  
% 11.88/1.99  
% 11.88/1.99  ------ 
% 11.88/1.99  Current options:
% 11.88/1.99  ------ 
% 11.88/1.99  
% 11.88/1.99  
% 11.88/1.99  
% 11.88/1.99  
% 11.88/1.99  ------ Proving...
% 11.88/1.99  
% 11.88/1.99  
% 11.88/1.99  % SZS status Theorem for theBenchmark.p
% 11.88/1.99  
% 11.88/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.88/1.99  
% 11.88/1.99  fof(f1,axiom,(
% 11.88/1.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f38,plain,(
% 11.88/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f1])).
% 11.88/1.99  
% 11.88/1.99  fof(f20,conjecture,(
% 11.88/1.99    ! [X0,X1] : (k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1) => r2_hidden(X1,X0))),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f21,negated_conjecture,(
% 11.88/1.99    ~! [X0,X1] : (k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1) => r2_hidden(X1,X0))),
% 11.88/1.99    inference(negated_conjecture,[],[f20])).
% 11.88/1.99  
% 11.88/1.99  fof(f27,plain,(
% 11.88/1.99    ? [X0,X1] : (~r2_hidden(X1,X0) & k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1))),
% 11.88/1.99    inference(ennf_transformation,[],[f21])).
% 11.88/1.99  
% 11.88/1.99  fof(f36,plain,(
% 11.88/1.99    ? [X0,X1] : (~r2_hidden(X1,X0) & k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1)) => (~r2_hidden(sK3,sK2) & k3_xboole_0(sK2,k1_tarski(sK3)) = k1_tarski(sK3))),
% 11.88/1.99    introduced(choice_axiom,[])).
% 11.88/1.99  
% 11.88/1.99  fof(f37,plain,(
% 11.88/1.99    ~r2_hidden(sK3,sK2) & k3_xboole_0(sK2,k1_tarski(sK3)) = k1_tarski(sK3)),
% 11.88/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f27,f36])).
% 11.88/1.99  
% 11.88/1.99  fof(f69,plain,(
% 11.88/1.99    k3_xboole_0(sK2,k1_tarski(sK3)) = k1_tarski(sK3)),
% 11.88/1.99    inference(cnf_transformation,[],[f37])).
% 11.88/1.99  
% 11.88/1.99  fof(f9,axiom,(
% 11.88/1.99    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f51,plain,(
% 11.88/1.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f9])).
% 11.88/1.99  
% 11.88/1.99  fof(f18,axiom,(
% 11.88/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f67,plain,(
% 11.88/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.88/1.99    inference(cnf_transformation,[],[f18])).
% 11.88/1.99  
% 11.88/1.99  fof(f76,plain,(
% 11.88/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 11.88/1.99    inference(definition_unfolding,[],[f67,f75])).
% 11.88/1.99  
% 11.88/1.99  fof(f77,plain,(
% 11.88/1.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 11.88/1.99    inference(definition_unfolding,[],[f51,f76])).
% 11.88/1.99  
% 11.88/1.99  fof(f11,axiom,(
% 11.88/1.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f60,plain,(
% 11.88/1.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f11])).
% 11.88/1.99  
% 11.88/1.99  fof(f12,axiom,(
% 11.88/1.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f61,plain,(
% 11.88/1.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f12])).
% 11.88/1.99  
% 11.88/1.99  fof(f13,axiom,(
% 11.88/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f62,plain,(
% 11.88/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f13])).
% 11.88/1.99  
% 11.88/1.99  fof(f14,axiom,(
% 11.88/1.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f63,plain,(
% 11.88/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f14])).
% 11.88/1.99  
% 11.88/1.99  fof(f15,axiom,(
% 11.88/1.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f64,plain,(
% 11.88/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f15])).
% 11.88/1.99  
% 11.88/1.99  fof(f16,axiom,(
% 11.88/1.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f65,plain,(
% 11.88/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f16])).
% 11.88/1.99  
% 11.88/1.99  fof(f17,axiom,(
% 11.88/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f66,plain,(
% 11.88/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f17])).
% 11.88/1.99  
% 11.88/1.99  fof(f71,plain,(
% 11.88/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.88/1.99    inference(definition_unfolding,[],[f65,f66])).
% 11.88/1.99  
% 11.88/1.99  fof(f72,plain,(
% 11.88/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.88/1.99    inference(definition_unfolding,[],[f64,f71])).
% 11.88/1.99  
% 11.88/1.99  fof(f73,plain,(
% 11.88/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.88/1.99    inference(definition_unfolding,[],[f63,f72])).
% 11.88/1.99  
% 11.88/1.99  fof(f74,plain,(
% 11.88/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.88/1.99    inference(definition_unfolding,[],[f62,f73])).
% 11.88/1.99  
% 11.88/1.99  fof(f75,plain,(
% 11.88/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.88/1.99    inference(definition_unfolding,[],[f61,f74])).
% 11.88/1.99  
% 11.88/1.99  fof(f79,plain,(
% 11.88/1.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.88/1.99    inference(definition_unfolding,[],[f60,f75])).
% 11.88/1.99  
% 11.88/1.99  fof(f91,plain,(
% 11.88/1.99    k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),
% 11.88/1.99    inference(definition_unfolding,[],[f69,f77,f79,f79])).
% 11.88/1.99  
% 11.88/1.99  fof(f7,axiom,(
% 11.88/1.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f49,plain,(
% 11.88/1.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f7])).
% 11.88/1.99  
% 11.88/1.99  fof(f6,axiom,(
% 11.88/1.99    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f48,plain,(
% 11.88/1.99    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f6])).
% 11.88/1.99  
% 11.88/1.99  fof(f5,axiom,(
% 11.88/1.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f47,plain,(
% 11.88/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f5])).
% 11.88/1.99  
% 11.88/1.99  fof(f78,plain,(
% 11.88/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1)) )),
% 11.88/1.99    inference(definition_unfolding,[],[f47,f77])).
% 11.88/1.99  
% 11.88/1.99  fof(f81,plain,(
% 11.88/1.99    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X1)) )),
% 11.88/1.99    inference(definition_unfolding,[],[f48,f78])).
% 11.88/1.99  
% 11.88/1.99  fof(f4,axiom,(
% 11.88/1.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f23,plain,(
% 11.88/1.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.88/1.99    inference(rectify,[],[f4])).
% 11.88/1.99  
% 11.88/1.99  fof(f25,plain,(
% 11.88/1.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 11.88/1.99    inference(ennf_transformation,[],[f23])).
% 11.88/1.99  
% 11.88/1.99  fof(f29,plain,(
% 11.88/1.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.88/1.99    introduced(choice_axiom,[])).
% 11.88/1.99  
% 11.88/1.99  fof(f30,plain,(
% 11.88/1.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 11.88/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f29])).
% 11.88/1.99  
% 11.88/1.99  fof(f46,plain,(
% 11.88/1.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f30])).
% 11.88/1.99  
% 11.88/1.99  fof(f3,axiom,(
% 11.88/1.99    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f24,plain,(
% 11.88/1.99    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 11.88/1.99    inference(ennf_transformation,[],[f3])).
% 11.88/1.99  
% 11.88/1.99  fof(f28,plain,(
% 11.88/1.99    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 11.88/1.99    inference(nnf_transformation,[],[f24])).
% 11.88/1.99  
% 11.88/1.99  fof(f42,plain,(
% 11.88/1.99    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 11.88/1.99    inference(cnf_transformation,[],[f28])).
% 11.88/1.99  
% 11.88/1.99  fof(f10,axiom,(
% 11.88/1.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 11.88/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.88/1.99  
% 11.88/1.99  fof(f26,plain,(
% 11.88/1.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 11.88/1.99    inference(ennf_transformation,[],[f10])).
% 11.88/1.99  
% 11.88/1.99  fof(f31,plain,(
% 11.88/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.88/1.99    inference(nnf_transformation,[],[f26])).
% 11.88/1.99  
% 11.88/1.99  fof(f32,plain,(
% 11.88/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.88/1.99    inference(flattening,[],[f31])).
% 11.88/1.99  
% 11.88/1.99  fof(f33,plain,(
% 11.88/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.88/1.99    inference(rectify,[],[f32])).
% 11.88/1.99  
% 11.88/1.99  fof(f34,plain,(
% 11.88/1.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 11.88/1.99    introduced(choice_axiom,[])).
% 11.88/1.99  
% 11.88/1.99  fof(f35,plain,(
% 11.88/1.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 11.88/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 11.88/1.99  
% 11.88/1.99  fof(f53,plain,(
% 11.88/1.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 11.88/1.99    inference(cnf_transformation,[],[f35])).
% 11.88/1.99  
% 11.88/1.99  fof(f88,plain,(
% 11.88/1.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 11.88/1.99    inference(definition_unfolding,[],[f53,f74])).
% 11.88/1.99  
% 11.88/1.99  fof(f96,plain,(
% 11.88/1.99    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 11.88/1.99    inference(equality_resolution,[],[f88])).
% 11.88/1.99  
% 11.88/1.99  fof(f97,plain,(
% 11.88/1.99    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 11.88/1.99    inference(equality_resolution,[],[f96])).
% 11.88/1.99  
% 11.88/1.99  fof(f70,plain,(
% 11.88/1.99    ~r2_hidden(sK3,sK2)),
% 11.88/1.99    inference(cnf_transformation,[],[f37])).
% 11.88/1.99  
% 11.88/1.99  cnf(c_0,plain,
% 11.88/1.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 11.88/1.99      inference(cnf_transformation,[],[f38]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_22,negated_conjecture,
% 11.88/1.99      ( k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 11.88/1.99      inference(cnf_transformation,[],[f91]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_10,plain,
% 11.88/1.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.88/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_238,negated_conjecture,
% 11.88/1.99      ( k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 11.88/1.99      inference(theory_normalisation,[status(thm)],[c_22,c_10,c_0]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_931,plain,
% 11.88/1.99      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),X0)) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0) ),
% 11.88/1.99      inference(superposition,[status(thm)],[c_238,c_10]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_952,plain,
% 11.88/1.99      ( k5_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))) = k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0) ),
% 11.88/1.99      inference(superposition,[status(thm)],[c_0,c_931]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_9,plain,
% 11.88/1.99      ( r1_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X1) ),
% 11.88/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_239,plain,
% 11.88/1.99      ( r1_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))),X1) ),
% 11.88/1.99      inference(theory_normalisation,[status(thm)],[c_9,c_10,c_0]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_545,plain,
% 11.88/1.99      ( r1_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))),X1) = iProver_top ),
% 11.88/1.99      inference(predicate_to_equality,[status(thm)],[c_239]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_38471,plain,
% 11.88/1.99      ( r1_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 11.88/1.99      inference(superposition,[status(thm)],[c_952,c_545]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_6,plain,
% 11.88/1.99      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 11.88/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_1672,plain,
% 11.88/1.99      ( ~ r1_xboole_0(k5_xboole_0(X0,X1),X2)
% 11.88/1.99      | ~ r2_hidden(X3,X2)
% 11.88/1.99      | ~ r2_hidden(X3,k5_xboole_0(X0,X1)) ),
% 11.88/1.99      inference(instantiation,[status(thm)],[c_6]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_2457,plain,
% 11.88/1.99      ( ~ r1_xboole_0(k5_xboole_0(X0,sK2),X1)
% 11.88/1.99      | ~ r2_hidden(sK3,X1)
% 11.88/1.99      | ~ r2_hidden(sK3,k5_xboole_0(X0,sK2)) ),
% 11.88/1.99      inference(instantiation,[status(thm)],[c_1672]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_8286,plain,
% 11.88/1.99      ( ~ r1_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X0,X1),sK2),X2)
% 11.88/1.99      | ~ r2_hidden(sK3,X2)
% 11.88/1.99      | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X0,X1),sK2)) ),
% 11.88/1.99      inference(instantiation,[status(thm)],[c_2457]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_14608,plain,
% 11.88/1.99      ( ~ r1_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X0,X1),sK2),k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4))
% 11.88/1.99      | ~ r2_hidden(sK3,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4))
% 11.88/1.99      | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X0,X1),sK2)) ),
% 11.88/1.99      inference(instantiation,[status(thm)],[c_8286]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_14609,plain,
% 11.88/1.99      ( r1_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X0,X1),sK2),k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4)) != iProver_top
% 11.88/1.99      | r2_hidden(sK3,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4)) != iProver_top
% 11.88/1.99      | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X0,X1),sK2)) != iProver_top ),
% 11.88/1.99      inference(predicate_to_equality,[status(thm)],[c_14608]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_14611,plain,
% 11.88/1.99      ( r1_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top
% 11.88/1.99      | r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top
% 11.88/1.99      | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK2)) != iProver_top ),
% 11.88/1.99      inference(instantiation,[status(thm)],[c_14609]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_3,plain,
% 11.88/1.99      ( ~ r2_hidden(X0,X1)
% 11.88/1.99      | r2_hidden(X0,X2)
% 11.88/1.99      | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 11.88/1.99      inference(cnf_transformation,[],[f42]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_710,plain,
% 11.88/1.99      ( r2_hidden(X0,X1)
% 11.88/1.99      | ~ r2_hidden(X0,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X0))
% 11.88/1.99      | r2_hidden(X0,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X0),X1)) ),
% 11.88/1.99      inference(instantiation,[status(thm)],[c_3]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_896,plain,
% 11.88/1.99      ( ~ r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3))
% 11.88/1.99      | r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK2))
% 11.88/1.99      | r2_hidden(sK3,sK2) ),
% 11.88/1.99      inference(instantiation,[status(thm)],[c_710]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_897,plain,
% 11.88/1.99      ( r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3)) != iProver_top
% 11.88/1.99      | r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK2)) = iProver_top
% 11.88/1.99      | r2_hidden(sK3,sK2) = iProver_top ),
% 11.88/1.99      inference(predicate_to_equality,[status(thm)],[c_896]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_899,plain,
% 11.88/1.99      ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top
% 11.88/1.99      | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK2)) = iProver_top
% 11.88/1.99      | r2_hidden(sK3,sK2) = iProver_top ),
% 11.88/1.99      inference(instantiation,[status(thm)],[c_897]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_18,plain,
% 11.88/1.99      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 11.88/1.99      inference(cnf_transformation,[],[f97]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_28,plain,
% 11.88/1.99      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 11.88/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_30,plain,
% 11.88/1.99      ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 11.88/1.99      inference(instantiation,[status(thm)],[c_28]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_21,negated_conjecture,
% 11.88/1.99      ( ~ r2_hidden(sK3,sK2) ),
% 11.88/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(c_23,plain,
% 11.88/1.99      ( r2_hidden(sK3,sK2) != iProver_top ),
% 11.88/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.88/1.99  
% 11.88/1.99  cnf(contradiction,plain,
% 11.88/1.99      ( $false ),
% 11.88/1.99      inference(minisat,[status(thm)],[c_38471,c_14611,c_899,c_30,c_23]) ).
% 11.88/1.99  
% 11.88/1.99  
% 11.88/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.88/1.99  
% 11.88/1.99  ------                               Statistics
% 11.88/1.99  
% 11.88/1.99  ------ Selected
% 11.88/1.99  
% 11.88/1.99  total_time:                             1.338
% 11.88/1.99  
%------------------------------------------------------------------------------
