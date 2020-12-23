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
% DateTime   : Thu Dec  3 11:32:37 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  115 (2289 expanded)
%              Number of clauses        :   46 ( 241 expanded)
%              Number of leaves         :   20 ( 712 expanded)
%              Depth                    :   26
%              Number of atoms          :  390 (4228 expanded)
%              Number of equality atoms :  258 (3435 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f60,f73])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f59,f74])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f75])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f76])).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f68,f77])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f42,f78])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & sK4 != sK5
      & k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & sK4 != sK5
    & k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f21,f37])).

fof(f69,plain,(
    k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f77])).

fof(f101,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
    inference(definition_unfolding,[],[f69,f78,f79])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f87,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f47,f78])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f35])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f65,f79,f79])).

fof(f71,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f38])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f41,f78])).

fof(f102,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f83])).

fof(f70,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f20])).

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
    inference(flattening,[],[f29])).

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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f48,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f95,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f48,f76])).

fof(f111,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f95])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f44,f78])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f27])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_917,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_25,negated_conjecture,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_8,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_911,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1654,plain,
    ( r1_tarski(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_911])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_898,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1658,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1654,c_898])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_405,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1201,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_405])).

cnf(c_406,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1079,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_406])).

cnf(c_1228,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1079])).

cnf(c_1798,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1658,c_23,c_1201,c_1228])).

cnf(c_1803,plain,
    ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK4 ),
    inference(demodulation,[status(thm)],[c_1798,c_25])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_916,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2081,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1803,c_916])).

cnf(c_5184,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = sK5
    | r2_hidden(sK0(X0,X1,sK5),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,sK5),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_917,c_2081])).

cnf(c_6435,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) = sK5
    | r2_hidden(sK0(X0,sK5,sK5),X0) = iProver_top
    | r2_hidden(sK0(X0,sK5,sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5184,c_2081])).

cnf(c_6581,plain,
    ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK5
    | r2_hidden(sK0(sK4,sK5,sK5),sK4) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_6435])).

cnf(c_6583,plain,
    ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK5
    | r2_hidden(sK0(sK4,sK5,sK5),sK4) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6581])).

cnf(c_6586,plain,
    ( sK4 = sK5
    | r2_hidden(sK0(sK4,sK5,sK5),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6583,c_1803])).

cnf(c_24,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_6765,plain,
    ( r2_hidden(sK0(sK4,sK5,sK5),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6586,c_24])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_903,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3158,plain,
    ( sK3 = X0
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1798,c_903])).

cnf(c_6770,plain,
    ( sK0(sK4,sK5,sK5) = sK3 ),
    inference(superposition,[status(thm)],[c_6765,c_3158])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_919,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6776,plain,
    ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK5
    | r2_hidden(sK0(sK4,sK5,sK5),sK5) != iProver_top
    | r2_hidden(sK3,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6770,c_919])).

cnf(c_6799,plain,
    ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK5
    | r2_hidden(sK3,sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6776,c_6770])).

cnf(c_6800,plain,
    ( sK4 = sK5
    | r2_hidden(sK3,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6799,c_1803])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_913,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2094,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK1(sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_913,c_2081])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1078,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_406])).

cnf(c_1200,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1078])).

cnf(c_2385,plain,
    ( r2_hidden(sK1(sK5),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2094,c_22,c_1200,c_1201])).

cnf(c_3824,plain,
    ( sK1(sK5) = sK3 ),
    inference(superposition,[status(thm)],[c_2385,c_3158])).

cnf(c_3993,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3824,c_913])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6800,c_3993,c_1201,c_1200,c_22,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:35:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.98/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.01  
% 2.98/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.98/1.01  
% 2.98/1.01  ------  iProver source info
% 2.98/1.01  
% 2.98/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.98/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.98/1.01  git: non_committed_changes: false
% 2.98/1.01  git: last_make_outside_of_git: false
% 2.98/1.01  
% 2.98/1.01  ------ 
% 2.98/1.01  
% 2.98/1.01  ------ Input Options
% 2.98/1.01  
% 2.98/1.01  --out_options                           all
% 2.98/1.01  --tptp_safe_out                         true
% 2.98/1.01  --problem_path                          ""
% 2.98/1.01  --include_path                          ""
% 2.98/1.01  --clausifier                            res/vclausify_rel
% 2.98/1.01  --clausifier_options                    --mode clausify
% 2.98/1.01  --stdin                                 false
% 2.98/1.01  --stats_out                             all
% 2.98/1.01  
% 2.98/1.01  ------ General Options
% 2.98/1.01  
% 2.98/1.01  --fof                                   false
% 2.98/1.01  --time_out_real                         305.
% 2.98/1.01  --time_out_virtual                      -1.
% 2.98/1.01  --symbol_type_check                     false
% 2.98/1.01  --clausify_out                          false
% 2.98/1.01  --sig_cnt_out                           false
% 2.98/1.01  --trig_cnt_out                          false
% 2.98/1.01  --trig_cnt_out_tolerance                1.
% 2.98/1.01  --trig_cnt_out_sk_spl                   false
% 2.98/1.01  --abstr_cl_out                          false
% 2.98/1.01  
% 2.98/1.01  ------ Global Options
% 2.98/1.01  
% 2.98/1.01  --schedule                              default
% 2.98/1.01  --add_important_lit                     false
% 2.98/1.01  --prop_solver_per_cl                    1000
% 2.98/1.01  --min_unsat_core                        false
% 2.98/1.01  --soft_assumptions                      false
% 2.98/1.01  --soft_lemma_size                       3
% 2.98/1.01  --prop_impl_unit_size                   0
% 2.98/1.01  --prop_impl_unit                        []
% 2.98/1.01  --share_sel_clauses                     true
% 2.98/1.01  --reset_solvers                         false
% 2.98/1.01  --bc_imp_inh                            [conj_cone]
% 2.98/1.01  --conj_cone_tolerance                   3.
% 2.98/1.01  --extra_neg_conj                        none
% 2.98/1.01  --large_theory_mode                     true
% 2.98/1.01  --prolific_symb_bound                   200
% 2.98/1.01  --lt_threshold                          2000
% 2.98/1.01  --clause_weak_htbl                      true
% 2.98/1.01  --gc_record_bc_elim                     false
% 2.98/1.01  
% 2.98/1.01  ------ Preprocessing Options
% 2.98/1.01  
% 2.98/1.01  --preprocessing_flag                    true
% 2.98/1.01  --time_out_prep_mult                    0.1
% 2.98/1.01  --splitting_mode                        input
% 2.98/1.01  --splitting_grd                         true
% 2.98/1.01  --splitting_cvd                         false
% 2.98/1.01  --splitting_cvd_svl                     false
% 2.98/1.01  --splitting_nvd                         32
% 2.98/1.01  --sub_typing                            true
% 2.98/1.01  --prep_gs_sim                           true
% 2.98/1.01  --prep_unflatten                        true
% 2.98/1.01  --prep_res_sim                          true
% 2.98/1.01  --prep_upred                            true
% 2.98/1.01  --prep_sem_filter                       exhaustive
% 2.98/1.01  --prep_sem_filter_out                   false
% 2.98/1.01  --pred_elim                             true
% 2.98/1.01  --res_sim_input                         true
% 2.98/1.01  --eq_ax_congr_red                       true
% 2.98/1.01  --pure_diseq_elim                       true
% 2.98/1.01  --brand_transform                       false
% 2.98/1.01  --non_eq_to_eq                          false
% 2.98/1.01  --prep_def_merge                        true
% 2.98/1.01  --prep_def_merge_prop_impl              false
% 2.98/1.01  --prep_def_merge_mbd                    true
% 2.98/1.01  --prep_def_merge_tr_red                 false
% 2.98/1.01  --prep_def_merge_tr_cl                  false
% 2.98/1.01  --smt_preprocessing                     true
% 2.98/1.01  --smt_ac_axioms                         fast
% 2.98/1.01  --preprocessed_out                      false
% 2.98/1.01  --preprocessed_stats                    false
% 2.98/1.01  
% 2.98/1.01  ------ Abstraction refinement Options
% 2.98/1.01  
% 2.98/1.01  --abstr_ref                             []
% 2.98/1.01  --abstr_ref_prep                        false
% 2.98/1.01  --abstr_ref_until_sat                   false
% 2.98/1.01  --abstr_ref_sig_restrict                funpre
% 2.98/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/1.01  --abstr_ref_under                       []
% 2.98/1.01  
% 2.98/1.01  ------ SAT Options
% 2.98/1.01  
% 2.98/1.01  --sat_mode                              false
% 2.98/1.01  --sat_fm_restart_options                ""
% 2.98/1.01  --sat_gr_def                            false
% 2.98/1.01  --sat_epr_types                         true
% 2.98/1.01  --sat_non_cyclic_types                  false
% 2.98/1.01  --sat_finite_models                     false
% 2.98/1.01  --sat_fm_lemmas                         false
% 2.98/1.01  --sat_fm_prep                           false
% 2.98/1.01  --sat_fm_uc_incr                        true
% 2.98/1.01  --sat_out_model                         small
% 2.98/1.01  --sat_out_clauses                       false
% 2.98/1.01  
% 2.98/1.01  ------ QBF Options
% 2.98/1.01  
% 2.98/1.01  --qbf_mode                              false
% 2.98/1.01  --qbf_elim_univ                         false
% 2.98/1.01  --qbf_dom_inst                          none
% 2.98/1.01  --qbf_dom_pre_inst                      false
% 2.98/1.01  --qbf_sk_in                             false
% 2.98/1.01  --qbf_pred_elim                         true
% 2.98/1.01  --qbf_split                             512
% 2.98/1.01  
% 2.98/1.01  ------ BMC1 Options
% 2.98/1.01  
% 2.98/1.01  --bmc1_incremental                      false
% 2.98/1.01  --bmc1_axioms                           reachable_all
% 2.98/1.01  --bmc1_min_bound                        0
% 2.98/1.01  --bmc1_max_bound                        -1
% 2.98/1.01  --bmc1_max_bound_default                -1
% 2.98/1.01  --bmc1_symbol_reachability              true
% 2.98/1.01  --bmc1_property_lemmas                  false
% 2.98/1.01  --bmc1_k_induction                      false
% 2.98/1.01  --bmc1_non_equiv_states                 false
% 2.98/1.01  --bmc1_deadlock                         false
% 2.98/1.01  --bmc1_ucm                              false
% 2.98/1.01  --bmc1_add_unsat_core                   none
% 2.98/1.01  --bmc1_unsat_core_children              false
% 2.98/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/1.01  --bmc1_out_stat                         full
% 2.98/1.01  --bmc1_ground_init                      false
% 2.98/1.01  --bmc1_pre_inst_next_state              false
% 2.98/1.01  --bmc1_pre_inst_state                   false
% 2.98/1.01  --bmc1_pre_inst_reach_state             false
% 2.98/1.01  --bmc1_out_unsat_core                   false
% 2.98/1.01  --bmc1_aig_witness_out                  false
% 2.98/1.01  --bmc1_verbose                          false
% 2.98/1.01  --bmc1_dump_clauses_tptp                false
% 2.98/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.98/1.01  --bmc1_dump_file                        -
% 2.98/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.98/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.98/1.01  --bmc1_ucm_extend_mode                  1
% 2.98/1.01  --bmc1_ucm_init_mode                    2
% 2.98/1.01  --bmc1_ucm_cone_mode                    none
% 2.98/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.98/1.01  --bmc1_ucm_relax_model                  4
% 2.98/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.98/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/1.01  --bmc1_ucm_layered_model                none
% 2.98/1.01  --bmc1_ucm_max_lemma_size               10
% 2.98/1.01  
% 2.98/1.01  ------ AIG Options
% 2.98/1.01  
% 2.98/1.01  --aig_mode                              false
% 2.98/1.01  
% 2.98/1.01  ------ Instantiation Options
% 2.98/1.01  
% 2.98/1.01  --instantiation_flag                    true
% 2.98/1.01  --inst_sos_flag                         false
% 2.98/1.01  --inst_sos_phase                        true
% 2.98/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/1.01  --inst_lit_sel_side                     num_symb
% 2.98/1.01  --inst_solver_per_active                1400
% 2.98/1.01  --inst_solver_calls_frac                1.
% 2.98/1.01  --inst_passive_queue_type               priority_queues
% 2.98/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/1.01  --inst_passive_queues_freq              [25;2]
% 2.98/1.01  --inst_dismatching                      true
% 2.98/1.01  --inst_eager_unprocessed_to_passive     true
% 2.98/1.01  --inst_prop_sim_given                   true
% 2.98/1.01  --inst_prop_sim_new                     false
% 2.98/1.01  --inst_subs_new                         false
% 2.98/1.01  --inst_eq_res_simp                      false
% 2.98/1.01  --inst_subs_given                       false
% 2.98/1.01  --inst_orphan_elimination               true
% 2.98/1.01  --inst_learning_loop_flag               true
% 2.98/1.01  --inst_learning_start                   3000
% 2.98/1.01  --inst_learning_factor                  2
% 2.98/1.01  --inst_start_prop_sim_after_learn       3
% 2.98/1.01  --inst_sel_renew                        solver
% 2.98/1.01  --inst_lit_activity_flag                true
% 2.98/1.01  --inst_restr_to_given                   false
% 2.98/1.01  --inst_activity_threshold               500
% 2.98/1.01  --inst_out_proof                        true
% 2.98/1.01  
% 2.98/1.01  ------ Resolution Options
% 2.98/1.01  
% 2.98/1.01  --resolution_flag                       true
% 2.98/1.01  --res_lit_sel                           adaptive
% 2.98/1.01  --res_lit_sel_side                      none
% 2.98/1.01  --res_ordering                          kbo
% 2.98/1.01  --res_to_prop_solver                    active
% 2.98/1.01  --res_prop_simpl_new                    false
% 2.98/1.01  --res_prop_simpl_given                  true
% 2.98/1.01  --res_passive_queue_type                priority_queues
% 2.98/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/1.01  --res_passive_queues_freq               [15;5]
% 2.98/1.01  --res_forward_subs                      full
% 2.98/1.01  --res_backward_subs                     full
% 2.98/1.01  --res_forward_subs_resolution           true
% 2.98/1.01  --res_backward_subs_resolution          true
% 2.98/1.01  --res_orphan_elimination                true
% 2.98/1.01  --res_time_limit                        2.
% 2.98/1.01  --res_out_proof                         true
% 2.98/1.01  
% 2.98/1.01  ------ Superposition Options
% 2.98/1.01  
% 2.98/1.01  --superposition_flag                    true
% 2.98/1.01  --sup_passive_queue_type                priority_queues
% 2.98/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.98/1.01  --demod_completeness_check              fast
% 2.98/1.01  --demod_use_ground                      true
% 2.98/1.01  --sup_to_prop_solver                    passive
% 2.98/1.01  --sup_prop_simpl_new                    true
% 2.98/1.01  --sup_prop_simpl_given                  true
% 2.98/1.01  --sup_fun_splitting                     false
% 2.98/1.01  --sup_smt_interval                      50000
% 2.98/1.01  
% 2.98/1.01  ------ Superposition Simplification Setup
% 2.98/1.01  
% 2.98/1.01  --sup_indices_passive                   []
% 2.98/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/1.01  --sup_full_bw                           [BwDemod]
% 2.98/1.01  --sup_immed_triv                        [TrivRules]
% 2.98/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/1.01  --sup_immed_bw_main                     []
% 2.98/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/1.01  
% 2.98/1.01  ------ Combination Options
% 2.98/1.01  
% 2.98/1.01  --comb_res_mult                         3
% 2.98/1.01  --comb_sup_mult                         2
% 2.98/1.01  --comb_inst_mult                        10
% 2.98/1.01  
% 2.98/1.01  ------ Debug Options
% 2.98/1.01  
% 2.98/1.01  --dbg_backtrace                         false
% 2.98/1.01  --dbg_dump_prop_clauses                 false
% 2.98/1.01  --dbg_dump_prop_clauses_file            -
% 2.98/1.01  --dbg_out_stat                          false
% 2.98/1.01  ------ Parsing...
% 2.98/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.98/1.01  
% 2.98/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.98/1.01  
% 2.98/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.98/1.01  
% 2.98/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.98/1.01  ------ Proving...
% 2.98/1.01  ------ Problem Properties 
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  clauses                                 26
% 2.98/1.01  conjectures                             4
% 2.98/1.01  EPR                                     3
% 2.98/1.01  Horn                                    20
% 2.98/1.01  unary                                   10
% 2.98/1.01  binary                                  6
% 2.98/1.01  lits                                    56
% 2.98/1.01  lits eq                                 24
% 2.98/1.01  fd_pure                                 0
% 2.98/1.01  fd_pseudo                               0
% 2.98/1.01  fd_cond                                 1
% 2.98/1.01  fd_pseudo_cond                          8
% 2.98/1.01  AC symbols                              0
% 2.98/1.01  
% 2.98/1.01  ------ Schedule dynamic 5 is on 
% 2.98/1.01  
% 2.98/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  ------ 
% 2.98/1.01  Current options:
% 2.98/1.01  ------ 
% 2.98/1.01  
% 2.98/1.01  ------ Input Options
% 2.98/1.01  
% 2.98/1.01  --out_options                           all
% 2.98/1.01  --tptp_safe_out                         true
% 2.98/1.01  --problem_path                          ""
% 2.98/1.01  --include_path                          ""
% 2.98/1.01  --clausifier                            res/vclausify_rel
% 2.98/1.01  --clausifier_options                    --mode clausify
% 2.98/1.01  --stdin                                 false
% 2.98/1.01  --stats_out                             all
% 2.98/1.01  
% 2.98/1.01  ------ General Options
% 2.98/1.01  
% 2.98/1.01  --fof                                   false
% 2.98/1.01  --time_out_real                         305.
% 2.98/1.01  --time_out_virtual                      -1.
% 2.98/1.01  --symbol_type_check                     false
% 2.98/1.01  --clausify_out                          false
% 2.98/1.01  --sig_cnt_out                           false
% 2.98/1.01  --trig_cnt_out                          false
% 2.98/1.01  --trig_cnt_out_tolerance                1.
% 2.98/1.01  --trig_cnt_out_sk_spl                   false
% 2.98/1.01  --abstr_cl_out                          false
% 2.98/1.01  
% 2.98/1.01  ------ Global Options
% 2.98/1.01  
% 2.98/1.01  --schedule                              default
% 2.98/1.01  --add_important_lit                     false
% 2.98/1.01  --prop_solver_per_cl                    1000
% 2.98/1.01  --min_unsat_core                        false
% 2.98/1.01  --soft_assumptions                      false
% 2.98/1.01  --soft_lemma_size                       3
% 2.98/1.01  --prop_impl_unit_size                   0
% 2.98/1.01  --prop_impl_unit                        []
% 2.98/1.01  --share_sel_clauses                     true
% 2.98/1.01  --reset_solvers                         false
% 2.98/1.01  --bc_imp_inh                            [conj_cone]
% 2.98/1.01  --conj_cone_tolerance                   3.
% 2.98/1.01  --extra_neg_conj                        none
% 2.98/1.01  --large_theory_mode                     true
% 2.98/1.01  --prolific_symb_bound                   200
% 2.98/1.01  --lt_threshold                          2000
% 2.98/1.01  --clause_weak_htbl                      true
% 2.98/1.01  --gc_record_bc_elim                     false
% 2.98/1.01  
% 2.98/1.01  ------ Preprocessing Options
% 2.98/1.01  
% 2.98/1.01  --preprocessing_flag                    true
% 2.98/1.01  --time_out_prep_mult                    0.1
% 2.98/1.01  --splitting_mode                        input
% 2.98/1.01  --splitting_grd                         true
% 2.98/1.01  --splitting_cvd                         false
% 2.98/1.01  --splitting_cvd_svl                     false
% 2.98/1.01  --splitting_nvd                         32
% 2.98/1.01  --sub_typing                            true
% 2.98/1.01  --prep_gs_sim                           true
% 2.98/1.01  --prep_unflatten                        true
% 2.98/1.01  --prep_res_sim                          true
% 2.98/1.01  --prep_upred                            true
% 2.98/1.01  --prep_sem_filter                       exhaustive
% 2.98/1.01  --prep_sem_filter_out                   false
% 2.98/1.01  --pred_elim                             true
% 2.98/1.01  --res_sim_input                         true
% 2.98/1.01  --eq_ax_congr_red                       true
% 2.98/1.01  --pure_diseq_elim                       true
% 2.98/1.01  --brand_transform                       false
% 2.98/1.01  --non_eq_to_eq                          false
% 2.98/1.01  --prep_def_merge                        true
% 2.98/1.01  --prep_def_merge_prop_impl              false
% 2.98/1.01  --prep_def_merge_mbd                    true
% 2.98/1.01  --prep_def_merge_tr_red                 false
% 2.98/1.01  --prep_def_merge_tr_cl                  false
% 2.98/1.01  --smt_preprocessing                     true
% 2.98/1.01  --smt_ac_axioms                         fast
% 2.98/1.01  --preprocessed_out                      false
% 2.98/1.01  --preprocessed_stats                    false
% 2.98/1.01  
% 2.98/1.01  ------ Abstraction refinement Options
% 2.98/1.01  
% 2.98/1.01  --abstr_ref                             []
% 2.98/1.01  --abstr_ref_prep                        false
% 2.98/1.01  --abstr_ref_until_sat                   false
% 2.98/1.01  --abstr_ref_sig_restrict                funpre
% 2.98/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/1.01  --abstr_ref_under                       []
% 2.98/1.01  
% 2.98/1.01  ------ SAT Options
% 2.98/1.01  
% 2.98/1.01  --sat_mode                              false
% 2.98/1.01  --sat_fm_restart_options                ""
% 2.98/1.01  --sat_gr_def                            false
% 2.98/1.01  --sat_epr_types                         true
% 2.98/1.01  --sat_non_cyclic_types                  false
% 2.98/1.01  --sat_finite_models                     false
% 2.98/1.01  --sat_fm_lemmas                         false
% 2.98/1.01  --sat_fm_prep                           false
% 2.98/1.01  --sat_fm_uc_incr                        true
% 2.98/1.01  --sat_out_model                         small
% 2.98/1.01  --sat_out_clauses                       false
% 2.98/1.01  
% 2.98/1.01  ------ QBF Options
% 2.98/1.01  
% 2.98/1.01  --qbf_mode                              false
% 2.98/1.01  --qbf_elim_univ                         false
% 2.98/1.01  --qbf_dom_inst                          none
% 2.98/1.01  --qbf_dom_pre_inst                      false
% 2.98/1.01  --qbf_sk_in                             false
% 2.98/1.01  --qbf_pred_elim                         true
% 2.98/1.01  --qbf_split                             512
% 2.98/1.01  
% 2.98/1.01  ------ BMC1 Options
% 2.98/1.01  
% 2.98/1.01  --bmc1_incremental                      false
% 2.98/1.01  --bmc1_axioms                           reachable_all
% 2.98/1.01  --bmc1_min_bound                        0
% 2.98/1.01  --bmc1_max_bound                        -1
% 2.98/1.01  --bmc1_max_bound_default                -1
% 2.98/1.01  --bmc1_symbol_reachability              true
% 2.98/1.01  --bmc1_property_lemmas                  false
% 2.98/1.01  --bmc1_k_induction                      false
% 2.98/1.01  --bmc1_non_equiv_states                 false
% 2.98/1.01  --bmc1_deadlock                         false
% 2.98/1.01  --bmc1_ucm                              false
% 2.98/1.01  --bmc1_add_unsat_core                   none
% 2.98/1.01  --bmc1_unsat_core_children              false
% 2.98/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/1.01  --bmc1_out_stat                         full
% 2.98/1.01  --bmc1_ground_init                      false
% 2.98/1.01  --bmc1_pre_inst_next_state              false
% 2.98/1.01  --bmc1_pre_inst_state                   false
% 2.98/1.01  --bmc1_pre_inst_reach_state             false
% 2.98/1.01  --bmc1_out_unsat_core                   false
% 2.98/1.01  --bmc1_aig_witness_out                  false
% 2.98/1.01  --bmc1_verbose                          false
% 2.98/1.01  --bmc1_dump_clauses_tptp                false
% 2.98/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.98/1.01  --bmc1_dump_file                        -
% 2.98/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.98/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.98/1.01  --bmc1_ucm_extend_mode                  1
% 2.98/1.01  --bmc1_ucm_init_mode                    2
% 2.98/1.01  --bmc1_ucm_cone_mode                    none
% 2.98/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.98/1.01  --bmc1_ucm_relax_model                  4
% 2.98/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.98/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/1.01  --bmc1_ucm_layered_model                none
% 2.98/1.01  --bmc1_ucm_max_lemma_size               10
% 2.98/1.01  
% 2.98/1.01  ------ AIG Options
% 2.98/1.01  
% 2.98/1.01  --aig_mode                              false
% 2.98/1.01  
% 2.98/1.01  ------ Instantiation Options
% 2.98/1.01  
% 2.98/1.01  --instantiation_flag                    true
% 2.98/1.01  --inst_sos_flag                         false
% 2.98/1.01  --inst_sos_phase                        true
% 2.98/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/1.01  --inst_lit_sel_side                     none
% 2.98/1.01  --inst_solver_per_active                1400
% 2.98/1.01  --inst_solver_calls_frac                1.
% 2.98/1.01  --inst_passive_queue_type               priority_queues
% 2.98/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/1.01  --inst_passive_queues_freq              [25;2]
% 2.98/1.01  --inst_dismatching                      true
% 2.98/1.01  --inst_eager_unprocessed_to_passive     true
% 2.98/1.01  --inst_prop_sim_given                   true
% 2.98/1.01  --inst_prop_sim_new                     false
% 2.98/1.01  --inst_subs_new                         false
% 2.98/1.01  --inst_eq_res_simp                      false
% 2.98/1.01  --inst_subs_given                       false
% 2.98/1.01  --inst_orphan_elimination               true
% 2.98/1.01  --inst_learning_loop_flag               true
% 2.98/1.01  --inst_learning_start                   3000
% 2.98/1.01  --inst_learning_factor                  2
% 2.98/1.01  --inst_start_prop_sim_after_learn       3
% 2.98/1.01  --inst_sel_renew                        solver
% 2.98/1.01  --inst_lit_activity_flag                true
% 2.98/1.01  --inst_restr_to_given                   false
% 2.98/1.01  --inst_activity_threshold               500
% 2.98/1.01  --inst_out_proof                        true
% 2.98/1.01  
% 2.98/1.01  ------ Resolution Options
% 2.98/1.01  
% 2.98/1.01  --resolution_flag                       false
% 2.98/1.01  --res_lit_sel                           adaptive
% 2.98/1.01  --res_lit_sel_side                      none
% 2.98/1.01  --res_ordering                          kbo
% 2.98/1.01  --res_to_prop_solver                    active
% 2.98/1.01  --res_prop_simpl_new                    false
% 2.98/1.01  --res_prop_simpl_given                  true
% 2.98/1.01  --res_passive_queue_type                priority_queues
% 2.98/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/1.01  --res_passive_queues_freq               [15;5]
% 2.98/1.01  --res_forward_subs                      full
% 2.98/1.01  --res_backward_subs                     full
% 2.98/1.01  --res_forward_subs_resolution           true
% 2.98/1.01  --res_backward_subs_resolution          true
% 2.98/1.01  --res_orphan_elimination                true
% 2.98/1.01  --res_time_limit                        2.
% 2.98/1.01  --res_out_proof                         true
% 2.98/1.01  
% 2.98/1.01  ------ Superposition Options
% 2.98/1.01  
% 2.98/1.01  --superposition_flag                    true
% 2.98/1.01  --sup_passive_queue_type                priority_queues
% 2.98/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.98/1.01  --demod_completeness_check              fast
% 2.98/1.01  --demod_use_ground                      true
% 2.98/1.01  --sup_to_prop_solver                    passive
% 2.98/1.01  --sup_prop_simpl_new                    true
% 2.98/1.01  --sup_prop_simpl_given                  true
% 2.98/1.01  --sup_fun_splitting                     false
% 2.98/1.01  --sup_smt_interval                      50000
% 2.98/1.01  
% 2.98/1.01  ------ Superposition Simplification Setup
% 2.98/1.01  
% 2.98/1.01  --sup_indices_passive                   []
% 2.98/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/1.01  --sup_full_bw                           [BwDemod]
% 2.98/1.01  --sup_immed_triv                        [TrivRules]
% 2.98/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/1.01  --sup_immed_bw_main                     []
% 2.98/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/1.01  
% 2.98/1.01  ------ Combination Options
% 2.98/1.01  
% 2.98/1.01  --comb_res_mult                         3
% 2.98/1.01  --comb_sup_mult                         2
% 2.98/1.01  --comb_inst_mult                        10
% 2.98/1.01  
% 2.98/1.01  ------ Debug Options
% 2.98/1.01  
% 2.98/1.01  --dbg_backtrace                         false
% 2.98/1.01  --dbg_dump_prop_clauses                 false
% 2.98/1.01  --dbg_dump_prop_clauses_file            -
% 2.98/1.01  --dbg_out_stat                          false
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  ------ Proving...
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  % SZS status Theorem for theBenchmark.p
% 2.98/1.01  
% 2.98/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.98/1.01  
% 2.98/1.01  fof(f1,axiom,(
% 2.98/1.01    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f22,plain,(
% 2.98/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.98/1.01    inference(nnf_transformation,[],[f1])).
% 2.98/1.01  
% 2.98/1.01  fof(f23,plain,(
% 2.98/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.98/1.01    inference(flattening,[],[f22])).
% 2.98/1.01  
% 2.98/1.01  fof(f24,plain,(
% 2.98/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.98/1.01    inference(rectify,[],[f23])).
% 2.98/1.01  
% 2.98/1.01  fof(f25,plain,(
% 2.98/1.01    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.98/1.01    introduced(choice_axiom,[])).
% 2.98/1.01  
% 2.98/1.01  fof(f26,plain,(
% 2.98/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.98/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 2.98/1.01  
% 2.98/1.01  fof(f42,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f26])).
% 2.98/1.01  
% 2.98/1.01  fof(f15,axiom,(
% 2.98/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f68,plain,(
% 2.98/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.98/1.01    inference(cnf_transformation,[],[f15])).
% 2.98/1.01  
% 2.98/1.01  fof(f7,axiom,(
% 2.98/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f57,plain,(
% 2.98/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f7])).
% 2.98/1.01  
% 2.98/1.01  fof(f8,axiom,(
% 2.98/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f58,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f8])).
% 2.98/1.01  
% 2.98/1.01  fof(f9,axiom,(
% 2.98/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f59,plain,(
% 2.98/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f9])).
% 2.98/1.01  
% 2.98/1.01  fof(f10,axiom,(
% 2.98/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f60,plain,(
% 2.98/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f10])).
% 2.98/1.01  
% 2.98/1.01  fof(f11,axiom,(
% 2.98/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f61,plain,(
% 2.98/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f11])).
% 2.98/1.01  
% 2.98/1.01  fof(f12,axiom,(
% 2.98/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f62,plain,(
% 2.98/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f12])).
% 2.98/1.01  
% 2.98/1.01  fof(f73,plain,(
% 2.98/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.98/1.01    inference(definition_unfolding,[],[f61,f62])).
% 2.98/1.01  
% 2.98/1.01  fof(f74,plain,(
% 2.98/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.98/1.01    inference(definition_unfolding,[],[f60,f73])).
% 2.98/1.01  
% 2.98/1.01  fof(f75,plain,(
% 2.98/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.98/1.01    inference(definition_unfolding,[],[f59,f74])).
% 2.98/1.01  
% 2.98/1.01  fof(f76,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.98/1.01    inference(definition_unfolding,[],[f58,f75])).
% 2.98/1.01  
% 2.98/1.01  fof(f77,plain,(
% 2.98/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.98/1.01    inference(definition_unfolding,[],[f57,f76])).
% 2.98/1.01  
% 2.98/1.01  fof(f78,plain,(
% 2.98/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.98/1.01    inference(definition_unfolding,[],[f68,f77])).
% 2.98/1.01  
% 2.98/1.01  fof(f82,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.98/1.01    inference(definition_unfolding,[],[f42,f78])).
% 2.98/1.01  
% 2.98/1.01  fof(f16,conjecture,(
% 2.98/1.01    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f17,negated_conjecture,(
% 2.98/1.01    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.98/1.01    inference(negated_conjecture,[],[f16])).
% 2.98/1.01  
% 2.98/1.01  fof(f21,plain,(
% 2.98/1.01    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.98/1.01    inference(ennf_transformation,[],[f17])).
% 2.98/1.01  
% 2.98/1.01  fof(f37,plain,(
% 2.98/1.01    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0)) => (k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & sK4 != sK5 & k2_xboole_0(sK4,sK5) = k1_tarski(sK3))),
% 2.98/1.01    introduced(choice_axiom,[])).
% 2.98/1.01  
% 2.98/1.01  fof(f38,plain,(
% 2.98/1.01    k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & sK4 != sK5 & k2_xboole_0(sK4,sK5) = k1_tarski(sK3)),
% 2.98/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f21,f37])).
% 2.98/1.01  
% 2.98/1.01  fof(f69,plain,(
% 2.98/1.01    k2_xboole_0(sK4,sK5) = k1_tarski(sK3)),
% 2.98/1.01    inference(cnf_transformation,[],[f38])).
% 2.98/1.01  
% 2.98/1.01  fof(f6,axiom,(
% 2.98/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f56,plain,(
% 2.98/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f6])).
% 2.98/1.01  
% 2.98/1.01  fof(f79,plain,(
% 2.98/1.01    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.98/1.01    inference(definition_unfolding,[],[f56,f77])).
% 2.98/1.01  
% 2.98/1.01  fof(f101,plain,(
% 2.98/1.01    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),
% 2.98/1.01    inference(definition_unfolding,[],[f69,f78,f79])).
% 2.98/1.01  
% 2.98/1.01  fof(f4,axiom,(
% 2.98/1.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f47,plain,(
% 2.98/1.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.98/1.01    inference(cnf_transformation,[],[f4])).
% 2.98/1.01  
% 2.98/1.01  fof(f87,plain,(
% 2.98/1.01    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.98/1.01    inference(definition_unfolding,[],[f47,f78])).
% 2.98/1.01  
% 2.98/1.01  fof(f14,axiom,(
% 2.98/1.01    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f35,plain,(
% 2.98/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.98/1.01    inference(nnf_transformation,[],[f14])).
% 2.98/1.01  
% 2.98/1.01  fof(f36,plain,(
% 2.98/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.98/1.01    inference(flattening,[],[f35])).
% 2.98/1.01  
% 2.98/1.01  fof(f65,plain,(
% 2.98/1.01    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.98/1.01    inference(cnf_transformation,[],[f36])).
% 2.98/1.01  
% 2.98/1.01  fof(f100,plain,(
% 2.98/1.01    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 2.98/1.01    inference(definition_unfolding,[],[f65,f79,f79])).
% 2.98/1.01  
% 2.98/1.01  fof(f71,plain,(
% 2.98/1.01    k1_xboole_0 != sK4),
% 2.98/1.01    inference(cnf_transformation,[],[f38])).
% 2.98/1.01  
% 2.98/1.01  fof(f41,plain,(
% 2.98/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.98/1.01    inference(cnf_transformation,[],[f26])).
% 2.98/1.01  
% 2.98/1.01  fof(f83,plain,(
% 2.98/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.98/1.01    inference(definition_unfolding,[],[f41,f78])).
% 2.98/1.01  
% 2.98/1.01  fof(f102,plain,(
% 2.98/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.98/1.01    inference(equality_resolution,[],[f83])).
% 2.98/1.01  
% 2.98/1.01  fof(f70,plain,(
% 2.98/1.01    sK4 != sK5),
% 2.98/1.01    inference(cnf_transformation,[],[f38])).
% 2.98/1.01  
% 2.98/1.01  fof(f5,axiom,(
% 2.98/1.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f20,plain,(
% 2.98/1.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.98/1.01    inference(ennf_transformation,[],[f5])).
% 2.98/1.01  
% 2.98/1.01  fof(f29,plain,(
% 2.98/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.98/1.01    inference(nnf_transformation,[],[f20])).
% 2.98/1.01  
% 2.98/1.01  fof(f30,plain,(
% 2.98/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.98/1.01    inference(flattening,[],[f29])).
% 2.98/1.01  
% 2.98/1.01  fof(f31,plain,(
% 2.98/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.98/1.01    inference(rectify,[],[f30])).
% 2.98/1.01  
% 2.98/1.01  fof(f32,plain,(
% 2.98/1.01    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 2.98/1.01    introduced(choice_axiom,[])).
% 2.98/1.01  
% 2.98/1.01  fof(f33,plain,(
% 2.98/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.98/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 2.98/1.01  
% 2.98/1.01  fof(f48,plain,(
% 2.98/1.01    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.98/1.01    inference(cnf_transformation,[],[f33])).
% 2.98/1.01  
% 2.98/1.01  fof(f95,plain,(
% 2.98/1.01    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.98/1.01    inference(definition_unfolding,[],[f48,f76])).
% 2.98/1.01  
% 2.98/1.01  fof(f111,plain,(
% 2.98/1.01    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 2.98/1.01    inference(equality_resolution,[],[f95])).
% 2.98/1.01  
% 2.98/1.01  fof(f44,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f26])).
% 2.98/1.01  
% 2.98/1.01  fof(f80,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.98/1.01    inference(definition_unfolding,[],[f44,f78])).
% 2.98/1.01  
% 2.98/1.01  fof(f2,axiom,(
% 2.98/1.01    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f18,plain,(
% 2.98/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.98/1.01    inference(ennf_transformation,[],[f2])).
% 2.98/1.01  
% 2.98/1.01  fof(f27,plain,(
% 2.98/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 2.98/1.01    introduced(choice_axiom,[])).
% 2.98/1.01  
% 2.98/1.01  fof(f28,plain,(
% 2.98/1.01    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 2.98/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f27])).
% 2.98/1.01  
% 2.98/1.01  fof(f45,plain,(
% 2.98/1.01    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.98/1.01    inference(cnf_transformation,[],[f28])).
% 2.98/1.01  
% 2.98/1.01  fof(f72,plain,(
% 2.98/1.01    k1_xboole_0 != sK5),
% 2.98/1.01    inference(cnf_transformation,[],[f38])).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2,plain,
% 2.98/1.01      ( r2_hidden(sK0(X0,X1,X2),X1)
% 2.98/1.01      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.98/1.01      | r2_hidden(sK0(X0,X1,X2),X0)
% 2.98/1.01      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2 ),
% 2.98/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_917,plain,
% 2.98/1.01      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2
% 2.98/1.01      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
% 2.98/1.01      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 2.98/1.01      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_25,negated_conjecture,
% 2.98/1.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
% 2.98/1.01      inference(cnf_transformation,[],[f101]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_8,plain,
% 2.98/1.01      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 2.98/1.01      inference(cnf_transformation,[],[f87]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_911,plain,
% 2.98/1.01      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1654,plain,
% 2.98/1.01      ( r1_tarski(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_25,c_911]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_21,plain,
% 2.98/1.01      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 2.98/1.01      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 2.98/1.01      | k1_xboole_0 = X0 ),
% 2.98/1.01      inference(cnf_transformation,[],[f100]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_898,plain,
% 2.98/1.01      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 2.98/1.01      | k1_xboole_0 = X1
% 2.98/1.01      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1658,plain,
% 2.98/1.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4
% 2.98/1.01      | sK4 = k1_xboole_0 ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_1654,c_898]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_23,negated_conjecture,
% 2.98/1.01      ( k1_xboole_0 != sK4 ),
% 2.98/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_405,plain,( X0 = X0 ),theory(equality) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1201,plain,
% 2.98/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_405]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_406,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1079,plain,
% 2.98/1.01      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_406]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1228,plain,
% 2.98/1.01      ( sK4 != k1_xboole_0
% 2.98/1.01      | k1_xboole_0 = sK4
% 2.98/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_1079]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1798,plain,
% 2.98/1.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4 ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_1658,c_23,c_1201,c_1228]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1803,plain,
% 2.98/1.01      ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK4 ),
% 2.98/1.01      inference(demodulation,[status(thm)],[c_1798,c_25]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3,plain,
% 2.98/1.01      ( ~ r2_hidden(X0,X1)
% 2.98/1.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 2.98/1.01      inference(cnf_transformation,[],[f102]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_916,plain,
% 2.98/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.98/1.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2081,plain,
% 2.98/1.01      ( r2_hidden(X0,sK4) = iProver_top
% 2.98/1.01      | r2_hidden(X0,sK5) != iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_1803,c_916]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_5184,plain,
% 2.98/1.01      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = sK5
% 2.98/1.01      | r2_hidden(sK0(X0,X1,sK5),X1) = iProver_top
% 2.98/1.01      | r2_hidden(sK0(X0,X1,sK5),X0) = iProver_top
% 2.98/1.01      | r2_hidden(sK0(X0,X1,sK5),sK4) = iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_917,c_2081]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_6435,plain,
% 2.98/1.01      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) = sK5
% 2.98/1.01      | r2_hidden(sK0(X0,sK5,sK5),X0) = iProver_top
% 2.98/1.01      | r2_hidden(sK0(X0,sK5,sK5),sK4) = iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_5184,c_2081]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_6581,plain,
% 2.98/1.01      ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK5
% 2.98/1.01      | r2_hidden(sK0(sK4,sK5,sK5),sK4) = iProver_top
% 2.98/1.01      | iProver_top != iProver_top ),
% 2.98/1.01      inference(equality_factoring,[status(thm)],[c_6435]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_6583,plain,
% 2.98/1.01      ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK5
% 2.98/1.01      | r2_hidden(sK0(sK4,sK5,sK5),sK4) = iProver_top ),
% 2.98/1.01      inference(equality_resolution_simp,[status(thm)],[c_6581]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_6586,plain,
% 2.98/1.01      ( sK4 = sK5 | r2_hidden(sK0(sK4,sK5,sK5),sK4) = iProver_top ),
% 2.98/1.01      inference(demodulation,[status(thm)],[c_6583,c_1803]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_24,negated_conjecture,
% 2.98/1.01      ( sK4 != sK5 ),
% 2.98/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_6765,plain,
% 2.98/1.01      ( r2_hidden(sK0(sK4,sK5,sK5),sK4) = iProver_top ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_6586,c_24]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_16,plain,
% 2.98/1.01      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
% 2.98/1.01      | X0 = X1
% 2.98/1.01      | X0 = X2
% 2.98/1.01      | X0 = X3 ),
% 2.98/1.01      inference(cnf_transformation,[],[f111]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_903,plain,
% 2.98/1.01      ( X0 = X1
% 2.98/1.01      | X0 = X2
% 2.98/1.01      | X0 = X3
% 2.98/1.01      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3158,plain,
% 2.98/1.01      ( sK3 = X0 | r2_hidden(X0,sK4) != iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_1798,c_903]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_6770,plain,
% 2.98/1.01      ( sK0(sK4,sK5,sK5) = sK3 ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_6765,c_3158]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_0,plain,
% 2.98/1.01      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 2.98/1.01      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 2.98/1.01      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2 ),
% 2.98/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_919,plain,
% 2.98/1.01      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2
% 2.98/1.01      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 2.98/1.01      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_6776,plain,
% 2.98/1.01      ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK5
% 2.98/1.01      | r2_hidden(sK0(sK4,sK5,sK5),sK5) != iProver_top
% 2.98/1.01      | r2_hidden(sK3,sK5) != iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_6770,c_919]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_6799,plain,
% 2.98/1.01      ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK5
% 2.98/1.01      | r2_hidden(sK3,sK5) != iProver_top ),
% 2.98/1.01      inference(light_normalisation,[status(thm)],[c_6776,c_6770]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_6800,plain,
% 2.98/1.01      ( sK4 = sK5 | r2_hidden(sK3,sK5) != iProver_top ),
% 2.98/1.01      inference(demodulation,[status(thm)],[c_6799,c_1803]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_6,plain,
% 2.98/1.01      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 2.98/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_913,plain,
% 2.98/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2094,plain,
% 2.98/1.01      ( sK5 = k1_xboole_0 | r2_hidden(sK1(sK5),sK4) = iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_913,c_2081]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_22,negated_conjecture,
% 2.98/1.01      ( k1_xboole_0 != sK5 ),
% 2.98/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1078,plain,
% 2.98/1.01      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_406]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1200,plain,
% 2.98/1.01      ( sK5 != k1_xboole_0
% 2.98/1.01      | k1_xboole_0 = sK5
% 2.98/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 2.98/1.01      inference(instantiation,[status(thm)],[c_1078]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2385,plain,
% 2.98/1.01      ( r2_hidden(sK1(sK5),sK4) = iProver_top ),
% 2.98/1.01      inference(global_propositional_subsumption,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_2094,c_22,c_1200,c_1201]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3824,plain,
% 2.98/1.01      ( sK1(sK5) = sK3 ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_2385,c_3158]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3993,plain,
% 2.98/1.01      ( sK5 = k1_xboole_0 | r2_hidden(sK3,sK5) = iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_3824,c_913]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(contradiction,plain,
% 2.98/1.01      ( $false ),
% 2.98/1.01      inference(minisat,
% 2.98/1.01                [status(thm)],
% 2.98/1.01                [c_6800,c_3993,c_1201,c_1200,c_22,c_24]) ).
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.98/1.01  
% 2.98/1.01  ------                               Statistics
% 2.98/1.01  
% 2.98/1.01  ------ General
% 2.98/1.01  
% 2.98/1.01  abstr_ref_over_cycles:                  0
% 2.98/1.01  abstr_ref_under_cycles:                 0
% 2.98/1.01  gc_basic_clause_elim:                   0
% 2.98/1.01  forced_gc_time:                         0
% 2.98/1.01  parsing_time:                           0.007
% 2.98/1.01  unif_index_cands_time:                  0.
% 2.98/1.01  unif_index_add_time:                    0.
% 2.98/1.01  orderings_time:                         0.
% 2.98/1.01  out_proof_time:                         0.011
% 2.98/1.01  total_time:                             0.227
% 2.98/1.01  num_of_symbols:                         39
% 2.98/1.01  num_of_terms:                           8183
% 2.98/1.01  
% 2.98/1.01  ------ Preprocessing
% 2.98/1.01  
% 2.98/1.01  num_of_splits:                          0
% 2.98/1.01  num_of_split_atoms:                     0
% 2.98/1.01  num_of_reused_defs:                     0
% 2.98/1.01  num_eq_ax_congr_red:                    16
% 2.98/1.01  num_of_sem_filtered_clauses:            1
% 2.98/1.01  num_of_subtypes:                        0
% 2.98/1.01  monotx_restored_types:                  0
% 2.98/1.01  sat_num_of_epr_types:                   0
% 2.98/1.01  sat_num_of_non_cyclic_types:            0
% 2.98/1.01  sat_guarded_non_collapsed_types:        0
% 2.98/1.01  num_pure_diseq_elim:                    0
% 2.98/1.01  simp_replaced_by:                       0
% 2.98/1.01  res_preprocessed:                       91
% 2.98/1.01  prep_upred:                             0
% 2.98/1.01  prep_unflattend:                        17
% 2.98/1.01  smt_new_axioms:                         0
% 2.98/1.01  pred_elim_cands:                        2
% 2.98/1.01  pred_elim:                              0
% 2.98/1.01  pred_elim_cl:                           0
% 2.98/1.01  pred_elim_cycles:                       1
% 2.98/1.01  merged_defs:                            6
% 2.98/1.01  merged_defs_ncl:                        0
% 2.98/1.01  bin_hyper_res:                          6
% 2.98/1.01  prep_cycles:                            3
% 2.98/1.01  pred_elim_time:                         0.001
% 2.98/1.01  splitting_time:                         0.
% 2.98/1.01  sem_filter_time:                        0.
% 2.98/1.01  monotx_time:                            0.
% 2.98/1.01  subtype_inf_time:                       0.
% 2.98/1.01  
% 2.98/1.01  ------ Problem properties
% 2.98/1.01  
% 2.98/1.01  clauses:                                26
% 2.98/1.01  conjectures:                            4
% 2.98/1.01  epr:                                    3
% 2.98/1.01  horn:                                   20
% 2.98/1.01  ground:                                 4
% 2.98/1.01  unary:                                  10
% 2.98/1.01  binary:                                 6
% 2.98/1.01  lits:                                   56
% 2.98/1.01  lits_eq:                                24
% 2.98/1.01  fd_pure:                                0
% 2.98/1.01  fd_pseudo:                              0
% 2.98/1.01  fd_cond:                                1
% 2.98/1.01  fd_pseudo_cond:                         8
% 2.98/1.01  ac_symbols:                             0
% 2.98/1.01  
% 2.98/1.01  ------ Propositional Solver
% 2.98/1.01  
% 2.98/1.01  prop_solver_calls:                      23
% 2.98/1.01  prop_fast_solver_calls:                 566
% 2.98/1.01  smt_solver_calls:                       0
% 2.98/1.01  smt_fast_solver_calls:                  0
% 2.98/1.01  prop_num_of_clauses:                    2575
% 2.98/1.01  prop_preprocess_simplified:             7343
% 2.98/1.01  prop_fo_subsumed:                       4
% 2.98/1.01  prop_solver_time:                       0.
% 2.98/1.01  smt_solver_time:                        0.
% 2.98/1.01  smt_fast_solver_time:                   0.
% 2.98/1.01  prop_fast_solver_time:                  0.
% 2.98/1.01  prop_unsat_core_time:                   0.
% 2.98/1.01  
% 2.98/1.01  ------ QBF
% 2.98/1.01  
% 2.98/1.01  qbf_q_res:                              0
% 2.98/1.01  qbf_num_tautologies:                    0
% 2.98/1.01  qbf_prep_cycles:                        0
% 2.98/1.01  
% 2.98/1.01  ------ BMC1
% 2.98/1.01  
% 2.98/1.01  bmc1_current_bound:                     -1
% 2.98/1.01  bmc1_last_solved_bound:                 -1
% 2.98/1.01  bmc1_unsat_core_size:                   -1
% 2.98/1.01  bmc1_unsat_core_parents_size:           -1
% 2.98/1.01  bmc1_merge_next_fun:                    0
% 2.98/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.98/1.01  
% 2.98/1.01  ------ Instantiation
% 2.98/1.01  
% 2.98/1.01  inst_num_of_clauses:                    731
% 2.98/1.01  inst_num_in_passive:                    317
% 2.98/1.01  inst_num_in_active:                     255
% 2.98/1.01  inst_num_in_unprocessed:                159
% 2.98/1.01  inst_num_of_loops:                      300
% 2.98/1.01  inst_num_of_learning_restarts:          0
% 2.98/1.01  inst_num_moves_active_passive:          43
% 2.98/1.01  inst_lit_activity:                      0
% 2.98/1.01  inst_lit_activity_moves:                0
% 2.98/1.01  inst_num_tautologies:                   0
% 2.98/1.01  inst_num_prop_implied:                  0
% 2.98/1.01  inst_num_existing_simplified:           0
% 2.98/1.01  inst_num_eq_res_simplified:             0
% 2.98/1.01  inst_num_child_elim:                    0
% 2.98/1.01  inst_num_of_dismatching_blockings:      476
% 2.98/1.01  inst_num_of_non_proper_insts:           878
% 2.98/1.01  inst_num_of_duplicates:                 0
% 2.98/1.01  inst_inst_num_from_inst_to_res:         0
% 2.98/1.01  inst_dismatching_checking_time:         0.
% 2.98/1.01  
% 2.98/1.01  ------ Resolution
% 2.98/1.01  
% 2.98/1.01  res_num_of_clauses:                     0
% 2.98/1.01  res_num_in_passive:                     0
% 2.98/1.01  res_num_in_active:                      0
% 2.98/1.01  res_num_of_loops:                       94
% 2.98/1.01  res_forward_subset_subsumed:            90
% 2.98/1.01  res_backward_subset_subsumed:           0
% 2.98/1.01  res_forward_subsumed:                   0
% 2.98/1.01  res_backward_subsumed:                  0
% 2.98/1.01  res_forward_subsumption_resolution:     0
% 2.98/1.01  res_backward_subsumption_resolution:    0
% 2.98/1.01  res_clause_to_clause_subsumption:       913
% 2.98/1.01  res_orphan_elimination:                 0
% 2.98/1.01  res_tautology_del:                      19
% 2.98/1.01  res_num_eq_res_simplified:              0
% 2.98/1.01  res_num_sel_changes:                    0
% 2.98/1.01  res_moves_from_active_to_pass:          0
% 2.98/1.01  
% 2.98/1.01  ------ Superposition
% 2.98/1.01  
% 2.98/1.01  sup_time_total:                         0.
% 2.98/1.01  sup_time_generating:                    0.
% 2.98/1.01  sup_time_sim_full:                      0.
% 2.98/1.01  sup_time_sim_immed:                     0.
% 2.98/1.01  
% 2.98/1.01  sup_num_of_clauses:                     137
% 2.98/1.01  sup_num_in_active:                      55
% 2.98/1.01  sup_num_in_passive:                     82
% 2.98/1.01  sup_num_of_loops:                       59
% 2.98/1.01  sup_fw_superposition:                   57
% 2.98/1.01  sup_bw_superposition:                   138
% 2.98/1.01  sup_immediate_simplified:               38
% 2.98/1.01  sup_given_eliminated:                   0
% 2.98/1.01  comparisons_done:                       0
% 2.98/1.01  comparisons_avoided:                    6
% 2.98/1.01  
% 2.98/1.01  ------ Simplifications
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  sim_fw_subset_subsumed:                 29
% 2.98/1.01  sim_bw_subset_subsumed:                 0
% 2.98/1.01  sim_fw_subsumed:                        12
% 2.98/1.01  sim_bw_subsumed:                        1
% 2.98/1.01  sim_fw_subsumption_res:                 0
% 2.98/1.01  sim_bw_subsumption_res:                 0
% 2.98/1.01  sim_tautology_del:                      21
% 2.98/1.01  sim_eq_tautology_del:                   5
% 2.98/1.01  sim_eq_res_simp:                        21
% 2.98/1.01  sim_fw_demodulated:                     7
% 2.98/1.01  sim_bw_demodulated:                     5
% 2.98/1.01  sim_light_normalised:                   4
% 2.98/1.01  sim_joinable_taut:                      0
% 2.98/1.01  sim_joinable_simp:                      0
% 2.98/1.01  sim_ac_normalised:                      0
% 2.98/1.01  sim_smt_subsumption:                    0
% 2.98/1.01  
%------------------------------------------------------------------------------
