%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:19 EST 2020

% Result     : Theorem 43.67s
% Output     : CNFRefutation 43.67s
% Verified   : 
% Statistics : Number of formulae       :  201 (12797 expanded)
%              Number of clauses        :  119 (1779 expanded)
%              Number of leaves         :   20 (3659 expanded)
%              Depth                    :   24
%              Number of atoms          :  721 (45588 expanded)
%              Number of equality atoms :  434 (31298 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f14])).

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
    inference(flattening,[],[f21])).

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
    inference(rectify,[],[f22])).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK1(X0,X1,X2,X3) = X2
      | sK1(X0,X1,X2,X3) = X1
      | sK1(X0,X1,X2,X3) = X0
      | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f50,f57])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f58])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
      | sK1(X0,X1,X2,X3) = X2
      | sK1(X0,X1,X2,X3) = X1
      | sK1(X0,X1,X2,X3) = X0
      | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ),
    inference(definition_unfolding,[],[f42,f60])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
      <=> ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <~> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ( ( X0 != X1
            & ~ r2_hidden(X1,X2) )
          | r2_hidden(X0,X2)
          | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) )
        & ( ( ( X0 = X1
              | r2_hidden(X1,X2) )
            & ~ r2_hidden(X0,X2) )
          | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) )
   => ( ( ( sK2 != sK3
          & ~ r2_hidden(sK3,sK4) )
        | r2_hidden(sK2,sK4)
        | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k1_tarski(sK2) )
      & ( ( ( sK2 = sK3
            | r2_hidden(sK3,sK4) )
          & ~ r2_hidden(sK2,sK4) )
        | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_tarski(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ( sK2 != sK3
        & ~ r2_hidden(sK3,sK4) )
      | r2_hidden(sK2,sK4)
      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k1_tarski(sK2) )
    & ( ( ( sK2 = sK3
          | r2_hidden(sK3,sK4) )
        & ~ r2_hidden(sK2,sK4) )
      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_tarski(sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f28])).

fof(f56,plain,
    ( sK2 != sK3
    | r2_hidden(sK2,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f60])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f61])).

fof(f77,plain,
    ( sK2 != sK3
    | r2_hidden(sK2,sK4)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f56,f37,f61,f62])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f53,plain,
    ( ~ r2_hidden(sK2,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,
    ( ~ r2_hidden(sK2,sK4)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f53,f37,f61,f62])).

fof(f38,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f38,f60])).

fof(f90,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f39,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f39,f60])).

fof(f88,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f75])).

fof(f89,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f88])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f67])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f31,f37])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f68])).

fof(f40,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f40,f60])).

fof(f86,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f74])).

fof(f87,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f86])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f33,f37])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK1(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
      | sK1(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) ) ),
    inference(definition_unfolding,[],[f43,f60])).

fof(f54,plain,
    ( sK2 = sK3
    | r2_hidden(sK3,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,
    ( sK2 = sK3
    | r2_hidden(sK3,sK4)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f54,f37,f61,f62])).

fof(f41,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f41,f60])).

fof(f84,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f73])).

fof(f85,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f84])).

fof(f55,plain,
    ( ~ r2_hidden(sK3,sK4)
    | r2_hidden(sK2,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,
    ( ~ r2_hidden(sK3,sK4)
    | r2_hidden(sK2,sK4)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f55,f37,f61,f62])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK1(X0,X1,X2,X3) != X2
      | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
      | sK1(X0,X1,X2,X3) != X2
      | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) ) ),
    inference(definition_unfolding,[],[f45,f60])).

cnf(c_10,plain,
    ( r2_hidden(sK1(X0,X1,X2,X3),X3)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
    | sK1(X0,X1,X2,X3) = X2
    | sK1(X0,X1,X2,X3) = X1
    | sK1(X0,X1,X2,X3) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_5323,plain,
    ( r2_hidden(sK1(X0,X1,X1,X2),X2)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X1) = X2
    | sK1(X0,X1,X1,X2) = X1
    | sK1(X0,X1,X1,X2) = X0 ),
    inference(factoring,[status(thm)],[c_10])).

cnf(c_154,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_153,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_913,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_154,c_153])).

cnf(c_16468,plain,
    ( r2_hidden(sK1(X0,X1,X1,X2),X2)
    | X2 = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X1)
    | sK1(X0,X1,X1,X2) = X1
    | sK1(X0,X1,X1,X2) = X0 ),
    inference(resolution,[status(thm)],[c_5323,c_913])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK2,sK4)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK2 != sK3 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_45950,plain,
    ( r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | r2_hidden(sK2,sK4)
    | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK2
    | sK2 != sK3 ),
    inference(resolution,[status(thm)],[c_16468,c_15])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(sK2,sK4)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_416,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | r2_hidden(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_599,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | r2_hidden(sK2,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_416])).

cnf(c_19,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | r2_hidden(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_24,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_27,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_26,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_28,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_157,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_619,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2))
    | X0 != X2
    | X1 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2) ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_712,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))
    | r2_hidden(X3,k5_xboole_0(X4,k3_xboole_0(X4,X5)))
    | X3 != X0
    | k5_xboole_0(X4,k3_xboole_0(X4,X5)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0) ),
    inference(instantiation,[status(thm)],[c_619])).

cnf(c_1085,plain,
    ( r2_hidden(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | X0 != sK2
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_1086,plain,
    ( X0 != sK2
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | r2_hidden(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = iProver_top
    | r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1085])).

cnf(c_1088,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK2 != sK2
    | r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1086])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1367,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | ~ r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1368,plain,
    ( r2_hidden(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1367])).

cnf(c_1370,plain,
    ( r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != iProver_top
    | r2_hidden(sK2,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1368])).

cnf(c_2777,plain,
    ( r2_hidden(sK2,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_599,c_19,c_24,c_27,c_28,c_1088,c_1370])).

cnf(c_4049,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,sK3))
    | X0 = X1
    | X0 = X2
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_15307,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k6_enumset1(X3,X3,X3,X3,X3,X3,X2,sK3))
    | sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = X2
    | sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = X3
    | sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK3 ),
    inference(instantiation,[status(thm)],[c_4049])).

cnf(c_15308,plain,
    ( sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = X2
    | sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = X3
    | sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK3
    | r2_hidden(sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k6_enumset1(X3,X3,X3,X3,X3,X3,X2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15307])).

cnf(c_15310,plain,
    ( sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK3
    | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK2
    | r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_15308])).

cnf(c_3180,plain,
    ( sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != X3
    | sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK2
    | sK2 != X3 ),
    inference(instantiation,[status(thm)],[c_154])).

cnf(c_26470,plain,
    ( sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != sK3
    | sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK2
    | sK2 != sK3 ),
    inference(instantiation,[status(thm)],[c_3180])).

cnf(c_26475,plain,
    ( sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != sK3
    | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK2
    | sK2 != sK3 ),
    inference(instantiation,[status(thm)],[c_26470])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1372,plain,
    ( r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ r2_hidden(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_31576,plain,
    ( r2_hidden(sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ r2_hidden(sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) ),
    inference(instantiation,[status(thm)],[c_1372])).

cnf(c_31579,plain,
    ( r2_hidden(sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top
    | r2_hidden(sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31576])).

cnf(c_31581,plain,
    ( r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top
    | r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_31579])).

cnf(c_45951,plain,
    ( sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK2
    | sK2 != sK3
    | r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45950])).

cnf(c_47206,plain,
    ( sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK2
    | sK2 != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_45950,c_19,c_24,c_27,c_28,c_1088,c_1370,c_15310,c_26475,c_31581,c_45951])).

cnf(c_48305,plain,
    ( X0 != sK2
    | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = X0
    | sK2 != sK3 ),
    inference(resolution,[status(thm)],[c_47206,c_154])).

cnf(c_12,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_679,plain,
    ( r2_hidden(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_683,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_679])).

cnf(c_419,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK2 != sK3
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_22,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK2 != sK3
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1738,plain,
    ( sK2 != sK3
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_419,c_19,c_22,c_24,c_27,c_28,c_1088,c_1370])).

cnf(c_1739,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK2 != sK3 ),
    inference(renaming,[status(thm)],[c_1738])).

cnf(c_2779,plain,
    ( ~ r2_hidden(sK2,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2777])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_635,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_enumset1(X2,X2,X2,X2,X2,X2,X0,X3))
    | r2_hidden(X0,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X0,X3),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X0,X3),X1))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2888,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_635])).

cnf(c_3572,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(c_1025,plain,
    ( X0 != X1
    | X0 = k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4)
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_154])).

cnf(c_10895,plain,
    ( X0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X1,X2)
    | X0 != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X1,X2) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_1025])).

cnf(c_47361,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0,X1) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0,X1)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_10895])).

cnf(c_47362,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_47361])).

cnf(c_930,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_157,c_153])).

cnf(c_48307,plain,
    ( r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),X0)
    | ~ r2_hidden(sK2,X0)
    | sK2 != sK3 ),
    inference(resolution,[status(thm)],[c_47206,c_930])).

cnf(c_9,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2,X3),X3)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
    | sK1(X0,X1,X2,X3) != X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_48394,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
    | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != sK2
    | sK2 != sK3 ),
    inference(resolution,[status(thm)],[c_48307,c_9])).

cnf(c_49552,plain,
    ( sK2 != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_48305,c_683,c_1739,c_2779,c_2888,c_3572,c_47206,c_47362,c_48394])).

cnf(c_158,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | X14 != X15
    | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
    theory(equality)).

cnf(c_5849,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | X14 != X15
    | X16 != k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15)
    | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = X16 ),
    inference(resolution,[status(thm)],[c_158,c_154])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK3,sK4)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK2 = sK3 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_29555,plain,
    ( r2_hidden(sK3,sK4)
    | X0 != sK2
    | X1 != sK2
    | X2 != sK2
    | X3 != sK2
    | X4 != sK2
    | X5 != sK2
    | X6 != sK2
    | X7 != sK2
    | k6_enumset1(X1,X0,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
    | sK2 = sK3 ),
    inference(resolution,[status(thm)],[c_5849,c_17])).

cnf(c_156,plain,
    ( X0 != X1
    | X2 != X3
    | k5_xboole_0(X0,X2) = k5_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_1129,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
    | r2_hidden(X3,k5_xboole_0(X4,X5))
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    inference(resolution,[status(thm)],[c_156,c_157])).

cnf(c_5914,plain,
    ( ~ r2_hidden(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)
    | r2_hidden(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),X0)
    | r2_hidden(sK3,sK4)
    | sK2 = sK3 ),
    inference(resolution,[status(thm)],[c_930,c_17])).

cnf(c_12927,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,X2))
    | ~ r2_hidden(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X3,X4))
    | r2_hidden(sK3,sK4)
    | X1 != X3
    | X2 != X4
    | X0 != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
    | sK2 = sK3 ),
    inference(resolution,[status(thm)],[c_1129,c_5914])).

cnf(c_30233,plain,
    ( r2_hidden(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(X8,X9))
    | ~ r2_hidden(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X10,X11))
    | r2_hidden(sK3,sK4)
    | X8 != X10
    | X9 != X11
    | X1 != sK2
    | X0 != sK2
    | X2 != sK2
    | X3 != sK2
    | X4 != sK2
    | X5 != sK2
    | X6 != sK2
    | X7 != sK2
    | sK2 = sK3 ),
    inference(resolution,[status(thm)],[c_29555,c_12927])).

cnf(c_593,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_154])).

cnf(c_594,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_593])).

cnf(c_671,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
    | sK3 = X0
    | sK3 = X1
    | sK3 = X2 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_673,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | sK3 = sK2 ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_735,plain,
    ( ~ r2_hidden(sK3,X0)
    | r2_hidden(sK3,k5_xboole_0(X0,k3_xboole_0(X0,sK4)))
    | r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_793,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3))
    | r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4)))
    | r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_735])).

cnf(c_796,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_11,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_794,plain,
    ( r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_800,plain,
    ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_830,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(c_5874,plain,
    ( r2_hidden(sK3,sK4)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
    | sK2 = sK3 ),
    inference(resolution,[status(thm)],[c_913,c_17])).

cnf(c_1636,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK3,X2)
    | X1 != X2
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_4433,plain,
    ( ~ r2_hidden(sK3,X0)
    | r2_hidden(sK3,X1)
    | X1 != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1636])).

cnf(c_9864,plain,
    ( r2_hidden(sK3,X0)
    | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,sK3),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,sK3),X3)))
    | X0 != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,sK3),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,sK3),X3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4433])).

cnf(c_36540,plain,
    ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0,X1))
    | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0,X1) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_9864])).

cnf(c_36542,plain,
    ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_36540])).

cnf(c_37274,plain,
    ( r2_hidden(sK3,sK4)
    | sK2 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_30233,c_24,c_27,c_594,c_673,c_796,c_800,c_830,c_5874,c_36542])).

cnf(c_49558,plain,
    ( r2_hidden(sK3,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_49552,c_37274])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(sK3,sK4)
    | r2_hidden(sK2,sK4)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_100204,plain,
    ( r2_hidden(sK2,sK4)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_49558,c_16])).

cnf(c_100244,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_100204,c_16,c_683,c_1739,c_2779,c_2888,c_3572,c_37274,c_47206,c_47362,c_48394])).

cnf(c_5866,plain,
    ( r2_hidden(sK1(X0,X1,X2,X3),X3)
    | X3 = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)
    | sK1(X0,X1,X2,X3) = X2
    | sK1(X0,X1,X2,X3) = X1
    | sK1(X0,X1,X2,X3) = X0 ),
    inference(resolution,[status(thm)],[c_913,c_10])).

cnf(c_100900,plain,
    ( r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK2 ),
    inference(resolution,[status(thm)],[c_100244,c_5866])).

cnf(c_3168,plain,
    ( r2_hidden(sK1(sK2,X0,X1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0,X1) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
    | sK1(sK2,X0,X1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = X1
    | sK1(sK2,X0,X1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = X0
    | sK1(sK2,X0,X1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK2 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3172,plain,
    ( r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
    | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK2 ),
    inference(instantiation,[status(thm)],[c_3168])).

cnf(c_746,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4)))
    | X2 != X0
    | k5_xboole_0(X3,k3_xboole_0(X3,X4)) != X1 ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_1342,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | ~ r2_hidden(X3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | X0 != X3
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_746])).

cnf(c_3571,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | r2_hidden(X1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | X1 != X0
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_1342])).

cnf(c_74915,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | r2_hidden(sK1(X1,X2,X3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | sK1(X1,X2,X3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != X0
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_3571])).

cnf(c_74917,plain,
    ( r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | ~ r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != sK2
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_74915])).

cnf(c_101907,plain,
    ( r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_100900,c_16,c_683,c_1739,c_2779,c_2888,c_3172,c_3572,c_37274,c_47206,c_47362,c_48394,c_74917])).

cnf(c_102736,plain,
    ( ~ r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),sK4) ),
    inference(resolution,[status(thm)],[c_101907,c_5])).

cnf(c_1377,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK3,sK4)
    | X1 != sK4
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_3122,plain,
    ( r2_hidden(X0,sK4)
    | ~ r2_hidden(sK3,sK4)
    | X0 != sK3
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1377])).

cnf(c_77348,plain,
    ( r2_hidden(sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),sK4)
    | ~ r2_hidden(sK3,sK4)
    | sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != sK3
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3122])).

cnf(c_77350,plain,
    ( r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),sK4)
    | ~ r2_hidden(sK3,sK4)
    | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != sK3
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_77348])).

cnf(c_31580,plain,
    ( r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) ),
    inference(instantiation,[status(thm)],[c_31576])).

cnf(c_15309,plain,
    ( ~ r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK3
    | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK2 ),
    inference(instantiation,[status(thm)],[c_15307])).

cnf(c_3123,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(c_7,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2,X3),X3)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
    | sK1(X0,X1,X2,X3) != X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2012,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
    | sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != X2 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2015,plain,
    ( ~ r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
    | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != sK2 ),
    inference(instantiation,[status(thm)],[c_2012])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_102736,c_101907,c_77350,c_49552,c_47362,c_37274,c_31580,c_15309,c_3572,c_3123,c_2779,c_2015,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 43.67/6.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.67/6.02  
% 43.67/6.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.67/6.02  
% 43.67/6.02  ------  iProver source info
% 43.67/6.02  
% 43.67/6.02  git: date: 2020-06-30 10:37:57 +0100
% 43.67/6.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.67/6.02  git: non_committed_changes: false
% 43.67/6.02  git: last_make_outside_of_git: false
% 43.67/6.02  
% 43.67/6.02  ------ 
% 43.67/6.02  
% 43.67/6.02  ------ Input Options
% 43.67/6.02  
% 43.67/6.02  --out_options                           all
% 43.67/6.02  --tptp_safe_out                         true
% 43.67/6.02  --problem_path                          ""
% 43.67/6.02  --include_path                          ""
% 43.67/6.02  --clausifier                            res/vclausify_rel
% 43.67/6.02  --clausifier_options                    --mode clausify
% 43.67/6.02  --stdin                                 false
% 43.67/6.02  --stats_out                             sel
% 43.67/6.02  
% 43.67/6.02  ------ General Options
% 43.67/6.02  
% 43.67/6.02  --fof                                   false
% 43.67/6.02  --time_out_real                         604.99
% 43.67/6.02  --time_out_virtual                      -1.
% 43.67/6.02  --symbol_type_check                     false
% 43.67/6.02  --clausify_out                          false
% 43.67/6.02  --sig_cnt_out                           false
% 43.67/6.02  --trig_cnt_out                          false
% 43.67/6.02  --trig_cnt_out_tolerance                1.
% 43.67/6.02  --trig_cnt_out_sk_spl                   false
% 43.67/6.02  --abstr_cl_out                          false
% 43.67/6.02  
% 43.67/6.02  ------ Global Options
% 43.67/6.02  
% 43.67/6.02  --schedule                              none
% 43.67/6.02  --add_important_lit                     false
% 43.67/6.02  --prop_solver_per_cl                    1000
% 43.67/6.02  --min_unsat_core                        false
% 43.67/6.02  --soft_assumptions                      false
% 43.67/6.02  --soft_lemma_size                       3
% 43.67/6.02  --prop_impl_unit_size                   0
% 43.67/6.02  --prop_impl_unit                        []
% 43.67/6.02  --share_sel_clauses                     true
% 43.67/6.02  --reset_solvers                         false
% 43.67/6.02  --bc_imp_inh                            [conj_cone]
% 43.67/6.02  --conj_cone_tolerance                   3.
% 43.67/6.02  --extra_neg_conj                        none
% 43.67/6.02  --large_theory_mode                     true
% 43.67/6.02  --prolific_symb_bound                   200
% 43.67/6.02  --lt_threshold                          2000
% 43.67/6.02  --clause_weak_htbl                      true
% 43.67/6.02  --gc_record_bc_elim                     false
% 43.67/6.02  
% 43.67/6.02  ------ Preprocessing Options
% 43.67/6.02  
% 43.67/6.02  --preprocessing_flag                    true
% 43.67/6.02  --time_out_prep_mult                    0.1
% 43.67/6.02  --splitting_mode                        input
% 43.67/6.02  --splitting_grd                         true
% 43.67/6.02  --splitting_cvd                         false
% 43.67/6.02  --splitting_cvd_svl                     false
% 43.67/6.02  --splitting_nvd                         32
% 43.67/6.02  --sub_typing                            true
% 43.67/6.02  --prep_gs_sim                           false
% 43.67/6.02  --prep_unflatten                        true
% 43.67/6.02  --prep_res_sim                          true
% 43.67/6.02  --prep_upred                            true
% 43.67/6.02  --prep_sem_filter                       exhaustive
% 43.67/6.02  --prep_sem_filter_out                   false
% 43.67/6.02  --pred_elim                             false
% 43.67/6.02  --res_sim_input                         true
% 43.67/6.02  --eq_ax_congr_red                       true
% 43.67/6.02  --pure_diseq_elim                       true
% 43.67/6.02  --brand_transform                       false
% 43.67/6.02  --non_eq_to_eq                          false
% 43.67/6.02  --prep_def_merge                        true
% 43.67/6.02  --prep_def_merge_prop_impl              false
% 43.67/6.02  --prep_def_merge_mbd                    true
% 43.67/6.02  --prep_def_merge_tr_red                 false
% 43.67/6.02  --prep_def_merge_tr_cl                  false
% 43.67/6.02  --smt_preprocessing                     true
% 43.67/6.02  --smt_ac_axioms                         fast
% 43.67/6.02  --preprocessed_out                      false
% 43.67/6.02  --preprocessed_stats                    false
% 43.67/6.02  
% 43.67/6.02  ------ Abstraction refinement Options
% 43.67/6.02  
% 43.67/6.02  --abstr_ref                             []
% 43.67/6.02  --abstr_ref_prep                        false
% 43.67/6.02  --abstr_ref_until_sat                   false
% 43.67/6.02  --abstr_ref_sig_restrict                funpre
% 43.67/6.02  --abstr_ref_af_restrict_to_split_sk     false
% 43.67/6.02  --abstr_ref_under                       []
% 43.67/6.02  
% 43.67/6.02  ------ SAT Options
% 43.67/6.02  
% 43.67/6.02  --sat_mode                              false
% 43.67/6.02  --sat_fm_restart_options                ""
% 43.67/6.02  --sat_gr_def                            false
% 43.67/6.02  --sat_epr_types                         true
% 43.67/6.02  --sat_non_cyclic_types                  false
% 43.67/6.02  --sat_finite_models                     false
% 43.67/6.02  --sat_fm_lemmas                         false
% 43.67/6.02  --sat_fm_prep                           false
% 43.67/6.02  --sat_fm_uc_incr                        true
% 43.67/6.02  --sat_out_model                         small
% 43.67/6.02  --sat_out_clauses                       false
% 43.67/6.02  
% 43.67/6.02  ------ QBF Options
% 43.67/6.02  
% 43.67/6.02  --qbf_mode                              false
% 43.67/6.02  --qbf_elim_univ                         false
% 43.67/6.02  --qbf_dom_inst                          none
% 43.67/6.02  --qbf_dom_pre_inst                      false
% 43.67/6.02  --qbf_sk_in                             false
% 43.67/6.02  --qbf_pred_elim                         true
% 43.67/6.02  --qbf_split                             512
% 43.67/6.02  
% 43.67/6.02  ------ BMC1 Options
% 43.67/6.02  
% 43.67/6.02  --bmc1_incremental                      false
% 43.67/6.02  --bmc1_axioms                           reachable_all
% 43.67/6.02  --bmc1_min_bound                        0
% 43.67/6.02  --bmc1_max_bound                        -1
% 43.67/6.02  --bmc1_max_bound_default                -1
% 43.67/6.02  --bmc1_symbol_reachability              true
% 43.67/6.02  --bmc1_property_lemmas                  false
% 43.67/6.02  --bmc1_k_induction                      false
% 43.67/6.02  --bmc1_non_equiv_states                 false
% 43.67/6.02  --bmc1_deadlock                         false
% 43.67/6.02  --bmc1_ucm                              false
% 43.67/6.02  --bmc1_add_unsat_core                   none
% 43.67/6.02  --bmc1_unsat_core_children              false
% 43.67/6.02  --bmc1_unsat_core_extrapolate_axioms    false
% 43.67/6.02  --bmc1_out_stat                         full
% 43.67/6.02  --bmc1_ground_init                      false
% 43.67/6.02  --bmc1_pre_inst_next_state              false
% 43.67/6.02  --bmc1_pre_inst_state                   false
% 43.67/6.02  --bmc1_pre_inst_reach_state             false
% 43.67/6.02  --bmc1_out_unsat_core                   false
% 43.67/6.02  --bmc1_aig_witness_out                  false
% 43.67/6.02  --bmc1_verbose                          false
% 43.67/6.02  --bmc1_dump_clauses_tptp                false
% 43.67/6.02  --bmc1_dump_unsat_core_tptp             false
% 43.67/6.02  --bmc1_dump_file                        -
% 43.67/6.02  --bmc1_ucm_expand_uc_limit              128
% 43.67/6.02  --bmc1_ucm_n_expand_iterations          6
% 43.67/6.02  --bmc1_ucm_extend_mode                  1
% 43.67/6.02  --bmc1_ucm_init_mode                    2
% 43.67/6.02  --bmc1_ucm_cone_mode                    none
% 43.67/6.02  --bmc1_ucm_reduced_relation_type        0
% 43.67/6.02  --bmc1_ucm_relax_model                  4
% 43.67/6.02  --bmc1_ucm_full_tr_after_sat            true
% 43.67/6.02  --bmc1_ucm_expand_neg_assumptions       false
% 43.67/6.02  --bmc1_ucm_layered_model                none
% 43.67/6.02  --bmc1_ucm_max_lemma_size               10
% 43.67/6.02  
% 43.67/6.02  ------ AIG Options
% 43.67/6.02  
% 43.67/6.02  --aig_mode                              false
% 43.67/6.02  
% 43.67/6.02  ------ Instantiation Options
% 43.67/6.02  
% 43.67/6.02  --instantiation_flag                    true
% 43.67/6.02  --inst_sos_flag                         false
% 43.67/6.02  --inst_sos_phase                        true
% 43.67/6.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.67/6.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.67/6.02  --inst_lit_sel_side                     num_symb
% 43.67/6.02  --inst_solver_per_active                1400
% 43.67/6.02  --inst_solver_calls_frac                1.
% 43.67/6.02  --inst_passive_queue_type               priority_queues
% 43.67/6.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.67/6.02  --inst_passive_queues_freq              [25;2]
% 43.67/6.02  --inst_dismatching                      true
% 43.67/6.02  --inst_eager_unprocessed_to_passive     true
% 43.67/6.02  --inst_prop_sim_given                   true
% 43.67/6.02  --inst_prop_sim_new                     false
% 43.67/6.02  --inst_subs_new                         false
% 43.67/6.02  --inst_eq_res_simp                      false
% 43.67/6.02  --inst_subs_given                       false
% 43.67/6.02  --inst_orphan_elimination               true
% 43.67/6.02  --inst_learning_loop_flag               true
% 43.67/6.02  --inst_learning_start                   3000
% 43.67/6.02  --inst_learning_factor                  2
% 43.67/6.02  --inst_start_prop_sim_after_learn       3
% 43.67/6.02  --inst_sel_renew                        solver
% 43.67/6.02  --inst_lit_activity_flag                true
% 43.67/6.02  --inst_restr_to_given                   false
% 43.67/6.02  --inst_activity_threshold               500
% 43.67/6.02  --inst_out_proof                        true
% 43.67/6.02  
% 43.67/6.02  ------ Resolution Options
% 43.67/6.02  
% 43.67/6.02  --resolution_flag                       true
% 43.67/6.02  --res_lit_sel                           adaptive
% 43.67/6.02  --res_lit_sel_side                      none
% 43.67/6.02  --res_ordering                          kbo
% 43.67/6.02  --res_to_prop_solver                    active
% 43.67/6.02  --res_prop_simpl_new                    false
% 43.67/6.02  --res_prop_simpl_given                  true
% 43.67/6.02  --res_passive_queue_type                priority_queues
% 43.67/6.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.67/6.02  --res_passive_queues_freq               [15;5]
% 43.67/6.02  --res_forward_subs                      full
% 43.67/6.02  --res_backward_subs                     full
% 43.67/6.02  --res_forward_subs_resolution           true
% 43.67/6.02  --res_backward_subs_resolution          true
% 43.67/6.02  --res_orphan_elimination                true
% 43.67/6.02  --res_time_limit                        2.
% 43.67/6.02  --res_out_proof                         true
% 43.67/6.02  
% 43.67/6.02  ------ Superposition Options
% 43.67/6.02  
% 43.67/6.02  --superposition_flag                    true
% 43.67/6.02  --sup_passive_queue_type                priority_queues
% 43.67/6.02  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.67/6.02  --sup_passive_queues_freq               [1;4]
% 43.67/6.02  --demod_completeness_check              fast
% 43.67/6.02  --demod_use_ground                      true
% 43.67/6.02  --sup_to_prop_solver                    passive
% 43.67/6.02  --sup_prop_simpl_new                    true
% 43.67/6.02  --sup_prop_simpl_given                  true
% 43.67/6.02  --sup_fun_splitting                     false
% 43.67/6.02  --sup_smt_interval                      50000
% 43.67/6.02  
% 43.67/6.02  ------ Superposition Simplification Setup
% 43.67/6.02  
% 43.67/6.02  --sup_indices_passive                   []
% 43.67/6.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.67/6.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.67/6.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.67/6.02  --sup_full_triv                         [TrivRules;PropSubs]
% 43.67/6.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.67/6.02  --sup_full_bw                           [BwDemod]
% 43.67/6.02  --sup_immed_triv                        [TrivRules]
% 43.67/6.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.67/6.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.67/6.02  --sup_immed_bw_main                     []
% 43.67/6.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 43.67/6.02  --sup_input_triv                        [Unflattening;TrivRules]
% 43.67/6.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.67/6.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 43.67/6.02  
% 43.67/6.02  ------ Combination Options
% 43.67/6.02  
% 43.67/6.02  --comb_res_mult                         3
% 43.67/6.02  --comb_sup_mult                         2
% 43.67/6.02  --comb_inst_mult                        10
% 43.67/6.02  
% 43.67/6.02  ------ Debug Options
% 43.67/6.02  
% 43.67/6.02  --dbg_backtrace                         false
% 43.67/6.02  --dbg_dump_prop_clauses                 false
% 43.67/6.02  --dbg_dump_prop_clauses_file            -
% 43.67/6.02  --dbg_out_stat                          false
% 43.67/6.02  ------ Parsing...
% 43.67/6.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.67/6.02  
% 43.67/6.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 43.67/6.02  
% 43.67/6.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.67/6.02  
% 43.67/6.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.67/6.02  ------ Proving...
% 43.67/6.02  ------ Problem Properties 
% 43.67/6.02  
% 43.67/6.02  
% 43.67/6.02  clauses                                 19
% 43.67/6.02  conjectures                             4
% 43.67/6.02  EPR                                     0
% 43.67/6.02  Horn                                    12
% 43.67/6.02  unary                                   4
% 43.67/6.02  binary                                  3
% 43.67/6.02  lits                                    50
% 43.67/6.02  lits eq                                 23
% 43.67/6.02  fd_pure                                 0
% 43.67/6.02  fd_pseudo                               0
% 43.67/6.02  fd_cond                                 0
% 43.67/6.02  fd_pseudo_cond                          7
% 43.67/6.02  AC symbols                              0
% 43.67/6.02  
% 43.67/6.02  ------ Input Options Time Limit: Unbounded
% 43.67/6.02  
% 43.67/6.02  
% 43.67/6.02  ------ 
% 43.67/6.02  Current options:
% 43.67/6.02  ------ 
% 43.67/6.02  
% 43.67/6.02  ------ Input Options
% 43.67/6.02  
% 43.67/6.02  --out_options                           all
% 43.67/6.02  --tptp_safe_out                         true
% 43.67/6.02  --problem_path                          ""
% 43.67/6.02  --include_path                          ""
% 43.67/6.02  --clausifier                            res/vclausify_rel
% 43.67/6.02  --clausifier_options                    --mode clausify
% 43.67/6.02  --stdin                                 false
% 43.67/6.02  --stats_out                             sel
% 43.67/6.02  
% 43.67/6.02  ------ General Options
% 43.67/6.02  
% 43.67/6.02  --fof                                   false
% 43.67/6.02  --time_out_real                         604.99
% 43.67/6.02  --time_out_virtual                      -1.
% 43.67/6.02  --symbol_type_check                     false
% 43.67/6.02  --clausify_out                          false
% 43.67/6.02  --sig_cnt_out                           false
% 43.67/6.02  --trig_cnt_out                          false
% 43.67/6.02  --trig_cnt_out_tolerance                1.
% 43.67/6.02  --trig_cnt_out_sk_spl                   false
% 43.67/6.02  --abstr_cl_out                          false
% 43.67/6.02  
% 43.67/6.02  ------ Global Options
% 43.67/6.02  
% 43.67/6.02  --schedule                              none
% 43.67/6.02  --add_important_lit                     false
% 43.67/6.02  --prop_solver_per_cl                    1000
% 43.67/6.02  --min_unsat_core                        false
% 43.67/6.02  --soft_assumptions                      false
% 43.67/6.02  --soft_lemma_size                       3
% 43.67/6.02  --prop_impl_unit_size                   0
% 43.67/6.02  --prop_impl_unit                        []
% 43.67/6.02  --share_sel_clauses                     true
% 43.67/6.02  --reset_solvers                         false
% 43.67/6.02  --bc_imp_inh                            [conj_cone]
% 43.67/6.02  --conj_cone_tolerance                   3.
% 43.67/6.02  --extra_neg_conj                        none
% 43.67/6.02  --large_theory_mode                     true
% 43.67/6.02  --prolific_symb_bound                   200
% 43.67/6.02  --lt_threshold                          2000
% 43.67/6.02  --clause_weak_htbl                      true
% 43.67/6.02  --gc_record_bc_elim                     false
% 43.67/6.02  
% 43.67/6.02  ------ Preprocessing Options
% 43.67/6.02  
% 43.67/6.02  --preprocessing_flag                    true
% 43.67/6.02  --time_out_prep_mult                    0.1
% 43.67/6.02  --splitting_mode                        input
% 43.67/6.02  --splitting_grd                         true
% 43.67/6.02  --splitting_cvd                         false
% 43.67/6.02  --splitting_cvd_svl                     false
% 43.67/6.02  --splitting_nvd                         32
% 43.67/6.02  --sub_typing                            true
% 43.67/6.02  --prep_gs_sim                           false
% 43.67/6.02  --prep_unflatten                        true
% 43.67/6.02  --prep_res_sim                          true
% 43.67/6.02  --prep_upred                            true
% 43.67/6.02  --prep_sem_filter                       exhaustive
% 43.67/6.02  --prep_sem_filter_out                   false
% 43.67/6.02  --pred_elim                             false
% 43.67/6.02  --res_sim_input                         true
% 43.67/6.02  --eq_ax_congr_red                       true
% 43.67/6.02  --pure_diseq_elim                       true
% 43.67/6.02  --brand_transform                       false
% 43.67/6.02  --non_eq_to_eq                          false
% 43.67/6.02  --prep_def_merge                        true
% 43.67/6.02  --prep_def_merge_prop_impl              false
% 43.67/6.02  --prep_def_merge_mbd                    true
% 43.67/6.02  --prep_def_merge_tr_red                 false
% 43.67/6.02  --prep_def_merge_tr_cl                  false
% 43.67/6.02  --smt_preprocessing                     true
% 43.67/6.02  --smt_ac_axioms                         fast
% 43.67/6.02  --preprocessed_out                      false
% 43.67/6.02  --preprocessed_stats                    false
% 43.67/6.02  
% 43.67/6.02  ------ Abstraction refinement Options
% 43.67/6.02  
% 43.67/6.02  --abstr_ref                             []
% 43.67/6.02  --abstr_ref_prep                        false
% 43.67/6.02  --abstr_ref_until_sat                   false
% 43.67/6.02  --abstr_ref_sig_restrict                funpre
% 43.67/6.02  --abstr_ref_af_restrict_to_split_sk     false
% 43.67/6.02  --abstr_ref_under                       []
% 43.67/6.02  
% 43.67/6.02  ------ SAT Options
% 43.67/6.02  
% 43.67/6.02  --sat_mode                              false
% 43.67/6.02  --sat_fm_restart_options                ""
% 43.67/6.02  --sat_gr_def                            false
% 43.67/6.02  --sat_epr_types                         true
% 43.67/6.02  --sat_non_cyclic_types                  false
% 43.67/6.02  --sat_finite_models                     false
% 43.67/6.02  --sat_fm_lemmas                         false
% 43.67/6.02  --sat_fm_prep                           false
% 43.67/6.02  --sat_fm_uc_incr                        true
% 43.67/6.02  --sat_out_model                         small
% 43.67/6.02  --sat_out_clauses                       false
% 43.67/6.02  
% 43.67/6.02  ------ QBF Options
% 43.67/6.02  
% 43.67/6.02  --qbf_mode                              false
% 43.67/6.02  --qbf_elim_univ                         false
% 43.67/6.02  --qbf_dom_inst                          none
% 43.67/6.02  --qbf_dom_pre_inst                      false
% 43.67/6.02  --qbf_sk_in                             false
% 43.67/6.02  --qbf_pred_elim                         true
% 43.67/6.02  --qbf_split                             512
% 43.67/6.02  
% 43.67/6.02  ------ BMC1 Options
% 43.67/6.02  
% 43.67/6.02  --bmc1_incremental                      false
% 43.67/6.02  --bmc1_axioms                           reachable_all
% 43.67/6.02  --bmc1_min_bound                        0
% 43.67/6.02  --bmc1_max_bound                        -1
% 43.67/6.02  --bmc1_max_bound_default                -1
% 43.67/6.02  --bmc1_symbol_reachability              true
% 43.67/6.02  --bmc1_property_lemmas                  false
% 43.67/6.02  --bmc1_k_induction                      false
% 43.67/6.02  --bmc1_non_equiv_states                 false
% 43.67/6.02  --bmc1_deadlock                         false
% 43.67/6.02  --bmc1_ucm                              false
% 43.67/6.02  --bmc1_add_unsat_core                   none
% 43.67/6.02  --bmc1_unsat_core_children              false
% 43.67/6.02  --bmc1_unsat_core_extrapolate_axioms    false
% 43.67/6.02  --bmc1_out_stat                         full
% 43.67/6.02  --bmc1_ground_init                      false
% 43.67/6.02  --bmc1_pre_inst_next_state              false
% 43.67/6.02  --bmc1_pre_inst_state                   false
% 43.67/6.02  --bmc1_pre_inst_reach_state             false
% 43.67/6.02  --bmc1_out_unsat_core                   false
% 43.67/6.02  --bmc1_aig_witness_out                  false
% 43.67/6.02  --bmc1_verbose                          false
% 43.67/6.02  --bmc1_dump_clauses_tptp                false
% 43.67/6.02  --bmc1_dump_unsat_core_tptp             false
% 43.67/6.02  --bmc1_dump_file                        -
% 43.67/6.02  --bmc1_ucm_expand_uc_limit              128
% 43.67/6.02  --bmc1_ucm_n_expand_iterations          6
% 43.67/6.02  --bmc1_ucm_extend_mode                  1
% 43.67/6.02  --bmc1_ucm_init_mode                    2
% 43.67/6.02  --bmc1_ucm_cone_mode                    none
% 43.67/6.02  --bmc1_ucm_reduced_relation_type        0
% 43.67/6.02  --bmc1_ucm_relax_model                  4
% 43.67/6.02  --bmc1_ucm_full_tr_after_sat            true
% 43.67/6.02  --bmc1_ucm_expand_neg_assumptions       false
% 43.67/6.02  --bmc1_ucm_layered_model                none
% 43.67/6.02  --bmc1_ucm_max_lemma_size               10
% 43.67/6.02  
% 43.67/6.02  ------ AIG Options
% 43.67/6.02  
% 43.67/6.02  --aig_mode                              false
% 43.67/6.02  
% 43.67/6.02  ------ Instantiation Options
% 43.67/6.02  
% 43.67/6.02  --instantiation_flag                    true
% 43.67/6.02  --inst_sos_flag                         false
% 43.67/6.02  --inst_sos_phase                        true
% 43.67/6.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.67/6.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.67/6.02  --inst_lit_sel_side                     num_symb
% 43.67/6.02  --inst_solver_per_active                1400
% 43.67/6.02  --inst_solver_calls_frac                1.
% 43.67/6.02  --inst_passive_queue_type               priority_queues
% 43.67/6.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.67/6.02  --inst_passive_queues_freq              [25;2]
% 43.67/6.02  --inst_dismatching                      true
% 43.67/6.02  --inst_eager_unprocessed_to_passive     true
% 43.67/6.02  --inst_prop_sim_given                   true
% 43.67/6.02  --inst_prop_sim_new                     false
% 43.67/6.02  --inst_subs_new                         false
% 43.67/6.02  --inst_eq_res_simp                      false
% 43.67/6.02  --inst_subs_given                       false
% 43.67/6.02  --inst_orphan_elimination               true
% 43.67/6.02  --inst_learning_loop_flag               true
% 43.67/6.02  --inst_learning_start                   3000
% 43.67/6.02  --inst_learning_factor                  2
% 43.67/6.02  --inst_start_prop_sim_after_learn       3
% 43.67/6.02  --inst_sel_renew                        solver
% 43.67/6.02  --inst_lit_activity_flag                true
% 43.67/6.02  --inst_restr_to_given                   false
% 43.67/6.02  --inst_activity_threshold               500
% 43.67/6.02  --inst_out_proof                        true
% 43.67/6.02  
% 43.67/6.02  ------ Resolution Options
% 43.67/6.02  
% 43.67/6.02  --resolution_flag                       true
% 43.67/6.02  --res_lit_sel                           adaptive
% 43.67/6.02  --res_lit_sel_side                      none
% 43.67/6.02  --res_ordering                          kbo
% 43.67/6.02  --res_to_prop_solver                    active
% 43.67/6.02  --res_prop_simpl_new                    false
% 43.67/6.02  --res_prop_simpl_given                  true
% 43.67/6.02  --res_passive_queue_type                priority_queues
% 43.67/6.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.67/6.02  --res_passive_queues_freq               [15;5]
% 43.67/6.02  --res_forward_subs                      full
% 43.67/6.02  --res_backward_subs                     full
% 43.67/6.02  --res_forward_subs_resolution           true
% 43.67/6.02  --res_backward_subs_resolution          true
% 43.67/6.02  --res_orphan_elimination                true
% 43.67/6.02  --res_time_limit                        2.
% 43.67/6.02  --res_out_proof                         true
% 43.67/6.02  
% 43.67/6.02  ------ Superposition Options
% 43.67/6.02  
% 43.67/6.02  --superposition_flag                    true
% 43.67/6.02  --sup_passive_queue_type                priority_queues
% 43.67/6.02  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.67/6.02  --sup_passive_queues_freq               [1;4]
% 43.67/6.02  --demod_completeness_check              fast
% 43.67/6.02  --demod_use_ground                      true
% 43.67/6.02  --sup_to_prop_solver                    passive
% 43.67/6.02  --sup_prop_simpl_new                    true
% 43.67/6.02  --sup_prop_simpl_given                  true
% 43.67/6.02  --sup_fun_splitting                     false
% 43.67/6.02  --sup_smt_interval                      50000
% 43.67/6.02  
% 43.67/6.02  ------ Superposition Simplification Setup
% 43.67/6.02  
% 43.67/6.02  --sup_indices_passive                   []
% 43.67/6.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.67/6.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.67/6.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 43.67/6.02  --sup_full_triv                         [TrivRules;PropSubs]
% 43.67/6.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.67/6.02  --sup_full_bw                           [BwDemod]
% 43.67/6.02  --sup_immed_triv                        [TrivRules]
% 43.67/6.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.67/6.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.67/6.02  --sup_immed_bw_main                     []
% 43.67/6.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 43.67/6.02  --sup_input_triv                        [Unflattening;TrivRules]
% 43.67/6.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 43.67/6.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 43.67/6.02  
% 43.67/6.02  ------ Combination Options
% 43.67/6.02  
% 43.67/6.02  --comb_res_mult                         3
% 43.67/6.02  --comb_sup_mult                         2
% 43.67/6.02  --comb_inst_mult                        10
% 43.67/6.02  
% 43.67/6.02  ------ Debug Options
% 43.67/6.02  
% 43.67/6.02  --dbg_backtrace                         false
% 43.67/6.02  --dbg_dump_prop_clauses                 false
% 43.67/6.02  --dbg_dump_prop_clauses_file            -
% 43.67/6.02  --dbg_out_stat                          false
% 43.67/6.02  
% 43.67/6.02  
% 43.67/6.02  
% 43.67/6.02  
% 43.67/6.02  ------ Proving...
% 43.67/6.02  
% 43.67/6.02  
% 43.67/6.02  % SZS status Theorem for theBenchmark.p
% 43.67/6.02  
% 43.67/6.02  % SZS output start CNFRefutation for theBenchmark.p
% 43.67/6.02  
% 43.67/6.02  fof(f4,axiom,(
% 43.67/6.02    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 43.67/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.67/6.02  
% 43.67/6.02  fof(f14,plain,(
% 43.67/6.02    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 43.67/6.02    inference(ennf_transformation,[],[f4])).
% 43.67/6.02  
% 43.67/6.02  fof(f21,plain,(
% 43.67/6.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 43.67/6.02    inference(nnf_transformation,[],[f14])).
% 43.67/6.02  
% 43.67/6.02  fof(f22,plain,(
% 43.67/6.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 43.67/6.02    inference(flattening,[],[f21])).
% 43.67/6.02  
% 43.67/6.02  fof(f23,plain,(
% 43.67/6.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 43.67/6.02    inference(rectify,[],[f22])).
% 43.67/6.02  
% 43.67/6.02  fof(f24,plain,(
% 43.67/6.02    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 43.67/6.02    introduced(choice_axiom,[])).
% 43.67/6.02  
% 43.67/6.02  fof(f25,plain,(
% 43.67/6.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 43.67/6.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).
% 43.67/6.02  
% 43.67/6.02  fof(f42,plain,(
% 43.67/6.02    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)) )),
% 43.67/6.02    inference(cnf_transformation,[],[f25])).
% 43.67/6.02  
% 43.67/6.02  fof(f7,axiom,(
% 43.67/6.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 43.67/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.67/6.02  
% 43.67/6.02  fof(f48,plain,(
% 43.67/6.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 43.67/6.02    inference(cnf_transformation,[],[f7])).
% 43.67/6.02  
% 43.67/6.02  fof(f8,axiom,(
% 43.67/6.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 43.67/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.67/6.02  
% 43.67/6.02  fof(f49,plain,(
% 43.67/6.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 43.67/6.02    inference(cnf_transformation,[],[f8])).
% 43.67/6.02  
% 43.67/6.02  fof(f9,axiom,(
% 43.67/6.02    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 43.67/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.67/6.02  
% 43.67/6.02  fof(f50,plain,(
% 43.67/6.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 43.67/6.02    inference(cnf_transformation,[],[f9])).
% 43.67/6.02  
% 43.67/6.02  fof(f10,axiom,(
% 43.67/6.02    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 43.67/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.67/6.02  
% 43.67/6.02  fof(f51,plain,(
% 43.67/6.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 43.67/6.02    inference(cnf_transformation,[],[f10])).
% 43.67/6.02  
% 43.67/6.02  fof(f11,axiom,(
% 43.67/6.02    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 43.67/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.67/6.02  
% 43.67/6.02  fof(f52,plain,(
% 43.67/6.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 43.67/6.02    inference(cnf_transformation,[],[f11])).
% 43.67/6.02  
% 43.67/6.02  fof(f57,plain,(
% 43.67/6.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 43.67/6.02    inference(definition_unfolding,[],[f51,f52])).
% 43.67/6.02  
% 43.67/6.02  fof(f58,plain,(
% 43.67/6.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 43.67/6.02    inference(definition_unfolding,[],[f50,f57])).
% 43.67/6.02  
% 43.67/6.02  fof(f59,plain,(
% 43.67/6.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 43.67/6.02    inference(definition_unfolding,[],[f49,f58])).
% 43.67/6.02  
% 43.67/6.02  fof(f60,plain,(
% 43.67/6.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 43.67/6.02    inference(definition_unfolding,[],[f48,f59])).
% 43.67/6.02  
% 43.67/6.02  fof(f72,plain,(
% 43.67/6.02    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 | sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)) )),
% 43.67/6.02    inference(definition_unfolding,[],[f42,f60])).
% 43.67/6.02  
% 43.67/6.02  fof(f12,conjecture,(
% 43.67/6.02    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 43.67/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.67/6.02  
% 43.67/6.02  fof(f13,negated_conjecture,(
% 43.67/6.02    ~! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 43.67/6.02    inference(negated_conjecture,[],[f12])).
% 43.67/6.02  
% 43.67/6.02  fof(f15,plain,(
% 43.67/6.02    ? [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) <~> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 43.67/6.02    inference(ennf_transformation,[],[f13])).
% 43.67/6.02  
% 43.67/6.02  fof(f26,plain,(
% 43.67/6.02    ? [X0,X1,X2] : ((((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)))),
% 43.67/6.02    inference(nnf_transformation,[],[f15])).
% 43.67/6.02  
% 43.67/6.02  fof(f27,plain,(
% 43.67/6.02    ? [X0,X1,X2] : (((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)))),
% 43.67/6.02    inference(flattening,[],[f26])).
% 43.67/6.02  
% 43.67/6.02  fof(f28,plain,(
% 43.67/6.02    ? [X0,X1,X2] : (((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0))) => (((sK2 != sK3 & ~r2_hidden(sK3,sK4)) | r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k1_tarski(sK2)) & (((sK2 = sK3 | r2_hidden(sK3,sK4)) & ~r2_hidden(sK2,sK4)) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_tarski(sK2)))),
% 43.67/6.02    introduced(choice_axiom,[])).
% 43.67/6.02  
% 43.67/6.02  fof(f29,plain,(
% 43.67/6.02    ((sK2 != sK3 & ~r2_hidden(sK3,sK4)) | r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k1_tarski(sK2)) & (((sK2 = sK3 | r2_hidden(sK3,sK4)) & ~r2_hidden(sK2,sK4)) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_tarski(sK2))),
% 43.67/6.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f28])).
% 43.67/6.02  
% 43.67/6.02  fof(f56,plain,(
% 43.67/6.02    sK2 != sK3 | r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k1_tarski(sK2)),
% 43.67/6.02    inference(cnf_transformation,[],[f29])).
% 43.67/6.02  
% 43.67/6.02  fof(f3,axiom,(
% 43.67/6.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 43.67/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.67/6.02  
% 43.67/6.02  fof(f37,plain,(
% 43.67/6.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 43.67/6.02    inference(cnf_transformation,[],[f3])).
% 43.67/6.02  
% 43.67/6.02  fof(f5,axiom,(
% 43.67/6.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 43.67/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.67/6.02  
% 43.67/6.02  fof(f46,plain,(
% 43.67/6.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 43.67/6.02    inference(cnf_transformation,[],[f5])).
% 43.67/6.02  
% 43.67/6.02  fof(f6,axiom,(
% 43.67/6.02    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 43.67/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.67/6.02  
% 43.67/6.02  fof(f47,plain,(
% 43.67/6.02    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 43.67/6.02    inference(cnf_transformation,[],[f6])).
% 43.67/6.02  
% 43.67/6.02  fof(f61,plain,(
% 43.67/6.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 43.67/6.02    inference(definition_unfolding,[],[f47,f60])).
% 43.67/6.02  
% 43.67/6.02  fof(f62,plain,(
% 43.67/6.02    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 43.67/6.02    inference(definition_unfolding,[],[f46,f61])).
% 43.67/6.02  
% 43.67/6.02  fof(f77,plain,(
% 43.67/6.02    sK2 != sK3 | r2_hidden(sK2,sK4) | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 43.67/6.02    inference(definition_unfolding,[],[f56,f37,f61,f62])).
% 43.67/6.02  
% 43.67/6.02  fof(f1,axiom,(
% 43.67/6.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 43.67/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.67/6.02  
% 43.67/6.02  fof(f30,plain,(
% 43.67/6.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 43.67/6.02    inference(cnf_transformation,[],[f1])).
% 43.67/6.02  
% 43.67/6.02  fof(f53,plain,(
% 43.67/6.02    ~r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_tarski(sK2)),
% 43.67/6.02    inference(cnf_transformation,[],[f29])).
% 43.67/6.02  
% 43.67/6.02  fof(f80,plain,(
% 43.67/6.02    ~r2_hidden(sK2,sK4) | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 43.67/6.02    inference(definition_unfolding,[],[f53,f37,f61,f62])).
% 43.67/6.02  
% 43.67/6.02  fof(f38,plain,(
% 43.67/6.02    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 43.67/6.02    inference(cnf_transformation,[],[f25])).
% 43.67/6.02  
% 43.67/6.02  fof(f76,plain,(
% 43.67/6.02    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 43.67/6.02    inference(definition_unfolding,[],[f38,f60])).
% 43.67/6.02  
% 43.67/6.02  fof(f90,plain,(
% 43.67/6.02    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 43.67/6.02    inference(equality_resolution,[],[f76])).
% 43.67/6.02  
% 43.67/6.02  fof(f39,plain,(
% 43.67/6.02    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 43.67/6.02    inference(cnf_transformation,[],[f25])).
% 43.67/6.02  
% 43.67/6.02  fof(f75,plain,(
% 43.67/6.02    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 43.67/6.02    inference(definition_unfolding,[],[f39,f60])).
% 43.67/6.02  
% 43.67/6.02  fof(f88,plain,(
% 43.67/6.02    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 43.67/6.02    inference(equality_resolution,[],[f75])).
% 43.67/6.02  
% 43.67/6.02  fof(f89,plain,(
% 43.67/6.02    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 43.67/6.02    inference(equality_resolution,[],[f88])).
% 43.67/6.02  
% 43.67/6.02  fof(f2,axiom,(
% 43.67/6.02    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 43.67/6.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 43.67/6.02  
% 43.67/6.02  fof(f16,plain,(
% 43.67/6.02    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 43.67/6.02    inference(nnf_transformation,[],[f2])).
% 43.67/6.02  
% 43.67/6.02  fof(f17,plain,(
% 43.67/6.02    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 43.67/6.02    inference(flattening,[],[f16])).
% 43.67/6.02  
% 43.67/6.02  fof(f18,plain,(
% 43.67/6.02    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 43.67/6.02    inference(rectify,[],[f17])).
% 43.67/6.02  
% 43.67/6.02  fof(f19,plain,(
% 43.67/6.02    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 43.67/6.02    introduced(choice_axiom,[])).
% 43.67/6.02  
% 43.67/6.02  fof(f20,plain,(
% 43.67/6.02    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 43.67/6.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 43.67/6.02  
% 43.67/6.02  fof(f32,plain,(
% 43.67/6.02    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 43.67/6.02    inference(cnf_transformation,[],[f20])).
% 43.67/6.02  
% 43.67/6.02  fof(f67,plain,(
% 43.67/6.02    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 43.67/6.02    inference(definition_unfolding,[],[f32,f37])).
% 43.67/6.02  
% 43.67/6.02  fof(f82,plain,(
% 43.67/6.02    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 43.67/6.02    inference(equality_resolution,[],[f67])).
% 43.67/6.02  
% 43.67/6.02  fof(f31,plain,(
% 43.67/6.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 43.67/6.02    inference(cnf_transformation,[],[f20])).
% 43.67/6.02  
% 43.67/6.02  fof(f68,plain,(
% 43.67/6.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 43.67/6.02    inference(definition_unfolding,[],[f31,f37])).
% 43.67/6.02  
% 43.67/6.02  fof(f83,plain,(
% 43.67/6.02    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 43.67/6.02    inference(equality_resolution,[],[f68])).
% 43.67/6.02  
% 43.67/6.02  fof(f40,plain,(
% 43.67/6.02    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 43.67/6.02    inference(cnf_transformation,[],[f25])).
% 43.67/6.02  
% 43.67/6.02  fof(f74,plain,(
% 43.67/6.02    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 43.67/6.02    inference(definition_unfolding,[],[f40,f60])).
% 43.67/6.02  
% 43.67/6.02  fof(f86,plain,(
% 43.67/6.02    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 43.67/6.02    inference(equality_resolution,[],[f74])).
% 43.67/6.02  
% 43.67/6.02  fof(f87,plain,(
% 43.67/6.02    ( ! [X2,X0,X5] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2))) )),
% 43.67/6.02    inference(equality_resolution,[],[f86])).
% 43.67/6.02  
% 43.67/6.02  fof(f33,plain,(
% 43.67/6.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 43.67/6.02    inference(cnf_transformation,[],[f20])).
% 43.67/6.02  
% 43.67/6.02  fof(f66,plain,(
% 43.67/6.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 43.67/6.02    inference(definition_unfolding,[],[f33,f37])).
% 43.67/6.02  
% 43.67/6.02  fof(f81,plain,(
% 43.67/6.02    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 43.67/6.02    inference(equality_resolution,[],[f66])).
% 43.67/6.02  
% 43.67/6.02  fof(f43,plain,(
% 43.67/6.02    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK1(X0,X1,X2,X3) != X0 | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) )),
% 43.67/6.02    inference(cnf_transformation,[],[f25])).
% 43.67/6.02  
% 43.67/6.02  fof(f71,plain,(
% 43.67/6.02    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 | sK1(X0,X1,X2,X3) != X0 | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) )),
% 43.67/6.02    inference(definition_unfolding,[],[f43,f60])).
% 43.67/6.02  
% 43.67/6.02  fof(f54,plain,(
% 43.67/6.02    sK2 = sK3 | r2_hidden(sK3,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_tarski(sK2)),
% 43.67/6.02    inference(cnf_transformation,[],[f29])).
% 43.67/6.02  
% 43.67/6.02  fof(f79,plain,(
% 43.67/6.02    sK2 = sK3 | r2_hidden(sK3,sK4) | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 43.67/6.02    inference(definition_unfolding,[],[f54,f37,f61,f62])).
% 43.67/6.02  
% 43.67/6.02  fof(f41,plain,(
% 43.67/6.02    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 43.67/6.02    inference(cnf_transformation,[],[f25])).
% 43.67/6.02  
% 43.67/6.02  fof(f73,plain,(
% 43.67/6.02    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 43.67/6.02    inference(definition_unfolding,[],[f41,f60])).
% 43.67/6.02  
% 43.67/6.02  fof(f84,plain,(
% 43.67/6.02    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 43.67/6.02    inference(equality_resolution,[],[f73])).
% 43.67/6.02  
% 43.67/6.02  fof(f85,plain,(
% 43.67/6.02    ( ! [X0,X5,X1] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5))) )),
% 43.67/6.02    inference(equality_resolution,[],[f84])).
% 43.67/6.02  
% 43.67/6.02  fof(f55,plain,(
% 43.67/6.02    ~r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k1_tarski(sK2)),
% 43.67/6.02    inference(cnf_transformation,[],[f29])).
% 43.67/6.02  
% 43.67/6.02  fof(f78,plain,(
% 43.67/6.02    ~r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 43.67/6.02    inference(definition_unfolding,[],[f55,f37,f61,f62])).
% 43.67/6.02  
% 43.67/6.02  fof(f45,plain,(
% 43.67/6.02    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK1(X0,X1,X2,X3) != X2 | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) )),
% 43.67/6.02    inference(cnf_transformation,[],[f25])).
% 43.67/6.02  
% 43.67/6.02  fof(f69,plain,(
% 43.67/6.02    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 | sK1(X0,X1,X2,X3) != X2 | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) )),
% 43.67/6.02    inference(definition_unfolding,[],[f45,f60])).
% 43.67/6.02  
% 43.67/6.02  cnf(c_10,plain,
% 43.67/6.02      ( r2_hidden(sK1(X0,X1,X2,X3),X3)
% 43.67/6.02      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
% 43.67/6.02      | sK1(X0,X1,X2,X3) = X2
% 43.67/6.02      | sK1(X0,X1,X2,X3) = X1
% 43.67/6.02      | sK1(X0,X1,X2,X3) = X0 ),
% 43.67/6.02      inference(cnf_transformation,[],[f72]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_5323,plain,
% 43.67/6.02      ( r2_hidden(sK1(X0,X1,X1,X2),X2)
% 43.67/6.02      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X1) = X2
% 43.67/6.02      | sK1(X0,X1,X1,X2) = X1
% 43.67/6.02      | sK1(X0,X1,X1,X2) = X0 ),
% 43.67/6.02      inference(factoring,[status(thm)],[c_10]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_154,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_153,plain,( X0 = X0 ),theory(equality) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_913,plain,
% 43.67/6.02      ( X0 != X1 | X1 = X0 ),
% 43.67/6.02      inference(resolution,[status(thm)],[c_154,c_153]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_16468,plain,
% 43.67/6.02      ( r2_hidden(sK1(X0,X1,X1,X2),X2)
% 43.67/6.02      | X2 = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X1)
% 43.67/6.02      | sK1(X0,X1,X1,X2) = X1
% 43.67/6.02      | sK1(X0,X1,X1,X2) = X0 ),
% 43.67/6.02      inference(resolution,[status(thm)],[c_5323,c_913]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_15,negated_conjecture,
% 43.67/6.02      ( r2_hidden(sK2,sK4)
% 43.67/6.02      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 43.67/6.02      | sK2 != sK3 ),
% 43.67/6.02      inference(cnf_transformation,[],[f77]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_45950,plain,
% 43.67/6.02      ( r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 43.67/6.02      | r2_hidden(sK2,sK4)
% 43.67/6.02      | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK2
% 43.67/6.02      | sK2 != sK3 ),
% 43.67/6.02      inference(resolution,[status(thm)],[c_16468,c_15]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_0,plain,
% 43.67/6.02      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 43.67/6.02      inference(cnf_transformation,[],[f30]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_18,negated_conjecture,
% 43.67/6.02      ( ~ r2_hidden(sK2,sK4)
% 43.67/6.02      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 43.67/6.02      inference(cnf_transformation,[],[f80]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_416,plain,
% 43.67/6.02      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 43.67/6.02      | r2_hidden(sK2,sK4) != iProver_top ),
% 43.67/6.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_599,plain,
% 43.67/6.02      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 43.67/6.02      | r2_hidden(sK2,sK4) != iProver_top ),
% 43.67/6.02      inference(demodulation,[status(thm)],[c_0,c_416]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_19,plain,
% 43.67/6.02      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 43.67/6.02      | r2_hidden(sK2,sK4) != iProver_top ),
% 43.67/6.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_14,plain,
% 43.67/6.02      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
% 43.67/6.02      | X0 = X1
% 43.67/6.02      | X0 = X2
% 43.67/6.02      | X0 = X3 ),
% 43.67/6.02      inference(cnf_transformation,[],[f90]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_24,plain,
% 43.67/6.02      ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 43.67/6.02      | sK2 = sK2 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_14]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_13,plain,
% 43.67/6.02      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 43.67/6.02      inference(cnf_transformation,[],[f89]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_27,plain,
% 43.67/6.02      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_13]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_26,plain,
% 43.67/6.02      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 43.67/6.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_28,plain,
% 43.67/6.02      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_26]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_157,plain,
% 43.67/6.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 43.67/6.02      theory(equality) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_619,plain,
% 43.67/6.02      ( r2_hidden(X0,X1)
% 43.67/6.02      | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2))
% 43.67/6.02      | X0 != X2
% 43.67/6.02      | X1 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_157]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_712,plain,
% 43.67/6.02      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))
% 43.67/6.02      | r2_hidden(X3,k5_xboole_0(X4,k3_xboole_0(X4,X5)))
% 43.67/6.02      | X3 != X0
% 43.67/6.02      | k5_xboole_0(X4,k3_xboole_0(X4,X5)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_619]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_1085,plain,
% 43.67/6.02      ( r2_hidden(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 43.67/6.02      | ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 43.67/6.02      | X0 != sK2
% 43.67/6.02      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_712]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_1086,plain,
% 43.67/6.02      ( X0 != sK2
% 43.67/6.02      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 43.67/6.02      | r2_hidden(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = iProver_top
% 43.67/6.02      | r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 43.67/6.02      inference(predicate_to_equality,[status(thm)],[c_1085]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_1088,plain,
% 43.67/6.02      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 43.67/6.02      | sK2 != sK2
% 43.67/6.02      | r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 43.67/6.02      | r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = iProver_top ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_1086]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_5,plain,
% 43.67/6.02      ( ~ r2_hidden(X0,X1)
% 43.67/6.02      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 43.67/6.02      inference(cnf_transformation,[],[f82]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_1367,plain,
% 43.67/6.02      ( ~ r2_hidden(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 43.67/6.02      | ~ r2_hidden(X0,sK4) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_5]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_1368,plain,
% 43.67/6.02      ( r2_hidden(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != iProver_top
% 43.67/6.02      | r2_hidden(X0,sK4) != iProver_top ),
% 43.67/6.02      inference(predicate_to_equality,[status(thm)],[c_1367]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_1370,plain,
% 43.67/6.02      ( r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != iProver_top
% 43.67/6.02      | r2_hidden(sK2,sK4) != iProver_top ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_1368]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_2777,plain,
% 43.67/6.02      ( r2_hidden(sK2,sK4) != iProver_top ),
% 43.67/6.02      inference(global_propositional_subsumption,
% 43.67/6.02                [status(thm)],
% 43.67/6.02                [c_599,c_19,c_24,c_27,c_28,c_1088,c_1370]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_4049,plain,
% 43.67/6.02      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,sK3))
% 43.67/6.02      | X0 = X1
% 43.67/6.02      | X0 = X2
% 43.67/6.02      | X0 = sK3 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_14]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_15307,plain,
% 43.67/6.02      ( ~ r2_hidden(sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k6_enumset1(X3,X3,X3,X3,X3,X3,X2,sK3))
% 43.67/6.02      | sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = X2
% 43.67/6.02      | sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = X3
% 43.67/6.02      | sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK3 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_4049]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_15308,plain,
% 43.67/6.02      ( sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = X2
% 43.67/6.02      | sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = X3
% 43.67/6.02      | sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK3
% 43.67/6.02      | r2_hidden(sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k6_enumset1(X3,X3,X3,X3,X3,X3,X2,sK3)) != iProver_top ),
% 43.67/6.02      inference(predicate_to_equality,[status(thm)],[c_15307]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_15310,plain,
% 43.67/6.02      ( sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK3
% 43.67/6.02      | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK2
% 43.67/6.02      | r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_15308]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_3180,plain,
% 43.67/6.02      ( sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != X3
% 43.67/6.02      | sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK2
% 43.67/6.02      | sK2 != X3 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_154]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_26470,plain,
% 43.67/6.02      ( sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != sK3
% 43.67/6.02      | sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK2
% 43.67/6.02      | sK2 != sK3 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_3180]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_26475,plain,
% 43.67/6.02      ( sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != sK3
% 43.67/6.02      | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK2
% 43.67/6.02      | sK2 != sK3 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_26470]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_6,plain,
% 43.67/6.02      ( r2_hidden(X0,X1)
% 43.67/6.02      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 43.67/6.02      inference(cnf_transformation,[],[f83]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_1372,plain,
% 43.67/6.02      ( r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 43.67/6.02      | ~ r2_hidden(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_6]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_31576,plain,
% 43.67/6.02      ( r2_hidden(sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 43.67/6.02      | ~ r2_hidden(sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_1372]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_31579,plain,
% 43.67/6.02      ( r2_hidden(sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top
% 43.67/6.02      | r2_hidden(sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != iProver_top ),
% 43.67/6.02      inference(predicate_to_equality,[status(thm)],[c_31576]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_31581,plain,
% 43.67/6.02      ( r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top
% 43.67/6.02      | r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != iProver_top ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_31579]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_45951,plain,
% 43.67/6.02      ( sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK2
% 43.67/6.02      | sK2 != sK3
% 43.67/6.02      | r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = iProver_top
% 43.67/6.02      | r2_hidden(sK2,sK4) = iProver_top ),
% 43.67/6.02      inference(predicate_to_equality,[status(thm)],[c_45950]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_47206,plain,
% 43.67/6.02      ( sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK2
% 43.67/6.02      | sK2 != sK3 ),
% 43.67/6.02      inference(global_propositional_subsumption,
% 43.67/6.02                [status(thm)],
% 43.67/6.02                [c_45950,c_19,c_24,c_27,c_28,c_1088,c_1370,c_15310,
% 43.67/6.02                 c_26475,c_31581,c_45951]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_48305,plain,
% 43.67/6.02      ( X0 != sK2
% 43.67/6.02      | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = X0
% 43.67/6.02      | sK2 != sK3 ),
% 43.67/6.02      inference(resolution,[status(thm)],[c_47206,c_154]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_12,plain,
% 43.67/6.02      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X2)) ),
% 43.67/6.02      inference(cnf_transformation,[],[f87]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_679,plain,
% 43.67/6.02      ( r2_hidden(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,sK2,sK3)) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_12]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_683,plain,
% 43.67/6.02      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_679]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_419,plain,
% 43.67/6.02      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 43.67/6.02      | sK2 != sK3
% 43.67/6.02      | r2_hidden(sK2,sK4) = iProver_top ),
% 43.67/6.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_22,plain,
% 43.67/6.02      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 43.67/6.02      | sK2 != sK3
% 43.67/6.02      | r2_hidden(sK2,sK4) = iProver_top ),
% 43.67/6.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_1738,plain,
% 43.67/6.02      ( sK2 != sK3
% 43.67/6.02      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 43.67/6.02      inference(global_propositional_subsumption,
% 43.67/6.02                [status(thm)],
% 43.67/6.02                [c_419,c_19,c_22,c_24,c_27,c_28,c_1088,c_1370]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_1739,plain,
% 43.67/6.02      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 43.67/6.02      | sK2 != sK3 ),
% 43.67/6.02      inference(renaming,[status(thm)],[c_1738]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_2779,plain,
% 43.67/6.02      ( ~ r2_hidden(sK2,sK4) ),
% 43.67/6.02      inference(predicate_to_equality_rev,[status(thm)],[c_2777]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_4,plain,
% 43.67/6.02      ( ~ r2_hidden(X0,X1)
% 43.67/6.02      | r2_hidden(X0,X2)
% 43.67/6.02      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 43.67/6.02      inference(cnf_transformation,[],[f81]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_635,plain,
% 43.67/6.02      ( r2_hidden(X0,X1)
% 43.67/6.02      | ~ r2_hidden(X0,k6_enumset1(X2,X2,X2,X2,X2,X2,X0,X3))
% 43.67/6.02      | r2_hidden(X0,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X0,X3),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X0,X3),X1))) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_4]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_2888,plain,
% 43.67/6.02      ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 43.67/6.02      | r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 43.67/6.02      | r2_hidden(sK2,sK4) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_635]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_3572,plain,
% 43.67/6.02      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_153]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_1025,plain,
% 43.67/6.02      ( X0 != X1
% 43.67/6.02      | X0 = k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4)
% 43.67/6.02      | k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4) != X1 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_154]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_10895,plain,
% 43.67/6.02      ( X0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X1,X2)
% 43.67/6.02      | X0 != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
% 43.67/6.02      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X1,X2) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_1025]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_47361,plain,
% 43.67/6.02      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0,X1) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
% 43.67/6.02      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0,X1)
% 43.67/6.02      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_10895]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_47362,plain,
% 43.67/6.02      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
% 43.67/6.02      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 43.67/6.02      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_47361]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_930,plain,
% 43.67/6.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 43.67/6.02      inference(resolution,[status(thm)],[c_157,c_153]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_48307,plain,
% 43.67/6.02      ( r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),X0)
% 43.67/6.02      | ~ r2_hidden(sK2,X0)
% 43.67/6.02      | sK2 != sK3 ),
% 43.67/6.02      inference(resolution,[status(thm)],[c_47206,c_930]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_9,plain,
% 43.67/6.02      ( ~ r2_hidden(sK1(X0,X1,X2,X3),X3)
% 43.67/6.02      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
% 43.67/6.02      | sK1(X0,X1,X2,X3) != X0 ),
% 43.67/6.02      inference(cnf_transformation,[],[f71]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_48394,plain,
% 43.67/6.02      ( ~ r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 43.67/6.02      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
% 43.67/6.02      | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != sK2
% 43.67/6.02      | sK2 != sK3 ),
% 43.67/6.02      inference(resolution,[status(thm)],[c_48307,c_9]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_49552,plain,
% 43.67/6.02      ( sK2 != sK3 ),
% 43.67/6.02      inference(global_propositional_subsumption,
% 43.67/6.02                [status(thm)],
% 43.67/6.02                [c_48305,c_683,c_1739,c_2779,c_2888,c_3572,c_47206,
% 43.67/6.02                 c_47362,c_48394]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_158,plain,
% 43.67/6.02      ( X0 != X1
% 43.67/6.02      | X2 != X3
% 43.67/6.02      | X4 != X5
% 43.67/6.02      | X6 != X7
% 43.67/6.02      | X8 != X9
% 43.67/6.02      | X10 != X11
% 43.67/6.02      | X12 != X13
% 43.67/6.02      | X14 != X15
% 43.67/6.02      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 43.67/6.02      theory(equality) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_5849,plain,
% 43.67/6.02      ( X0 != X1
% 43.67/6.02      | X2 != X3
% 43.67/6.02      | X4 != X5
% 43.67/6.02      | X6 != X7
% 43.67/6.02      | X8 != X9
% 43.67/6.02      | X10 != X11
% 43.67/6.02      | X12 != X13
% 43.67/6.02      | X14 != X15
% 43.67/6.02      | X16 != k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15)
% 43.67/6.02      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = X16 ),
% 43.67/6.02      inference(resolution,[status(thm)],[c_158,c_154]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_17,negated_conjecture,
% 43.67/6.02      ( r2_hidden(sK3,sK4)
% 43.67/6.02      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 43.67/6.02      | sK2 = sK3 ),
% 43.67/6.02      inference(cnf_transformation,[],[f79]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_29555,plain,
% 43.67/6.02      ( r2_hidden(sK3,sK4)
% 43.67/6.02      | X0 != sK2
% 43.67/6.02      | X1 != sK2
% 43.67/6.02      | X2 != sK2
% 43.67/6.02      | X3 != sK2
% 43.67/6.02      | X4 != sK2
% 43.67/6.02      | X5 != sK2
% 43.67/6.02      | X6 != sK2
% 43.67/6.02      | X7 != sK2
% 43.67/6.02      | k6_enumset1(X1,X0,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
% 43.67/6.02      | sK2 = sK3 ),
% 43.67/6.02      inference(resolution,[status(thm)],[c_5849,c_17]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_156,plain,
% 43.67/6.02      ( X0 != X1 | X2 != X3 | k5_xboole_0(X0,X2) = k5_xboole_0(X1,X3) ),
% 43.67/6.02      theory(equality) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_1129,plain,
% 43.67/6.02      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
% 43.67/6.02      | r2_hidden(X3,k5_xboole_0(X4,X5))
% 43.67/6.02      | X3 != X0
% 43.67/6.02      | X4 != X1
% 43.67/6.02      | X5 != X2 ),
% 43.67/6.02      inference(resolution,[status(thm)],[c_156,c_157]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_5914,plain,
% 43.67/6.02      ( ~ r2_hidden(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0)
% 43.67/6.02      | r2_hidden(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),X0)
% 43.67/6.02      | r2_hidden(sK3,sK4)
% 43.67/6.02      | sK2 = sK3 ),
% 43.67/6.02      inference(resolution,[status(thm)],[c_930,c_17]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_12927,plain,
% 43.67/6.02      ( r2_hidden(X0,k5_xboole_0(X1,X2))
% 43.67/6.02      | ~ r2_hidden(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X3,X4))
% 43.67/6.02      | r2_hidden(sK3,sK4)
% 43.67/6.02      | X1 != X3
% 43.67/6.02      | X2 != X4
% 43.67/6.02      | X0 != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
% 43.67/6.02      | sK2 = sK3 ),
% 43.67/6.02      inference(resolution,[status(thm)],[c_1129,c_5914]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_30233,plain,
% 43.67/6.02      ( r2_hidden(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(X8,X9))
% 43.67/6.02      | ~ r2_hidden(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X10,X11))
% 43.67/6.02      | r2_hidden(sK3,sK4)
% 43.67/6.02      | X8 != X10
% 43.67/6.02      | X9 != X11
% 43.67/6.02      | X1 != sK2
% 43.67/6.02      | X0 != sK2
% 43.67/6.02      | X2 != sK2
% 43.67/6.02      | X3 != sK2
% 43.67/6.02      | X4 != sK2
% 43.67/6.02      | X5 != sK2
% 43.67/6.02      | X6 != sK2
% 43.67/6.02      | X7 != sK2
% 43.67/6.02      | sK2 = sK3 ),
% 43.67/6.02      inference(resolution,[status(thm)],[c_29555,c_12927]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_593,plain,
% 43.67/6.02      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_154]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_594,plain,
% 43.67/6.02      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_593]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_671,plain,
% 43.67/6.02      ( ~ r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
% 43.67/6.02      | sK3 = X0
% 43.67/6.02      | sK3 = X1
% 43.67/6.02      | sK3 = X2 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_14]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_673,plain,
% 43.67/6.02      ( ~ r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 43.67/6.02      | sK3 = sK2 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_671]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_735,plain,
% 43.67/6.02      ( ~ r2_hidden(sK3,X0)
% 43.67/6.02      | r2_hidden(sK3,k5_xboole_0(X0,k3_xboole_0(X0,sK4)))
% 43.67/6.02      | r2_hidden(sK3,sK4) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_4]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_793,plain,
% 43.67/6.02      ( ~ r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3))
% 43.67/6.02      | r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3),sK4)))
% 43.67/6.02      | r2_hidden(sK3,sK4) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_735]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_796,plain,
% 43.67/6.02      ( ~ r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 43.67/6.02      | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 43.67/6.02      | r2_hidden(sK3,sK4) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_793]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_11,plain,
% 43.67/6.02      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
% 43.67/6.02      inference(cnf_transformation,[],[f85]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_794,plain,
% 43.67/6.02      ( r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK3)) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_11]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_800,plain,
% 43.67/6.02      ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_794]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_830,plain,
% 43.67/6.02      ( sK3 = sK3 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_153]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_5874,plain,
% 43.67/6.02      ( r2_hidden(sK3,sK4)
% 43.67/6.02      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
% 43.67/6.02      | sK2 = sK3 ),
% 43.67/6.02      inference(resolution,[status(thm)],[c_913,c_17]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_1636,plain,
% 43.67/6.02      ( r2_hidden(X0,X1) | ~ r2_hidden(sK3,X2) | X1 != X2 | X0 != sK3 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_157]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_4433,plain,
% 43.67/6.02      ( ~ r2_hidden(sK3,X0) | r2_hidden(sK3,X1) | X1 != X0 | sK3 != sK3 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_1636]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_9864,plain,
% 43.67/6.02      ( r2_hidden(sK3,X0)
% 43.67/6.02      | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,sK3),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,sK3),X3)))
% 43.67/6.02      | X0 != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,sK3),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,sK3),X3))
% 43.67/6.02      | sK3 != sK3 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_4433]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_36540,plain,
% 43.67/6.02      ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0,X1))
% 43.67/6.02      | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 43.67/6.02      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0,X1) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
% 43.67/6.02      | sK3 != sK3 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_9864]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_36542,plain,
% 43.67/6.02      ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 43.67/6.02      | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 43.67/6.02      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
% 43.67/6.02      | sK3 != sK3 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_36540]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_37274,plain,
% 43.67/6.02      ( r2_hidden(sK3,sK4) | sK2 = sK3 ),
% 43.67/6.02      inference(global_propositional_subsumption,
% 43.67/6.02                [status(thm)],
% 43.67/6.02                [c_30233,c_24,c_27,c_594,c_673,c_796,c_800,c_830,c_5874,
% 43.67/6.02                 c_36542]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_49558,plain,
% 43.67/6.02      ( r2_hidden(sK3,sK4) ),
% 43.67/6.02      inference(backward_subsumption_resolution,
% 43.67/6.02                [status(thm)],
% 43.67/6.02                [c_49552,c_37274]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_16,negated_conjecture,
% 43.67/6.02      ( ~ r2_hidden(sK3,sK4)
% 43.67/6.02      | r2_hidden(sK2,sK4)
% 43.67/6.02      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 43.67/6.02      inference(cnf_transformation,[],[f78]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_100204,plain,
% 43.67/6.02      ( r2_hidden(sK2,sK4)
% 43.67/6.02      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 43.67/6.02      inference(backward_subsumption_resolution,
% 43.67/6.02                [status(thm)],
% 43.67/6.02                [c_49558,c_16]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_100244,plain,
% 43.67/6.02      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 43.67/6.02      inference(global_propositional_subsumption,
% 43.67/6.02                [status(thm)],
% 43.67/6.02                [c_100204,c_16,c_683,c_1739,c_2779,c_2888,c_3572,c_37274,
% 43.67/6.02                 c_47206,c_47362,c_48394]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_5866,plain,
% 43.67/6.02      ( r2_hidden(sK1(X0,X1,X2,X3),X3)
% 43.67/6.02      | X3 = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)
% 43.67/6.02      | sK1(X0,X1,X2,X3) = X2
% 43.67/6.02      | sK1(X0,X1,X2,X3) = X1
% 43.67/6.02      | sK1(X0,X1,X2,X3) = X0 ),
% 43.67/6.02      inference(resolution,[status(thm)],[c_913,c_10]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_100900,plain,
% 43.67/6.02      ( r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 43.67/6.02      | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK2 ),
% 43.67/6.02      inference(resolution,[status(thm)],[c_100244,c_5866]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_3168,plain,
% 43.67/6.02      ( r2_hidden(sK1(sK2,X0,X1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 43.67/6.02      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0,X1) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
% 43.67/6.02      | sK1(sK2,X0,X1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = X1
% 43.67/6.02      | sK1(sK2,X0,X1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = X0
% 43.67/6.02      | sK1(sK2,X0,X1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK2 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_10]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_3172,plain,
% 43.67/6.02      ( r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 43.67/6.02      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
% 43.67/6.02      | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK2 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_3168]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_746,plain,
% 43.67/6.02      ( ~ r2_hidden(X0,X1)
% 43.67/6.02      | r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4)))
% 43.67/6.02      | X2 != X0
% 43.67/6.02      | k5_xboole_0(X3,k3_xboole_0(X3,X4)) != X1 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_157]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_1342,plain,
% 43.67/6.02      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
% 43.67/6.02      | ~ r2_hidden(X3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 43.67/6.02      | X0 != X3
% 43.67/6.02      | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_746]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_3571,plain,
% 43.67/6.02      ( ~ r2_hidden(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 43.67/6.02      | r2_hidden(X1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 43.67/6.02      | X1 != X0
% 43.67/6.02      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_1342]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_74915,plain,
% 43.67/6.02      ( ~ r2_hidden(X0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 43.67/6.02      | r2_hidden(sK1(X1,X2,X3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 43.67/6.02      | sK1(X1,X2,X3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != X0
% 43.67/6.02      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_3571]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_74917,plain,
% 43.67/6.02      ( r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 43.67/6.02      | ~ r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 43.67/6.02      | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != sK2
% 43.67/6.02      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_74915]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_101907,plain,
% 43.67/6.02      ( r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) ),
% 43.67/6.02      inference(global_propositional_subsumption,
% 43.67/6.02                [status(thm)],
% 43.67/6.02                [c_100900,c_16,c_683,c_1739,c_2779,c_2888,c_3172,c_3572,
% 43.67/6.02                 c_37274,c_47206,c_47362,c_48394,c_74917]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_102736,plain,
% 43.67/6.02      ( ~ r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),sK4) ),
% 43.67/6.02      inference(resolution,[status(thm)],[c_101907,c_5]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_1377,plain,
% 43.67/6.02      ( r2_hidden(X0,X1) | ~ r2_hidden(sK3,sK4) | X1 != sK4 | X0 != sK3 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_157]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_3122,plain,
% 43.67/6.02      ( r2_hidden(X0,sK4)
% 43.67/6.02      | ~ r2_hidden(sK3,sK4)
% 43.67/6.02      | X0 != sK3
% 43.67/6.02      | sK4 != sK4 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_1377]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_77348,plain,
% 43.67/6.02      ( r2_hidden(sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),sK4)
% 43.67/6.02      | ~ r2_hidden(sK3,sK4)
% 43.67/6.02      | sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != sK3
% 43.67/6.02      | sK4 != sK4 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_3122]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_77350,plain,
% 43.67/6.02      ( r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),sK4)
% 43.67/6.02      | ~ r2_hidden(sK3,sK4)
% 43.67/6.02      | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != sK3
% 43.67/6.02      | sK4 != sK4 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_77348]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_31580,plain,
% 43.67/6.02      ( r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 43.67/6.02      | ~ r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_31576]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_15309,plain,
% 43.67/6.02      ( ~ r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 43.67/6.02      | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK3
% 43.67/6.02      | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) = sK2 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_15307]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_3123,plain,
% 43.67/6.02      ( sK4 = sK4 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_153]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_7,plain,
% 43.67/6.02      ( ~ r2_hidden(sK1(X0,X1,X2,X3),X3)
% 43.67/6.02      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
% 43.67/6.02      | sK1(X0,X1,X2,X3) != X2 ),
% 43.67/6.02      inference(cnf_transformation,[],[f69]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_2012,plain,
% 43.67/6.02      ( ~ r2_hidden(sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 43.67/6.02      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
% 43.67/6.02      | sK1(X0,X1,X2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != X2 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_7]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(c_2015,plain,
% 43.67/6.02      ( ~ r2_hidden(sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)))
% 43.67/6.02      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
% 43.67/6.02      | sK1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))) != sK2 ),
% 43.67/6.02      inference(instantiation,[status(thm)],[c_2012]) ).
% 43.67/6.02  
% 43.67/6.02  cnf(contradiction,plain,
% 43.67/6.02      ( $false ),
% 43.67/6.02      inference(minisat,
% 43.67/6.02                [status(thm)],
% 43.67/6.02                [c_102736,c_101907,c_77350,c_49552,c_47362,c_37274,
% 43.67/6.02                 c_31580,c_15309,c_3572,c_3123,c_2779,c_2015,c_16]) ).
% 43.67/6.02  
% 43.67/6.02  
% 43.67/6.02  % SZS output end CNFRefutation for theBenchmark.p
% 43.67/6.02  
% 43.67/6.02  ------                               Statistics
% 43.67/6.02  
% 43.67/6.02  ------ Selected
% 43.67/6.02  
% 43.67/6.02  total_time:                             5.391
% 43.67/6.02  
%------------------------------------------------------------------------------
