%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:05 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 321 expanded)
%              Number of clauses        :   50 (  57 expanded)
%              Number of leaves         :   23 (  93 expanded)
%              Depth                    :   20
%              Number of atoms          :  322 ( 648 expanded)
%              Number of equality atoms :  233 ( 519 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f64,f70])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f63,f71])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f72])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f73])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f60,f74])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f67,f75,f75])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( X0 = X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ( X0 = X1
          | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) )
        & ( X0 != X1
          | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) )
   => ( ( sK3 = sK4
        | k4_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k1_tarski(sK3) )
      & ( sK3 != sK4
        | k4_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k1_tarski(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( sK3 = sK4
      | k4_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k1_tarski(sK3) )
    & ( sK3 != sK4
      | k4_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k1_tarski(sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f38,f39])).

fof(f69,plain,
    ( sK3 = sK4
    | k4_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f86,plain,
    ( sK3 = sK4
    | k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f69,f49,f75,f75,f75])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f68,plain,
    ( sK3 != sK4
    | k4_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f87,plain,
    ( sK3 != sK4
    | k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f68,f49,f75,f75,f75])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f44,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f29])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

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
    inference(nnf_transformation,[],[f25])).

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
    inference(flattening,[],[f33])).

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
    inference(rectify,[],[f34])).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f53,f73])).

fof(f92,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f83])).

fof(f93,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f92])).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f52,f73])).

fof(f94,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f84])).

cnf(c_18,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1182,plain,
    ( X0 = X1
    | r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1196,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1698,plain,
    ( X0 = X1
    | k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1182,c_1196])).

cnf(c_19,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | sK3 = sK4 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_8863,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k1_xboole_0) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_1698,c_19])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_8864,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | sK4 = sK3 ),
    inference(demodulation,[status(thm)],[c_8863,c_8])).

cnf(c_8865,plain,
    ( sK4 = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_8864])).

cnf(c_20,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | sK3 != sK4 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_9567,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | sK3 != sK3 ),
    inference(demodulation,[status(thm)],[c_8865,c_20])).

cnf(c_9569,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_9567])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_9570,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_9569,c_3])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_7,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1192,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1461,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1192])).

cnf(c_1702,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1461,c_1196])).

cnf(c_9599,plain,
    ( k3_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9570,c_1702])).

cnf(c_9604,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9599,c_3])).

cnf(c_791,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1554,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_3591,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1554])).

cnf(c_7663,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != k1_xboole_0
    | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3591])).

cnf(c_7665,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k1_xboole_0
    | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7663])).

cnf(c_790,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_7191,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_790])).

cnf(c_794,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1277,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k3_xboole_0(X3,X4))
    | X2 != X0
    | k3_xboole_0(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_1609,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k3_xboole_0(k3_xboole_0(X3,X4),k5_xboole_0(X3,X4)))
    | X2 != X0
    | k3_xboole_0(k3_xboole_0(X3,X4),k5_xboole_0(X3,X4)) != X1 ),
    inference(instantiation,[status(thm)],[c_1277])).

cnf(c_1963,plain,
    ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)))
    | ~ r2_hidden(X3,k1_xboole_0)
    | X0 != X3
    | k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1609])).

cnf(c_1980,plain,
    ( r2_hidden(sK3,k3_xboole_0(k3_xboole_0(sK3,sK3),k5_xboole_0(sK3,sK3)))
    | ~ r2_hidden(sK3,k1_xboole_0)
    | k3_xboole_0(k3_xboole_0(sK3,sK3),k5_xboole_0(sK3,sK3)) != k1_xboole_0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1963])).

cnf(c_1321,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2))
    | X0 != X2
    | X1 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2) ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_1365,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))
    | r2_hidden(X3,k1_xboole_0)
    | X3 != X0
    | k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0) ),
    inference(instantiation,[status(thm)],[c_1321])).

cnf(c_1367,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | r2_hidden(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1365])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_295,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | k5_xboole_0(X3,X4) != X2
    | k3_xboole_0(X3,X4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_7])).

cnf(c_296,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_298,plain,
    ( ~ r2_hidden(sK3,k3_xboole_0(k3_xboole_0(sK3,sK3),k5_xboole_0(sK3,sK3))) ),
    inference(instantiation,[status(thm)],[c_296])).

cnf(c_136,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_274,plain,
    ( k5_xboole_0(X0,X1) != X2
    | k3_xboole_0(X0,X1) != X3
    | k3_xboole_0(X3,X2) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_136,c_7])).

cnf(c_275,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_276,plain,
    ( k3_xboole_0(k3_xboole_0(sK3,sK3),k5_xboole_0(sK3,sK3)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_275])).

cnf(c_16,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_28,plain,
    ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_25,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9604,c_7665,c_7191,c_1980,c_1367,c_298,c_276,c_28,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.73/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.00  
% 3.73/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.73/1.00  
% 3.73/1.00  ------  iProver source info
% 3.73/1.00  
% 3.73/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.73/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.73/1.00  git: non_committed_changes: false
% 3.73/1.00  git: last_make_outside_of_git: false
% 3.73/1.00  
% 3.73/1.00  ------ 
% 3.73/1.00  
% 3.73/1.00  ------ Input Options
% 3.73/1.00  
% 3.73/1.00  --out_options                           all
% 3.73/1.00  --tptp_safe_out                         true
% 3.73/1.00  --problem_path                          ""
% 3.73/1.00  --include_path                          ""
% 3.73/1.00  --clausifier                            res/vclausify_rel
% 3.73/1.00  --clausifier_options                    ""
% 3.73/1.00  --stdin                                 false
% 3.73/1.00  --stats_out                             all
% 3.73/1.00  
% 3.73/1.00  ------ General Options
% 3.73/1.00  
% 3.73/1.00  --fof                                   false
% 3.73/1.00  --time_out_real                         305.
% 3.73/1.00  --time_out_virtual                      -1.
% 3.73/1.00  --symbol_type_check                     false
% 3.73/1.00  --clausify_out                          false
% 3.73/1.00  --sig_cnt_out                           false
% 3.73/1.00  --trig_cnt_out                          false
% 3.73/1.00  --trig_cnt_out_tolerance                1.
% 3.73/1.00  --trig_cnt_out_sk_spl                   false
% 3.73/1.00  --abstr_cl_out                          false
% 3.73/1.00  
% 3.73/1.00  ------ Global Options
% 3.73/1.00  
% 3.73/1.00  --schedule                              default
% 3.73/1.00  --add_important_lit                     false
% 3.73/1.00  --prop_solver_per_cl                    1000
% 3.73/1.00  --min_unsat_core                        false
% 3.73/1.00  --soft_assumptions                      false
% 3.73/1.00  --soft_lemma_size                       3
% 3.73/1.00  --prop_impl_unit_size                   0
% 3.73/1.00  --prop_impl_unit                        []
% 3.73/1.00  --share_sel_clauses                     true
% 3.73/1.00  --reset_solvers                         false
% 3.73/1.00  --bc_imp_inh                            [conj_cone]
% 3.73/1.00  --conj_cone_tolerance                   3.
% 3.73/1.00  --extra_neg_conj                        none
% 3.73/1.00  --large_theory_mode                     true
% 3.73/1.00  --prolific_symb_bound                   200
% 3.73/1.00  --lt_threshold                          2000
% 3.73/1.00  --clause_weak_htbl                      true
% 3.73/1.00  --gc_record_bc_elim                     false
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing Options
% 3.73/1.00  
% 3.73/1.00  --preprocessing_flag                    true
% 3.73/1.00  --time_out_prep_mult                    0.1
% 3.73/1.00  --splitting_mode                        input
% 3.73/1.00  --splitting_grd                         true
% 3.73/1.00  --splitting_cvd                         false
% 3.73/1.00  --splitting_cvd_svl                     false
% 3.73/1.00  --splitting_nvd                         32
% 3.73/1.00  --sub_typing                            true
% 3.73/1.00  --prep_gs_sim                           true
% 3.73/1.00  --prep_unflatten                        true
% 3.73/1.00  --prep_res_sim                          true
% 3.73/1.00  --prep_upred                            true
% 3.73/1.00  --prep_sem_filter                       exhaustive
% 3.73/1.00  --prep_sem_filter_out                   false
% 3.73/1.00  --pred_elim                             true
% 3.73/1.00  --res_sim_input                         true
% 3.73/1.00  --eq_ax_congr_red                       true
% 3.73/1.00  --pure_diseq_elim                       true
% 3.73/1.00  --brand_transform                       false
% 3.73/1.00  --non_eq_to_eq                          false
% 3.73/1.00  --prep_def_merge                        true
% 3.73/1.00  --prep_def_merge_prop_impl              false
% 3.73/1.00  --prep_def_merge_mbd                    true
% 3.73/1.00  --prep_def_merge_tr_red                 false
% 3.73/1.00  --prep_def_merge_tr_cl                  false
% 3.73/1.00  --smt_preprocessing                     true
% 3.73/1.00  --smt_ac_axioms                         fast
% 3.73/1.00  --preprocessed_out                      false
% 3.73/1.00  --preprocessed_stats                    false
% 3.73/1.00  
% 3.73/1.00  ------ Abstraction refinement Options
% 3.73/1.00  
% 3.73/1.00  --abstr_ref                             []
% 3.73/1.00  --abstr_ref_prep                        false
% 3.73/1.00  --abstr_ref_until_sat                   false
% 3.73/1.00  --abstr_ref_sig_restrict                funpre
% 3.73/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.73/1.00  --abstr_ref_under                       []
% 3.73/1.00  
% 3.73/1.00  ------ SAT Options
% 3.73/1.00  
% 3.73/1.00  --sat_mode                              false
% 3.73/1.00  --sat_fm_restart_options                ""
% 3.73/1.00  --sat_gr_def                            false
% 3.73/1.00  --sat_epr_types                         true
% 3.73/1.00  --sat_non_cyclic_types                  false
% 3.73/1.00  --sat_finite_models                     false
% 3.73/1.00  --sat_fm_lemmas                         false
% 3.73/1.00  --sat_fm_prep                           false
% 3.73/1.00  --sat_fm_uc_incr                        true
% 3.73/1.00  --sat_out_model                         small
% 3.73/1.00  --sat_out_clauses                       false
% 3.73/1.00  
% 3.73/1.00  ------ QBF Options
% 3.73/1.00  
% 3.73/1.00  --qbf_mode                              false
% 3.73/1.00  --qbf_elim_univ                         false
% 3.73/1.00  --qbf_dom_inst                          none
% 3.73/1.00  --qbf_dom_pre_inst                      false
% 3.73/1.00  --qbf_sk_in                             false
% 3.73/1.00  --qbf_pred_elim                         true
% 3.73/1.00  --qbf_split                             512
% 3.73/1.00  
% 3.73/1.00  ------ BMC1 Options
% 3.73/1.00  
% 3.73/1.00  --bmc1_incremental                      false
% 3.73/1.00  --bmc1_axioms                           reachable_all
% 3.73/1.00  --bmc1_min_bound                        0
% 3.73/1.00  --bmc1_max_bound                        -1
% 3.73/1.00  --bmc1_max_bound_default                -1
% 3.73/1.00  --bmc1_symbol_reachability              true
% 3.73/1.00  --bmc1_property_lemmas                  false
% 3.73/1.00  --bmc1_k_induction                      false
% 3.73/1.00  --bmc1_non_equiv_states                 false
% 3.73/1.00  --bmc1_deadlock                         false
% 3.73/1.00  --bmc1_ucm                              false
% 3.73/1.00  --bmc1_add_unsat_core                   none
% 3.73/1.00  --bmc1_unsat_core_children              false
% 3.73/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.73/1.00  --bmc1_out_stat                         full
% 3.73/1.00  --bmc1_ground_init                      false
% 3.73/1.00  --bmc1_pre_inst_next_state              false
% 3.73/1.00  --bmc1_pre_inst_state                   false
% 3.73/1.00  --bmc1_pre_inst_reach_state             false
% 3.73/1.00  --bmc1_out_unsat_core                   false
% 3.73/1.00  --bmc1_aig_witness_out                  false
% 3.73/1.00  --bmc1_verbose                          false
% 3.73/1.00  --bmc1_dump_clauses_tptp                false
% 3.73/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.73/1.00  --bmc1_dump_file                        -
% 3.73/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.73/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.73/1.00  --bmc1_ucm_extend_mode                  1
% 3.73/1.00  --bmc1_ucm_init_mode                    2
% 3.73/1.00  --bmc1_ucm_cone_mode                    none
% 3.73/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.73/1.00  --bmc1_ucm_relax_model                  4
% 3.73/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.73/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.73/1.00  --bmc1_ucm_layered_model                none
% 3.73/1.00  --bmc1_ucm_max_lemma_size               10
% 3.73/1.00  
% 3.73/1.00  ------ AIG Options
% 3.73/1.00  
% 3.73/1.00  --aig_mode                              false
% 3.73/1.00  
% 3.73/1.00  ------ Instantiation Options
% 3.73/1.00  
% 3.73/1.00  --instantiation_flag                    true
% 3.73/1.00  --inst_sos_flag                         true
% 3.73/1.00  --inst_sos_phase                        true
% 3.73/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.73/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.73/1.00  --inst_lit_sel_side                     num_symb
% 3.73/1.00  --inst_solver_per_active                1400
% 3.73/1.00  --inst_solver_calls_frac                1.
% 3.73/1.00  --inst_passive_queue_type               priority_queues
% 3.73/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.73/1.00  --inst_passive_queues_freq              [25;2]
% 3.73/1.00  --inst_dismatching                      true
% 3.73/1.00  --inst_eager_unprocessed_to_passive     true
% 3.73/1.00  --inst_prop_sim_given                   true
% 3.73/1.00  --inst_prop_sim_new                     false
% 3.73/1.00  --inst_subs_new                         false
% 3.73/1.00  --inst_eq_res_simp                      false
% 3.73/1.00  --inst_subs_given                       false
% 3.73/1.00  --inst_orphan_elimination               true
% 3.73/1.00  --inst_learning_loop_flag               true
% 3.73/1.00  --inst_learning_start                   3000
% 3.73/1.00  --inst_learning_factor                  2
% 3.73/1.00  --inst_start_prop_sim_after_learn       3
% 3.73/1.00  --inst_sel_renew                        solver
% 3.73/1.00  --inst_lit_activity_flag                true
% 3.73/1.00  --inst_restr_to_given                   false
% 3.73/1.00  --inst_activity_threshold               500
% 3.73/1.00  --inst_out_proof                        true
% 3.73/1.00  
% 3.73/1.00  ------ Resolution Options
% 3.73/1.00  
% 3.73/1.00  --resolution_flag                       true
% 3.73/1.00  --res_lit_sel                           adaptive
% 3.73/1.00  --res_lit_sel_side                      none
% 3.73/1.00  --res_ordering                          kbo
% 3.73/1.00  --res_to_prop_solver                    active
% 3.73/1.00  --res_prop_simpl_new                    false
% 3.73/1.00  --res_prop_simpl_given                  true
% 3.73/1.00  --res_passive_queue_type                priority_queues
% 3.73/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.73/1.00  --res_passive_queues_freq               [15;5]
% 3.73/1.00  --res_forward_subs                      full
% 3.73/1.00  --res_backward_subs                     full
% 3.73/1.00  --res_forward_subs_resolution           true
% 3.73/1.00  --res_backward_subs_resolution          true
% 3.73/1.00  --res_orphan_elimination                true
% 3.73/1.00  --res_time_limit                        2.
% 3.73/1.00  --res_out_proof                         true
% 3.73/1.00  
% 3.73/1.00  ------ Superposition Options
% 3.73/1.00  
% 3.73/1.00  --superposition_flag                    true
% 3.73/1.00  --sup_passive_queue_type                priority_queues
% 3.73/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.73/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.73/1.00  --demod_completeness_check              fast
% 3.73/1.00  --demod_use_ground                      true
% 3.73/1.00  --sup_to_prop_solver                    passive
% 3.73/1.00  --sup_prop_simpl_new                    true
% 3.73/1.00  --sup_prop_simpl_given                  true
% 3.73/1.00  --sup_fun_splitting                     true
% 3.73/1.00  --sup_smt_interval                      50000
% 3.73/1.00  
% 3.73/1.00  ------ Superposition Simplification Setup
% 3.73/1.00  
% 3.73/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.73/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.73/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.73/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.73/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.73/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.73/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.73/1.00  --sup_immed_triv                        [TrivRules]
% 3.73/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.00  --sup_immed_bw_main                     []
% 3.73/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.73/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.73/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.00  --sup_input_bw                          []
% 3.73/1.00  
% 3.73/1.00  ------ Combination Options
% 3.73/1.00  
% 3.73/1.00  --comb_res_mult                         3
% 3.73/1.00  --comb_sup_mult                         2
% 3.73/1.00  --comb_inst_mult                        10
% 3.73/1.00  
% 3.73/1.00  ------ Debug Options
% 3.73/1.00  
% 3.73/1.00  --dbg_backtrace                         false
% 3.73/1.00  --dbg_dump_prop_clauses                 false
% 3.73/1.00  --dbg_dump_prop_clauses_file            -
% 3.73/1.00  --dbg_out_stat                          false
% 3.73/1.00  ------ Parsing...
% 3.73/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  ------ Proving...
% 3.73/1.00  ------ Problem Properties 
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  clauses                                 21
% 3.73/1.00  conjectures                             2
% 3.73/1.00  EPR                                     0
% 3.73/1.00  Horn                                    16
% 3.73/1.00  unary                                   8
% 3.73/1.00  binary                                  8
% 3.73/1.00  lits                                    42
% 3.73/1.00  lits eq                                 24
% 3.73/1.00  fd_pure                                 0
% 3.73/1.00  fd_pseudo                               0
% 3.73/1.00  fd_cond                                 1
% 3.73/1.00  fd_pseudo_cond                          5
% 3.73/1.00  AC symbols                              0
% 3.73/1.00  
% 3.73/1.00  ------ Schedule dynamic 5 is on 
% 3.73/1.00  
% 3.73/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ 
% 3.73/1.00  Current options:
% 3.73/1.00  ------ 
% 3.73/1.00  
% 3.73/1.00  ------ Input Options
% 3.73/1.00  
% 3.73/1.00  --out_options                           all
% 3.73/1.00  --tptp_safe_out                         true
% 3.73/1.00  --problem_path                          ""
% 3.73/1.00  --include_path                          ""
% 3.73/1.00  --clausifier                            res/vclausify_rel
% 3.73/1.00  --clausifier_options                    ""
% 3.73/1.00  --stdin                                 false
% 3.73/1.00  --stats_out                             all
% 3.73/1.00  
% 3.73/1.00  ------ General Options
% 3.73/1.00  
% 3.73/1.00  --fof                                   false
% 3.73/1.00  --time_out_real                         305.
% 3.73/1.00  --time_out_virtual                      -1.
% 3.73/1.00  --symbol_type_check                     false
% 3.73/1.00  --clausify_out                          false
% 3.73/1.00  --sig_cnt_out                           false
% 3.73/1.00  --trig_cnt_out                          false
% 3.73/1.00  --trig_cnt_out_tolerance                1.
% 3.73/1.00  --trig_cnt_out_sk_spl                   false
% 3.73/1.00  --abstr_cl_out                          false
% 3.73/1.00  
% 3.73/1.00  ------ Global Options
% 3.73/1.00  
% 3.73/1.00  --schedule                              default
% 3.73/1.00  --add_important_lit                     false
% 3.73/1.00  --prop_solver_per_cl                    1000
% 3.73/1.00  --min_unsat_core                        false
% 3.73/1.00  --soft_assumptions                      false
% 3.73/1.00  --soft_lemma_size                       3
% 3.73/1.00  --prop_impl_unit_size                   0
% 3.73/1.00  --prop_impl_unit                        []
% 3.73/1.00  --share_sel_clauses                     true
% 3.73/1.00  --reset_solvers                         false
% 3.73/1.00  --bc_imp_inh                            [conj_cone]
% 3.73/1.00  --conj_cone_tolerance                   3.
% 3.73/1.00  --extra_neg_conj                        none
% 3.73/1.00  --large_theory_mode                     true
% 3.73/1.00  --prolific_symb_bound                   200
% 3.73/1.00  --lt_threshold                          2000
% 3.73/1.00  --clause_weak_htbl                      true
% 3.73/1.00  --gc_record_bc_elim                     false
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing Options
% 3.73/1.00  
% 3.73/1.00  --preprocessing_flag                    true
% 3.73/1.00  --time_out_prep_mult                    0.1
% 3.73/1.00  --splitting_mode                        input
% 3.73/1.00  --splitting_grd                         true
% 3.73/1.00  --splitting_cvd                         false
% 3.73/1.00  --splitting_cvd_svl                     false
% 3.73/1.00  --splitting_nvd                         32
% 3.73/1.00  --sub_typing                            true
% 3.73/1.00  --prep_gs_sim                           true
% 3.73/1.00  --prep_unflatten                        true
% 3.73/1.00  --prep_res_sim                          true
% 3.73/1.00  --prep_upred                            true
% 3.73/1.00  --prep_sem_filter                       exhaustive
% 3.73/1.00  --prep_sem_filter_out                   false
% 3.73/1.00  --pred_elim                             true
% 3.73/1.00  --res_sim_input                         true
% 3.73/1.00  --eq_ax_congr_red                       true
% 3.73/1.00  --pure_diseq_elim                       true
% 3.73/1.00  --brand_transform                       false
% 3.73/1.00  --non_eq_to_eq                          false
% 3.73/1.00  --prep_def_merge                        true
% 3.73/1.00  --prep_def_merge_prop_impl              false
% 3.73/1.00  --prep_def_merge_mbd                    true
% 3.73/1.00  --prep_def_merge_tr_red                 false
% 3.73/1.00  --prep_def_merge_tr_cl                  false
% 3.73/1.00  --smt_preprocessing                     true
% 3.73/1.00  --smt_ac_axioms                         fast
% 3.73/1.00  --preprocessed_out                      false
% 3.73/1.00  --preprocessed_stats                    false
% 3.73/1.00  
% 3.73/1.00  ------ Abstraction refinement Options
% 3.73/1.00  
% 3.73/1.00  --abstr_ref                             []
% 3.73/1.00  --abstr_ref_prep                        false
% 3.73/1.00  --abstr_ref_until_sat                   false
% 3.73/1.00  --abstr_ref_sig_restrict                funpre
% 3.73/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.73/1.00  --abstr_ref_under                       []
% 3.73/1.00  
% 3.73/1.00  ------ SAT Options
% 3.73/1.00  
% 3.73/1.00  --sat_mode                              false
% 3.73/1.00  --sat_fm_restart_options                ""
% 3.73/1.00  --sat_gr_def                            false
% 3.73/1.00  --sat_epr_types                         true
% 3.73/1.00  --sat_non_cyclic_types                  false
% 3.73/1.00  --sat_finite_models                     false
% 3.73/1.00  --sat_fm_lemmas                         false
% 3.73/1.00  --sat_fm_prep                           false
% 3.73/1.00  --sat_fm_uc_incr                        true
% 3.73/1.00  --sat_out_model                         small
% 3.73/1.00  --sat_out_clauses                       false
% 3.73/1.00  
% 3.73/1.00  ------ QBF Options
% 3.73/1.00  
% 3.73/1.00  --qbf_mode                              false
% 3.73/1.00  --qbf_elim_univ                         false
% 3.73/1.00  --qbf_dom_inst                          none
% 3.73/1.00  --qbf_dom_pre_inst                      false
% 3.73/1.00  --qbf_sk_in                             false
% 3.73/1.00  --qbf_pred_elim                         true
% 3.73/1.00  --qbf_split                             512
% 3.73/1.00  
% 3.73/1.00  ------ BMC1 Options
% 3.73/1.00  
% 3.73/1.00  --bmc1_incremental                      false
% 3.73/1.00  --bmc1_axioms                           reachable_all
% 3.73/1.00  --bmc1_min_bound                        0
% 3.73/1.00  --bmc1_max_bound                        -1
% 3.73/1.00  --bmc1_max_bound_default                -1
% 3.73/1.00  --bmc1_symbol_reachability              true
% 3.73/1.00  --bmc1_property_lemmas                  false
% 3.73/1.00  --bmc1_k_induction                      false
% 3.73/1.00  --bmc1_non_equiv_states                 false
% 3.73/1.00  --bmc1_deadlock                         false
% 3.73/1.00  --bmc1_ucm                              false
% 3.73/1.00  --bmc1_add_unsat_core                   none
% 3.73/1.00  --bmc1_unsat_core_children              false
% 3.73/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.73/1.00  --bmc1_out_stat                         full
% 3.73/1.00  --bmc1_ground_init                      false
% 3.73/1.00  --bmc1_pre_inst_next_state              false
% 3.73/1.00  --bmc1_pre_inst_state                   false
% 3.73/1.00  --bmc1_pre_inst_reach_state             false
% 3.73/1.00  --bmc1_out_unsat_core                   false
% 3.73/1.00  --bmc1_aig_witness_out                  false
% 3.73/1.00  --bmc1_verbose                          false
% 3.73/1.00  --bmc1_dump_clauses_tptp                false
% 3.73/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.73/1.00  --bmc1_dump_file                        -
% 3.73/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.73/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.73/1.00  --bmc1_ucm_extend_mode                  1
% 3.73/1.00  --bmc1_ucm_init_mode                    2
% 3.73/1.00  --bmc1_ucm_cone_mode                    none
% 3.73/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.73/1.00  --bmc1_ucm_relax_model                  4
% 3.73/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.73/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.73/1.00  --bmc1_ucm_layered_model                none
% 3.73/1.00  --bmc1_ucm_max_lemma_size               10
% 3.73/1.00  
% 3.73/1.00  ------ AIG Options
% 3.73/1.00  
% 3.73/1.00  --aig_mode                              false
% 3.73/1.00  
% 3.73/1.00  ------ Instantiation Options
% 3.73/1.00  
% 3.73/1.00  --instantiation_flag                    true
% 3.73/1.00  --inst_sos_flag                         true
% 3.73/1.00  --inst_sos_phase                        true
% 3.73/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.73/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.73/1.00  --inst_lit_sel_side                     none
% 3.73/1.00  --inst_solver_per_active                1400
% 3.73/1.00  --inst_solver_calls_frac                1.
% 3.73/1.00  --inst_passive_queue_type               priority_queues
% 3.73/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.73/1.00  --inst_passive_queues_freq              [25;2]
% 3.73/1.00  --inst_dismatching                      true
% 3.73/1.00  --inst_eager_unprocessed_to_passive     true
% 3.73/1.00  --inst_prop_sim_given                   true
% 3.73/1.00  --inst_prop_sim_new                     false
% 3.73/1.00  --inst_subs_new                         false
% 3.73/1.00  --inst_eq_res_simp                      false
% 3.73/1.00  --inst_subs_given                       false
% 3.73/1.00  --inst_orphan_elimination               true
% 3.73/1.00  --inst_learning_loop_flag               true
% 3.73/1.00  --inst_learning_start                   3000
% 3.73/1.00  --inst_learning_factor                  2
% 3.73/1.00  --inst_start_prop_sim_after_learn       3
% 3.73/1.00  --inst_sel_renew                        solver
% 3.73/1.00  --inst_lit_activity_flag                true
% 3.73/1.00  --inst_restr_to_given                   false
% 3.73/1.00  --inst_activity_threshold               500
% 3.73/1.00  --inst_out_proof                        true
% 3.73/1.00  
% 3.73/1.00  ------ Resolution Options
% 3.73/1.00  
% 3.73/1.00  --resolution_flag                       false
% 3.73/1.00  --res_lit_sel                           adaptive
% 3.73/1.00  --res_lit_sel_side                      none
% 3.73/1.00  --res_ordering                          kbo
% 3.73/1.00  --res_to_prop_solver                    active
% 3.73/1.00  --res_prop_simpl_new                    false
% 3.73/1.00  --res_prop_simpl_given                  true
% 3.73/1.00  --res_passive_queue_type                priority_queues
% 3.73/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.73/1.00  --res_passive_queues_freq               [15;5]
% 3.73/1.00  --res_forward_subs                      full
% 3.73/1.00  --res_backward_subs                     full
% 3.73/1.00  --res_forward_subs_resolution           true
% 3.73/1.00  --res_backward_subs_resolution          true
% 3.73/1.00  --res_orphan_elimination                true
% 3.73/1.00  --res_time_limit                        2.
% 3.73/1.00  --res_out_proof                         true
% 3.73/1.00  
% 3.73/1.00  ------ Superposition Options
% 3.73/1.00  
% 3.73/1.00  --superposition_flag                    true
% 3.73/1.00  --sup_passive_queue_type                priority_queues
% 3.73/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.73/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.73/1.00  --demod_completeness_check              fast
% 3.73/1.00  --demod_use_ground                      true
% 3.73/1.00  --sup_to_prop_solver                    passive
% 3.73/1.00  --sup_prop_simpl_new                    true
% 3.73/1.00  --sup_prop_simpl_given                  true
% 3.73/1.00  --sup_fun_splitting                     true
% 3.73/1.00  --sup_smt_interval                      50000
% 3.73/1.00  
% 3.73/1.00  ------ Superposition Simplification Setup
% 3.73/1.00  
% 3.73/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.73/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.73/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.73/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.73/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.73/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.73/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.73/1.00  --sup_immed_triv                        [TrivRules]
% 3.73/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.00  --sup_immed_bw_main                     []
% 3.73/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.73/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.73/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.00  --sup_input_bw                          []
% 3.73/1.00  
% 3.73/1.00  ------ Combination Options
% 3.73/1.00  
% 3.73/1.00  --comb_res_mult                         3
% 3.73/1.00  --comb_sup_mult                         2
% 3.73/1.00  --comb_inst_mult                        10
% 3.73/1.00  
% 3.73/1.00  ------ Debug Options
% 3.73/1.00  
% 3.73/1.00  --dbg_backtrace                         false
% 3.73/1.00  --dbg_dump_prop_clauses                 false
% 3.73/1.00  --dbg_dump_prop_clauses_file            -
% 3.73/1.00  --dbg_out_stat                          false
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  % SZS status Theorem for theBenchmark.p
% 3.73/1.00  
% 3.73/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.73/1.00  
% 3.73/1.00  fof(f18,axiom,(
% 3.73/1.00    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f26,plain,(
% 3.73/1.00    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 3.73/1.00    inference(ennf_transformation,[],[f18])).
% 3.73/1.00  
% 3.73/1.00  fof(f67,plain,(
% 3.73/1.00    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 3.73/1.00    inference(cnf_transformation,[],[f26])).
% 3.73/1.00  
% 3.73/1.00  fof(f11,axiom,(
% 3.73/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f60,plain,(
% 3.73/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f11])).
% 3.73/1.00  
% 3.73/1.00  fof(f12,axiom,(
% 3.73/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f61,plain,(
% 3.73/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f12])).
% 3.73/1.00  
% 3.73/1.00  fof(f13,axiom,(
% 3.73/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f62,plain,(
% 3.73/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f13])).
% 3.73/1.00  
% 3.73/1.00  fof(f14,axiom,(
% 3.73/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f63,plain,(
% 3.73/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f14])).
% 3.73/1.00  
% 3.73/1.00  fof(f15,axiom,(
% 3.73/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f64,plain,(
% 3.73/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f15])).
% 3.73/1.00  
% 3.73/1.00  fof(f16,axiom,(
% 3.73/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f65,plain,(
% 3.73/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f16])).
% 3.73/1.00  
% 3.73/1.00  fof(f17,axiom,(
% 3.73/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f66,plain,(
% 3.73/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f17])).
% 3.73/1.00  
% 3.73/1.00  fof(f70,plain,(
% 3.73/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.73/1.00    inference(definition_unfolding,[],[f65,f66])).
% 3.73/1.00  
% 3.73/1.00  fof(f71,plain,(
% 3.73/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.73/1.00    inference(definition_unfolding,[],[f64,f70])).
% 3.73/1.00  
% 3.73/1.00  fof(f72,plain,(
% 3.73/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.73/1.00    inference(definition_unfolding,[],[f63,f71])).
% 3.73/1.00  
% 3.73/1.00  fof(f73,plain,(
% 3.73/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.73/1.00    inference(definition_unfolding,[],[f62,f72])).
% 3.73/1.00  
% 3.73/1.00  fof(f74,plain,(
% 3.73/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.73/1.00    inference(definition_unfolding,[],[f61,f73])).
% 3.73/1.00  
% 3.73/1.00  fof(f75,plain,(
% 3.73/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.73/1.00    inference(definition_unfolding,[],[f60,f74])).
% 3.73/1.00  
% 3.73/1.00  fof(f85,plain,(
% 3.73/1.00    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1) )),
% 3.73/1.00    inference(definition_unfolding,[],[f67,f75,f75])).
% 3.73/1.00  
% 3.73/1.00  fof(f2,axiom,(
% 3.73/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f28,plain,(
% 3.73/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.73/1.00    inference(nnf_transformation,[],[f2])).
% 3.73/1.00  
% 3.73/1.00  fof(f42,plain,(
% 3.73/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f28])).
% 3.73/1.00  
% 3.73/1.00  fof(f19,conjecture,(
% 3.73/1.00    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f20,negated_conjecture,(
% 3.73/1.00    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.73/1.00    inference(negated_conjecture,[],[f19])).
% 3.73/1.00  
% 3.73/1.00  fof(f27,plain,(
% 3.73/1.00    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <~> X0 != X1)),
% 3.73/1.00    inference(ennf_transformation,[],[f20])).
% 3.73/1.00  
% 3.73/1.00  fof(f38,plain,(
% 3.73/1.00    ? [X0,X1] : ((X0 = X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)))),
% 3.73/1.00    inference(nnf_transformation,[],[f27])).
% 3.73/1.00  
% 3.73/1.00  fof(f39,plain,(
% 3.73/1.00    ? [X0,X1] : ((X0 = X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))) => ((sK3 = sK4 | k4_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k1_tarski(sK3)) & (sK3 != sK4 | k4_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k1_tarski(sK3)))),
% 3.73/1.00    introduced(choice_axiom,[])).
% 3.73/1.00  
% 3.73/1.00  fof(f40,plain,(
% 3.73/1.00    (sK3 = sK4 | k4_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k1_tarski(sK3)) & (sK3 != sK4 | k4_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k1_tarski(sK3))),
% 3.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f38,f39])).
% 3.73/1.00  
% 3.73/1.00  fof(f69,plain,(
% 3.73/1.00    sK3 = sK4 | k4_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) != k1_tarski(sK3)),
% 3.73/1.00    inference(cnf_transformation,[],[f40])).
% 3.73/1.00  
% 3.73/1.00  fof(f7,axiom,(
% 3.73/1.00    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f49,plain,(
% 3.73/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f7])).
% 3.73/1.00  
% 3.73/1.00  fof(f86,plain,(
% 3.73/1.00    sK3 = sK4 | k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),
% 3.73/1.00    inference(definition_unfolding,[],[f69,f49,f75,f75,f75])).
% 3.73/1.00  
% 3.73/1.00  fof(f8,axiom,(
% 3.73/1.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f50,plain,(
% 3.73/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.73/1.00    inference(cnf_transformation,[],[f8])).
% 3.73/1.00  
% 3.73/1.00  fof(f68,plain,(
% 3.73/1.00    sK3 != sK4 | k4_xboole_0(k1_tarski(sK3),k1_tarski(sK4)) = k1_tarski(sK3)),
% 3.73/1.00    inference(cnf_transformation,[],[f40])).
% 3.73/1.00  
% 3.73/1.00  fof(f87,plain,(
% 3.73/1.00    sK3 != sK4 | k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),
% 3.73/1.00    inference(definition_unfolding,[],[f68,f49,f75,f75,f75])).
% 3.73/1.00  
% 3.73/1.00  fof(f3,axiom,(
% 3.73/1.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f21,plain,(
% 3.73/1.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.73/1.00    inference(rectify,[],[f3])).
% 3.73/1.00  
% 3.73/1.00  fof(f44,plain,(
% 3.73/1.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.73/1.00    inference(cnf_transformation,[],[f21])).
% 3.73/1.00  
% 3.73/1.00  fof(f1,axiom,(
% 3.73/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f41,plain,(
% 3.73/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f1])).
% 3.73/1.00  
% 3.73/1.00  fof(f6,axiom,(
% 3.73/1.00    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f48,plain,(
% 3.73/1.00    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 3.73/1.00    inference(cnf_transformation,[],[f6])).
% 3.73/1.00  
% 3.73/1.00  fof(f4,axiom,(
% 3.73/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f22,plain,(
% 3.73/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.73/1.00    inference(rectify,[],[f4])).
% 3.73/1.00  
% 3.73/1.00  fof(f23,plain,(
% 3.73/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.73/1.00    inference(ennf_transformation,[],[f22])).
% 3.73/1.00  
% 3.73/1.00  fof(f29,plain,(
% 3.73/1.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.73/1.00    introduced(choice_axiom,[])).
% 3.73/1.00  
% 3.73/1.00  fof(f30,plain,(
% 3.73/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f29])).
% 3.73/1.00  
% 3.73/1.00  fof(f46,plain,(
% 3.73/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.73/1.00    inference(cnf_transformation,[],[f30])).
% 3.73/1.00  
% 3.73/1.00  fof(f10,axiom,(
% 3.73/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f25,plain,(
% 3.73/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.73/1.00    inference(ennf_transformation,[],[f10])).
% 3.73/1.00  
% 3.73/1.00  fof(f33,plain,(
% 3.73/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.73/1.00    inference(nnf_transformation,[],[f25])).
% 3.73/1.00  
% 3.73/1.00  fof(f34,plain,(
% 3.73/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.73/1.00    inference(flattening,[],[f33])).
% 3.73/1.00  
% 3.73/1.00  fof(f35,plain,(
% 3.73/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.73/1.00    inference(rectify,[],[f34])).
% 3.73/1.00  
% 3.73/1.00  fof(f36,plain,(
% 3.73/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 3.73/1.00    introduced(choice_axiom,[])).
% 3.73/1.00  
% 3.73/1.00  fof(f37,plain,(
% 3.73/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 3.73/1.00  
% 3.73/1.00  fof(f53,plain,(
% 3.73/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.73/1.00    inference(cnf_transformation,[],[f37])).
% 3.73/1.00  
% 3.73/1.00  fof(f83,plain,(
% 3.73/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.73/1.00    inference(definition_unfolding,[],[f53,f73])).
% 3.73/1.00  
% 3.73/1.00  fof(f92,plain,(
% 3.73/1.00    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 3.73/1.00    inference(equality_resolution,[],[f83])).
% 3.73/1.00  
% 3.73/1.00  fof(f93,plain,(
% 3.73/1.00    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 3.73/1.00    inference(equality_resolution,[],[f92])).
% 3.73/1.00  
% 3.73/1.00  fof(f52,plain,(
% 3.73/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.73/1.00    inference(cnf_transformation,[],[f37])).
% 3.73/1.00  
% 3.73/1.00  fof(f84,plain,(
% 3.73/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.73/1.00    inference(definition_unfolding,[],[f52,f73])).
% 3.73/1.00  
% 3.73/1.00  fof(f94,plain,(
% 3.73/1.00    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 3.73/1.00    inference(equality_resolution,[],[f84])).
% 3.73/1.00  
% 3.73/1.00  cnf(c_18,plain,
% 3.73/1.00      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 3.73/1.00      | X1 = X0 ),
% 3.73/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1182,plain,
% 3.73/1.00      ( X0 = X1
% 3.73/1.00      | r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_2,plain,
% 3.73/1.00      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.73/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1196,plain,
% 3.73/1.00      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 3.73/1.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1698,plain,
% 3.73/1.00      ( X0 = X1
% 3.73/1.00      | k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k1_xboole_0 ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_1182,c_1196]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_19,negated_conjecture,
% 3.73/1.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 3.73/1.00      | sK3 = sK4 ),
% 3.73/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_8863,plain,
% 3.73/1.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k1_xboole_0) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 3.73/1.00      | sK4 = sK3 ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_1698,c_19]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_8,plain,
% 3.73/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.73/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_8864,plain,
% 3.73/1.00      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 3.73/1.00      | sK4 = sK3 ),
% 3.73/1.00      inference(demodulation,[status(thm)],[c_8863,c_8]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_8865,plain,
% 3.73/1.00      ( sK4 = sK3 ),
% 3.73/1.00      inference(equality_resolution_simp,[status(thm)],[c_8864]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_20,negated_conjecture,
% 3.73/1.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 3.73/1.00      | sK3 != sK4 ),
% 3.73/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_9567,plain,
% 3.73/1.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 3.73/1.00      | sK3 != sK3 ),
% 3.73/1.00      inference(demodulation,[status(thm)],[c_8865,c_20]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_9569,plain,
% 3.73/1.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 3.73/1.00      inference(equality_resolution_simp,[status(thm)],[c_9567]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3,plain,
% 3.73/1.00      ( k3_xboole_0(X0,X0) = X0 ),
% 3.73/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_9570,plain,
% 3.73/1.00      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 3.73/1.00      inference(demodulation,[status(thm)],[c_9569,c_3]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_0,plain,
% 3.73/1.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.73/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_7,plain,
% 3.73/1.00      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 3.73/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1192,plain,
% 3.73/1.00      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1461,plain,
% 3.73/1.00      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_0,c_1192]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1702,plain,
% 3.73/1.00      ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_1461,c_1196]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_9599,plain,
% 3.73/1.00      ( k3_xboole_0(k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k1_xboole_0 ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_9570,c_1702]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_9604,plain,
% 3.73/1.00      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 3.73/1.00      inference(demodulation,[status(thm)],[c_9599,c_3]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_791,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1554,plain,
% 3.73/1.00      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_791]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3591,plain,
% 3.73/1.00      ( X0 != k1_xboole_0
% 3.73/1.00      | k1_xboole_0 = X0
% 3.73/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_1554]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_7663,plain,
% 3.73/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != k1_xboole_0
% 3.73/1.00      | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)
% 3.73/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_3591]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_7665,plain,
% 3.73/1.00      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k1_xboole_0
% 3.73/1.00      | k1_xboole_0 = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 3.73/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_7663]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_790,plain,( X0 = X0 ),theory(equality) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_7191,plain,
% 3.73/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_790]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_794,plain,
% 3.73/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.73/1.00      theory(equality) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1277,plain,
% 3.73/1.00      ( ~ r2_hidden(X0,X1)
% 3.73/1.00      | r2_hidden(X2,k3_xboole_0(X3,X4))
% 3.73/1.00      | X2 != X0
% 3.73/1.00      | k3_xboole_0(X3,X4) != X1 ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_794]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1609,plain,
% 3.73/1.00      ( ~ r2_hidden(X0,X1)
% 3.73/1.00      | r2_hidden(X2,k3_xboole_0(k3_xboole_0(X3,X4),k5_xboole_0(X3,X4)))
% 3.73/1.00      | X2 != X0
% 3.73/1.00      | k3_xboole_0(k3_xboole_0(X3,X4),k5_xboole_0(X3,X4)) != X1 ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_1277]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1963,plain,
% 3.73/1.00      ( r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)))
% 3.73/1.00      | ~ r2_hidden(X3,k1_xboole_0)
% 3.73/1.00      | X0 != X3
% 3.73/1.00      | k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) != k1_xboole_0 ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_1609]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1980,plain,
% 3.73/1.00      ( r2_hidden(sK3,k3_xboole_0(k3_xboole_0(sK3,sK3),k5_xboole_0(sK3,sK3)))
% 3.73/1.00      | ~ r2_hidden(sK3,k1_xboole_0)
% 3.73/1.00      | k3_xboole_0(k3_xboole_0(sK3,sK3),k5_xboole_0(sK3,sK3)) != k1_xboole_0
% 3.73/1.00      | sK3 != sK3 ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_1963]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1321,plain,
% 3.73/1.00      ( r2_hidden(X0,X1)
% 3.73/1.00      | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2))
% 3.73/1.00      | X0 != X2
% 3.73/1.00      | X1 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2) ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_794]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1365,plain,
% 3.73/1.00      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))
% 3.73/1.00      | r2_hidden(X3,k1_xboole_0)
% 3.73/1.00      | X3 != X0
% 3.73/1.00      | k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0) ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_1321]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1367,plain,
% 3.73/1.00      ( ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
% 3.73/1.00      | r2_hidden(sK3,k1_xboole_0)
% 3.73/1.00      | sK3 != sK3
% 3.73/1.00      | k1_xboole_0 != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_1365]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_4,plain,
% 3.73/1.00      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 3.73/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_295,plain,
% 3.73/1.00      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 3.73/1.00      | k5_xboole_0(X3,X4) != X2
% 3.73/1.00      | k3_xboole_0(X3,X4) != X1 ),
% 3.73/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_7]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_296,plain,
% 3.73/1.00      ( ~ r2_hidden(X0,k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) ),
% 3.73/1.00      inference(unflattening,[status(thm)],[c_295]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_298,plain,
% 3.73/1.00      ( ~ r2_hidden(sK3,k3_xboole_0(k3_xboole_0(sK3,sK3),k5_xboole_0(sK3,sK3))) ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_296]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_136,plain,
% 3.73/1.00      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.73/1.00      inference(prop_impl,[status(thm)],[c_2]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_274,plain,
% 3.73/1.00      ( k5_xboole_0(X0,X1) != X2
% 3.73/1.00      | k3_xboole_0(X0,X1) != X3
% 3.73/1.00      | k3_xboole_0(X3,X2) = k1_xboole_0 ),
% 3.73/1.00      inference(resolution_lifted,[status(thm)],[c_136,c_7]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_275,plain,
% 3.73/1.00      ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.73/1.00      inference(unflattening,[status(thm)],[c_274]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_276,plain,
% 3.73/1.00      ( k3_xboole_0(k3_xboole_0(sK3,sK3),k5_xboole_0(sK3,sK3)) = k1_xboole_0 ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_275]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_16,plain,
% 3.73/1.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 3.73/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_28,plain,
% 3.73/1.00      ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_17,plain,
% 3.73/1.00      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
% 3.73/1.00      | X0 = X1
% 3.73/1.00      | X0 = X2
% 3.73/1.00      | X0 = X3 ),
% 3.73/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_25,plain,
% 3.73/1.00      ( ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
% 3.73/1.00      | sK3 = sK3 ),
% 3.73/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(contradiction,plain,
% 3.73/1.00      ( $false ),
% 3.73/1.00      inference(minisat,
% 3.73/1.00                [status(thm)],
% 3.73/1.00                [c_9604,c_7665,c_7191,c_1980,c_1367,c_298,c_276,c_28,
% 3.73/1.00                 c_25]) ).
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.73/1.00  
% 3.73/1.00  ------                               Statistics
% 3.73/1.00  
% 3.73/1.00  ------ General
% 3.73/1.00  
% 3.73/1.00  abstr_ref_over_cycles:                  0
% 3.73/1.00  abstr_ref_under_cycles:                 0
% 3.73/1.00  gc_basic_clause_elim:                   0
% 3.73/1.00  forced_gc_time:                         0
% 3.73/1.00  parsing_time:                           0.01
% 3.73/1.00  unif_index_cands_time:                  0.
% 3.73/1.00  unif_index_add_time:                    0.
% 3.73/1.00  orderings_time:                         0.
% 3.73/1.00  out_proof_time:                         0.008
% 3.73/1.00  total_time:                             0.4
% 3.73/1.00  num_of_symbols:                         42
% 3.73/1.00  num_of_terms:                           10912
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing
% 3.73/1.00  
% 3.73/1.00  num_of_splits:                          0
% 3.73/1.00  num_of_split_atoms:                     0
% 3.73/1.00  num_of_reused_defs:                     0
% 3.73/1.00  num_eq_ax_congr_red:                    14
% 3.73/1.00  num_of_sem_filtered_clauses:            1
% 3.73/1.00  num_of_subtypes:                        0
% 3.73/1.00  monotx_restored_types:                  0
% 3.73/1.00  sat_num_of_epr_types:                   0
% 3.73/1.00  sat_num_of_non_cyclic_types:            0
% 3.73/1.00  sat_guarded_non_collapsed_types:        0
% 3.73/1.00  num_pure_diseq_elim:                    0
% 3.73/1.00  simp_replaced_by:                       0
% 3.73/1.00  res_preprocessed:                       78
% 3.73/1.00  prep_upred:                             0
% 3.73/1.00  prep_unflattend:                        47
% 3.73/1.00  smt_new_axioms:                         0
% 3.73/1.00  pred_elim_cands:                        2
% 3.73/1.00  pred_elim:                              0
% 3.73/1.00  pred_elim_cl:                           0
% 3.73/1.00  pred_elim_cycles:                       2
% 3.73/1.00  merged_defs:                            12
% 3.73/1.00  merged_defs_ncl:                        0
% 3.73/1.00  bin_hyper_res:                          12
% 3.73/1.00  prep_cycles:                            3
% 3.73/1.00  pred_elim_time:                         0.008
% 3.73/1.00  splitting_time:                         0.
% 3.73/1.00  sem_filter_time:                        0.
% 3.73/1.00  monotx_time:                            0.
% 3.73/1.00  subtype_inf_time:                       0.
% 3.73/1.00  
% 3.73/1.00  ------ Problem properties
% 3.73/1.00  
% 3.73/1.00  clauses:                                21
% 3.73/1.00  conjectures:                            2
% 3.73/1.00  epr:                                    0
% 3.73/1.00  horn:                                   16
% 3.73/1.00  ground:                                 2
% 3.73/1.00  unary:                                  8
% 3.73/1.00  binary:                                 8
% 3.73/1.00  lits:                                   42
% 3.73/1.00  lits_eq:                                24
% 3.73/1.00  fd_pure:                                0
% 3.73/1.00  fd_pseudo:                              0
% 3.73/1.00  fd_cond:                                1
% 3.73/1.00  fd_pseudo_cond:                         5
% 3.73/1.00  ac_symbols:                             0
% 3.73/1.00  
% 3.73/1.00  ------ Propositional Solver
% 3.73/1.00  
% 3.73/1.00  prop_solver_calls:                      27
% 3.73/1.00  prop_fast_solver_calls:                 606
% 3.73/1.00  smt_solver_calls:                       0
% 3.73/1.00  smt_fast_solver_calls:                  0
% 3.73/1.00  prop_num_of_clauses:                    3105
% 3.73/1.00  prop_preprocess_simplified:             6594
% 3.73/1.00  prop_fo_subsumed:                       0
% 3.73/1.00  prop_solver_time:                       0.
% 3.73/1.00  smt_solver_time:                        0.
% 3.73/1.00  smt_fast_solver_time:                   0.
% 3.73/1.00  prop_fast_solver_time:                  0.
% 3.73/1.00  prop_unsat_core_time:                   0.
% 3.73/1.00  
% 3.73/1.00  ------ QBF
% 3.73/1.00  
% 3.73/1.00  qbf_q_res:                              0
% 3.73/1.00  qbf_num_tautologies:                    0
% 3.73/1.00  qbf_prep_cycles:                        0
% 3.73/1.00  
% 3.73/1.00  ------ BMC1
% 3.73/1.00  
% 3.73/1.00  bmc1_current_bound:                     -1
% 3.73/1.00  bmc1_last_solved_bound:                 -1
% 3.73/1.00  bmc1_unsat_core_size:                   -1
% 3.73/1.00  bmc1_unsat_core_parents_size:           -1
% 3.73/1.00  bmc1_merge_next_fun:                    0
% 3.73/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.73/1.00  
% 3.73/1.00  ------ Instantiation
% 3.73/1.00  
% 3.73/1.00  inst_num_of_clauses:                    783
% 3.73/1.00  inst_num_in_passive:                    72
% 3.73/1.00  inst_num_in_active:                     322
% 3.73/1.00  inst_num_in_unprocessed:                389
% 3.73/1.00  inst_num_of_loops:                      510
% 3.73/1.00  inst_num_of_learning_restarts:          0
% 3.73/1.00  inst_num_moves_active_passive:          181
% 3.73/1.00  inst_lit_activity:                      0
% 3.73/1.00  inst_lit_activity_moves:                0
% 3.73/1.00  inst_num_tautologies:                   0
% 3.73/1.00  inst_num_prop_implied:                  0
% 3.73/1.00  inst_num_existing_simplified:           0
% 3.73/1.00  inst_num_eq_res_simplified:             0
% 3.73/1.00  inst_num_child_elim:                    0
% 3.73/1.00  inst_num_of_dismatching_blockings:      573
% 3.73/1.00  inst_num_of_non_proper_insts:           1146
% 3.73/1.00  inst_num_of_duplicates:                 0
% 3.73/1.00  inst_inst_num_from_inst_to_res:         0
% 3.73/1.00  inst_dismatching_checking_time:         0.
% 3.73/1.00  
% 3.73/1.00  ------ Resolution
% 3.73/1.00  
% 3.73/1.00  res_num_of_clauses:                     0
% 3.73/1.00  res_num_in_passive:                     0
% 3.73/1.00  res_num_in_active:                      0
% 3.73/1.00  res_num_of_loops:                       81
% 3.73/1.00  res_forward_subset_subsumed:            144
% 3.73/1.00  res_backward_subset_subsumed:           0
% 3.73/1.00  res_forward_subsumed:                   0
% 3.73/1.00  res_backward_subsumed:                  0
% 3.73/1.00  res_forward_subsumption_resolution:     1
% 3.73/1.00  res_backward_subsumption_resolution:    0
% 3.73/1.00  res_clause_to_clause_subsumption:       2847
% 3.73/1.00  res_orphan_elimination:                 0
% 3.73/1.00  res_tautology_del:                      75
% 3.73/1.00  res_num_eq_res_simplified:              0
% 3.73/1.00  res_num_sel_changes:                    0
% 3.73/1.00  res_moves_from_active_to_pass:          0
% 3.73/1.00  
% 3.73/1.00  ------ Superposition
% 3.73/1.00  
% 3.73/1.00  sup_time_total:                         0.
% 3.73/1.00  sup_time_generating:                    0.
% 3.73/1.00  sup_time_sim_full:                      0.
% 3.73/1.00  sup_time_sim_immed:                     0.
% 3.73/1.00  
% 3.73/1.00  sup_num_of_clauses:                     277
% 3.73/1.00  sup_num_in_active:                      98
% 3.73/1.00  sup_num_in_passive:                     179
% 3.73/1.00  sup_num_of_loops:                       101
% 3.73/1.00  sup_fw_superposition:                   1258
% 3.73/1.00  sup_bw_superposition:                   837
% 3.73/1.00  sup_immediate_simplified:               505
% 3.73/1.00  sup_given_eliminated:                   1
% 3.73/1.00  comparisons_done:                       0
% 3.73/1.00  comparisons_avoided:                    9
% 3.73/1.00  
% 3.73/1.00  ------ Simplifications
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  sim_fw_subset_subsumed:                 38
% 3.73/1.00  sim_bw_subset_subsumed:                 0
% 3.73/1.00  sim_fw_subsumed:                        11
% 3.73/1.00  sim_bw_subsumed:                        2
% 3.73/1.00  sim_fw_subsumption_res:                 0
% 3.73/1.00  sim_bw_subsumption_res:                 0
% 3.73/1.00  sim_tautology_del:                      3
% 3.73/1.00  sim_eq_tautology_del:                   163
% 3.73/1.00  sim_eq_res_simp:                        2
% 3.73/1.00  sim_fw_demodulated:                     427
% 3.73/1.00  sim_bw_demodulated:                     4
% 3.73/1.00  sim_light_normalised:                   40
% 3.73/1.00  sim_joinable_taut:                      0
% 3.73/1.00  sim_joinable_simp:                      0
% 3.73/1.00  sim_ac_normalised:                      0
% 3.73/1.00  sim_smt_subsumption:                    0
% 3.73/1.00  
%------------------------------------------------------------------------------
