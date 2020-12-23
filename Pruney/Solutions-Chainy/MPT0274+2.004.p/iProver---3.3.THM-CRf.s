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
% DateTime   : Thu Dec  3 11:36:20 EST 2020

% Result     : Theorem 27.36s
% Output     : CNFRefutation 27.36s
% Verified   : 
% Statistics : Number of formulae       :  218 (1923 expanded)
%              Number of clauses        :  124 ( 557 expanded)
%              Number of leaves         :   31 ( 505 expanded)
%              Depth                    :   21
%              Number of atoms          :  450 (2904 expanded)
%              Number of equality atoms :  240 (1924 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f53,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f93,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f70,f65])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f41])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f39])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f92,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f68,f65])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f77,f78])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f76,f87])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f75,f88])).

fof(f90,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f74,f89])).

fof(f91,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f73,f90])).

fof(f94,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f72,f91,f91])).

fof(f26,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f47,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f48,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f49,plain,
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

fof(f50,plain,
    ( ( r2_hidden(sK3,sK4)
      | r2_hidden(sK2,sK4)
      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3) )
    & ( ( ~ r2_hidden(sK3,sK4)
        & ~ r2_hidden(sK2,sK4) )
      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f48,f49])).

fof(f85,plain,
    ( ~ r2_hidden(sK3,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f101,plain,
    ( ~ r2_hidden(sK3,sK4)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(definition_unfolding,[],[f85,f65,f91,f91])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f104,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f45])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f80,f91])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f79,f91])).

fof(f86,plain,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK2,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f100,plain,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK2,sK4)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(definition_unfolding,[],[f86,f65,f91,f91])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f82,f91,f91])).

fof(f84,plain,
    ( ~ r2_hidden(sK2,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f102,plain,
    ( ~ r2_hidden(sK2,sK4)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(definition_unfolding,[],[f84,f65,f91,f91])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f83,f91])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_18,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_903,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1914,plain,
    ( r1_xboole_0(k5_xboole_0(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_903])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_909,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_911,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10596,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_909,c_911])).

cnf(c_31656,plain,
    ( k3_xboole_0(k5_xboole_0(X0,X0),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1914,c_10596])).

cnf(c_14,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1395,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_2,c_14])).

cnf(c_3713,plain,
    ( k3_xboole_0(k5_xboole_0(X0,X0),X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2,c_1395])).

cnf(c_31868,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_31656,c_3713])).

cnf(c_19,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1037,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_19,c_1])).

cnf(c_16,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_904,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2230,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_904])).

cnf(c_3671,plain,
    ( r1_tarski(k3_xboole_0(k5_xboole_0(X0,X1),X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1395,c_2230])).

cnf(c_5274,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_3671])).

cnf(c_5909,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1037,c_5274])).

cnf(c_32226,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_31868,c_5909])).

cnf(c_17,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_32246,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_32226,c_17])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_905,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_33192,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_32246,c_905])).

cnf(c_43351,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_33192])).

cnf(c_3356,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_17,c_1037])).

cnf(c_3714,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_1395,c_3356])).

cnf(c_1256,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_17,c_1])).

cnf(c_3752,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(k5_xboole_0(X1,X0),X1) ),
    inference(demodulation,[status(thm)],[c_3714,c_1256])).

cnf(c_45986,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = k5_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_43351,c_3752])).

cnf(c_1398,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(k5_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_2,c_14])).

cnf(c_4693,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_1398,c_1])).

cnf(c_3711,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_0,c_1395])).

cnf(c_7501,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_3711,c_3356])).

cnf(c_7544,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_7501,c_1256])).

cnf(c_46054,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(X0,X1),X1),X1) = k3_xboole_0(k5_xboole_0(X1,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_45986,c_4693,c_7544])).

cnf(c_46055,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_46054,c_43351])).

cnf(c_20,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(sK3,sK4)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_896,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1133,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_896])).

cnf(c_1544,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2),k3_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20,c_1133])).

cnf(c_3674,plain,
    ( k3_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2),sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1395,c_1544])).

cnf(c_136805,plain,
    ( k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2),k5_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_46055,c_3674])).

cnf(c_12,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1080,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1206,plain,
    ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1080])).

cnf(c_1209,plain,
    ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1206])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1166,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0))
    | r2_hidden(X0,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1580,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3))
    | r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),sK4))
    | r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1166])).

cnf(c_1581,plain,
    ( r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3)) != iProver_top
    | r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),sK4)) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1580])).

cnf(c_1583,plain,
    ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
    | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1581])).

cnf(c_22,plain,
    ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
    | r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1079,plain,
    ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
    | r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1800,plain,
    ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3))
    | r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3)) ),
    inference(instantiation,[status(thm)],[c_1079])).

cnf(c_1801,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3)) != iProver_top
    | r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1800])).

cnf(c_1803,plain,
    ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
    | r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1801])).

cnf(c_23,plain,
    ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
    | r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1114,plain,
    ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
    | r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1866,plain,
    ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1114])).

cnf(c_1869,plain,
    ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
    | r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1866])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK3,sK4)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_897,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1132,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_897])).

cnf(c_3669,plain,
    ( k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1395,c_1132])).

cnf(c_3942,plain,
    ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_3669])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2051,plain,
    ( ~ r2_hidden(sK2,X0)
    | ~ r2_hidden(sK3,X0)
    | k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),X0) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_5255,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),X1))
    | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),X1))
    | k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),X1)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2051])).

cnf(c_8561,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),sK4))
    | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),sK4))
    | k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_5255])).

cnf(c_8563,plain,
    ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),sK4)) != iProver_top
    | r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8561])).

cnf(c_8565,plain,
    ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != iProver_top
    | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8563])).

cnf(c_1308,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,k5_xboole_0(X0,sK4))
    | r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8562,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3))
    | r2_hidden(sK2,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),sK4))
    | r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1308])).

cnf(c_8567,plain,
    ( r2_hidden(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3)) != iProver_top
    | r2_hidden(sK2,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),sK4)) = iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8562])).

cnf(c_8569,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
    | r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8567])).

cnf(c_28,negated_conjecture,
    ( ~ r2_hidden(sK2,sK4)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_895,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1134,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_895])).

cnf(c_3670,plain,
    ( k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1395,c_1134])).

cnf(c_136803,plain,
    ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_46055,c_3670])).

cnf(c_29,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1101,plain,
    ( ~ r1_tarski(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),X0)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1205,plain,
    ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1101])).

cnf(c_543,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1109,plain,
    ( X0 != X1
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != X1
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_1214,plain,
    ( X0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = X0
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1109])).

cnf(c_1731,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1214])).

cnf(c_542,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1777,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_542])).

cnf(c_6284,plain,
    ( r1_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_6285,plain,
    ( r1_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6284])).

cnf(c_547,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2420,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X3)
    | X1 != X3
    | X0 != k5_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_3486,plain,
    ( r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),X0)
    | ~ r1_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4)
    | X0 != sK4
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_2420])).

cnf(c_17009,plain,
    ( r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)
    | ~ r1_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3486])).

cnf(c_17010,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
    | sK4 != sK4
    | r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4) = iProver_top
    | r1_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17009])).

cnf(c_25,plain,
    ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_47925,plain,
    ( ~ r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)
    | ~ r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_47926,plain,
    ( r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4) != iProver_top
    | r2_hidden(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47925])).

cnf(c_137727,plain,
    ( r2_hidden(sK2,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_136803,c_29,c_1205,c_1206,c_1731,c_1777,c_6285,c_17010,c_47926])).

cnf(c_137733,plain,
    ( k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2),k5_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_136805,c_29,c_1205,c_1206,c_1209,c_1583,c_1731,c_1777,c_1803,c_1869,c_3942,c_6285,c_8565,c_8569,c_17010,c_47926])).

cnf(c_1912,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_903])).

cnf(c_3672,plain,
    ( r1_xboole_0(k3_xboole_0(k5_xboole_0(X0,X1),X0),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1395,c_1912])).

cnf(c_5715,plain,
    ( r1_xboole_0(k3_xboole_0(X0,k5_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_3672])).

cnf(c_6102,plain,
    ( r1_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_5715])).

cnf(c_137807,plain,
    ( r1_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_137733,c_6102])).

cnf(c_898,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_138357,plain,
    ( r2_hidden(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_137807,c_898])).

cnf(c_1723,plain,
    ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2),k3_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_1132])).

cnf(c_3673,plain,
    ( k3_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2),sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1395,c_1723])).

cnf(c_4047,plain,
    ( k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_3673])).

cnf(c_4907,plain,
    ( k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2),k5_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_4047])).

cnf(c_137736,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | r2_hidden(sK2,sK4) = iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_137733,c_4907])).

cnf(c_1316,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_138357,c_137736,c_137727,c_1316])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 27.36/4.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.36/4.01  
% 27.36/4.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.36/4.01  
% 27.36/4.01  ------  iProver source info
% 27.36/4.01  
% 27.36/4.01  git: date: 2020-06-30 10:37:57 +0100
% 27.36/4.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.36/4.01  git: non_committed_changes: false
% 27.36/4.01  git: last_make_outside_of_git: false
% 27.36/4.01  
% 27.36/4.01  ------ 
% 27.36/4.01  
% 27.36/4.01  ------ Input Options
% 27.36/4.01  
% 27.36/4.01  --out_options                           all
% 27.36/4.01  --tptp_safe_out                         true
% 27.36/4.01  --problem_path                          ""
% 27.36/4.01  --include_path                          ""
% 27.36/4.01  --clausifier                            res/vclausify_rel
% 27.36/4.01  --clausifier_options                    --mode clausify
% 27.36/4.01  --stdin                                 false
% 27.36/4.01  --stats_out                             all
% 27.36/4.01  
% 27.36/4.01  ------ General Options
% 27.36/4.01  
% 27.36/4.01  --fof                                   false
% 27.36/4.01  --time_out_real                         305.
% 27.36/4.01  --time_out_virtual                      -1.
% 27.36/4.01  --symbol_type_check                     false
% 27.36/4.01  --clausify_out                          false
% 27.36/4.01  --sig_cnt_out                           false
% 27.36/4.01  --trig_cnt_out                          false
% 27.36/4.01  --trig_cnt_out_tolerance                1.
% 27.36/4.01  --trig_cnt_out_sk_spl                   false
% 27.36/4.01  --abstr_cl_out                          false
% 27.36/4.01  
% 27.36/4.01  ------ Global Options
% 27.36/4.01  
% 27.36/4.01  --schedule                              default
% 27.36/4.01  --add_important_lit                     false
% 27.36/4.01  --prop_solver_per_cl                    1000
% 27.36/4.01  --min_unsat_core                        false
% 27.36/4.01  --soft_assumptions                      false
% 27.36/4.01  --soft_lemma_size                       3
% 27.36/4.01  --prop_impl_unit_size                   0
% 27.36/4.01  --prop_impl_unit                        []
% 27.36/4.01  --share_sel_clauses                     true
% 27.36/4.01  --reset_solvers                         false
% 27.36/4.01  --bc_imp_inh                            [conj_cone]
% 27.36/4.01  --conj_cone_tolerance                   3.
% 27.36/4.01  --extra_neg_conj                        none
% 27.36/4.01  --large_theory_mode                     true
% 27.36/4.01  --prolific_symb_bound                   200
% 27.36/4.01  --lt_threshold                          2000
% 27.36/4.01  --clause_weak_htbl                      true
% 27.36/4.01  --gc_record_bc_elim                     false
% 27.36/4.01  
% 27.36/4.01  ------ Preprocessing Options
% 27.36/4.01  
% 27.36/4.01  --preprocessing_flag                    true
% 27.36/4.01  --time_out_prep_mult                    0.1
% 27.36/4.01  --splitting_mode                        input
% 27.36/4.01  --splitting_grd                         true
% 27.36/4.01  --splitting_cvd                         false
% 27.36/4.01  --splitting_cvd_svl                     false
% 27.36/4.01  --splitting_nvd                         32
% 27.36/4.01  --sub_typing                            true
% 27.36/4.01  --prep_gs_sim                           true
% 27.36/4.01  --prep_unflatten                        true
% 27.36/4.01  --prep_res_sim                          true
% 27.36/4.01  --prep_upred                            true
% 27.36/4.01  --prep_sem_filter                       exhaustive
% 27.36/4.01  --prep_sem_filter_out                   false
% 27.36/4.01  --pred_elim                             true
% 27.36/4.01  --res_sim_input                         true
% 27.36/4.01  --eq_ax_congr_red                       true
% 27.36/4.01  --pure_diseq_elim                       true
% 27.36/4.01  --brand_transform                       false
% 27.36/4.01  --non_eq_to_eq                          false
% 27.36/4.01  --prep_def_merge                        true
% 27.36/4.01  --prep_def_merge_prop_impl              false
% 27.36/4.01  --prep_def_merge_mbd                    true
% 27.36/4.01  --prep_def_merge_tr_red                 false
% 27.36/4.01  --prep_def_merge_tr_cl                  false
% 27.36/4.01  --smt_preprocessing                     true
% 27.36/4.01  --smt_ac_axioms                         fast
% 27.36/4.01  --preprocessed_out                      false
% 27.36/4.01  --preprocessed_stats                    false
% 27.36/4.01  
% 27.36/4.01  ------ Abstraction refinement Options
% 27.36/4.01  
% 27.36/4.01  --abstr_ref                             []
% 27.36/4.01  --abstr_ref_prep                        false
% 27.36/4.01  --abstr_ref_until_sat                   false
% 27.36/4.01  --abstr_ref_sig_restrict                funpre
% 27.36/4.01  --abstr_ref_af_restrict_to_split_sk     false
% 27.36/4.01  --abstr_ref_under                       []
% 27.36/4.01  
% 27.36/4.01  ------ SAT Options
% 27.36/4.01  
% 27.36/4.01  --sat_mode                              false
% 27.36/4.01  --sat_fm_restart_options                ""
% 27.36/4.01  --sat_gr_def                            false
% 27.36/4.01  --sat_epr_types                         true
% 27.36/4.01  --sat_non_cyclic_types                  false
% 27.36/4.01  --sat_finite_models                     false
% 27.36/4.01  --sat_fm_lemmas                         false
% 27.36/4.01  --sat_fm_prep                           false
% 27.36/4.01  --sat_fm_uc_incr                        true
% 27.36/4.01  --sat_out_model                         small
% 27.36/4.01  --sat_out_clauses                       false
% 27.36/4.01  
% 27.36/4.01  ------ QBF Options
% 27.36/4.01  
% 27.36/4.01  --qbf_mode                              false
% 27.36/4.01  --qbf_elim_univ                         false
% 27.36/4.01  --qbf_dom_inst                          none
% 27.36/4.01  --qbf_dom_pre_inst                      false
% 27.36/4.01  --qbf_sk_in                             false
% 27.36/4.01  --qbf_pred_elim                         true
% 27.36/4.01  --qbf_split                             512
% 27.36/4.01  
% 27.36/4.01  ------ BMC1 Options
% 27.36/4.01  
% 27.36/4.01  --bmc1_incremental                      false
% 27.36/4.01  --bmc1_axioms                           reachable_all
% 27.36/4.01  --bmc1_min_bound                        0
% 27.36/4.01  --bmc1_max_bound                        -1
% 27.36/4.01  --bmc1_max_bound_default                -1
% 27.36/4.01  --bmc1_symbol_reachability              true
% 27.36/4.01  --bmc1_property_lemmas                  false
% 27.36/4.01  --bmc1_k_induction                      false
% 27.36/4.01  --bmc1_non_equiv_states                 false
% 27.36/4.01  --bmc1_deadlock                         false
% 27.36/4.01  --bmc1_ucm                              false
% 27.36/4.01  --bmc1_add_unsat_core                   none
% 27.36/4.01  --bmc1_unsat_core_children              false
% 27.36/4.01  --bmc1_unsat_core_extrapolate_axioms    false
% 27.36/4.01  --bmc1_out_stat                         full
% 27.36/4.01  --bmc1_ground_init                      false
% 27.36/4.01  --bmc1_pre_inst_next_state              false
% 27.36/4.01  --bmc1_pre_inst_state                   false
% 27.36/4.01  --bmc1_pre_inst_reach_state             false
% 27.36/4.01  --bmc1_out_unsat_core                   false
% 27.36/4.01  --bmc1_aig_witness_out                  false
% 27.36/4.01  --bmc1_verbose                          false
% 27.36/4.01  --bmc1_dump_clauses_tptp                false
% 27.36/4.01  --bmc1_dump_unsat_core_tptp             false
% 27.36/4.01  --bmc1_dump_file                        -
% 27.36/4.01  --bmc1_ucm_expand_uc_limit              128
% 27.36/4.01  --bmc1_ucm_n_expand_iterations          6
% 27.36/4.01  --bmc1_ucm_extend_mode                  1
% 27.36/4.01  --bmc1_ucm_init_mode                    2
% 27.36/4.01  --bmc1_ucm_cone_mode                    none
% 27.36/4.01  --bmc1_ucm_reduced_relation_type        0
% 27.36/4.01  --bmc1_ucm_relax_model                  4
% 27.36/4.01  --bmc1_ucm_full_tr_after_sat            true
% 27.36/4.01  --bmc1_ucm_expand_neg_assumptions       false
% 27.36/4.01  --bmc1_ucm_layered_model                none
% 27.36/4.01  --bmc1_ucm_max_lemma_size               10
% 27.36/4.01  
% 27.36/4.01  ------ AIG Options
% 27.36/4.01  
% 27.36/4.01  --aig_mode                              false
% 27.36/4.01  
% 27.36/4.01  ------ Instantiation Options
% 27.36/4.01  
% 27.36/4.01  --instantiation_flag                    true
% 27.36/4.01  --inst_sos_flag                         false
% 27.36/4.01  --inst_sos_phase                        true
% 27.36/4.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.36/4.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.36/4.01  --inst_lit_sel_side                     num_symb
% 27.36/4.01  --inst_solver_per_active                1400
% 27.36/4.01  --inst_solver_calls_frac                1.
% 27.36/4.01  --inst_passive_queue_type               priority_queues
% 27.36/4.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.36/4.01  --inst_passive_queues_freq              [25;2]
% 27.36/4.01  --inst_dismatching                      true
% 27.36/4.01  --inst_eager_unprocessed_to_passive     true
% 27.36/4.01  --inst_prop_sim_given                   true
% 27.36/4.01  --inst_prop_sim_new                     false
% 27.36/4.01  --inst_subs_new                         false
% 27.36/4.01  --inst_eq_res_simp                      false
% 27.36/4.01  --inst_subs_given                       false
% 27.36/4.01  --inst_orphan_elimination               true
% 27.36/4.01  --inst_learning_loop_flag               true
% 27.36/4.01  --inst_learning_start                   3000
% 27.36/4.01  --inst_learning_factor                  2
% 27.36/4.01  --inst_start_prop_sim_after_learn       3
% 27.36/4.01  --inst_sel_renew                        solver
% 27.36/4.01  --inst_lit_activity_flag                true
% 27.36/4.01  --inst_restr_to_given                   false
% 27.36/4.01  --inst_activity_threshold               500
% 27.36/4.01  --inst_out_proof                        true
% 27.36/4.01  
% 27.36/4.01  ------ Resolution Options
% 27.36/4.01  
% 27.36/4.01  --resolution_flag                       true
% 27.36/4.01  --res_lit_sel                           adaptive
% 27.36/4.01  --res_lit_sel_side                      none
% 27.36/4.01  --res_ordering                          kbo
% 27.36/4.01  --res_to_prop_solver                    active
% 27.36/4.01  --res_prop_simpl_new                    false
% 27.36/4.01  --res_prop_simpl_given                  true
% 27.36/4.01  --res_passive_queue_type                priority_queues
% 27.36/4.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.36/4.01  --res_passive_queues_freq               [15;5]
% 27.36/4.01  --res_forward_subs                      full
% 27.36/4.01  --res_backward_subs                     full
% 27.36/4.01  --res_forward_subs_resolution           true
% 27.36/4.01  --res_backward_subs_resolution          true
% 27.36/4.01  --res_orphan_elimination                true
% 27.36/4.01  --res_time_limit                        2.
% 27.36/4.01  --res_out_proof                         true
% 27.36/4.01  
% 27.36/4.01  ------ Superposition Options
% 27.36/4.01  
% 27.36/4.01  --superposition_flag                    true
% 27.36/4.01  --sup_passive_queue_type                priority_queues
% 27.36/4.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.36/4.01  --sup_passive_queues_freq               [8;1;4]
% 27.36/4.01  --demod_completeness_check              fast
% 27.36/4.01  --demod_use_ground                      true
% 27.36/4.01  --sup_to_prop_solver                    passive
% 27.36/4.01  --sup_prop_simpl_new                    true
% 27.36/4.01  --sup_prop_simpl_given                  true
% 27.36/4.01  --sup_fun_splitting                     false
% 27.36/4.01  --sup_smt_interval                      50000
% 27.36/4.01  
% 27.36/4.01  ------ Superposition Simplification Setup
% 27.36/4.01  
% 27.36/4.01  --sup_indices_passive                   []
% 27.36/4.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.36/4.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.36/4.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.36/4.01  --sup_full_triv                         [TrivRules;PropSubs]
% 27.36/4.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.36/4.01  --sup_full_bw                           [BwDemod]
% 27.36/4.01  --sup_immed_triv                        [TrivRules]
% 27.36/4.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.36/4.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.36/4.01  --sup_immed_bw_main                     []
% 27.36/4.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.36/4.01  --sup_input_triv                        [Unflattening;TrivRules]
% 27.36/4.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.36/4.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.36/4.01  
% 27.36/4.01  ------ Combination Options
% 27.36/4.01  
% 27.36/4.01  --comb_res_mult                         3
% 27.36/4.01  --comb_sup_mult                         2
% 27.36/4.01  --comb_inst_mult                        10
% 27.36/4.01  
% 27.36/4.01  ------ Debug Options
% 27.36/4.01  
% 27.36/4.01  --dbg_backtrace                         false
% 27.36/4.01  --dbg_dump_prop_clauses                 false
% 27.36/4.01  --dbg_dump_prop_clauses_file            -
% 27.36/4.01  --dbg_out_stat                          false
% 27.36/4.01  ------ Parsing...
% 27.36/4.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.36/4.01  
% 27.36/4.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 27.36/4.01  
% 27.36/4.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.36/4.01  
% 27.36/4.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.36/4.01  ------ Proving...
% 27.36/4.01  ------ Problem Properties 
% 27.36/4.01  
% 27.36/4.01  
% 27.36/4.01  clauses                                 28
% 27.36/4.01  conjectures                             3
% 27.36/4.01  EPR                                     2
% 27.36/4.01  Horn                                    22
% 27.36/4.01  unary                                   11
% 27.36/4.01  binary                                  9
% 27.36/4.01  lits                                    53
% 27.36/4.01  lits eq                                 14
% 27.36/4.01  fd_pure                                 0
% 27.36/4.01  fd_pseudo                               0
% 27.36/4.01  fd_cond                                 1
% 27.36/4.01  fd_pseudo_cond                          1
% 27.36/4.01  AC symbols                              1
% 27.36/4.01  
% 27.36/4.01  ------ Schedule dynamic 5 is on 
% 27.36/4.01  
% 27.36/4.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.36/4.01  
% 27.36/4.01  
% 27.36/4.01  ------ 
% 27.36/4.01  Current options:
% 27.36/4.01  ------ 
% 27.36/4.01  
% 27.36/4.01  ------ Input Options
% 27.36/4.01  
% 27.36/4.01  --out_options                           all
% 27.36/4.01  --tptp_safe_out                         true
% 27.36/4.01  --problem_path                          ""
% 27.36/4.01  --include_path                          ""
% 27.36/4.01  --clausifier                            res/vclausify_rel
% 27.36/4.01  --clausifier_options                    --mode clausify
% 27.36/4.01  --stdin                                 false
% 27.36/4.01  --stats_out                             all
% 27.36/4.01  
% 27.36/4.01  ------ General Options
% 27.36/4.01  
% 27.36/4.01  --fof                                   false
% 27.36/4.01  --time_out_real                         305.
% 27.36/4.01  --time_out_virtual                      -1.
% 27.36/4.01  --symbol_type_check                     false
% 27.36/4.01  --clausify_out                          false
% 27.36/4.01  --sig_cnt_out                           false
% 27.36/4.01  --trig_cnt_out                          false
% 27.36/4.01  --trig_cnt_out_tolerance                1.
% 27.36/4.01  --trig_cnt_out_sk_spl                   false
% 27.36/4.01  --abstr_cl_out                          false
% 27.36/4.01  
% 27.36/4.01  ------ Global Options
% 27.36/4.01  
% 27.36/4.01  --schedule                              default
% 27.36/4.01  --add_important_lit                     false
% 27.36/4.01  --prop_solver_per_cl                    1000
% 27.36/4.01  --min_unsat_core                        false
% 27.36/4.01  --soft_assumptions                      false
% 27.36/4.01  --soft_lemma_size                       3
% 27.36/4.01  --prop_impl_unit_size                   0
% 27.36/4.01  --prop_impl_unit                        []
% 27.36/4.01  --share_sel_clauses                     true
% 27.36/4.01  --reset_solvers                         false
% 27.36/4.01  --bc_imp_inh                            [conj_cone]
% 27.36/4.01  --conj_cone_tolerance                   3.
% 27.36/4.01  --extra_neg_conj                        none
% 27.36/4.01  --large_theory_mode                     true
% 27.36/4.01  --prolific_symb_bound                   200
% 27.36/4.01  --lt_threshold                          2000
% 27.36/4.01  --clause_weak_htbl                      true
% 27.36/4.01  --gc_record_bc_elim                     false
% 27.36/4.01  
% 27.36/4.01  ------ Preprocessing Options
% 27.36/4.01  
% 27.36/4.01  --preprocessing_flag                    true
% 27.36/4.01  --time_out_prep_mult                    0.1
% 27.36/4.01  --splitting_mode                        input
% 27.36/4.01  --splitting_grd                         true
% 27.36/4.01  --splitting_cvd                         false
% 27.36/4.01  --splitting_cvd_svl                     false
% 27.36/4.01  --splitting_nvd                         32
% 27.36/4.01  --sub_typing                            true
% 27.36/4.01  --prep_gs_sim                           true
% 27.36/4.01  --prep_unflatten                        true
% 27.36/4.01  --prep_res_sim                          true
% 27.36/4.01  --prep_upred                            true
% 27.36/4.01  --prep_sem_filter                       exhaustive
% 27.36/4.01  --prep_sem_filter_out                   false
% 27.36/4.01  --pred_elim                             true
% 27.36/4.01  --res_sim_input                         true
% 27.36/4.01  --eq_ax_congr_red                       true
% 27.36/4.01  --pure_diseq_elim                       true
% 27.36/4.01  --brand_transform                       false
% 27.36/4.01  --non_eq_to_eq                          false
% 27.36/4.01  --prep_def_merge                        true
% 27.36/4.01  --prep_def_merge_prop_impl              false
% 27.36/4.01  --prep_def_merge_mbd                    true
% 27.36/4.01  --prep_def_merge_tr_red                 false
% 27.36/4.01  --prep_def_merge_tr_cl                  false
% 27.36/4.01  --smt_preprocessing                     true
% 27.36/4.01  --smt_ac_axioms                         fast
% 27.36/4.01  --preprocessed_out                      false
% 27.36/4.01  --preprocessed_stats                    false
% 27.36/4.01  
% 27.36/4.01  ------ Abstraction refinement Options
% 27.36/4.01  
% 27.36/4.01  --abstr_ref                             []
% 27.36/4.01  --abstr_ref_prep                        false
% 27.36/4.01  --abstr_ref_until_sat                   false
% 27.36/4.01  --abstr_ref_sig_restrict                funpre
% 27.36/4.01  --abstr_ref_af_restrict_to_split_sk     false
% 27.36/4.01  --abstr_ref_under                       []
% 27.36/4.01  
% 27.36/4.01  ------ SAT Options
% 27.36/4.01  
% 27.36/4.01  --sat_mode                              false
% 27.36/4.01  --sat_fm_restart_options                ""
% 27.36/4.01  --sat_gr_def                            false
% 27.36/4.01  --sat_epr_types                         true
% 27.36/4.01  --sat_non_cyclic_types                  false
% 27.36/4.01  --sat_finite_models                     false
% 27.36/4.01  --sat_fm_lemmas                         false
% 27.36/4.01  --sat_fm_prep                           false
% 27.36/4.01  --sat_fm_uc_incr                        true
% 27.36/4.01  --sat_out_model                         small
% 27.36/4.01  --sat_out_clauses                       false
% 27.36/4.01  
% 27.36/4.01  ------ QBF Options
% 27.36/4.01  
% 27.36/4.01  --qbf_mode                              false
% 27.36/4.01  --qbf_elim_univ                         false
% 27.36/4.01  --qbf_dom_inst                          none
% 27.36/4.01  --qbf_dom_pre_inst                      false
% 27.36/4.01  --qbf_sk_in                             false
% 27.36/4.01  --qbf_pred_elim                         true
% 27.36/4.01  --qbf_split                             512
% 27.36/4.01  
% 27.36/4.01  ------ BMC1 Options
% 27.36/4.01  
% 27.36/4.01  --bmc1_incremental                      false
% 27.36/4.01  --bmc1_axioms                           reachable_all
% 27.36/4.01  --bmc1_min_bound                        0
% 27.36/4.01  --bmc1_max_bound                        -1
% 27.36/4.01  --bmc1_max_bound_default                -1
% 27.36/4.01  --bmc1_symbol_reachability              true
% 27.36/4.01  --bmc1_property_lemmas                  false
% 27.36/4.01  --bmc1_k_induction                      false
% 27.36/4.01  --bmc1_non_equiv_states                 false
% 27.36/4.01  --bmc1_deadlock                         false
% 27.36/4.01  --bmc1_ucm                              false
% 27.36/4.01  --bmc1_add_unsat_core                   none
% 27.36/4.01  --bmc1_unsat_core_children              false
% 27.36/4.01  --bmc1_unsat_core_extrapolate_axioms    false
% 27.36/4.01  --bmc1_out_stat                         full
% 27.36/4.01  --bmc1_ground_init                      false
% 27.36/4.01  --bmc1_pre_inst_next_state              false
% 27.36/4.01  --bmc1_pre_inst_state                   false
% 27.36/4.01  --bmc1_pre_inst_reach_state             false
% 27.36/4.01  --bmc1_out_unsat_core                   false
% 27.36/4.01  --bmc1_aig_witness_out                  false
% 27.36/4.01  --bmc1_verbose                          false
% 27.36/4.01  --bmc1_dump_clauses_tptp                false
% 27.36/4.01  --bmc1_dump_unsat_core_tptp             false
% 27.36/4.01  --bmc1_dump_file                        -
% 27.36/4.01  --bmc1_ucm_expand_uc_limit              128
% 27.36/4.01  --bmc1_ucm_n_expand_iterations          6
% 27.36/4.01  --bmc1_ucm_extend_mode                  1
% 27.36/4.01  --bmc1_ucm_init_mode                    2
% 27.36/4.01  --bmc1_ucm_cone_mode                    none
% 27.36/4.01  --bmc1_ucm_reduced_relation_type        0
% 27.36/4.01  --bmc1_ucm_relax_model                  4
% 27.36/4.01  --bmc1_ucm_full_tr_after_sat            true
% 27.36/4.01  --bmc1_ucm_expand_neg_assumptions       false
% 27.36/4.01  --bmc1_ucm_layered_model                none
% 27.36/4.01  --bmc1_ucm_max_lemma_size               10
% 27.36/4.01  
% 27.36/4.01  ------ AIG Options
% 27.36/4.01  
% 27.36/4.01  --aig_mode                              false
% 27.36/4.01  
% 27.36/4.01  ------ Instantiation Options
% 27.36/4.01  
% 27.36/4.01  --instantiation_flag                    true
% 27.36/4.01  --inst_sos_flag                         false
% 27.36/4.01  --inst_sos_phase                        true
% 27.36/4.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.36/4.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.36/4.01  --inst_lit_sel_side                     none
% 27.36/4.01  --inst_solver_per_active                1400
% 27.36/4.01  --inst_solver_calls_frac                1.
% 27.36/4.01  --inst_passive_queue_type               priority_queues
% 27.36/4.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.36/4.01  --inst_passive_queues_freq              [25;2]
% 27.36/4.01  --inst_dismatching                      true
% 27.36/4.01  --inst_eager_unprocessed_to_passive     true
% 27.36/4.01  --inst_prop_sim_given                   true
% 27.36/4.01  --inst_prop_sim_new                     false
% 27.36/4.01  --inst_subs_new                         false
% 27.36/4.01  --inst_eq_res_simp                      false
% 27.36/4.01  --inst_subs_given                       false
% 27.36/4.01  --inst_orphan_elimination               true
% 27.36/4.01  --inst_learning_loop_flag               true
% 27.36/4.01  --inst_learning_start                   3000
% 27.36/4.01  --inst_learning_factor                  2
% 27.36/4.01  --inst_start_prop_sim_after_learn       3
% 27.36/4.01  --inst_sel_renew                        solver
% 27.36/4.01  --inst_lit_activity_flag                true
% 27.36/4.01  --inst_restr_to_given                   false
% 27.36/4.01  --inst_activity_threshold               500
% 27.36/4.01  --inst_out_proof                        true
% 27.36/4.01  
% 27.36/4.01  ------ Resolution Options
% 27.36/4.01  
% 27.36/4.01  --resolution_flag                       false
% 27.36/4.01  --res_lit_sel                           adaptive
% 27.36/4.01  --res_lit_sel_side                      none
% 27.36/4.01  --res_ordering                          kbo
% 27.36/4.01  --res_to_prop_solver                    active
% 27.36/4.01  --res_prop_simpl_new                    false
% 27.36/4.01  --res_prop_simpl_given                  true
% 27.36/4.01  --res_passive_queue_type                priority_queues
% 27.36/4.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.36/4.01  --res_passive_queues_freq               [15;5]
% 27.36/4.01  --res_forward_subs                      full
% 27.36/4.01  --res_backward_subs                     full
% 27.36/4.01  --res_forward_subs_resolution           true
% 27.36/4.01  --res_backward_subs_resolution          true
% 27.36/4.01  --res_orphan_elimination                true
% 27.36/4.01  --res_time_limit                        2.
% 27.36/4.01  --res_out_proof                         true
% 27.36/4.01  
% 27.36/4.01  ------ Superposition Options
% 27.36/4.01  
% 27.36/4.01  --superposition_flag                    true
% 27.36/4.01  --sup_passive_queue_type                priority_queues
% 27.36/4.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.36/4.01  --sup_passive_queues_freq               [8;1;4]
% 27.36/4.01  --demod_completeness_check              fast
% 27.36/4.01  --demod_use_ground                      true
% 27.36/4.01  --sup_to_prop_solver                    passive
% 27.36/4.01  --sup_prop_simpl_new                    true
% 27.36/4.01  --sup_prop_simpl_given                  true
% 27.36/4.01  --sup_fun_splitting                     false
% 27.36/4.01  --sup_smt_interval                      50000
% 27.36/4.01  
% 27.36/4.01  ------ Superposition Simplification Setup
% 27.36/4.01  
% 27.36/4.01  --sup_indices_passive                   []
% 27.36/4.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.36/4.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.36/4.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.36/4.01  --sup_full_triv                         [TrivRules;PropSubs]
% 27.36/4.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.36/4.01  --sup_full_bw                           [BwDemod]
% 27.36/4.01  --sup_immed_triv                        [TrivRules]
% 27.36/4.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.36/4.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.36/4.01  --sup_immed_bw_main                     []
% 27.36/4.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.36/4.01  --sup_input_triv                        [Unflattening;TrivRules]
% 27.36/4.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.36/4.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.36/4.01  
% 27.36/4.01  ------ Combination Options
% 27.36/4.01  
% 27.36/4.01  --comb_res_mult                         3
% 27.36/4.01  --comb_sup_mult                         2
% 27.36/4.01  --comb_inst_mult                        10
% 27.36/4.01  
% 27.36/4.01  ------ Debug Options
% 27.36/4.01  
% 27.36/4.01  --dbg_backtrace                         false
% 27.36/4.01  --dbg_dump_prop_clauses                 false
% 27.36/4.01  --dbg_dump_prop_clauses_file            -
% 27.36/4.01  --dbg_out_stat                          false
% 27.36/4.01  
% 27.36/4.01  
% 27.36/4.01  
% 27.36/4.01  
% 27.36/4.01  ------ Proving...
% 27.36/4.01  
% 27.36/4.01  
% 27.36/4.01  % SZS status Theorem for theBenchmark.p
% 27.36/4.01  
% 27.36/4.01  % SZS output start CNFRefutation for theBenchmark.p
% 27.36/4.01  
% 27.36/4.01  fof(f1,axiom,(
% 27.36/4.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f51,plain,(
% 27.36/4.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 27.36/4.01    inference(cnf_transformation,[],[f1])).
% 27.36/4.01  
% 27.36/4.01  fof(f3,axiom,(
% 27.36/4.01    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f28,plain,(
% 27.36/4.01    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 27.36/4.01    inference(rectify,[],[f3])).
% 27.36/4.01  
% 27.36/4.01  fof(f53,plain,(
% 27.36/4.01    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 27.36/4.01    inference(cnf_transformation,[],[f28])).
% 27.36/4.01  
% 27.36/4.01  fof(f14,axiom,(
% 27.36/4.01    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f70,plain,(
% 27.36/4.01    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 27.36/4.01    inference(cnf_transformation,[],[f14])).
% 27.36/4.01  
% 27.36/4.01  fof(f9,axiom,(
% 27.36/4.01    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f65,plain,(
% 27.36/4.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 27.36/4.01    inference(cnf_transformation,[],[f9])).
% 27.36/4.01  
% 27.36/4.01  fof(f93,plain,(
% 27.36/4.01    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 27.36/4.01    inference(definition_unfolding,[],[f70,f65])).
% 27.36/4.01  
% 27.36/4.01  fof(f6,axiom,(
% 27.36/4.01    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f32,plain,(
% 27.36/4.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 27.36/4.01    inference(ennf_transformation,[],[f6])).
% 27.36/4.01  
% 27.36/4.01  fof(f41,plain,(
% 27.36/4.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 27.36/4.01    introduced(choice_axiom,[])).
% 27.36/4.01  
% 27.36/4.01  fof(f42,plain,(
% 27.36/4.01    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 27.36/4.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f41])).
% 27.36/4.01  
% 27.36/4.01  fof(f60,plain,(
% 27.36/4.01    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 27.36/4.01    inference(cnf_transformation,[],[f42])).
% 27.36/4.01  
% 27.36/4.01  fof(f5,axiom,(
% 27.36/4.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f29,plain,(
% 27.36/4.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 27.36/4.01    inference(rectify,[],[f5])).
% 27.36/4.01  
% 27.36/4.01  fof(f31,plain,(
% 27.36/4.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 27.36/4.01    inference(ennf_transformation,[],[f29])).
% 27.36/4.01  
% 27.36/4.01  fof(f39,plain,(
% 27.36/4.01    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 27.36/4.01    introduced(choice_axiom,[])).
% 27.36/4.01  
% 27.36/4.01  fof(f40,plain,(
% 27.36/4.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 27.36/4.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f39])).
% 27.36/4.01  
% 27.36/4.01  fof(f59,plain,(
% 27.36/4.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 27.36/4.01    inference(cnf_transformation,[],[f40])).
% 27.36/4.01  
% 27.36/4.01  fof(f10,axiom,(
% 27.36/4.01    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f66,plain,(
% 27.36/4.01    ( ! [X2,X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))) )),
% 27.36/4.01    inference(cnf_transformation,[],[f10])).
% 27.36/4.01  
% 27.36/4.01  fof(f15,axiom,(
% 27.36/4.01    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f71,plain,(
% 27.36/4.01    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 27.36/4.01    inference(cnf_transformation,[],[f15])).
% 27.36/4.01  
% 27.36/4.01  fof(f2,axiom,(
% 27.36/4.01    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f52,plain,(
% 27.36/4.01    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 27.36/4.01    inference(cnf_transformation,[],[f2])).
% 27.36/4.01  
% 27.36/4.01  fof(f12,axiom,(
% 27.36/4.01    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f68,plain,(
% 27.36/4.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 27.36/4.01    inference(cnf_transformation,[],[f12])).
% 27.36/4.01  
% 27.36/4.01  fof(f92,plain,(
% 27.36/4.01    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 27.36/4.01    inference(definition_unfolding,[],[f68,f65])).
% 27.36/4.01  
% 27.36/4.01  fof(f13,axiom,(
% 27.36/4.01    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f69,plain,(
% 27.36/4.01    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.36/4.01    inference(cnf_transformation,[],[f13])).
% 27.36/4.01  
% 27.36/4.01  fof(f11,axiom,(
% 27.36/4.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f33,plain,(
% 27.36/4.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 27.36/4.01    inference(ennf_transformation,[],[f11])).
% 27.36/4.01  
% 27.36/4.01  fof(f67,plain,(
% 27.36/4.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 27.36/4.01    inference(cnf_transformation,[],[f33])).
% 27.36/4.01  
% 27.36/4.01  fof(f16,axiom,(
% 27.36/4.01    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f72,plain,(
% 27.36/4.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 27.36/4.01    inference(cnf_transformation,[],[f16])).
% 27.36/4.01  
% 27.36/4.01  fof(f17,axiom,(
% 27.36/4.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f73,plain,(
% 27.36/4.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 27.36/4.01    inference(cnf_transformation,[],[f17])).
% 27.36/4.01  
% 27.36/4.01  fof(f18,axiom,(
% 27.36/4.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f74,plain,(
% 27.36/4.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 27.36/4.01    inference(cnf_transformation,[],[f18])).
% 27.36/4.01  
% 27.36/4.01  fof(f19,axiom,(
% 27.36/4.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f75,plain,(
% 27.36/4.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 27.36/4.01    inference(cnf_transformation,[],[f19])).
% 27.36/4.01  
% 27.36/4.01  fof(f20,axiom,(
% 27.36/4.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f76,plain,(
% 27.36/4.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 27.36/4.01    inference(cnf_transformation,[],[f20])).
% 27.36/4.01  
% 27.36/4.01  fof(f21,axiom,(
% 27.36/4.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f77,plain,(
% 27.36/4.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 27.36/4.01    inference(cnf_transformation,[],[f21])).
% 27.36/4.01  
% 27.36/4.01  fof(f22,axiom,(
% 27.36/4.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f78,plain,(
% 27.36/4.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 27.36/4.01    inference(cnf_transformation,[],[f22])).
% 27.36/4.01  
% 27.36/4.01  fof(f87,plain,(
% 27.36/4.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 27.36/4.01    inference(definition_unfolding,[],[f77,f78])).
% 27.36/4.01  
% 27.36/4.01  fof(f88,plain,(
% 27.36/4.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 27.36/4.01    inference(definition_unfolding,[],[f76,f87])).
% 27.36/4.01  
% 27.36/4.01  fof(f89,plain,(
% 27.36/4.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 27.36/4.01    inference(definition_unfolding,[],[f75,f88])).
% 27.36/4.01  
% 27.36/4.01  fof(f90,plain,(
% 27.36/4.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 27.36/4.01    inference(definition_unfolding,[],[f74,f89])).
% 27.36/4.01  
% 27.36/4.01  fof(f91,plain,(
% 27.36/4.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 27.36/4.01    inference(definition_unfolding,[],[f73,f90])).
% 27.36/4.01  
% 27.36/4.01  fof(f94,plain,(
% 27.36/4.01    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 27.36/4.01    inference(definition_unfolding,[],[f72,f91,f91])).
% 27.36/4.01  
% 27.36/4.01  fof(f26,conjecture,(
% 27.36/4.01    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f27,negated_conjecture,(
% 27.36/4.01    ~! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 27.36/4.01    inference(negated_conjecture,[],[f26])).
% 27.36/4.01  
% 27.36/4.01  fof(f37,plain,(
% 27.36/4.01    ? [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 27.36/4.01    inference(ennf_transformation,[],[f27])).
% 27.36/4.01  
% 27.36/4.01  fof(f47,plain,(
% 27.36/4.01    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)))),
% 27.36/4.01    inference(nnf_transformation,[],[f37])).
% 27.36/4.01  
% 27.36/4.01  fof(f48,plain,(
% 27.36/4.01    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)))),
% 27.36/4.01    inference(flattening,[],[f47])).
% 27.36/4.01  
% 27.36/4.01  fof(f49,plain,(
% 27.36/4.01    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1))) => ((r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3)) & ((~r2_hidden(sK3,sK4) & ~r2_hidden(sK2,sK4)) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3)))),
% 27.36/4.01    introduced(choice_axiom,[])).
% 27.36/4.01  
% 27.36/4.01  fof(f50,plain,(
% 27.36/4.01    (r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3)) & ((~r2_hidden(sK3,sK4) & ~r2_hidden(sK2,sK4)) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3))),
% 27.36/4.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f48,f49])).
% 27.36/4.01  
% 27.36/4.01  fof(f85,plain,(
% 27.36/4.01    ~r2_hidden(sK3,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3)),
% 27.36/4.01    inference(cnf_transformation,[],[f50])).
% 27.36/4.01  
% 27.36/4.01  fof(f101,plain,(
% 27.36/4.01    ~r2_hidden(sK3,sK4) | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)),
% 27.36/4.01    inference(definition_unfolding,[],[f85,f65,f91,f91])).
% 27.36/4.01  
% 27.36/4.01  fof(f7,axiom,(
% 27.36/4.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f43,plain,(
% 27.36/4.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.36/4.01    inference(nnf_transformation,[],[f7])).
% 27.36/4.01  
% 27.36/4.01  fof(f44,plain,(
% 27.36/4.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.36/4.01    inference(flattening,[],[f43])).
% 27.36/4.01  
% 27.36/4.01  fof(f61,plain,(
% 27.36/4.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 27.36/4.01    inference(cnf_transformation,[],[f44])).
% 27.36/4.01  
% 27.36/4.01  fof(f104,plain,(
% 27.36/4.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 27.36/4.01    inference(equality_resolution,[],[f61])).
% 27.36/4.01  
% 27.36/4.01  fof(f4,axiom,(
% 27.36/4.01    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f30,plain,(
% 27.36/4.01    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 27.36/4.01    inference(ennf_transformation,[],[f4])).
% 27.36/4.01  
% 27.36/4.01  fof(f38,plain,(
% 27.36/4.01    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 27.36/4.01    inference(nnf_transformation,[],[f30])).
% 27.36/4.01  
% 27.36/4.01  fof(f56,plain,(
% 27.36/4.01    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 27.36/4.01    inference(cnf_transformation,[],[f38])).
% 27.36/4.01  
% 27.36/4.01  fof(f23,axiom,(
% 27.36/4.01    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f45,plain,(
% 27.36/4.01    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 27.36/4.01    inference(nnf_transformation,[],[f23])).
% 27.36/4.01  
% 27.36/4.01  fof(f46,plain,(
% 27.36/4.01    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 27.36/4.01    inference(flattening,[],[f45])).
% 27.36/4.01  
% 27.36/4.01  fof(f80,plain,(
% 27.36/4.01    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 27.36/4.01    inference(cnf_transformation,[],[f46])).
% 27.36/4.01  
% 27.36/4.01  fof(f96,plain,(
% 27.36/4.01    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 27.36/4.01    inference(definition_unfolding,[],[f80,f91])).
% 27.36/4.01  
% 27.36/4.01  fof(f79,plain,(
% 27.36/4.01    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 27.36/4.01    inference(cnf_transformation,[],[f46])).
% 27.36/4.01  
% 27.36/4.01  fof(f97,plain,(
% 27.36/4.01    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 27.36/4.01    inference(definition_unfolding,[],[f79,f91])).
% 27.36/4.01  
% 27.36/4.01  fof(f86,plain,(
% 27.36/4.01    r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k2_tarski(sK2,sK3)),
% 27.36/4.01    inference(cnf_transformation,[],[f50])).
% 27.36/4.01  
% 27.36/4.01  fof(f100,plain,(
% 27.36/4.01    r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)),
% 27.36/4.01    inference(definition_unfolding,[],[f86,f65,f91,f91])).
% 27.36/4.01  
% 27.36/4.01  fof(f24,axiom,(
% 27.36/4.01    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2))),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f34,plain,(
% 27.36/4.01    ! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 27.36/4.01    inference(ennf_transformation,[],[f24])).
% 27.36/4.01  
% 27.36/4.01  fof(f35,plain,(
% 27.36/4.01    ! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 27.36/4.01    inference(flattening,[],[f34])).
% 27.36/4.01  
% 27.36/4.01  fof(f82,plain,(
% 27.36/4.01    ( ! [X2,X0,X1] : (k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 27.36/4.01    inference(cnf_transformation,[],[f35])).
% 27.36/4.01  
% 27.36/4.01  fof(f98,plain,(
% 27.36/4.01    ( ! [X2,X0,X1] : (k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 27.36/4.01    inference(definition_unfolding,[],[f82,f91,f91])).
% 27.36/4.01  
% 27.36/4.01  fof(f84,plain,(
% 27.36/4.01    ~r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3)),
% 27.36/4.01    inference(cnf_transformation,[],[f50])).
% 27.36/4.01  
% 27.36/4.01  fof(f102,plain,(
% 27.36/4.01    ~r2_hidden(sK2,sK4) | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)),
% 27.36/4.01    inference(definition_unfolding,[],[f84,f65,f91,f91])).
% 27.36/4.01  
% 27.36/4.01  fof(f63,plain,(
% 27.36/4.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 27.36/4.01    inference(cnf_transformation,[],[f44])).
% 27.36/4.01  
% 27.36/4.01  fof(f25,axiom,(
% 27.36/4.01    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 27.36/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.36/4.01  
% 27.36/4.01  fof(f36,plain,(
% 27.36/4.01    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 27.36/4.01    inference(ennf_transformation,[],[f25])).
% 27.36/4.01  
% 27.36/4.01  fof(f83,plain,(
% 27.36/4.01    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 27.36/4.01    inference(cnf_transformation,[],[f36])).
% 27.36/4.01  
% 27.36/4.01  fof(f99,plain,(
% 27.36/4.01    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 27.36/4.01    inference(definition_unfolding,[],[f83,f91])).
% 27.36/4.01  
% 27.36/4.01  cnf(c_0,plain,
% 27.36/4.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 27.36/4.01      inference(cnf_transformation,[],[f51]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_2,plain,
% 27.36/4.01      ( k3_xboole_0(X0,X0) = X0 ),
% 27.36/4.01      inference(cnf_transformation,[],[f53]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_18,plain,
% 27.36/4.01      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 27.36/4.01      inference(cnf_transformation,[],[f93]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_903,plain,
% 27.36/4.01      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 27.36/4.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1914,plain,
% 27.36/4.01      ( r1_xboole_0(k5_xboole_0(X0,X0),X0) = iProver_top ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_2,c_903]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_9,plain,
% 27.36/4.01      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 27.36/4.01      inference(cnf_transformation,[],[f60]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_909,plain,
% 27.36/4.01      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 27.36/4.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_7,plain,
% 27.36/4.01      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 27.36/4.01      inference(cnf_transformation,[],[f59]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_911,plain,
% 27.36/4.01      ( r1_xboole_0(X0,X1) != iProver_top
% 27.36/4.01      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 27.36/4.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_10596,plain,
% 27.36/4.01      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 27.36/4.01      | r1_xboole_0(X0,X1) != iProver_top ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_909,c_911]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_31656,plain,
% 27.36/4.01      ( k3_xboole_0(k5_xboole_0(X0,X0),X0) = k1_xboole_0 ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_1914,c_10596]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_14,plain,
% 27.36/4.01      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
% 27.36/4.01      inference(cnf_transformation,[],[f66]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1395,plain,
% 27.36/4.01      ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_2,c_14]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_3713,plain,
% 27.36/4.01      ( k3_xboole_0(k5_xboole_0(X0,X0),X0) = k5_xboole_0(X0,X0) ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_2,c_1395]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_31868,plain,
% 27.36/4.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 27.36/4.01      inference(demodulation,[status(thm)],[c_31656,c_3713]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_19,plain,
% 27.36/4.01      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 27.36/4.01      inference(cnf_transformation,[],[f71]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1,plain,
% 27.36/4.01      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 27.36/4.01      inference(cnf_transformation,[],[f52]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1037,plain,
% 27.36/4.01      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_19,c_1]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_16,plain,
% 27.36/4.01      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 27.36/4.01      inference(cnf_transformation,[],[f92]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_904,plain,
% 27.36/4.01      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 27.36/4.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_2230,plain,
% 27.36/4.01      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_0,c_904]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_3671,plain,
% 27.36/4.01      ( r1_tarski(k3_xboole_0(k5_xboole_0(X0,X1),X0),X0) = iProver_top ),
% 27.36/4.01      inference(demodulation,[status(thm)],[c_1395,c_2230]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_5274,plain,
% 27.36/4.01      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X0,X1)),X0) = iProver_top ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_0,c_3671]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_5909,plain,
% 27.36/4.01      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))),X0) = iProver_top ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_1037,c_5274]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_32226,plain,
% 27.36/4.01      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)),X0) = iProver_top ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_31868,c_5909]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_17,plain,
% 27.36/4.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.36/4.01      inference(cnf_transformation,[],[f69]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_32246,plain,
% 27.36/4.01      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 27.36/4.01      inference(demodulation,[status(thm)],[c_32226,c_17]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_15,plain,
% 27.36/4.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 27.36/4.01      inference(cnf_transformation,[],[f67]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_905,plain,
% 27.36/4.01      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 27.36/4.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_33192,plain,
% 27.36/4.01      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_32246,c_905]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_43351,plain,
% 27.36/4.01      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_0,c_33192]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_3356,plain,
% 27.36/4.01      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_17,c_1037]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_3714,plain,
% 27.36/4.01      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(k3_xboole_0(X1,X0),X0) ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_1395,c_3356]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1256,plain,
% 27.36/4.01      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_17,c_1]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_3752,plain,
% 27.36/4.01      ( k5_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(k5_xboole_0(X1,X0),X1) ),
% 27.36/4.01      inference(demodulation,[status(thm)],[c_3714,c_1256]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_45986,plain,
% 27.36/4.01      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = k5_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_43351,c_3752]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1398,plain,
% 27.36/4.01      ( k5_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(k5_xboole_0(X0,X1),X1) ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_2,c_14]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_4693,plain,
% 27.36/4.01      ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X1,X0),X0) ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_1398,c_1]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_3711,plain,
% 27.36/4.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_0,c_1395]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_7501,plain,
% 27.36/4.01      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(X0,X1),X0)) = k5_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_3711,c_3356]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_7544,plain,
% 27.36/4.01      ( k5_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
% 27.36/4.01      inference(demodulation,[status(thm)],[c_7501,c_1256]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_46054,plain,
% 27.36/4.01      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(X0,X1),X1),X1) = k3_xboole_0(k5_xboole_0(X1,X0),X1) ),
% 27.36/4.01      inference(light_normalisation,
% 27.36/4.01                [status(thm)],
% 27.36/4.01                [c_45986,c_4693,c_7544]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_46055,plain,
% 27.36/4.01      ( k3_xboole_0(X0,k5_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
% 27.36/4.01      inference(demodulation,[status(thm)],[c_46054,c_43351]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_20,plain,
% 27.36/4.01      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 27.36/4.01      inference(cnf_transformation,[],[f94]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_27,negated_conjecture,
% 27.36/4.01      ( ~ r2_hidden(sK3,sK4)
% 27.36/4.01      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 27.36/4.01      inference(cnf_transformation,[],[f101]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_896,plain,
% 27.36/4.01      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 27.36/4.01      | r2_hidden(sK3,sK4) != iProver_top ),
% 27.36/4.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1133,plain,
% 27.36/4.01      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 27.36/4.01      | r2_hidden(sK3,sK4) != iProver_top ),
% 27.36/4.01      inference(demodulation,[status(thm)],[c_0,c_896]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1544,plain,
% 27.36/4.01      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2),k3_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)
% 27.36/4.01      | r2_hidden(sK3,sK4) != iProver_top ),
% 27.36/4.01      inference(demodulation,[status(thm)],[c_20,c_1133]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_3674,plain,
% 27.36/4.01      ( k3_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2),sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)
% 27.36/4.01      | r2_hidden(sK3,sK4) != iProver_top ),
% 27.36/4.01      inference(demodulation,[status(thm)],[c_1395,c_1544]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_136805,plain,
% 27.36/4.01      ( k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2),k5_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)
% 27.36/4.01      | r2_hidden(sK3,sK4) != iProver_top ),
% 27.36/4.01      inference(demodulation,[status(thm)],[c_46055,c_3674]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_12,plain,
% 27.36/4.01      ( r1_tarski(X0,X0) ),
% 27.36/4.01      inference(cnf_transformation,[],[f104]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1080,plain,
% 27.36/4.01      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_12]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1206,plain,
% 27.36/4.01      ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_1080]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1209,plain,
% 27.36/4.01      ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top ),
% 27.36/4.01      inference(predicate_to_equality,[status(thm)],[c_1206]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_4,plain,
% 27.36/4.01      ( ~ r2_hidden(X0,X1)
% 27.36/4.01      | r2_hidden(X0,X2)
% 27.36/4.01      | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 27.36/4.01      inference(cnf_transformation,[],[f56]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1166,plain,
% 27.36/4.01      ( r2_hidden(X0,X1)
% 27.36/4.01      | ~ r2_hidden(X0,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0))
% 27.36/4.01      | r2_hidden(X0,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1)) ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_4]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1580,plain,
% 27.36/4.01      ( ~ r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3))
% 27.36/4.01      | r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),sK4))
% 27.36/4.01      | r2_hidden(sK3,sK4) ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_1166]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1581,plain,
% 27.36/4.01      ( r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3)) != iProver_top
% 27.36/4.01      | r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),sK4)) = iProver_top
% 27.36/4.01      | r2_hidden(sK3,sK4) = iProver_top ),
% 27.36/4.01      inference(predicate_to_equality,[status(thm)],[c_1580]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1583,plain,
% 27.36/4.01      ( r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
% 27.36/4.01      | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = iProver_top
% 27.36/4.01      | r2_hidden(sK3,sK4) = iProver_top ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_1581]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_22,plain,
% 27.36/4.01      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
% 27.36/4.01      | r2_hidden(X1,X2) ),
% 27.36/4.01      inference(cnf_transformation,[],[f96]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1079,plain,
% 27.36/4.01      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
% 27.36/4.01      | r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_22]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1800,plain,
% 27.36/4.01      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3))
% 27.36/4.01      | r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3)) ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_1079]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1801,plain,
% 27.36/4.01      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3)) != iProver_top
% 27.36/4.01      | r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3)) = iProver_top ),
% 27.36/4.01      inference(predicate_to_equality,[status(thm)],[c_1800]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1803,plain,
% 27.36/4.01      ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
% 27.36/4.01      | r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_1801]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_23,plain,
% 27.36/4.01      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
% 27.36/4.01      | r2_hidden(X0,X2) ),
% 27.36/4.01      inference(cnf_transformation,[],[f97]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1114,plain,
% 27.36/4.01      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
% 27.36/4.01      | r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_23]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1866,plain,
% 27.36/4.01      ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 27.36/4.01      | r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_1114]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1869,plain,
% 27.36/4.01      ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
% 27.36/4.01      | r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = iProver_top ),
% 27.36/4.01      inference(predicate_to_equality,[status(thm)],[c_1866]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_26,negated_conjecture,
% 27.36/4.01      ( r2_hidden(sK2,sK4)
% 27.36/4.01      | r2_hidden(sK3,sK4)
% 27.36/4.01      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 27.36/4.01      inference(cnf_transformation,[],[f100]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_897,plain,
% 27.36/4.01      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 27.36/4.01      | r2_hidden(sK2,sK4) = iProver_top
% 27.36/4.01      | r2_hidden(sK3,sK4) = iProver_top ),
% 27.36/4.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1132,plain,
% 27.36/4.01      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 27.36/4.01      | r2_hidden(sK2,sK4) = iProver_top
% 27.36/4.01      | r2_hidden(sK3,sK4) = iProver_top ),
% 27.36/4.01      inference(demodulation,[status(thm)],[c_0,c_897]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_3669,plain,
% 27.36/4.01      ( k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 27.36/4.01      | r2_hidden(sK2,sK4) = iProver_top
% 27.36/4.01      | r2_hidden(sK3,sK4) = iProver_top ),
% 27.36/4.01      inference(demodulation,[status(thm)],[c_1395,c_1132]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_3942,plain,
% 27.36/4.01      ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 27.36/4.01      | r2_hidden(sK2,sK4) = iProver_top
% 27.36/4.01      | r2_hidden(sK3,sK4) = iProver_top ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_0,c_3669]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_24,plain,
% 27.36/4.01      ( ~ r2_hidden(X0,X1)
% 27.36/4.01      | ~ r2_hidden(X2,X1)
% 27.36/4.01      | k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) ),
% 27.36/4.01      inference(cnf_transformation,[],[f98]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_2051,plain,
% 27.36/4.01      ( ~ r2_hidden(sK2,X0)
% 27.36/4.01      | ~ r2_hidden(sK3,X0)
% 27.36/4.01      | k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),X0) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_24]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_5255,plain,
% 27.36/4.01      ( ~ r2_hidden(sK2,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),X1))
% 27.36/4.01      | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),X1))
% 27.36/4.01      | k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),X1)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_2051]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_8561,plain,
% 27.36/4.01      ( ~ r2_hidden(sK2,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),sK4))
% 27.36/4.01      | ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),sK4))
% 27.36/4.01      | k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_5255]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_8563,plain,
% 27.36/4.01      ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 27.36/4.01      | r2_hidden(sK2,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),sK4)) != iProver_top
% 27.36/4.01      | r2_hidden(sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),sK4)) != iProver_top ),
% 27.36/4.01      inference(predicate_to_equality,[status(thm)],[c_8561]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_8565,plain,
% 27.36/4.01      ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 27.36/4.01      | r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != iProver_top
% 27.36/4.01      | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != iProver_top ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_8563]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1308,plain,
% 27.36/4.01      ( ~ r2_hidden(sK2,X0)
% 27.36/4.01      | r2_hidden(sK2,k5_xboole_0(X0,sK4))
% 27.36/4.01      | r2_hidden(sK2,sK4) ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_4]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_8562,plain,
% 27.36/4.01      ( ~ r2_hidden(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3))
% 27.36/4.01      | r2_hidden(sK2,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),sK4))
% 27.36/4.01      | r2_hidden(sK2,sK4) ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_1308]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_8567,plain,
% 27.36/4.01      ( r2_hidden(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3)) != iProver_top
% 27.36/4.01      | r2_hidden(sK2,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),sK4)) = iProver_top
% 27.36/4.01      | r2_hidden(sK2,sK4) = iProver_top ),
% 27.36/4.01      inference(predicate_to_equality,[status(thm)],[c_8562]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_8569,plain,
% 27.36/4.01      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top
% 27.36/4.01      | r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = iProver_top
% 27.36/4.01      | r2_hidden(sK2,sK4) = iProver_top ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_8567]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_28,negated_conjecture,
% 27.36/4.01      ( ~ r2_hidden(sK2,sK4)
% 27.36/4.01      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 27.36/4.01      inference(cnf_transformation,[],[f102]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_895,plain,
% 27.36/4.01      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 27.36/4.01      | r2_hidden(sK2,sK4) != iProver_top ),
% 27.36/4.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1134,plain,
% 27.36/4.01      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 27.36/4.01      | r2_hidden(sK2,sK4) != iProver_top ),
% 27.36/4.01      inference(demodulation,[status(thm)],[c_0,c_895]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_3670,plain,
% 27.36/4.01      ( k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 27.36/4.01      | r2_hidden(sK2,sK4) != iProver_top ),
% 27.36/4.01      inference(demodulation,[status(thm)],[c_1395,c_1134]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_136803,plain,
% 27.36/4.01      ( k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_xboole_0(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 27.36/4.01      | r2_hidden(sK2,sK4) != iProver_top ),
% 27.36/4.01      inference(demodulation,[status(thm)],[c_46055,c_3670]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_29,plain,
% 27.36/4.01      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 27.36/4.01      | r2_hidden(sK2,sK4) != iProver_top ),
% 27.36/4.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_10,plain,
% 27.36/4.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 27.36/4.01      inference(cnf_transformation,[],[f63]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1101,plain,
% 27.36/4.01      ( ~ r1_tarski(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 27.36/4.01      | ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),X0)
% 27.36/4.01      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = X0 ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_10]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1205,plain,
% 27.36/4.01      ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 27.36/4.01      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_1101]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_543,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1109,plain,
% 27.36/4.01      ( X0 != X1
% 27.36/4.01      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != X1
% 27.36/4.01      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = X0 ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_543]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1214,plain,
% 27.36/4.01      ( X0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 27.36/4.01      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = X0
% 27.36/4.01      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_1109]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1731,plain,
% 27.36/4.01      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 27.36/4.01      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
% 27.36/4.01      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_1214]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_542,plain,( X0 = X0 ),theory(equality) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1777,plain,
% 27.36/4.01      ( sK4 = sK4 ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_542]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_6284,plain,
% 27.36/4.01      ( r1_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4) ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_18]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_6285,plain,
% 27.36/4.01      ( r1_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4) = iProver_top ),
% 27.36/4.01      inference(predicate_to_equality,[status(thm)],[c_6284]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_547,plain,
% 27.36/4.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.36/4.01      theory(equality) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_2420,plain,
% 27.36/4.01      ( r1_xboole_0(X0,X1)
% 27.36/4.01      | ~ r1_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X3)
% 27.36/4.01      | X1 != X3
% 27.36/4.01      | X0 != k5_xboole_0(X2,k3_xboole_0(X2,X3)) ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_547]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_3486,plain,
% 27.36/4.01      ( r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),X0)
% 27.36/4.01      | ~ r1_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4)
% 27.36/4.01      | X0 != sK4
% 27.36/4.01      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)) ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_2420]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_17009,plain,
% 27.36/4.01      ( r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)
% 27.36/4.01      | ~ r1_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4)
% 27.36/4.01      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
% 27.36/4.01      | sK4 != sK4 ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_3486]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_17010,plain,
% 27.36/4.01      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4))
% 27.36/4.01      | sK4 != sK4
% 27.36/4.01      | r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4) = iProver_top
% 27.36/4.01      | r1_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)),sK4) != iProver_top ),
% 27.36/4.01      inference(predicate_to_equality,[status(thm)],[c_17009]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_25,plain,
% 27.36/4.01      ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
% 27.36/4.01      | ~ r2_hidden(X0,X2) ),
% 27.36/4.01      inference(cnf_transformation,[],[f99]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_47925,plain,
% 27.36/4.01      ( ~ r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4)
% 27.36/4.01      | ~ r2_hidden(sK2,sK4) ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_25]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_47926,plain,
% 27.36/4.01      ( r1_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),sK4) != iProver_top
% 27.36/4.01      | r2_hidden(sK2,sK4) != iProver_top ),
% 27.36/4.01      inference(predicate_to_equality,[status(thm)],[c_47925]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_137727,plain,
% 27.36/4.01      ( r2_hidden(sK2,sK4) != iProver_top ),
% 27.36/4.01      inference(global_propositional_subsumption,
% 27.36/4.01                [status(thm)],
% 27.36/4.01                [c_136803,c_29,c_1205,c_1206,c_1731,c_1777,c_6285,
% 27.36/4.01                 c_17010,c_47926]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_137733,plain,
% 27.36/4.01      ( k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2),k5_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2))) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2) ),
% 27.36/4.01      inference(global_propositional_subsumption,
% 27.36/4.01                [status(thm)],
% 27.36/4.01                [c_136805,c_29,c_1205,c_1206,c_1209,c_1583,c_1731,c_1777,
% 27.36/4.01                 c_1803,c_1869,c_3942,c_6285,c_8565,c_8569,c_17010,
% 27.36/4.01                 c_47926]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1912,plain,
% 27.36/4.01      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = iProver_top ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_0,c_903]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_3672,plain,
% 27.36/4.01      ( r1_xboole_0(k3_xboole_0(k5_xboole_0(X0,X1),X0),X1) = iProver_top ),
% 27.36/4.01      inference(demodulation,[status(thm)],[c_1395,c_1912]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_5715,plain,
% 27.36/4.01      ( r1_xboole_0(k3_xboole_0(X0,k5_xboole_0(X0,X1)),X1) = iProver_top ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_0,c_3672]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_6102,plain,
% 27.36/4.01      ( r1_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,X0)),X1) = iProver_top ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_1,c_5715]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_137807,plain,
% 27.36/4.01      ( r1_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2),sK4) = iProver_top ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_137733,c_6102]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_898,plain,
% 27.36/4.01      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != iProver_top
% 27.36/4.01      | r2_hidden(X0,X2) != iProver_top ),
% 27.36/4.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_138357,plain,
% 27.36/4.01      ( r2_hidden(sK3,sK4) != iProver_top ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_137807,c_898]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1723,plain,
% 27.36/4.01      ( k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2),k3_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 27.36/4.01      | r2_hidden(sK2,sK4) = iProver_top
% 27.36/4.01      | r2_hidden(sK3,sK4) = iProver_top ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_20,c_1132]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_3673,plain,
% 27.36/4.01      ( k3_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2),sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 27.36/4.01      | r2_hidden(sK2,sK4) = iProver_top
% 27.36/4.01      | r2_hidden(sK3,sK4) = iProver_top ),
% 27.36/4.01      inference(demodulation,[status(thm)],[c_1395,c_1723]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_4047,plain,
% 27.36/4.01      ( k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2),sK4)) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 27.36/4.01      | r2_hidden(sK2,sK4) = iProver_top
% 27.36/4.01      | r2_hidden(sK3,sK4) = iProver_top ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_0,c_3673]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_4907,plain,
% 27.36/4.01      ( k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2),k5_xboole_0(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2))) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 27.36/4.01      | r2_hidden(sK2,sK4) = iProver_top
% 27.36/4.01      | r2_hidden(sK3,sK4) = iProver_top ),
% 27.36/4.01      inference(superposition,[status(thm)],[c_1,c_4047]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_137736,plain,
% 27.36/4.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 27.36/4.01      | r2_hidden(sK2,sK4) = iProver_top
% 27.36/4.01      | r2_hidden(sK3,sK4) = iProver_top ),
% 27.36/4.01      inference(demodulation,[status(thm)],[c_137733,c_4907]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(c_1316,plain,
% 27.36/4.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 27.36/4.01      inference(instantiation,[status(thm)],[c_20]) ).
% 27.36/4.01  
% 27.36/4.01  cnf(contradiction,plain,
% 27.36/4.01      ( $false ),
% 27.36/4.01      inference(minisat,[status(thm)],[c_138357,c_137736,c_137727,c_1316]) ).
% 27.36/4.01  
% 27.36/4.01  
% 27.36/4.01  % SZS output end CNFRefutation for theBenchmark.p
% 27.36/4.01  
% 27.36/4.01  ------                               Statistics
% 27.36/4.01  
% 27.36/4.01  ------ General
% 27.36/4.01  
% 27.36/4.01  abstr_ref_over_cycles:                  0
% 27.36/4.01  abstr_ref_under_cycles:                 0
% 27.36/4.01  gc_basic_clause_elim:                   0
% 27.36/4.01  forced_gc_time:                         0
% 27.36/4.01  parsing_time:                           0.019
% 27.36/4.01  unif_index_cands_time:                  0.
% 27.36/4.01  unif_index_add_time:                    0.
% 27.36/4.01  orderings_time:                         0.
% 27.36/4.01  out_proof_time:                         0.023
% 27.36/4.01  total_time:                             3.048
% 27.36/4.01  num_of_symbols:                         43
% 27.36/4.01  num_of_terms:                           134915
% 27.36/4.01  
% 27.36/4.01  ------ Preprocessing
% 27.36/4.01  
% 27.36/4.01  num_of_splits:                          0
% 27.36/4.01  num_of_split_atoms:                     0
% 27.36/4.01  num_of_reused_defs:                     0
% 27.36/4.01  num_eq_ax_congr_red:                    12
% 27.36/4.01  num_of_sem_filtered_clauses:            1
% 27.36/4.01  num_of_subtypes:                        0
% 27.36/4.01  monotx_restored_types:                  0
% 27.36/4.01  sat_num_of_epr_types:                   0
% 27.36/4.01  sat_num_of_non_cyclic_types:            0
% 27.36/4.01  sat_guarded_non_collapsed_types:        0
% 27.36/4.01  num_pure_diseq_elim:                    0
% 27.36/4.01  simp_replaced_by:                       0
% 27.36/4.01  res_preprocessed:                       127
% 27.36/4.01  prep_upred:                             0
% 27.36/4.01  prep_unflattend:                        16
% 27.36/4.01  smt_new_axioms:                         0
% 27.36/4.01  pred_elim_cands:                        3
% 27.36/4.01  pred_elim:                              0
% 27.36/4.01  pred_elim_cl:                           0
% 27.36/4.01  pred_elim_cycles:                       2
% 27.36/4.01  merged_defs:                            0
% 27.36/4.01  merged_defs_ncl:                        0
% 27.36/4.01  bin_hyper_res:                          0
% 27.36/4.01  prep_cycles:                            4
% 27.36/4.01  pred_elim_time:                         0.003
% 27.36/4.01  splitting_time:                         0.
% 27.36/4.01  sem_filter_time:                        0.
% 27.36/4.01  monotx_time:                            0.
% 27.36/4.01  subtype_inf_time:                       0.
% 27.36/4.01  
% 27.36/4.01  ------ Problem properties
% 27.36/4.01  
% 27.36/4.01  clauses:                                28
% 27.36/4.01  conjectures:                            3
% 27.36/4.01  epr:                                    2
% 27.36/4.01  horn:                                   22
% 27.36/4.01  ground:                                 3
% 27.36/4.01  unary:                                  11
% 27.36/4.01  binary:                                 9
% 27.36/4.01  lits:                                   53
% 27.36/4.01  lits_eq:                                14
% 27.36/4.01  fd_pure:                                0
% 27.36/4.01  fd_pseudo:                              0
% 27.36/4.01  fd_cond:                                1
% 27.36/4.01  fd_pseudo_cond:                         1
% 27.36/4.01  ac_symbols:                             1
% 27.36/4.01  
% 27.36/4.01  ------ Propositional Solver
% 27.36/4.01  
% 27.36/4.01  prop_solver_calls:                      33
% 27.36/4.01  prop_fast_solver_calls:                 1079
% 27.36/4.01  smt_solver_calls:                       0
% 27.36/4.01  smt_fast_solver_calls:                  0
% 27.36/4.01  prop_num_of_clauses:                    32480
% 27.36/4.01  prop_preprocess_simplified:             42972
% 27.36/4.01  prop_fo_subsumed:                       2
% 27.36/4.01  prop_solver_time:                       0.
% 27.36/4.01  smt_solver_time:                        0.
% 27.36/4.01  smt_fast_solver_time:                   0.
% 27.36/4.01  prop_fast_solver_time:                  0.
% 27.36/4.01  prop_unsat_core_time:                   0.003
% 27.36/4.01  
% 27.36/4.01  ------ QBF
% 27.36/4.01  
% 27.36/4.01  qbf_q_res:                              0
% 27.36/4.01  qbf_num_tautologies:                    0
% 27.36/4.01  qbf_prep_cycles:                        0
% 27.36/4.01  
% 27.36/4.01  ------ BMC1
% 27.36/4.01  
% 27.36/4.01  bmc1_current_bound:                     -1
% 27.36/4.01  bmc1_last_solved_bound:                 -1
% 27.36/4.01  bmc1_unsat_core_size:                   -1
% 27.36/4.01  bmc1_unsat_core_parents_size:           -1
% 27.36/4.01  bmc1_merge_next_fun:                    0
% 27.36/4.01  bmc1_unsat_core_clauses_time:           0.
% 27.36/4.01  
% 27.36/4.01  ------ Instantiation
% 27.36/4.01  
% 27.36/4.01  inst_num_of_clauses:                    5425
% 27.36/4.01  inst_num_in_passive:                    3677
% 27.36/4.01  inst_num_in_active:                     1318
% 27.36/4.01  inst_num_in_unprocessed:                431
% 27.36/4.01  inst_num_of_loops:                      1840
% 27.36/4.01  inst_num_of_learning_restarts:          0
% 27.36/4.01  inst_num_moves_active_passive:          520
% 27.36/4.01  inst_lit_activity:                      0
% 27.36/4.01  inst_lit_activity_moves:                1
% 27.36/4.01  inst_num_tautologies:                   0
% 27.36/4.01  inst_num_prop_implied:                  0
% 27.36/4.01  inst_num_existing_simplified:           0
% 27.36/4.01  inst_num_eq_res_simplified:             0
% 27.36/4.01  inst_num_child_elim:                    0
% 27.36/4.01  inst_num_of_dismatching_blockings:      6434
% 27.36/4.01  inst_num_of_non_proper_insts:           8256
% 27.36/4.01  inst_num_of_duplicates:                 0
% 27.36/4.01  inst_inst_num_from_inst_to_res:         0
% 27.36/4.01  inst_dismatching_checking_time:         0.
% 27.36/4.01  
% 27.36/4.01  ------ Resolution
% 27.36/4.01  
% 27.36/4.01  res_num_of_clauses:                     0
% 27.36/4.01  res_num_in_passive:                     0
% 27.36/4.01  res_num_in_active:                      0
% 27.36/4.01  res_num_of_loops:                       131
% 27.36/4.01  res_forward_subset_subsumed:            646
% 27.36/4.01  res_backward_subset_subsumed:           2
% 27.36/4.01  res_forward_subsumed:                   0
% 27.36/4.01  res_backward_subsumed:                  0
% 27.36/4.01  res_forward_subsumption_resolution:     0
% 27.36/4.01  res_backward_subsumption_resolution:    0
% 27.36/4.01  res_clause_to_clause_subsumption:       203392
% 27.36/4.01  res_orphan_elimination:                 0
% 27.36/4.01  res_tautology_del:                      555
% 27.36/4.01  res_num_eq_res_simplified:              0
% 27.36/4.01  res_num_sel_changes:                    0
% 27.36/4.01  res_moves_from_active_to_pass:          0
% 27.36/4.01  
% 27.36/4.01  ------ Superposition
% 27.36/4.01  
% 27.36/4.01  sup_time_total:                         0.
% 27.36/4.01  sup_time_generating:                    0.
% 27.36/4.01  sup_time_sim_full:                      0.
% 27.36/4.01  sup_time_sim_immed:                     0.
% 27.36/4.01  
% 27.36/4.01  sup_num_of_clauses:                     9362
% 27.36/4.01  sup_num_in_active:                      180
% 27.36/4.01  sup_num_in_passive:                     9182
% 27.36/4.01  sup_num_of_loops:                       367
% 27.36/4.01  sup_fw_superposition:                   23478
% 27.36/4.01  sup_bw_superposition:                   20292
% 27.36/4.01  sup_immediate_simplified:               12972
% 27.36/4.01  sup_given_eliminated:                   3
% 27.36/4.01  comparisons_done:                       0
% 27.36/4.01  comparisons_avoided:                    2
% 27.36/4.01  
% 27.36/4.01  ------ Simplifications
% 27.36/4.01  
% 27.36/4.01  
% 27.36/4.01  sim_fw_subset_subsumed:                 43
% 27.36/4.01  sim_bw_subset_subsumed:                 4
% 27.36/4.01  sim_fw_subsumed:                        1909
% 27.36/4.01  sim_bw_subsumed:                        53
% 27.36/4.01  sim_fw_subsumption_res:                 2
% 27.36/4.01  sim_bw_subsumption_res:                 0
% 27.36/4.01  sim_tautology_del:                      25
% 27.36/4.01  sim_eq_tautology_del:                   1399
% 27.36/4.01  sim_eq_res_simp:                        0
% 27.36/4.01  sim_fw_demodulated:                     6470
% 27.36/4.01  sim_bw_demodulated:                     525
% 27.36/4.01  sim_light_normalised:                   6014
% 27.36/4.01  sim_joinable_taut:                      317
% 27.36/4.01  sim_joinable_simp:                      0
% 27.36/4.01  sim_ac_normalised:                      0
% 27.36/4.01  sim_smt_subsumption:                    0
% 27.36/4.01  
%------------------------------------------------------------------------------
