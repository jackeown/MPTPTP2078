%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:10 EST 2020

% Result     : Theorem 7.34s
% Output     : CNFRefutation 7.34s
% Verified   : 
% Statistics : Number of formulae       :  154 (2620 expanded)
%              Number of clauses        :   85 ( 476 expanded)
%              Number of leaves         :   18 ( 682 expanded)
%              Depth                    :   22
%              Number of atoms          :  423 (10243 expanded)
%              Number of equality atoms :  240 (3696 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f2])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f17])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f53])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f54])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f55])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f56])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f40,f57])).

fof(f73,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f66])).

fof(f74,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f73])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f31,f36])).

fof(f71,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f39,f57])).

fof(f75,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
        & ( r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) )
   => ( ( ~ r2_hidden(sK2,sK3)
        | k4_xboole_0(k1_tarski(sK2),sK3) != k1_xboole_0 )
      & ( r2_hidden(sK2,sK3)
        | k4_xboole_0(k1_tarski(sK2),sK3) = k1_xboole_0 ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( ~ r2_hidden(sK2,sK3)
      | k4_xboole_0(k1_tarski(sK2),sK3) != k1_xboole_0 )
    & ( r2_hidden(sK2,sK3)
      | k4_xboole_0(k1_tarski(sK2),sK3) = k1_xboole_0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f27])).

fof(f51,plain,
    ( ~ r2_hidden(sK2,sK3)
    | k4_xboole_0(k1_tarski(sK2),sK3) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,
    ( ~ r2_hidden(sK2,sK3)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f51,f36,f57])).

fof(f50,plain,
    ( r2_hidden(sK2,sK3)
    | k4_xboole_0(k1_tarski(sK2),sK3) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,
    ( r2_hidden(sK2,sK3)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f50,f36,f57])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f30,f36])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f34,f36])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_489,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_483,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_487,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_908,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k1_xboole_0)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_487])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_911,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_908,c_8])).

cnf(c_1230,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_483,c_911])).

cnf(c_2036,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_489,c_1230])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_482,plain,
    ( X0 = X1
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2799,plain,
    ( sK0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1,k1_xboole_0) = X0
    | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2036,c_482])).

cnf(c_13,negated_conjecture,
    ( ~ r2_hidden(sK2,sK3)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_481,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_xboole_0
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_19251,plain,
    ( sK0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,k1_xboole_0) = sK2
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2799,c_481])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK2,sK3)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_480,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2043,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r2_hidden(sK0(X0,X1,X0),X0) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_489])).

cnf(c_2045,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r2_hidden(sK0(X0,X1,X0),X0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2043])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_491,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3056,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r2_hidden(sK0(X0,X1,X0),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2045,c_491])).

cnf(c_3077,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r2_hidden(sK0(X0,X1,X0),X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3056,c_2045])).

cnf(c_4263,plain,
    ( sK0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X0) = X1
    | k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_3077,c_482])).

cnf(c_10494,plain,
    ( sK0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X0) = X1
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4263,c_487])).

cnf(c_15717,plain,
    ( sK0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X0) = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_483,c_10494])).

cnf(c_15902,plain,
    ( sK0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = sK2
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_480,c_15717])).

cnf(c_18,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_21,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_32,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)))
    | r2_hidden(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_35,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)))
    | ~ r2_hidden(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_590,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | r2_hidden(X0,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_648,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
    | r2_hidden(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_590])).

cnf(c_179,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_630,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4)))
    | X2 != X0
    | k5_xboole_0(X3,k3_xboole_0(X3,X4)) != X1 ),
    inference(instantiation,[status(thm)],[c_179])).

cnf(c_724,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
    | r2_hidden(X3,k5_xboole_0(X4,k3_xboole_0(X4,X5)))
    | X3 != X0
    | k5_xboole_0(X4,k3_xboole_0(X4,X5)) != k5_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_630])).

cnf(c_1024,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | ~ r2_hidden(X3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
    | X0 != X3
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_724])).

cnf(c_1026,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
    | r2_hidden(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)))
    | k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1024])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_490,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2257,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1
    | r2_hidden(sK0(X0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_489,c_490])).

cnf(c_2798,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) = k1_xboole_0
    | r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2,k1_xboole_0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2036,c_487])).

cnf(c_3649,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2257,c_2798])).

cnf(c_3651,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3649,c_7,c_8])).

cnf(c_3660,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3651])).

cnf(c_176,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_723,plain,
    ( X0 != X1
    | k5_xboole_0(X2,k3_xboole_0(X2,X3)) != X1
    | k5_xboole_0(X2,k3_xboole_0(X2,X3)) = X0 ),
    inference(instantiation,[status(thm)],[c_176])).

cnf(c_4382,plain,
    ( X0 != k1_xboole_0
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X0
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_723])).

cnf(c_13358,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4382])).

cnf(c_13359,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_xboole_0
    | k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
    | k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13358])).

cnf(c_16399,plain,
    ( sK0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15902,c_13,c_18,c_21,c_32,c_35,c_648,c_1026,c_3660,c_13359])).

cnf(c_16412,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = sK3
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_16399,c_2045])).

cnf(c_15,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_20,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_22,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_31,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_33,plain,
    ( r2_hidden(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))) != iProver_top
    | r2_hidden(sK2,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_624,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,k5_xboole_0(X0,k3_xboole_0(X0,sK3)))
    | r2_hidden(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_625,plain,
    ( r2_hidden(sK2,X0) != iProver_top
    | r2_hidden(sK2,k5_xboole_0(X0,k3_xboole_0(X0,sK3))) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_624])).

cnf(c_627,plain,
    ( r2_hidden(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top
    | r2_hidden(sK2,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_649,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_648])).

cnf(c_1025,plain,
    ( X0 != X1
    | k5_xboole_0(X2,k3_xboole_0(X2,X3)) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = iProver_top
    | r2_hidden(X1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1024])).

cnf(c_1027,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
    | sK2 != sK2
    | r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) != iProver_top
    | r2_hidden(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1025])).

cnf(c_4262,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = X0
    | r2_hidden(sK0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)),X0),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3077,c_487])).

cnf(c_4404,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_2045,c_4262])).

cnf(c_3059,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2045,c_487])).

cnf(c_4448,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))),X2)) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))
    | r2_hidden(sK0(X0,X2,X0),k5_xboole_0(X1,k3_xboole_0(X1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4404,c_3059])).

cnf(c_4480,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r2_hidden(sK0(X0,X1,X0),k5_xboole_0(X2,k3_xboole_0(X2,X0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4448,c_4404])).

cnf(c_16409,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = sK3
    | r2_hidden(sK2,k5_xboole_0(X0,k3_xboole_0(X0,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_16399,c_4480])).

cnf(c_669,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(X0,k3_xboole_0(X0,sK3)))
    | ~ r2_hidden(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_670,plain,
    ( r2_hidden(sK2,k5_xboole_0(X0,k3_xboole_0(X0,sK3))) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_669])).

cnf(c_16691,plain,
    ( r2_hidden(sK2,k5_xboole_0(X0,k3_xboole_0(X0,sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16409,c_15,c_13,c_18,c_21,c_32,c_35,c_648,c_670,c_1026,c_3660,c_13359])).

cnf(c_16694,plain,
    ( r2_hidden(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_16691])).

cnf(c_17026,plain,
    ( r2_hidden(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16412,c_15,c_13,c_18,c_21,c_32,c_35,c_648,c_1026,c_3660,c_13359])).

cnf(c_20232,plain,
    ( sK0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,k1_xboole_0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19251,c_15,c_13,c_18,c_21,c_32,c_35,c_648,c_1026,c_3660,c_13359])).

cnf(c_20239,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0
    | r2_hidden(sK0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,k1_xboole_0),k1_xboole_0) = iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_20232,c_490])).

cnf(c_20261,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0
    | r2_hidden(sK2,sK3) != iProver_top
    | r2_hidden(sK2,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20239,c_20232])).

cnf(c_1241,plain,
    ( r2_hidden(sK2,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1230])).

cnf(c_16,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_xboole_0
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20261,c_17026,c_1241,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n020.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 20:29:07 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.34/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.34/1.50  
% 7.34/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.34/1.50  
% 7.34/1.50  ------  iProver source info
% 7.34/1.50  
% 7.34/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.34/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.34/1.50  git: non_committed_changes: false
% 7.34/1.50  git: last_make_outside_of_git: false
% 7.34/1.50  
% 7.34/1.50  ------ 
% 7.34/1.50  
% 7.34/1.50  ------ Input Options
% 7.34/1.50  
% 7.34/1.50  --out_options                           all
% 7.34/1.50  --tptp_safe_out                         true
% 7.34/1.50  --problem_path                          ""
% 7.34/1.50  --include_path                          ""
% 7.34/1.50  --clausifier                            res/vclausify_rel
% 7.34/1.50  --clausifier_options                    --mode clausify
% 7.34/1.50  --stdin                                 false
% 7.34/1.50  --stats_out                             all
% 7.34/1.50  
% 7.34/1.50  ------ General Options
% 7.34/1.50  
% 7.34/1.50  --fof                                   false
% 7.34/1.50  --time_out_real                         305.
% 7.34/1.50  --time_out_virtual                      -1.
% 7.34/1.50  --symbol_type_check                     false
% 7.34/1.50  --clausify_out                          false
% 7.34/1.50  --sig_cnt_out                           false
% 7.34/1.50  --trig_cnt_out                          false
% 7.34/1.50  --trig_cnt_out_tolerance                1.
% 7.34/1.50  --trig_cnt_out_sk_spl                   false
% 7.34/1.50  --abstr_cl_out                          false
% 7.34/1.50  
% 7.34/1.50  ------ Global Options
% 7.34/1.50  
% 7.34/1.50  --schedule                              default
% 7.34/1.50  --add_important_lit                     false
% 7.34/1.50  --prop_solver_per_cl                    1000
% 7.34/1.50  --min_unsat_core                        false
% 7.34/1.50  --soft_assumptions                      false
% 7.34/1.50  --soft_lemma_size                       3
% 7.34/1.50  --prop_impl_unit_size                   0
% 7.34/1.50  --prop_impl_unit                        []
% 7.34/1.50  --share_sel_clauses                     true
% 7.34/1.50  --reset_solvers                         false
% 7.34/1.50  --bc_imp_inh                            [conj_cone]
% 7.34/1.50  --conj_cone_tolerance                   3.
% 7.34/1.50  --extra_neg_conj                        none
% 7.34/1.50  --large_theory_mode                     true
% 7.34/1.50  --prolific_symb_bound                   200
% 7.34/1.50  --lt_threshold                          2000
% 7.34/1.50  --clause_weak_htbl                      true
% 7.34/1.50  --gc_record_bc_elim                     false
% 7.34/1.50  
% 7.34/1.50  ------ Preprocessing Options
% 7.34/1.50  
% 7.34/1.50  --preprocessing_flag                    true
% 7.34/1.50  --time_out_prep_mult                    0.1
% 7.34/1.50  --splitting_mode                        input
% 7.34/1.50  --splitting_grd                         true
% 7.34/1.50  --splitting_cvd                         false
% 7.34/1.50  --splitting_cvd_svl                     false
% 7.34/1.50  --splitting_nvd                         32
% 7.34/1.50  --sub_typing                            true
% 7.34/1.50  --prep_gs_sim                           true
% 7.34/1.50  --prep_unflatten                        true
% 7.34/1.50  --prep_res_sim                          true
% 7.34/1.50  --prep_upred                            true
% 7.34/1.50  --prep_sem_filter                       exhaustive
% 7.34/1.50  --prep_sem_filter_out                   false
% 7.34/1.50  --pred_elim                             true
% 7.34/1.50  --res_sim_input                         true
% 7.34/1.50  --eq_ax_congr_red                       true
% 7.34/1.50  --pure_diseq_elim                       true
% 7.34/1.50  --brand_transform                       false
% 7.34/1.50  --non_eq_to_eq                          false
% 7.34/1.50  --prep_def_merge                        true
% 7.34/1.50  --prep_def_merge_prop_impl              false
% 7.34/1.50  --prep_def_merge_mbd                    true
% 7.34/1.50  --prep_def_merge_tr_red                 false
% 7.34/1.50  --prep_def_merge_tr_cl                  false
% 7.34/1.50  --smt_preprocessing                     true
% 7.34/1.50  --smt_ac_axioms                         fast
% 7.34/1.50  --preprocessed_out                      false
% 7.34/1.50  --preprocessed_stats                    false
% 7.34/1.50  
% 7.34/1.50  ------ Abstraction refinement Options
% 7.34/1.50  
% 7.34/1.50  --abstr_ref                             []
% 7.34/1.50  --abstr_ref_prep                        false
% 7.34/1.50  --abstr_ref_until_sat                   false
% 7.34/1.50  --abstr_ref_sig_restrict                funpre
% 7.34/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.34/1.50  --abstr_ref_under                       []
% 7.34/1.50  
% 7.34/1.50  ------ SAT Options
% 7.34/1.50  
% 7.34/1.50  --sat_mode                              false
% 7.34/1.50  --sat_fm_restart_options                ""
% 7.34/1.50  --sat_gr_def                            false
% 7.34/1.50  --sat_epr_types                         true
% 7.34/1.50  --sat_non_cyclic_types                  false
% 7.34/1.50  --sat_finite_models                     false
% 7.34/1.50  --sat_fm_lemmas                         false
% 7.34/1.50  --sat_fm_prep                           false
% 7.34/1.50  --sat_fm_uc_incr                        true
% 7.34/1.50  --sat_out_model                         small
% 7.34/1.50  --sat_out_clauses                       false
% 7.34/1.50  
% 7.34/1.50  ------ QBF Options
% 7.34/1.50  
% 7.34/1.50  --qbf_mode                              false
% 7.34/1.50  --qbf_elim_univ                         false
% 7.34/1.50  --qbf_dom_inst                          none
% 7.34/1.50  --qbf_dom_pre_inst                      false
% 7.34/1.50  --qbf_sk_in                             false
% 7.34/1.50  --qbf_pred_elim                         true
% 7.34/1.50  --qbf_split                             512
% 7.34/1.50  
% 7.34/1.50  ------ BMC1 Options
% 7.34/1.50  
% 7.34/1.50  --bmc1_incremental                      false
% 7.34/1.50  --bmc1_axioms                           reachable_all
% 7.34/1.50  --bmc1_min_bound                        0
% 7.34/1.50  --bmc1_max_bound                        -1
% 7.34/1.50  --bmc1_max_bound_default                -1
% 7.34/1.50  --bmc1_symbol_reachability              true
% 7.34/1.50  --bmc1_property_lemmas                  false
% 7.34/1.50  --bmc1_k_induction                      false
% 7.34/1.50  --bmc1_non_equiv_states                 false
% 7.34/1.50  --bmc1_deadlock                         false
% 7.34/1.50  --bmc1_ucm                              false
% 7.34/1.50  --bmc1_add_unsat_core                   none
% 7.34/1.50  --bmc1_unsat_core_children              false
% 7.34/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.34/1.50  --bmc1_out_stat                         full
% 7.34/1.50  --bmc1_ground_init                      false
% 7.34/1.50  --bmc1_pre_inst_next_state              false
% 7.34/1.50  --bmc1_pre_inst_state                   false
% 7.34/1.50  --bmc1_pre_inst_reach_state             false
% 7.34/1.50  --bmc1_out_unsat_core                   false
% 7.34/1.50  --bmc1_aig_witness_out                  false
% 7.34/1.50  --bmc1_verbose                          false
% 7.34/1.50  --bmc1_dump_clauses_tptp                false
% 7.34/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.34/1.50  --bmc1_dump_file                        -
% 7.34/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.34/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.34/1.50  --bmc1_ucm_extend_mode                  1
% 7.34/1.50  --bmc1_ucm_init_mode                    2
% 7.34/1.50  --bmc1_ucm_cone_mode                    none
% 7.34/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.34/1.50  --bmc1_ucm_relax_model                  4
% 7.34/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.34/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.34/1.50  --bmc1_ucm_layered_model                none
% 7.34/1.50  --bmc1_ucm_max_lemma_size               10
% 7.34/1.50  
% 7.34/1.50  ------ AIG Options
% 7.34/1.50  
% 7.34/1.50  --aig_mode                              false
% 7.34/1.50  
% 7.34/1.50  ------ Instantiation Options
% 7.34/1.50  
% 7.34/1.50  --instantiation_flag                    true
% 7.34/1.50  --inst_sos_flag                         false
% 7.34/1.50  --inst_sos_phase                        true
% 7.34/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.34/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.34/1.50  --inst_lit_sel_side                     num_symb
% 7.34/1.50  --inst_solver_per_active                1400
% 7.34/1.50  --inst_solver_calls_frac                1.
% 7.34/1.50  --inst_passive_queue_type               priority_queues
% 7.34/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.34/1.50  --inst_passive_queues_freq              [25;2]
% 7.34/1.50  --inst_dismatching                      true
% 7.34/1.50  --inst_eager_unprocessed_to_passive     true
% 7.34/1.50  --inst_prop_sim_given                   true
% 7.34/1.50  --inst_prop_sim_new                     false
% 7.34/1.50  --inst_subs_new                         false
% 7.34/1.50  --inst_eq_res_simp                      false
% 7.34/1.50  --inst_subs_given                       false
% 7.34/1.50  --inst_orphan_elimination               true
% 7.34/1.50  --inst_learning_loop_flag               true
% 7.34/1.50  --inst_learning_start                   3000
% 7.34/1.50  --inst_learning_factor                  2
% 7.34/1.50  --inst_start_prop_sim_after_learn       3
% 7.34/1.50  --inst_sel_renew                        solver
% 7.34/1.50  --inst_lit_activity_flag                true
% 7.34/1.50  --inst_restr_to_given                   false
% 7.34/1.50  --inst_activity_threshold               500
% 7.34/1.50  --inst_out_proof                        true
% 7.34/1.50  
% 7.34/1.50  ------ Resolution Options
% 7.34/1.50  
% 7.34/1.50  --resolution_flag                       true
% 7.34/1.50  --res_lit_sel                           adaptive
% 7.34/1.50  --res_lit_sel_side                      none
% 7.34/1.50  --res_ordering                          kbo
% 7.34/1.50  --res_to_prop_solver                    active
% 7.34/1.50  --res_prop_simpl_new                    false
% 7.34/1.50  --res_prop_simpl_given                  true
% 7.34/1.50  --res_passive_queue_type                priority_queues
% 7.34/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.34/1.50  --res_passive_queues_freq               [15;5]
% 7.34/1.50  --res_forward_subs                      full
% 7.34/1.50  --res_backward_subs                     full
% 7.34/1.50  --res_forward_subs_resolution           true
% 7.34/1.50  --res_backward_subs_resolution          true
% 7.34/1.50  --res_orphan_elimination                true
% 7.34/1.50  --res_time_limit                        2.
% 7.34/1.50  --res_out_proof                         true
% 7.34/1.50  
% 7.34/1.50  ------ Superposition Options
% 7.34/1.50  
% 7.34/1.50  --superposition_flag                    true
% 7.34/1.50  --sup_passive_queue_type                priority_queues
% 7.34/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.34/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.34/1.50  --demod_completeness_check              fast
% 7.34/1.50  --demod_use_ground                      true
% 7.34/1.50  --sup_to_prop_solver                    passive
% 7.34/1.50  --sup_prop_simpl_new                    true
% 7.34/1.50  --sup_prop_simpl_given                  true
% 7.34/1.50  --sup_fun_splitting                     false
% 7.34/1.50  --sup_smt_interval                      50000
% 7.34/1.50  
% 7.34/1.50  ------ Superposition Simplification Setup
% 7.34/1.50  
% 7.34/1.50  --sup_indices_passive                   []
% 7.34/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.34/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.50  --sup_full_bw                           [BwDemod]
% 7.34/1.50  --sup_immed_triv                        [TrivRules]
% 7.34/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.34/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.50  --sup_immed_bw_main                     []
% 7.34/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.34/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.34/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.34/1.50  
% 7.34/1.50  ------ Combination Options
% 7.34/1.50  
% 7.34/1.50  --comb_res_mult                         3
% 7.34/1.50  --comb_sup_mult                         2
% 7.34/1.50  --comb_inst_mult                        10
% 7.34/1.50  
% 7.34/1.50  ------ Debug Options
% 7.34/1.50  
% 7.34/1.50  --dbg_backtrace                         false
% 7.34/1.50  --dbg_dump_prop_clauses                 false
% 7.34/1.50  --dbg_dump_prop_clauses_file            -
% 7.34/1.50  --dbg_out_stat                          false
% 7.34/1.50  ------ Parsing...
% 7.34/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.34/1.50  
% 7.34/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.34/1.50  
% 7.34/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.34/1.50  
% 7.34/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.34/1.50  ------ Proving...
% 7.34/1.50  ------ Problem Properties 
% 7.34/1.50  
% 7.34/1.50  
% 7.34/1.50  clauses                                 15
% 7.34/1.50  conjectures                             2
% 7.34/1.50  EPR                                     0
% 7.34/1.50  Horn                                    9
% 7.34/1.50  unary                                   4
% 7.34/1.50  binary                                  5
% 7.34/1.50  lits                                    33
% 7.34/1.50  lits eq                                 13
% 7.34/1.50  fd_pure                                 0
% 7.34/1.50  fd_pseudo                               0
% 7.34/1.50  fd_cond                                 0
% 7.34/1.50  fd_pseudo_cond                          5
% 7.34/1.50  AC symbols                              0
% 7.34/1.50  
% 7.34/1.50  ------ Schedule dynamic 5 is on 
% 7.34/1.50  
% 7.34/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.34/1.50  
% 7.34/1.50  
% 7.34/1.50  ------ 
% 7.34/1.50  Current options:
% 7.34/1.50  ------ 
% 7.34/1.50  
% 7.34/1.50  ------ Input Options
% 7.34/1.50  
% 7.34/1.50  --out_options                           all
% 7.34/1.50  --tptp_safe_out                         true
% 7.34/1.50  --problem_path                          ""
% 7.34/1.50  --include_path                          ""
% 7.34/1.50  --clausifier                            res/vclausify_rel
% 7.34/1.50  --clausifier_options                    --mode clausify
% 7.34/1.50  --stdin                                 false
% 7.34/1.50  --stats_out                             all
% 7.34/1.50  
% 7.34/1.50  ------ General Options
% 7.34/1.50  
% 7.34/1.50  --fof                                   false
% 7.34/1.50  --time_out_real                         305.
% 7.34/1.50  --time_out_virtual                      -1.
% 7.34/1.50  --symbol_type_check                     false
% 7.34/1.50  --clausify_out                          false
% 7.34/1.50  --sig_cnt_out                           false
% 7.34/1.50  --trig_cnt_out                          false
% 7.34/1.50  --trig_cnt_out_tolerance                1.
% 7.34/1.50  --trig_cnt_out_sk_spl                   false
% 7.34/1.50  --abstr_cl_out                          false
% 7.34/1.50  
% 7.34/1.50  ------ Global Options
% 7.34/1.50  
% 7.34/1.50  --schedule                              default
% 7.34/1.50  --add_important_lit                     false
% 7.34/1.50  --prop_solver_per_cl                    1000
% 7.34/1.50  --min_unsat_core                        false
% 7.34/1.50  --soft_assumptions                      false
% 7.34/1.50  --soft_lemma_size                       3
% 7.34/1.50  --prop_impl_unit_size                   0
% 7.34/1.50  --prop_impl_unit                        []
% 7.34/1.50  --share_sel_clauses                     true
% 7.34/1.50  --reset_solvers                         false
% 7.34/1.50  --bc_imp_inh                            [conj_cone]
% 7.34/1.50  --conj_cone_tolerance                   3.
% 7.34/1.50  --extra_neg_conj                        none
% 7.34/1.50  --large_theory_mode                     true
% 7.34/1.50  --prolific_symb_bound                   200
% 7.34/1.50  --lt_threshold                          2000
% 7.34/1.50  --clause_weak_htbl                      true
% 7.34/1.50  --gc_record_bc_elim                     false
% 7.34/1.50  
% 7.34/1.50  ------ Preprocessing Options
% 7.34/1.50  
% 7.34/1.50  --preprocessing_flag                    true
% 7.34/1.50  --time_out_prep_mult                    0.1
% 7.34/1.50  --splitting_mode                        input
% 7.34/1.50  --splitting_grd                         true
% 7.34/1.50  --splitting_cvd                         false
% 7.34/1.50  --splitting_cvd_svl                     false
% 7.34/1.50  --splitting_nvd                         32
% 7.34/1.50  --sub_typing                            true
% 7.34/1.50  --prep_gs_sim                           true
% 7.34/1.50  --prep_unflatten                        true
% 7.34/1.50  --prep_res_sim                          true
% 7.34/1.50  --prep_upred                            true
% 7.34/1.50  --prep_sem_filter                       exhaustive
% 7.34/1.50  --prep_sem_filter_out                   false
% 7.34/1.50  --pred_elim                             true
% 7.34/1.50  --res_sim_input                         true
% 7.34/1.50  --eq_ax_congr_red                       true
% 7.34/1.50  --pure_diseq_elim                       true
% 7.34/1.50  --brand_transform                       false
% 7.34/1.50  --non_eq_to_eq                          false
% 7.34/1.50  --prep_def_merge                        true
% 7.34/1.50  --prep_def_merge_prop_impl              false
% 7.34/1.50  --prep_def_merge_mbd                    true
% 7.34/1.50  --prep_def_merge_tr_red                 false
% 7.34/1.50  --prep_def_merge_tr_cl                  false
% 7.34/1.50  --smt_preprocessing                     true
% 7.34/1.50  --smt_ac_axioms                         fast
% 7.34/1.50  --preprocessed_out                      false
% 7.34/1.50  --preprocessed_stats                    false
% 7.34/1.50  
% 7.34/1.50  ------ Abstraction refinement Options
% 7.34/1.50  
% 7.34/1.50  --abstr_ref                             []
% 7.34/1.50  --abstr_ref_prep                        false
% 7.34/1.50  --abstr_ref_until_sat                   false
% 7.34/1.50  --abstr_ref_sig_restrict                funpre
% 7.34/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.34/1.50  --abstr_ref_under                       []
% 7.34/1.50  
% 7.34/1.50  ------ SAT Options
% 7.34/1.50  
% 7.34/1.50  --sat_mode                              false
% 7.34/1.50  --sat_fm_restart_options                ""
% 7.34/1.50  --sat_gr_def                            false
% 7.34/1.50  --sat_epr_types                         true
% 7.34/1.50  --sat_non_cyclic_types                  false
% 7.34/1.50  --sat_finite_models                     false
% 7.34/1.50  --sat_fm_lemmas                         false
% 7.34/1.50  --sat_fm_prep                           false
% 7.34/1.50  --sat_fm_uc_incr                        true
% 7.34/1.50  --sat_out_model                         small
% 7.34/1.50  --sat_out_clauses                       false
% 7.34/1.50  
% 7.34/1.50  ------ QBF Options
% 7.34/1.50  
% 7.34/1.50  --qbf_mode                              false
% 7.34/1.50  --qbf_elim_univ                         false
% 7.34/1.50  --qbf_dom_inst                          none
% 7.34/1.50  --qbf_dom_pre_inst                      false
% 7.34/1.50  --qbf_sk_in                             false
% 7.34/1.50  --qbf_pred_elim                         true
% 7.34/1.50  --qbf_split                             512
% 7.34/1.50  
% 7.34/1.50  ------ BMC1 Options
% 7.34/1.50  
% 7.34/1.50  --bmc1_incremental                      false
% 7.34/1.50  --bmc1_axioms                           reachable_all
% 7.34/1.50  --bmc1_min_bound                        0
% 7.34/1.50  --bmc1_max_bound                        -1
% 7.34/1.50  --bmc1_max_bound_default                -1
% 7.34/1.50  --bmc1_symbol_reachability              true
% 7.34/1.50  --bmc1_property_lemmas                  false
% 7.34/1.50  --bmc1_k_induction                      false
% 7.34/1.50  --bmc1_non_equiv_states                 false
% 7.34/1.50  --bmc1_deadlock                         false
% 7.34/1.50  --bmc1_ucm                              false
% 7.34/1.50  --bmc1_add_unsat_core                   none
% 7.34/1.50  --bmc1_unsat_core_children              false
% 7.34/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.34/1.50  --bmc1_out_stat                         full
% 7.34/1.50  --bmc1_ground_init                      false
% 7.34/1.50  --bmc1_pre_inst_next_state              false
% 7.34/1.50  --bmc1_pre_inst_state                   false
% 7.34/1.50  --bmc1_pre_inst_reach_state             false
% 7.34/1.50  --bmc1_out_unsat_core                   false
% 7.34/1.50  --bmc1_aig_witness_out                  false
% 7.34/1.50  --bmc1_verbose                          false
% 7.34/1.50  --bmc1_dump_clauses_tptp                false
% 7.34/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.34/1.50  --bmc1_dump_file                        -
% 7.34/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.34/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.34/1.50  --bmc1_ucm_extend_mode                  1
% 7.34/1.50  --bmc1_ucm_init_mode                    2
% 7.34/1.50  --bmc1_ucm_cone_mode                    none
% 7.34/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.34/1.50  --bmc1_ucm_relax_model                  4
% 7.34/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.34/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.34/1.50  --bmc1_ucm_layered_model                none
% 7.34/1.50  --bmc1_ucm_max_lemma_size               10
% 7.34/1.50  
% 7.34/1.50  ------ AIG Options
% 7.34/1.50  
% 7.34/1.50  --aig_mode                              false
% 7.34/1.50  
% 7.34/1.50  ------ Instantiation Options
% 7.34/1.50  
% 7.34/1.50  --instantiation_flag                    true
% 7.34/1.50  --inst_sos_flag                         false
% 7.34/1.50  --inst_sos_phase                        true
% 7.34/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.34/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.34/1.50  --inst_lit_sel_side                     none
% 7.34/1.50  --inst_solver_per_active                1400
% 7.34/1.50  --inst_solver_calls_frac                1.
% 7.34/1.50  --inst_passive_queue_type               priority_queues
% 7.34/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.34/1.50  --inst_passive_queues_freq              [25;2]
% 7.34/1.50  --inst_dismatching                      true
% 7.34/1.50  --inst_eager_unprocessed_to_passive     true
% 7.34/1.50  --inst_prop_sim_given                   true
% 7.34/1.50  --inst_prop_sim_new                     false
% 7.34/1.50  --inst_subs_new                         false
% 7.34/1.50  --inst_eq_res_simp                      false
% 7.34/1.50  --inst_subs_given                       false
% 7.34/1.50  --inst_orphan_elimination               true
% 7.34/1.50  --inst_learning_loop_flag               true
% 7.34/1.50  --inst_learning_start                   3000
% 7.34/1.50  --inst_learning_factor                  2
% 7.34/1.50  --inst_start_prop_sim_after_learn       3
% 7.34/1.50  --inst_sel_renew                        solver
% 7.34/1.50  --inst_lit_activity_flag                true
% 7.34/1.50  --inst_restr_to_given                   false
% 7.34/1.50  --inst_activity_threshold               500
% 7.34/1.50  --inst_out_proof                        true
% 7.34/1.50  
% 7.34/1.50  ------ Resolution Options
% 7.34/1.50  
% 7.34/1.50  --resolution_flag                       false
% 7.34/1.50  --res_lit_sel                           adaptive
% 7.34/1.50  --res_lit_sel_side                      none
% 7.34/1.50  --res_ordering                          kbo
% 7.34/1.50  --res_to_prop_solver                    active
% 7.34/1.50  --res_prop_simpl_new                    false
% 7.34/1.50  --res_prop_simpl_given                  true
% 7.34/1.50  --res_passive_queue_type                priority_queues
% 7.34/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.34/1.50  --res_passive_queues_freq               [15;5]
% 7.34/1.50  --res_forward_subs                      full
% 7.34/1.50  --res_backward_subs                     full
% 7.34/1.50  --res_forward_subs_resolution           true
% 7.34/1.50  --res_backward_subs_resolution          true
% 7.34/1.50  --res_orphan_elimination                true
% 7.34/1.50  --res_time_limit                        2.
% 7.34/1.50  --res_out_proof                         true
% 7.34/1.50  
% 7.34/1.50  ------ Superposition Options
% 7.34/1.50  
% 7.34/1.50  --superposition_flag                    true
% 7.34/1.50  --sup_passive_queue_type                priority_queues
% 7.34/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.34/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.34/1.50  --demod_completeness_check              fast
% 7.34/1.50  --demod_use_ground                      true
% 7.34/1.50  --sup_to_prop_solver                    passive
% 7.34/1.50  --sup_prop_simpl_new                    true
% 7.34/1.50  --sup_prop_simpl_given                  true
% 7.34/1.50  --sup_fun_splitting                     false
% 7.34/1.50  --sup_smt_interval                      50000
% 7.34/1.50  
% 7.34/1.50  ------ Superposition Simplification Setup
% 7.34/1.50  
% 7.34/1.50  --sup_indices_passive                   []
% 7.34/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.34/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.50  --sup_full_bw                           [BwDemod]
% 7.34/1.50  --sup_immed_triv                        [TrivRules]
% 7.34/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.34/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.50  --sup_immed_bw_main                     []
% 7.34/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.34/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.34/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.34/1.50  
% 7.34/1.50  ------ Combination Options
% 7.34/1.50  
% 7.34/1.50  --comb_res_mult                         3
% 7.34/1.50  --comb_sup_mult                         2
% 7.34/1.50  --comb_inst_mult                        10
% 7.34/1.50  
% 7.34/1.50  ------ Debug Options
% 7.34/1.50  
% 7.34/1.50  --dbg_backtrace                         false
% 7.34/1.50  --dbg_dump_prop_clauses                 false
% 7.34/1.50  --dbg_dump_prop_clauses_file            -
% 7.34/1.50  --dbg_out_stat                          false
% 7.34/1.50  
% 7.34/1.50  
% 7.34/1.50  
% 7.34/1.50  
% 7.34/1.50  ------ Proving...
% 7.34/1.50  
% 7.34/1.50  
% 7.34/1.50  % SZS status Theorem for theBenchmark.p
% 7.34/1.50  
% 7.34/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.34/1.50  
% 7.34/1.50  fof(f2,axiom,(
% 7.34/1.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.34/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f17,plain,(
% 7.34/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.34/1.50    inference(nnf_transformation,[],[f2])).
% 7.34/1.50  
% 7.34/1.50  fof(f18,plain,(
% 7.34/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.34/1.50    inference(flattening,[],[f17])).
% 7.34/1.50  
% 7.34/1.50  fof(f19,plain,(
% 7.34/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.34/1.50    inference(rectify,[],[f18])).
% 7.34/1.50  
% 7.34/1.50  fof(f20,plain,(
% 7.34/1.50    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.34/1.50    introduced(choice_axiom,[])).
% 7.34/1.50  
% 7.34/1.50  fof(f21,plain,(
% 7.34/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.34/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 7.34/1.50  
% 7.34/1.50  fof(f33,plain,(
% 7.34/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.34/1.50    inference(cnf_transformation,[],[f21])).
% 7.34/1.50  
% 7.34/1.50  fof(f3,axiom,(
% 7.34/1.50    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.34/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f36,plain,(
% 7.34/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.34/1.50    inference(cnf_transformation,[],[f3])).
% 7.34/1.50  
% 7.34/1.50  fof(f60,plain,(
% 7.34/1.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.34/1.50    inference(definition_unfolding,[],[f33,f36])).
% 7.34/1.50  
% 7.34/1.50  fof(f6,axiom,(
% 7.34/1.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.34/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f22,plain,(
% 7.34/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.34/1.50    inference(nnf_transformation,[],[f6])).
% 7.34/1.50  
% 7.34/1.50  fof(f23,plain,(
% 7.34/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.34/1.50    inference(rectify,[],[f22])).
% 7.34/1.50  
% 7.34/1.50  fof(f24,plain,(
% 7.34/1.50    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 7.34/1.50    introduced(choice_axiom,[])).
% 7.34/1.50  
% 7.34/1.50  fof(f25,plain,(
% 7.34/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.34/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).
% 7.34/1.50  
% 7.34/1.50  fof(f40,plain,(
% 7.34/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.34/1.50    inference(cnf_transformation,[],[f25])).
% 7.34/1.50  
% 7.34/1.50  fof(f7,axiom,(
% 7.34/1.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.34/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f43,plain,(
% 7.34/1.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.34/1.50    inference(cnf_transformation,[],[f7])).
% 7.34/1.50  
% 7.34/1.50  fof(f8,axiom,(
% 7.34/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.34/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f44,plain,(
% 7.34/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.34/1.50    inference(cnf_transformation,[],[f8])).
% 7.34/1.50  
% 7.34/1.50  fof(f9,axiom,(
% 7.34/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.34/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f45,plain,(
% 7.34/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.34/1.50    inference(cnf_transformation,[],[f9])).
% 7.34/1.50  
% 7.34/1.50  fof(f10,axiom,(
% 7.34/1.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.34/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f46,plain,(
% 7.34/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.34/1.50    inference(cnf_transformation,[],[f10])).
% 7.34/1.50  
% 7.34/1.50  fof(f11,axiom,(
% 7.34/1.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.34/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f47,plain,(
% 7.34/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.34/1.50    inference(cnf_transformation,[],[f11])).
% 7.34/1.50  
% 7.34/1.50  fof(f12,axiom,(
% 7.34/1.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.34/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f48,plain,(
% 7.34/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.34/1.50    inference(cnf_transformation,[],[f12])).
% 7.34/1.50  
% 7.34/1.50  fof(f13,axiom,(
% 7.34/1.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.34/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f49,plain,(
% 7.34/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.34/1.50    inference(cnf_transformation,[],[f13])).
% 7.34/1.50  
% 7.34/1.50  fof(f52,plain,(
% 7.34/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.34/1.50    inference(definition_unfolding,[],[f48,f49])).
% 7.34/1.50  
% 7.34/1.50  fof(f53,plain,(
% 7.34/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.34/1.50    inference(definition_unfolding,[],[f47,f52])).
% 7.34/1.50  
% 7.34/1.50  fof(f54,plain,(
% 7.34/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.34/1.50    inference(definition_unfolding,[],[f46,f53])).
% 7.34/1.50  
% 7.34/1.50  fof(f55,plain,(
% 7.34/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.34/1.50    inference(definition_unfolding,[],[f45,f54])).
% 7.34/1.50  
% 7.34/1.50  fof(f56,plain,(
% 7.34/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.34/1.50    inference(definition_unfolding,[],[f44,f55])).
% 7.34/1.50  
% 7.34/1.50  fof(f57,plain,(
% 7.34/1.50    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.34/1.50    inference(definition_unfolding,[],[f43,f56])).
% 7.34/1.50  
% 7.34/1.50  fof(f66,plain,(
% 7.34/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 7.34/1.50    inference(definition_unfolding,[],[f40,f57])).
% 7.34/1.50  
% 7.34/1.50  fof(f73,plain,(
% 7.34/1.50    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 7.34/1.50    inference(equality_resolution,[],[f66])).
% 7.34/1.50  
% 7.34/1.50  fof(f74,plain,(
% 7.34/1.50    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 7.34/1.50    inference(equality_resolution,[],[f73])).
% 7.34/1.50  
% 7.34/1.50  fof(f4,axiom,(
% 7.34/1.50    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.34/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f37,plain,(
% 7.34/1.50    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.34/1.50    inference(cnf_transformation,[],[f4])).
% 7.34/1.50  
% 7.34/1.50  fof(f31,plain,(
% 7.34/1.50    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.34/1.50    inference(cnf_transformation,[],[f21])).
% 7.34/1.50  
% 7.34/1.50  fof(f62,plain,(
% 7.34/1.50    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 7.34/1.50    inference(definition_unfolding,[],[f31,f36])).
% 7.34/1.50  
% 7.34/1.50  fof(f71,plain,(
% 7.34/1.50    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 7.34/1.50    inference(equality_resolution,[],[f62])).
% 7.34/1.50  
% 7.34/1.50  fof(f5,axiom,(
% 7.34/1.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.34/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.50  
% 7.34/1.50  fof(f38,plain,(
% 7.34/1.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.34/1.50    inference(cnf_transformation,[],[f5])).
% 7.34/1.50  
% 7.34/1.50  fof(f39,plain,(
% 7.34/1.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.34/1.50    inference(cnf_transformation,[],[f25])).
% 7.34/1.50  
% 7.34/1.50  fof(f67,plain,(
% 7.34/1.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 7.34/1.50    inference(definition_unfolding,[],[f39,f57])).
% 7.34/1.50  
% 7.34/1.50  fof(f75,plain,(
% 7.34/1.50    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 7.34/1.50    inference(equality_resolution,[],[f67])).
% 7.34/1.50  
% 7.34/1.50  fof(f14,conjecture,(
% 7.34/1.50    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 7.34/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.34/1.51  
% 7.34/1.51  fof(f15,negated_conjecture,(
% 7.34/1.51    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 7.34/1.51    inference(negated_conjecture,[],[f14])).
% 7.34/1.51  
% 7.34/1.51  fof(f16,plain,(
% 7.34/1.51    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <~> r2_hidden(X0,X1))),
% 7.34/1.51    inference(ennf_transformation,[],[f15])).
% 7.34/1.51  
% 7.34/1.51  fof(f26,plain,(
% 7.34/1.51    ? [X0,X1] : ((~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0))),
% 7.34/1.51    inference(nnf_transformation,[],[f16])).
% 7.34/1.51  
% 7.34/1.51  fof(f27,plain,(
% 7.34/1.51    ? [X0,X1] : ((~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0)) => ((~r2_hidden(sK2,sK3) | k4_xboole_0(k1_tarski(sK2),sK3) != k1_xboole_0) & (r2_hidden(sK2,sK3) | k4_xboole_0(k1_tarski(sK2),sK3) = k1_xboole_0))),
% 7.34/1.51    introduced(choice_axiom,[])).
% 7.34/1.51  
% 7.34/1.51  fof(f28,plain,(
% 7.34/1.51    (~r2_hidden(sK2,sK3) | k4_xboole_0(k1_tarski(sK2),sK3) != k1_xboole_0) & (r2_hidden(sK2,sK3) | k4_xboole_0(k1_tarski(sK2),sK3) = k1_xboole_0)),
% 7.34/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f27])).
% 7.34/1.51  
% 7.34/1.51  fof(f51,plain,(
% 7.34/1.51    ~r2_hidden(sK2,sK3) | k4_xboole_0(k1_tarski(sK2),sK3) != k1_xboole_0),
% 7.34/1.51    inference(cnf_transformation,[],[f28])).
% 7.34/1.51  
% 7.34/1.51  fof(f68,plain,(
% 7.34/1.51    ~r2_hidden(sK2,sK3) | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_xboole_0),
% 7.34/1.51    inference(definition_unfolding,[],[f51,f36,f57])).
% 7.34/1.51  
% 7.34/1.51  fof(f50,plain,(
% 7.34/1.51    r2_hidden(sK2,sK3) | k4_xboole_0(k1_tarski(sK2),sK3) = k1_xboole_0),
% 7.34/1.51    inference(cnf_transformation,[],[f28])).
% 7.34/1.51  
% 7.34/1.51  fof(f69,plain,(
% 7.34/1.51    r2_hidden(sK2,sK3) | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0),
% 7.34/1.51    inference(definition_unfolding,[],[f50,f36,f57])).
% 7.34/1.51  
% 7.34/1.51  fof(f35,plain,(
% 7.34/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.34/1.51    inference(cnf_transformation,[],[f21])).
% 7.34/1.51  
% 7.34/1.51  fof(f58,plain,(
% 7.34/1.51    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.34/1.51    inference(definition_unfolding,[],[f35,f36])).
% 7.34/1.51  
% 7.34/1.51  fof(f30,plain,(
% 7.34/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.34/1.51    inference(cnf_transformation,[],[f21])).
% 7.34/1.51  
% 7.34/1.51  fof(f63,plain,(
% 7.34/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 7.34/1.51    inference(definition_unfolding,[],[f30,f36])).
% 7.34/1.51  
% 7.34/1.51  fof(f72,plain,(
% 7.34/1.51    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 7.34/1.51    inference(equality_resolution,[],[f63])).
% 7.34/1.51  
% 7.34/1.51  fof(f32,plain,(
% 7.34/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 7.34/1.51    inference(cnf_transformation,[],[f21])).
% 7.34/1.51  
% 7.34/1.51  fof(f61,plain,(
% 7.34/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 7.34/1.51    inference(definition_unfolding,[],[f32,f36])).
% 7.34/1.51  
% 7.34/1.51  fof(f70,plain,(
% 7.34/1.51    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 7.34/1.51    inference(equality_resolution,[],[f61])).
% 7.34/1.51  
% 7.34/1.51  fof(f34,plain,(
% 7.34/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.34/1.51    inference(cnf_transformation,[],[f21])).
% 7.34/1.51  
% 7.34/1.51  fof(f59,plain,(
% 7.34/1.51    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.34/1.51    inference(definition_unfolding,[],[f34,f36])).
% 7.34/1.51  
% 7.34/1.51  cnf(c_3,plain,
% 7.34/1.51      ( r2_hidden(sK0(X0,X1,X2),X0)
% 7.34/1.51      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.34/1.51      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 7.34/1.51      inference(cnf_transformation,[],[f60]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_489,plain,
% 7.34/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 7.34/1.51      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 7.34/1.51      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_11,plain,
% 7.34/1.51      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 7.34/1.51      inference(cnf_transformation,[],[f74]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_483,plain,
% 7.34/1.51      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_7,plain,
% 7.34/1.51      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.34/1.51      inference(cnf_transformation,[],[f37]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_5,plain,
% 7.34/1.51      ( ~ r2_hidden(X0,X1)
% 7.34/1.51      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 7.34/1.51      inference(cnf_transformation,[],[f71]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_487,plain,
% 7.34/1.51      ( r2_hidden(X0,X1) != iProver_top
% 7.34/1.51      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_908,plain,
% 7.34/1.51      ( r2_hidden(X0,k5_xboole_0(X1,k1_xboole_0)) != iProver_top
% 7.34/1.51      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_7,c_487]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_8,plain,
% 7.34/1.51      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.34/1.51      inference(cnf_transformation,[],[f38]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_911,plain,
% 7.34/1.51      ( r2_hidden(X0,X1) != iProver_top
% 7.34/1.51      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.34/1.51      inference(demodulation,[status(thm)],[c_908,c_8]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_1230,plain,
% 7.34/1.51      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_483,c_911]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_2036,plain,
% 7.34/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 7.34/1.51      | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_489,c_1230]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_12,plain,
% 7.34/1.51      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 7.34/1.51      inference(cnf_transformation,[],[f75]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_482,plain,
% 7.34/1.51      ( X0 = X1
% 7.34/1.51      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_2799,plain,
% 7.34/1.51      ( sK0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1,k1_xboole_0) = X0
% 7.34/1.51      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) = k1_xboole_0 ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_2036,c_482]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_13,negated_conjecture,
% 7.34/1.51      ( ~ r2_hidden(sK2,sK3)
% 7.34/1.51      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_xboole_0 ),
% 7.34/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_481,plain,
% 7.34/1.51      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_xboole_0
% 7.34/1.51      | r2_hidden(sK2,sK3) != iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_19251,plain,
% 7.34/1.51      ( sK0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,k1_xboole_0) = sK2
% 7.34/1.51      | r2_hidden(sK2,sK3) != iProver_top ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_2799,c_481]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_14,negated_conjecture,
% 7.34/1.51      ( r2_hidden(sK2,sK3)
% 7.34/1.51      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
% 7.34/1.51      inference(cnf_transformation,[],[f69]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_480,plain,
% 7.34/1.51      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0
% 7.34/1.51      | r2_hidden(sK2,sK3) = iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_2043,plain,
% 7.34/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 7.34/1.51      | r2_hidden(sK0(X0,X1,X0),X0) = iProver_top
% 7.34/1.51      | iProver_top != iProver_top ),
% 7.34/1.51      inference(equality_factoring,[status(thm)],[c_489]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_2045,plain,
% 7.34/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 7.34/1.51      | r2_hidden(sK0(X0,X1,X0),X0) = iProver_top ),
% 7.34/1.51      inference(equality_resolution_simp,[status(thm)],[c_2043]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_1,plain,
% 7.34/1.51      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 7.34/1.51      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 7.34/1.51      | r2_hidden(sK0(X0,X1,X2),X1)
% 7.34/1.51      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 7.34/1.51      inference(cnf_transformation,[],[f58]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_491,plain,
% 7.34/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 7.34/1.51      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 7.34/1.51      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 7.34/1.51      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_3056,plain,
% 7.34/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 7.34/1.51      | r2_hidden(sK0(X0,X1,X0),X0) != iProver_top
% 7.34/1.51      | r2_hidden(sK0(X0,X1,X0),X1) = iProver_top ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_2045,c_491]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_3077,plain,
% 7.34/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 7.34/1.51      | r2_hidden(sK0(X0,X1,X0),X1) = iProver_top ),
% 7.34/1.51      inference(forward_subsumption_resolution,
% 7.34/1.51                [status(thm)],
% 7.34/1.51                [c_3056,c_2045]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_4263,plain,
% 7.34/1.51      ( sK0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X0) = X1
% 7.34/1.51      | k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X0 ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_3077,c_482]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_10494,plain,
% 7.34/1.51      ( sK0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X0) = X1
% 7.34/1.51      | r2_hidden(X2,X0) != iProver_top
% 7.34/1.51      | r2_hidden(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_4263,c_487]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_15717,plain,
% 7.34/1.51      ( sK0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X0) = X1
% 7.34/1.51      | r2_hidden(X1,X0) != iProver_top ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_483,c_10494]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_15902,plain,
% 7.34/1.51      ( sK0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = sK2
% 7.34/1.51      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0 ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_480,c_15717]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_18,plain,
% 7.34/1.51      ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 7.34/1.51      | sK2 = sK2 ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_12]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_21,plain,
% 7.34/1.51      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_11]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_6,plain,
% 7.34/1.51      ( r2_hidden(X0,X1)
% 7.34/1.51      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.34/1.51      inference(cnf_transformation,[],[f72]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_32,plain,
% 7.34/1.51      ( ~ r2_hidden(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)))
% 7.34/1.51      | r2_hidden(sK2,sK2) ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_6]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_35,plain,
% 7.34/1.51      ( ~ r2_hidden(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)))
% 7.34/1.51      | ~ r2_hidden(sK2,sK2) ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_5]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_4,plain,
% 7.34/1.51      ( ~ r2_hidden(X0,X1)
% 7.34/1.51      | r2_hidden(X0,X2)
% 7.34/1.51      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.34/1.51      inference(cnf_transformation,[],[f70]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_590,plain,
% 7.34/1.51      ( r2_hidden(X0,X1)
% 7.34/1.51      | ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 7.34/1.51      | r2_hidden(X0,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_648,plain,
% 7.34/1.51      ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 7.34/1.51      | r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
% 7.34/1.51      | r2_hidden(sK2,sK3) ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_590]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_179,plain,
% 7.34/1.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.34/1.51      theory(equality) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_630,plain,
% 7.34/1.51      ( ~ r2_hidden(X0,X1)
% 7.34/1.51      | r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4)))
% 7.34/1.51      | X2 != X0
% 7.34/1.51      | k5_xboole_0(X3,k3_xboole_0(X3,X4)) != X1 ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_179]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_724,plain,
% 7.34/1.51      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
% 7.34/1.51      | r2_hidden(X3,k5_xboole_0(X4,k3_xboole_0(X4,X5)))
% 7.34/1.51      | X3 != X0
% 7.34/1.51      | k5_xboole_0(X4,k3_xboole_0(X4,X5)) != k5_xboole_0(X1,X2) ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_630]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_1024,plain,
% 7.34/1.51      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
% 7.34/1.51      | ~ r2_hidden(X3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
% 7.34/1.51      | X0 != X3
% 7.34/1.51      | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_724]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_1026,plain,
% 7.34/1.51      ( ~ r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))
% 7.34/1.51      | r2_hidden(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)))
% 7.34/1.51      | k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
% 7.34/1.51      | sK2 != sK2 ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_1024]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_2,plain,
% 7.34/1.51      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 7.34/1.51      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.34/1.51      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 7.34/1.51      inference(cnf_transformation,[],[f59]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_490,plain,
% 7.34/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 7.34/1.51      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 7.34/1.51      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_2257,plain,
% 7.34/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1
% 7.34/1.51      | r2_hidden(sK0(X0,X0,X1),X1) = iProver_top ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_489,c_490]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_2798,plain,
% 7.34/1.51      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) = k1_xboole_0
% 7.34/1.51      | r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2,k1_xboole_0),X1) != iProver_top ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_2036,c_487]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_3649,plain,
% 7.34/1.51      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) = k1_xboole_0 ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_2257,c_2798]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_3651,plain,
% 7.34/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 7.34/1.51      inference(light_normalisation,[status(thm)],[c_3649,c_7,c_8]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_3660,plain,
% 7.34/1.51      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = k1_xboole_0 ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_3651]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_176,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_723,plain,
% 7.34/1.51      ( X0 != X1
% 7.34/1.51      | k5_xboole_0(X2,k3_xboole_0(X2,X3)) != X1
% 7.34/1.51      | k5_xboole_0(X2,k3_xboole_0(X2,X3)) = X0 ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_176]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_4382,plain,
% 7.34/1.51      ( X0 != k1_xboole_0
% 7.34/1.51      | k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X0
% 7.34/1.51      | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_723]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_13358,plain,
% 7.34/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
% 7.34/1.51      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 7.34/1.51      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_xboole_0 ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_4382]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_13359,plain,
% 7.34/1.51      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_xboole_0
% 7.34/1.51      | k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
% 7.34/1.51      | k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) != k1_xboole_0 ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_13358]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_16399,plain,
% 7.34/1.51      ( sK0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) = sK2 ),
% 7.34/1.51      inference(global_propositional_subsumption,
% 7.34/1.51                [status(thm)],
% 7.34/1.51                [c_15902,c_13,c_18,c_21,c_32,c_35,c_648,c_1026,c_3660,
% 7.34/1.51                 c_13359]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_16412,plain,
% 7.34/1.51      ( k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = sK3
% 7.34/1.51      | r2_hidden(sK2,sK3) = iProver_top ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_16399,c_2045]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_15,plain,
% 7.34/1.51      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0
% 7.34/1.51      | r2_hidden(sK2,sK3) = iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_20,plain,
% 7.34/1.51      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_22,plain,
% 7.34/1.51      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_20]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_31,plain,
% 7.34/1.51      ( r2_hidden(X0,X1) = iProver_top
% 7.34/1.51      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_33,plain,
% 7.34/1.51      ( r2_hidden(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))) != iProver_top
% 7.34/1.51      | r2_hidden(sK2,sK2) = iProver_top ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_31]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_624,plain,
% 7.34/1.51      ( ~ r2_hidden(sK2,X0)
% 7.34/1.51      | r2_hidden(sK2,k5_xboole_0(X0,k3_xboole_0(X0,sK3)))
% 7.34/1.51      | r2_hidden(sK2,sK3) ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_625,plain,
% 7.34/1.51      ( r2_hidden(sK2,X0) != iProver_top
% 7.34/1.51      | r2_hidden(sK2,k5_xboole_0(X0,k3_xboole_0(X0,sK3))) = iProver_top
% 7.34/1.51      | r2_hidden(sK2,sK3) = iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_624]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_627,plain,
% 7.34/1.51      ( r2_hidden(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) = iProver_top
% 7.34/1.51      | r2_hidden(sK2,sK3) = iProver_top
% 7.34/1.51      | r2_hidden(sK2,sK2) != iProver_top ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_625]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_649,plain,
% 7.34/1.51      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 7.34/1.51      | r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) = iProver_top
% 7.34/1.51      | r2_hidden(sK2,sK3) = iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_648]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_1025,plain,
% 7.34/1.51      ( X0 != X1
% 7.34/1.51      | k5_xboole_0(X2,k3_xboole_0(X2,X3)) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
% 7.34/1.51      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = iProver_top
% 7.34/1.51      | r2_hidden(X1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) != iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_1024]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_1027,plain,
% 7.34/1.51      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) != k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
% 7.34/1.51      | sK2 != sK2
% 7.34/1.51      | r2_hidden(sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) != iProver_top
% 7.34/1.51      | r2_hidden(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))) = iProver_top ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_1025]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_4262,plain,
% 7.34/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = X0
% 7.34/1.51      | r2_hidden(sK0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)),X0),X2) != iProver_top ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_3077,c_487]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_4404,plain,
% 7.34/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_2045,c_4262]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_3059,plain,
% 7.34/1.51      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
% 7.34/1.51      | r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))),X1) != iProver_top ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_2045,c_487]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_4448,plain,
% 7.34/1.51      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))),X2)) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))
% 7.34/1.51      | r2_hidden(sK0(X0,X2,X0),k5_xboole_0(X1,k3_xboole_0(X1,X0))) != iProver_top ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_4404,c_3059]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_4480,plain,
% 7.34/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 7.34/1.51      | r2_hidden(sK0(X0,X1,X0),k5_xboole_0(X2,k3_xboole_0(X2,X0))) != iProver_top ),
% 7.34/1.51      inference(light_normalisation,[status(thm)],[c_4448,c_4404]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_16409,plain,
% 7.34/1.51      ( k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = sK3
% 7.34/1.51      | r2_hidden(sK2,k5_xboole_0(X0,k3_xboole_0(X0,sK3))) != iProver_top ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_16399,c_4480]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_669,plain,
% 7.34/1.51      ( ~ r2_hidden(sK2,k5_xboole_0(X0,k3_xboole_0(X0,sK3)))
% 7.34/1.51      | ~ r2_hidden(sK2,sK3) ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_5]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_670,plain,
% 7.34/1.51      ( r2_hidden(sK2,k5_xboole_0(X0,k3_xboole_0(X0,sK3))) != iProver_top
% 7.34/1.51      | r2_hidden(sK2,sK3) != iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_669]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_16691,plain,
% 7.34/1.51      ( r2_hidden(sK2,k5_xboole_0(X0,k3_xboole_0(X0,sK3))) != iProver_top ),
% 7.34/1.51      inference(global_propositional_subsumption,
% 7.34/1.51                [status(thm)],
% 7.34/1.51                [c_16409,c_15,c_13,c_18,c_21,c_32,c_35,c_648,c_670,
% 7.34/1.51                 c_1026,c_3660,c_13359]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_16694,plain,
% 7.34/1.51      ( r2_hidden(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) != iProver_top ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_16691]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_17026,plain,
% 7.34/1.51      ( r2_hidden(sK2,sK3) = iProver_top ),
% 7.34/1.51      inference(global_propositional_subsumption,
% 7.34/1.51                [status(thm)],
% 7.34/1.51                [c_16412,c_15,c_13,c_18,c_21,c_32,c_35,c_648,c_1026,
% 7.34/1.51                 c_3660,c_13359]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_20232,plain,
% 7.34/1.51      ( sK0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,k1_xboole_0) = sK2 ),
% 7.34/1.51      inference(global_propositional_subsumption,
% 7.34/1.51                [status(thm)],
% 7.34/1.51                [c_19251,c_15,c_13,c_18,c_21,c_32,c_35,c_648,c_1026,
% 7.34/1.51                 c_3660,c_13359]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_20239,plain,
% 7.34/1.51      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0
% 7.34/1.51      | r2_hidden(sK0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,k1_xboole_0),k1_xboole_0) = iProver_top
% 7.34/1.51      | r2_hidden(sK2,sK3) != iProver_top ),
% 7.34/1.51      inference(superposition,[status(thm)],[c_20232,c_490]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_20261,plain,
% 7.34/1.51      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_xboole_0
% 7.34/1.51      | r2_hidden(sK2,sK3) != iProver_top
% 7.34/1.51      | r2_hidden(sK2,k1_xboole_0) = iProver_top ),
% 7.34/1.51      inference(light_normalisation,[status(thm)],[c_20239,c_20232]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_1241,plain,
% 7.34/1.51      ( r2_hidden(sK2,k1_xboole_0) != iProver_top ),
% 7.34/1.51      inference(instantiation,[status(thm)],[c_1230]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(c_16,plain,
% 7.34/1.51      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_xboole_0
% 7.34/1.51      | r2_hidden(sK2,sK3) != iProver_top ),
% 7.34/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.34/1.51  
% 7.34/1.51  cnf(contradiction,plain,
% 7.34/1.51      ( $false ),
% 7.34/1.51      inference(minisat,[status(thm)],[c_20261,c_17026,c_1241,c_16]) ).
% 7.34/1.51  
% 7.34/1.51  
% 7.34/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.34/1.51  
% 7.34/1.51  ------                               Statistics
% 7.34/1.51  
% 7.34/1.51  ------ General
% 7.34/1.51  
% 7.34/1.51  abstr_ref_over_cycles:                  0
% 7.34/1.51  abstr_ref_under_cycles:                 0
% 7.34/1.51  gc_basic_clause_elim:                   0
% 7.34/1.51  forced_gc_time:                         0
% 7.34/1.51  parsing_time:                           0.009
% 7.34/1.51  unif_index_cands_time:                  0.
% 7.34/1.51  unif_index_add_time:                    0.
% 7.34/1.51  orderings_time:                         0.
% 7.34/1.51  out_proof_time:                         0.012
% 7.34/1.51  total_time:                             0.817
% 7.34/1.51  num_of_symbols:                         40
% 7.34/1.51  num_of_terms:                           25755
% 7.34/1.51  
% 7.34/1.51  ------ Preprocessing
% 7.34/1.51  
% 7.34/1.51  num_of_splits:                          0
% 7.34/1.51  num_of_split_atoms:                     0
% 7.34/1.51  num_of_reused_defs:                     0
% 7.34/1.51  num_eq_ax_congr_red:                    10
% 7.34/1.51  num_of_sem_filtered_clauses:            1
% 7.34/1.51  num_of_subtypes:                        0
% 7.34/1.51  monotx_restored_types:                  0
% 7.34/1.51  sat_num_of_epr_types:                   0
% 7.34/1.51  sat_num_of_non_cyclic_types:            0
% 7.34/1.51  sat_guarded_non_collapsed_types:        0
% 7.34/1.51  num_pure_diseq_elim:                    0
% 7.34/1.51  simp_replaced_by:                       0
% 7.34/1.51  res_preprocessed:                       58
% 7.34/1.51  prep_upred:                             0
% 7.34/1.51  prep_unflattend:                        0
% 7.34/1.51  smt_new_axioms:                         0
% 7.34/1.51  pred_elim_cands:                        1
% 7.34/1.51  pred_elim:                              0
% 7.34/1.51  pred_elim_cl:                           0
% 7.34/1.51  pred_elim_cycles:                       1
% 7.34/1.51  merged_defs:                            6
% 7.34/1.51  merged_defs_ncl:                        0
% 7.34/1.51  bin_hyper_res:                          6
% 7.34/1.51  prep_cycles:                            3
% 7.34/1.51  pred_elim_time:                         0.
% 7.34/1.51  splitting_time:                         0.
% 7.34/1.51  sem_filter_time:                        0.
% 7.34/1.51  monotx_time:                            0.
% 7.34/1.51  subtype_inf_time:                       0.
% 7.34/1.51  
% 7.34/1.51  ------ Problem properties
% 7.34/1.51  
% 7.34/1.51  clauses:                                15
% 7.34/1.51  conjectures:                            2
% 7.34/1.51  epr:                                    0
% 7.34/1.51  horn:                                   9
% 7.34/1.51  ground:                                 2
% 7.34/1.51  unary:                                  4
% 7.34/1.51  binary:                                 5
% 7.34/1.51  lits:                                   33
% 7.34/1.51  lits_eq:                                13
% 7.34/1.51  fd_pure:                                0
% 7.34/1.51  fd_pseudo:                              0
% 7.34/1.51  fd_cond:                                0
% 7.34/1.51  fd_pseudo_cond:                         5
% 7.34/1.51  ac_symbols:                             0
% 7.34/1.51  
% 7.34/1.51  ------ Propositional Solver
% 7.34/1.51  
% 7.34/1.51  prop_solver_calls:                      25
% 7.34/1.51  prop_fast_solver_calls:                 766
% 7.34/1.51  smt_solver_calls:                       0
% 7.34/1.51  smt_fast_solver_calls:                  0
% 7.34/1.51  prop_num_of_clauses:                    5987
% 7.34/1.51  prop_preprocess_simplified:             11507
% 7.34/1.51  prop_fo_subsumed:                       21
% 7.34/1.51  prop_solver_time:                       0.
% 7.34/1.51  smt_solver_time:                        0.
% 7.34/1.51  smt_fast_solver_time:                   0.
% 7.34/1.51  prop_fast_solver_time:                  0.
% 7.34/1.51  prop_unsat_core_time:                   0.
% 7.34/1.51  
% 7.34/1.51  ------ QBF
% 7.34/1.51  
% 7.34/1.51  qbf_q_res:                              0
% 7.34/1.51  qbf_num_tautologies:                    0
% 7.34/1.51  qbf_prep_cycles:                        0
% 7.34/1.51  
% 7.34/1.51  ------ BMC1
% 7.34/1.51  
% 7.34/1.51  bmc1_current_bound:                     -1
% 7.34/1.51  bmc1_last_solved_bound:                 -1
% 7.34/1.51  bmc1_unsat_core_size:                   -1
% 7.34/1.51  bmc1_unsat_core_parents_size:           -1
% 7.34/1.51  bmc1_merge_next_fun:                    0
% 7.34/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.34/1.51  
% 7.34/1.51  ------ Instantiation
% 7.34/1.51  
% 7.34/1.51  inst_num_of_clauses:                    1508
% 7.34/1.51  inst_num_in_passive:                    504
% 7.34/1.51  inst_num_in_active:                     374
% 7.34/1.51  inst_num_in_unprocessed:                631
% 7.34/1.51  inst_num_of_loops:                      550
% 7.34/1.51  inst_num_of_learning_restarts:          0
% 7.34/1.51  inst_num_moves_active_passive:          174
% 7.34/1.51  inst_lit_activity:                      0
% 7.34/1.51  inst_lit_activity_moves:                0
% 7.34/1.51  inst_num_tautologies:                   0
% 7.34/1.51  inst_num_prop_implied:                  0
% 7.34/1.51  inst_num_existing_simplified:           0
% 7.34/1.51  inst_num_eq_res_simplified:             0
% 7.34/1.51  inst_num_child_elim:                    0
% 7.34/1.51  inst_num_of_dismatching_blockings:      2317
% 7.34/1.51  inst_num_of_non_proper_insts:           1719
% 7.34/1.51  inst_num_of_duplicates:                 0
% 7.34/1.51  inst_inst_num_from_inst_to_res:         0
% 7.34/1.51  inst_dismatching_checking_time:         0.
% 7.34/1.51  
% 7.34/1.51  ------ Resolution
% 7.34/1.51  
% 7.34/1.51  res_num_of_clauses:                     0
% 7.34/1.51  res_num_in_passive:                     0
% 7.34/1.51  res_num_in_active:                      0
% 7.34/1.51  res_num_of_loops:                       61
% 7.34/1.51  res_forward_subset_subsumed:            63
% 7.34/1.51  res_backward_subset_subsumed:           4
% 7.34/1.51  res_forward_subsumed:                   0
% 7.34/1.51  res_backward_subsumed:                  0
% 7.34/1.51  res_forward_subsumption_resolution:     0
% 7.34/1.51  res_backward_subsumption_resolution:    0
% 7.34/1.51  res_clause_to_clause_subsumption:       5289
% 7.34/1.51  res_orphan_elimination:                 0
% 7.34/1.51  res_tautology_del:                      191
% 7.34/1.51  res_num_eq_res_simplified:              0
% 7.34/1.51  res_num_sel_changes:                    0
% 7.34/1.51  res_moves_from_active_to_pass:          0
% 7.34/1.51  
% 7.34/1.51  ------ Superposition
% 7.34/1.51  
% 7.34/1.51  sup_time_total:                         0.
% 7.34/1.51  sup_time_generating:                    0.
% 7.34/1.51  sup_time_sim_full:                      0.
% 7.34/1.51  sup_time_sim_immed:                     0.
% 7.34/1.51  
% 7.34/1.51  sup_num_of_clauses:                     414
% 7.34/1.51  sup_num_in_active:                      105
% 7.34/1.51  sup_num_in_passive:                     309
% 7.34/1.51  sup_num_of_loops:                       108
% 7.34/1.51  sup_fw_superposition:                   773
% 7.34/1.51  sup_bw_superposition:                   531
% 7.34/1.51  sup_immediate_simplified:               554
% 7.34/1.51  sup_given_eliminated:                   3
% 7.34/1.51  comparisons_done:                       0
% 7.34/1.51  comparisons_avoided:                    30
% 7.34/1.51  
% 7.34/1.51  ------ Simplifications
% 7.34/1.51  
% 7.34/1.51  
% 7.34/1.51  sim_fw_subset_subsumed:                 108
% 7.34/1.51  sim_bw_subset_subsumed:                 1
% 7.34/1.51  sim_fw_subsumed:                        155
% 7.34/1.51  sim_bw_subsumed:                        8
% 7.34/1.51  sim_fw_subsumption_res:                 9
% 7.34/1.51  sim_bw_subsumption_res:                 0
% 7.34/1.51  sim_tautology_del:                      25
% 7.34/1.51  sim_eq_tautology_del:                   132
% 7.34/1.51  sim_eq_res_simp:                        3
% 7.34/1.51  sim_fw_demodulated:                     276
% 7.34/1.51  sim_bw_demodulated:                     4
% 7.34/1.51  sim_light_normalised:                   196
% 7.34/1.51  sim_joinable_taut:                      0
% 7.34/1.51  sim_joinable_simp:                      0
% 7.34/1.51  sim_ac_normalised:                      0
% 7.34/1.51  sim_smt_subsumption:                    0
% 7.34/1.51  
%------------------------------------------------------------------------------
