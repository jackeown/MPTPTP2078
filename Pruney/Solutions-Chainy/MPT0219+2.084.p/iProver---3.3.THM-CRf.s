%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:22 EST 2020

% Result     : Theorem 7.84s
% Output     : CNFRefutation 7.84s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 391 expanded)
%              Number of clauses        :   54 (  72 expanded)
%              Number of leaves         :   21 ( 115 expanded)
%              Depth                    :   15
%              Number of atoms          :  351 ( 904 expanded)
%              Number of equality atoms :  267 ( 738 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f62])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f63])).

fof(f65,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f54,f64])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f65])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)),k3_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f52,f38,f58,f66])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f21,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK2 != sK3
      & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( sK2 != sK3
    & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f31])).

fof(f60,plain,(
    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f81,plain,(
    k5_xboole_0(k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f60,f38,f66,f66,f66])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

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
    inference(nnf_transformation,[],[f20])).

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
    inference(flattening,[],[f22])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
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
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f43,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f73,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f43,f64])).

fof(f82,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f73])).

fof(f83,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f82])).

fof(f41,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f41,f64])).

fof(f86,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f75])).

fof(f87,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f86])).

fof(f40,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f40,f64])).

fof(f88,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f48,f66])).

fof(f91,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f49,f66])).

fof(f89,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k5_enumset1(X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f79])).

fof(f90,plain,(
    ! [X3] : r2_hidden(X3,k5_enumset1(X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f89])).

fof(f61,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_672,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1269,plain,
    ( X0 != X1
    | k5_enumset1(X2,X3,X4,X5,X6,X7,X8) != X1
    | k5_enumset1(X2,X3,X4,X5,X6,X7,X8) = X0 ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_1869,plain,
    ( X0 != k5_enumset1(X1,X2,X3,X4,X5,X6,X7)
    | k5_enumset1(X8,X9,X10,X11,X12,X13,X14) = X0
    | k5_enumset1(X8,X9,X10,X11,X12,X13,X14) != k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_2560,plain,
    ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1869])).

cnf(c_18888,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X1,sK3) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k5_enumset1(X0,X0,X0,X0,X0,X1,sK3) = k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2560])).

cnf(c_18889,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_18888])).

cnf(c_2589,plain,
    ( X0 != k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = X0
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_4297,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X1,sK3) != k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_enumset1(X0,X0,X0,X0,X0,X1,sK3)
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    inference(instantiation,[status(thm)],[c_2589])).

cnf(c_4299,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    inference(instantiation,[status(thm)],[c_4297])).

cnf(c_1866,plain,
    ( X0 != k5_enumset1(X1,X2,X3,X4,X5,X6,X7)
    | k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = X0
    | k5_enumset1(X1,X2,X3,X4,X5,X6,X7) != k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_2497,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1866])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)),k3_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_669,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(theory_normalisation,[status(thm)],[c_0,c_3,c_1])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_878,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_3,c_1])).

cnf(c_1462,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_878])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1492,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_1462,c_2])).

cnf(c_20,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_667,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(theory_normalisation,[status(thm)],[c_20,c_3,c_1])).

cnf(c_1215,plain,
    ( k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))),X0)) = k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0) ),
    inference(superposition,[status(thm)],[c_667,c_3])).

cnf(c_1228,plain,
    ( k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),X0))) = k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0) ),
    inference(superposition,[status(thm)],[c_3,c_1215])).

cnf(c_1643,plain,
    ( k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)) ),
    inference(superposition,[status(thm)],[c_1492,c_1228])).

cnf(c_1825,plain,
    ( k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_669,c_1643])).

cnf(c_1826,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_1825,c_2,c_4])).

cnf(c_676,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_970,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK3,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))
    | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_676])).

cnf(c_1157,plain,
    ( ~ r2_hidden(sK3,X0)
    | r2_hidden(sK3,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
    | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_970])).

cnf(c_1559,plain,
    ( r2_hidden(sK3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
    | ~ r2_hidden(sK3,k5_enumset1(X1,X1,X1,X1,X1,X2,sK3))
    | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != k5_enumset1(X1,X1,X1,X1,X1,X2,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1157])).

cnf(c_1561,plain,
    ( ~ r2_hidden(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | r2_hidden(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1559])).

cnf(c_10,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1104,plain,
    ( r2_hidden(sK3,k5_enumset1(X0,X0,X0,X0,X0,X1,sK3)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1106,plain,
    ( r2_hidden(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1104])).

cnf(c_12,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1098,plain,
    ( r2_hidden(sK3,k5_enumset1(sK3,sK3,sK3,sK3,sK3,X0,X1)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1100,plain,
    ( r2_hidden(sK3,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_1098])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_896,plain,
    ( ~ r2_hidden(sK3,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))
    | sK3 = X0
    | sK3 = X1
    | sK3 = X2 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_985,plain,
    ( ~ r2_hidden(sK3,k5_enumset1(sK3,sK3,sK3,sK3,sK3,X0,X1))
    | sK3 = X0
    | sK3 = X1
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_896])).

cnf(c_987,plain,
    ( ~ r2_hidden(sK3,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK2,sK2))
    | sK3 = sK3
    | sK3 = sK2 ),
    inference(instantiation,[status(thm)],[c_985])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_897,plain,
    ( ~ r2_hidden(sK3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_899,plain,
    ( ~ r2_hidden(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | sK3 = sK2 ),
    inference(instantiation,[status(thm)],[c_897])).

cnf(c_888,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_889,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_888])).

cnf(c_673,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | k5_enumset1(X0,X2,X4,X6,X8,X10,X12) = k5_enumset1(X1,X3,X5,X7,X9,X11,X13) ),
    theory(equality)).

cnf(c_677,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_16,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_26,plain,
    ( r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_23,plain,
    ( ~ r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_19,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18889,c_4299,c_2497,c_1826,c_1561,c_1106,c_1100,c_987,c_899,c_889,c_667,c_677,c_26,c_23,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:54:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.84/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.84/1.48  
% 7.84/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.84/1.48  
% 7.84/1.48  ------  iProver source info
% 7.84/1.48  
% 7.84/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.84/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.84/1.48  git: non_committed_changes: false
% 7.84/1.48  git: last_make_outside_of_git: false
% 7.84/1.48  
% 7.84/1.48  ------ 
% 7.84/1.48  
% 7.84/1.48  ------ Input Options
% 7.84/1.48  
% 7.84/1.48  --out_options                           all
% 7.84/1.48  --tptp_safe_out                         true
% 7.84/1.48  --problem_path                          ""
% 7.84/1.48  --include_path                          ""
% 7.84/1.48  --clausifier                            res/vclausify_rel
% 7.84/1.48  --clausifier_options                    ""
% 7.84/1.48  --stdin                                 false
% 7.84/1.48  --stats_out                             all
% 7.84/1.48  
% 7.84/1.48  ------ General Options
% 7.84/1.48  
% 7.84/1.48  --fof                                   false
% 7.84/1.48  --time_out_real                         305.
% 7.84/1.48  --time_out_virtual                      -1.
% 7.84/1.48  --symbol_type_check                     false
% 7.84/1.48  --clausify_out                          false
% 7.84/1.48  --sig_cnt_out                           false
% 7.84/1.48  --trig_cnt_out                          false
% 7.84/1.48  --trig_cnt_out_tolerance                1.
% 7.84/1.48  --trig_cnt_out_sk_spl                   false
% 7.84/1.48  --abstr_cl_out                          false
% 7.84/1.48  
% 7.84/1.48  ------ Global Options
% 7.84/1.48  
% 7.84/1.48  --schedule                              default
% 7.84/1.48  --add_important_lit                     false
% 7.84/1.48  --prop_solver_per_cl                    1000
% 7.84/1.48  --min_unsat_core                        false
% 7.84/1.48  --soft_assumptions                      false
% 7.84/1.48  --soft_lemma_size                       3
% 7.84/1.48  --prop_impl_unit_size                   0
% 7.84/1.48  --prop_impl_unit                        []
% 7.84/1.48  --share_sel_clauses                     true
% 7.84/1.48  --reset_solvers                         false
% 7.84/1.48  --bc_imp_inh                            [conj_cone]
% 7.84/1.48  --conj_cone_tolerance                   3.
% 7.84/1.48  --extra_neg_conj                        none
% 7.84/1.48  --large_theory_mode                     true
% 7.84/1.48  --prolific_symb_bound                   200
% 7.84/1.48  --lt_threshold                          2000
% 7.84/1.48  --clause_weak_htbl                      true
% 7.84/1.48  --gc_record_bc_elim                     false
% 7.84/1.48  
% 7.84/1.48  ------ Preprocessing Options
% 7.84/1.48  
% 7.84/1.48  --preprocessing_flag                    true
% 7.84/1.48  --time_out_prep_mult                    0.1
% 7.84/1.48  --splitting_mode                        input
% 7.84/1.48  --splitting_grd                         true
% 7.84/1.48  --splitting_cvd                         false
% 7.84/1.48  --splitting_cvd_svl                     false
% 7.84/1.48  --splitting_nvd                         32
% 7.84/1.48  --sub_typing                            true
% 7.84/1.48  --prep_gs_sim                           true
% 7.84/1.48  --prep_unflatten                        true
% 7.84/1.48  --prep_res_sim                          true
% 7.84/1.48  --prep_upred                            true
% 7.84/1.48  --prep_sem_filter                       exhaustive
% 7.84/1.48  --prep_sem_filter_out                   false
% 7.84/1.48  --pred_elim                             true
% 7.84/1.48  --res_sim_input                         true
% 7.84/1.48  --eq_ax_congr_red                       true
% 7.84/1.48  --pure_diseq_elim                       true
% 7.84/1.48  --brand_transform                       false
% 7.84/1.48  --non_eq_to_eq                          false
% 7.84/1.48  --prep_def_merge                        true
% 7.84/1.48  --prep_def_merge_prop_impl              false
% 7.84/1.48  --prep_def_merge_mbd                    true
% 7.84/1.48  --prep_def_merge_tr_red                 false
% 7.84/1.48  --prep_def_merge_tr_cl                  false
% 7.84/1.48  --smt_preprocessing                     true
% 7.84/1.48  --smt_ac_axioms                         fast
% 7.84/1.48  --preprocessed_out                      false
% 7.84/1.48  --preprocessed_stats                    false
% 7.84/1.48  
% 7.84/1.48  ------ Abstraction refinement Options
% 7.84/1.48  
% 7.84/1.48  --abstr_ref                             []
% 7.84/1.48  --abstr_ref_prep                        false
% 7.84/1.48  --abstr_ref_until_sat                   false
% 7.84/1.48  --abstr_ref_sig_restrict                funpre
% 7.84/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.84/1.48  --abstr_ref_under                       []
% 7.84/1.48  
% 7.84/1.48  ------ SAT Options
% 7.84/1.48  
% 7.84/1.48  --sat_mode                              false
% 7.84/1.48  --sat_fm_restart_options                ""
% 7.84/1.48  --sat_gr_def                            false
% 7.84/1.48  --sat_epr_types                         true
% 7.84/1.48  --sat_non_cyclic_types                  false
% 7.84/1.48  --sat_finite_models                     false
% 7.84/1.48  --sat_fm_lemmas                         false
% 7.84/1.48  --sat_fm_prep                           false
% 7.84/1.48  --sat_fm_uc_incr                        true
% 7.84/1.48  --sat_out_model                         small
% 7.84/1.48  --sat_out_clauses                       false
% 7.84/1.48  
% 7.84/1.48  ------ QBF Options
% 7.84/1.48  
% 7.84/1.48  --qbf_mode                              false
% 7.84/1.48  --qbf_elim_univ                         false
% 7.84/1.48  --qbf_dom_inst                          none
% 7.84/1.48  --qbf_dom_pre_inst                      false
% 7.84/1.48  --qbf_sk_in                             false
% 7.84/1.48  --qbf_pred_elim                         true
% 7.84/1.48  --qbf_split                             512
% 7.84/1.48  
% 7.84/1.48  ------ BMC1 Options
% 7.84/1.48  
% 7.84/1.48  --bmc1_incremental                      false
% 7.84/1.48  --bmc1_axioms                           reachable_all
% 7.84/1.48  --bmc1_min_bound                        0
% 7.84/1.48  --bmc1_max_bound                        -1
% 7.84/1.48  --bmc1_max_bound_default                -1
% 7.84/1.48  --bmc1_symbol_reachability              true
% 7.84/1.48  --bmc1_property_lemmas                  false
% 7.84/1.48  --bmc1_k_induction                      false
% 7.84/1.48  --bmc1_non_equiv_states                 false
% 7.84/1.48  --bmc1_deadlock                         false
% 7.84/1.48  --bmc1_ucm                              false
% 7.84/1.48  --bmc1_add_unsat_core                   none
% 7.84/1.48  --bmc1_unsat_core_children              false
% 7.84/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.84/1.48  --bmc1_out_stat                         full
% 7.84/1.48  --bmc1_ground_init                      false
% 7.84/1.48  --bmc1_pre_inst_next_state              false
% 7.84/1.48  --bmc1_pre_inst_state                   false
% 7.84/1.48  --bmc1_pre_inst_reach_state             false
% 7.84/1.48  --bmc1_out_unsat_core                   false
% 7.84/1.48  --bmc1_aig_witness_out                  false
% 7.84/1.48  --bmc1_verbose                          false
% 7.84/1.48  --bmc1_dump_clauses_tptp                false
% 7.84/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.84/1.48  --bmc1_dump_file                        -
% 7.84/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.84/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.84/1.48  --bmc1_ucm_extend_mode                  1
% 7.84/1.48  --bmc1_ucm_init_mode                    2
% 7.84/1.48  --bmc1_ucm_cone_mode                    none
% 7.84/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.84/1.48  --bmc1_ucm_relax_model                  4
% 7.84/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.84/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.84/1.48  --bmc1_ucm_layered_model                none
% 7.84/1.48  --bmc1_ucm_max_lemma_size               10
% 7.84/1.48  
% 7.84/1.48  ------ AIG Options
% 7.84/1.48  
% 7.84/1.48  --aig_mode                              false
% 7.84/1.48  
% 7.84/1.48  ------ Instantiation Options
% 7.84/1.48  
% 7.84/1.48  --instantiation_flag                    true
% 7.84/1.48  --inst_sos_flag                         true
% 7.84/1.48  --inst_sos_phase                        true
% 7.84/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.84/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.84/1.48  --inst_lit_sel_side                     num_symb
% 7.84/1.48  --inst_solver_per_active                1400
% 7.84/1.48  --inst_solver_calls_frac                1.
% 7.84/1.48  --inst_passive_queue_type               priority_queues
% 7.84/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.84/1.48  --inst_passive_queues_freq              [25;2]
% 7.84/1.48  --inst_dismatching                      true
% 7.84/1.48  --inst_eager_unprocessed_to_passive     true
% 7.84/1.48  --inst_prop_sim_given                   true
% 7.84/1.48  --inst_prop_sim_new                     false
% 7.84/1.48  --inst_subs_new                         false
% 7.84/1.48  --inst_eq_res_simp                      false
% 7.84/1.48  --inst_subs_given                       false
% 7.84/1.48  --inst_orphan_elimination               true
% 7.84/1.48  --inst_learning_loop_flag               true
% 7.84/1.48  --inst_learning_start                   3000
% 7.84/1.48  --inst_learning_factor                  2
% 7.84/1.48  --inst_start_prop_sim_after_learn       3
% 7.84/1.48  --inst_sel_renew                        solver
% 7.84/1.48  --inst_lit_activity_flag                true
% 7.84/1.48  --inst_restr_to_given                   false
% 7.84/1.48  --inst_activity_threshold               500
% 7.84/1.48  --inst_out_proof                        true
% 7.84/1.48  
% 7.84/1.48  ------ Resolution Options
% 7.84/1.48  
% 7.84/1.48  --resolution_flag                       true
% 7.84/1.48  --res_lit_sel                           adaptive
% 7.84/1.48  --res_lit_sel_side                      none
% 7.84/1.48  --res_ordering                          kbo
% 7.84/1.48  --res_to_prop_solver                    active
% 7.84/1.48  --res_prop_simpl_new                    false
% 7.84/1.48  --res_prop_simpl_given                  true
% 7.84/1.48  --res_passive_queue_type                priority_queues
% 7.84/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.84/1.48  --res_passive_queues_freq               [15;5]
% 7.84/1.48  --res_forward_subs                      full
% 7.84/1.48  --res_backward_subs                     full
% 7.84/1.48  --res_forward_subs_resolution           true
% 7.84/1.48  --res_backward_subs_resolution          true
% 7.84/1.48  --res_orphan_elimination                true
% 7.84/1.48  --res_time_limit                        2.
% 7.84/1.48  --res_out_proof                         true
% 7.84/1.48  
% 7.84/1.48  ------ Superposition Options
% 7.84/1.48  
% 7.84/1.48  --superposition_flag                    true
% 7.84/1.48  --sup_passive_queue_type                priority_queues
% 7.84/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.84/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.84/1.48  --demod_completeness_check              fast
% 7.84/1.48  --demod_use_ground                      true
% 7.84/1.48  --sup_to_prop_solver                    passive
% 7.84/1.48  --sup_prop_simpl_new                    true
% 7.84/1.48  --sup_prop_simpl_given                  true
% 7.84/1.48  --sup_fun_splitting                     true
% 7.84/1.48  --sup_smt_interval                      50000
% 7.84/1.48  
% 7.84/1.48  ------ Superposition Simplification Setup
% 7.84/1.48  
% 7.84/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.84/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.84/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.84/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.84/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.84/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.84/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.84/1.48  --sup_immed_triv                        [TrivRules]
% 7.84/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.48  --sup_immed_bw_main                     []
% 7.84/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.84/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.84/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.48  --sup_input_bw                          []
% 7.84/1.48  
% 7.84/1.48  ------ Combination Options
% 7.84/1.48  
% 7.84/1.48  --comb_res_mult                         3
% 7.84/1.48  --comb_sup_mult                         2
% 7.84/1.48  --comb_inst_mult                        10
% 7.84/1.48  
% 7.84/1.48  ------ Debug Options
% 7.84/1.48  
% 7.84/1.48  --dbg_backtrace                         false
% 7.84/1.48  --dbg_dump_prop_clauses                 false
% 7.84/1.48  --dbg_dump_prop_clauses_file            -
% 7.84/1.48  --dbg_out_stat                          false
% 7.84/1.48  ------ Parsing...
% 7.84/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.84/1.48  
% 7.84/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.84/1.48  
% 7.84/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.84/1.48  
% 7.84/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.84/1.48  ------ Proving...
% 7.84/1.48  ------ Problem Properties 
% 7.84/1.48  
% 7.84/1.48  
% 7.84/1.48  clauses                                 21
% 7.84/1.48  conjectures                             2
% 7.84/1.48  EPR                                     1
% 7.84/1.48  Horn                                    18
% 7.84/1.48  unary                                   13
% 7.84/1.48  binary                                  1
% 7.84/1.48  lits                                    39
% 7.84/1.48  lits eq                                 27
% 7.84/1.48  fd_pure                                 0
% 7.84/1.48  fd_pseudo                               0
% 7.84/1.48  fd_cond                                 0
% 7.84/1.48  fd_pseudo_cond                          6
% 7.84/1.48  AC symbols                              1
% 7.84/1.48  
% 7.84/1.48  ------ Schedule dynamic 5 is on 
% 7.84/1.48  
% 7.84/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.84/1.48  
% 7.84/1.48  
% 7.84/1.48  ------ 
% 7.84/1.48  Current options:
% 7.84/1.48  ------ 
% 7.84/1.48  
% 7.84/1.48  ------ Input Options
% 7.84/1.48  
% 7.84/1.48  --out_options                           all
% 7.84/1.48  --tptp_safe_out                         true
% 7.84/1.48  --problem_path                          ""
% 7.84/1.48  --include_path                          ""
% 7.84/1.48  --clausifier                            res/vclausify_rel
% 7.84/1.48  --clausifier_options                    ""
% 7.84/1.48  --stdin                                 false
% 7.84/1.48  --stats_out                             all
% 7.84/1.48  
% 7.84/1.48  ------ General Options
% 7.84/1.48  
% 7.84/1.48  --fof                                   false
% 7.84/1.48  --time_out_real                         305.
% 7.84/1.48  --time_out_virtual                      -1.
% 7.84/1.48  --symbol_type_check                     false
% 7.84/1.48  --clausify_out                          false
% 7.84/1.48  --sig_cnt_out                           false
% 7.84/1.48  --trig_cnt_out                          false
% 7.84/1.48  --trig_cnt_out_tolerance                1.
% 7.84/1.48  --trig_cnt_out_sk_spl                   false
% 7.84/1.48  --abstr_cl_out                          false
% 7.84/1.48  
% 7.84/1.48  ------ Global Options
% 7.84/1.48  
% 7.84/1.48  --schedule                              default
% 7.84/1.48  --add_important_lit                     false
% 7.84/1.48  --prop_solver_per_cl                    1000
% 7.84/1.48  --min_unsat_core                        false
% 7.84/1.48  --soft_assumptions                      false
% 7.84/1.48  --soft_lemma_size                       3
% 7.84/1.48  --prop_impl_unit_size                   0
% 7.84/1.48  --prop_impl_unit                        []
% 7.84/1.48  --share_sel_clauses                     true
% 7.84/1.48  --reset_solvers                         false
% 7.84/1.48  --bc_imp_inh                            [conj_cone]
% 7.84/1.48  --conj_cone_tolerance                   3.
% 7.84/1.48  --extra_neg_conj                        none
% 7.84/1.48  --large_theory_mode                     true
% 7.84/1.48  --prolific_symb_bound                   200
% 7.84/1.48  --lt_threshold                          2000
% 7.84/1.48  --clause_weak_htbl                      true
% 7.84/1.48  --gc_record_bc_elim                     false
% 7.84/1.48  
% 7.84/1.48  ------ Preprocessing Options
% 7.84/1.48  
% 7.84/1.48  --preprocessing_flag                    true
% 7.84/1.48  --time_out_prep_mult                    0.1
% 7.84/1.48  --splitting_mode                        input
% 7.84/1.48  --splitting_grd                         true
% 7.84/1.48  --splitting_cvd                         false
% 7.84/1.48  --splitting_cvd_svl                     false
% 7.84/1.48  --splitting_nvd                         32
% 7.84/1.48  --sub_typing                            true
% 7.84/1.48  --prep_gs_sim                           true
% 7.84/1.48  --prep_unflatten                        true
% 7.84/1.48  --prep_res_sim                          true
% 7.84/1.48  --prep_upred                            true
% 7.84/1.48  --prep_sem_filter                       exhaustive
% 7.84/1.48  --prep_sem_filter_out                   false
% 7.84/1.48  --pred_elim                             true
% 7.84/1.48  --res_sim_input                         true
% 7.84/1.48  --eq_ax_congr_red                       true
% 7.84/1.48  --pure_diseq_elim                       true
% 7.84/1.48  --brand_transform                       false
% 7.84/1.48  --non_eq_to_eq                          false
% 7.84/1.48  --prep_def_merge                        true
% 7.84/1.48  --prep_def_merge_prop_impl              false
% 7.84/1.48  --prep_def_merge_mbd                    true
% 7.84/1.48  --prep_def_merge_tr_red                 false
% 7.84/1.48  --prep_def_merge_tr_cl                  false
% 7.84/1.48  --smt_preprocessing                     true
% 7.84/1.48  --smt_ac_axioms                         fast
% 7.84/1.48  --preprocessed_out                      false
% 7.84/1.48  --preprocessed_stats                    false
% 7.84/1.48  
% 7.84/1.48  ------ Abstraction refinement Options
% 7.84/1.48  
% 7.84/1.48  --abstr_ref                             []
% 7.84/1.48  --abstr_ref_prep                        false
% 7.84/1.48  --abstr_ref_until_sat                   false
% 7.84/1.48  --abstr_ref_sig_restrict                funpre
% 7.84/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.84/1.48  --abstr_ref_under                       []
% 7.84/1.48  
% 7.84/1.48  ------ SAT Options
% 7.84/1.48  
% 7.84/1.48  --sat_mode                              false
% 7.84/1.48  --sat_fm_restart_options                ""
% 7.84/1.48  --sat_gr_def                            false
% 7.84/1.48  --sat_epr_types                         true
% 7.84/1.48  --sat_non_cyclic_types                  false
% 7.84/1.48  --sat_finite_models                     false
% 7.84/1.48  --sat_fm_lemmas                         false
% 7.84/1.48  --sat_fm_prep                           false
% 7.84/1.48  --sat_fm_uc_incr                        true
% 7.84/1.48  --sat_out_model                         small
% 7.84/1.48  --sat_out_clauses                       false
% 7.84/1.48  
% 7.84/1.48  ------ QBF Options
% 7.84/1.48  
% 7.84/1.48  --qbf_mode                              false
% 7.84/1.48  --qbf_elim_univ                         false
% 7.84/1.48  --qbf_dom_inst                          none
% 7.84/1.48  --qbf_dom_pre_inst                      false
% 7.84/1.48  --qbf_sk_in                             false
% 7.84/1.48  --qbf_pred_elim                         true
% 7.84/1.48  --qbf_split                             512
% 7.84/1.48  
% 7.84/1.48  ------ BMC1 Options
% 7.84/1.48  
% 7.84/1.48  --bmc1_incremental                      false
% 7.84/1.48  --bmc1_axioms                           reachable_all
% 7.84/1.48  --bmc1_min_bound                        0
% 7.84/1.48  --bmc1_max_bound                        -1
% 7.84/1.48  --bmc1_max_bound_default                -1
% 7.84/1.48  --bmc1_symbol_reachability              true
% 7.84/1.48  --bmc1_property_lemmas                  false
% 7.84/1.48  --bmc1_k_induction                      false
% 7.84/1.48  --bmc1_non_equiv_states                 false
% 7.84/1.48  --bmc1_deadlock                         false
% 7.84/1.48  --bmc1_ucm                              false
% 7.84/1.48  --bmc1_add_unsat_core                   none
% 7.84/1.48  --bmc1_unsat_core_children              false
% 7.84/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.84/1.48  --bmc1_out_stat                         full
% 7.84/1.48  --bmc1_ground_init                      false
% 7.84/1.48  --bmc1_pre_inst_next_state              false
% 7.84/1.48  --bmc1_pre_inst_state                   false
% 7.84/1.48  --bmc1_pre_inst_reach_state             false
% 7.84/1.48  --bmc1_out_unsat_core                   false
% 7.84/1.48  --bmc1_aig_witness_out                  false
% 7.84/1.48  --bmc1_verbose                          false
% 7.84/1.48  --bmc1_dump_clauses_tptp                false
% 7.84/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.84/1.48  --bmc1_dump_file                        -
% 7.84/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.84/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.84/1.48  --bmc1_ucm_extend_mode                  1
% 7.84/1.48  --bmc1_ucm_init_mode                    2
% 7.84/1.48  --bmc1_ucm_cone_mode                    none
% 7.84/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.84/1.48  --bmc1_ucm_relax_model                  4
% 7.84/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.84/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.84/1.48  --bmc1_ucm_layered_model                none
% 7.84/1.48  --bmc1_ucm_max_lemma_size               10
% 7.84/1.48  
% 7.84/1.48  ------ AIG Options
% 7.84/1.48  
% 7.84/1.48  --aig_mode                              false
% 7.84/1.48  
% 7.84/1.48  ------ Instantiation Options
% 7.84/1.48  
% 7.84/1.48  --instantiation_flag                    true
% 7.84/1.48  --inst_sos_flag                         true
% 7.84/1.48  --inst_sos_phase                        true
% 7.84/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.84/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.84/1.48  --inst_lit_sel_side                     none
% 7.84/1.48  --inst_solver_per_active                1400
% 7.84/1.48  --inst_solver_calls_frac                1.
% 7.84/1.48  --inst_passive_queue_type               priority_queues
% 7.84/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.84/1.48  --inst_passive_queues_freq              [25;2]
% 7.84/1.48  --inst_dismatching                      true
% 7.84/1.48  --inst_eager_unprocessed_to_passive     true
% 7.84/1.48  --inst_prop_sim_given                   true
% 7.84/1.48  --inst_prop_sim_new                     false
% 7.84/1.48  --inst_subs_new                         false
% 7.84/1.48  --inst_eq_res_simp                      false
% 7.84/1.48  --inst_subs_given                       false
% 7.84/1.48  --inst_orphan_elimination               true
% 7.84/1.48  --inst_learning_loop_flag               true
% 7.84/1.48  --inst_learning_start                   3000
% 7.84/1.48  --inst_learning_factor                  2
% 7.84/1.48  --inst_start_prop_sim_after_learn       3
% 7.84/1.48  --inst_sel_renew                        solver
% 7.84/1.48  --inst_lit_activity_flag                true
% 7.84/1.48  --inst_restr_to_given                   false
% 7.84/1.48  --inst_activity_threshold               500
% 7.84/1.48  --inst_out_proof                        true
% 7.84/1.48  
% 7.84/1.48  ------ Resolution Options
% 7.84/1.48  
% 7.84/1.48  --resolution_flag                       false
% 7.84/1.48  --res_lit_sel                           adaptive
% 7.84/1.48  --res_lit_sel_side                      none
% 7.84/1.48  --res_ordering                          kbo
% 7.84/1.48  --res_to_prop_solver                    active
% 7.84/1.48  --res_prop_simpl_new                    false
% 7.84/1.48  --res_prop_simpl_given                  true
% 7.84/1.48  --res_passive_queue_type                priority_queues
% 7.84/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.84/1.48  --res_passive_queues_freq               [15;5]
% 7.84/1.48  --res_forward_subs                      full
% 7.84/1.48  --res_backward_subs                     full
% 7.84/1.48  --res_forward_subs_resolution           true
% 7.84/1.48  --res_backward_subs_resolution          true
% 7.84/1.48  --res_orphan_elimination                true
% 7.84/1.48  --res_time_limit                        2.
% 7.84/1.48  --res_out_proof                         true
% 7.84/1.48  
% 7.84/1.48  ------ Superposition Options
% 7.84/1.48  
% 7.84/1.48  --superposition_flag                    true
% 7.84/1.48  --sup_passive_queue_type                priority_queues
% 7.84/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.84/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.84/1.48  --demod_completeness_check              fast
% 7.84/1.48  --demod_use_ground                      true
% 7.84/1.48  --sup_to_prop_solver                    passive
% 7.84/1.48  --sup_prop_simpl_new                    true
% 7.84/1.48  --sup_prop_simpl_given                  true
% 7.84/1.48  --sup_fun_splitting                     true
% 7.84/1.48  --sup_smt_interval                      50000
% 7.84/1.48  
% 7.84/1.48  ------ Superposition Simplification Setup
% 7.84/1.48  
% 7.84/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.84/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.84/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.84/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.84/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.84/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.84/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.84/1.48  --sup_immed_triv                        [TrivRules]
% 7.84/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.48  --sup_immed_bw_main                     []
% 7.84/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.84/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.84/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.84/1.48  --sup_input_bw                          []
% 7.84/1.48  
% 7.84/1.48  ------ Combination Options
% 7.84/1.48  
% 7.84/1.48  --comb_res_mult                         3
% 7.84/1.48  --comb_sup_mult                         2
% 7.84/1.48  --comb_inst_mult                        10
% 7.84/1.48  
% 7.84/1.48  ------ Debug Options
% 7.84/1.48  
% 7.84/1.48  --dbg_backtrace                         false
% 7.84/1.48  --dbg_dump_prop_clauses                 false
% 7.84/1.48  --dbg_dump_prop_clauses_file            -
% 7.84/1.48  --dbg_out_stat                          false
% 7.84/1.48  
% 7.84/1.48  
% 7.84/1.48  
% 7.84/1.48  
% 7.84/1.48  ------ Proving...
% 7.84/1.48  
% 7.84/1.48  
% 7.84/1.48  % SZS status Theorem for theBenchmark.p
% 7.84/1.48  
% 7.84/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.84/1.48  
% 7.84/1.48  fof(f10,axiom,(
% 7.84/1.48    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f52,plain,(
% 7.84/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.84/1.48    inference(cnf_transformation,[],[f10])).
% 7.84/1.48  
% 7.84/1.48  fof(f6,axiom,(
% 7.84/1.48    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f38,plain,(
% 7.84/1.48    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 7.84/1.48    inference(cnf_transformation,[],[f6])).
% 7.84/1.48  
% 7.84/1.48  fof(f11,axiom,(
% 7.84/1.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f53,plain,(
% 7.84/1.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.84/1.48    inference(cnf_transformation,[],[f11])).
% 7.84/1.48  
% 7.84/1.48  fof(f12,axiom,(
% 7.84/1.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f54,plain,(
% 7.84/1.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.84/1.48    inference(cnf_transformation,[],[f12])).
% 7.84/1.48  
% 7.84/1.48  fof(f13,axiom,(
% 7.84/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f55,plain,(
% 7.84/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.84/1.48    inference(cnf_transformation,[],[f13])).
% 7.84/1.48  
% 7.84/1.48  fof(f14,axiom,(
% 7.84/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f56,plain,(
% 7.84/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.84/1.48    inference(cnf_transformation,[],[f14])).
% 7.84/1.48  
% 7.84/1.48  fof(f15,axiom,(
% 7.84/1.48    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f57,plain,(
% 7.84/1.48    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.84/1.48    inference(cnf_transformation,[],[f15])).
% 7.84/1.48  
% 7.84/1.48  fof(f16,axiom,(
% 7.84/1.48    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f58,plain,(
% 7.84/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.84/1.48    inference(cnf_transformation,[],[f16])).
% 7.84/1.48  
% 7.84/1.48  fof(f62,plain,(
% 7.84/1.48    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.84/1.48    inference(definition_unfolding,[],[f57,f58])).
% 7.84/1.48  
% 7.84/1.48  fof(f63,plain,(
% 7.84/1.48    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.84/1.48    inference(definition_unfolding,[],[f56,f62])).
% 7.84/1.48  
% 7.84/1.48  fof(f64,plain,(
% 7.84/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 7.84/1.48    inference(definition_unfolding,[],[f55,f63])).
% 7.84/1.48  
% 7.84/1.48  fof(f65,plain,(
% 7.84/1.48    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.84/1.48    inference(definition_unfolding,[],[f54,f64])).
% 7.84/1.48  
% 7.84/1.48  fof(f66,plain,(
% 7.84/1.48    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 7.84/1.48    inference(definition_unfolding,[],[f53,f65])).
% 7.84/1.48  
% 7.84/1.48  fof(f67,plain,(
% 7.84/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)),k3_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.84/1.48    inference(definition_unfolding,[],[f52,f38,f58,f66])).
% 7.84/1.48  
% 7.84/1.48  fof(f4,axiom,(
% 7.84/1.48    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f36,plain,(
% 7.84/1.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.84/1.48    inference(cnf_transformation,[],[f4])).
% 7.84/1.48  
% 7.84/1.48  fof(f1,axiom,(
% 7.84/1.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f33,plain,(
% 7.84/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.84/1.48    inference(cnf_transformation,[],[f1])).
% 7.84/1.48  
% 7.84/1.48  fof(f5,axiom,(
% 7.84/1.48    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f37,plain,(
% 7.84/1.48    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.84/1.48    inference(cnf_transformation,[],[f5])).
% 7.84/1.48  
% 7.84/1.48  fof(f3,axiom,(
% 7.84/1.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f35,plain,(
% 7.84/1.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.84/1.48    inference(cnf_transformation,[],[f3])).
% 7.84/1.48  
% 7.84/1.48  fof(f18,conjecture,(
% 7.84/1.48    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 7.84/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.48  
% 7.84/1.48  fof(f19,negated_conjecture,(
% 7.84/1.48    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 7.84/1.48    inference(negated_conjecture,[],[f18])).
% 7.84/1.48  
% 7.84/1.48  fof(f21,plain,(
% 7.84/1.48    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 7.84/1.48    inference(ennf_transformation,[],[f19])).
% 7.84/1.48  
% 7.84/1.48  fof(f31,plain,(
% 7.84/1.48    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK2 != sK3 & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2))),
% 7.84/1.48    introduced(choice_axiom,[])).
% 7.84/1.48  
% 7.84/1.48  fof(f32,plain,(
% 7.84/1.48    sK2 != sK3 & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 7.84/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f31])).
% 7.84/1.49  
% 7.84/1.49  fof(f60,plain,(
% 7.84/1.49    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 7.84/1.49    inference(cnf_transformation,[],[f32])).
% 7.84/1.49  
% 7.84/1.49  fof(f81,plain,(
% 7.84/1.49    k5_xboole_0(k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 7.84/1.49    inference(definition_unfolding,[],[f60,f38,f66,f66,f66])).
% 7.84/1.49  
% 7.84/1.49  fof(f8,axiom,(
% 7.84/1.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.84/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f20,plain,(
% 7.84/1.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.84/1.49    inference(ennf_transformation,[],[f8])).
% 7.84/1.49  
% 7.84/1.49  fof(f22,plain,(
% 7.84/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.84/1.49    inference(nnf_transformation,[],[f20])).
% 7.84/1.49  
% 7.84/1.49  fof(f23,plain,(
% 7.84/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.84/1.49    inference(flattening,[],[f22])).
% 7.84/1.49  
% 7.84/1.49  fof(f24,plain,(
% 7.84/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.84/1.49    inference(rectify,[],[f23])).
% 7.84/1.49  
% 7.84/1.49  fof(f25,plain,(
% 7.84/1.49    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 7.84/1.49    introduced(choice_axiom,[])).
% 7.84/1.49  
% 7.84/1.49  fof(f26,plain,(
% 7.84/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.84/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 7.84/1.49  
% 7.84/1.49  fof(f43,plain,(
% 7.84/1.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.84/1.49    inference(cnf_transformation,[],[f26])).
% 7.84/1.49  
% 7.84/1.49  fof(f73,plain,(
% 7.84/1.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.84/1.49    inference(definition_unfolding,[],[f43,f64])).
% 7.84/1.49  
% 7.84/1.49  fof(f82,plain,(
% 7.84/1.49    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 7.84/1.49    inference(equality_resolution,[],[f73])).
% 7.84/1.49  
% 7.84/1.49  fof(f83,plain,(
% 7.84/1.49    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5))) )),
% 7.84/1.49    inference(equality_resolution,[],[f82])).
% 7.84/1.49  
% 7.84/1.49  fof(f41,plain,(
% 7.84/1.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.84/1.49    inference(cnf_transformation,[],[f26])).
% 7.84/1.49  
% 7.84/1.49  fof(f75,plain,(
% 7.84/1.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.84/1.49    inference(definition_unfolding,[],[f41,f64])).
% 7.84/1.49  
% 7.84/1.49  fof(f86,plain,(
% 7.84/1.49    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 7.84/1.49    inference(equality_resolution,[],[f75])).
% 7.84/1.49  
% 7.84/1.49  fof(f87,plain,(
% 7.84/1.49    ( ! [X2,X5,X1] : (r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2))) )),
% 7.84/1.49    inference(equality_resolution,[],[f86])).
% 7.84/1.49  
% 7.84/1.49  fof(f40,plain,(
% 7.84/1.49    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 7.84/1.49    inference(cnf_transformation,[],[f26])).
% 7.84/1.49  
% 7.84/1.49  fof(f76,plain,(
% 7.84/1.49    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.84/1.49    inference(definition_unfolding,[],[f40,f64])).
% 7.84/1.49  
% 7.84/1.49  fof(f88,plain,(
% 7.84/1.49    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) )),
% 7.84/1.49    inference(equality_resolution,[],[f76])).
% 7.84/1.49  
% 7.84/1.49  fof(f9,axiom,(
% 7.84/1.49    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.84/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.84/1.49  
% 7.84/1.49  fof(f27,plain,(
% 7.84/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.84/1.49    inference(nnf_transformation,[],[f9])).
% 7.84/1.49  
% 7.84/1.49  fof(f28,plain,(
% 7.84/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.84/1.49    inference(rectify,[],[f27])).
% 7.84/1.49  
% 7.84/1.49  fof(f29,plain,(
% 7.84/1.49    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 7.84/1.49    introduced(choice_axiom,[])).
% 7.84/1.49  
% 7.84/1.49  fof(f30,plain,(
% 7.84/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.84/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 7.84/1.49  
% 7.84/1.49  fof(f48,plain,(
% 7.84/1.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.84/1.49    inference(cnf_transformation,[],[f30])).
% 7.84/1.49  
% 7.84/1.49  fof(f80,plain,(
% 7.84/1.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 7.84/1.49    inference(definition_unfolding,[],[f48,f66])).
% 7.84/1.49  
% 7.84/1.49  fof(f91,plain,(
% 7.84/1.49    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) )),
% 7.84/1.49    inference(equality_resolution,[],[f80])).
% 7.84/1.49  
% 7.84/1.49  fof(f49,plain,(
% 7.84/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.84/1.49    inference(cnf_transformation,[],[f30])).
% 7.84/1.49  
% 7.84/1.49  fof(f79,plain,(
% 7.84/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 7.84/1.49    inference(definition_unfolding,[],[f49,f66])).
% 7.84/1.49  
% 7.84/1.49  fof(f89,plain,(
% 7.84/1.49    ( ! [X3,X1] : (r2_hidden(X3,X1) | k5_enumset1(X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 7.84/1.49    inference(equality_resolution,[],[f79])).
% 7.84/1.49  
% 7.84/1.49  fof(f90,plain,(
% 7.84/1.49    ( ! [X3] : (r2_hidden(X3,k5_enumset1(X3,X3,X3,X3,X3,X3,X3))) )),
% 7.84/1.49    inference(equality_resolution,[],[f89])).
% 7.84/1.49  
% 7.84/1.49  fof(f61,plain,(
% 7.84/1.49    sK2 != sK3),
% 7.84/1.49    inference(cnf_transformation,[],[f32])).
% 7.84/1.49  
% 7.84/1.49  cnf(c_672,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_1269,plain,
% 7.84/1.49      ( X0 != X1
% 7.84/1.49      | k5_enumset1(X2,X3,X4,X5,X6,X7,X8) != X1
% 7.84/1.49      | k5_enumset1(X2,X3,X4,X5,X6,X7,X8) = X0 ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_672]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_1869,plain,
% 7.84/1.49      ( X0 != k5_enumset1(X1,X2,X3,X4,X5,X6,X7)
% 7.84/1.49      | k5_enumset1(X8,X9,X10,X11,X12,X13,X14) = X0
% 7.84/1.49      | k5_enumset1(X8,X9,X10,X11,X12,X13,X14) != k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_1269]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_2560,plain,
% 7.84/1.49      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 7.84/1.49      | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
% 7.84/1.49      | k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_1869]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_18888,plain,
% 7.84/1.49      ( k5_enumset1(X0,X0,X0,X0,X0,X1,sK3) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 7.84/1.49      | k5_enumset1(X0,X0,X0,X0,X0,X1,sK3) = k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
% 7.84/1.49      | k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_2560]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_18889,plain,
% 7.84/1.49      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 7.84/1.49      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
% 7.84/1.49      | k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_18888]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_2589,plain,
% 7.84/1.49      ( X0 != k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
% 7.84/1.49      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = X0
% 7.84/1.49      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_1269]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_4297,plain,
% 7.84/1.49      ( k5_enumset1(X0,X0,X0,X0,X0,X1,sK3) != k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
% 7.84/1.49      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_enumset1(X0,X0,X0,X0,X0,X1,sK3)
% 7.84/1.49      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_2589]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_4299,plain,
% 7.84/1.49      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
% 7.84/1.49      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 7.84/1.49      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_4297]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_1866,plain,
% 7.84/1.49      ( X0 != k5_enumset1(X1,X2,X3,X4,X5,X6,X7)
% 7.84/1.49      | k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = X0
% 7.84/1.49      | k5_enumset1(X1,X2,X3,X4,X5,X6,X7) != k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_1269]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_2497,plain,
% 7.84/1.49      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 7.84/1.49      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
% 7.84/1.49      | k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_1866]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_0,plain,
% 7.84/1.49      ( k5_xboole_0(k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)),k3_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 7.84/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_3,plain,
% 7.84/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.84/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_1,plain,
% 7.84/1.49      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.84/1.49      inference(cnf_transformation,[],[f33]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_669,plain,
% 7.84/1.49      ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 7.84/1.49      inference(theory_normalisation,[status(thm)],[c_0,c_3,c_1]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_4,plain,
% 7.84/1.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.84/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_878,plain,
% 7.84/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_3,c_1]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_1462,plain,
% 7.84/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_4,c_878]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_2,plain,
% 7.84/1.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.84/1.49      inference(cnf_transformation,[],[f35]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_1492,plain,
% 7.84/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.84/1.49      inference(demodulation,[status(thm)],[c_1462,c_2]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_20,negated_conjecture,
% 7.84/1.49      ( k5_xboole_0(k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 7.84/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_667,negated_conjecture,
% 7.84/1.49      ( k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 7.84/1.49      inference(theory_normalisation,[status(thm)],[c_20,c_3,c_1]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_1215,plain,
% 7.84/1.49      ( k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))),X0)) = k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0) ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_667,c_3]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_1228,plain,
% 7.84/1.49      ( k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),X0))) = k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),X0) ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_3,c_1215]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_1643,plain,
% 7.84/1.49      ( k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) = k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)) ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_1492,c_1228]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_1825,plain,
% 7.84/1.49      ( k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 7.84/1.49      inference(superposition,[status(thm)],[c_669,c_1643]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_1826,plain,
% 7.84/1.49      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 7.84/1.49      inference(demodulation,[status(thm)],[c_1825,c_2,c_4]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_676,plain,
% 7.84/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.84/1.49      theory(equality) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_970,plain,
% 7.84/1.49      ( ~ r2_hidden(X0,X1)
% 7.84/1.49      | r2_hidden(sK3,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))
% 7.84/1.49      | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) != X1
% 7.84/1.49      | sK3 != X0 ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_676]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_1157,plain,
% 7.84/1.49      ( ~ r2_hidden(sK3,X0)
% 7.84/1.49      | r2_hidden(sK3,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
% 7.84/1.49      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) != X0
% 7.84/1.49      | sK3 != sK3 ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_970]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_1559,plain,
% 7.84/1.49      ( r2_hidden(sK3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
% 7.84/1.49      | ~ r2_hidden(sK3,k5_enumset1(X1,X1,X1,X1,X1,X2,sK3))
% 7.84/1.49      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != k5_enumset1(X1,X1,X1,X1,X1,X2,sK3)
% 7.84/1.49      | sK3 != sK3 ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_1157]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_1561,plain,
% 7.84/1.49      ( ~ r2_hidden(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
% 7.84/1.49      | r2_hidden(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 7.84/1.49      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 7.84/1.49      | sK3 != sK3 ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_1559]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_10,plain,
% 7.84/1.49      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
% 7.84/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_1104,plain,
% 7.84/1.49      ( r2_hidden(sK3,k5_enumset1(X0,X0,X0,X0,X0,X1,sK3)) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_1106,plain,
% 7.84/1.49      ( r2_hidden(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_1104]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_12,plain,
% 7.84/1.49      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
% 7.84/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_1098,plain,
% 7.84/1.49      ( r2_hidden(sK3,k5_enumset1(sK3,sK3,sK3,sK3,sK3,X0,X1)) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_12]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_1100,plain,
% 7.84/1.49      ( r2_hidden(sK3,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK2,sK2)) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_1098]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_13,plain,
% 7.84/1.49      ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X3))
% 7.84/1.49      | X0 = X1
% 7.84/1.49      | X0 = X2
% 7.84/1.49      | X0 = X3 ),
% 7.84/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_896,plain,
% 7.84/1.49      ( ~ r2_hidden(sK3,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))
% 7.84/1.49      | sK3 = X0
% 7.84/1.49      | sK3 = X1
% 7.84/1.49      | sK3 = X2 ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_985,plain,
% 7.84/1.49      ( ~ r2_hidden(sK3,k5_enumset1(sK3,sK3,sK3,sK3,sK3,X0,X1))
% 7.84/1.49      | sK3 = X0
% 7.84/1.49      | sK3 = X1
% 7.84/1.49      | sK3 = sK3 ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_896]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_987,plain,
% 7.84/1.49      ( ~ r2_hidden(sK3,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK2,sK2))
% 7.84/1.49      | sK3 = sK3
% 7.84/1.49      | sK3 = sK2 ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_985]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_17,plain,
% 7.84/1.49      ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 7.84/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_897,plain,
% 7.84/1.49      ( ~ r2_hidden(sK3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) | sK3 = X0 ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_899,plain,
% 7.84/1.49      ( ~ r2_hidden(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 7.84/1.49      | sK3 = sK2 ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_897]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_888,plain,
% 7.84/1.49      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_672]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_889,plain,
% 7.84/1.49      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_888]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_673,plain,
% 7.84/1.49      ( X0 != X1
% 7.84/1.49      | X2 != X3
% 7.84/1.49      | X4 != X5
% 7.84/1.49      | X6 != X7
% 7.84/1.49      | X8 != X9
% 7.84/1.49      | X10 != X11
% 7.84/1.49      | X12 != X13
% 7.84/1.49      | k5_enumset1(X0,X2,X4,X6,X8,X10,X12) = k5_enumset1(X1,X3,X5,X7,X9,X11,X13) ),
% 7.84/1.49      theory(equality) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_677,plain,
% 7.84/1.49      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 7.84/1.49      | sK2 != sK2 ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_673]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_16,plain,
% 7.84/1.49      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ),
% 7.84/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_26,plain,
% 7.84/1.49      ( r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_16]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_23,plain,
% 7.84/1.49      ( ~ r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 7.84/1.49      | sK2 = sK2 ),
% 7.84/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(c_19,negated_conjecture,
% 7.84/1.49      ( sK2 != sK3 ),
% 7.84/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.84/1.49  
% 7.84/1.49  cnf(contradiction,plain,
% 7.84/1.49      ( $false ),
% 7.84/1.49      inference(minisat,
% 7.84/1.49                [status(thm)],
% 7.84/1.49                [c_18889,c_4299,c_2497,c_1826,c_1561,c_1106,c_1100,c_987,
% 7.84/1.49                 c_899,c_889,c_667,c_677,c_26,c_23,c_19]) ).
% 7.84/1.49  
% 7.84/1.49  
% 7.84/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.84/1.49  
% 7.84/1.49  ------                               Statistics
% 7.84/1.49  
% 7.84/1.49  ------ General
% 7.84/1.49  
% 7.84/1.49  abstr_ref_over_cycles:                  0
% 7.84/1.49  abstr_ref_under_cycles:                 0
% 7.84/1.49  gc_basic_clause_elim:                   0
% 7.84/1.49  forced_gc_time:                         0
% 7.84/1.49  parsing_time:                           0.008
% 7.84/1.49  unif_index_cands_time:                  0.
% 7.84/1.49  unif_index_add_time:                    0.
% 7.84/1.49  orderings_time:                         0.
% 7.84/1.49  out_proof_time:                         0.011
% 7.84/1.49  total_time:                             0.837
% 7.84/1.49  num_of_symbols:                         41
% 7.84/1.49  num_of_terms:                           43965
% 7.84/1.49  
% 7.84/1.49  ------ Preprocessing
% 7.84/1.49  
% 7.84/1.49  num_of_splits:                          0
% 7.84/1.49  num_of_split_atoms:                     0
% 7.84/1.49  num_of_reused_defs:                     0
% 7.84/1.49  num_eq_ax_congr_red:                    28
% 7.84/1.49  num_of_sem_filtered_clauses:            1
% 7.84/1.49  num_of_subtypes:                        0
% 7.84/1.49  monotx_restored_types:                  0
% 7.84/1.49  sat_num_of_epr_types:                   0
% 7.84/1.49  sat_num_of_non_cyclic_types:            0
% 7.84/1.49  sat_guarded_non_collapsed_types:        0
% 7.84/1.49  num_pure_diseq_elim:                    0
% 7.84/1.49  simp_replaced_by:                       0
% 7.84/1.49  res_preprocessed:                       76
% 7.84/1.49  prep_upred:                             0
% 7.84/1.49  prep_unflattend:                        36
% 7.84/1.49  smt_new_axioms:                         0
% 7.84/1.49  pred_elim_cands:                        1
% 7.84/1.49  pred_elim:                              0
% 7.84/1.49  pred_elim_cl:                           0
% 7.84/1.49  pred_elim_cycles:                       1
% 7.84/1.49  merged_defs:                            0
% 7.84/1.49  merged_defs_ncl:                        0
% 7.84/1.49  bin_hyper_res:                          0
% 7.84/1.49  prep_cycles:                            3
% 7.84/1.49  pred_elim_time:                         0.004
% 7.84/1.49  splitting_time:                         0.
% 7.84/1.49  sem_filter_time:                        0.
% 7.84/1.49  monotx_time:                            0.
% 7.84/1.49  subtype_inf_time:                       0.
% 7.84/1.49  
% 7.84/1.49  ------ Problem properties
% 7.84/1.49  
% 7.84/1.49  clauses:                                21
% 7.84/1.49  conjectures:                            2
% 7.84/1.49  epr:                                    1
% 7.84/1.49  horn:                                   18
% 7.84/1.49  ground:                                 2
% 7.84/1.49  unary:                                  13
% 7.84/1.49  binary:                                 1
% 7.84/1.49  lits:                                   39
% 7.84/1.49  lits_eq:                                27
% 7.84/1.49  fd_pure:                                0
% 7.84/1.49  fd_pseudo:                              0
% 7.84/1.49  fd_cond:                                0
% 7.84/1.49  fd_pseudo_cond:                         6
% 7.84/1.49  ac_symbols:                             1
% 7.84/1.49  
% 7.84/1.49  ------ Propositional Solver
% 7.84/1.49  
% 7.84/1.49  prop_solver_calls:                      28
% 7.84/1.49  prop_fast_solver_calls:                 602
% 7.84/1.49  smt_solver_calls:                       0
% 7.84/1.49  smt_fast_solver_calls:                  0
% 7.84/1.49  prop_num_of_clauses:                    5660
% 7.84/1.49  prop_preprocess_simplified:             9189
% 7.84/1.49  prop_fo_subsumed:                       0
% 7.84/1.49  prop_solver_time:                       0.
% 7.84/1.49  smt_solver_time:                        0.
% 7.84/1.49  smt_fast_solver_time:                   0.
% 7.84/1.49  prop_fast_solver_time:                  0.
% 7.84/1.49  prop_unsat_core_time:                   0.
% 7.84/1.49  
% 7.84/1.49  ------ QBF
% 7.84/1.49  
% 7.84/1.49  qbf_q_res:                              0
% 7.84/1.49  qbf_num_tautologies:                    0
% 7.84/1.49  qbf_prep_cycles:                        0
% 7.84/1.49  
% 7.84/1.49  ------ BMC1
% 7.84/1.49  
% 7.84/1.49  bmc1_current_bound:                     -1
% 7.84/1.49  bmc1_last_solved_bound:                 -1
% 7.84/1.49  bmc1_unsat_core_size:                   -1
% 7.84/1.49  bmc1_unsat_core_parents_size:           -1
% 7.84/1.49  bmc1_merge_next_fun:                    0
% 7.84/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.84/1.49  
% 7.84/1.49  ------ Instantiation
% 7.84/1.49  
% 7.84/1.49  inst_num_of_clauses:                    1133
% 7.84/1.49  inst_num_in_passive:                    471
% 7.84/1.49  inst_num_in_active:                     288
% 7.84/1.49  inst_num_in_unprocessed:                373
% 7.84/1.49  inst_num_of_loops:                      369
% 7.84/1.49  inst_num_of_learning_restarts:          0
% 7.84/1.49  inst_num_moves_active_passive:          76
% 7.84/1.49  inst_lit_activity:                      0
% 7.84/1.49  inst_lit_activity_moves:                0
% 7.84/1.49  inst_num_tautologies:                   0
% 7.84/1.49  inst_num_prop_implied:                  0
% 7.84/1.49  inst_num_existing_simplified:           0
% 7.84/1.49  inst_num_eq_res_simplified:             0
% 7.84/1.49  inst_num_child_elim:                    0
% 7.84/1.49  inst_num_of_dismatching_blockings:      882
% 7.84/1.49  inst_num_of_non_proper_insts:           1235
% 7.84/1.49  inst_num_of_duplicates:                 0
% 7.84/1.49  inst_inst_num_from_inst_to_res:         0
% 7.84/1.49  inst_dismatching_checking_time:         0.
% 7.84/1.49  
% 7.84/1.49  ------ Resolution
% 7.84/1.49  
% 7.84/1.49  res_num_of_clauses:                     0
% 7.84/1.49  res_num_in_passive:                     0
% 7.84/1.49  res_num_in_active:                      0
% 7.84/1.49  res_num_of_loops:                       79
% 7.84/1.49  res_forward_subset_subsumed:            330
% 7.84/1.49  res_backward_subset_subsumed:           0
% 7.84/1.49  res_forward_subsumed:                   1
% 7.84/1.49  res_backward_subsumed:                  0
% 7.84/1.49  res_forward_subsumption_resolution:     0
% 7.84/1.49  res_backward_subsumption_resolution:    0
% 7.84/1.49  res_clause_to_clause_subsumption:       53577
% 7.84/1.49  res_orphan_elimination:                 0
% 7.84/1.49  res_tautology_del:                      54
% 7.84/1.49  res_num_eq_res_simplified:              0
% 7.84/1.49  res_num_sel_changes:                    0
% 7.84/1.49  res_moves_from_active_to_pass:          0
% 7.84/1.49  
% 7.84/1.49  ------ Superposition
% 7.84/1.49  
% 7.84/1.49  sup_time_total:                         0.
% 7.84/1.49  sup_time_generating:                    0.
% 7.84/1.49  sup_time_sim_full:                      0.
% 7.84/1.49  sup_time_sim_immed:                     0.
% 7.84/1.49  
% 7.84/1.49  sup_num_of_clauses:                     1675
% 7.84/1.49  sup_num_in_active:                      64
% 7.84/1.49  sup_num_in_passive:                     1611
% 7.84/1.49  sup_num_of_loops:                       72
% 7.84/1.49  sup_fw_superposition:                   3809
% 7.84/1.49  sup_bw_superposition:                   1884
% 7.84/1.49  sup_immediate_simplified:               3603
% 7.84/1.49  sup_given_eliminated:                   4
% 7.84/1.49  comparisons_done:                       0
% 7.84/1.49  comparisons_avoided:                    8
% 7.84/1.49  
% 7.84/1.49  ------ Simplifications
% 7.84/1.49  
% 7.84/1.49  
% 7.84/1.49  sim_fw_subset_subsumed:                 0
% 7.84/1.49  sim_bw_subset_subsumed:                 0
% 7.84/1.49  sim_fw_subsumed:                        334
% 7.84/1.49  sim_bw_subsumed:                        31
% 7.84/1.49  sim_fw_subsumption_res:                 0
% 7.84/1.49  sim_bw_subsumption_res:                 0
% 7.84/1.49  sim_tautology_del:                      0
% 7.84/1.49  sim_eq_tautology_del:                   556
% 7.84/1.49  sim_eq_res_simp:                        0
% 7.84/1.49  sim_fw_demodulated:                     2457
% 7.84/1.49  sim_bw_demodulated:                     122
% 7.84/1.49  sim_light_normalised:                   1709
% 7.84/1.49  sim_joinable_taut:                      288
% 7.84/1.49  sim_joinable_simp:                      0
% 7.84/1.49  sim_ac_normalised:                      0
% 7.84/1.49  sim_smt_subsumption:                    0
% 7.84/1.49  
%------------------------------------------------------------------------------
