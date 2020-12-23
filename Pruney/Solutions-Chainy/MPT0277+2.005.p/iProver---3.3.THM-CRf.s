%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:29 EST 2020

% Result     : Theorem 23.27s
% Output     : CNFRefutation 23.27s
% Verified   : 
% Statistics : Number of formulae       :  157 (17585 expanded)
%              Number of clauses        :   82 (3175 expanded)
%              Number of leaves         :   20 (5340 expanded)
%              Depth                    :   34
%              Number of atoms          :  524 (37265 expanded)
%              Number of equality atoms :  449 (35195 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0 )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0 )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 ) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ( ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0 )
        & ( k2_tarski(X1,X2) = X0
          | k1_tarski(X2) = X0
          | k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 ) )
   => ( ( ( k2_tarski(sK2,sK3) != sK1
          & k1_tarski(sK3) != sK1
          & k1_tarski(sK2) != sK1
          & k1_xboole_0 != sK1 )
        | k4_xboole_0(sK1,k2_tarski(sK2,sK3)) != k1_xboole_0 )
      & ( k2_tarski(sK2,sK3) = sK1
        | k1_tarski(sK3) = sK1
        | k1_tarski(sK2) = sK1
        | k1_xboole_0 = sK1
        | k4_xboole_0(sK1,k2_tarski(sK2,sK3)) = k1_xboole_0 ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ( k2_tarski(sK2,sK3) != sK1
        & k1_tarski(sK3) != sK1
        & k1_tarski(sK2) != sK1
        & k1_xboole_0 != sK1 )
      | k4_xboole_0(sK1,k2_tarski(sK2,sK3)) != k1_xboole_0 )
    & ( k2_tarski(sK2,sK3) = sK1
      | k1_tarski(sK3) = sK1
      | k1_tarski(sK2) = sK1
      | k1_xboole_0 = sK1
      | k4_xboole_0(sK1,k2_tarski(sK2,sK3)) = k1_xboole_0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f32])).

fof(f62,plain,
    ( k2_tarski(sK2,sK3) = sK1
    | k1_tarski(sK3) = sK1
    | k1_tarski(sK2) = sK1
    | k1_xboole_0 = sK1
    | k4_xboole_0(sK1,k2_tarski(sK2,sK3)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f67])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f94,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK3) = sK1
    | k2_enumset1(sK3,sK3,sK3,sK3) = sK1
    | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
    | k1_xboole_0 = sK1
    | k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f62,f67,f68,f68,f67])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f34,f38,f38])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f71,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f36,f40])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f26])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X1,X1,X1,X2) = X0
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f52,f67,f68,f68,f67])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

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
    inference(nnf_transformation,[],[f18])).

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
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f42,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f42,f51])).

fof(f99,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f78])).

fof(f100,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f99])).

fof(f66,plain,
    ( k2_tarski(sK2,sK3) != sK1
    | k4_xboole_0(sK1,k2_tarski(sK2,sK3)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK3) != sK1
    | k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f66,f67,f67])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

fof(f85,plain,(
    ! [X0,X1] : k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f57,f68,f67])).

fof(f64,plain,
    ( k1_tarski(sK2) != sK1
    | k4_xboole_0(sK1,k2_tarski(sK2,sK3)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != sK1
    | k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f64,f68,f67])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k2_enumset1(X2,X2,X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f55,f67,f68])).

fof(f103,plain,(
    ! [X2,X1] : r1_tarski(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f81])).

fof(f65,plain,
    ( k1_tarski(sK3) != sK1
    | k4_xboole_0(sK1,k2_tarski(sK2,sK3)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

fof(f91,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != sK1
    | k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f65,f68,f67])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) != k2_enumset1(X0,X0,X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f67,f67])).

fof(f41,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f41,f51])).

fof(f101,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) != k2_enumset1(X0,X0,X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f67,f67])).

fof(f63,plain,
    ( k1_xboole_0 != sK1
    | k4_xboole_0(sK1,k2_tarski(sK2,sK3)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

fof(f93,plain,
    ( k1_xboole_0 != sK1
    | k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f63,f67])).

cnf(c_27,negated_conjecture,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = sK1
    | k2_enumset1(sK2,sK2,sK2,sK3) = sK1
    | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
    | k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) = k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_547,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_965,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_547])).

cnf(c_2253,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = sK1
    | k2_enumset1(sK2,sK2,sK2,sK3) = sK1
    | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
    | sK1 = k1_xboole_0
    | r1_tarski(k4_xboole_0(sK1,k1_xboole_0),k2_enumset1(sK2,sK2,sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_965])).

cnf(c_4,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_967,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_4])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1588,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_967,c_0])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_548,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2,c_4])).

cnf(c_1593,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1588,c_548])).

cnf(c_2259,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = sK1
    | k2_enumset1(sK2,sK2,sK2,sK3) = sK1
    | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
    | sK1 = k1_xboole_0
    | r1_tarski(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2253,c_1593])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_534,plain,
    ( k2_enumset1(X0,X0,X0,X1) = X2
    | k2_enumset1(X1,X1,X1,X1) = X2
    | k2_enumset1(X0,X0,X0,X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2408,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = sK1
    | k2_enumset1(sK2,sK2,sK2,sK3) = sK1
    | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2259,c_534])).

cnf(c_11,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_540,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2411,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK3) = sK1
    | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
    | sK1 = k1_xboole_0
    | r2_hidden(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2408,c_540])).

cnf(c_2417,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = X0
    | k2_enumset1(sK2,sK2,sK2,sK3) = sK1
    | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2408,c_534])).

cnf(c_3736,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,X0)
    | k2_enumset1(sK2,sK2,sK2,sK3) = sK1
    | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
    | k4_xboole_0(sK1,X0) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_547,c_2417])).

cnf(c_3940,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK3) = sK1
    | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
    | k4_xboole_0(sK1,X0) = sK1
    | k4_xboole_0(sK1,X0) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3736,c_2408])).

cnf(c_23,negated_conjecture,
    ( k2_enumset1(sK2,sK2,sK2,sK3) != sK1
    | k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_5291,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK3) != sK1
    | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
    | k4_xboole_0(sK1,X0) = sK1
    | k4_xboole_0(sK1,X0) = k1_xboole_0
    | k4_xboole_0(sK1,sK1) != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3940,c_23])).

cnf(c_1594,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1593,c_967])).

cnf(c_5294,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK3) != sK1
    | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
    | k4_xboole_0(sK1,X0) = sK1
    | k4_xboole_0(sK1,X0) = k1_xboole_0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5291,c_1594])).

cnf(c_5295,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK3) != sK1
    | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
    | k4_xboole_0(sK1,X0) = sK1
    | k4_xboole_0(sK1,X0) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5294])).

cnf(c_5350,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = sK1
    | k4_xboole_0(sK1,X0) = sK1
    | k4_xboole_0(sK1,X0) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5295,c_3940])).

cnf(c_18,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_5398,plain,
    ( k4_xboole_0(sK1,X0) = sK1
    | k4_xboole_0(sK1,X0) = k1_xboole_0
    | k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,X1)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5350,c_18])).

cnf(c_25,negated_conjecture,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != sK1
    | k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_7178,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != sK1
    | k4_xboole_0(sK1,X0) = sK1
    | k4_xboole_0(sK1,X0) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5398,c_25])).

cnf(c_7519,plain,
    ( k4_xboole_0(sK1,X0) = sK1
    | k4_xboole_0(sK1,X0) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7178,c_5350])).

cnf(c_966,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_7548,plain,
    ( k5_xboole_0(X0,k4_xboole_0(sK1,sK1)) = k4_xboole_0(X0,sK1)
    | k4_xboole_0(sK1,X0) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7519,c_966])).

cnf(c_7577,plain,
    ( k4_xboole_0(X0,sK1) = X0
    | k4_xboole_0(sK1,X0) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7548,c_548,c_1594])).

cnf(c_10522,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != sK1
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK1) = k2_enumset1(sK2,sK2,sK2,sK3)
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7577,c_25])).

cnf(c_582,plain,
    ( ~ r1_tarski(sK1,k2_enumset1(sK2,sK2,sK2,sK3))
    | k2_enumset1(sK3,sK3,sK3,sK3) = sK1
    | k2_enumset1(sK2,sK2,sK2,sK3) = sK1
    | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_268,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_932,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_268])).

cnf(c_14,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_537,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2872,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK3) = sK1
    | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
    | sK1 = k1_xboole_0
    | r1_tarski(sK1,k2_enumset1(X0,X0,X0,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2408,c_537])).

cnf(c_2877,plain,
    ( r1_tarski(sK1,k2_enumset1(X0,X0,X0,sK3))
    | k2_enumset1(sK2,sK2,sK2,sK3) = sK1
    | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2872])).

cnf(c_2879,plain,
    ( r1_tarski(sK1,k2_enumset1(sK2,sK2,sK2,sK3))
    | k2_enumset1(sK2,sK2,sK2,sK3) = sK1
    | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
    | sK1 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2877])).

cnf(c_24,negated_conjecture,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != sK1
    | k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_10523,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != sK1
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK1) = k2_enumset1(sK2,sK2,sK2,sK3)
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7577,c_24])).

cnf(c_10524,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK3) != sK1
    | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK1) = k2_enumset1(sK2,sK2,sK2,sK3)
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7577,c_23])).

cnf(c_269,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_678,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_786,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_11573,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_12311,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK1) = k2_enumset1(sK2,sK2,sK2,sK3)
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10522,c_582,c_932,c_2879,c_10523,c_10524,c_11573])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k2_enumset1(X2,X2,X2,X0),X1) != k2_enumset1(X2,X2,X2,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_532,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) != k2_enumset1(X0,X0,X0,X1)
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_13274,plain,
    ( sK1 = k1_xboole_0
    | r2_hidden(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_12311,c_532])).

cnf(c_14000,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK3) = sK1
    | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2411,c_13274])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_49,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_52,plain,
    ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_51,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_53,plain,
    ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_1488,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != sK1
    | sK1 = k2_enumset1(sK2,sK2,sK2,sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_274,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1161,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X3,X3,X4,X2))
    | X0 != X2
    | X1 != k2_enumset1(X3,X3,X4,X2) ),
    inference(instantiation,[status(thm)],[c_274])).

cnf(c_2216,plain,
    ( r2_hidden(X0,sK1)
    | ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2))
    | X0 != sK2
    | sK1 != k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1161])).

cnf(c_2217,plain,
    ( X0 != sK2
    | sK1 != k2_enumset1(sK2,sK2,sK2,sK2)
    | r2_hidden(X0,sK1) = iProver_top
    | r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2216])).

cnf(c_2219,plain,
    ( sK1 != k2_enumset1(sK2,sK2,sK2,sK2)
    | sK2 != sK2
    | r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(sK2,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2217])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) != k2_enumset1(X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_531,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) != k2_enumset1(X0,X0,X0,X1)
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_12333,plain,
    ( sK1 = k1_xboole_0
    | r2_hidden(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_12311,c_531])).

cnf(c_17248,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK3) = sK1
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14000,c_49,c_52,c_53,c_932,c_1488,c_2219,c_2411,c_12333,c_13274])).

cnf(c_12331,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK2,sK2,sK2,sK3))) = k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12311,c_966])).

cnf(c_12354,plain,
    ( k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) = sK1
    | sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12331,c_548,c_1594])).

cnf(c_17269,plain,
    ( k4_xboole_0(sK1,sK1) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17248,c_12354])).

cnf(c_17283,plain,
    ( sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_17269,c_1594])).

cnf(c_26,negated_conjecture,
    ( k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) != k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_73834,plain,
    ( k4_xboole_0(k1_xboole_0,k2_enumset1(sK2,sK2,sK2,sK3)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_17283,c_26])).

cnf(c_73835,plain,
    ( k4_xboole_0(k1_xboole_0,k2_enumset1(sK2,sK2,sK2,sK3)) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_73834])).

cnf(c_73836,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_73835,c_4])).

cnf(c_73837,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_73836])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:36:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.27/3.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.27/3.49  
% 23.27/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.27/3.49  
% 23.27/3.49  ------  iProver source info
% 23.27/3.49  
% 23.27/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.27/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.27/3.49  git: non_committed_changes: false
% 23.27/3.49  git: last_make_outside_of_git: false
% 23.27/3.49  
% 23.27/3.49  ------ 
% 23.27/3.49  
% 23.27/3.49  ------ Input Options
% 23.27/3.49  
% 23.27/3.49  --out_options                           all
% 23.27/3.49  --tptp_safe_out                         true
% 23.27/3.49  --problem_path                          ""
% 23.27/3.49  --include_path                          ""
% 23.27/3.49  --clausifier                            res/vclausify_rel
% 23.27/3.49  --clausifier_options                    ""
% 23.27/3.49  --stdin                                 false
% 23.27/3.49  --stats_out                             all
% 23.27/3.49  
% 23.27/3.49  ------ General Options
% 23.27/3.49  
% 23.27/3.49  --fof                                   false
% 23.27/3.49  --time_out_real                         305.
% 23.27/3.49  --time_out_virtual                      -1.
% 23.27/3.49  --symbol_type_check                     false
% 23.27/3.49  --clausify_out                          false
% 23.27/3.49  --sig_cnt_out                           false
% 23.27/3.49  --trig_cnt_out                          false
% 23.27/3.49  --trig_cnt_out_tolerance                1.
% 23.27/3.49  --trig_cnt_out_sk_spl                   false
% 23.27/3.49  --abstr_cl_out                          false
% 23.27/3.49  
% 23.27/3.49  ------ Global Options
% 23.27/3.49  
% 23.27/3.49  --schedule                              default
% 23.27/3.49  --add_important_lit                     false
% 23.27/3.49  --prop_solver_per_cl                    1000
% 23.27/3.49  --min_unsat_core                        false
% 23.27/3.49  --soft_assumptions                      false
% 23.27/3.49  --soft_lemma_size                       3
% 23.27/3.49  --prop_impl_unit_size                   0
% 23.27/3.49  --prop_impl_unit                        []
% 23.27/3.49  --share_sel_clauses                     true
% 23.27/3.49  --reset_solvers                         false
% 23.27/3.49  --bc_imp_inh                            [conj_cone]
% 23.27/3.49  --conj_cone_tolerance                   3.
% 23.27/3.49  --extra_neg_conj                        none
% 23.27/3.49  --large_theory_mode                     true
% 23.27/3.49  --prolific_symb_bound                   200
% 23.27/3.49  --lt_threshold                          2000
% 23.27/3.49  --clause_weak_htbl                      true
% 23.27/3.49  --gc_record_bc_elim                     false
% 23.27/3.49  
% 23.27/3.49  ------ Preprocessing Options
% 23.27/3.49  
% 23.27/3.49  --preprocessing_flag                    true
% 23.27/3.49  --time_out_prep_mult                    0.1
% 23.27/3.49  --splitting_mode                        input
% 23.27/3.49  --splitting_grd                         true
% 23.27/3.49  --splitting_cvd                         false
% 23.27/3.49  --splitting_cvd_svl                     false
% 23.27/3.49  --splitting_nvd                         32
% 23.27/3.49  --sub_typing                            true
% 23.27/3.49  --prep_gs_sim                           true
% 23.27/3.49  --prep_unflatten                        true
% 23.27/3.49  --prep_res_sim                          true
% 23.27/3.49  --prep_upred                            true
% 23.27/3.49  --prep_sem_filter                       exhaustive
% 23.27/3.49  --prep_sem_filter_out                   false
% 23.27/3.49  --pred_elim                             true
% 23.27/3.49  --res_sim_input                         true
% 23.27/3.49  --eq_ax_congr_red                       true
% 23.27/3.49  --pure_diseq_elim                       true
% 23.27/3.49  --brand_transform                       false
% 23.27/3.49  --non_eq_to_eq                          false
% 23.27/3.49  --prep_def_merge                        true
% 23.27/3.49  --prep_def_merge_prop_impl              false
% 23.27/3.49  --prep_def_merge_mbd                    true
% 23.27/3.49  --prep_def_merge_tr_red                 false
% 23.27/3.49  --prep_def_merge_tr_cl                  false
% 23.27/3.49  --smt_preprocessing                     true
% 23.27/3.49  --smt_ac_axioms                         fast
% 23.27/3.49  --preprocessed_out                      false
% 23.27/3.49  --preprocessed_stats                    false
% 23.27/3.49  
% 23.27/3.49  ------ Abstraction refinement Options
% 23.27/3.49  
% 23.27/3.49  --abstr_ref                             []
% 23.27/3.49  --abstr_ref_prep                        false
% 23.27/3.49  --abstr_ref_until_sat                   false
% 23.27/3.49  --abstr_ref_sig_restrict                funpre
% 23.27/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.27/3.49  --abstr_ref_under                       []
% 23.27/3.49  
% 23.27/3.49  ------ SAT Options
% 23.27/3.49  
% 23.27/3.49  --sat_mode                              false
% 23.27/3.49  --sat_fm_restart_options                ""
% 23.27/3.49  --sat_gr_def                            false
% 23.27/3.49  --sat_epr_types                         true
% 23.27/3.49  --sat_non_cyclic_types                  false
% 23.27/3.49  --sat_finite_models                     false
% 23.27/3.49  --sat_fm_lemmas                         false
% 23.27/3.49  --sat_fm_prep                           false
% 23.27/3.49  --sat_fm_uc_incr                        true
% 23.27/3.49  --sat_out_model                         small
% 23.27/3.49  --sat_out_clauses                       false
% 23.27/3.49  
% 23.27/3.49  ------ QBF Options
% 23.27/3.49  
% 23.27/3.49  --qbf_mode                              false
% 23.27/3.49  --qbf_elim_univ                         false
% 23.27/3.49  --qbf_dom_inst                          none
% 23.27/3.49  --qbf_dom_pre_inst                      false
% 23.27/3.49  --qbf_sk_in                             false
% 23.27/3.49  --qbf_pred_elim                         true
% 23.27/3.49  --qbf_split                             512
% 23.27/3.49  
% 23.27/3.49  ------ BMC1 Options
% 23.27/3.49  
% 23.27/3.49  --bmc1_incremental                      false
% 23.27/3.49  --bmc1_axioms                           reachable_all
% 23.27/3.49  --bmc1_min_bound                        0
% 23.27/3.49  --bmc1_max_bound                        -1
% 23.27/3.49  --bmc1_max_bound_default                -1
% 23.27/3.49  --bmc1_symbol_reachability              true
% 23.27/3.49  --bmc1_property_lemmas                  false
% 23.27/3.49  --bmc1_k_induction                      false
% 23.27/3.49  --bmc1_non_equiv_states                 false
% 23.27/3.49  --bmc1_deadlock                         false
% 23.27/3.49  --bmc1_ucm                              false
% 23.27/3.49  --bmc1_add_unsat_core                   none
% 23.27/3.49  --bmc1_unsat_core_children              false
% 23.27/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.27/3.49  --bmc1_out_stat                         full
% 23.27/3.49  --bmc1_ground_init                      false
% 23.27/3.49  --bmc1_pre_inst_next_state              false
% 23.27/3.49  --bmc1_pre_inst_state                   false
% 23.27/3.49  --bmc1_pre_inst_reach_state             false
% 23.27/3.49  --bmc1_out_unsat_core                   false
% 23.27/3.49  --bmc1_aig_witness_out                  false
% 23.27/3.49  --bmc1_verbose                          false
% 23.27/3.49  --bmc1_dump_clauses_tptp                false
% 23.27/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.27/3.49  --bmc1_dump_file                        -
% 23.27/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.27/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.27/3.49  --bmc1_ucm_extend_mode                  1
% 23.27/3.49  --bmc1_ucm_init_mode                    2
% 23.27/3.49  --bmc1_ucm_cone_mode                    none
% 23.27/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.27/3.49  --bmc1_ucm_relax_model                  4
% 23.27/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.27/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.27/3.49  --bmc1_ucm_layered_model                none
% 23.27/3.49  --bmc1_ucm_max_lemma_size               10
% 23.27/3.49  
% 23.27/3.49  ------ AIG Options
% 23.27/3.49  
% 23.27/3.49  --aig_mode                              false
% 23.27/3.49  
% 23.27/3.49  ------ Instantiation Options
% 23.27/3.49  
% 23.27/3.49  --instantiation_flag                    true
% 23.27/3.49  --inst_sos_flag                         true
% 23.27/3.49  --inst_sos_phase                        true
% 23.27/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.27/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.27/3.49  --inst_lit_sel_side                     num_symb
% 23.27/3.49  --inst_solver_per_active                1400
% 23.27/3.49  --inst_solver_calls_frac                1.
% 23.27/3.49  --inst_passive_queue_type               priority_queues
% 23.27/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.27/3.49  --inst_passive_queues_freq              [25;2]
% 23.27/3.49  --inst_dismatching                      true
% 23.27/3.49  --inst_eager_unprocessed_to_passive     true
% 23.27/3.49  --inst_prop_sim_given                   true
% 23.27/3.49  --inst_prop_sim_new                     false
% 23.27/3.49  --inst_subs_new                         false
% 23.27/3.49  --inst_eq_res_simp                      false
% 23.27/3.49  --inst_subs_given                       false
% 23.27/3.49  --inst_orphan_elimination               true
% 23.27/3.49  --inst_learning_loop_flag               true
% 23.27/3.49  --inst_learning_start                   3000
% 23.27/3.49  --inst_learning_factor                  2
% 23.27/3.49  --inst_start_prop_sim_after_learn       3
% 23.27/3.49  --inst_sel_renew                        solver
% 23.27/3.49  --inst_lit_activity_flag                true
% 23.27/3.49  --inst_restr_to_given                   false
% 23.27/3.49  --inst_activity_threshold               500
% 23.27/3.49  --inst_out_proof                        true
% 23.27/3.49  
% 23.27/3.49  ------ Resolution Options
% 23.27/3.49  
% 23.27/3.49  --resolution_flag                       true
% 23.27/3.49  --res_lit_sel                           adaptive
% 23.27/3.49  --res_lit_sel_side                      none
% 23.27/3.49  --res_ordering                          kbo
% 23.27/3.49  --res_to_prop_solver                    active
% 23.27/3.49  --res_prop_simpl_new                    false
% 23.27/3.49  --res_prop_simpl_given                  true
% 23.27/3.49  --res_passive_queue_type                priority_queues
% 23.27/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.27/3.49  --res_passive_queues_freq               [15;5]
% 23.27/3.49  --res_forward_subs                      full
% 23.27/3.49  --res_backward_subs                     full
% 23.27/3.49  --res_forward_subs_resolution           true
% 23.27/3.49  --res_backward_subs_resolution          true
% 23.27/3.49  --res_orphan_elimination                true
% 23.27/3.49  --res_time_limit                        2.
% 23.27/3.49  --res_out_proof                         true
% 23.27/3.49  
% 23.27/3.49  ------ Superposition Options
% 23.27/3.49  
% 23.27/3.49  --superposition_flag                    true
% 23.27/3.49  --sup_passive_queue_type                priority_queues
% 23.27/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.27/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.27/3.49  --demod_completeness_check              fast
% 23.27/3.49  --demod_use_ground                      true
% 23.27/3.49  --sup_to_prop_solver                    passive
% 23.27/3.49  --sup_prop_simpl_new                    true
% 23.27/3.49  --sup_prop_simpl_given                  true
% 23.27/3.49  --sup_fun_splitting                     true
% 23.27/3.49  --sup_smt_interval                      50000
% 23.27/3.49  
% 23.27/3.49  ------ Superposition Simplification Setup
% 23.27/3.49  
% 23.27/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.27/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.27/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.27/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.27/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.27/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.27/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.27/3.49  --sup_immed_triv                        [TrivRules]
% 23.27/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.27/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.27/3.49  --sup_immed_bw_main                     []
% 23.27/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.27/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.27/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.27/3.49  --sup_input_bw                          []
% 23.27/3.49  
% 23.27/3.49  ------ Combination Options
% 23.27/3.49  
% 23.27/3.49  --comb_res_mult                         3
% 23.27/3.49  --comb_sup_mult                         2
% 23.27/3.49  --comb_inst_mult                        10
% 23.27/3.49  
% 23.27/3.49  ------ Debug Options
% 23.27/3.49  
% 23.27/3.49  --dbg_backtrace                         false
% 23.27/3.49  --dbg_dump_prop_clauses                 false
% 23.27/3.49  --dbg_dump_prop_clauses_file            -
% 23.27/3.49  --dbg_out_stat                          false
% 23.27/3.49  ------ Parsing...
% 23.27/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.27/3.49  
% 23.27/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.27/3.49  
% 23.27/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.27/3.49  
% 23.27/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.27/3.49  ------ Proving...
% 23.27/3.49  ------ Problem Properties 
% 23.27/3.49  
% 23.27/3.49  
% 23.27/3.49  clauses                                 28
% 23.27/3.49  conjectures                             5
% 23.27/3.49  EPR                                     0
% 23.27/3.49  Horn                                    22
% 23.27/3.49  unary                                   13
% 23.27/3.49  binary                                  7
% 23.27/3.49  lits                                    58
% 23.27/3.49  lits eq                                 40
% 23.27/3.49  fd_pure                                 0
% 23.27/3.49  fd_pseudo                               0
% 23.27/3.49  fd_cond                                 0
% 23.27/3.49  fd_pseudo_cond                          5
% 23.27/3.49  AC symbols                              0
% 23.27/3.49  
% 23.27/3.49  ------ Schedule dynamic 5 is on 
% 23.27/3.49  
% 23.27/3.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.27/3.49  
% 23.27/3.49  
% 23.27/3.49  ------ 
% 23.27/3.49  Current options:
% 23.27/3.49  ------ 
% 23.27/3.49  
% 23.27/3.49  ------ Input Options
% 23.27/3.49  
% 23.27/3.49  --out_options                           all
% 23.27/3.49  --tptp_safe_out                         true
% 23.27/3.49  --problem_path                          ""
% 23.27/3.49  --include_path                          ""
% 23.27/3.49  --clausifier                            res/vclausify_rel
% 23.27/3.49  --clausifier_options                    ""
% 23.27/3.49  --stdin                                 false
% 23.27/3.49  --stats_out                             all
% 23.27/3.49  
% 23.27/3.49  ------ General Options
% 23.27/3.49  
% 23.27/3.49  --fof                                   false
% 23.27/3.49  --time_out_real                         305.
% 23.27/3.49  --time_out_virtual                      -1.
% 23.27/3.49  --symbol_type_check                     false
% 23.27/3.49  --clausify_out                          false
% 23.27/3.49  --sig_cnt_out                           false
% 23.27/3.49  --trig_cnt_out                          false
% 23.27/3.49  --trig_cnt_out_tolerance                1.
% 23.27/3.49  --trig_cnt_out_sk_spl                   false
% 23.27/3.49  --abstr_cl_out                          false
% 23.27/3.49  
% 23.27/3.49  ------ Global Options
% 23.27/3.49  
% 23.27/3.49  --schedule                              default
% 23.27/3.49  --add_important_lit                     false
% 23.27/3.49  --prop_solver_per_cl                    1000
% 23.27/3.49  --min_unsat_core                        false
% 23.27/3.49  --soft_assumptions                      false
% 23.27/3.49  --soft_lemma_size                       3
% 23.27/3.49  --prop_impl_unit_size                   0
% 23.27/3.49  --prop_impl_unit                        []
% 23.27/3.49  --share_sel_clauses                     true
% 23.27/3.49  --reset_solvers                         false
% 23.27/3.49  --bc_imp_inh                            [conj_cone]
% 23.27/3.49  --conj_cone_tolerance                   3.
% 23.27/3.49  --extra_neg_conj                        none
% 23.27/3.49  --large_theory_mode                     true
% 23.27/3.49  --prolific_symb_bound                   200
% 23.27/3.49  --lt_threshold                          2000
% 23.27/3.49  --clause_weak_htbl                      true
% 23.27/3.49  --gc_record_bc_elim                     false
% 23.27/3.49  
% 23.27/3.49  ------ Preprocessing Options
% 23.27/3.49  
% 23.27/3.49  --preprocessing_flag                    true
% 23.27/3.49  --time_out_prep_mult                    0.1
% 23.27/3.49  --splitting_mode                        input
% 23.27/3.49  --splitting_grd                         true
% 23.27/3.49  --splitting_cvd                         false
% 23.27/3.49  --splitting_cvd_svl                     false
% 23.27/3.49  --splitting_nvd                         32
% 23.27/3.49  --sub_typing                            true
% 23.27/3.49  --prep_gs_sim                           true
% 23.27/3.49  --prep_unflatten                        true
% 23.27/3.49  --prep_res_sim                          true
% 23.27/3.49  --prep_upred                            true
% 23.27/3.49  --prep_sem_filter                       exhaustive
% 23.27/3.49  --prep_sem_filter_out                   false
% 23.27/3.49  --pred_elim                             true
% 23.27/3.49  --res_sim_input                         true
% 23.27/3.49  --eq_ax_congr_red                       true
% 23.27/3.49  --pure_diseq_elim                       true
% 23.27/3.49  --brand_transform                       false
% 23.27/3.49  --non_eq_to_eq                          false
% 23.27/3.49  --prep_def_merge                        true
% 23.27/3.49  --prep_def_merge_prop_impl              false
% 23.27/3.49  --prep_def_merge_mbd                    true
% 23.27/3.49  --prep_def_merge_tr_red                 false
% 23.27/3.49  --prep_def_merge_tr_cl                  false
% 23.27/3.49  --smt_preprocessing                     true
% 23.27/3.49  --smt_ac_axioms                         fast
% 23.27/3.49  --preprocessed_out                      false
% 23.27/3.49  --preprocessed_stats                    false
% 23.27/3.49  
% 23.27/3.49  ------ Abstraction refinement Options
% 23.27/3.49  
% 23.27/3.49  --abstr_ref                             []
% 23.27/3.49  --abstr_ref_prep                        false
% 23.27/3.49  --abstr_ref_until_sat                   false
% 23.27/3.49  --abstr_ref_sig_restrict                funpre
% 23.27/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.27/3.49  --abstr_ref_under                       []
% 23.27/3.49  
% 23.27/3.49  ------ SAT Options
% 23.27/3.49  
% 23.27/3.49  --sat_mode                              false
% 23.27/3.49  --sat_fm_restart_options                ""
% 23.27/3.49  --sat_gr_def                            false
% 23.27/3.49  --sat_epr_types                         true
% 23.27/3.49  --sat_non_cyclic_types                  false
% 23.27/3.49  --sat_finite_models                     false
% 23.27/3.49  --sat_fm_lemmas                         false
% 23.27/3.49  --sat_fm_prep                           false
% 23.27/3.49  --sat_fm_uc_incr                        true
% 23.27/3.49  --sat_out_model                         small
% 23.27/3.49  --sat_out_clauses                       false
% 23.27/3.49  
% 23.27/3.49  ------ QBF Options
% 23.27/3.49  
% 23.27/3.49  --qbf_mode                              false
% 23.27/3.49  --qbf_elim_univ                         false
% 23.27/3.49  --qbf_dom_inst                          none
% 23.27/3.49  --qbf_dom_pre_inst                      false
% 23.27/3.49  --qbf_sk_in                             false
% 23.27/3.49  --qbf_pred_elim                         true
% 23.27/3.49  --qbf_split                             512
% 23.27/3.49  
% 23.27/3.49  ------ BMC1 Options
% 23.27/3.49  
% 23.27/3.49  --bmc1_incremental                      false
% 23.27/3.49  --bmc1_axioms                           reachable_all
% 23.27/3.49  --bmc1_min_bound                        0
% 23.27/3.49  --bmc1_max_bound                        -1
% 23.27/3.49  --bmc1_max_bound_default                -1
% 23.27/3.49  --bmc1_symbol_reachability              true
% 23.27/3.49  --bmc1_property_lemmas                  false
% 23.27/3.49  --bmc1_k_induction                      false
% 23.27/3.49  --bmc1_non_equiv_states                 false
% 23.27/3.49  --bmc1_deadlock                         false
% 23.27/3.49  --bmc1_ucm                              false
% 23.27/3.49  --bmc1_add_unsat_core                   none
% 23.27/3.49  --bmc1_unsat_core_children              false
% 23.27/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.27/3.49  --bmc1_out_stat                         full
% 23.27/3.49  --bmc1_ground_init                      false
% 23.27/3.49  --bmc1_pre_inst_next_state              false
% 23.27/3.49  --bmc1_pre_inst_state                   false
% 23.27/3.49  --bmc1_pre_inst_reach_state             false
% 23.27/3.49  --bmc1_out_unsat_core                   false
% 23.27/3.49  --bmc1_aig_witness_out                  false
% 23.27/3.49  --bmc1_verbose                          false
% 23.27/3.49  --bmc1_dump_clauses_tptp                false
% 23.27/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.27/3.49  --bmc1_dump_file                        -
% 23.27/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.27/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.27/3.49  --bmc1_ucm_extend_mode                  1
% 23.27/3.49  --bmc1_ucm_init_mode                    2
% 23.27/3.49  --bmc1_ucm_cone_mode                    none
% 23.27/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.27/3.49  --bmc1_ucm_relax_model                  4
% 23.27/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.27/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.27/3.49  --bmc1_ucm_layered_model                none
% 23.27/3.49  --bmc1_ucm_max_lemma_size               10
% 23.27/3.49  
% 23.27/3.49  ------ AIG Options
% 23.27/3.49  
% 23.27/3.49  --aig_mode                              false
% 23.27/3.49  
% 23.27/3.49  ------ Instantiation Options
% 23.27/3.49  
% 23.27/3.49  --instantiation_flag                    true
% 23.27/3.49  --inst_sos_flag                         true
% 23.27/3.49  --inst_sos_phase                        true
% 23.27/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.27/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.27/3.49  --inst_lit_sel_side                     none
% 23.27/3.49  --inst_solver_per_active                1400
% 23.27/3.49  --inst_solver_calls_frac                1.
% 23.27/3.49  --inst_passive_queue_type               priority_queues
% 23.27/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.27/3.49  --inst_passive_queues_freq              [25;2]
% 23.27/3.49  --inst_dismatching                      true
% 23.27/3.49  --inst_eager_unprocessed_to_passive     true
% 23.27/3.49  --inst_prop_sim_given                   true
% 23.27/3.49  --inst_prop_sim_new                     false
% 23.27/3.49  --inst_subs_new                         false
% 23.27/3.49  --inst_eq_res_simp                      false
% 23.27/3.49  --inst_subs_given                       false
% 23.27/3.49  --inst_orphan_elimination               true
% 23.27/3.49  --inst_learning_loop_flag               true
% 23.27/3.49  --inst_learning_start                   3000
% 23.27/3.49  --inst_learning_factor                  2
% 23.27/3.49  --inst_start_prop_sim_after_learn       3
% 23.27/3.49  --inst_sel_renew                        solver
% 23.27/3.49  --inst_lit_activity_flag                true
% 23.27/3.49  --inst_restr_to_given                   false
% 23.27/3.49  --inst_activity_threshold               500
% 23.27/3.49  --inst_out_proof                        true
% 23.27/3.49  
% 23.27/3.49  ------ Resolution Options
% 23.27/3.49  
% 23.27/3.49  --resolution_flag                       false
% 23.27/3.49  --res_lit_sel                           adaptive
% 23.27/3.49  --res_lit_sel_side                      none
% 23.27/3.49  --res_ordering                          kbo
% 23.27/3.49  --res_to_prop_solver                    active
% 23.27/3.49  --res_prop_simpl_new                    false
% 23.27/3.49  --res_prop_simpl_given                  true
% 23.27/3.49  --res_passive_queue_type                priority_queues
% 23.27/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.27/3.49  --res_passive_queues_freq               [15;5]
% 23.27/3.49  --res_forward_subs                      full
% 23.27/3.49  --res_backward_subs                     full
% 23.27/3.49  --res_forward_subs_resolution           true
% 23.27/3.49  --res_backward_subs_resolution          true
% 23.27/3.49  --res_orphan_elimination                true
% 23.27/3.49  --res_time_limit                        2.
% 23.27/3.49  --res_out_proof                         true
% 23.27/3.49  
% 23.27/3.49  ------ Superposition Options
% 23.27/3.49  
% 23.27/3.49  --superposition_flag                    true
% 23.27/3.49  --sup_passive_queue_type                priority_queues
% 23.27/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.27/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.27/3.49  --demod_completeness_check              fast
% 23.27/3.49  --demod_use_ground                      true
% 23.27/3.49  --sup_to_prop_solver                    passive
% 23.27/3.49  --sup_prop_simpl_new                    true
% 23.27/3.49  --sup_prop_simpl_given                  true
% 23.27/3.49  --sup_fun_splitting                     true
% 23.27/3.49  --sup_smt_interval                      50000
% 23.27/3.49  
% 23.27/3.49  ------ Superposition Simplification Setup
% 23.27/3.49  
% 23.27/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.27/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.27/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.27/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.27/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.27/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.27/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.27/3.49  --sup_immed_triv                        [TrivRules]
% 23.27/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.27/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.27/3.49  --sup_immed_bw_main                     []
% 23.27/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.27/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.27/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.27/3.49  --sup_input_bw                          []
% 23.27/3.49  
% 23.27/3.49  ------ Combination Options
% 23.27/3.49  
% 23.27/3.49  --comb_res_mult                         3
% 23.27/3.49  --comb_sup_mult                         2
% 23.27/3.49  --comb_inst_mult                        10
% 23.27/3.49  
% 23.27/3.49  ------ Debug Options
% 23.27/3.49  
% 23.27/3.49  --dbg_backtrace                         false
% 23.27/3.49  --dbg_dump_prop_clauses                 false
% 23.27/3.49  --dbg_dump_prop_clauses_file            -
% 23.27/3.49  --dbg_out_stat                          false
% 23.27/3.49  
% 23.27/3.49  
% 23.27/3.49  
% 23.27/3.49  
% 23.27/3.49  ------ Proving...
% 23.27/3.49  
% 23.27/3.49  
% 23.27/3.49  % SZS status Theorem for theBenchmark.p
% 23.27/3.49  
% 23.27/3.49   Resolution empty clause
% 23.27/3.49  
% 23.27/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.27/3.49  
% 23.27/3.49  fof(f16,conjecture,(
% 23.27/3.49    ! [X0,X1,X2] : (k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f17,negated_conjecture,(
% 23.27/3.49    ~! [X0,X1,X2] : (k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 23.27/3.49    inference(negated_conjecture,[],[f16])).
% 23.27/3.49  
% 23.27/3.49  fof(f20,plain,(
% 23.27/3.49    ? [X0,X1,X2] : (k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0 <~> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 23.27/3.49    inference(ennf_transformation,[],[f17])).
% 23.27/3.49  
% 23.27/3.49  fof(f30,plain,(
% 23.27/3.49    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0))),
% 23.27/3.49    inference(nnf_transformation,[],[f20])).
% 23.27/3.49  
% 23.27/3.49  fof(f31,plain,(
% 23.27/3.49    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0))),
% 23.27/3.49    inference(flattening,[],[f30])).
% 23.27/3.49  
% 23.27/3.49  fof(f32,plain,(
% 23.27/3.49    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k4_xboole_0(X0,k2_tarski(X1,X2)) != k1_xboole_0) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k4_xboole_0(X0,k2_tarski(X1,X2)) = k1_xboole_0)) => (((k2_tarski(sK2,sK3) != sK1 & k1_tarski(sK3) != sK1 & k1_tarski(sK2) != sK1 & k1_xboole_0 != sK1) | k4_xboole_0(sK1,k2_tarski(sK2,sK3)) != k1_xboole_0) & (k2_tarski(sK2,sK3) = sK1 | k1_tarski(sK3) = sK1 | k1_tarski(sK2) = sK1 | k1_xboole_0 = sK1 | k4_xboole_0(sK1,k2_tarski(sK2,sK3)) = k1_xboole_0))),
% 23.27/3.49    introduced(choice_axiom,[])).
% 23.27/3.49  
% 23.27/3.49  fof(f33,plain,(
% 23.27/3.49    ((k2_tarski(sK2,sK3) != sK1 & k1_tarski(sK3) != sK1 & k1_tarski(sK2) != sK1 & k1_xboole_0 != sK1) | k4_xboole_0(sK1,k2_tarski(sK2,sK3)) != k1_xboole_0) & (k2_tarski(sK2,sK3) = sK1 | k1_tarski(sK3) = sK1 | k1_tarski(sK2) = sK1 | k1_xboole_0 = sK1 | k4_xboole_0(sK1,k2_tarski(sK2,sK3)) = k1_xboole_0)),
% 23.27/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f32])).
% 23.27/3.49  
% 23.27/3.49  fof(f62,plain,(
% 23.27/3.49    k2_tarski(sK2,sK3) = sK1 | k1_tarski(sK3) = sK1 | k1_tarski(sK2) = sK1 | k1_xboole_0 = sK1 | k4_xboole_0(sK1,k2_tarski(sK2,sK3)) = k1_xboole_0),
% 23.27/3.49    inference(cnf_transformation,[],[f33])).
% 23.27/3.49  
% 23.27/3.49  fof(f9,axiom,(
% 23.27/3.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f49,plain,(
% 23.27/3.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f9])).
% 23.27/3.49  
% 23.27/3.49  fof(f68,plain,(
% 23.27/3.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 23.27/3.49    inference(definition_unfolding,[],[f49,f67])).
% 23.27/3.49  
% 23.27/3.49  fof(f10,axiom,(
% 23.27/3.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f50,plain,(
% 23.27/3.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f10])).
% 23.27/3.49  
% 23.27/3.49  fof(f11,axiom,(
% 23.27/3.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f51,plain,(
% 23.27/3.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f11])).
% 23.27/3.49  
% 23.27/3.49  fof(f67,plain,(
% 23.27/3.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 23.27/3.49    inference(definition_unfolding,[],[f50,f51])).
% 23.27/3.49  
% 23.27/3.49  fof(f94,plain,(
% 23.27/3.49    k2_enumset1(sK2,sK2,sK2,sK3) = sK1 | k2_enumset1(sK3,sK3,sK3,sK3) = sK1 | k2_enumset1(sK2,sK2,sK2,sK2) = sK1 | k1_xboole_0 = sK1 | k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) = k1_xboole_0),
% 23.27/3.49    inference(definition_unfolding,[],[f62,f67,f68,f68,f67])).
% 23.27/3.49  
% 23.27/3.49  fof(f1,axiom,(
% 23.27/3.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f34,plain,(
% 23.27/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f1])).
% 23.27/3.49  
% 23.27/3.49  fof(f5,axiom,(
% 23.27/3.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f38,plain,(
% 23.27/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 23.27/3.49    inference(cnf_transformation,[],[f5])).
% 23.27/3.49  
% 23.27/3.49  fof(f70,plain,(
% 23.27/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 23.27/3.49    inference(definition_unfolding,[],[f34,f38,f38])).
% 23.27/3.49  
% 23.27/3.49  fof(f4,axiom,(
% 23.27/3.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f37,plain,(
% 23.27/3.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f4])).
% 23.27/3.49  
% 23.27/3.49  fof(f6,axiom,(
% 23.27/3.49    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f39,plain,(
% 23.27/3.49    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 23.27/3.49    inference(cnf_transformation,[],[f6])).
% 23.27/3.49  
% 23.27/3.49  fof(f2,axiom,(
% 23.27/3.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f35,plain,(
% 23.27/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 23.27/3.49    inference(cnf_transformation,[],[f2])).
% 23.27/3.49  
% 23.27/3.49  fof(f69,plain,(
% 23.27/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 23.27/3.49    inference(definition_unfolding,[],[f35,f38])).
% 23.27/3.49  
% 23.27/3.49  fof(f3,axiom,(
% 23.27/3.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f36,plain,(
% 23.27/3.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.27/3.49    inference(cnf_transformation,[],[f3])).
% 23.27/3.49  
% 23.27/3.49  fof(f7,axiom,(
% 23.27/3.49    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f40,plain,(
% 23.27/3.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f7])).
% 23.27/3.49  
% 23.27/3.49  fof(f71,plain,(
% 23.27/3.49    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 23.27/3.49    inference(definition_unfolding,[],[f36,f40])).
% 23.27/3.49  
% 23.27/3.49  fof(f12,axiom,(
% 23.27/3.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f19,plain,(
% 23.27/3.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 23.27/3.49    inference(ennf_transformation,[],[f12])).
% 23.27/3.49  
% 23.27/3.49  fof(f26,plain,(
% 23.27/3.49    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 23.27/3.49    inference(nnf_transformation,[],[f19])).
% 23.27/3.49  
% 23.27/3.49  fof(f27,plain,(
% 23.27/3.49    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 23.27/3.49    inference(flattening,[],[f26])).
% 23.27/3.49  
% 23.27/3.49  fof(f52,plain,(
% 23.27/3.49    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 23.27/3.49    inference(cnf_transformation,[],[f27])).
% 23.27/3.49  
% 23.27/3.49  fof(f84,plain,(
% 23.27/3.49    ( ! [X2,X0,X1] : (k2_enumset1(X1,X1,X1,X2) = X0 | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))) )),
% 23.27/3.49    inference(definition_unfolding,[],[f52,f67,f68,f68,f67])).
% 23.27/3.49  
% 23.27/3.49  fof(f8,axiom,(
% 23.27/3.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f18,plain,(
% 23.27/3.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 23.27/3.49    inference(ennf_transformation,[],[f8])).
% 23.27/3.49  
% 23.27/3.49  fof(f21,plain,(
% 23.27/3.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.27/3.49    inference(nnf_transformation,[],[f18])).
% 23.27/3.49  
% 23.27/3.49  fof(f22,plain,(
% 23.27/3.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.27/3.49    inference(flattening,[],[f21])).
% 23.27/3.49  
% 23.27/3.49  fof(f23,plain,(
% 23.27/3.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.27/3.49    inference(rectify,[],[f22])).
% 23.27/3.49  
% 23.27/3.49  fof(f24,plain,(
% 23.27/3.49    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 23.27/3.49    introduced(choice_axiom,[])).
% 23.27/3.49  
% 23.27/3.49  fof(f25,plain,(
% 23.27/3.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.27/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 23.27/3.49  
% 23.27/3.49  fof(f42,plain,(
% 23.27/3.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 23.27/3.49    inference(cnf_transformation,[],[f25])).
% 23.27/3.49  
% 23.27/3.49  fof(f78,plain,(
% 23.27/3.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 23.27/3.49    inference(definition_unfolding,[],[f42,f51])).
% 23.27/3.49  
% 23.27/3.49  fof(f99,plain,(
% 23.27/3.49    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 23.27/3.49    inference(equality_resolution,[],[f78])).
% 23.27/3.49  
% 23.27/3.49  fof(f100,plain,(
% 23.27/3.49    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 23.27/3.49    inference(equality_resolution,[],[f99])).
% 23.27/3.49  
% 23.27/3.49  fof(f66,plain,(
% 23.27/3.49    k2_tarski(sK2,sK3) != sK1 | k4_xboole_0(sK1,k2_tarski(sK2,sK3)) != k1_xboole_0),
% 23.27/3.49    inference(cnf_transformation,[],[f33])).
% 23.27/3.49  
% 23.27/3.49  fof(f90,plain,(
% 23.27/3.49    k2_enumset1(sK2,sK2,sK2,sK3) != sK1 | k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) != k1_xboole_0),
% 23.27/3.49    inference(definition_unfolding,[],[f66,f67,f67])).
% 23.27/3.49  
% 23.27/3.49  fof(f13,axiom,(
% 23.27/3.49    ! [X0,X1] : k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_xboole_0),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f57,plain,(
% 23.27/3.49    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_xboole_0) )),
% 23.27/3.49    inference(cnf_transformation,[],[f13])).
% 23.27/3.49  
% 23.27/3.49  fof(f85,plain,(
% 23.27/3.49    ( ! [X0,X1] : (k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0) )),
% 23.27/3.49    inference(definition_unfolding,[],[f57,f68,f67])).
% 23.27/3.49  
% 23.27/3.49  fof(f64,plain,(
% 23.27/3.49    k1_tarski(sK2) != sK1 | k4_xboole_0(sK1,k2_tarski(sK2,sK3)) != k1_xboole_0),
% 23.27/3.49    inference(cnf_transformation,[],[f33])).
% 23.27/3.49  
% 23.27/3.49  fof(f92,plain,(
% 23.27/3.49    k2_enumset1(sK2,sK2,sK2,sK2) != sK1 | k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) != k1_xboole_0),
% 23.27/3.49    inference(definition_unfolding,[],[f64,f68,f67])).
% 23.27/3.49  
% 23.27/3.49  fof(f55,plain,(
% 23.27/3.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 23.27/3.49    inference(cnf_transformation,[],[f27])).
% 23.27/3.49  
% 23.27/3.49  fof(f81,plain,(
% 23.27/3.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k2_enumset1(X2,X2,X2,X2) != X0) )),
% 23.27/3.49    inference(definition_unfolding,[],[f55,f67,f68])).
% 23.27/3.49  
% 23.27/3.49  fof(f103,plain,(
% 23.27/3.49    ( ! [X2,X1] : (r1_tarski(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X1,X1,X1,X2))) )),
% 23.27/3.49    inference(equality_resolution,[],[f81])).
% 23.27/3.49  
% 23.27/3.49  fof(f65,plain,(
% 23.27/3.49    k1_tarski(sK3) != sK1 | k4_xboole_0(sK1,k2_tarski(sK2,sK3)) != k1_xboole_0),
% 23.27/3.49    inference(cnf_transformation,[],[f33])).
% 23.27/3.49  
% 23.27/3.49  fof(f91,plain,(
% 23.27/3.49    k2_enumset1(sK3,sK3,sK3,sK3) != sK1 | k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) != k1_xboole_0),
% 23.27/3.49    inference(definition_unfolding,[],[f65,f68,f67])).
% 23.27/3.49  
% 23.27/3.49  fof(f15,axiom,(
% 23.27/3.49    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 23.27/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.27/3.49  
% 23.27/3.49  fof(f28,plain,(
% 23.27/3.49    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 23.27/3.49    inference(nnf_transformation,[],[f15])).
% 23.27/3.49  
% 23.27/3.49  fof(f29,plain,(
% 23.27/3.49    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 23.27/3.49    inference(flattening,[],[f28])).
% 23.27/3.49  
% 23.27/3.49  fof(f60,plain,(
% 23.27/3.49    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f29])).
% 23.27/3.49  
% 23.27/3.49  fof(f88,plain,(
% 23.27/3.49    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) != k2_enumset1(X0,X0,X0,X1)) )),
% 23.27/3.49    inference(definition_unfolding,[],[f60,f67,f67])).
% 23.27/3.49  
% 23.27/3.49  fof(f41,plain,(
% 23.27/3.49    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 23.27/3.49    inference(cnf_transformation,[],[f25])).
% 23.27/3.49  
% 23.27/3.49  fof(f79,plain,(
% 23.27/3.49    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 23.27/3.49    inference(definition_unfolding,[],[f41,f51])).
% 23.27/3.49  
% 23.27/3.49  fof(f101,plain,(
% 23.27/3.49    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 23.27/3.49    inference(equality_resolution,[],[f79])).
% 23.27/3.49  
% 23.27/3.49  fof(f59,plain,(
% 23.27/3.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) )),
% 23.27/3.49    inference(cnf_transformation,[],[f29])).
% 23.27/3.49  
% 23.27/3.49  fof(f89,plain,(
% 23.27/3.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) != k2_enumset1(X0,X0,X0,X1)) )),
% 23.27/3.49    inference(definition_unfolding,[],[f59,f67,f67])).
% 23.27/3.49  
% 23.27/3.49  fof(f63,plain,(
% 23.27/3.49    k1_xboole_0 != sK1 | k4_xboole_0(sK1,k2_tarski(sK2,sK3)) != k1_xboole_0),
% 23.27/3.49    inference(cnf_transformation,[],[f33])).
% 23.27/3.49  
% 23.27/3.49  fof(f93,plain,(
% 23.27/3.49    k1_xboole_0 != sK1 | k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) != k1_xboole_0),
% 23.27/3.49    inference(definition_unfolding,[],[f63,f67])).
% 23.27/3.49  
% 23.27/3.49  cnf(c_27,negated_conjecture,
% 23.27/3.49      ( k2_enumset1(sK3,sK3,sK3,sK3) = sK1
% 23.27/3.49      | k2_enumset1(sK2,sK2,sK2,sK3) = sK1
% 23.27/3.49      | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
% 23.27/3.49      | k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) = k1_xboole_0
% 23.27/3.49      | k1_xboole_0 = sK1 ),
% 23.27/3.49      inference(cnf_transformation,[],[f94]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_1,plain,
% 23.27/3.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 23.27/3.49      inference(cnf_transformation,[],[f70]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_3,plain,
% 23.27/3.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 23.27/3.49      inference(cnf_transformation,[],[f37]) ).
% 23.27/3.49  
% 23.27/3.49  cnf(c_547,plain,
% 23.27/3.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 23.27/3.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_965,plain,
% 23.27/3.50      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_1,c_547]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_2253,plain,
% 23.27/3.50      ( k2_enumset1(sK3,sK3,sK3,sK3) = sK1
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK3) = sK1
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
% 23.27/3.50      | sK1 = k1_xboole_0
% 23.27/3.50      | r1_tarski(k4_xboole_0(sK1,k1_xboole_0),k2_enumset1(sK2,sK2,sK2,sK3)) = iProver_top ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_27,c_965]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_4,plain,
% 23.27/3.50      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 23.27/3.50      inference(cnf_transformation,[],[f39]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_967,plain,
% 23.27/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_1,c_4]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_0,plain,
% 23.27/3.50      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 23.27/3.50      inference(cnf_transformation,[],[f69]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_1588,plain,
% 23.27/3.50      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_967,c_0]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_2,plain,
% 23.27/3.50      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 23.27/3.50      inference(cnf_transformation,[],[f71]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_548,plain,
% 23.27/3.50      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.27/3.50      inference(light_normalisation,[status(thm)],[c_2,c_4]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_1593,plain,
% 23.27/3.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.27/3.50      inference(light_normalisation,[status(thm)],[c_1588,c_548]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_2259,plain,
% 23.27/3.50      ( k2_enumset1(sK3,sK3,sK3,sK3) = sK1
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK3) = sK1
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
% 23.27/3.50      | sK1 = k1_xboole_0
% 23.27/3.50      | r1_tarski(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) = iProver_top ),
% 23.27/3.50      inference(demodulation,[status(thm)],[c_2253,c_1593]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_17,plain,
% 23.27/3.50      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
% 23.27/3.50      | k2_enumset1(X1,X1,X1,X2) = X0
% 23.27/3.50      | k2_enumset1(X2,X2,X2,X2) = X0
% 23.27/3.50      | k2_enumset1(X1,X1,X1,X1) = X0
% 23.27/3.50      | k1_xboole_0 = X0 ),
% 23.27/3.50      inference(cnf_transformation,[],[f84]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_534,plain,
% 23.27/3.50      ( k2_enumset1(X0,X0,X0,X1) = X2
% 23.27/3.50      | k2_enumset1(X1,X1,X1,X1) = X2
% 23.27/3.50      | k2_enumset1(X0,X0,X0,X0) = X2
% 23.27/3.50      | k1_xboole_0 = X2
% 23.27/3.50      | r1_tarski(X2,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
% 23.27/3.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_2408,plain,
% 23.27/3.50      ( k2_enumset1(sK3,sK3,sK3,sK3) = sK1
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK3) = sK1
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
% 23.27/3.50      | sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_2259,c_534]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_11,plain,
% 23.27/3.50      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 23.27/3.50      inference(cnf_transformation,[],[f100]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_540,plain,
% 23.27/3.50      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
% 23.27/3.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_2411,plain,
% 23.27/3.50      ( k2_enumset1(sK2,sK2,sK2,sK3) = sK1
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
% 23.27/3.50      | sK1 = k1_xboole_0
% 23.27/3.50      | r2_hidden(sK3,sK1) = iProver_top ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_2408,c_540]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_2417,plain,
% 23.27/3.50      ( k2_enumset1(sK3,sK3,sK3,sK3) = X0
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK3) = sK1
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
% 23.27/3.50      | sK1 = k1_xboole_0
% 23.27/3.50      | k1_xboole_0 = X0
% 23.27/3.50      | r1_tarski(X0,sK1) != iProver_top ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_2408,c_534]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_3736,plain,
% 23.27/3.50      ( k2_enumset1(sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,X0)
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK3) = sK1
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
% 23.27/3.50      | k4_xboole_0(sK1,X0) = k1_xboole_0
% 23.27/3.50      | sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_547,c_2417]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_3940,plain,
% 23.27/3.50      ( k2_enumset1(sK2,sK2,sK2,sK3) = sK1
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
% 23.27/3.50      | k4_xboole_0(sK1,X0) = sK1
% 23.27/3.50      | k4_xboole_0(sK1,X0) = k1_xboole_0
% 23.27/3.50      | sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_3736,c_2408]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_23,negated_conjecture,
% 23.27/3.50      ( k2_enumset1(sK2,sK2,sK2,sK3) != sK1
% 23.27/3.50      | k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) != k1_xboole_0 ),
% 23.27/3.50      inference(cnf_transformation,[],[f90]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_5291,plain,
% 23.27/3.50      ( k2_enumset1(sK2,sK2,sK2,sK3) != sK1
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
% 23.27/3.50      | k4_xboole_0(sK1,X0) = sK1
% 23.27/3.50      | k4_xboole_0(sK1,X0) = k1_xboole_0
% 23.27/3.50      | k4_xboole_0(sK1,sK1) != k1_xboole_0
% 23.27/3.50      | sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_3940,c_23]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_1594,plain,
% 23.27/3.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 23.27/3.50      inference(demodulation,[status(thm)],[c_1593,c_967]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_5294,plain,
% 23.27/3.50      ( k2_enumset1(sK2,sK2,sK2,sK3) != sK1
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
% 23.27/3.50      | k4_xboole_0(sK1,X0) = sK1
% 23.27/3.50      | k4_xboole_0(sK1,X0) = k1_xboole_0
% 23.27/3.50      | sK1 = k1_xboole_0
% 23.27/3.50      | k1_xboole_0 != k1_xboole_0 ),
% 23.27/3.50      inference(demodulation,[status(thm)],[c_5291,c_1594]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_5295,plain,
% 23.27/3.50      ( k2_enumset1(sK2,sK2,sK2,sK3) != sK1
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
% 23.27/3.50      | k4_xboole_0(sK1,X0) = sK1
% 23.27/3.50      | k4_xboole_0(sK1,X0) = k1_xboole_0
% 23.27/3.50      | sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(equality_resolution_simp,[status(thm)],[c_5294]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_5350,plain,
% 23.27/3.50      ( k2_enumset1(sK2,sK2,sK2,sK2) = sK1
% 23.27/3.50      | k4_xboole_0(sK1,X0) = sK1
% 23.27/3.50      | k4_xboole_0(sK1,X0) = k1_xboole_0
% 23.27/3.50      | sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(global_propositional_subsumption,[status(thm)],[c_5295,c_3940]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_18,plain,
% 23.27/3.50      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0 ),
% 23.27/3.50      inference(cnf_transformation,[],[f85]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_5398,plain,
% 23.27/3.50      ( k4_xboole_0(sK1,X0) = sK1
% 23.27/3.50      | k4_xboole_0(sK1,X0) = k1_xboole_0
% 23.27/3.50      | k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,X1)) = k1_xboole_0
% 23.27/3.50      | sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_5350,c_18]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_25,negated_conjecture,
% 23.27/3.50      ( k2_enumset1(sK2,sK2,sK2,sK2) != sK1
% 23.27/3.50      | k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) != k1_xboole_0 ),
% 23.27/3.50      inference(cnf_transformation,[],[f92]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_7178,plain,
% 23.27/3.50      ( k2_enumset1(sK2,sK2,sK2,sK2) != sK1
% 23.27/3.50      | k4_xboole_0(sK1,X0) = sK1
% 23.27/3.50      | k4_xboole_0(sK1,X0) = k1_xboole_0
% 23.27/3.50      | sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_5398,c_25]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_7519,plain,
% 23.27/3.50      ( k4_xboole_0(sK1,X0) = sK1
% 23.27/3.50      | k4_xboole_0(sK1,X0) = k1_xboole_0
% 23.27/3.50      | sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(global_propositional_subsumption,[status(thm)],[c_7178,c_5350]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_966,plain,
% 23.27/3.50      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_7548,plain,
% 23.27/3.50      ( k5_xboole_0(X0,k4_xboole_0(sK1,sK1)) = k4_xboole_0(X0,sK1)
% 23.27/3.50      | k4_xboole_0(sK1,X0) = k1_xboole_0
% 23.27/3.50      | sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_7519,c_966]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_7577,plain,
% 23.27/3.50      ( k4_xboole_0(X0,sK1) = X0
% 23.27/3.50      | k4_xboole_0(sK1,X0) = k1_xboole_0
% 23.27/3.50      | sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(demodulation,[status(thm)],[c_7548,c_548,c_1594]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_10522,plain,
% 23.27/3.50      ( k2_enumset1(sK2,sK2,sK2,sK2) != sK1
% 23.27/3.50      | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK1) = k2_enumset1(sK2,sK2,sK2,sK3)
% 23.27/3.50      | sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_7577,c_25]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_582,plain,
% 23.27/3.50      ( ~ r1_tarski(sK1,k2_enumset1(sK2,sK2,sK2,sK3))
% 23.27/3.50      | k2_enumset1(sK3,sK3,sK3,sK3) = sK1
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK3) = sK1
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
% 23.27/3.50      | k1_xboole_0 = sK1 ),
% 23.27/3.50      inference(instantiation,[status(thm)],[c_17]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_268,plain,( X0 = X0 ),theory(equality) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_932,plain,
% 23.27/3.50      ( sK1 = sK1 ),
% 23.27/3.50      inference(instantiation,[status(thm)],[c_268]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_14,plain,
% 23.27/3.50      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X0)) ),
% 23.27/3.50      inference(cnf_transformation,[],[f103]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_537,plain,
% 23.27/3.50      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
% 23.27/3.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_2872,plain,
% 23.27/3.50      ( k2_enumset1(sK2,sK2,sK2,sK3) = sK1
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
% 23.27/3.50      | sK1 = k1_xboole_0
% 23.27/3.50      | r1_tarski(sK1,k2_enumset1(X0,X0,X0,sK3)) = iProver_top ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_2408,c_537]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_2877,plain,
% 23.27/3.50      ( r1_tarski(sK1,k2_enumset1(X0,X0,X0,sK3))
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK3) = sK1
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
% 23.27/3.50      | sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(predicate_to_equality_rev,[status(thm)],[c_2872]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_2879,plain,
% 23.27/3.50      ( r1_tarski(sK1,k2_enumset1(sK2,sK2,sK2,sK3))
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK3) = sK1
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
% 23.27/3.50      | sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(instantiation,[status(thm)],[c_2877]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_24,negated_conjecture,
% 23.27/3.50      ( k2_enumset1(sK3,sK3,sK3,sK3) != sK1
% 23.27/3.50      | k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) != k1_xboole_0 ),
% 23.27/3.50      inference(cnf_transformation,[],[f91]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_10523,plain,
% 23.27/3.50      ( k2_enumset1(sK3,sK3,sK3,sK3) != sK1
% 23.27/3.50      | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK1) = k2_enumset1(sK2,sK2,sK2,sK3)
% 23.27/3.50      | sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_7577,c_24]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_10524,plain,
% 23.27/3.50      ( k2_enumset1(sK2,sK2,sK2,sK3) != sK1
% 23.27/3.50      | k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK1) = k2_enumset1(sK2,sK2,sK2,sK3)
% 23.27/3.50      | sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_7577,c_23]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_269,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_678,plain,
% 23.27/3.50      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 23.27/3.50      inference(instantiation,[status(thm)],[c_269]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_786,plain,
% 23.27/3.50      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 23.27/3.50      inference(instantiation,[status(thm)],[c_678]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_11573,plain,
% 23.27/3.50      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 23.27/3.50      inference(instantiation,[status(thm)],[c_786]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_12311,plain,
% 23.27/3.50      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK1) = k2_enumset1(sK2,sK2,sK2,sK3)
% 23.27/3.50      | sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(global_propositional_subsumption,
% 23.27/3.50                [status(thm)],
% 23.27/3.50                [c_10522,c_582,c_932,c_2879,c_10523,c_10524,c_11573]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_21,plain,
% 23.27/3.50      ( ~ r2_hidden(X0,X1)
% 23.27/3.50      | k4_xboole_0(k2_enumset1(X2,X2,X2,X0),X1) != k2_enumset1(X2,X2,X2,X0) ),
% 23.27/3.50      inference(cnf_transformation,[],[f88]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_532,plain,
% 23.27/3.50      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) != k2_enumset1(X0,X0,X0,X1)
% 23.27/3.50      | r2_hidden(X1,X2) != iProver_top ),
% 23.27/3.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_13274,plain,
% 23.27/3.50      ( sK1 = k1_xboole_0 | r2_hidden(sK3,sK1) != iProver_top ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_12311,c_532]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_14000,plain,
% 23.27/3.50      ( k2_enumset1(sK2,sK2,sK2,sK3) = sK1
% 23.27/3.50      | k2_enumset1(sK2,sK2,sK2,sK2) = sK1
% 23.27/3.50      | sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_2411,c_13274]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_12,plain,
% 23.27/3.50      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 23.27/3.50      | X0 = X1
% 23.27/3.50      | X0 = X2
% 23.27/3.50      | X0 = X3 ),
% 23.27/3.50      inference(cnf_transformation,[],[f101]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_49,plain,
% 23.27/3.50      ( ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) | sK2 = sK2 ),
% 23.27/3.50      inference(instantiation,[status(thm)],[c_12]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_52,plain,
% 23.27/3.50      ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 23.27/3.50      inference(instantiation,[status(thm)],[c_11]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_51,plain,
% 23.27/3.50      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
% 23.27/3.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_53,plain,
% 23.27/3.50      ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 23.27/3.50      inference(instantiation,[status(thm)],[c_51]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_1488,plain,
% 23.27/3.50      ( k2_enumset1(sK2,sK2,sK2,sK2) != sK1
% 23.27/3.50      | sK1 = k2_enumset1(sK2,sK2,sK2,sK2)
% 23.27/3.50      | sK1 != sK1 ),
% 23.27/3.50      inference(instantiation,[status(thm)],[c_786]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_274,plain,
% 23.27/3.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.27/3.50      theory(equality) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_1161,plain,
% 23.27/3.50      ( r2_hidden(X0,X1)
% 23.27/3.50      | ~ r2_hidden(X2,k2_enumset1(X3,X3,X4,X2))
% 23.27/3.50      | X0 != X2
% 23.27/3.50      | X1 != k2_enumset1(X3,X3,X4,X2) ),
% 23.27/3.50      inference(instantiation,[status(thm)],[c_274]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_2216,plain,
% 23.27/3.50      ( r2_hidden(X0,sK1)
% 23.27/3.50      | ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2))
% 23.27/3.50      | X0 != sK2
% 23.27/3.50      | sK1 != k2_enumset1(sK2,sK2,sK2,sK2) ),
% 23.27/3.50      inference(instantiation,[status(thm)],[c_1161]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_2217,plain,
% 23.27/3.50      ( X0 != sK2
% 23.27/3.50      | sK1 != k2_enumset1(sK2,sK2,sK2,sK2)
% 23.27/3.50      | r2_hidden(X0,sK1) = iProver_top
% 23.27/3.50      | r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
% 23.27/3.50      inference(predicate_to_equality,[status(thm)],[c_2216]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_2219,plain,
% 23.27/3.50      ( sK1 != k2_enumset1(sK2,sK2,sK2,sK2)
% 23.27/3.50      | sK2 != sK2
% 23.27/3.50      | r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 23.27/3.50      | r2_hidden(sK2,sK1) = iProver_top ),
% 23.27/3.50      inference(instantiation,[status(thm)],[c_2217]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_22,plain,
% 23.27/3.50      ( ~ r2_hidden(X0,X1)
% 23.27/3.50      | k4_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) != k2_enumset1(X0,X0,X0,X2) ),
% 23.27/3.50      inference(cnf_transformation,[],[f89]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_531,plain,
% 23.27/3.50      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) != k2_enumset1(X0,X0,X0,X1)
% 23.27/3.50      | r2_hidden(X0,X2) != iProver_top ),
% 23.27/3.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_12333,plain,
% 23.27/3.50      ( sK1 = k1_xboole_0 | r2_hidden(sK2,sK1) != iProver_top ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_12311,c_531]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_17248,plain,
% 23.27/3.50      ( k2_enumset1(sK2,sK2,sK2,sK3) = sK1 | sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(global_propositional_subsumption,
% 23.27/3.50                [status(thm)],
% 23.27/3.50                [c_14000,c_49,c_52,c_53,c_932,c_1488,c_2219,c_2411,c_12333,
% 23.27/3.50                 c_13274]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_12331,plain,
% 23.27/3.50      ( k5_xboole_0(sK1,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK2,sK2,sK2,sK3))) = k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3))
% 23.27/3.50      | sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_12311,c_966]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_12354,plain,
% 23.27/3.50      ( k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) = sK1
% 23.27/3.50      | sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(demodulation,[status(thm)],[c_12331,c_548,c_1594]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_17269,plain,
% 23.27/3.50      ( k4_xboole_0(sK1,sK1) = sK1 | sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(superposition,[status(thm)],[c_17248,c_12354]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_17283,plain,
% 23.27/3.50      ( sK1 = k1_xboole_0 ),
% 23.27/3.50      inference(demodulation,[status(thm)],[c_17269,c_1594]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_26,negated_conjecture,
% 23.27/3.50      ( k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK3)) != k1_xboole_0
% 23.27/3.50      | k1_xboole_0 != sK1 ),
% 23.27/3.50      inference(cnf_transformation,[],[f93]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_73834,plain,
% 23.27/3.50      ( k4_xboole_0(k1_xboole_0,k2_enumset1(sK2,sK2,sK2,sK3)) != k1_xboole_0
% 23.27/3.50      | k1_xboole_0 != k1_xboole_0 ),
% 23.27/3.50      inference(demodulation,[status(thm)],[c_17283,c_26]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_73835,plain,
% 23.27/3.50      ( k4_xboole_0(k1_xboole_0,k2_enumset1(sK2,sK2,sK2,sK3)) != k1_xboole_0 ),
% 23.27/3.50      inference(equality_resolution_simp,[status(thm)],[c_73834]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_73836,plain,
% 23.27/3.50      ( k1_xboole_0 != k1_xboole_0 ),
% 23.27/3.50      inference(demodulation,[status(thm)],[c_73835,c_4]) ).
% 23.27/3.50  
% 23.27/3.50  cnf(c_73837,plain,
% 23.27/3.50      ( $false ),
% 23.27/3.50      inference(equality_resolution_simp,[status(thm)],[c_73836]) ).
% 23.27/3.50  
% 23.27/3.50  
% 23.27/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.27/3.50  
% 23.27/3.50  ------                               Statistics
% 23.27/3.50  
% 23.27/3.50  ------ General
% 23.27/3.50  
% 23.27/3.50  abstr_ref_over_cycles:                  0
% 23.27/3.50  abstr_ref_under_cycles:                 0
% 23.27/3.50  gc_basic_clause_elim:                   0
% 23.27/3.50  forced_gc_time:                         0
% 23.27/3.50  parsing_time:                           0.008
% 23.27/3.50  unif_index_cands_time:                  0.
% 23.27/3.50  unif_index_add_time:                    0.
% 23.27/3.50  orderings_time:                         0.
% 23.27/3.50  out_proof_time:                         0.012
% 23.27/3.50  total_time:                             2.678
% 23.27/3.50  num_of_symbols:                         41
% 23.27/3.50  num_of_terms:                           75452
% 23.27/3.50  
% 23.27/3.50  ------ Preprocessing
% 23.27/3.50  
% 23.27/3.50  num_of_splits:                          0
% 23.27/3.50  num_of_split_atoms:                     0
% 23.27/3.50  num_of_reused_defs:                     0
% 23.27/3.50  num_eq_ax_congr_red:                    10
% 23.27/3.50  num_of_sem_filtered_clauses:            1
% 23.27/3.50  num_of_subtypes:                        0
% 23.27/3.50  monotx_restored_types:                  0
% 23.27/3.50  sat_num_of_epr_types:                   0
% 23.27/3.50  sat_num_of_non_cyclic_types:            0
% 23.27/3.50  sat_guarded_non_collapsed_types:        0
% 23.27/3.50  num_pure_diseq_elim:                    0
% 23.27/3.50  simp_replaced_by:                       0
% 23.27/3.50  res_preprocessed:                       99
% 23.27/3.50  prep_upred:                             0
% 23.27/3.50  prep_unflattend:                        6
% 23.27/3.50  smt_new_axioms:                         0
% 23.27/3.50  pred_elim_cands:                        2
% 23.27/3.50  pred_elim:                              0
% 23.27/3.50  pred_elim_cl:                           0
% 23.27/3.50  pred_elim_cycles:                       1
% 23.27/3.50  merged_defs:                            0
% 23.27/3.50  merged_defs_ncl:                        0
% 23.27/3.50  bin_hyper_res:                          0
% 23.27/3.50  prep_cycles:                            3
% 23.27/3.50  pred_elim_time:                         0.001
% 23.27/3.50  splitting_time:                         0.
% 23.27/3.50  sem_filter_time:                        0.
% 23.27/3.50  monotx_time:                            0.
% 23.27/3.50  subtype_inf_time:                       0.
% 23.27/3.50  
% 23.27/3.50  ------ Problem properties
% 23.27/3.50  
% 23.27/3.50  clauses:                                28
% 23.27/3.50  conjectures:                            5
% 23.27/3.50  epr:                                    0
% 23.27/3.50  horn:                                   22
% 23.27/3.50  ground:                                 5
% 23.27/3.50  unary:                                  13
% 23.27/3.50  binary:                                 7
% 23.27/3.50  lits:                                   58
% 23.27/3.50  lits_eq:                                40
% 23.27/3.50  fd_pure:                                0
% 23.27/3.50  fd_pseudo:                              0
% 23.27/3.50  fd_cond:                                0
% 23.27/3.50  fd_pseudo_cond:                         5
% 23.27/3.50  ac_symbols:                             0
% 23.27/3.50  
% 23.27/3.50  ------ Propositional Solver
% 23.27/3.50  
% 23.27/3.50  prop_solver_calls:                      31
% 23.27/3.50  prop_fast_solver_calls:                 2640
% 23.27/3.50  smt_solver_calls:                       0
% 23.27/3.50  smt_fast_solver_calls:                  0
% 23.27/3.50  prop_num_of_clauses:                    23116
% 23.27/3.50  prop_preprocess_simplified:             26191
% 23.27/3.50  prop_fo_subsumed:                       914
% 23.27/3.50  prop_solver_time:                       0.
% 23.27/3.50  smt_solver_time:                        0.
% 23.27/3.50  smt_fast_solver_time:                   0.
% 23.27/3.50  prop_fast_solver_time:                  0.
% 23.27/3.50  prop_unsat_core_time:                   0.
% 23.27/3.50  
% 23.27/3.50  ------ QBF
% 23.27/3.50  
% 23.27/3.50  qbf_q_res:                              0
% 23.27/3.50  qbf_num_tautologies:                    0
% 23.27/3.50  qbf_prep_cycles:                        0
% 23.27/3.50  
% 23.27/3.50  ------ BMC1
% 23.27/3.50  
% 23.27/3.50  bmc1_current_bound:                     -1
% 23.27/3.50  bmc1_last_solved_bound:                 -1
% 23.27/3.50  bmc1_unsat_core_size:                   -1
% 23.27/3.50  bmc1_unsat_core_parents_size:           -1
% 23.27/3.50  bmc1_merge_next_fun:                    0
% 23.27/3.50  bmc1_unsat_core_clauses_time:           0.
% 23.27/3.50  
% 23.27/3.50  ------ Instantiation
% 23.27/3.50  
% 23.27/3.50  inst_num_of_clauses:                    2999
% 23.27/3.50  inst_num_in_passive:                    1376
% 23.27/3.50  inst_num_in_active:                     667
% 23.27/3.50  inst_num_in_unprocessed:                956
% 23.27/3.50  inst_num_of_loops:                      1120
% 23.27/3.50  inst_num_of_learning_restarts:          0
% 23.27/3.50  inst_num_moves_active_passive:          450
% 23.27/3.50  inst_lit_activity:                      0
% 23.27/3.50  inst_lit_activity_moves:                1
% 23.27/3.50  inst_num_tautologies:                   0
% 23.27/3.50  inst_num_prop_implied:                  0
% 23.27/3.50  inst_num_existing_simplified:           0
% 23.27/3.50  inst_num_eq_res_simplified:             0
% 23.27/3.50  inst_num_child_elim:                    0
% 23.27/3.50  inst_num_of_dismatching_blockings:      4535
% 23.27/3.50  inst_num_of_non_proper_insts:           4237
% 23.27/3.50  inst_num_of_duplicates:                 0
% 23.27/3.50  inst_inst_num_from_inst_to_res:         0
% 23.27/3.50  inst_dismatching_checking_time:         0.
% 23.27/3.50  
% 23.27/3.50  ------ Resolution
% 23.27/3.50  
% 23.27/3.50  res_num_of_clauses:                     0
% 23.27/3.50  res_num_in_passive:                     0
% 23.27/3.50  res_num_in_active:                      0
% 23.27/3.50  res_num_of_loops:                       102
% 23.27/3.50  res_forward_subset_subsumed:            921
% 23.27/3.50  res_backward_subset_subsumed:           0
% 23.27/3.50  res_forward_subsumed:                   0
% 23.27/3.50  res_backward_subsumed:                  0
% 23.27/3.50  res_forward_subsumption_resolution:     0
% 23.27/3.50  res_backward_subsumption_resolution:    0
% 23.27/3.50  res_clause_to_clause_subsumption:       103072
% 23.27/3.50  res_orphan_elimination:                 0
% 23.27/3.50  res_tautology_del:                      120
% 23.27/3.50  res_num_eq_res_simplified:              0
% 23.27/3.50  res_num_sel_changes:                    0
% 23.27/3.50  res_moves_from_active_to_pass:          0
% 23.27/3.50  
% 23.27/3.50  ------ Superposition
% 23.27/3.50  
% 23.27/3.50  sup_time_total:                         0.
% 23.27/3.50  sup_time_generating:                    0.
% 23.27/3.50  sup_time_sim_full:                      0.
% 23.27/3.50  sup_time_sim_immed:                     0.
% 23.27/3.50  
% 23.27/3.50  sup_num_of_clauses:                     4754
% 23.27/3.50  sup_num_in_active:                      139
% 23.27/3.50  sup_num_in_passive:                     4615
% 23.27/3.50  sup_num_of_loops:                       223
% 23.27/3.50  sup_fw_superposition:                   18136
% 23.27/3.50  sup_bw_superposition:                   8302
% 23.27/3.50  sup_immediate_simplified:               14148
% 23.27/3.50  sup_given_eliminated:                   4
% 23.27/3.50  comparisons_done:                       0
% 23.27/3.50  comparisons_avoided:                    178
% 23.27/3.50  
% 23.27/3.50  ------ Simplifications
% 23.27/3.50  
% 23.27/3.50  
% 23.27/3.50  sim_fw_subset_subsumed:                 3914
% 23.27/3.50  sim_bw_subset_subsumed:                 121
% 23.27/3.50  sim_fw_subsumed:                        2852
% 23.27/3.50  sim_bw_subsumed:                        124
% 23.27/3.50  sim_fw_subsumption_res:                 0
% 23.27/3.50  sim_bw_subsumption_res:                 0
% 23.27/3.50  sim_tautology_del:                      64
% 23.27/3.50  sim_eq_tautology_del:                   1751
% 23.27/3.50  sim_eq_res_simp:                        13
% 23.27/3.50  sim_fw_demodulated:                     9739
% 23.27/3.50  sim_bw_demodulated:                     79
% 23.27/3.50  sim_light_normalised:                   2063
% 23.27/3.50  sim_joinable_taut:                      0
% 23.27/3.50  sim_joinable_simp:                      0
% 23.27/3.50  sim_ac_normalised:                      0
% 23.27/3.50  sim_smt_subsumption:                    0
% 23.27/3.50  
%------------------------------------------------------------------------------
