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
% DateTime   : Thu Dec  3 11:29:18 EST 2020

% Result     : Theorem 7.43s
% Output     : CNFRefutation 7.43s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 237 expanded)
%              Number of clauses        :   18 (  19 expanded)
%              Number of leaves         :   17 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          :  237 ( 482 expanded)
%              Number of equality atoms :  180 ( 387 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f23])).

fof(f32,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f46,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK4 != sK5
      & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( sK4 != sK5
    & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f46])).

fof(f81,plain,(
    k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f83,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f60,f54])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f79,f80])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f78,f84])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f77,f85])).

fof(f87,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f76,f86])).

fof(f88,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f75,f87])).

fof(f89,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f74,f88])).

fof(f106,plain,(
    k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f81,f83,f89,f89,f89])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f15])).

fof(f90,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f73,f83,f80,f89])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f64,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f98,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f64,f87])).

fof(f107,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f98])).

fof(f108,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f107])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f105,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f69,f89])).

fof(f116,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f105])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f70,f89])).

fof(f114,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f104])).

fof(f115,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f114])).

fof(f82,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_25,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_0,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1126,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(superposition,[status(thm)],[c_25,c_0])).

cnf(c_16,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_681,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_23059,plain,
    ( r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1126,c_681])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_809,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_810,plain,
    ( sK5 = X0
    | r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_809])).

cnf(c_812,plain,
    ( sK5 = sK4
    | r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_810])).

cnf(c_369,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_738,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_369])).

cnf(c_739,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_738])).

cnf(c_22,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_30,plain,
    ( r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_27,plain,
    ( ~ r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f82])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23059,c_812,c_739,c_30,c_27,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:58:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.43/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.43/1.49  
% 7.43/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.43/1.49  
% 7.43/1.49  ------  iProver source info
% 7.43/1.49  
% 7.43/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.43/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.43/1.49  git: non_committed_changes: false
% 7.43/1.49  git: last_make_outside_of_git: false
% 7.43/1.49  
% 7.43/1.49  ------ 
% 7.43/1.49  ------ Parsing...
% 7.43/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.43/1.49  
% 7.43/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.43/1.49  
% 7.43/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.43/1.49  
% 7.43/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.43/1.49  ------ Proving...
% 7.43/1.49  ------ Problem Properties 
% 7.43/1.49  
% 7.43/1.49  
% 7.43/1.49  clauses                                 25
% 7.43/1.49  conjectures                             2
% 7.43/1.49  EPR                                     1
% 7.43/1.49  Horn                                    21
% 7.43/1.49  unary                                   14
% 7.43/1.49  binary                                  4
% 7.43/1.49  lits                                    46
% 7.43/1.49  lits eq                                 28
% 7.43/1.49  fd_pure                                 0
% 7.43/1.49  fd_pseudo                               0
% 7.43/1.49  fd_cond                                 1
% 7.43/1.49  fd_pseudo_cond                          6
% 7.43/1.49  AC symbols                              0
% 7.43/1.49  
% 7.43/1.49  ------ Input Options Time Limit: Unbounded
% 7.43/1.49  
% 7.43/1.49  
% 7.43/1.49  ------ 
% 7.43/1.49  Current options:
% 7.43/1.49  ------ 
% 7.43/1.49  
% 7.43/1.49  
% 7.43/1.49  
% 7.43/1.49  
% 7.43/1.49  ------ Proving...
% 7.43/1.49  
% 7.43/1.49  
% 7.43/1.49  % SZS status Theorem for theBenchmark.p
% 7.43/1.49  
% 7.43/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.43/1.49  
% 7.43/1.49  fof(f23,conjecture,(
% 7.43/1.49    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f24,negated_conjecture,(
% 7.43/1.49    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 7.43/1.49    inference(negated_conjecture,[],[f23])).
% 7.43/1.49  
% 7.43/1.49  fof(f32,plain,(
% 7.43/1.49    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 7.43/1.49    inference(ennf_transformation,[],[f24])).
% 7.43/1.49  
% 7.43/1.49  fof(f46,plain,(
% 7.43/1.49    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK4 != sK5 & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4))),
% 7.43/1.49    introduced(choice_axiom,[])).
% 7.43/1.49  
% 7.43/1.49  fof(f47,plain,(
% 7.43/1.49    sK4 != sK5 & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4)),
% 7.43/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f46])).
% 7.43/1.49  
% 7.43/1.49  fof(f81,plain,(
% 7.43/1.49    k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4)),
% 7.43/1.49    inference(cnf_transformation,[],[f47])).
% 7.43/1.49  
% 7.43/1.49  fof(f12,axiom,(
% 7.43/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f60,plain,(
% 7.43/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.43/1.49    inference(cnf_transformation,[],[f12])).
% 7.43/1.49  
% 7.43/1.49  fof(f6,axiom,(
% 7.43/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f54,plain,(
% 7.43/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.43/1.49    inference(cnf_transformation,[],[f6])).
% 7.43/1.49  
% 7.43/1.49  fof(f83,plain,(
% 7.43/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 7.43/1.49    inference(definition_unfolding,[],[f60,f54])).
% 7.43/1.49  
% 7.43/1.49  fof(f16,axiom,(
% 7.43/1.49    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f74,plain,(
% 7.43/1.49    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f16])).
% 7.43/1.49  
% 7.43/1.49  fof(f17,axiom,(
% 7.43/1.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f75,plain,(
% 7.43/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f17])).
% 7.43/1.49  
% 7.43/1.49  fof(f18,axiom,(
% 7.43/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f76,plain,(
% 7.43/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f18])).
% 7.43/1.49  
% 7.43/1.49  fof(f19,axiom,(
% 7.43/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f77,plain,(
% 7.43/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f19])).
% 7.43/1.49  
% 7.43/1.49  fof(f20,axiom,(
% 7.43/1.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f78,plain,(
% 7.43/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f20])).
% 7.43/1.49  
% 7.43/1.49  fof(f21,axiom,(
% 7.43/1.49    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f79,plain,(
% 7.43/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f21])).
% 7.43/1.49  
% 7.43/1.49  fof(f22,axiom,(
% 7.43/1.49    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f80,plain,(
% 7.43/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f22])).
% 7.43/1.49  
% 7.43/1.49  fof(f84,plain,(
% 7.43/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.43/1.49    inference(definition_unfolding,[],[f79,f80])).
% 7.43/1.49  
% 7.43/1.49  fof(f85,plain,(
% 7.43/1.49    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.43/1.49    inference(definition_unfolding,[],[f78,f84])).
% 7.43/1.49  
% 7.43/1.49  fof(f86,plain,(
% 7.43/1.49    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.43/1.49    inference(definition_unfolding,[],[f77,f85])).
% 7.43/1.49  
% 7.43/1.49  fof(f87,plain,(
% 7.43/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.43/1.49    inference(definition_unfolding,[],[f76,f86])).
% 7.43/1.49  
% 7.43/1.49  fof(f88,plain,(
% 7.43/1.49    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.43/1.49    inference(definition_unfolding,[],[f75,f87])).
% 7.43/1.49  
% 7.43/1.49  fof(f89,plain,(
% 7.43/1.49    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.43/1.49    inference(definition_unfolding,[],[f74,f88])).
% 7.43/1.49  
% 7.43/1.49  fof(f106,plain,(
% 7.43/1.49    k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 7.43/1.49    inference(definition_unfolding,[],[f81,f83,f89,f89,f89])).
% 7.43/1.49  
% 7.43/1.49  fof(f15,axiom,(
% 7.43/1.49    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f73,plain,(
% 7.43/1.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f15])).
% 7.43/1.49  
% 7.43/1.49  fof(f90,plain,(
% 7.43/1.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.43/1.49    inference(definition_unfolding,[],[f73,f83,f80,f89])).
% 7.43/1.49  
% 7.43/1.49  fof(f13,axiom,(
% 7.43/1.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f31,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.43/1.49    inference(ennf_transformation,[],[f13])).
% 7.43/1.49  
% 7.43/1.49  fof(f37,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.43/1.49    inference(nnf_transformation,[],[f31])).
% 7.43/1.49  
% 7.43/1.49  fof(f38,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.43/1.49    inference(flattening,[],[f37])).
% 7.43/1.49  
% 7.43/1.49  fof(f39,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.43/1.49    inference(rectify,[],[f38])).
% 7.43/1.49  
% 7.43/1.49  fof(f40,plain,(
% 7.43/1.49    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 7.43/1.49    introduced(choice_axiom,[])).
% 7.43/1.49  
% 7.43/1.49  fof(f41,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.43/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 7.43/1.49  
% 7.43/1.49  fof(f64,plain,(
% 7.43/1.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.43/1.49    inference(cnf_transformation,[],[f41])).
% 7.43/1.49  
% 7.43/1.49  fof(f98,plain,(
% 7.43/1.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.43/1.49    inference(definition_unfolding,[],[f64,f87])).
% 7.43/1.49  
% 7.43/1.49  fof(f107,plain,(
% 7.43/1.49    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 7.43/1.49    inference(equality_resolution,[],[f98])).
% 7.43/1.49  
% 7.43/1.49  fof(f108,plain,(
% 7.43/1.49    ( ! [X0,X5,X1] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5))) )),
% 7.43/1.49    inference(equality_resolution,[],[f107])).
% 7.43/1.49  
% 7.43/1.49  fof(f14,axiom,(
% 7.43/1.49    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f42,plain,(
% 7.43/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.43/1.49    inference(nnf_transformation,[],[f14])).
% 7.43/1.49  
% 7.43/1.49  fof(f43,plain,(
% 7.43/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.43/1.49    inference(rectify,[],[f42])).
% 7.43/1.49  
% 7.43/1.49  fof(f44,plain,(
% 7.43/1.49    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 7.43/1.49    introduced(choice_axiom,[])).
% 7.43/1.49  
% 7.43/1.49  fof(f45,plain,(
% 7.43/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.43/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 7.43/1.49  
% 7.43/1.49  fof(f69,plain,(
% 7.43/1.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.43/1.49    inference(cnf_transformation,[],[f45])).
% 7.43/1.49  
% 7.43/1.49  fof(f105,plain,(
% 7.43/1.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 7.43/1.49    inference(definition_unfolding,[],[f69,f89])).
% 7.43/1.49  
% 7.43/1.49  fof(f116,plain,(
% 7.43/1.49    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 7.43/1.49    inference(equality_resolution,[],[f105])).
% 7.43/1.49  
% 7.43/1.49  fof(f70,plain,(
% 7.43/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.43/1.49    inference(cnf_transformation,[],[f45])).
% 7.43/1.49  
% 7.43/1.49  fof(f104,plain,(
% 7.43/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 7.43/1.49    inference(definition_unfolding,[],[f70,f89])).
% 7.43/1.49  
% 7.43/1.49  fof(f114,plain,(
% 7.43/1.49    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 7.43/1.49    inference(equality_resolution,[],[f104])).
% 7.43/1.49  
% 7.43/1.49  fof(f115,plain,(
% 7.43/1.49    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 7.43/1.49    inference(equality_resolution,[],[f114])).
% 7.43/1.49  
% 7.43/1.49  fof(f82,plain,(
% 7.43/1.49    sK4 != sK5),
% 7.43/1.49    inference(cnf_transformation,[],[f47])).
% 7.43/1.49  
% 7.43/1.49  cnf(c_25,negated_conjecture,
% 7.43/1.49      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 7.43/1.49      inference(cnf_transformation,[],[f106]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_0,plain,
% 7.43/1.49      ( k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 7.43/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1126,plain,
% 7.43/1.49      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_25,c_0]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_16,plain,
% 7.43/1.49      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
% 7.43/1.49      inference(cnf_transformation,[],[f108]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_681,plain,
% 7.43/1.49      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_23059,plain,
% 7.43/1.49      ( r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_1126,c_681]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_23,plain,
% 7.43/1.49      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 7.43/1.49      inference(cnf_transformation,[],[f116]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_809,plain,
% 7.43/1.49      ( ~ r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 7.43/1.49      | sK5 = X0 ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_23]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_810,plain,
% 7.43/1.49      ( sK5 = X0
% 7.43/1.49      | r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_809]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_812,plain,
% 7.43/1.49      ( sK5 = sK4
% 7.43/1.49      | r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_810]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_369,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_738,plain,
% 7.43/1.49      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_369]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_739,plain,
% 7.43/1.49      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_738]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_22,plain,
% 7.43/1.49      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 7.43/1.49      inference(cnf_transformation,[],[f115]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_30,plain,
% 7.43/1.49      ( r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_22]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_27,plain,
% 7.43/1.49      ( ~ r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 7.43/1.49      | sK4 = sK4 ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_23]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_24,negated_conjecture,
% 7.43/1.49      ( sK4 != sK5 ),
% 7.43/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(contradiction,plain,
% 7.43/1.49      ( $false ),
% 7.43/1.49      inference(minisat,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_23059,c_812,c_739,c_30,c_27,c_24]) ).
% 7.43/1.49  
% 7.43/1.49  
% 7.43/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.43/1.49  
% 7.43/1.49  ------                               Statistics
% 7.43/1.49  
% 7.43/1.49  ------ Selected
% 7.43/1.49  
% 7.43/1.49  total_time:                             0.901
% 7.43/1.49  
%------------------------------------------------------------------------------
