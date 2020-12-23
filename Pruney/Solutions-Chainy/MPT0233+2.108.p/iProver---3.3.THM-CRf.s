%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:28 EST 2020

% Result     : Theorem 7.23s
% Output     : CNFRefutation 7.23s
% Verified   : 
% Statistics : Number of formulae       :  138 (1453 expanded)
%              Number of clauses        :   61 ( 105 expanded)
%              Number of leaves         :   20 ( 455 expanded)
%              Depth                    :   21
%              Number of atoms          :  398 (2595 expanded)
%              Number of equality atoms :  313 (2236 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f46,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK3 != sK6
      & sK3 != sK5
      & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( sK3 != sK6
    & sK3 != sK5
    & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f31,f46])).

fof(f83,plain,(
    r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f69,f86])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f68,f87])).

fof(f89,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f67,f88])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f89])).

fof(f116,plain,(
    r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(definition_unfolding,[],[f83,f90,f90])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f91,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f65,f90])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f76,f90,f91,f91,f90])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f79,f90,f91])).

fof(f124,plain,(
    ! [X2,X1] : r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f110])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f82,f91,f91,f91])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f93,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f48,f57,f57])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f92,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f53,f57])).

fof(f84,plain,(
    sK3 != sK5 ),
    inference(cnf_transformation,[],[f47])).

fof(f85,plain,(
    sK3 != sK6 ),
    inference(cnf_transformation,[],[f47])).

fof(f81,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f115,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f81,f91,f91,f91])).

fof(f127,plain,(
    ! [X1] : k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f115])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f104,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f59,f90])).

fof(f121,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f104])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f102,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f61,f90])).

fof(f117,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f102])).

fof(f118,plain,(
    ! [X4,X0] : r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f117])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f103,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f60,f90])).

fof(f119,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f103])).

fof(f120,plain,(
    ! [X4,X1] : r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f119])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(flattening,[],[f41])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f72,f90,f91])).

cnf(c_29,negated_conjecture,
    ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_662,plain,
    ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_24,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_663,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X2
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1033,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_662,c_663])).

cnf(c_21,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_666,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1380,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = X0
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1033,c_663])).

cnf(c_5320,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_666,c_1380])).

cnf(c_25,plain,
    ( X0 = X1
    | k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1382,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | sK5 = X0 ),
    inference(superposition,[status(thm)],[c_1033,c_25])).

cnf(c_7194,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | sK4 = sK5 ),
    inference(superposition,[status(thm)],[c_5320,c_1382])).

cnf(c_10096,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | sK4 = sK5 ),
    inference(superposition,[status(thm)],[c_1033,c_7194])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1035,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1040,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_4096,plain,
    ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1035,c_1040])).

cnf(c_4186,plain,
    ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_4096,c_8])).

cnf(c_12149,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | k5_xboole_0(k4_xboole_0(k1_xboole_0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),k4_xboole_0(k1_xboole_0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k4_xboole_0(k1_xboole_0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | sK4 = sK5 ),
    inference(superposition,[status(thm)],[c_10096,c_4186])).

cnf(c_28,negated_conjecture,
    ( sK3 != sK5 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_27,negated_conjecture,
    ( sK3 != sK6 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_26,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_31,plain,
    ( k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_32,plain,
    ( k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_286,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_843,plain,
    ( sK6 != X0
    | sK3 != X0
    | sK3 = sK6 ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_844,plain,
    ( sK6 != sK3
    | sK3 = sK6
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_845,plain,
    ( sK5 != X0
    | sK3 != X0
    | sK3 = sK5 ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_846,plain,
    ( sK5 != sK3
    | sK3 = sK5
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_845])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_868,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0))
    | sK3 = X0
    | sK3 = sK6 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_985,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | sK3 = sK6 ),
    inference(instantiation,[status(thm)],[c_868])).

cnf(c_290,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1140,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK3,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_290])).

cnf(c_4450,plain,
    ( ~ r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | r2_hidden(sK3,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_4453,plain,
    ( r2_hidden(sK3,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4450])).

cnf(c_13,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_674,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_672,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14280,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK5 = X0
    | r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1033,c_672])).

cnf(c_15095,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK4 = sK5 ),
    inference(superposition,[status(thm)],[c_674,c_14280])).

cnf(c_14,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_673,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15096,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK5 = sK3 ),
    inference(superposition,[status(thm)],[c_673,c_14280])).

cnf(c_15275,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15095,c_28,c_31,c_32,c_846,c_15096])).

cnf(c_15276,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_15275])).

cnf(c_15289,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK5 = X0
    | sK6 = X0
    | r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15276,c_672])).

cnf(c_15373,plain,
    ( ~ r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK5 = X0
    | sK6 = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15289])).

cnf(c_15375,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK5 = sK3
    | sK6 = sK3 ),
    inference(instantiation,[status(thm)],[c_15373])).

cnf(c_15491,plain,
    ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_15868,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12149,c_28,c_27,c_31,c_32,c_844,c_846,c_985,c_4453,c_15375,c_15491])).

cnf(c_15891,plain,
    ( r2_hidden(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_15868,c_673])).

cnf(c_1448,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1453,plain,
    ( k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k1_xboole_0) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1448])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1447,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1449,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1447])).

cnf(c_1451,plain,
    ( k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k1_xboole_0) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(sK3,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1449])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15891,c_1453,c_1451])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:53:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.23/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.23/1.51  
% 7.23/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.23/1.51  
% 7.23/1.51  ------  iProver source info
% 7.23/1.51  
% 7.23/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.23/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.23/1.51  git: non_committed_changes: false
% 7.23/1.51  git: last_make_outside_of_git: false
% 7.23/1.51  
% 7.23/1.51  ------ 
% 7.23/1.51  
% 7.23/1.51  ------ Input Options
% 7.23/1.51  
% 7.23/1.51  --out_options                           all
% 7.23/1.51  --tptp_safe_out                         true
% 7.23/1.51  --problem_path                          ""
% 7.23/1.51  --include_path                          ""
% 7.23/1.51  --clausifier                            res/vclausify_rel
% 7.23/1.51  --clausifier_options                    --mode clausify
% 7.23/1.51  --stdin                                 false
% 7.23/1.51  --stats_out                             all
% 7.23/1.51  
% 7.23/1.51  ------ General Options
% 7.23/1.51  
% 7.23/1.51  --fof                                   false
% 7.23/1.51  --time_out_real                         305.
% 7.23/1.51  --time_out_virtual                      -1.
% 7.23/1.51  --symbol_type_check                     false
% 7.23/1.51  --clausify_out                          false
% 7.23/1.51  --sig_cnt_out                           false
% 7.23/1.51  --trig_cnt_out                          false
% 7.23/1.51  --trig_cnt_out_tolerance                1.
% 7.23/1.51  --trig_cnt_out_sk_spl                   false
% 7.23/1.51  --abstr_cl_out                          false
% 7.23/1.51  
% 7.23/1.51  ------ Global Options
% 7.23/1.51  
% 7.23/1.51  --schedule                              default
% 7.23/1.51  --add_important_lit                     false
% 7.23/1.51  --prop_solver_per_cl                    1000
% 7.23/1.51  --min_unsat_core                        false
% 7.23/1.51  --soft_assumptions                      false
% 7.23/1.51  --soft_lemma_size                       3
% 7.23/1.51  --prop_impl_unit_size                   0
% 7.23/1.51  --prop_impl_unit                        []
% 7.23/1.51  --share_sel_clauses                     true
% 7.23/1.51  --reset_solvers                         false
% 7.23/1.51  --bc_imp_inh                            [conj_cone]
% 7.23/1.51  --conj_cone_tolerance                   3.
% 7.23/1.51  --extra_neg_conj                        none
% 7.23/1.51  --large_theory_mode                     true
% 7.23/1.51  --prolific_symb_bound                   200
% 7.23/1.51  --lt_threshold                          2000
% 7.23/1.51  --clause_weak_htbl                      true
% 7.23/1.51  --gc_record_bc_elim                     false
% 7.23/1.51  
% 7.23/1.51  ------ Preprocessing Options
% 7.23/1.51  
% 7.23/1.51  --preprocessing_flag                    true
% 7.23/1.51  --time_out_prep_mult                    0.1
% 7.23/1.51  --splitting_mode                        input
% 7.23/1.51  --splitting_grd                         true
% 7.23/1.51  --splitting_cvd                         false
% 7.23/1.51  --splitting_cvd_svl                     false
% 7.23/1.51  --splitting_nvd                         32
% 7.23/1.51  --sub_typing                            true
% 7.23/1.51  --prep_gs_sim                           true
% 7.23/1.51  --prep_unflatten                        true
% 7.23/1.51  --prep_res_sim                          true
% 7.23/1.51  --prep_upred                            true
% 7.23/1.51  --prep_sem_filter                       exhaustive
% 7.23/1.51  --prep_sem_filter_out                   false
% 7.23/1.51  --pred_elim                             true
% 7.23/1.51  --res_sim_input                         true
% 7.23/1.51  --eq_ax_congr_red                       true
% 7.23/1.51  --pure_diseq_elim                       true
% 7.23/1.51  --brand_transform                       false
% 7.23/1.51  --non_eq_to_eq                          false
% 7.23/1.51  --prep_def_merge                        true
% 7.23/1.51  --prep_def_merge_prop_impl              false
% 7.23/1.51  --prep_def_merge_mbd                    true
% 7.23/1.51  --prep_def_merge_tr_red                 false
% 7.23/1.51  --prep_def_merge_tr_cl                  false
% 7.23/1.51  --smt_preprocessing                     true
% 7.23/1.51  --smt_ac_axioms                         fast
% 7.23/1.51  --preprocessed_out                      false
% 7.23/1.51  --preprocessed_stats                    false
% 7.23/1.51  
% 7.23/1.51  ------ Abstraction refinement Options
% 7.23/1.51  
% 7.23/1.51  --abstr_ref                             []
% 7.23/1.51  --abstr_ref_prep                        false
% 7.23/1.51  --abstr_ref_until_sat                   false
% 7.23/1.51  --abstr_ref_sig_restrict                funpre
% 7.23/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.23/1.51  --abstr_ref_under                       []
% 7.23/1.51  
% 7.23/1.51  ------ SAT Options
% 7.23/1.51  
% 7.23/1.51  --sat_mode                              false
% 7.23/1.51  --sat_fm_restart_options                ""
% 7.23/1.51  --sat_gr_def                            false
% 7.23/1.51  --sat_epr_types                         true
% 7.23/1.51  --sat_non_cyclic_types                  false
% 7.23/1.51  --sat_finite_models                     false
% 7.23/1.51  --sat_fm_lemmas                         false
% 7.23/1.51  --sat_fm_prep                           false
% 7.23/1.51  --sat_fm_uc_incr                        true
% 7.23/1.51  --sat_out_model                         small
% 7.23/1.51  --sat_out_clauses                       false
% 7.23/1.51  
% 7.23/1.51  ------ QBF Options
% 7.23/1.51  
% 7.23/1.51  --qbf_mode                              false
% 7.23/1.51  --qbf_elim_univ                         false
% 7.23/1.51  --qbf_dom_inst                          none
% 7.23/1.51  --qbf_dom_pre_inst                      false
% 7.23/1.51  --qbf_sk_in                             false
% 7.23/1.51  --qbf_pred_elim                         true
% 7.23/1.51  --qbf_split                             512
% 7.23/1.51  
% 7.23/1.51  ------ BMC1 Options
% 7.23/1.51  
% 7.23/1.51  --bmc1_incremental                      false
% 7.23/1.51  --bmc1_axioms                           reachable_all
% 7.23/1.51  --bmc1_min_bound                        0
% 7.23/1.51  --bmc1_max_bound                        -1
% 7.23/1.51  --bmc1_max_bound_default                -1
% 7.23/1.51  --bmc1_symbol_reachability              true
% 7.23/1.51  --bmc1_property_lemmas                  false
% 7.23/1.51  --bmc1_k_induction                      false
% 7.23/1.51  --bmc1_non_equiv_states                 false
% 7.23/1.51  --bmc1_deadlock                         false
% 7.23/1.51  --bmc1_ucm                              false
% 7.23/1.51  --bmc1_add_unsat_core                   none
% 7.23/1.51  --bmc1_unsat_core_children              false
% 7.23/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.23/1.51  --bmc1_out_stat                         full
% 7.23/1.51  --bmc1_ground_init                      false
% 7.23/1.51  --bmc1_pre_inst_next_state              false
% 7.23/1.51  --bmc1_pre_inst_state                   false
% 7.23/1.51  --bmc1_pre_inst_reach_state             false
% 7.23/1.51  --bmc1_out_unsat_core                   false
% 7.23/1.51  --bmc1_aig_witness_out                  false
% 7.23/1.51  --bmc1_verbose                          false
% 7.23/1.51  --bmc1_dump_clauses_tptp                false
% 7.23/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.23/1.51  --bmc1_dump_file                        -
% 7.23/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.23/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.23/1.51  --bmc1_ucm_extend_mode                  1
% 7.23/1.51  --bmc1_ucm_init_mode                    2
% 7.23/1.51  --bmc1_ucm_cone_mode                    none
% 7.23/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.23/1.51  --bmc1_ucm_relax_model                  4
% 7.23/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.23/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.23/1.51  --bmc1_ucm_layered_model                none
% 7.23/1.51  --bmc1_ucm_max_lemma_size               10
% 7.23/1.51  
% 7.23/1.51  ------ AIG Options
% 7.23/1.51  
% 7.23/1.51  --aig_mode                              false
% 7.23/1.51  
% 7.23/1.51  ------ Instantiation Options
% 7.23/1.51  
% 7.23/1.51  --instantiation_flag                    true
% 7.23/1.51  --inst_sos_flag                         false
% 7.23/1.51  --inst_sos_phase                        true
% 7.23/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.23/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.23/1.51  --inst_lit_sel_side                     num_symb
% 7.23/1.51  --inst_solver_per_active                1400
% 7.23/1.51  --inst_solver_calls_frac                1.
% 7.23/1.51  --inst_passive_queue_type               priority_queues
% 7.23/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.23/1.51  --inst_passive_queues_freq              [25;2]
% 7.23/1.51  --inst_dismatching                      true
% 7.23/1.51  --inst_eager_unprocessed_to_passive     true
% 7.23/1.51  --inst_prop_sim_given                   true
% 7.23/1.51  --inst_prop_sim_new                     false
% 7.23/1.51  --inst_subs_new                         false
% 7.23/1.51  --inst_eq_res_simp                      false
% 7.23/1.51  --inst_subs_given                       false
% 7.23/1.51  --inst_orphan_elimination               true
% 7.23/1.51  --inst_learning_loop_flag               true
% 7.23/1.51  --inst_learning_start                   3000
% 7.23/1.51  --inst_learning_factor                  2
% 7.23/1.51  --inst_start_prop_sim_after_learn       3
% 7.23/1.51  --inst_sel_renew                        solver
% 7.23/1.51  --inst_lit_activity_flag                true
% 7.23/1.51  --inst_restr_to_given                   false
% 7.23/1.51  --inst_activity_threshold               500
% 7.23/1.51  --inst_out_proof                        true
% 7.23/1.51  
% 7.23/1.51  ------ Resolution Options
% 7.23/1.51  
% 7.23/1.51  --resolution_flag                       true
% 7.23/1.51  --res_lit_sel                           adaptive
% 7.23/1.51  --res_lit_sel_side                      none
% 7.23/1.51  --res_ordering                          kbo
% 7.23/1.51  --res_to_prop_solver                    active
% 7.23/1.51  --res_prop_simpl_new                    false
% 7.23/1.51  --res_prop_simpl_given                  true
% 7.23/1.51  --res_passive_queue_type                priority_queues
% 7.23/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.23/1.51  --res_passive_queues_freq               [15;5]
% 7.23/1.51  --res_forward_subs                      full
% 7.23/1.51  --res_backward_subs                     full
% 7.23/1.51  --res_forward_subs_resolution           true
% 7.23/1.51  --res_backward_subs_resolution          true
% 7.23/1.51  --res_orphan_elimination                true
% 7.23/1.51  --res_time_limit                        2.
% 7.23/1.51  --res_out_proof                         true
% 7.23/1.51  
% 7.23/1.51  ------ Superposition Options
% 7.23/1.51  
% 7.23/1.51  --superposition_flag                    true
% 7.23/1.51  --sup_passive_queue_type                priority_queues
% 7.23/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.23/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.23/1.51  --demod_completeness_check              fast
% 7.23/1.51  --demod_use_ground                      true
% 7.23/1.51  --sup_to_prop_solver                    passive
% 7.23/1.51  --sup_prop_simpl_new                    true
% 7.23/1.51  --sup_prop_simpl_given                  true
% 7.23/1.51  --sup_fun_splitting                     false
% 7.23/1.51  --sup_smt_interval                      50000
% 7.23/1.51  
% 7.23/1.51  ------ Superposition Simplification Setup
% 7.23/1.51  
% 7.23/1.51  --sup_indices_passive                   []
% 7.23/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.23/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.51  --sup_full_bw                           [BwDemod]
% 7.23/1.51  --sup_immed_triv                        [TrivRules]
% 7.23/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.23/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.51  --sup_immed_bw_main                     []
% 7.23/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.23/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.23/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.23/1.51  
% 7.23/1.51  ------ Combination Options
% 7.23/1.51  
% 7.23/1.51  --comb_res_mult                         3
% 7.23/1.51  --comb_sup_mult                         2
% 7.23/1.51  --comb_inst_mult                        10
% 7.23/1.51  
% 7.23/1.51  ------ Debug Options
% 7.23/1.51  
% 7.23/1.51  --dbg_backtrace                         false
% 7.23/1.51  --dbg_dump_prop_clauses                 false
% 7.23/1.51  --dbg_dump_prop_clauses_file            -
% 7.23/1.51  --dbg_out_stat                          false
% 7.23/1.51  ------ Parsing...
% 7.23/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.23/1.51  
% 7.23/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.23/1.51  
% 7.23/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.23/1.51  
% 7.23/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.23/1.51  ------ Proving...
% 7.23/1.51  ------ Problem Properties 
% 7.23/1.51  
% 7.23/1.51  
% 7.23/1.51  clauses                                 30
% 7.23/1.51  conjectures                             3
% 7.23/1.51  EPR                                     3
% 7.23/1.51  Horn                                    21
% 7.23/1.51  unary                                   15
% 7.23/1.51  binary                                  8
% 7.23/1.51  lits                                    55
% 7.23/1.51  lits eq                                 29
% 7.23/1.51  fd_pure                                 0
% 7.23/1.51  fd_pseudo                               0
% 7.23/1.51  fd_cond                                 1
% 7.23/1.51  fd_pseudo_cond                          6
% 7.23/1.51  AC symbols                              0
% 7.23/1.51  
% 7.23/1.51  ------ Schedule dynamic 5 is on 
% 7.23/1.51  
% 7.23/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.23/1.51  
% 7.23/1.51  
% 7.23/1.51  ------ 
% 7.23/1.51  Current options:
% 7.23/1.51  ------ 
% 7.23/1.51  
% 7.23/1.51  ------ Input Options
% 7.23/1.51  
% 7.23/1.51  --out_options                           all
% 7.23/1.51  --tptp_safe_out                         true
% 7.23/1.51  --problem_path                          ""
% 7.23/1.51  --include_path                          ""
% 7.23/1.51  --clausifier                            res/vclausify_rel
% 7.23/1.51  --clausifier_options                    --mode clausify
% 7.23/1.51  --stdin                                 false
% 7.23/1.51  --stats_out                             all
% 7.23/1.51  
% 7.23/1.51  ------ General Options
% 7.23/1.51  
% 7.23/1.51  --fof                                   false
% 7.23/1.51  --time_out_real                         305.
% 7.23/1.51  --time_out_virtual                      -1.
% 7.23/1.51  --symbol_type_check                     false
% 7.23/1.51  --clausify_out                          false
% 7.23/1.51  --sig_cnt_out                           false
% 7.23/1.51  --trig_cnt_out                          false
% 7.23/1.51  --trig_cnt_out_tolerance                1.
% 7.23/1.51  --trig_cnt_out_sk_spl                   false
% 7.23/1.51  --abstr_cl_out                          false
% 7.23/1.51  
% 7.23/1.51  ------ Global Options
% 7.23/1.51  
% 7.23/1.51  --schedule                              default
% 7.23/1.51  --add_important_lit                     false
% 7.23/1.51  --prop_solver_per_cl                    1000
% 7.23/1.51  --min_unsat_core                        false
% 7.23/1.51  --soft_assumptions                      false
% 7.23/1.51  --soft_lemma_size                       3
% 7.23/1.51  --prop_impl_unit_size                   0
% 7.23/1.51  --prop_impl_unit                        []
% 7.23/1.51  --share_sel_clauses                     true
% 7.23/1.51  --reset_solvers                         false
% 7.23/1.51  --bc_imp_inh                            [conj_cone]
% 7.23/1.51  --conj_cone_tolerance                   3.
% 7.23/1.51  --extra_neg_conj                        none
% 7.23/1.51  --large_theory_mode                     true
% 7.23/1.51  --prolific_symb_bound                   200
% 7.23/1.51  --lt_threshold                          2000
% 7.23/1.51  --clause_weak_htbl                      true
% 7.23/1.51  --gc_record_bc_elim                     false
% 7.23/1.51  
% 7.23/1.51  ------ Preprocessing Options
% 7.23/1.51  
% 7.23/1.51  --preprocessing_flag                    true
% 7.23/1.51  --time_out_prep_mult                    0.1
% 7.23/1.51  --splitting_mode                        input
% 7.23/1.51  --splitting_grd                         true
% 7.23/1.51  --splitting_cvd                         false
% 7.23/1.51  --splitting_cvd_svl                     false
% 7.23/1.51  --splitting_nvd                         32
% 7.23/1.51  --sub_typing                            true
% 7.23/1.51  --prep_gs_sim                           true
% 7.23/1.51  --prep_unflatten                        true
% 7.23/1.51  --prep_res_sim                          true
% 7.23/1.51  --prep_upred                            true
% 7.23/1.51  --prep_sem_filter                       exhaustive
% 7.23/1.51  --prep_sem_filter_out                   false
% 7.23/1.51  --pred_elim                             true
% 7.23/1.51  --res_sim_input                         true
% 7.23/1.51  --eq_ax_congr_red                       true
% 7.23/1.51  --pure_diseq_elim                       true
% 7.23/1.51  --brand_transform                       false
% 7.23/1.51  --non_eq_to_eq                          false
% 7.23/1.51  --prep_def_merge                        true
% 7.23/1.51  --prep_def_merge_prop_impl              false
% 7.23/1.51  --prep_def_merge_mbd                    true
% 7.23/1.51  --prep_def_merge_tr_red                 false
% 7.23/1.51  --prep_def_merge_tr_cl                  false
% 7.23/1.51  --smt_preprocessing                     true
% 7.23/1.51  --smt_ac_axioms                         fast
% 7.23/1.51  --preprocessed_out                      false
% 7.23/1.51  --preprocessed_stats                    false
% 7.23/1.51  
% 7.23/1.51  ------ Abstraction refinement Options
% 7.23/1.51  
% 7.23/1.51  --abstr_ref                             []
% 7.23/1.51  --abstr_ref_prep                        false
% 7.23/1.51  --abstr_ref_until_sat                   false
% 7.23/1.51  --abstr_ref_sig_restrict                funpre
% 7.23/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.23/1.51  --abstr_ref_under                       []
% 7.23/1.51  
% 7.23/1.51  ------ SAT Options
% 7.23/1.51  
% 7.23/1.51  --sat_mode                              false
% 7.23/1.51  --sat_fm_restart_options                ""
% 7.23/1.51  --sat_gr_def                            false
% 7.23/1.51  --sat_epr_types                         true
% 7.23/1.51  --sat_non_cyclic_types                  false
% 7.23/1.51  --sat_finite_models                     false
% 7.23/1.51  --sat_fm_lemmas                         false
% 7.23/1.51  --sat_fm_prep                           false
% 7.23/1.51  --sat_fm_uc_incr                        true
% 7.23/1.51  --sat_out_model                         small
% 7.23/1.51  --sat_out_clauses                       false
% 7.23/1.51  
% 7.23/1.51  ------ QBF Options
% 7.23/1.51  
% 7.23/1.51  --qbf_mode                              false
% 7.23/1.51  --qbf_elim_univ                         false
% 7.23/1.51  --qbf_dom_inst                          none
% 7.23/1.51  --qbf_dom_pre_inst                      false
% 7.23/1.51  --qbf_sk_in                             false
% 7.23/1.51  --qbf_pred_elim                         true
% 7.23/1.51  --qbf_split                             512
% 7.23/1.51  
% 7.23/1.51  ------ BMC1 Options
% 7.23/1.51  
% 7.23/1.51  --bmc1_incremental                      false
% 7.23/1.51  --bmc1_axioms                           reachable_all
% 7.23/1.51  --bmc1_min_bound                        0
% 7.23/1.51  --bmc1_max_bound                        -1
% 7.23/1.51  --bmc1_max_bound_default                -1
% 7.23/1.51  --bmc1_symbol_reachability              true
% 7.23/1.51  --bmc1_property_lemmas                  false
% 7.23/1.51  --bmc1_k_induction                      false
% 7.23/1.51  --bmc1_non_equiv_states                 false
% 7.23/1.51  --bmc1_deadlock                         false
% 7.23/1.51  --bmc1_ucm                              false
% 7.23/1.51  --bmc1_add_unsat_core                   none
% 7.23/1.51  --bmc1_unsat_core_children              false
% 7.23/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.23/1.51  --bmc1_out_stat                         full
% 7.23/1.51  --bmc1_ground_init                      false
% 7.23/1.51  --bmc1_pre_inst_next_state              false
% 7.23/1.51  --bmc1_pre_inst_state                   false
% 7.23/1.51  --bmc1_pre_inst_reach_state             false
% 7.23/1.51  --bmc1_out_unsat_core                   false
% 7.23/1.51  --bmc1_aig_witness_out                  false
% 7.23/1.51  --bmc1_verbose                          false
% 7.23/1.51  --bmc1_dump_clauses_tptp                false
% 7.23/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.23/1.51  --bmc1_dump_file                        -
% 7.23/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.23/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.23/1.51  --bmc1_ucm_extend_mode                  1
% 7.23/1.51  --bmc1_ucm_init_mode                    2
% 7.23/1.51  --bmc1_ucm_cone_mode                    none
% 7.23/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.23/1.51  --bmc1_ucm_relax_model                  4
% 7.23/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.23/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.23/1.51  --bmc1_ucm_layered_model                none
% 7.23/1.51  --bmc1_ucm_max_lemma_size               10
% 7.23/1.51  
% 7.23/1.51  ------ AIG Options
% 7.23/1.51  
% 7.23/1.51  --aig_mode                              false
% 7.23/1.51  
% 7.23/1.51  ------ Instantiation Options
% 7.23/1.51  
% 7.23/1.51  --instantiation_flag                    true
% 7.23/1.51  --inst_sos_flag                         false
% 7.23/1.51  --inst_sos_phase                        true
% 7.23/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.23/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.23/1.51  --inst_lit_sel_side                     none
% 7.23/1.51  --inst_solver_per_active                1400
% 7.23/1.51  --inst_solver_calls_frac                1.
% 7.23/1.51  --inst_passive_queue_type               priority_queues
% 7.23/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.23/1.51  --inst_passive_queues_freq              [25;2]
% 7.23/1.51  --inst_dismatching                      true
% 7.23/1.51  --inst_eager_unprocessed_to_passive     true
% 7.23/1.51  --inst_prop_sim_given                   true
% 7.23/1.51  --inst_prop_sim_new                     false
% 7.23/1.51  --inst_subs_new                         false
% 7.23/1.51  --inst_eq_res_simp                      false
% 7.23/1.51  --inst_subs_given                       false
% 7.23/1.51  --inst_orphan_elimination               true
% 7.23/1.51  --inst_learning_loop_flag               true
% 7.23/1.51  --inst_learning_start                   3000
% 7.23/1.51  --inst_learning_factor                  2
% 7.23/1.51  --inst_start_prop_sim_after_learn       3
% 7.23/1.51  --inst_sel_renew                        solver
% 7.23/1.51  --inst_lit_activity_flag                true
% 7.23/1.51  --inst_restr_to_given                   false
% 7.23/1.51  --inst_activity_threshold               500
% 7.23/1.51  --inst_out_proof                        true
% 7.23/1.51  
% 7.23/1.51  ------ Resolution Options
% 7.23/1.51  
% 7.23/1.51  --resolution_flag                       false
% 7.23/1.51  --res_lit_sel                           adaptive
% 7.23/1.51  --res_lit_sel_side                      none
% 7.23/1.51  --res_ordering                          kbo
% 7.23/1.51  --res_to_prop_solver                    active
% 7.23/1.51  --res_prop_simpl_new                    false
% 7.23/1.51  --res_prop_simpl_given                  true
% 7.23/1.51  --res_passive_queue_type                priority_queues
% 7.23/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.23/1.51  --res_passive_queues_freq               [15;5]
% 7.23/1.51  --res_forward_subs                      full
% 7.23/1.51  --res_backward_subs                     full
% 7.23/1.51  --res_forward_subs_resolution           true
% 7.23/1.51  --res_backward_subs_resolution          true
% 7.23/1.51  --res_orphan_elimination                true
% 7.23/1.51  --res_time_limit                        2.
% 7.23/1.51  --res_out_proof                         true
% 7.23/1.51  
% 7.23/1.51  ------ Superposition Options
% 7.23/1.51  
% 7.23/1.51  --superposition_flag                    true
% 7.23/1.51  --sup_passive_queue_type                priority_queues
% 7.23/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.23/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.23/1.51  --demod_completeness_check              fast
% 7.23/1.51  --demod_use_ground                      true
% 7.23/1.51  --sup_to_prop_solver                    passive
% 7.23/1.51  --sup_prop_simpl_new                    true
% 7.23/1.51  --sup_prop_simpl_given                  true
% 7.23/1.51  --sup_fun_splitting                     false
% 7.23/1.51  --sup_smt_interval                      50000
% 7.23/1.51  
% 7.23/1.51  ------ Superposition Simplification Setup
% 7.23/1.51  
% 7.23/1.51  --sup_indices_passive                   []
% 7.23/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.23/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.23/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.51  --sup_full_bw                           [BwDemod]
% 7.23/1.51  --sup_immed_triv                        [TrivRules]
% 7.23/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.23/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.51  --sup_immed_bw_main                     []
% 7.23/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.23/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.23/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.23/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.23/1.51  
% 7.23/1.51  ------ Combination Options
% 7.23/1.51  
% 7.23/1.51  --comb_res_mult                         3
% 7.23/1.51  --comb_sup_mult                         2
% 7.23/1.51  --comb_inst_mult                        10
% 7.23/1.51  
% 7.23/1.51  ------ Debug Options
% 7.23/1.51  
% 7.23/1.51  --dbg_backtrace                         false
% 7.23/1.51  --dbg_dump_prop_clauses                 false
% 7.23/1.51  --dbg_dump_prop_clauses_file            -
% 7.23/1.51  --dbg_out_stat                          false
% 7.23/1.51  
% 7.23/1.51  
% 7.23/1.51  
% 7.23/1.51  
% 7.23/1.51  ------ Proving...
% 7.23/1.51  
% 7.23/1.51  
% 7.23/1.51  % SZS status Theorem for theBenchmark.p
% 7.23/1.51  
% 7.23/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.23/1.51  
% 7.23/1.51  fof(f22,conjecture,(
% 7.23/1.51    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 7.23/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f23,negated_conjecture,(
% 7.23/1.51    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 7.23/1.51    inference(negated_conjecture,[],[f22])).
% 7.23/1.51  
% 7.23/1.51  fof(f31,plain,(
% 7.23/1.51    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 7.23/1.51    inference(ennf_transformation,[],[f23])).
% 7.23/1.51  
% 7.23/1.51  fof(f46,plain,(
% 7.23/1.51    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK3 != sK6 & sK3 != sK5 & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)))),
% 7.23/1.51    introduced(choice_axiom,[])).
% 7.23/1.51  
% 7.23/1.51  fof(f47,plain,(
% 7.23/1.51    sK3 != sK6 & sK3 != sK5 & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))),
% 7.23/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f31,f46])).
% 7.23/1.51  
% 7.23/1.51  fof(f83,plain,(
% 7.23/1.51    r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))),
% 7.23/1.51    inference(cnf_transformation,[],[f47])).
% 7.23/1.51  
% 7.23/1.51  fof(f13,axiom,(
% 7.23/1.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.23/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f66,plain,(
% 7.23/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.23/1.51    inference(cnf_transformation,[],[f13])).
% 7.23/1.51  
% 7.23/1.51  fof(f14,axiom,(
% 7.23/1.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.23/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f67,plain,(
% 7.23/1.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.23/1.51    inference(cnf_transformation,[],[f14])).
% 7.23/1.51  
% 7.23/1.51  fof(f15,axiom,(
% 7.23/1.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.23/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f68,plain,(
% 7.23/1.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.23/1.51    inference(cnf_transformation,[],[f15])).
% 7.23/1.51  
% 7.23/1.51  fof(f16,axiom,(
% 7.23/1.51    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.23/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f69,plain,(
% 7.23/1.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.23/1.51    inference(cnf_transformation,[],[f16])).
% 7.23/1.51  
% 7.23/1.51  fof(f17,axiom,(
% 7.23/1.51    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.23/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f70,plain,(
% 7.23/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.23/1.51    inference(cnf_transformation,[],[f17])).
% 7.23/1.51  
% 7.23/1.51  fof(f18,axiom,(
% 7.23/1.51    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.23/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f71,plain,(
% 7.23/1.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.23/1.51    inference(cnf_transformation,[],[f18])).
% 7.23/1.51  
% 7.23/1.51  fof(f86,plain,(
% 7.23/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.23/1.51    inference(definition_unfolding,[],[f70,f71])).
% 7.23/1.51  
% 7.23/1.51  fof(f87,plain,(
% 7.23/1.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.23/1.51    inference(definition_unfolding,[],[f69,f86])).
% 7.23/1.51  
% 7.23/1.51  fof(f88,plain,(
% 7.23/1.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.23/1.51    inference(definition_unfolding,[],[f68,f87])).
% 7.23/1.51  
% 7.23/1.51  fof(f89,plain,(
% 7.23/1.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.23/1.51    inference(definition_unfolding,[],[f67,f88])).
% 7.23/1.51  
% 7.23/1.51  fof(f90,plain,(
% 7.23/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.23/1.51    inference(definition_unfolding,[],[f66,f89])).
% 7.23/1.51  
% 7.23/1.51  fof(f116,plain,(
% 7.23/1.51    r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))),
% 7.23/1.51    inference(definition_unfolding,[],[f83,f90,f90])).
% 7.23/1.51  
% 7.23/1.51  fof(f20,axiom,(
% 7.23/1.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 7.23/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f30,plain,(
% 7.23/1.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.23/1.51    inference(ennf_transformation,[],[f20])).
% 7.23/1.51  
% 7.23/1.51  fof(f43,plain,(
% 7.23/1.51    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 7.23/1.51    inference(nnf_transformation,[],[f30])).
% 7.23/1.51  
% 7.23/1.51  fof(f44,plain,(
% 7.23/1.51    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 7.23/1.51    inference(flattening,[],[f43])).
% 7.23/1.51  
% 7.23/1.51  fof(f76,plain,(
% 7.23/1.51    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 7.23/1.51    inference(cnf_transformation,[],[f44])).
% 7.23/1.51  
% 7.23/1.51  fof(f12,axiom,(
% 7.23/1.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.23/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f65,plain,(
% 7.23/1.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.23/1.51    inference(cnf_transformation,[],[f12])).
% 7.23/1.51  
% 7.23/1.51  fof(f91,plain,(
% 7.23/1.51    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.23/1.51    inference(definition_unfolding,[],[f65,f90])).
% 7.23/1.51  
% 7.23/1.51  fof(f113,plain,(
% 7.23/1.51    ( ! [X2,X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0 | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 7.23/1.51    inference(definition_unfolding,[],[f76,f90,f91,f91,f90])).
% 7.23/1.51  
% 7.23/1.51  fof(f79,plain,(
% 7.23/1.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 7.23/1.51    inference(cnf_transformation,[],[f44])).
% 7.23/1.51  
% 7.23/1.51  fof(f110,plain,(
% 7.23/1.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X0) )),
% 7.23/1.51    inference(definition_unfolding,[],[f79,f90,f91])).
% 7.23/1.51  
% 7.23/1.51  fof(f124,plain,(
% 7.23/1.51    ( ! [X2,X1] : (r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 7.23/1.51    inference(equality_resolution,[],[f110])).
% 7.23/1.51  
% 7.23/1.51  fof(f21,axiom,(
% 7.23/1.51    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 7.23/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f45,plain,(
% 7.23/1.51    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 7.23/1.51    inference(nnf_transformation,[],[f21])).
% 7.23/1.51  
% 7.23/1.51  fof(f82,plain,(
% 7.23/1.51    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 7.23/1.51    inference(cnf_transformation,[],[f45])).
% 7.23/1.51  
% 7.23/1.51  fof(f114,plain,(
% 7.23/1.51    ( ! [X0,X1] : (k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | X0 = X1) )),
% 7.23/1.51    inference(definition_unfolding,[],[f82,f91,f91,f91])).
% 7.23/1.51  
% 7.23/1.51  fof(f8,axiom,(
% 7.23/1.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.23/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f56,plain,(
% 7.23/1.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.23/1.51    inference(cnf_transformation,[],[f8])).
% 7.23/1.51  
% 7.23/1.51  fof(f1,axiom,(
% 7.23/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.23/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f48,plain,(
% 7.23/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.23/1.51    inference(cnf_transformation,[],[f1])).
% 7.23/1.51  
% 7.23/1.51  fof(f9,axiom,(
% 7.23/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.23/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f57,plain,(
% 7.23/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.23/1.51    inference(cnf_transformation,[],[f9])).
% 7.23/1.51  
% 7.23/1.51  fof(f93,plain,(
% 7.23/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.23/1.51    inference(definition_unfolding,[],[f48,f57,f57])).
% 7.23/1.51  
% 7.23/1.51  fof(f5,axiom,(
% 7.23/1.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.23/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f53,plain,(
% 7.23/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.23/1.51    inference(cnf_transformation,[],[f5])).
% 7.23/1.51  
% 7.23/1.51  fof(f92,plain,(
% 7.23/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.23/1.51    inference(definition_unfolding,[],[f53,f57])).
% 7.23/1.51  
% 7.23/1.51  fof(f84,plain,(
% 7.23/1.51    sK3 != sK5),
% 7.23/1.51    inference(cnf_transformation,[],[f47])).
% 7.23/1.51  
% 7.23/1.51  fof(f85,plain,(
% 7.23/1.51    sK3 != sK6),
% 7.23/1.51    inference(cnf_transformation,[],[f47])).
% 7.23/1.51  
% 7.23/1.51  fof(f81,plain,(
% 7.23/1.51    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 7.23/1.51    inference(cnf_transformation,[],[f45])).
% 7.23/1.51  
% 7.23/1.51  fof(f115,plain,(
% 7.23/1.51    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.23/1.51    inference(definition_unfolding,[],[f81,f91,f91,f91])).
% 7.23/1.51  
% 7.23/1.51  fof(f127,plain,(
% 7.23/1.51    ( ! [X1] : (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 7.23/1.51    inference(equality_resolution,[],[f115])).
% 7.23/1.51  
% 7.23/1.51  fof(f11,axiom,(
% 7.23/1.51    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.23/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f36,plain,(
% 7.23/1.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.23/1.51    inference(nnf_transformation,[],[f11])).
% 7.23/1.51  
% 7.23/1.51  fof(f37,plain,(
% 7.23/1.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.23/1.51    inference(flattening,[],[f36])).
% 7.23/1.51  
% 7.23/1.51  fof(f38,plain,(
% 7.23/1.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.23/1.51    inference(rectify,[],[f37])).
% 7.23/1.51  
% 7.23/1.51  fof(f39,plain,(
% 7.23/1.51    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 7.23/1.51    introduced(choice_axiom,[])).
% 7.23/1.51  
% 7.23/1.51  fof(f40,plain,(
% 7.23/1.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.23/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 7.23/1.51  
% 7.23/1.51  fof(f59,plain,(
% 7.23/1.51    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 7.23/1.51    inference(cnf_transformation,[],[f40])).
% 7.23/1.51  
% 7.23/1.51  fof(f104,plain,(
% 7.23/1.51    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 7.23/1.51    inference(definition_unfolding,[],[f59,f90])).
% 7.23/1.51  
% 7.23/1.51  fof(f121,plain,(
% 7.23/1.51    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.23/1.51    inference(equality_resolution,[],[f104])).
% 7.23/1.51  
% 7.23/1.51  fof(f61,plain,(
% 7.23/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.23/1.51    inference(cnf_transformation,[],[f40])).
% 7.23/1.51  
% 7.23/1.51  fof(f102,plain,(
% 7.23/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 7.23/1.51    inference(definition_unfolding,[],[f61,f90])).
% 7.23/1.51  
% 7.23/1.51  fof(f117,plain,(
% 7.23/1.51    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X4) != X2) )),
% 7.23/1.51    inference(equality_resolution,[],[f102])).
% 7.23/1.51  
% 7.23/1.51  fof(f118,plain,(
% 7.23/1.51    ( ! [X4,X0] : (r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X4))) )),
% 7.23/1.51    inference(equality_resolution,[],[f117])).
% 7.23/1.51  
% 7.23/1.51  fof(f60,plain,(
% 7.23/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.23/1.51    inference(cnf_transformation,[],[f40])).
% 7.23/1.51  
% 7.23/1.51  fof(f103,plain,(
% 7.23/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 7.23/1.51    inference(definition_unfolding,[],[f60,f90])).
% 7.23/1.51  
% 7.23/1.51  fof(f119,plain,(
% 7.23/1.51    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1) != X2) )),
% 7.23/1.51    inference(equality_resolution,[],[f103])).
% 7.23/1.51  
% 7.23/1.51  fof(f120,plain,(
% 7.23/1.51    ( ! [X4,X1] : (r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1))) )),
% 7.23/1.51    inference(equality_resolution,[],[f119])).
% 7.23/1.51  
% 7.23/1.51  fof(f19,axiom,(
% 7.23/1.51    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 7.23/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.23/1.51  
% 7.23/1.51  fof(f41,plain,(
% 7.23/1.51    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 7.23/1.51    inference(nnf_transformation,[],[f19])).
% 7.23/1.51  
% 7.23/1.51  fof(f42,plain,(
% 7.23/1.51    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 7.23/1.51    inference(flattening,[],[f41])).
% 7.23/1.51  
% 7.23/1.51  fof(f72,plain,(
% 7.23/1.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)) )),
% 7.23/1.51    inference(cnf_transformation,[],[f42])).
% 7.23/1.51  
% 7.23/1.51  fof(f108,plain,(
% 7.23/1.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.23/1.51    inference(definition_unfolding,[],[f72,f90,f91])).
% 7.23/1.51  
% 7.23/1.51  cnf(c_29,negated_conjecture,
% 7.23/1.51      ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
% 7.23/1.51      inference(cnf_transformation,[],[f116]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_662,plain,
% 7.23/1.51      ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) = iProver_top ),
% 7.23/1.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_24,plain,
% 7.23/1.51      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 7.23/1.51      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
% 7.23/1.51      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
% 7.23/1.51      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 7.23/1.51      | k1_xboole_0 = X0 ),
% 7.23/1.51      inference(cnf_transformation,[],[f113]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_663,plain,
% 7.23/1.51      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
% 7.23/1.51      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X2
% 7.23/1.51      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X2
% 7.23/1.51      | k1_xboole_0 = X2
% 7.23/1.51      | r1_tarski(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
% 7.23/1.51      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_1033,plain,
% 7.23/1.51      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_662,c_663]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_21,plain,
% 7.23/1.51      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
% 7.23/1.51      inference(cnf_transformation,[],[f124]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_666,plain,
% 7.23/1.51      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = iProver_top ),
% 7.23/1.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_1380,plain,
% 7.23/1.51      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = X0
% 7.23/1.51      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.23/1.51      | k1_xboole_0 = X0
% 7.23/1.51      | r1_tarski(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_1033,c_663]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_5320,plain,
% 7.23/1.51      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 7.23/1.51      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
% 7.23/1.51      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_666,c_1380]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_25,plain,
% 7.23/1.51      ( X0 = X1
% 7.23/1.51      | k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 7.23/1.51      inference(cnf_transformation,[],[f114]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_1382,plain,
% 7.23/1.51      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.23/1.51      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 7.23/1.51      | sK5 = X0 ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_1033,c_25]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_7194,plain,
% 7.23/1.51      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
% 7.23/1.51      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.23/1.51      | k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 7.23/1.51      | sK4 = sK5 ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_5320,c_1382]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_10096,plain,
% 7.23/1.51      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
% 7.23/1.51      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.23/1.51      | k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 7.23/1.51      | sK4 = sK5 ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_1033,c_7194]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_8,plain,
% 7.23/1.51      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.23/1.51      inference(cnf_transformation,[],[f56]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_1,plain,
% 7.23/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.23/1.51      inference(cnf_transformation,[],[f93]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_1035,plain,
% 7.23/1.51      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_0,plain,
% 7.23/1.51      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.23/1.51      inference(cnf_transformation,[],[f92]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_1040,plain,
% 7.23/1.51      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_4096,plain,
% 7.23/1.51      ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_1035,c_1040]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_4186,plain,
% 7.23/1.51      ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.23/1.51      inference(demodulation,[status(thm)],[c_4096,c_8]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_12149,plain,
% 7.23/1.51      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
% 7.23/1.51      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.23/1.51      | k5_xboole_0(k4_xboole_0(k1_xboole_0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),k4_xboole_0(k1_xboole_0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k4_xboole_0(k1_xboole_0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 7.23/1.51      | sK4 = sK5 ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_10096,c_4186]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_28,negated_conjecture,
% 7.23/1.51      ( sK3 != sK5 ),
% 7.23/1.51      inference(cnf_transformation,[],[f84]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_27,negated_conjecture,
% 7.23/1.51      ( sK3 != sK6 ),
% 7.23/1.51      inference(cnf_transformation,[],[f85]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_26,plain,
% 7.23/1.51      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 7.23/1.51      inference(cnf_transformation,[],[f127]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_31,plain,
% 7.23/1.51      ( k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 7.23/1.51      inference(instantiation,[status(thm)],[c_26]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_32,plain,
% 7.23/1.51      ( k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 7.23/1.51      | sK3 = sK3 ),
% 7.23/1.51      inference(instantiation,[status(thm)],[c_25]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_286,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_843,plain,
% 7.23/1.51      ( sK6 != X0 | sK3 != X0 | sK3 = sK6 ),
% 7.23/1.51      inference(instantiation,[status(thm)],[c_286]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_844,plain,
% 7.23/1.51      ( sK6 != sK3 | sK3 = sK6 | sK3 != sK3 ),
% 7.23/1.51      inference(instantiation,[status(thm)],[c_843]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_845,plain,
% 7.23/1.51      ( sK5 != X0 | sK3 != X0 | sK3 = sK5 ),
% 7.23/1.51      inference(instantiation,[status(thm)],[c_286]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_846,plain,
% 7.23/1.51      ( sK5 != sK3 | sK3 = sK5 | sK3 != sK3 ),
% 7.23/1.51      inference(instantiation,[status(thm)],[c_845]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_15,plain,
% 7.23/1.51      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 7.23/1.51      | X0 = X1
% 7.23/1.51      | X0 = X2 ),
% 7.23/1.51      inference(cnf_transformation,[],[f121]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_868,plain,
% 7.23/1.51      ( ~ r2_hidden(sK3,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0))
% 7.23/1.51      | sK3 = X0
% 7.23/1.51      | sK3 = sK6 ),
% 7.23/1.51      inference(instantiation,[status(thm)],[c_15]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_985,plain,
% 7.23/1.51      ( ~ r2_hidden(sK3,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 7.23/1.51      | sK3 = sK6 ),
% 7.23/1.51      inference(instantiation,[status(thm)],[c_868]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_290,plain,
% 7.23/1.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.23/1.51      theory(equality) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_1140,plain,
% 7.23/1.51      ( ~ r2_hidden(X0,X1)
% 7.23/1.51      | r2_hidden(sK3,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 7.23/1.51      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != X1
% 7.23/1.51      | sK3 != X0 ),
% 7.23/1.51      inference(instantiation,[status(thm)],[c_290]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_4450,plain,
% 7.23/1.51      ( ~ r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 7.23/1.51      | r2_hidden(sK3,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 7.23/1.51      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | sK3 != X0 ),
% 7.23/1.51      inference(instantiation,[status(thm)],[c_1140]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_4453,plain,
% 7.23/1.51      ( r2_hidden(sK3,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 7.23/1.51      | ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 7.23/1.51      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | sK3 != sK3 ),
% 7.23/1.51      inference(instantiation,[status(thm)],[c_4450]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_13,plain,
% 7.23/1.51      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
% 7.23/1.51      inference(cnf_transformation,[],[f118]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_674,plain,
% 7.23/1.51      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = iProver_top ),
% 7.23/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_672,plain,
% 7.23/1.51      ( X0 = X1
% 7.23/1.51      | X0 = X2
% 7.23/1.51      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) != iProver_top ),
% 7.23/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_14280,plain,
% 7.23/1.51      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.23/1.51      | sK5 = X0
% 7.23/1.51      | r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_1033,c_672]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_15095,plain,
% 7.23/1.51      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.23/1.51      | sK4 = sK5 ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_674,c_14280]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_14,plain,
% 7.23/1.51      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 7.23/1.51      inference(cnf_transformation,[],[f120]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_673,plain,
% 7.23/1.51      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 7.23/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_15096,plain,
% 7.23/1.51      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.23/1.51      | sK5 = sK3 ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_673,c_14280]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_15275,plain,
% 7.23/1.51      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.23/1.51      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
% 7.23/1.51      inference(global_propositional_subsumption,
% 7.23/1.51                [status(thm)],
% 7.23/1.51                [c_15095,c_28,c_31,c_32,c_846,c_15096]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_15276,plain,
% 7.23/1.51      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 7.23/1.51      inference(renaming,[status(thm)],[c_15275]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_15289,plain,
% 7.23/1.51      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.23/1.51      | sK5 = X0
% 7.23/1.51      | sK6 = X0
% 7.23/1.51      | r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_15276,c_672]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_15373,plain,
% 7.23/1.51      ( ~ r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 7.23/1.51      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.23/1.51      | sK5 = X0
% 7.23/1.51      | sK6 = X0 ),
% 7.23/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_15289]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_15375,plain,
% 7.23/1.51      ( ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 7.23/1.51      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.23/1.51      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.23/1.51      | sK5 = sK3
% 7.23/1.51      | sK6 = sK3 ),
% 7.23/1.51      inference(instantiation,[status(thm)],[c_15373]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_15491,plain,
% 7.23/1.51      ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 7.23/1.51      inference(instantiation,[status(thm)],[c_14]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_15868,plain,
% 7.23/1.51      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 7.23/1.51      inference(global_propositional_subsumption,
% 7.23/1.51                [status(thm)],
% 7.23/1.51                [c_12149,c_28,c_27,c_31,c_32,c_844,c_846,c_985,c_4453,
% 7.23/1.51                 c_15375,c_15491]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_15891,plain,
% 7.23/1.51      ( r2_hidden(sK3,k1_xboole_0) = iProver_top ),
% 7.23/1.51      inference(superposition,[status(thm)],[c_15868,c_673]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_1448,plain,
% 7.23/1.51      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 7.23/1.51      inference(instantiation,[status(thm)],[c_8]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_1453,plain,
% 7.23/1.51      ( k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k1_xboole_0) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 7.23/1.51      inference(instantiation,[status(thm)],[c_1448]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_19,plain,
% 7.23/1.51      ( ~ r2_hidden(X0,X1)
% 7.23/1.51      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 7.23/1.51      inference(cnf_transformation,[],[f108]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_1447,plain,
% 7.23/1.51      ( ~ r2_hidden(X0,k1_xboole_0)
% 7.23/1.51      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 7.23/1.51      inference(instantiation,[status(thm)],[c_19]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_1449,plain,
% 7.23/1.51      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 7.23/1.51      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.23/1.51      inference(predicate_to_equality,[status(thm)],[c_1447]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(c_1451,plain,
% 7.23/1.51      ( k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k1_xboole_0) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 7.23/1.51      | r2_hidden(sK3,k1_xboole_0) != iProver_top ),
% 7.23/1.51      inference(instantiation,[status(thm)],[c_1449]) ).
% 7.23/1.51  
% 7.23/1.51  cnf(contradiction,plain,
% 7.23/1.51      ( $false ),
% 7.23/1.51      inference(minisat,[status(thm)],[c_15891,c_1453,c_1451]) ).
% 7.23/1.51  
% 7.23/1.51  
% 7.23/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.23/1.51  
% 7.23/1.51  ------                               Statistics
% 7.23/1.51  
% 7.23/1.51  ------ General
% 7.23/1.51  
% 7.23/1.51  abstr_ref_over_cycles:                  0
% 7.23/1.51  abstr_ref_under_cycles:                 0
% 7.23/1.51  gc_basic_clause_elim:                   0
% 7.23/1.51  forced_gc_time:                         0
% 7.23/1.51  parsing_time:                           0.022
% 7.23/1.51  unif_index_cands_time:                  0.
% 7.23/1.51  unif_index_add_time:                    0.
% 7.23/1.51  orderings_time:                         0.
% 7.23/1.51  out_proof_time:                         0.011
% 7.23/1.51  total_time:                             0.556
% 7.23/1.51  num_of_symbols:                         45
% 7.23/1.51  num_of_terms:                           12540
% 7.23/1.51  
% 7.23/1.51  ------ Preprocessing
% 7.23/1.51  
% 7.23/1.51  num_of_splits:                          0
% 7.23/1.51  num_of_split_atoms:                     0
% 7.23/1.51  num_of_reused_defs:                     0
% 7.23/1.51  num_eq_ax_congr_red:                    16
% 7.23/1.51  num_of_sem_filtered_clauses:            1
% 7.23/1.51  num_of_subtypes:                        0
% 7.23/1.51  monotx_restored_types:                  0
% 7.23/1.51  sat_num_of_epr_types:                   0
% 7.23/1.51  sat_num_of_non_cyclic_types:            0
% 7.23/1.51  sat_guarded_non_collapsed_types:        0
% 7.23/1.51  num_pure_diseq_elim:                    0
% 7.23/1.51  simp_replaced_by:                       0
% 7.23/1.51  res_preprocessed:                       107
% 7.23/1.51  prep_upred:                             0
% 7.23/1.51  prep_unflattend:                        4
% 7.23/1.51  smt_new_axioms:                         0
% 7.23/1.51  pred_elim_cands:                        3
% 7.23/1.51  pred_elim:                              0
% 7.23/1.51  pred_elim_cl:                           0
% 7.23/1.51  pred_elim_cycles:                       1
% 7.23/1.51  merged_defs:                            0
% 7.23/1.51  merged_defs_ncl:                        0
% 7.23/1.51  bin_hyper_res:                          0
% 7.23/1.51  prep_cycles:                            3
% 7.23/1.51  pred_elim_time:                         0.001
% 7.23/1.51  splitting_time:                         0.
% 7.23/1.51  sem_filter_time:                        0.
% 7.23/1.51  monotx_time:                            0.001
% 7.23/1.51  subtype_inf_time:                       0.
% 7.23/1.51  
% 7.23/1.51  ------ Problem properties
% 7.23/1.51  
% 7.23/1.51  clauses:                                30
% 7.23/1.51  conjectures:                            3
% 7.23/1.51  epr:                                    3
% 7.23/1.51  horn:                                   21
% 7.23/1.51  ground:                                 3
% 7.23/1.51  unary:                                  15
% 7.23/1.51  binary:                                 8
% 7.23/1.51  lits:                                   55
% 7.23/1.51  lits_eq:                                29
% 7.23/1.51  fd_pure:                                0
% 7.23/1.51  fd_pseudo:                              0
% 7.23/1.51  fd_cond:                                1
% 7.23/1.51  fd_pseudo_cond:                         6
% 7.23/1.51  ac_symbols:                             0
% 7.23/1.51  
% 7.23/1.51  ------ Propositional Solver
% 7.23/1.51  
% 7.23/1.51  prop_solver_calls:                      23
% 7.23/1.51  prop_fast_solver_calls:                 903
% 7.23/1.51  smt_solver_calls:                       0
% 7.23/1.51  smt_fast_solver_calls:                  0
% 7.23/1.51  prop_num_of_clauses:                    4326
% 7.23/1.51  prop_preprocess_simplified:             8613
% 7.23/1.51  prop_fo_subsumed:                       38
% 7.23/1.51  prop_solver_time:                       0.
% 7.23/1.51  smt_solver_time:                        0.
% 7.23/1.51  smt_fast_solver_time:                   0.
% 7.23/1.51  prop_fast_solver_time:                  0.
% 7.23/1.51  prop_unsat_core_time:                   0.
% 7.23/1.51  
% 7.23/1.51  ------ QBF
% 7.23/1.51  
% 7.23/1.51  qbf_q_res:                              0
% 7.23/1.51  qbf_num_tautologies:                    0
% 7.23/1.51  qbf_prep_cycles:                        0
% 7.23/1.51  
% 7.23/1.51  ------ BMC1
% 7.23/1.51  
% 7.23/1.51  bmc1_current_bound:                     -1
% 7.23/1.51  bmc1_last_solved_bound:                 -1
% 7.23/1.51  bmc1_unsat_core_size:                   -1
% 7.23/1.51  bmc1_unsat_core_parents_size:           -1
% 7.23/1.51  bmc1_merge_next_fun:                    0
% 7.23/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.23/1.51  
% 7.23/1.51  ------ Instantiation
% 7.23/1.51  
% 7.23/1.51  inst_num_of_clauses:                    1026
% 7.23/1.51  inst_num_in_passive:                    361
% 7.23/1.51  inst_num_in_active:                     368
% 7.23/1.51  inst_num_in_unprocessed:                297
% 7.23/1.51  inst_num_of_loops:                      520
% 7.23/1.51  inst_num_of_learning_restarts:          0
% 7.23/1.51  inst_num_moves_active_passive:          151
% 7.23/1.51  inst_lit_activity:                      0
% 7.23/1.51  inst_lit_activity_moves:                0
% 7.23/1.51  inst_num_tautologies:                   0
% 7.23/1.51  inst_num_prop_implied:                  0
% 7.23/1.51  inst_num_existing_simplified:           0
% 7.23/1.51  inst_num_eq_res_simplified:             0
% 7.23/1.51  inst_num_child_elim:                    0
% 7.23/1.51  inst_num_of_dismatching_blockings:      735
% 7.23/1.51  inst_num_of_non_proper_insts:           1104
% 7.23/1.51  inst_num_of_duplicates:                 0
% 7.23/1.51  inst_inst_num_from_inst_to_res:         0
% 7.23/1.51  inst_dismatching_checking_time:         0.
% 7.23/1.51  
% 7.23/1.51  ------ Resolution
% 7.23/1.51  
% 7.23/1.51  res_num_of_clauses:                     0
% 7.23/1.51  res_num_in_passive:                     0
% 7.23/1.51  res_num_in_active:                      0
% 7.23/1.51  res_num_of_loops:                       110
% 7.23/1.51  res_forward_subset_subsumed:            167
% 7.23/1.51  res_backward_subset_subsumed:           0
% 7.23/1.51  res_forward_subsumed:                   0
% 7.23/1.51  res_backward_subsumed:                  0
% 7.23/1.51  res_forward_subsumption_resolution:     0
% 7.23/1.51  res_backward_subsumption_resolution:    0
% 7.23/1.51  res_clause_to_clause_subsumption:       4132
% 7.23/1.51  res_orphan_elimination:                 0
% 7.23/1.51  res_tautology_del:                      28
% 7.23/1.51  res_num_eq_res_simplified:              0
% 7.23/1.51  res_num_sel_changes:                    0
% 7.23/1.51  res_moves_from_active_to_pass:          0
% 7.23/1.51  
% 7.23/1.51  ------ Superposition
% 7.23/1.51  
% 7.23/1.51  sup_time_total:                         0.
% 7.23/1.51  sup_time_generating:                    0.
% 7.23/1.51  sup_time_sim_full:                      0.
% 7.23/1.51  sup_time_sim_immed:                     0.
% 7.23/1.51  
% 7.23/1.51  sup_num_of_clauses:                     195
% 7.23/1.51  sup_num_in_active:                      50
% 7.23/1.51  sup_num_in_passive:                     145
% 7.23/1.51  sup_num_of_loops:                       102
% 7.23/1.51  sup_fw_superposition:                   890
% 7.23/1.51  sup_bw_superposition:                   350
% 7.23/1.51  sup_immediate_simplified:               340
% 7.23/1.51  sup_given_eliminated:                   3
% 7.23/1.51  comparisons_done:                       0
% 7.23/1.51  comparisons_avoided:                    165
% 7.23/1.51  
% 7.23/1.51  ------ Simplifications
% 7.23/1.51  
% 7.23/1.51  
% 7.23/1.51  sim_fw_subset_subsumed:                 37
% 7.23/1.51  sim_bw_subset_subsumed:                 362
% 7.23/1.51  sim_fw_subsumed:                        72
% 7.23/1.51  sim_bw_subsumed:                        21
% 7.23/1.51  sim_fw_subsumption_res:                 1
% 7.23/1.51  sim_bw_subsumption_res:                 0
% 7.23/1.51  sim_tautology_del:                      27
% 7.23/1.51  sim_eq_tautology_del:                   155
% 7.23/1.51  sim_eq_res_simp:                        0
% 7.23/1.51  sim_fw_demodulated:                     199
% 7.23/1.51  sim_bw_demodulated:                     21
% 7.23/1.51  sim_light_normalised:                   30
% 7.23/1.51  sim_joinable_taut:                      0
% 7.23/1.51  sim_joinable_simp:                      0
% 7.23/1.51  sim_ac_normalised:                      0
% 7.23/1.51  sim_smt_subsumption:                    0
% 7.23/1.51  
%------------------------------------------------------------------------------
