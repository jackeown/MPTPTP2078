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

% Result     : Theorem 7.29s
% Output     : CNFRefutation 7.29s
% Verified   : 
% Statistics : Number of formulae       :  159 (2309 expanded)
%              Number of clauses        :   76 ( 190 expanded)
%              Number of leaves         :   21 ( 696 expanded)
%              Depth                    :   25
%              Number of atoms          :  439 (5234 expanded)
%              Number of equality atoms :  349 (4267 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f21])).

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
    inference(nnf_transformation,[],[f31])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

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

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f69,f85])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f68,f86])).

fof(f88,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f67,f87])).

fof(f89,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f88])).

fof(f90,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f65,f89])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f79,f89,f90])).

fof(f123,plain,(
    ! [X2,X1] : r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f111])).

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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f32,f46])).

fof(f82,plain,(
    r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(cnf_transformation,[],[f47])).

fof(f114,plain,(
    r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(definition_unfolding,[],[f82,f89,f89])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f77,f89,f90,f90,f89])).

fof(f83,plain,(
    sK3 != sK5 ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f11])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f103,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f59,f89])).

fof(f119,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f103])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f102,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f60,f89])).

fof(f117,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f102])).

fof(f118,plain,(
    ! [X4,X1] : r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f117])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f61,f89])).

fof(f115,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f101])).

fof(f116,plain,(
    ! [X4,X0] : r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f115])).

fof(f84,plain,(
    sK3 != sK6 ),
    inference(cnf_transformation,[],[f47])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(flattening,[],[f42])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | r2_hidden(X1,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | r2_hidden(X1,X2)
      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f74,f89,f90])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f78,f89])).

fof(f124,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f112])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f91,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f53,f56])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f92,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f48,f56,f56])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f49,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f93,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f49,f56])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f73,f89,f90])).

cnf(c_23,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_689,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_686,plain,
    ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_25,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_687,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X2
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1164,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_686,c_687])).

cnf(c_1583,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = X0
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1164,c_687])).

cnf(c_2396,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_689,c_1583])).

cnf(c_4160,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2396,c_1164])).

cnf(c_27,negated_conjecture,
    ( sK3 != sK5 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_55,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_58,plain,
    ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_294,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_870,plain,
    ( sK5 != X0
    | sK3 != X0
    | sK3 = sK5 ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_871,plain,
    ( sK5 != sK3
    | sK3 = sK5
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_870])).

cnf(c_982,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
    | sK5 = X0
    | sK5 = X1 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_983,plain,
    ( sK5 = X0
    | sK5 = X1
    | r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_982])).

cnf(c_985,plain,
    ( sK5 = sK3
    | r2_hidden(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_983])).

cnf(c_13,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_699,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4155,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
    | r2_hidden(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2396,c_699])).

cnf(c_4368,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4160,c_27,c_55,c_58,c_871,c_985,c_4155])).

cnf(c_4369,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4368])).

cnf(c_4377,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = X0
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = X0
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = X0
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4369,c_687])).

cnf(c_6683,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_689,c_4377])).

cnf(c_26,negated_conjecture,
    ( sK3 != sK6 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_868,plain,
    ( sK6 != X0
    | sK3 != X0
    | sK3 = sK6 ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_869,plain,
    ( sK6 != sK3
    | sK3 = sK6
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_868])).

cnf(c_697,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10420,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK5 = X0
    | r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1164,c_697])).

cnf(c_11342,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK4 = sK5 ),
    inference(superposition,[status(thm)],[c_699,c_10420])).

cnf(c_698,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11343,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK5 = sK3 ),
    inference(superposition,[status(thm)],[c_698,c_10420])).

cnf(c_11394,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11342,c_27,c_55,c_58,c_871,c_11343])).

cnf(c_11395,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_11394])).

cnf(c_19,plain,
    ( r2_hidden(X0,X1)
    | X0 = X2
    | k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_693,plain,
    ( X0 = X1
    | k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),X2) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | r2_hidden(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11405,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),X0) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | sK5 = sK6
    | r2_hidden(sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11395,c_693])).

cnf(c_11408,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK5 = X0
    | sK6 = X0
    | r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11395,c_697])).

cnf(c_14569,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK5 = sK3
    | sK6 = sK3 ),
    inference(superposition,[status(thm)],[c_698,c_11408])).

cnf(c_14629,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11405,c_27,c_26,c_55,c_58,c_869,c_871,c_14569])).

cnf(c_14630,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_14629])).

cnf(c_14642,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK6 = X0
    | r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14630,c_697])).

cnf(c_14684,plain,
    ( ~ r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK6 = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14642])).

cnf(c_14686,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK6 = sK3 ),
    inference(instantiation,[status(thm)],[c_14684])).

cnf(c_1153,plain,
    ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_20697,plain,
    ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1153])).

cnf(c_21192,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6683,c_26,c_55,c_58,c_869,c_14686,c_20697])).

cnf(c_21285,plain,
    ( r2_hidden(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_21192,c_698])).

cnf(c_24,plain,
    ( r1_tarski(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_688,plain,
    ( r1_tarski(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_704,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2608,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_688,c_704])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_17676,plain,
    ( k4_xboole_0(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2608,c_0])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_17862,plain,
    ( k4_xboole_0(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_17676,c_8])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1169,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_18164,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_17862,c_1169])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_995,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_1005,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_995])).

cnf(c_18226,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k1_xboole_0) = k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_18164,c_1005])).

cnf(c_18227,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k1_xboole_0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(demodulation,[status(thm)],[c_18226,c_8])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_692,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_18932,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_18227,c_692])).

cnf(c_18980,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(sK3,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_18932])).

cnf(c_300,plain,
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

cnf(c_306,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21285,c_18980,c_306,c_58,c_55])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.12/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/1.50  
% 7.12/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.12/1.50  
% 7.12/1.50  ------  iProver source info
% 7.12/1.50  
% 7.12/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.12/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.12/1.50  git: non_committed_changes: false
% 7.12/1.50  git: last_make_outside_of_git: false
% 7.12/1.50  
% 7.12/1.50  ------ 
% 7.12/1.50  
% 7.12/1.50  ------ Input Options
% 7.12/1.50  
% 7.12/1.50  --out_options                           all
% 7.12/1.50  --tptp_safe_out                         true
% 7.12/1.50  --problem_path                          ""
% 7.12/1.50  --include_path                          ""
% 7.12/1.50  --clausifier                            res/vclausify_rel
% 7.12/1.50  --clausifier_options                    --mode clausify
% 7.12/1.50  --stdin                                 false
% 7.12/1.50  --stats_out                             all
% 7.12/1.50  
% 7.12/1.50  ------ General Options
% 7.12/1.50  
% 7.12/1.50  --fof                                   false
% 7.12/1.50  --time_out_real                         305.
% 7.12/1.50  --time_out_virtual                      -1.
% 7.12/1.50  --symbol_type_check                     false
% 7.12/1.50  --clausify_out                          false
% 7.12/1.50  --sig_cnt_out                           false
% 7.29/1.50  --trig_cnt_out                          false
% 7.29/1.50  --trig_cnt_out_tolerance                1.
% 7.29/1.50  --trig_cnt_out_sk_spl                   false
% 7.29/1.50  --abstr_cl_out                          false
% 7.29/1.50  
% 7.29/1.50  ------ Global Options
% 7.29/1.50  
% 7.29/1.50  --schedule                              default
% 7.29/1.50  --add_important_lit                     false
% 7.29/1.50  --prop_solver_per_cl                    1000
% 7.29/1.50  --min_unsat_core                        false
% 7.29/1.50  --soft_assumptions                      false
% 7.29/1.50  --soft_lemma_size                       3
% 7.29/1.50  --prop_impl_unit_size                   0
% 7.29/1.50  --prop_impl_unit                        []
% 7.29/1.50  --share_sel_clauses                     true
% 7.29/1.50  --reset_solvers                         false
% 7.29/1.50  --bc_imp_inh                            [conj_cone]
% 7.29/1.50  --conj_cone_tolerance                   3.
% 7.29/1.50  --extra_neg_conj                        none
% 7.29/1.50  --large_theory_mode                     true
% 7.29/1.50  --prolific_symb_bound                   200
% 7.29/1.50  --lt_threshold                          2000
% 7.29/1.50  --clause_weak_htbl                      true
% 7.29/1.50  --gc_record_bc_elim                     false
% 7.29/1.50  
% 7.29/1.50  ------ Preprocessing Options
% 7.29/1.50  
% 7.29/1.50  --preprocessing_flag                    true
% 7.29/1.50  --time_out_prep_mult                    0.1
% 7.29/1.50  --splitting_mode                        input
% 7.29/1.50  --splitting_grd                         true
% 7.29/1.50  --splitting_cvd                         false
% 7.29/1.50  --splitting_cvd_svl                     false
% 7.29/1.50  --splitting_nvd                         32
% 7.29/1.50  --sub_typing                            true
% 7.29/1.50  --prep_gs_sim                           true
% 7.29/1.50  --prep_unflatten                        true
% 7.29/1.50  --prep_res_sim                          true
% 7.29/1.50  --prep_upred                            true
% 7.29/1.50  --prep_sem_filter                       exhaustive
% 7.29/1.50  --prep_sem_filter_out                   false
% 7.29/1.50  --pred_elim                             true
% 7.29/1.50  --res_sim_input                         true
% 7.29/1.50  --eq_ax_congr_red                       true
% 7.29/1.50  --pure_diseq_elim                       true
% 7.29/1.50  --brand_transform                       false
% 7.29/1.50  --non_eq_to_eq                          false
% 7.29/1.50  --prep_def_merge                        true
% 7.29/1.50  --prep_def_merge_prop_impl              false
% 7.29/1.50  --prep_def_merge_mbd                    true
% 7.29/1.50  --prep_def_merge_tr_red                 false
% 7.29/1.50  --prep_def_merge_tr_cl                  false
% 7.29/1.50  --smt_preprocessing                     true
% 7.29/1.50  --smt_ac_axioms                         fast
% 7.29/1.50  --preprocessed_out                      false
% 7.29/1.50  --preprocessed_stats                    false
% 7.29/1.50  
% 7.29/1.50  ------ Abstraction refinement Options
% 7.29/1.50  
% 7.29/1.50  --abstr_ref                             []
% 7.29/1.50  --abstr_ref_prep                        false
% 7.29/1.50  --abstr_ref_until_sat                   false
% 7.29/1.50  --abstr_ref_sig_restrict                funpre
% 7.29/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.29/1.50  --abstr_ref_under                       []
% 7.29/1.50  
% 7.29/1.50  ------ SAT Options
% 7.29/1.50  
% 7.29/1.50  --sat_mode                              false
% 7.29/1.50  --sat_fm_restart_options                ""
% 7.29/1.50  --sat_gr_def                            false
% 7.29/1.50  --sat_epr_types                         true
% 7.29/1.50  --sat_non_cyclic_types                  false
% 7.29/1.50  --sat_finite_models                     false
% 7.29/1.50  --sat_fm_lemmas                         false
% 7.29/1.50  --sat_fm_prep                           false
% 7.29/1.50  --sat_fm_uc_incr                        true
% 7.29/1.50  --sat_out_model                         small
% 7.29/1.50  --sat_out_clauses                       false
% 7.29/1.50  
% 7.29/1.50  ------ QBF Options
% 7.29/1.50  
% 7.29/1.50  --qbf_mode                              false
% 7.29/1.50  --qbf_elim_univ                         false
% 7.29/1.50  --qbf_dom_inst                          none
% 7.29/1.50  --qbf_dom_pre_inst                      false
% 7.29/1.50  --qbf_sk_in                             false
% 7.29/1.50  --qbf_pred_elim                         true
% 7.29/1.50  --qbf_split                             512
% 7.29/1.50  
% 7.29/1.50  ------ BMC1 Options
% 7.29/1.50  
% 7.29/1.50  --bmc1_incremental                      false
% 7.29/1.50  --bmc1_axioms                           reachable_all
% 7.29/1.50  --bmc1_min_bound                        0
% 7.29/1.50  --bmc1_max_bound                        -1
% 7.29/1.50  --bmc1_max_bound_default                -1
% 7.29/1.50  --bmc1_symbol_reachability              true
% 7.29/1.50  --bmc1_property_lemmas                  false
% 7.29/1.50  --bmc1_k_induction                      false
% 7.29/1.50  --bmc1_non_equiv_states                 false
% 7.29/1.50  --bmc1_deadlock                         false
% 7.29/1.50  --bmc1_ucm                              false
% 7.29/1.50  --bmc1_add_unsat_core                   none
% 7.29/1.50  --bmc1_unsat_core_children              false
% 7.29/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.29/1.50  --bmc1_out_stat                         full
% 7.29/1.50  --bmc1_ground_init                      false
% 7.29/1.50  --bmc1_pre_inst_next_state              false
% 7.29/1.50  --bmc1_pre_inst_state                   false
% 7.29/1.50  --bmc1_pre_inst_reach_state             false
% 7.29/1.50  --bmc1_out_unsat_core                   false
% 7.29/1.50  --bmc1_aig_witness_out                  false
% 7.29/1.50  --bmc1_verbose                          false
% 7.29/1.50  --bmc1_dump_clauses_tptp                false
% 7.29/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.29/1.50  --bmc1_dump_file                        -
% 7.29/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.29/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.29/1.50  --bmc1_ucm_extend_mode                  1
% 7.29/1.50  --bmc1_ucm_init_mode                    2
% 7.29/1.50  --bmc1_ucm_cone_mode                    none
% 7.29/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.29/1.50  --bmc1_ucm_relax_model                  4
% 7.29/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.29/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.29/1.50  --bmc1_ucm_layered_model                none
% 7.29/1.50  --bmc1_ucm_max_lemma_size               10
% 7.29/1.50  
% 7.29/1.50  ------ AIG Options
% 7.29/1.50  
% 7.29/1.50  --aig_mode                              false
% 7.29/1.50  
% 7.29/1.50  ------ Instantiation Options
% 7.29/1.50  
% 7.29/1.50  --instantiation_flag                    true
% 7.29/1.50  --inst_sos_flag                         false
% 7.29/1.50  --inst_sos_phase                        true
% 7.29/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.29/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.29/1.50  --inst_lit_sel_side                     num_symb
% 7.29/1.50  --inst_solver_per_active                1400
% 7.29/1.50  --inst_solver_calls_frac                1.
% 7.29/1.50  --inst_passive_queue_type               priority_queues
% 7.29/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.29/1.50  --inst_passive_queues_freq              [25;2]
% 7.29/1.50  --inst_dismatching                      true
% 7.29/1.50  --inst_eager_unprocessed_to_passive     true
% 7.29/1.50  --inst_prop_sim_given                   true
% 7.29/1.50  --inst_prop_sim_new                     false
% 7.29/1.50  --inst_subs_new                         false
% 7.29/1.50  --inst_eq_res_simp                      false
% 7.29/1.50  --inst_subs_given                       false
% 7.29/1.50  --inst_orphan_elimination               true
% 7.29/1.50  --inst_learning_loop_flag               true
% 7.29/1.50  --inst_learning_start                   3000
% 7.29/1.50  --inst_learning_factor                  2
% 7.29/1.50  --inst_start_prop_sim_after_learn       3
% 7.29/1.50  --inst_sel_renew                        solver
% 7.29/1.50  --inst_lit_activity_flag                true
% 7.29/1.50  --inst_restr_to_given                   false
% 7.29/1.50  --inst_activity_threshold               500
% 7.29/1.50  --inst_out_proof                        true
% 7.29/1.50  
% 7.29/1.50  ------ Resolution Options
% 7.29/1.50  
% 7.29/1.50  --resolution_flag                       true
% 7.29/1.50  --res_lit_sel                           adaptive
% 7.29/1.50  --res_lit_sel_side                      none
% 7.29/1.50  --res_ordering                          kbo
% 7.29/1.50  --res_to_prop_solver                    active
% 7.29/1.50  --res_prop_simpl_new                    false
% 7.29/1.50  --res_prop_simpl_given                  true
% 7.29/1.50  --res_passive_queue_type                priority_queues
% 7.29/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.29/1.50  --res_passive_queues_freq               [15;5]
% 7.29/1.50  --res_forward_subs                      full
% 7.29/1.50  --res_backward_subs                     full
% 7.29/1.50  --res_forward_subs_resolution           true
% 7.29/1.50  --res_backward_subs_resolution          true
% 7.29/1.50  --res_orphan_elimination                true
% 7.29/1.50  --res_time_limit                        2.
% 7.29/1.50  --res_out_proof                         true
% 7.29/1.50  
% 7.29/1.50  ------ Superposition Options
% 7.29/1.50  
% 7.29/1.50  --superposition_flag                    true
% 7.29/1.50  --sup_passive_queue_type                priority_queues
% 7.29/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.29/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.29/1.50  --demod_completeness_check              fast
% 7.29/1.50  --demod_use_ground                      true
% 7.29/1.50  --sup_to_prop_solver                    passive
% 7.29/1.50  --sup_prop_simpl_new                    true
% 7.29/1.50  --sup_prop_simpl_given                  true
% 7.29/1.50  --sup_fun_splitting                     false
% 7.29/1.50  --sup_smt_interval                      50000
% 7.29/1.50  
% 7.29/1.50  ------ Superposition Simplification Setup
% 7.29/1.50  
% 7.29/1.50  --sup_indices_passive                   []
% 7.29/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.29/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.29/1.50  --sup_full_bw                           [BwDemod]
% 7.29/1.50  --sup_immed_triv                        [TrivRules]
% 7.29/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.29/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.29/1.50  --sup_immed_bw_main                     []
% 7.29/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.29/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.29/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.29/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.29/1.50  
% 7.29/1.50  ------ Combination Options
% 7.29/1.50  
% 7.29/1.50  --comb_res_mult                         3
% 7.29/1.50  --comb_sup_mult                         2
% 7.29/1.50  --comb_inst_mult                        10
% 7.29/1.50  
% 7.29/1.50  ------ Debug Options
% 7.29/1.50  
% 7.29/1.50  --dbg_backtrace                         false
% 7.29/1.50  --dbg_dump_prop_clauses                 false
% 7.29/1.50  --dbg_dump_prop_clauses_file            -
% 7.29/1.50  --dbg_out_stat                          false
% 7.29/1.50  ------ Parsing...
% 7.29/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.29/1.50  
% 7.29/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.29/1.50  
% 7.29/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.29/1.50  
% 7.29/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.29/1.50  ------ Proving...
% 7.29/1.50  ------ Problem Properties 
% 7.29/1.50  
% 7.29/1.50  
% 7.29/1.50  clauses                                 29
% 7.29/1.50  conjectures                             3
% 7.29/1.50  EPR                                     3
% 7.29/1.50  Horn                                    21
% 7.29/1.50  unary                                   14
% 7.29/1.50  binary                                  8
% 7.29/1.50  lits                                    54
% 7.29/1.50  lits eq                                 27
% 7.29/1.50  fd_pure                                 0
% 7.29/1.50  fd_pseudo                               0
% 7.29/1.50  fd_cond                                 1
% 7.29/1.50  fd_pseudo_cond                          5
% 7.29/1.50  AC symbols                              0
% 7.29/1.50  
% 7.29/1.50  ------ Schedule dynamic 5 is on 
% 7.29/1.50  
% 7.29/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.29/1.50  
% 7.29/1.50  
% 7.29/1.50  ------ 
% 7.29/1.50  Current options:
% 7.29/1.50  ------ 
% 7.29/1.50  
% 7.29/1.50  ------ Input Options
% 7.29/1.50  
% 7.29/1.50  --out_options                           all
% 7.29/1.50  --tptp_safe_out                         true
% 7.29/1.50  --problem_path                          ""
% 7.29/1.50  --include_path                          ""
% 7.29/1.50  --clausifier                            res/vclausify_rel
% 7.29/1.50  --clausifier_options                    --mode clausify
% 7.29/1.50  --stdin                                 false
% 7.29/1.50  --stats_out                             all
% 7.29/1.50  
% 7.29/1.50  ------ General Options
% 7.29/1.50  
% 7.29/1.50  --fof                                   false
% 7.29/1.50  --time_out_real                         305.
% 7.29/1.50  --time_out_virtual                      -1.
% 7.29/1.50  --symbol_type_check                     false
% 7.29/1.50  --clausify_out                          false
% 7.29/1.50  --sig_cnt_out                           false
% 7.29/1.50  --trig_cnt_out                          false
% 7.29/1.50  --trig_cnt_out_tolerance                1.
% 7.29/1.50  --trig_cnt_out_sk_spl                   false
% 7.29/1.50  --abstr_cl_out                          false
% 7.29/1.50  
% 7.29/1.50  ------ Global Options
% 7.29/1.50  
% 7.29/1.50  --schedule                              default
% 7.29/1.50  --add_important_lit                     false
% 7.29/1.50  --prop_solver_per_cl                    1000
% 7.29/1.50  --min_unsat_core                        false
% 7.29/1.50  --soft_assumptions                      false
% 7.29/1.50  --soft_lemma_size                       3
% 7.29/1.50  --prop_impl_unit_size                   0
% 7.29/1.50  --prop_impl_unit                        []
% 7.29/1.50  --share_sel_clauses                     true
% 7.29/1.50  --reset_solvers                         false
% 7.29/1.50  --bc_imp_inh                            [conj_cone]
% 7.29/1.50  --conj_cone_tolerance                   3.
% 7.29/1.50  --extra_neg_conj                        none
% 7.29/1.50  --large_theory_mode                     true
% 7.29/1.50  --prolific_symb_bound                   200
% 7.29/1.50  --lt_threshold                          2000
% 7.29/1.50  --clause_weak_htbl                      true
% 7.29/1.50  --gc_record_bc_elim                     false
% 7.29/1.50  
% 7.29/1.50  ------ Preprocessing Options
% 7.29/1.50  
% 7.29/1.50  --preprocessing_flag                    true
% 7.29/1.50  --time_out_prep_mult                    0.1
% 7.29/1.50  --splitting_mode                        input
% 7.29/1.50  --splitting_grd                         true
% 7.29/1.50  --splitting_cvd                         false
% 7.29/1.50  --splitting_cvd_svl                     false
% 7.29/1.50  --splitting_nvd                         32
% 7.29/1.50  --sub_typing                            true
% 7.29/1.50  --prep_gs_sim                           true
% 7.29/1.50  --prep_unflatten                        true
% 7.29/1.50  --prep_res_sim                          true
% 7.29/1.50  --prep_upred                            true
% 7.29/1.50  --prep_sem_filter                       exhaustive
% 7.29/1.50  --prep_sem_filter_out                   false
% 7.29/1.50  --pred_elim                             true
% 7.29/1.50  --res_sim_input                         true
% 7.29/1.50  --eq_ax_congr_red                       true
% 7.29/1.50  --pure_diseq_elim                       true
% 7.29/1.50  --brand_transform                       false
% 7.29/1.50  --non_eq_to_eq                          false
% 7.29/1.50  --prep_def_merge                        true
% 7.29/1.50  --prep_def_merge_prop_impl              false
% 7.29/1.50  --prep_def_merge_mbd                    true
% 7.29/1.50  --prep_def_merge_tr_red                 false
% 7.29/1.50  --prep_def_merge_tr_cl                  false
% 7.29/1.50  --smt_preprocessing                     true
% 7.29/1.50  --smt_ac_axioms                         fast
% 7.29/1.50  --preprocessed_out                      false
% 7.29/1.50  --preprocessed_stats                    false
% 7.29/1.50  
% 7.29/1.50  ------ Abstraction refinement Options
% 7.29/1.50  
% 7.29/1.50  --abstr_ref                             []
% 7.29/1.50  --abstr_ref_prep                        false
% 7.29/1.50  --abstr_ref_until_sat                   false
% 7.29/1.50  --abstr_ref_sig_restrict                funpre
% 7.29/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.29/1.50  --abstr_ref_under                       []
% 7.29/1.50  
% 7.29/1.50  ------ SAT Options
% 7.29/1.50  
% 7.29/1.50  --sat_mode                              false
% 7.29/1.50  --sat_fm_restart_options                ""
% 7.29/1.50  --sat_gr_def                            false
% 7.29/1.50  --sat_epr_types                         true
% 7.29/1.50  --sat_non_cyclic_types                  false
% 7.29/1.50  --sat_finite_models                     false
% 7.29/1.50  --sat_fm_lemmas                         false
% 7.29/1.50  --sat_fm_prep                           false
% 7.29/1.50  --sat_fm_uc_incr                        true
% 7.29/1.50  --sat_out_model                         small
% 7.29/1.50  --sat_out_clauses                       false
% 7.29/1.50  
% 7.29/1.50  ------ QBF Options
% 7.29/1.50  
% 7.29/1.50  --qbf_mode                              false
% 7.29/1.50  --qbf_elim_univ                         false
% 7.29/1.50  --qbf_dom_inst                          none
% 7.29/1.50  --qbf_dom_pre_inst                      false
% 7.29/1.50  --qbf_sk_in                             false
% 7.29/1.50  --qbf_pred_elim                         true
% 7.29/1.50  --qbf_split                             512
% 7.29/1.50  
% 7.29/1.50  ------ BMC1 Options
% 7.29/1.50  
% 7.29/1.50  --bmc1_incremental                      false
% 7.29/1.50  --bmc1_axioms                           reachable_all
% 7.29/1.50  --bmc1_min_bound                        0
% 7.29/1.50  --bmc1_max_bound                        -1
% 7.29/1.50  --bmc1_max_bound_default                -1
% 7.29/1.50  --bmc1_symbol_reachability              true
% 7.29/1.50  --bmc1_property_lemmas                  false
% 7.29/1.50  --bmc1_k_induction                      false
% 7.29/1.50  --bmc1_non_equiv_states                 false
% 7.29/1.50  --bmc1_deadlock                         false
% 7.29/1.50  --bmc1_ucm                              false
% 7.29/1.50  --bmc1_add_unsat_core                   none
% 7.29/1.50  --bmc1_unsat_core_children              false
% 7.29/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.29/1.50  --bmc1_out_stat                         full
% 7.29/1.50  --bmc1_ground_init                      false
% 7.29/1.50  --bmc1_pre_inst_next_state              false
% 7.29/1.50  --bmc1_pre_inst_state                   false
% 7.29/1.50  --bmc1_pre_inst_reach_state             false
% 7.29/1.50  --bmc1_out_unsat_core                   false
% 7.29/1.50  --bmc1_aig_witness_out                  false
% 7.29/1.50  --bmc1_verbose                          false
% 7.29/1.50  --bmc1_dump_clauses_tptp                false
% 7.29/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.29/1.50  --bmc1_dump_file                        -
% 7.29/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.29/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.29/1.50  --bmc1_ucm_extend_mode                  1
% 7.29/1.50  --bmc1_ucm_init_mode                    2
% 7.29/1.50  --bmc1_ucm_cone_mode                    none
% 7.29/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.29/1.50  --bmc1_ucm_relax_model                  4
% 7.29/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.29/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.29/1.50  --bmc1_ucm_layered_model                none
% 7.29/1.50  --bmc1_ucm_max_lemma_size               10
% 7.29/1.50  
% 7.29/1.50  ------ AIG Options
% 7.29/1.50  
% 7.29/1.50  --aig_mode                              false
% 7.29/1.50  
% 7.29/1.50  ------ Instantiation Options
% 7.29/1.50  
% 7.29/1.50  --instantiation_flag                    true
% 7.29/1.50  --inst_sos_flag                         false
% 7.29/1.50  --inst_sos_phase                        true
% 7.29/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.29/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.29/1.50  --inst_lit_sel_side                     none
% 7.29/1.50  --inst_solver_per_active                1400
% 7.29/1.50  --inst_solver_calls_frac                1.
% 7.29/1.50  --inst_passive_queue_type               priority_queues
% 7.29/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.29/1.50  --inst_passive_queues_freq              [25;2]
% 7.29/1.50  --inst_dismatching                      true
% 7.29/1.50  --inst_eager_unprocessed_to_passive     true
% 7.29/1.50  --inst_prop_sim_given                   true
% 7.29/1.50  --inst_prop_sim_new                     false
% 7.29/1.50  --inst_subs_new                         false
% 7.29/1.50  --inst_eq_res_simp                      false
% 7.29/1.50  --inst_subs_given                       false
% 7.29/1.50  --inst_orphan_elimination               true
% 7.29/1.50  --inst_learning_loop_flag               true
% 7.29/1.50  --inst_learning_start                   3000
% 7.29/1.50  --inst_learning_factor                  2
% 7.29/1.50  --inst_start_prop_sim_after_learn       3
% 7.29/1.50  --inst_sel_renew                        solver
% 7.29/1.50  --inst_lit_activity_flag                true
% 7.29/1.50  --inst_restr_to_given                   false
% 7.29/1.50  --inst_activity_threshold               500
% 7.29/1.50  --inst_out_proof                        true
% 7.29/1.50  
% 7.29/1.50  ------ Resolution Options
% 7.29/1.50  
% 7.29/1.50  --resolution_flag                       false
% 7.29/1.50  --res_lit_sel                           adaptive
% 7.29/1.50  --res_lit_sel_side                      none
% 7.29/1.50  --res_ordering                          kbo
% 7.29/1.50  --res_to_prop_solver                    active
% 7.29/1.50  --res_prop_simpl_new                    false
% 7.29/1.50  --res_prop_simpl_given                  true
% 7.29/1.50  --res_passive_queue_type                priority_queues
% 7.29/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.29/1.50  --res_passive_queues_freq               [15;5]
% 7.29/1.50  --res_forward_subs                      full
% 7.29/1.50  --res_backward_subs                     full
% 7.29/1.50  --res_forward_subs_resolution           true
% 7.29/1.50  --res_backward_subs_resolution          true
% 7.29/1.50  --res_orphan_elimination                true
% 7.29/1.50  --res_time_limit                        2.
% 7.29/1.50  --res_out_proof                         true
% 7.29/1.50  
% 7.29/1.50  ------ Superposition Options
% 7.29/1.50  
% 7.29/1.50  --superposition_flag                    true
% 7.29/1.50  --sup_passive_queue_type                priority_queues
% 7.29/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.29/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.29/1.50  --demod_completeness_check              fast
% 7.29/1.50  --demod_use_ground                      true
% 7.29/1.50  --sup_to_prop_solver                    passive
% 7.29/1.50  --sup_prop_simpl_new                    true
% 7.29/1.50  --sup_prop_simpl_given                  true
% 7.29/1.50  --sup_fun_splitting                     false
% 7.29/1.50  --sup_smt_interval                      50000
% 7.29/1.50  
% 7.29/1.50  ------ Superposition Simplification Setup
% 7.29/1.50  
% 7.29/1.50  --sup_indices_passive                   []
% 7.29/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.29/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.29/1.50  --sup_full_bw                           [BwDemod]
% 7.29/1.50  --sup_immed_triv                        [TrivRules]
% 7.29/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.29/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.29/1.50  --sup_immed_bw_main                     []
% 7.29/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.29/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.29/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.29/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.29/1.50  
% 7.29/1.50  ------ Combination Options
% 7.29/1.50  
% 7.29/1.50  --comb_res_mult                         3
% 7.29/1.50  --comb_sup_mult                         2
% 7.29/1.50  --comb_inst_mult                        10
% 7.29/1.50  
% 7.29/1.50  ------ Debug Options
% 7.29/1.50  
% 7.29/1.50  --dbg_backtrace                         false
% 7.29/1.50  --dbg_dump_prop_clauses                 false
% 7.29/1.50  --dbg_dump_prop_clauses_file            -
% 7.29/1.50  --dbg_out_stat                          false
% 7.29/1.50  
% 7.29/1.50  
% 7.29/1.50  
% 7.29/1.50  
% 7.29/1.50  ------ Proving...
% 7.29/1.50  
% 7.29/1.50  
% 7.29/1.50  % SZS status Theorem for theBenchmark.p
% 7.29/1.50  
% 7.29/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.29/1.50  
% 7.29/1.50  fof(f21,axiom,(
% 7.29/1.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 7.29/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f31,plain,(
% 7.29/1.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.29/1.50    inference(ennf_transformation,[],[f21])).
% 7.29/1.50  
% 7.29/1.50  fof(f44,plain,(
% 7.29/1.50    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 7.29/1.50    inference(nnf_transformation,[],[f31])).
% 7.29/1.50  
% 7.29/1.50  fof(f45,plain,(
% 7.29/1.50    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 7.29/1.50    inference(flattening,[],[f44])).
% 7.29/1.50  
% 7.29/1.50  fof(f79,plain,(
% 7.29/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 7.29/1.50    inference(cnf_transformation,[],[f45])).
% 7.29/1.50  
% 7.29/1.50  fof(f12,axiom,(
% 7.29/1.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.29/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f65,plain,(
% 7.29/1.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f12])).
% 7.29/1.50  
% 7.29/1.50  fof(f13,axiom,(
% 7.29/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.29/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f66,plain,(
% 7.29/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f13])).
% 7.29/1.50  
% 7.29/1.50  fof(f14,axiom,(
% 7.29/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.29/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f67,plain,(
% 7.29/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f14])).
% 7.29/1.50  
% 7.29/1.50  fof(f15,axiom,(
% 7.29/1.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.29/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f68,plain,(
% 7.29/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f15])).
% 7.29/1.50  
% 7.29/1.50  fof(f16,axiom,(
% 7.29/1.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.29/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f69,plain,(
% 7.29/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f16])).
% 7.29/1.50  
% 7.29/1.50  fof(f17,axiom,(
% 7.29/1.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.29/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f70,plain,(
% 7.29/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f17])).
% 7.29/1.50  
% 7.29/1.50  fof(f18,axiom,(
% 7.29/1.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.29/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f71,plain,(
% 7.29/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f18])).
% 7.29/1.50  
% 7.29/1.50  fof(f85,plain,(
% 7.29/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.29/1.50    inference(definition_unfolding,[],[f70,f71])).
% 7.29/1.50  
% 7.29/1.50  fof(f86,plain,(
% 7.29/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.29/1.50    inference(definition_unfolding,[],[f69,f85])).
% 7.29/1.50  
% 7.29/1.50  fof(f87,plain,(
% 7.29/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.29/1.50    inference(definition_unfolding,[],[f68,f86])).
% 7.29/1.50  
% 7.29/1.50  fof(f88,plain,(
% 7.29/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.29/1.50    inference(definition_unfolding,[],[f67,f87])).
% 7.29/1.50  
% 7.29/1.50  fof(f89,plain,(
% 7.29/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.29/1.50    inference(definition_unfolding,[],[f66,f88])).
% 7.29/1.50  
% 7.29/1.50  fof(f90,plain,(
% 7.29/1.50    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.29/1.50    inference(definition_unfolding,[],[f65,f89])).
% 7.29/1.50  
% 7.29/1.50  fof(f111,plain,(
% 7.29/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0) )),
% 7.29/1.50    inference(definition_unfolding,[],[f79,f89,f90])).
% 7.29/1.50  
% 7.29/1.50  fof(f123,plain,(
% 7.29/1.50    ( ! [X2,X1] : (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 7.29/1.50    inference(equality_resolution,[],[f111])).
% 7.29/1.50  
% 7.29/1.50  fof(f22,conjecture,(
% 7.29/1.50    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 7.29/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f23,negated_conjecture,(
% 7.29/1.50    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 7.29/1.50    inference(negated_conjecture,[],[f22])).
% 7.29/1.50  
% 7.29/1.50  fof(f32,plain,(
% 7.29/1.50    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 7.29/1.50    inference(ennf_transformation,[],[f23])).
% 7.29/1.50  
% 7.29/1.50  fof(f46,plain,(
% 7.29/1.50    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK3 != sK6 & sK3 != sK5 & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)))),
% 7.29/1.50    introduced(choice_axiom,[])).
% 7.29/1.50  
% 7.29/1.50  fof(f47,plain,(
% 7.29/1.50    sK3 != sK6 & sK3 != sK5 & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))),
% 7.29/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f32,f46])).
% 7.29/1.50  
% 7.29/1.50  fof(f82,plain,(
% 7.29/1.50    r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))),
% 7.29/1.50    inference(cnf_transformation,[],[f47])).
% 7.29/1.50  
% 7.29/1.50  fof(f114,plain,(
% 7.29/1.50    r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))),
% 7.29/1.50    inference(definition_unfolding,[],[f82,f89,f89])).
% 7.29/1.50  
% 7.29/1.50  fof(f77,plain,(
% 7.29/1.50    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 7.29/1.50    inference(cnf_transformation,[],[f45])).
% 7.29/1.50  
% 7.29/1.50  fof(f113,plain,(
% 7.29/1.50    ( ! [X2,X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0 | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 7.29/1.50    inference(definition_unfolding,[],[f77,f89,f90,f90,f89])).
% 7.29/1.50  
% 7.29/1.50  fof(f83,plain,(
% 7.29/1.50    sK3 != sK5),
% 7.29/1.50    inference(cnf_transformation,[],[f47])).
% 7.29/1.50  
% 7.29/1.50  fof(f11,axiom,(
% 7.29/1.50    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.29/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f37,plain,(
% 7.29/1.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.29/1.50    inference(nnf_transformation,[],[f11])).
% 7.29/1.50  
% 7.29/1.50  fof(f38,plain,(
% 7.29/1.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.29/1.50    inference(flattening,[],[f37])).
% 7.29/1.50  
% 7.29/1.50  fof(f39,plain,(
% 7.29/1.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.29/1.50    inference(rectify,[],[f38])).
% 7.29/1.50  
% 7.29/1.50  fof(f40,plain,(
% 7.29/1.50    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 7.29/1.50    introduced(choice_axiom,[])).
% 7.29/1.50  
% 7.29/1.50  fof(f41,plain,(
% 7.29/1.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.29/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 7.29/1.50  
% 7.29/1.50  fof(f59,plain,(
% 7.29/1.50    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 7.29/1.50    inference(cnf_transformation,[],[f41])).
% 7.29/1.50  
% 7.29/1.50  fof(f103,plain,(
% 7.29/1.50    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 7.29/1.50    inference(definition_unfolding,[],[f59,f89])).
% 7.29/1.50  
% 7.29/1.50  fof(f119,plain,(
% 7.29/1.50    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.29/1.50    inference(equality_resolution,[],[f103])).
% 7.29/1.50  
% 7.29/1.50  fof(f60,plain,(
% 7.29/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.29/1.50    inference(cnf_transformation,[],[f41])).
% 7.29/1.50  
% 7.29/1.50  fof(f102,plain,(
% 7.29/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 7.29/1.50    inference(definition_unfolding,[],[f60,f89])).
% 7.29/1.50  
% 7.29/1.50  fof(f117,plain,(
% 7.29/1.50    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1) != X2) )),
% 7.29/1.50    inference(equality_resolution,[],[f102])).
% 7.29/1.50  
% 7.29/1.50  fof(f118,plain,(
% 7.29/1.50    ( ! [X4,X1] : (r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1))) )),
% 7.29/1.50    inference(equality_resolution,[],[f117])).
% 7.29/1.50  
% 7.29/1.50  fof(f61,plain,(
% 7.29/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.29/1.50    inference(cnf_transformation,[],[f41])).
% 7.29/1.50  
% 7.29/1.50  fof(f101,plain,(
% 7.29/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 7.29/1.50    inference(definition_unfolding,[],[f61,f89])).
% 7.29/1.50  
% 7.29/1.50  fof(f115,plain,(
% 7.29/1.50    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X4) != X2) )),
% 7.29/1.50    inference(equality_resolution,[],[f101])).
% 7.29/1.50  
% 7.29/1.50  fof(f116,plain,(
% 7.29/1.50    ( ! [X4,X0] : (r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X4))) )),
% 7.29/1.50    inference(equality_resolution,[],[f115])).
% 7.29/1.50  
% 7.29/1.50  fof(f84,plain,(
% 7.29/1.50    sK3 != sK6),
% 7.29/1.50    inference(cnf_transformation,[],[f47])).
% 7.29/1.50  
% 7.29/1.50  fof(f20,axiom,(
% 7.29/1.50    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 7.29/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f42,plain,(
% 7.29/1.50    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 7.29/1.50    inference(nnf_transformation,[],[f20])).
% 7.29/1.50  
% 7.29/1.50  fof(f43,plain,(
% 7.29/1.50    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 7.29/1.50    inference(flattening,[],[f42])).
% 7.29/1.50  
% 7.29/1.50  fof(f74,plain,(
% 7.29/1.50    ( ! [X2,X0,X1] : (X0 = X1 | r2_hidden(X1,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f43])).
% 7.29/1.50  
% 7.29/1.50  fof(f107,plain,(
% 7.29/1.50    ( ! [X2,X0,X1] : (X0 = X1 | r2_hidden(X1,X2) | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.29/1.50    inference(definition_unfolding,[],[f74,f89,f90])).
% 7.29/1.50  
% 7.29/1.50  fof(f78,plain,(
% 7.29/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_xboole_0 != X0) )),
% 7.29/1.50    inference(cnf_transformation,[],[f45])).
% 7.29/1.50  
% 7.29/1.50  fof(f112,plain,(
% 7.29/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k1_xboole_0 != X0) )),
% 7.29/1.50    inference(definition_unfolding,[],[f78,f89])).
% 7.29/1.50  
% 7.29/1.50  fof(f124,plain,(
% 7.29/1.50    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 7.29/1.50    inference(equality_resolution,[],[f112])).
% 7.29/1.50  
% 7.29/1.50  fof(f7,axiom,(
% 7.29/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.29/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f29,plain,(
% 7.29/1.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.29/1.50    inference(ennf_transformation,[],[f7])).
% 7.29/1.50  
% 7.29/1.50  fof(f55,plain,(
% 7.29/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f29])).
% 7.29/1.50  
% 7.29/1.50  fof(f8,axiom,(
% 7.29/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.29/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f56,plain,(
% 7.29/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.29/1.50    inference(cnf_transformation,[],[f8])).
% 7.29/1.50  
% 7.29/1.50  fof(f97,plain,(
% 7.29/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.29/1.50    inference(definition_unfolding,[],[f55,f56])).
% 7.29/1.50  
% 7.29/1.50  fof(f5,axiom,(
% 7.29/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.29/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f53,plain,(
% 7.29/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.29/1.50    inference(cnf_transformation,[],[f5])).
% 7.29/1.50  
% 7.29/1.50  fof(f91,plain,(
% 7.29/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.29/1.50    inference(definition_unfolding,[],[f53,f56])).
% 7.29/1.50  
% 7.29/1.50  fof(f9,axiom,(
% 7.29/1.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.29/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f57,plain,(
% 7.29/1.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.29/1.50    inference(cnf_transformation,[],[f9])).
% 7.29/1.50  
% 7.29/1.50  fof(f1,axiom,(
% 7.29/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.29/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f48,plain,(
% 7.29/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f1])).
% 7.29/1.50  
% 7.29/1.50  fof(f92,plain,(
% 7.29/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.29/1.50    inference(definition_unfolding,[],[f48,f56,f56])).
% 7.29/1.50  
% 7.29/1.50  fof(f2,axiom,(
% 7.29/1.50    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.29/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f24,plain,(
% 7.29/1.50    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.29/1.50    inference(rectify,[],[f2])).
% 7.29/1.50  
% 7.29/1.50  fof(f49,plain,(
% 7.29/1.50    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.29/1.50    inference(cnf_transformation,[],[f24])).
% 7.29/1.50  
% 7.29/1.50  fof(f93,plain,(
% 7.29/1.50    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 7.29/1.50    inference(definition_unfolding,[],[f49,f56])).
% 7.29/1.50  
% 7.29/1.50  fof(f73,plain,(
% 7.29/1.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f43])).
% 7.29/1.50  
% 7.29/1.50  fof(f108,plain,(
% 7.29/1.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.29/1.50    inference(definition_unfolding,[],[f73,f89,f90])).
% 7.29/1.50  
% 7.29/1.50  cnf(c_23,plain,
% 7.29/1.50      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 7.29/1.50      inference(cnf_transformation,[],[f123]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_689,plain,
% 7.29/1.50      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_28,negated_conjecture,
% 7.29/1.50      ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
% 7.29/1.50      inference(cnf_transformation,[],[f114]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_686,plain,
% 7.29/1.50      ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) = iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_25,plain,
% 7.29/1.50      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 7.29/1.50      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
% 7.29/1.50      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
% 7.29/1.50      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 7.29/1.50      | k1_xboole_0 = X0 ),
% 7.29/1.50      inference(cnf_transformation,[],[f113]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_687,plain,
% 7.29/1.50      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
% 7.29/1.50      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X2
% 7.29/1.50      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X2
% 7.29/1.50      | k1_xboole_0 = X2
% 7.29/1.50      | r1_tarski(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_1164,plain,
% 7.29/1.50      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_686,c_687]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_1583,plain,
% 7.29/1.50      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = X0
% 7.29/1.50      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.29/1.50      | k1_xboole_0 = X0
% 7.29/1.50      | r1_tarski(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_1164,c_687]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_2396,plain,
% 7.29/1.50      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 7.29/1.50      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_689,c_1583]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_4160,plain,
% 7.29/1.50      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_2396,c_1164]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_27,negated_conjecture,
% 7.29/1.50      ( sK3 != sK5 ),
% 7.29/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_15,plain,
% 7.29/1.50      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 7.29/1.50      | X0 = X1
% 7.29/1.50      | X0 = X2 ),
% 7.29/1.50      inference(cnf_transformation,[],[f119]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_55,plain,
% 7.29/1.50      ( ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
% 7.29/1.50      | sK3 = sK3 ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_15]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_14,plain,
% 7.29/1.50      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 7.29/1.50      inference(cnf_transformation,[],[f118]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_58,plain,
% 7.29/1.50      ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_294,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_870,plain,
% 7.29/1.50      ( sK5 != X0 | sK3 != X0 | sK3 = sK5 ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_294]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_871,plain,
% 7.29/1.50      ( sK5 != sK3 | sK3 = sK5 | sK3 != sK3 ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_870]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_982,plain,
% 7.29/1.50      ( ~ r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
% 7.29/1.50      | sK5 = X0
% 7.29/1.50      | sK5 = X1 ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_15]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_983,plain,
% 7.29/1.50      ( sK5 = X0
% 7.29/1.50      | sK5 = X1
% 7.29/1.50      | r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_982]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_985,plain,
% 7.29/1.50      ( sK5 = sK3
% 7.29/1.50      | r2_hidden(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_983]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_13,plain,
% 7.29/1.50      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
% 7.29/1.50      inference(cnf_transformation,[],[f116]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_699,plain,
% 7.29/1.50      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_4155,plain,
% 7.29/1.50      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
% 7.29/1.50      | r2_hidden(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_2396,c_699]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_4368,plain,
% 7.29/1.50      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.29/1.50      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 7.29/1.50      inference(global_propositional_subsumption,
% 7.29/1.50                [status(thm)],
% 7.29/1.50                [c_4160,c_27,c_55,c_58,c_871,c_985,c_4155]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_4369,plain,
% 7.29/1.50      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 7.29/1.50      inference(renaming,[status(thm)],[c_4368]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_4377,plain,
% 7.29/1.50      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = X0
% 7.29/1.50      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = X0
% 7.29/1.50      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = X0
% 7.29/1.50      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
% 7.29/1.50      | k1_xboole_0 = X0
% 7.29/1.50      | r1_tarski(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_4369,c_687]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_6683,plain,
% 7.29/1.50      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 7.29/1.50      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_689,c_4377]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_26,negated_conjecture,
% 7.29/1.50      ( sK3 != sK6 ),
% 7.29/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_868,plain,
% 7.29/1.50      ( sK6 != X0 | sK3 != X0 | sK3 = sK6 ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_294]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_869,plain,
% 7.29/1.50      ( sK6 != sK3 | sK3 = sK6 | sK3 != sK3 ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_868]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_697,plain,
% 7.29/1.50      ( X0 = X1
% 7.29/1.50      | X0 = X2
% 7.29/1.50      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) != iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_10420,plain,
% 7.29/1.50      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.29/1.50      | sK5 = X0
% 7.29/1.50      | r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_1164,c_697]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_11342,plain,
% 7.29/1.50      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.29/1.50      | sK4 = sK5 ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_699,c_10420]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_698,plain,
% 7.29/1.50      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_11343,plain,
% 7.29/1.50      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.29/1.50      | sK5 = sK3 ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_698,c_10420]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_11394,plain,
% 7.29/1.50      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.29/1.50      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
% 7.29/1.50      inference(global_propositional_subsumption,
% 7.29/1.50                [status(thm)],
% 7.29/1.50                [c_11342,c_27,c_55,c_58,c_871,c_11343]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_11395,plain,
% 7.29/1.50      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 7.29/1.50      inference(renaming,[status(thm)],[c_11394]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_19,plain,
% 7.29/1.50      ( r2_hidden(X0,X1)
% 7.29/1.50      | X0 = X2
% 7.29/1.50      | k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
% 7.29/1.50      inference(cnf_transformation,[],[f107]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_693,plain,
% 7.29/1.50      ( X0 = X1
% 7.29/1.50      | k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),X2) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
% 7.29/1.50      | r2_hidden(X0,X2) = iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_11405,plain,
% 7.29/1.50      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.29/1.50      | k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),X0) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 7.29/1.50      | sK5 = sK6
% 7.29/1.50      | r2_hidden(sK6,X0) = iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_11395,c_693]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_11408,plain,
% 7.29/1.50      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.29/1.50      | sK5 = X0
% 7.29/1.50      | sK6 = X0
% 7.29/1.50      | r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_11395,c_697]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_14569,plain,
% 7.29/1.50      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.29/1.50      | sK5 = sK3
% 7.29/1.50      | sK6 = sK3 ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_698,c_11408]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_14629,plain,
% 7.29/1.50      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.29/1.50      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
% 7.29/1.50      inference(global_propositional_subsumption,
% 7.29/1.50                [status(thm)],
% 7.29/1.50                [c_11405,c_27,c_26,c_55,c_58,c_869,c_871,c_14569]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_14630,plain,
% 7.29/1.50      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 7.29/1.50      inference(renaming,[status(thm)],[c_14629]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_14642,plain,
% 7.29/1.50      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.29/1.50      | sK6 = X0
% 7.29/1.50      | r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_14630,c_697]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_14684,plain,
% 7.29/1.50      ( ~ r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.29/1.50      | sK6 = X0 ),
% 7.29/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_14642]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_14686,plain,
% 7.29/1.50      ( ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 7.29/1.50      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.29/1.50      | sK6 = sK3 ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_14684]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_1153,plain,
% 7.29/1.50      ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0)) ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_20697,plain,
% 7.29/1.50      ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_1153]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_21192,plain,
% 7.29/1.50      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 7.29/1.50      inference(global_propositional_subsumption,
% 7.29/1.50                [status(thm)],
% 7.29/1.50                [c_6683,c_26,c_55,c_58,c_869,c_14686,c_20697]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_21285,plain,
% 7.29/1.50      ( r2_hidden(sK3,k1_xboole_0) = iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_21192,c_698]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_24,plain,
% 7.29/1.50      ( r1_tarski(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 7.29/1.50      inference(cnf_transformation,[],[f124]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_688,plain,
% 7.29/1.50      ( r1_tarski(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_7,plain,
% 7.29/1.50      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.29/1.50      inference(cnf_transformation,[],[f97]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_704,plain,
% 7.29/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 7.29/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_2608,plain,
% 7.29/1.50      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_688,c_704]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_0,plain,
% 7.29/1.50      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.29/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_17676,plain,
% 7.29/1.50      ( k4_xboole_0(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_2608,c_0]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_8,plain,
% 7.29/1.50      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.29/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_17862,plain,
% 7.29/1.50      ( k4_xboole_0(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_xboole_0 ),
% 7.29/1.50      inference(demodulation,[status(thm)],[c_17676,c_8]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_1,plain,
% 7.29/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.29/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_1169,plain,
% 7.29/1.50      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_18164,plain,
% 7.29/1.50      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k1_xboole_0) ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_17862,c_1169]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_2,plain,
% 7.29/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 7.29/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_995,plain,
% 7.29/1.50      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_1005,plain,
% 7.29/1.50      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_8,c_995]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_18226,plain,
% 7.29/1.50      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k1_xboole_0) = k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k1_xboole_0) ),
% 7.29/1.50      inference(light_normalisation,[status(thm)],[c_18164,c_1005]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_18227,plain,
% 7.29/1.50      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k1_xboole_0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
% 7.29/1.50      inference(demodulation,[status(thm)],[c_18226,c_8]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_20,plain,
% 7.29/1.50      ( ~ r2_hidden(X0,X1)
% 7.29/1.50      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 7.29/1.50      inference(cnf_transformation,[],[f108]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_692,plain,
% 7.29/1.50      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 7.29/1.50      | r2_hidden(X0,X2) != iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_18932,plain,
% 7.29/1.50      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)
% 7.29/1.50      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_18227,c_692]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_18980,plain,
% 7.29/1.50      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 7.29/1.50      | r2_hidden(sK3,k1_xboole_0) != iProver_top ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_18932]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_300,plain,
% 7.29/1.50      ( X0 != X1
% 7.29/1.50      | X2 != X3
% 7.29/1.50      | X4 != X5
% 7.29/1.50      | X6 != X7
% 7.29/1.50      | X8 != X9
% 7.29/1.50      | X10 != X11
% 7.29/1.50      | X12 != X13
% 7.29/1.50      | X14 != X15
% 7.29/1.50      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 7.29/1.50      theory(equality) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_306,plain,
% 7.29/1.50      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 7.29/1.50      | sK3 != sK3 ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_300]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(contradiction,plain,
% 7.29/1.50      ( $false ),
% 7.29/1.50      inference(minisat,[status(thm)],[c_21285,c_18980,c_306,c_58,c_55]) ).
% 7.29/1.50  
% 7.29/1.50  
% 7.29/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.29/1.50  
% 7.29/1.50  ------                               Statistics
% 7.29/1.50  
% 7.29/1.50  ------ General
% 7.29/1.50  
% 7.29/1.50  abstr_ref_over_cycles:                  0
% 7.29/1.50  abstr_ref_under_cycles:                 0
% 7.29/1.50  gc_basic_clause_elim:                   0
% 7.29/1.50  forced_gc_time:                         0
% 7.29/1.50  parsing_time:                           0.008
% 7.29/1.50  unif_index_cands_time:                  0.
% 7.29/1.50  unif_index_add_time:                    0.
% 7.29/1.50  orderings_time:                         0.
% 7.29/1.50  out_proof_time:                         0.013
% 7.29/1.50  total_time:                             0.789
% 7.29/1.50  num_of_symbols:                         45
% 7.29/1.50  num_of_terms:                           20443
% 7.29/1.50  
% 7.29/1.50  ------ Preprocessing
% 7.29/1.50  
% 7.29/1.50  num_of_splits:                          0
% 7.29/1.50  num_of_split_atoms:                     0
% 7.29/1.50  num_of_reused_defs:                     0
% 7.29/1.50  num_eq_ax_congr_red:                    16
% 7.29/1.50  num_of_sem_filtered_clauses:            1
% 7.29/1.50  num_of_subtypes:                        0
% 7.29/1.50  monotx_restored_types:                  0
% 7.29/1.50  sat_num_of_epr_types:                   0
% 7.29/1.50  sat_num_of_non_cyclic_types:            0
% 7.29/1.50  sat_guarded_non_collapsed_types:        0
% 7.29/1.50  num_pure_diseq_elim:                    0
% 7.29/1.50  simp_replaced_by:                       0
% 7.29/1.50  res_preprocessed:                       104
% 7.29/1.50  prep_upred:                             0
% 7.29/1.50  prep_unflattend:                        4
% 7.29/1.50  smt_new_axioms:                         0
% 7.29/1.50  pred_elim_cands:                        3
% 7.29/1.50  pred_elim:                              0
% 7.29/1.50  pred_elim_cl:                           0
% 7.29/1.50  pred_elim_cycles:                       1
% 7.29/1.50  merged_defs:                            0
% 7.29/1.50  merged_defs_ncl:                        0
% 7.29/1.50  bin_hyper_res:                          0
% 7.29/1.50  prep_cycles:                            3
% 7.29/1.50  pred_elim_time:                         0.
% 7.29/1.50  splitting_time:                         0.
% 7.29/1.50  sem_filter_time:                        0.
% 7.29/1.50  monotx_time:                            0.
% 7.29/1.50  subtype_inf_time:                       0.
% 7.29/1.50  
% 7.29/1.50  ------ Problem properties
% 7.29/1.50  
% 7.29/1.50  clauses:                                29
% 7.29/1.50  conjectures:                            3
% 7.29/1.50  epr:                                    3
% 7.29/1.50  horn:                                   21
% 7.29/1.50  ground:                                 3
% 7.29/1.50  unary:                                  14
% 7.29/1.50  binary:                                 8
% 7.29/1.50  lits:                                   54
% 7.29/1.50  lits_eq:                                27
% 7.29/1.50  fd_pure:                                0
% 7.29/1.50  fd_pseudo:                              0
% 7.29/1.50  fd_cond:                                1
% 7.29/1.50  fd_pseudo_cond:                         5
% 7.29/1.50  ac_symbols:                             0
% 7.29/1.50  
% 7.29/1.50  ------ Propositional Solver
% 7.29/1.50  
% 7.29/1.50  prop_solver_calls:                      24
% 7.29/1.50  prop_fast_solver_calls:                 864
% 7.29/1.50  smt_solver_calls:                       0
% 7.29/1.50  smt_fast_solver_calls:                  0
% 7.29/1.50  prop_num_of_clauses:                    6707
% 7.29/1.50  prop_preprocess_simplified:             13137
% 7.29/1.50  prop_fo_subsumed:                       48
% 7.29/1.50  prop_solver_time:                       0.
% 7.29/1.50  smt_solver_time:                        0.
% 7.29/1.50  smt_fast_solver_time:                   0.
% 7.29/1.50  prop_fast_solver_time:                  0.
% 7.29/1.50  prop_unsat_core_time:                   0.
% 7.29/1.50  
% 7.29/1.50  ------ QBF
% 7.29/1.50  
% 7.29/1.50  qbf_q_res:                              0
% 7.29/1.50  qbf_num_tautologies:                    0
% 7.29/1.50  qbf_prep_cycles:                        0
% 7.29/1.50  
% 7.29/1.50  ------ BMC1
% 7.29/1.50  
% 7.29/1.50  bmc1_current_bound:                     -1
% 7.29/1.50  bmc1_last_solved_bound:                 -1
% 7.29/1.50  bmc1_unsat_core_size:                   -1
% 7.29/1.50  bmc1_unsat_core_parents_size:           -1
% 7.29/1.50  bmc1_merge_next_fun:                    0
% 7.29/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.29/1.50  
% 7.29/1.50  ------ Instantiation
% 7.29/1.50  
% 7.29/1.50  inst_num_of_clauses:                    1507
% 7.29/1.50  inst_num_in_passive:                    986
% 7.29/1.50  inst_num_in_active:                     504
% 7.29/1.50  inst_num_in_unprocessed:                17
% 7.29/1.50  inst_num_of_loops:                      670
% 7.29/1.50  inst_num_of_learning_restarts:          0
% 7.29/1.50  inst_num_moves_active_passive:          165
% 7.29/1.50  inst_lit_activity:                      0
% 7.29/1.50  inst_lit_activity_moves:                0
% 7.29/1.50  inst_num_tautologies:                   0
% 7.29/1.50  inst_num_prop_implied:                  0
% 7.29/1.50  inst_num_existing_simplified:           0
% 7.29/1.50  inst_num_eq_res_simplified:             0
% 7.29/1.50  inst_num_child_elim:                    0
% 7.29/1.50  inst_num_of_dismatching_blockings:      1738
% 7.29/1.50  inst_num_of_non_proper_insts:           1578
% 7.29/1.50  inst_num_of_duplicates:                 0
% 7.29/1.50  inst_inst_num_from_inst_to_res:         0
% 7.29/1.50  inst_dismatching_checking_time:         0.
% 7.29/1.50  
% 7.29/1.50  ------ Resolution
% 7.29/1.50  
% 7.29/1.50  res_num_of_clauses:                     0
% 7.29/1.50  res_num_in_passive:                     0
% 7.29/1.50  res_num_in_active:                      0
% 7.29/1.50  res_num_of_loops:                       107
% 7.29/1.50  res_forward_subset_subsumed:            126
% 7.29/1.50  res_backward_subset_subsumed:           0
% 7.29/1.50  res_forward_subsumed:                   0
% 7.29/1.50  res_backward_subsumed:                  0
% 7.29/1.50  res_forward_subsumption_resolution:     0
% 7.29/1.50  res_backward_subsumption_resolution:    0
% 7.29/1.50  res_clause_to_clause_subsumption:       6193
% 7.29/1.50  res_orphan_elimination:                 0
% 7.29/1.50  res_tautology_del:                      31
% 7.29/1.50  res_num_eq_res_simplified:              0
% 7.29/1.50  res_num_sel_changes:                    0
% 7.29/1.50  res_moves_from_active_to_pass:          0
% 7.29/1.50  
% 7.29/1.50  ------ Superposition
% 7.29/1.50  
% 7.29/1.50  sup_time_total:                         0.
% 7.29/1.50  sup_time_generating:                    0.
% 7.29/1.50  sup_time_sim_full:                      0.
% 7.29/1.50  sup_time_sim_immed:                     0.
% 7.29/1.50  
% 7.29/1.50  sup_num_of_clauses:                     432
% 7.29/1.50  sup_num_in_active:                      72
% 7.29/1.50  sup_num_in_passive:                     360
% 7.29/1.50  sup_num_of_loops:                       133
% 7.29/1.50  sup_fw_superposition:                   855
% 7.29/1.50  sup_bw_superposition:                   766
% 7.29/1.50  sup_immediate_simplified:               776
% 7.29/1.50  sup_given_eliminated:                   4
% 7.29/1.50  comparisons_done:                       0
% 7.29/1.50  comparisons_avoided:                    121
% 7.29/1.50  
% 7.29/1.50  ------ Simplifications
% 7.29/1.50  
% 7.29/1.50  
% 7.29/1.50  sim_fw_subset_subsumed:                 61
% 7.29/1.50  sim_bw_subset_subsumed:                 287
% 7.29/1.50  sim_fw_subsumed:                        178
% 7.29/1.50  sim_bw_subsumed:                        3
% 7.29/1.50  sim_fw_subsumption_res:                 0
% 7.29/1.50  sim_bw_subsumption_res:                 0
% 7.29/1.50  sim_tautology_del:                      77
% 7.29/1.50  sim_eq_tautology_del:                   108
% 7.29/1.50  sim_eq_res_simp:                        0
% 7.29/1.50  sim_fw_demodulated:                     229
% 7.29/1.50  sim_bw_demodulated:                     86
% 7.29/1.50  sim_light_normalised:                   410
% 7.29/1.50  sim_joinable_taut:                      0
% 7.29/1.50  sim_joinable_simp:                      0
% 7.29/1.50  sim_ac_normalised:                      0
% 7.29/1.50  sim_smt_subsumption:                    0
% 7.29/1.50  
%------------------------------------------------------------------------------
