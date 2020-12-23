%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:34 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  156 (6489 expanded)
%              Number of clauses        :   75 ( 404 expanded)
%              Number of leaves         :   21 (2049 expanded)
%              Depth                    :   27
%              Number of atoms          :  433 (10812 expanded)
%              Number of equality atoms :  333 (9396 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f19])).

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

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f68,f85])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f67,f86])).

fof(f88,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f87])).

fof(f89,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f65,f88])).

fof(f90,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f64,f89])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f77,f89,f90])).

fof(f122,plain,(
    ! [X2,X1] : r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f108])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f22])).

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

fof(f82,plain,(
    r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(cnf_transformation,[],[f47])).

fof(f113,plain,(
    r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(definition_unfolding,[],[f82,f89,f89])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f75,f89,f90,f90,f89])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f80,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f112,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f80,f90,f90,f90])).

fof(f124,plain,(
    ! [X1] : k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f112])).

fof(f83,plain,(
    sK3 != sK5 ),
    inference(cnf_transformation,[],[f47])).

fof(f84,plain,(
    sK3 != sK6 ),
    inference(cnf_transformation,[],[f47])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f81,f90,f90,f90])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f10])).

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
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f100,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f59,f89])).

fof(f116,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f100])).

fof(f117,plain,(
    ! [X4,X1] : r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f116])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f101,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f58,f89])).

fof(f118,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f101])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f18])).

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

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f71,f89,f90])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f78,f89,f90])).

fof(f121,plain,(
    ! [X2,X1] : r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f107])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f48,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f92,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f55])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f91,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f52,f55])).

cnf(c_21,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_658,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_655,plain,
    ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_673,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4658,plain,
    ( r1_tarski(X0,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) = iProver_top
    | r1_tarski(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_655,c_673])).

cnf(c_5096,plain,
    ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_658,c_4658])).

cnf(c_23,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_656,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X2
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5364,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5096,c_656])).

cnf(c_25,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_9342,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
    | k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(superposition,[status(thm)],[c_5364,c_25])).

cnf(c_27,negated_conjecture,
    ( sK3 != sK5 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_26,negated_conjecture,
    ( sK3 != sK6 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_30,plain,
    ( k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_24,plain,
    ( X0 = X1
    | k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_31,plain,
    ( k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_13,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_57,plain,
    ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_56,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_58,plain,
    ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_281,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_843,plain,
    ( sK5 != X0
    | sK3 != X0
    | sK3 = sK5 ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_844,plain,
    ( sK5 != sK3
    | sK3 = sK5
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_868,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0))
    | sK3 = X0
    | sK3 = sK6 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1007,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | sK3 = sK6 ),
    inference(instantiation,[status(thm)],[c_868])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_661,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6686,plain,
    ( X0 = X1
    | r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_661])).

cnf(c_9338,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
    | sK5 = X0
    | r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5364,c_6686])).

cnf(c_9483,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
    | sK5 = sK3
    | r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9338])).

cnf(c_20,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_659,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1182,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_655,c_656])).

cnf(c_1414,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = X0
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1182,c_656])).

cnf(c_4427,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_659,c_1414])).

cnf(c_841,plain,
    ( sK6 != X0
    | sK3 != X0
    | sK3 = sK6 ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_842,plain,
    ( sK6 != sK3
    | sK3 = sK6
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_6698,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),X0) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | r2_hidden(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1182,c_661])).

cnf(c_666,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_665,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6465,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK5 = X0
    | r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1182,c_665])).

cnf(c_7019,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK5 = sK3 ),
    inference(superposition,[status(thm)],[c_666,c_6465])).

cnf(c_7241,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6698,c_27,c_30,c_31,c_844,c_7019])).

cnf(c_7246,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),X0) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | r2_hidden(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7241,c_661])).

cnf(c_7256,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK5 = X0
    | sK6 = X0
    | r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7241,c_665])).

cnf(c_7922,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK5 = sK3
    | sK6 = sK3 ),
    inference(superposition,[status(thm)],[c_666,c_7256])).

cnf(c_8347,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7246,c_27,c_26,c_30,c_31,c_842,c_844,c_7922])).

cnf(c_8363,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK6 = X0
    | r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8347,c_6686])).

cnf(c_8433,plain,
    ( ~ r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK6 = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8363])).

cnf(c_8435,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK6 = sK3 ),
    inference(instantiation,[status(thm)],[c_8433])).

cnf(c_10208,plain,
    ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_10396,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4427,c_26,c_30,c_31,c_842,c_8435,c_10208])).

cnf(c_10430,plain,
    ( r2_hidden(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10396,c_666])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_6685,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)
    | r2_hidden(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_661])).

cnf(c_10425,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k1_xboole_0
    | r2_hidden(sK3,k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10396,c_6685])).

cnf(c_10478,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k1_xboole_0
    | r2_hidden(sK3,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10425,c_10396])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_953,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_963,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_953])).

cnf(c_10481,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k1_xboole_0
    | r2_hidden(sK3,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10478,c_963])).

cnf(c_285,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_865,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))
    | X0 != X2
    | X1 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3) ),
    inference(instantiation,[status(thm)],[c_285])).

cnf(c_11567,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
    | r2_hidden(sK3,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_11569,plain,
    ( r2_hidden(sK3,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_11567])).

cnf(c_12181,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9342,c_27,c_26,c_30,c_31,c_57,c_58,c_844,c_1007,c_9483,c_10430,c_10481,c_11569])).

cnf(c_12256,plain,
    ( r2_hidden(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12181,c_666])).

cnf(c_988,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
    | sK5 = X0
    | sK5 = X1 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_989,plain,
    ( sK5 = X0
    | sK5 = X1
    | r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_988])).

cnf(c_991,plain,
    ( sK5 = sK3
    | r2_hidden(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_989])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12256,c_991,c_844,c_31,c_30,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:33:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.75/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/0.98  
% 3.75/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.75/0.98  
% 3.75/0.98  ------  iProver source info
% 3.75/0.98  
% 3.75/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.75/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.75/0.98  git: non_committed_changes: false
% 3.75/0.98  git: last_make_outside_of_git: false
% 3.75/0.98  
% 3.75/0.98  ------ 
% 3.75/0.98  
% 3.75/0.98  ------ Input Options
% 3.75/0.98  
% 3.75/0.98  --out_options                           all
% 3.75/0.98  --tptp_safe_out                         true
% 3.75/0.98  --problem_path                          ""
% 3.75/0.98  --include_path                          ""
% 3.75/0.98  --clausifier                            res/vclausify_rel
% 3.75/0.98  --clausifier_options                    --mode clausify
% 3.75/0.98  --stdin                                 false
% 3.75/0.98  --stats_out                             all
% 3.75/0.98  
% 3.75/0.98  ------ General Options
% 3.75/0.98  
% 3.75/0.98  --fof                                   false
% 3.75/0.98  --time_out_real                         305.
% 3.75/0.98  --time_out_virtual                      -1.
% 3.75/0.98  --symbol_type_check                     false
% 3.75/0.98  --clausify_out                          false
% 3.75/0.98  --sig_cnt_out                           false
% 3.75/0.98  --trig_cnt_out                          false
% 3.75/0.98  --trig_cnt_out_tolerance                1.
% 3.75/0.98  --trig_cnt_out_sk_spl                   false
% 3.75/0.98  --abstr_cl_out                          false
% 3.75/0.98  
% 3.75/0.98  ------ Global Options
% 3.75/0.98  
% 3.75/0.98  --schedule                              default
% 3.75/0.98  --add_important_lit                     false
% 3.75/0.98  --prop_solver_per_cl                    1000
% 3.75/0.98  --min_unsat_core                        false
% 3.75/0.98  --soft_assumptions                      false
% 3.75/0.98  --soft_lemma_size                       3
% 3.75/0.98  --prop_impl_unit_size                   0
% 3.75/0.98  --prop_impl_unit                        []
% 3.75/0.98  --share_sel_clauses                     true
% 3.75/0.98  --reset_solvers                         false
% 3.75/0.98  --bc_imp_inh                            [conj_cone]
% 3.75/0.98  --conj_cone_tolerance                   3.
% 3.75/0.98  --extra_neg_conj                        none
% 3.75/0.98  --large_theory_mode                     true
% 3.75/0.98  --prolific_symb_bound                   200
% 3.75/0.98  --lt_threshold                          2000
% 3.75/0.98  --clause_weak_htbl                      true
% 3.75/0.98  --gc_record_bc_elim                     false
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing Options
% 3.75/0.98  
% 3.75/0.98  --preprocessing_flag                    true
% 3.75/0.98  --time_out_prep_mult                    0.1
% 3.75/0.98  --splitting_mode                        input
% 3.75/0.98  --splitting_grd                         true
% 3.75/0.98  --splitting_cvd                         false
% 3.75/0.98  --splitting_cvd_svl                     false
% 3.75/0.98  --splitting_nvd                         32
% 3.75/0.98  --sub_typing                            true
% 3.75/0.98  --prep_gs_sim                           true
% 3.75/0.98  --prep_unflatten                        true
% 3.75/0.98  --prep_res_sim                          true
% 3.75/0.98  --prep_upred                            true
% 3.75/0.98  --prep_sem_filter                       exhaustive
% 3.75/0.98  --prep_sem_filter_out                   false
% 3.75/0.98  --pred_elim                             true
% 3.75/0.98  --res_sim_input                         true
% 3.75/0.98  --eq_ax_congr_red                       true
% 3.75/0.98  --pure_diseq_elim                       true
% 3.75/0.98  --brand_transform                       false
% 3.75/0.98  --non_eq_to_eq                          false
% 3.75/0.98  --prep_def_merge                        true
% 3.75/0.98  --prep_def_merge_prop_impl              false
% 3.75/0.98  --prep_def_merge_mbd                    true
% 3.75/0.98  --prep_def_merge_tr_red                 false
% 3.75/0.98  --prep_def_merge_tr_cl                  false
% 3.75/0.98  --smt_preprocessing                     true
% 3.75/0.98  --smt_ac_axioms                         fast
% 3.75/0.98  --preprocessed_out                      false
% 3.75/0.98  --preprocessed_stats                    false
% 3.75/0.98  
% 3.75/0.98  ------ Abstraction refinement Options
% 3.75/0.98  
% 3.75/0.98  --abstr_ref                             []
% 3.75/0.98  --abstr_ref_prep                        false
% 3.75/0.98  --abstr_ref_until_sat                   false
% 3.75/0.98  --abstr_ref_sig_restrict                funpre
% 3.75/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.75/0.98  --abstr_ref_under                       []
% 3.75/0.98  
% 3.75/0.98  ------ SAT Options
% 3.75/0.98  
% 3.75/0.98  --sat_mode                              false
% 3.75/0.98  --sat_fm_restart_options                ""
% 3.75/0.98  --sat_gr_def                            false
% 3.75/0.98  --sat_epr_types                         true
% 3.75/0.98  --sat_non_cyclic_types                  false
% 3.75/0.98  --sat_finite_models                     false
% 3.75/0.98  --sat_fm_lemmas                         false
% 3.75/0.98  --sat_fm_prep                           false
% 3.75/0.98  --sat_fm_uc_incr                        true
% 3.75/0.98  --sat_out_model                         small
% 3.75/0.98  --sat_out_clauses                       false
% 3.75/0.98  
% 3.75/0.98  ------ QBF Options
% 3.75/0.98  
% 3.75/0.98  --qbf_mode                              false
% 3.75/0.98  --qbf_elim_univ                         false
% 3.75/0.98  --qbf_dom_inst                          none
% 3.75/0.98  --qbf_dom_pre_inst                      false
% 3.75/0.98  --qbf_sk_in                             false
% 3.75/0.98  --qbf_pred_elim                         true
% 3.75/0.98  --qbf_split                             512
% 3.75/0.98  
% 3.75/0.98  ------ BMC1 Options
% 3.75/0.98  
% 3.75/0.98  --bmc1_incremental                      false
% 3.75/0.98  --bmc1_axioms                           reachable_all
% 3.75/0.98  --bmc1_min_bound                        0
% 3.75/0.98  --bmc1_max_bound                        -1
% 3.75/0.98  --bmc1_max_bound_default                -1
% 3.75/0.98  --bmc1_symbol_reachability              true
% 3.75/0.98  --bmc1_property_lemmas                  false
% 3.75/0.98  --bmc1_k_induction                      false
% 3.75/0.98  --bmc1_non_equiv_states                 false
% 3.75/0.98  --bmc1_deadlock                         false
% 3.75/0.98  --bmc1_ucm                              false
% 3.75/0.98  --bmc1_add_unsat_core                   none
% 3.75/0.98  --bmc1_unsat_core_children              false
% 3.75/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.75/0.98  --bmc1_out_stat                         full
% 3.75/0.98  --bmc1_ground_init                      false
% 3.75/0.98  --bmc1_pre_inst_next_state              false
% 3.75/0.98  --bmc1_pre_inst_state                   false
% 3.75/0.98  --bmc1_pre_inst_reach_state             false
% 3.75/0.98  --bmc1_out_unsat_core                   false
% 3.75/0.98  --bmc1_aig_witness_out                  false
% 3.75/0.98  --bmc1_verbose                          false
% 3.75/0.98  --bmc1_dump_clauses_tptp                false
% 3.75/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.75/0.98  --bmc1_dump_file                        -
% 3.75/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.75/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.75/0.98  --bmc1_ucm_extend_mode                  1
% 3.75/0.98  --bmc1_ucm_init_mode                    2
% 3.75/0.98  --bmc1_ucm_cone_mode                    none
% 3.75/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.75/0.98  --bmc1_ucm_relax_model                  4
% 3.75/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.75/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.75/0.98  --bmc1_ucm_layered_model                none
% 3.75/0.98  --bmc1_ucm_max_lemma_size               10
% 3.75/0.98  
% 3.75/0.98  ------ AIG Options
% 3.75/0.98  
% 3.75/0.98  --aig_mode                              false
% 3.75/0.98  
% 3.75/0.98  ------ Instantiation Options
% 3.75/0.98  
% 3.75/0.98  --instantiation_flag                    true
% 3.75/0.98  --inst_sos_flag                         false
% 3.75/0.98  --inst_sos_phase                        true
% 3.75/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.75/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.75/0.98  --inst_lit_sel_side                     num_symb
% 3.75/0.98  --inst_solver_per_active                1400
% 3.75/0.98  --inst_solver_calls_frac                1.
% 3.75/0.98  --inst_passive_queue_type               priority_queues
% 3.75/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.75/0.98  --inst_passive_queues_freq              [25;2]
% 3.75/0.98  --inst_dismatching                      true
% 3.75/0.98  --inst_eager_unprocessed_to_passive     true
% 3.75/0.98  --inst_prop_sim_given                   true
% 3.75/0.98  --inst_prop_sim_new                     false
% 3.75/0.98  --inst_subs_new                         false
% 3.75/0.98  --inst_eq_res_simp                      false
% 3.75/0.98  --inst_subs_given                       false
% 3.75/0.98  --inst_orphan_elimination               true
% 3.75/0.98  --inst_learning_loop_flag               true
% 3.75/0.98  --inst_learning_start                   3000
% 3.75/0.98  --inst_learning_factor                  2
% 3.75/0.98  --inst_start_prop_sim_after_learn       3
% 3.75/0.98  --inst_sel_renew                        solver
% 3.75/0.98  --inst_lit_activity_flag                true
% 3.75/0.98  --inst_restr_to_given                   false
% 3.75/0.98  --inst_activity_threshold               500
% 3.75/0.98  --inst_out_proof                        true
% 3.75/0.98  
% 3.75/0.98  ------ Resolution Options
% 3.75/0.98  
% 3.75/0.98  --resolution_flag                       true
% 3.75/0.98  --res_lit_sel                           adaptive
% 3.75/0.98  --res_lit_sel_side                      none
% 3.75/0.98  --res_ordering                          kbo
% 3.75/0.98  --res_to_prop_solver                    active
% 3.75/0.98  --res_prop_simpl_new                    false
% 3.75/0.98  --res_prop_simpl_given                  true
% 3.75/0.98  --res_passive_queue_type                priority_queues
% 3.75/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.75/0.98  --res_passive_queues_freq               [15;5]
% 3.75/0.98  --res_forward_subs                      full
% 3.75/0.98  --res_backward_subs                     full
% 3.75/0.98  --res_forward_subs_resolution           true
% 3.75/0.98  --res_backward_subs_resolution          true
% 3.75/0.98  --res_orphan_elimination                true
% 3.75/0.98  --res_time_limit                        2.
% 3.75/0.98  --res_out_proof                         true
% 3.75/0.98  
% 3.75/0.98  ------ Superposition Options
% 3.75/0.98  
% 3.75/0.98  --superposition_flag                    true
% 3.75/0.98  --sup_passive_queue_type                priority_queues
% 3.75/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.75/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.75/0.98  --demod_completeness_check              fast
% 3.75/0.98  --demod_use_ground                      true
% 3.75/0.98  --sup_to_prop_solver                    passive
% 3.75/0.98  --sup_prop_simpl_new                    true
% 3.75/0.98  --sup_prop_simpl_given                  true
% 3.75/0.98  --sup_fun_splitting                     false
% 3.75/0.98  --sup_smt_interval                      50000
% 3.75/0.98  
% 3.75/0.98  ------ Superposition Simplification Setup
% 3.75/0.98  
% 3.75/0.98  --sup_indices_passive                   []
% 3.75/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.75/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.98  --sup_full_bw                           [BwDemod]
% 3.75/0.98  --sup_immed_triv                        [TrivRules]
% 3.75/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.98  --sup_immed_bw_main                     []
% 3.75/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.75/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/0.98  
% 3.75/0.98  ------ Combination Options
% 3.75/0.98  
% 3.75/0.98  --comb_res_mult                         3
% 3.75/0.98  --comb_sup_mult                         2
% 3.75/0.98  --comb_inst_mult                        10
% 3.75/0.98  
% 3.75/0.98  ------ Debug Options
% 3.75/0.98  
% 3.75/0.98  --dbg_backtrace                         false
% 3.75/0.98  --dbg_dump_prop_clauses                 false
% 3.75/0.98  --dbg_dump_prop_clauses_file            -
% 3.75/0.98  --dbg_out_stat                          false
% 3.75/0.98  ------ Parsing...
% 3.75/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.75/0.98  ------ Proving...
% 3.75/0.98  ------ Problem Properties 
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  clauses                                 29
% 3.75/0.98  conjectures                             3
% 3.75/0.98  EPR                                     4
% 3.75/0.98  Horn                                    20
% 3.75/0.98  unary                                   14
% 3.75/0.98  binary                                  7
% 3.75/0.98  lits                                    55
% 3.75/0.98  lits eq                                 28
% 3.75/0.98  fd_pure                                 0
% 3.75/0.98  fd_pseudo                               0
% 3.75/0.98  fd_cond                                 1
% 3.75/0.98  fd_pseudo_cond                          6
% 3.75/0.98  AC symbols                              0
% 3.75/0.98  
% 3.75/0.98  ------ Schedule dynamic 5 is on 
% 3.75/0.98  
% 3.75/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  ------ 
% 3.75/0.98  Current options:
% 3.75/0.98  ------ 
% 3.75/0.98  
% 3.75/0.98  ------ Input Options
% 3.75/0.98  
% 3.75/0.98  --out_options                           all
% 3.75/0.98  --tptp_safe_out                         true
% 3.75/0.98  --problem_path                          ""
% 3.75/0.98  --include_path                          ""
% 3.75/0.98  --clausifier                            res/vclausify_rel
% 3.75/0.98  --clausifier_options                    --mode clausify
% 3.75/0.98  --stdin                                 false
% 3.75/0.98  --stats_out                             all
% 3.75/0.98  
% 3.75/0.98  ------ General Options
% 3.75/0.98  
% 3.75/0.98  --fof                                   false
% 3.75/0.98  --time_out_real                         305.
% 3.75/0.98  --time_out_virtual                      -1.
% 3.75/0.98  --symbol_type_check                     false
% 3.75/0.98  --clausify_out                          false
% 3.75/0.98  --sig_cnt_out                           false
% 3.75/0.98  --trig_cnt_out                          false
% 3.75/0.98  --trig_cnt_out_tolerance                1.
% 3.75/0.98  --trig_cnt_out_sk_spl                   false
% 3.75/0.98  --abstr_cl_out                          false
% 3.75/0.98  
% 3.75/0.98  ------ Global Options
% 3.75/0.98  
% 3.75/0.98  --schedule                              default
% 3.75/0.98  --add_important_lit                     false
% 3.75/0.98  --prop_solver_per_cl                    1000
% 3.75/0.98  --min_unsat_core                        false
% 3.75/0.98  --soft_assumptions                      false
% 3.75/0.98  --soft_lemma_size                       3
% 3.75/0.98  --prop_impl_unit_size                   0
% 3.75/0.98  --prop_impl_unit                        []
% 3.75/0.98  --share_sel_clauses                     true
% 3.75/0.98  --reset_solvers                         false
% 3.75/0.98  --bc_imp_inh                            [conj_cone]
% 3.75/0.98  --conj_cone_tolerance                   3.
% 3.75/0.98  --extra_neg_conj                        none
% 3.75/0.98  --large_theory_mode                     true
% 3.75/0.98  --prolific_symb_bound                   200
% 3.75/0.98  --lt_threshold                          2000
% 3.75/0.98  --clause_weak_htbl                      true
% 3.75/0.98  --gc_record_bc_elim                     false
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing Options
% 3.75/0.98  
% 3.75/0.98  --preprocessing_flag                    true
% 3.75/0.98  --time_out_prep_mult                    0.1
% 3.75/0.98  --splitting_mode                        input
% 3.75/0.98  --splitting_grd                         true
% 3.75/0.98  --splitting_cvd                         false
% 3.75/0.98  --splitting_cvd_svl                     false
% 3.75/0.98  --splitting_nvd                         32
% 3.75/0.98  --sub_typing                            true
% 3.75/0.98  --prep_gs_sim                           true
% 3.75/0.98  --prep_unflatten                        true
% 3.75/0.98  --prep_res_sim                          true
% 3.75/0.98  --prep_upred                            true
% 3.75/0.98  --prep_sem_filter                       exhaustive
% 3.75/0.98  --prep_sem_filter_out                   false
% 3.75/0.98  --pred_elim                             true
% 3.75/0.98  --res_sim_input                         true
% 3.75/0.98  --eq_ax_congr_red                       true
% 3.75/0.98  --pure_diseq_elim                       true
% 3.75/0.98  --brand_transform                       false
% 3.75/0.98  --non_eq_to_eq                          false
% 3.75/0.98  --prep_def_merge                        true
% 3.75/0.98  --prep_def_merge_prop_impl              false
% 3.75/0.98  --prep_def_merge_mbd                    true
% 3.75/0.98  --prep_def_merge_tr_red                 false
% 3.75/0.98  --prep_def_merge_tr_cl                  false
% 3.75/0.98  --smt_preprocessing                     true
% 3.75/0.98  --smt_ac_axioms                         fast
% 3.75/0.98  --preprocessed_out                      false
% 3.75/0.98  --preprocessed_stats                    false
% 3.75/0.98  
% 3.75/0.98  ------ Abstraction refinement Options
% 3.75/0.98  
% 3.75/0.98  --abstr_ref                             []
% 3.75/0.98  --abstr_ref_prep                        false
% 3.75/0.98  --abstr_ref_until_sat                   false
% 3.75/0.98  --abstr_ref_sig_restrict                funpre
% 3.75/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.75/0.98  --abstr_ref_under                       []
% 3.75/0.98  
% 3.75/0.98  ------ SAT Options
% 3.75/0.98  
% 3.75/0.98  --sat_mode                              false
% 3.75/0.98  --sat_fm_restart_options                ""
% 3.75/0.98  --sat_gr_def                            false
% 3.75/0.98  --sat_epr_types                         true
% 3.75/0.98  --sat_non_cyclic_types                  false
% 3.75/0.98  --sat_finite_models                     false
% 3.75/0.98  --sat_fm_lemmas                         false
% 3.75/0.98  --sat_fm_prep                           false
% 3.75/0.98  --sat_fm_uc_incr                        true
% 3.75/0.98  --sat_out_model                         small
% 3.75/0.98  --sat_out_clauses                       false
% 3.75/0.98  
% 3.75/0.98  ------ QBF Options
% 3.75/0.98  
% 3.75/0.98  --qbf_mode                              false
% 3.75/0.98  --qbf_elim_univ                         false
% 3.75/0.98  --qbf_dom_inst                          none
% 3.75/0.98  --qbf_dom_pre_inst                      false
% 3.75/0.98  --qbf_sk_in                             false
% 3.75/0.98  --qbf_pred_elim                         true
% 3.75/0.98  --qbf_split                             512
% 3.75/0.98  
% 3.75/0.98  ------ BMC1 Options
% 3.75/0.98  
% 3.75/0.98  --bmc1_incremental                      false
% 3.75/0.98  --bmc1_axioms                           reachable_all
% 3.75/0.98  --bmc1_min_bound                        0
% 3.75/0.98  --bmc1_max_bound                        -1
% 3.75/0.98  --bmc1_max_bound_default                -1
% 3.75/0.98  --bmc1_symbol_reachability              true
% 3.75/0.98  --bmc1_property_lemmas                  false
% 3.75/0.98  --bmc1_k_induction                      false
% 3.75/0.98  --bmc1_non_equiv_states                 false
% 3.75/0.98  --bmc1_deadlock                         false
% 3.75/0.98  --bmc1_ucm                              false
% 3.75/0.98  --bmc1_add_unsat_core                   none
% 3.75/0.98  --bmc1_unsat_core_children              false
% 3.75/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.75/0.98  --bmc1_out_stat                         full
% 3.75/0.98  --bmc1_ground_init                      false
% 3.75/0.98  --bmc1_pre_inst_next_state              false
% 3.75/0.98  --bmc1_pre_inst_state                   false
% 3.75/0.98  --bmc1_pre_inst_reach_state             false
% 3.75/0.98  --bmc1_out_unsat_core                   false
% 3.75/0.98  --bmc1_aig_witness_out                  false
% 3.75/0.98  --bmc1_verbose                          false
% 3.75/0.98  --bmc1_dump_clauses_tptp                false
% 3.75/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.75/0.98  --bmc1_dump_file                        -
% 3.75/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.75/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.75/0.98  --bmc1_ucm_extend_mode                  1
% 3.75/0.98  --bmc1_ucm_init_mode                    2
% 3.75/0.98  --bmc1_ucm_cone_mode                    none
% 3.75/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.75/0.98  --bmc1_ucm_relax_model                  4
% 3.75/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.75/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.75/0.98  --bmc1_ucm_layered_model                none
% 3.75/0.98  --bmc1_ucm_max_lemma_size               10
% 3.75/0.98  
% 3.75/0.98  ------ AIG Options
% 3.75/0.98  
% 3.75/0.98  --aig_mode                              false
% 3.75/0.98  
% 3.75/0.98  ------ Instantiation Options
% 3.75/0.98  
% 3.75/0.98  --instantiation_flag                    true
% 3.75/0.98  --inst_sos_flag                         false
% 3.75/0.98  --inst_sos_phase                        true
% 3.75/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.75/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.75/0.98  --inst_lit_sel_side                     none
% 3.75/0.98  --inst_solver_per_active                1400
% 3.75/0.98  --inst_solver_calls_frac                1.
% 3.75/0.98  --inst_passive_queue_type               priority_queues
% 3.75/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.75/0.98  --inst_passive_queues_freq              [25;2]
% 3.75/0.98  --inst_dismatching                      true
% 3.75/0.98  --inst_eager_unprocessed_to_passive     true
% 3.75/0.98  --inst_prop_sim_given                   true
% 3.75/0.98  --inst_prop_sim_new                     false
% 3.75/0.98  --inst_subs_new                         false
% 3.75/0.98  --inst_eq_res_simp                      false
% 3.75/0.98  --inst_subs_given                       false
% 3.75/0.98  --inst_orphan_elimination               true
% 3.75/0.98  --inst_learning_loop_flag               true
% 3.75/0.98  --inst_learning_start                   3000
% 3.75/0.98  --inst_learning_factor                  2
% 3.75/0.98  --inst_start_prop_sim_after_learn       3
% 3.75/0.98  --inst_sel_renew                        solver
% 3.75/0.98  --inst_lit_activity_flag                true
% 3.75/0.98  --inst_restr_to_given                   false
% 3.75/0.98  --inst_activity_threshold               500
% 3.75/0.98  --inst_out_proof                        true
% 3.75/0.98  
% 3.75/0.98  ------ Resolution Options
% 3.75/0.98  
% 3.75/0.98  --resolution_flag                       false
% 3.75/0.98  --res_lit_sel                           adaptive
% 3.75/0.98  --res_lit_sel_side                      none
% 3.75/0.98  --res_ordering                          kbo
% 3.75/0.98  --res_to_prop_solver                    active
% 3.75/0.98  --res_prop_simpl_new                    false
% 3.75/0.98  --res_prop_simpl_given                  true
% 3.75/0.98  --res_passive_queue_type                priority_queues
% 3.75/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.75/0.98  --res_passive_queues_freq               [15;5]
% 3.75/0.98  --res_forward_subs                      full
% 3.75/0.98  --res_backward_subs                     full
% 3.75/0.98  --res_forward_subs_resolution           true
% 3.75/0.98  --res_backward_subs_resolution          true
% 3.75/0.98  --res_orphan_elimination                true
% 3.75/0.98  --res_time_limit                        2.
% 3.75/0.98  --res_out_proof                         true
% 3.75/0.98  
% 3.75/0.98  ------ Superposition Options
% 3.75/0.98  
% 3.75/0.98  --superposition_flag                    true
% 3.75/0.98  --sup_passive_queue_type                priority_queues
% 3.75/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.75/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.75/0.98  --demod_completeness_check              fast
% 3.75/0.98  --demod_use_ground                      true
% 3.75/0.98  --sup_to_prop_solver                    passive
% 3.75/0.98  --sup_prop_simpl_new                    true
% 3.75/0.98  --sup_prop_simpl_given                  true
% 3.75/0.98  --sup_fun_splitting                     false
% 3.75/0.98  --sup_smt_interval                      50000
% 3.75/0.98  
% 3.75/0.98  ------ Superposition Simplification Setup
% 3.75/0.98  
% 3.75/0.98  --sup_indices_passive                   []
% 3.75/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.75/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.98  --sup_full_bw                           [BwDemod]
% 3.75/0.98  --sup_immed_triv                        [TrivRules]
% 3.75/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.98  --sup_immed_bw_main                     []
% 3.75/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.75/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/0.98  
% 3.75/0.98  ------ Combination Options
% 3.75/0.98  
% 3.75/0.98  --comb_res_mult                         3
% 3.75/0.98  --comb_sup_mult                         2
% 3.75/0.98  --comb_inst_mult                        10
% 3.75/0.98  
% 3.75/0.98  ------ Debug Options
% 3.75/0.98  
% 3.75/0.98  --dbg_backtrace                         false
% 3.75/0.98  --dbg_dump_prop_clauses                 false
% 3.75/0.98  --dbg_dump_prop_clauses_file            -
% 3.75/0.98  --dbg_out_stat                          false
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  ------ Proving...
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  % SZS status Theorem for theBenchmark.p
% 3.75/0.98  
% 3.75/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.75/0.98  
% 3.75/0.98  fof(f19,axiom,(
% 3.75/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f30,plain,(
% 3.75/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.75/0.98    inference(ennf_transformation,[],[f19])).
% 3.75/0.98  
% 3.75/0.98  fof(f43,plain,(
% 3.75/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.75/0.98    inference(nnf_transformation,[],[f30])).
% 3.75/0.98  
% 3.75/0.98  fof(f44,plain,(
% 3.75/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.75/0.98    inference(flattening,[],[f43])).
% 3.75/0.98  
% 3.75/0.98  fof(f77,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 3.75/0.98    inference(cnf_transformation,[],[f44])).
% 3.75/0.98  
% 3.75/0.98  fof(f11,axiom,(
% 3.75/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f64,plain,(
% 3.75/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f11])).
% 3.75/0.98  
% 3.75/0.98  fof(f12,axiom,(
% 3.75/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f65,plain,(
% 3.75/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f12])).
% 3.75/0.98  
% 3.75/0.98  fof(f13,axiom,(
% 3.75/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f66,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f13])).
% 3.75/0.98  
% 3.75/0.98  fof(f14,axiom,(
% 3.75/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f67,plain,(
% 3.75/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f14])).
% 3.75/0.98  
% 3.75/0.98  fof(f15,axiom,(
% 3.75/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f68,plain,(
% 3.75/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f15])).
% 3.75/0.98  
% 3.75/0.98  fof(f16,axiom,(
% 3.75/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f69,plain,(
% 3.75/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f16])).
% 3.75/0.98  
% 3.75/0.98  fof(f17,axiom,(
% 3.75/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f70,plain,(
% 3.75/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f17])).
% 3.75/0.98  
% 3.75/0.98  fof(f85,plain,(
% 3.75/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.75/0.98    inference(definition_unfolding,[],[f69,f70])).
% 3.75/0.98  
% 3.75/0.98  fof(f86,plain,(
% 3.75/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.75/0.98    inference(definition_unfolding,[],[f68,f85])).
% 3.75/0.98  
% 3.75/0.98  fof(f87,plain,(
% 3.75/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.75/0.98    inference(definition_unfolding,[],[f67,f86])).
% 3.75/0.98  
% 3.75/0.98  fof(f88,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.75/0.98    inference(definition_unfolding,[],[f66,f87])).
% 3.75/0.98  
% 3.75/0.98  fof(f89,plain,(
% 3.75/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.75/0.98    inference(definition_unfolding,[],[f65,f88])).
% 3.75/0.98  
% 3.75/0.98  fof(f90,plain,(
% 3.75/0.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.75/0.98    inference(definition_unfolding,[],[f64,f89])).
% 3.75/0.98  
% 3.75/0.98  fof(f108,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0) )),
% 3.75/0.98    inference(definition_unfolding,[],[f77,f89,f90])).
% 3.75/0.98  
% 3.75/0.98  fof(f122,plain,(
% 3.75/0.98    ( ! [X2,X1] : (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 3.75/0.98    inference(equality_resolution,[],[f108])).
% 3.75/0.98  
% 3.75/0.98  fof(f21,conjecture,(
% 3.75/0.98    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f22,negated_conjecture,(
% 3.75/0.98    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 3.75/0.98    inference(negated_conjecture,[],[f21])).
% 3.75/0.98  
% 3.75/0.98  fof(f31,plain,(
% 3.75/0.98    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 3.75/0.98    inference(ennf_transformation,[],[f22])).
% 3.75/0.98  
% 3.75/0.98  fof(f46,plain,(
% 3.75/0.98    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK3 != sK6 & sK3 != sK5 & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)))),
% 3.75/0.98    introduced(choice_axiom,[])).
% 3.75/0.98  
% 3.75/0.98  fof(f47,plain,(
% 3.75/0.98    sK3 != sK6 & sK3 != sK5 & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))),
% 3.75/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f31,f46])).
% 3.75/0.98  
% 3.75/0.98  fof(f82,plain,(
% 3.75/0.98    r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))),
% 3.75/0.98    inference(cnf_transformation,[],[f47])).
% 3.75/0.98  
% 3.75/0.98  fof(f113,plain,(
% 3.75/0.98    r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))),
% 3.75/0.98    inference(definition_unfolding,[],[f82,f89,f89])).
% 3.75/0.98  
% 3.75/0.98  fof(f5,axiom,(
% 3.75/0.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f27,plain,(
% 3.75/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.75/0.98    inference(ennf_transformation,[],[f5])).
% 3.75/0.98  
% 3.75/0.98  fof(f28,plain,(
% 3.75/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.75/0.98    inference(flattening,[],[f27])).
% 3.75/0.98  
% 3.75/0.98  fof(f53,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f28])).
% 3.75/0.98  
% 3.75/0.98  fof(f75,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 3.75/0.98    inference(cnf_transformation,[],[f44])).
% 3.75/0.98  
% 3.75/0.98  fof(f110,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0 | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 3.75/0.98    inference(definition_unfolding,[],[f75,f89,f90,f90,f89])).
% 3.75/0.98  
% 3.75/0.98  fof(f20,axiom,(
% 3.75/0.98    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f45,plain,(
% 3.75/0.98    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 3.75/0.98    inference(nnf_transformation,[],[f20])).
% 3.75/0.98  
% 3.75/0.98  fof(f80,plain,(
% 3.75/0.98    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f45])).
% 3.75/0.98  
% 3.75/0.98  fof(f112,plain,(
% 3.75/0.98    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.75/0.98    inference(definition_unfolding,[],[f80,f90,f90,f90])).
% 3.75/0.98  
% 3.75/0.98  fof(f124,plain,(
% 3.75/0.98    ( ! [X1] : (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 3.75/0.98    inference(equality_resolution,[],[f112])).
% 3.75/0.98  
% 3.75/0.98  fof(f83,plain,(
% 3.75/0.98    sK3 != sK5),
% 3.75/0.98    inference(cnf_transformation,[],[f47])).
% 3.75/0.98  
% 3.75/0.98  fof(f84,plain,(
% 3.75/0.98    sK3 != sK6),
% 3.75/0.98    inference(cnf_transformation,[],[f47])).
% 3.75/0.98  
% 3.75/0.98  fof(f81,plain,(
% 3.75/0.98    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 3.75/0.98    inference(cnf_transformation,[],[f45])).
% 3.75/0.98  
% 3.75/0.98  fof(f111,plain,(
% 3.75/0.98    ( ! [X0,X1] : (k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | X0 = X1) )),
% 3.75/0.98    inference(definition_unfolding,[],[f81,f90,f90,f90])).
% 3.75/0.98  
% 3.75/0.98  fof(f10,axiom,(
% 3.75/0.98    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f36,plain,(
% 3.75/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.75/0.98    inference(nnf_transformation,[],[f10])).
% 3.75/0.98  
% 3.75/0.98  fof(f37,plain,(
% 3.75/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.75/0.98    inference(flattening,[],[f36])).
% 3.75/0.98  
% 3.75/0.98  fof(f38,plain,(
% 3.75/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.75/0.98    inference(rectify,[],[f37])).
% 3.75/0.98  
% 3.75/0.98  fof(f39,plain,(
% 3.75/0.98    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.75/0.98    introduced(choice_axiom,[])).
% 3.75/0.98  
% 3.75/0.98  fof(f40,plain,(
% 3.75/0.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.75/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 3.75/0.98  
% 3.75/0.98  fof(f59,plain,(
% 3.75/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.75/0.98    inference(cnf_transformation,[],[f40])).
% 3.75/0.98  
% 3.75/0.98  fof(f100,plain,(
% 3.75/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 3.75/0.98    inference(definition_unfolding,[],[f59,f89])).
% 3.75/0.98  
% 3.75/0.98  fof(f116,plain,(
% 3.75/0.98    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1) != X2) )),
% 3.75/0.98    inference(equality_resolution,[],[f100])).
% 3.75/0.98  
% 3.75/0.98  fof(f117,plain,(
% 3.75/0.98    ( ! [X4,X1] : (r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X1))) )),
% 3.75/0.98    inference(equality_resolution,[],[f116])).
% 3.75/0.98  
% 3.75/0.98  fof(f58,plain,(
% 3.75/0.98    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.75/0.98    inference(cnf_transformation,[],[f40])).
% 3.75/0.98  
% 3.75/0.98  fof(f101,plain,(
% 3.75/0.98    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 3.75/0.98    inference(definition_unfolding,[],[f58,f89])).
% 3.75/0.98  
% 3.75/0.98  fof(f118,plain,(
% 3.75/0.98    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.75/0.98    inference(equality_resolution,[],[f101])).
% 3.75/0.98  
% 3.75/0.98  fof(f18,axiom,(
% 3.75/0.98    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f41,plain,(
% 3.75/0.98    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 3.75/0.98    inference(nnf_transformation,[],[f18])).
% 3.75/0.98  
% 3.75/0.98  fof(f42,plain,(
% 3.75/0.98    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 3.75/0.98    inference(flattening,[],[f41])).
% 3.75/0.98  
% 3.75/0.98  fof(f71,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)) )),
% 3.75/0.98    inference(cnf_transformation,[],[f42])).
% 3.75/0.98  
% 3.75/0.98  fof(f105,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.75/0.98    inference(definition_unfolding,[],[f71,f89,f90])).
% 3.75/0.98  
% 3.75/0.98  fof(f78,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 3.75/0.98    inference(cnf_transformation,[],[f44])).
% 3.75/0.98  
% 3.75/0.98  fof(f107,plain,(
% 3.75/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X0) )),
% 3.75/0.98    inference(definition_unfolding,[],[f78,f89,f90])).
% 3.75/0.98  
% 3.75/0.98  fof(f121,plain,(
% 3.75/0.98    ( ! [X2,X1] : (r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 3.75/0.98    inference(equality_resolution,[],[f107])).
% 3.75/0.98  
% 3.75/0.98  fof(f1,axiom,(
% 3.75/0.98    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f23,plain,(
% 3.75/0.98    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.75/0.98    inference(rectify,[],[f1])).
% 3.75/0.98  
% 3.75/0.98  fof(f48,plain,(
% 3.75/0.98    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.75/0.98    inference(cnf_transformation,[],[f23])).
% 3.75/0.98  
% 3.75/0.98  fof(f7,axiom,(
% 3.75/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f55,plain,(
% 3.75/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.75/0.98    inference(cnf_transformation,[],[f7])).
% 3.75/0.98  
% 3.75/0.98  fof(f92,plain,(
% 3.75/0.98    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 3.75/0.98    inference(definition_unfolding,[],[f48,f55])).
% 3.75/0.98  
% 3.75/0.98  fof(f8,axiom,(
% 3.75/0.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f56,plain,(
% 3.75/0.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.75/0.98    inference(cnf_transformation,[],[f8])).
% 3.75/0.98  
% 3.75/0.98  fof(f4,axiom,(
% 3.75/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.75/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.75/0.98  
% 3.75/0.98  fof(f52,plain,(
% 3.75/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.75/0.98    inference(cnf_transformation,[],[f4])).
% 3.75/0.98  
% 3.75/0.98  fof(f91,plain,(
% 3.75/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.75/0.98    inference(definition_unfolding,[],[f52,f55])).
% 3.75/0.98  
% 3.75/0.98  cnf(c_21,plain,
% 3.75/0.98      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 3.75/0.98      inference(cnf_transformation,[],[f122]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_658,plain,
% 3.75/0.98      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_28,negated_conjecture,
% 3.75/0.98      ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
% 3.75/0.98      inference(cnf_transformation,[],[f113]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_655,plain,
% 3.75/0.98      ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) = iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_5,plain,
% 3.75/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.75/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_673,plain,
% 3.75/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.75/0.98      | r1_tarski(X2,X0) != iProver_top
% 3.75/0.98      | r1_tarski(X2,X1) = iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_4658,plain,
% 3.75/0.98      ( r1_tarski(X0,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) = iProver_top
% 3.75/0.98      | r1_tarski(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_655,c_673]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_5096,plain,
% 3.75/0.98      ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) = iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_658,c_4658]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_23,plain,
% 3.75/0.98      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 3.75/0.98      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
% 3.75/0.98      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
% 3.75/0.98      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 3.75/0.98      | k1_xboole_0 = X0 ),
% 3.75/0.98      inference(cnf_transformation,[],[f110]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_656,plain,
% 3.75/0.98      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
% 3.75/0.98      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X2
% 3.75/0.98      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X2
% 3.75/0.98      | k1_xboole_0 = X2
% 3.75/0.98      | r1_tarski(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_5364,plain,
% 3.75/0.98      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 3.75/0.98      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 3.75/0.98      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
% 3.75/0.98      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_5096,c_656]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_25,plain,
% 3.75/0.98      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.75/0.98      inference(cnf_transformation,[],[f124]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_9342,plain,
% 3.75/0.98      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 3.75/0.98      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
% 3.75/0.98      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
% 3.75/0.98      | k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_5364,c_25]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_27,negated_conjecture,
% 3.75/0.98      ( sK3 != sK5 ),
% 3.75/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_26,negated_conjecture,
% 3.75/0.98      ( sK3 != sK6 ),
% 3.75/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_30,plain,
% 3.75/0.98      ( k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_25]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_24,plain,
% 3.75/0.98      ( X0 = X1
% 3.75/0.98      | k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 3.75/0.98      inference(cnf_transformation,[],[f111]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_31,plain,
% 3.75/0.98      ( k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 3.75/0.98      | sK3 = sK3 ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_24]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_13,plain,
% 3.75/0.98      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 3.75/0.98      inference(cnf_transformation,[],[f117]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_57,plain,
% 3.75/0.98      ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_56,plain,
% 3.75/0.98      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_58,plain,
% 3.75/0.98      ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_56]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_281,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_843,plain,
% 3.75/0.98      ( sK5 != X0 | sK3 != X0 | sK3 = sK5 ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_281]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_844,plain,
% 3.75/0.98      ( sK5 != sK3 | sK3 = sK5 | sK3 != sK3 ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_843]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_14,plain,
% 3.75/0.98      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 3.75/0.98      | X0 = X1
% 3.75/0.98      | X0 = X2 ),
% 3.75/0.98      inference(cnf_transformation,[],[f118]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_868,plain,
% 3.75/0.98      ( ~ r2_hidden(sK3,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0))
% 3.75/0.98      | sK3 = X0
% 3.75/0.98      | sK3 = sK6 ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1007,plain,
% 3.75/0.98      ( ~ r2_hidden(sK3,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 3.75/0.98      | sK3 = sK6 ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_868]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_18,plain,
% 3.75/0.98      ( ~ r2_hidden(X0,X1)
% 3.75/0.98      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.75/0.98      inference(cnf_transformation,[],[f105]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_661,plain,
% 3.75/0.98      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 3.75/0.98      | r2_hidden(X0,X2) != iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_6686,plain,
% 3.75/0.98      ( X0 = X1
% 3.75/0.98      | r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_24,c_661]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_9338,plain,
% 3.75/0.98      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 3.75/0.98      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
% 3.75/0.98      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
% 3.75/0.98      | sK5 = X0
% 3.75/0.98      | r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_5364,c_6686]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_9483,plain,
% 3.75/0.98      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 3.75/0.98      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)
% 3.75/0.98      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
% 3.75/0.98      | sK5 = sK3
% 3.75/0.98      | r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_9338]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_20,plain,
% 3.75/0.98      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
% 3.75/0.98      inference(cnf_transformation,[],[f121]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_659,plain,
% 3.75/0.98      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1182,plain,
% 3.75/0.98      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 3.75/0.98      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 3.75/0.98      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 3.75/0.98      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_655,c_656]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1414,plain,
% 3.75/0.98      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = X0
% 3.75/0.98      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 3.75/0.98      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 3.75/0.98      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 3.75/0.98      | k1_xboole_0 = X0
% 3.75/0.98      | r1_tarski(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_1182,c_656]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_4427,plain,
% 3.75/0.98      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 3.75/0.98      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
% 3.75/0.98      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 3.75/0.98      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 3.75/0.98      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_659,c_1414]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_841,plain,
% 3.75/0.98      ( sK6 != X0 | sK3 != X0 | sK3 = sK6 ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_281]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_842,plain,
% 3.75/0.98      ( sK6 != sK3 | sK3 = sK6 | sK3 != sK3 ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_841]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_6698,plain,
% 3.75/0.98      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 3.75/0.98      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 3.75/0.98      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 3.75/0.98      | k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),X0) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 3.75/0.98      | r2_hidden(sK5,X0) != iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_1182,c_661]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_666,plain,
% 3.75/0.98      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_665,plain,
% 3.75/0.98      ( X0 = X1
% 3.75/0.98      | X0 = X2
% 3.75/0.98      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) != iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_6465,plain,
% 3.75/0.98      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 3.75/0.98      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 3.75/0.98      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 3.75/0.98      | sK5 = X0
% 3.75/0.98      | r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_1182,c_665]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_7019,plain,
% 3.75/0.98      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 3.75/0.98      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 3.75/0.98      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 3.75/0.98      | sK5 = sK3 ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_666,c_6465]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_7241,plain,
% 3.75/0.98      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 3.75/0.98      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 3.75/0.98      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 3.75/0.98      inference(global_propositional_subsumption,
% 3.75/0.98                [status(thm)],
% 3.75/0.98                [c_6698,c_27,c_30,c_31,c_844,c_7019]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_7246,plain,
% 3.75/0.98      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 3.75/0.98      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 3.75/0.98      | k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),X0) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 3.75/0.98      | r2_hidden(sK5,X0) != iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_7241,c_661]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_7256,plain,
% 3.75/0.98      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 3.75/0.98      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 3.75/0.98      | sK5 = X0
% 3.75/0.98      | sK6 = X0
% 3.75/0.98      | r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_7241,c_665]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_7922,plain,
% 3.75/0.98      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 3.75/0.98      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 3.75/0.98      | sK5 = sK3
% 3.75/0.98      | sK6 = sK3 ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_666,c_7256]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_8347,plain,
% 3.75/0.98      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)
% 3.75/0.98      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 3.75/0.98      inference(global_propositional_subsumption,
% 3.75/0.98                [status(thm)],
% 3.75/0.98                [c_7246,c_27,c_26,c_30,c_31,c_842,c_844,c_7922]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_8363,plain,
% 3.75/0.98      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 3.75/0.98      | sK6 = X0
% 3.75/0.98      | r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_8347,c_6686]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_8433,plain,
% 3.75/0.98      ( ~ r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 3.75/0.98      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 3.75/0.98      | sK6 = X0 ),
% 3.75/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_8363]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_8435,plain,
% 3.75/0.98      ( ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 3.75/0.98      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0
% 3.75/0.98      | sK6 = sK3 ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_8433]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_10208,plain,
% 3.75/0.98      ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_10396,plain,
% 3.75/0.98      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 3.75/0.98      inference(global_propositional_subsumption,
% 3.75/0.98                [status(thm)],
% 3.75/0.98                [c_4427,c_26,c_30,c_31,c_842,c_8435,c_10208]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_10430,plain,
% 3.75/0.98      ( r2_hidden(sK3,k1_xboole_0) = iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_10396,c_666]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_1,plain,
% 3.75/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.75/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_6685,plain,
% 3.75/0.98      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)
% 3.75/0.98      | r2_hidden(X0,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_1,c_661]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_10425,plain,
% 3.75/0.98      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k1_xboole_0
% 3.75/0.98      | r2_hidden(sK3,k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))) != iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_10396,c_6685]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_10478,plain,
% 3.75/0.98      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k1_xboole_0
% 3.75/0.98      | r2_hidden(sK3,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.75/0.98      inference(light_normalisation,[status(thm)],[c_10425,c_10396]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_7,plain,
% 3.75/0.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.75/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_0,plain,
% 3.75/0.98      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.75/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_953,plain,
% 3.75/0.98      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_963,plain,
% 3.75/0.98      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_7,c_953]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_10481,plain,
% 3.75/0.98      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k1_xboole_0
% 3.75/0.98      | r2_hidden(sK3,k1_xboole_0) != iProver_top ),
% 3.75/0.98      inference(light_normalisation,[status(thm)],[c_10478,c_963]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_285,plain,
% 3.75/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.75/0.98      theory(equality) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_865,plain,
% 3.75/0.98      ( r2_hidden(X0,X1)
% 3.75/0.98      | ~ r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))
% 3.75/0.98      | X0 != X2
% 3.75/0.98      | X1 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3) ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_285]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_11567,plain,
% 3.75/0.98      ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
% 3.75/0.98      | r2_hidden(sK3,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 3.75/0.98      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)
% 3.75/0.98      | sK3 != X0 ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_865]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_11569,plain,
% 3.75/0.98      ( r2_hidden(sK3,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 3.75/0.98      | ~ r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
% 3.75/0.98      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 3.75/0.98      | sK3 != sK3 ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_11567]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_12181,plain,
% 3.75/0.98      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6) ),
% 3.75/0.98      inference(global_propositional_subsumption,
% 3.75/0.98                [status(thm)],
% 3.75/0.98                [c_9342,c_27,c_26,c_30,c_31,c_57,c_58,c_844,c_1007,
% 3.75/0.98                 c_9483,c_10430,c_10481,c_11569]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_12256,plain,
% 3.75/0.98      ( r2_hidden(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 3.75/0.98      inference(superposition,[status(thm)],[c_12181,c_666]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_988,plain,
% 3.75/0.98      ( ~ r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
% 3.75/0.98      | sK5 = X0
% 3.75/0.98      | sK5 = X1 ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_989,plain,
% 3.75/0.98      ( sK5 = X0
% 3.75/0.98      | sK5 = X1
% 3.75/0.98      | r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
% 3.75/0.98      inference(predicate_to_equality,[status(thm)],[c_988]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(c_991,plain,
% 3.75/0.98      ( sK5 = sK3
% 3.75/0.98      | r2_hidden(sK5,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
% 3.75/0.98      inference(instantiation,[status(thm)],[c_989]) ).
% 3.75/0.98  
% 3.75/0.98  cnf(contradiction,plain,
% 3.75/0.98      ( $false ),
% 3.75/0.98      inference(minisat,
% 3.75/0.98                [status(thm)],
% 3.75/0.98                [c_12256,c_991,c_844,c_31,c_30,c_27]) ).
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.75/0.98  
% 3.75/0.98  ------                               Statistics
% 3.75/0.98  
% 3.75/0.98  ------ General
% 3.75/0.98  
% 3.75/0.98  abstr_ref_over_cycles:                  0
% 3.75/0.98  abstr_ref_under_cycles:                 0
% 3.75/0.98  gc_basic_clause_elim:                   0
% 3.75/0.98  forced_gc_time:                         0
% 3.75/0.98  parsing_time:                           0.01
% 3.75/0.98  unif_index_cands_time:                  0.
% 3.75/0.98  unif_index_add_time:                    0.
% 3.75/0.98  orderings_time:                         0.
% 3.75/0.98  out_proof_time:                         0.01
% 3.75/0.98  total_time:                             0.403
% 3.75/0.98  num_of_symbols:                         45
% 3.75/0.98  num_of_terms:                           9653
% 3.75/0.98  
% 3.75/0.98  ------ Preprocessing
% 3.75/0.98  
% 3.75/0.98  num_of_splits:                          0
% 3.75/0.98  num_of_split_atoms:                     0
% 3.75/0.98  num_of_reused_defs:                     0
% 3.75/0.98  num_eq_ax_congr_red:                    16
% 3.75/0.98  num_of_sem_filtered_clauses:            1
% 3.75/0.98  num_of_subtypes:                        0
% 3.75/0.98  monotx_restored_types:                  0
% 3.75/0.98  sat_num_of_epr_types:                   0
% 3.75/0.98  sat_num_of_non_cyclic_types:            0
% 3.75/0.98  sat_guarded_non_collapsed_types:        0
% 3.75/0.98  num_pure_diseq_elim:                    0
% 3.75/0.98  simp_replaced_by:                       0
% 3.75/0.98  res_preprocessed:                       104
% 3.75/0.98  prep_upred:                             0
% 3.75/0.98  prep_unflattend:                        4
% 3.75/0.98  smt_new_axioms:                         0
% 3.75/0.98  pred_elim_cands:                        3
% 3.75/0.98  pred_elim:                              0
% 3.75/0.98  pred_elim_cl:                           0
% 3.75/0.98  pred_elim_cycles:                       1
% 3.75/0.98  merged_defs:                            0
% 3.75/0.98  merged_defs_ncl:                        0
% 3.75/0.98  bin_hyper_res:                          0
% 3.75/0.98  prep_cycles:                            3
% 3.75/0.98  pred_elim_time:                         0.
% 3.75/0.98  splitting_time:                         0.
% 3.75/0.98  sem_filter_time:                        0.
% 3.75/0.98  monotx_time:                            0.001
% 3.75/0.98  subtype_inf_time:                       0.
% 3.75/0.98  
% 3.75/0.98  ------ Problem properties
% 3.75/0.98  
% 3.75/0.98  clauses:                                29
% 3.75/0.98  conjectures:                            3
% 3.75/0.98  epr:                                    4
% 3.75/0.98  horn:                                   20
% 3.75/0.98  ground:                                 3
% 3.75/0.98  unary:                                  14
% 3.75/0.98  binary:                                 7
% 3.75/0.98  lits:                                   55
% 3.75/0.98  lits_eq:                                28
% 3.75/0.98  fd_pure:                                0
% 3.75/0.98  fd_pseudo:                              0
% 3.75/0.98  fd_cond:                                1
% 3.75/0.98  fd_pseudo_cond:                         6
% 3.75/0.98  ac_symbols:                             0
% 3.75/0.98  
% 3.75/0.98  ------ Propositional Solver
% 3.75/0.98  
% 3.75/0.98  prop_solver_calls:                      23
% 3.75/0.98  prop_fast_solver_calls:                 796
% 3.75/0.98  smt_solver_calls:                       0
% 3.75/0.98  smt_fast_solver_calls:                  0
% 3.75/0.98  prop_num_of_clauses:                    4431
% 3.75/0.98  prop_preprocess_simplified:             9393
% 3.75/0.98  prop_fo_subsumed:                       43
% 3.75/0.98  prop_solver_time:                       0.
% 3.75/0.98  smt_solver_time:                        0.
% 3.75/0.98  smt_fast_solver_time:                   0.
% 3.75/0.98  prop_fast_solver_time:                  0.
% 3.75/0.98  prop_unsat_core_time:                   0.
% 3.75/0.98  
% 3.75/0.98  ------ QBF
% 3.75/0.98  
% 3.75/0.98  qbf_q_res:                              0
% 3.75/0.98  qbf_num_tautologies:                    0
% 3.75/0.98  qbf_prep_cycles:                        0
% 3.75/0.98  
% 3.75/0.98  ------ BMC1
% 3.75/0.98  
% 3.75/0.98  bmc1_current_bound:                     -1
% 3.75/0.98  bmc1_last_solved_bound:                 -1
% 3.75/0.98  bmc1_unsat_core_size:                   -1
% 3.75/0.98  bmc1_unsat_core_parents_size:           -1
% 3.75/0.98  bmc1_merge_next_fun:                    0
% 3.75/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.75/0.98  
% 3.75/0.98  ------ Instantiation
% 3.75/0.98  
% 3.75/0.98  inst_num_of_clauses:                    1289
% 3.75/0.98  inst_num_in_passive:                    279
% 3.75/0.98  inst_num_in_active:                     376
% 3.75/0.98  inst_num_in_unprocessed:                634
% 3.75/0.98  inst_num_of_loops:                      500
% 3.75/0.98  inst_num_of_learning_restarts:          0
% 3.75/0.98  inst_num_moves_active_passive:          123
% 3.75/0.98  inst_lit_activity:                      0
% 3.75/0.98  inst_lit_activity_moves:                0
% 3.75/0.98  inst_num_tautologies:                   0
% 3.75/0.98  inst_num_prop_implied:                  0
% 3.75/0.98  inst_num_existing_simplified:           0
% 3.75/0.98  inst_num_eq_res_simplified:             0
% 3.75/0.98  inst_num_child_elim:                    0
% 3.75/0.98  inst_num_of_dismatching_blockings:      716
% 3.75/0.98  inst_num_of_non_proper_insts:           1380
% 3.75/0.98  inst_num_of_duplicates:                 0
% 3.75/0.98  inst_inst_num_from_inst_to_res:         0
% 3.75/0.98  inst_dismatching_checking_time:         0.
% 3.75/0.98  
% 3.75/0.98  ------ Resolution
% 3.75/0.98  
% 3.75/0.98  res_num_of_clauses:                     0
% 3.75/0.98  res_num_in_passive:                     0
% 3.75/0.98  res_num_in_active:                      0
% 3.75/0.98  res_num_of_loops:                       107
% 3.75/0.98  res_forward_subset_subsumed:            283
% 3.75/0.98  res_backward_subset_subsumed:           0
% 3.75/0.98  res_forward_subsumed:                   0
% 3.75/0.98  res_backward_subsumed:                  0
% 3.75/0.98  res_forward_subsumption_resolution:     0
% 3.75/0.98  res_backward_subsumption_resolution:    0
% 3.75/0.98  res_clause_to_clause_subsumption:       1406
% 3.75/0.98  res_orphan_elimination:                 0
% 3.75/0.98  res_tautology_del:                      63
% 3.75/0.98  res_num_eq_res_simplified:              0
% 3.75/0.98  res_num_sel_changes:                    0
% 3.75/0.98  res_moves_from_active_to_pass:          0
% 3.75/0.98  
% 3.75/0.98  ------ Superposition
% 3.75/0.98  
% 3.75/0.98  sup_time_total:                         0.
% 3.75/0.98  sup_time_generating:                    0.
% 3.75/0.98  sup_time_sim_full:                      0.
% 3.75/0.98  sup_time_sim_immed:                     0.
% 3.75/0.98  
% 3.75/0.98  sup_num_of_clauses:                     178
% 3.75/0.98  sup_num_in_active:                      46
% 3.75/0.98  sup_num_in_passive:                     132
% 3.75/0.98  sup_num_of_loops:                       98
% 3.75/0.98  sup_fw_superposition:                   311
% 3.75/0.98  sup_bw_superposition:                   307
% 3.75/0.98  sup_immediate_simplified:               131
% 3.75/0.98  sup_given_eliminated:                   3
% 3.75/0.98  comparisons_done:                       0
% 3.75/0.98  comparisons_avoided:                    90
% 3.75/0.98  
% 3.75/0.98  ------ Simplifications
% 3.75/0.98  
% 3.75/0.98  
% 3.75/0.98  sim_fw_subset_subsumed:                 37
% 3.75/0.98  sim_bw_subset_subsumed:                 113
% 3.75/0.98  sim_fw_subsumed:                        40
% 3.75/0.98  sim_bw_subsumed:                        4
% 3.75/0.98  sim_fw_subsumption_res:                 0
% 3.75/0.98  sim_bw_subsumption_res:                 0
% 3.75/0.98  sim_tautology_del:                      7
% 3.75/0.98  sim_eq_tautology_del:                   94
% 3.75/0.98  sim_eq_res_simp:                        0
% 3.75/0.98  sim_fw_demodulated:                     37
% 3.75/0.98  sim_bw_demodulated:                     26
% 3.75/0.98  sim_light_normalised:                   25
% 3.75/0.98  sim_joinable_taut:                      0
% 3.75/0.98  sim_joinable_simp:                      0
% 3.75/0.98  sim_ac_normalised:                      0
% 3.75/0.98  sim_smt_subsumption:                    0
% 3.75/0.98  
%------------------------------------------------------------------------------
