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
% DateTime   : Thu Dec  3 11:32:10 EST 2020

% Result     : Theorem 51.83s
% Output     : CNFRefutation 51.83s
% Verified   : 
% Statistics : Number of formulae       :  177 (1223 expanded)
%              Number of clauses        :  101 ( 238 expanded)
%              Number of leaves         :   23 ( 347 expanded)
%              Depth                    :   12
%              Number of atoms          :  501 (3070 expanded)
%              Number of equality atoms :  286 (2052 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
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

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f85,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f75,f76])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f74,f85])).

fof(f88,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f73,f86])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f71,f88])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f46,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK6
        | k1_tarski(sK4) != sK5 )
      & ( k1_tarski(sK4) != sK6
        | k1_xboole_0 != sK5 )
      & ( k1_tarski(sK4) != sK6
        | k1_tarski(sK4) != sK5 )
      & k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ( k1_xboole_0 != sK6
      | k1_tarski(sK4) != sK5 )
    & ( k1_tarski(sK4) != sK6
      | k1_xboole_0 != sK5 )
    & ( k1_tarski(sK4) != sK6
      | k1_tarski(sK4) != sK5 )
    & k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f26,f46])).

fof(f82,plain,
    ( k1_tarski(sK4) != sK6
    | k1_tarski(sK4) != sK5 ),
    inference(cnf_transformation,[],[f47])).

fof(f105,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK5 ),
    inference(definition_unfolding,[],[f82,f88,f88])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f69,f88])).

fof(f114,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f99])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f70,f88])).

fof(f112,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f98])).

fof(f113,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f112])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f36])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,
    ( k1_tarski(sK4) != sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f47])).

fof(f104,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6
    | k1_xboole_0 != sK5 ),
    inference(definition_unfolding,[],[f83,f88])).

fof(f81,plain,(
    k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f87,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f77,f86])).

fof(f106,plain,(
    k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
    inference(definition_unfolding,[],[f81,f87,f88])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f95,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f68,f87])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f44])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f80,f86])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f89,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f48,f87,f87])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f84,plain,
    ( k1_xboole_0 != sK6
    | k1_tarski(sK4) != sK5 ),
    inference(cnf_transformation,[],[f47])).

fof(f103,plain,
    ( k1_xboole_0 != sK6
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK5 ),
    inference(definition_unfolding,[],[f84,f88])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f111,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f87])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

cnf(c_403,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1305,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK6)
    | X2 != X0
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_403])).

cnf(c_2746,plain,
    ( ~ r1_tarski(X0,sK6)
    | r1_tarski(X1,sK6)
    | X1 != X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_31415,plain,
    ( ~ r1_tarski(X0,sK6)
    | r1_tarski(sK5,sK6)
    | sK5 != X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2746])).

cnf(c_237624,plain,
    ( r1_tarski(sK5,sK6)
    | ~ r1_tarski(sK6,sK6)
    | sK5 != sK6
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_31415])).

cnf(c_400,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1108,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_4573,plain,
    ( sK5 != X0
    | sK6 != X0
    | sK6 = sK5 ),
    inference(instantiation,[status(thm)],[c_1108])).

cnf(c_87060,plain,
    ( sK5 != k1_xboole_0
    | sK6 = sK5
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4573])).

cnf(c_404,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3897,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,sK5)
    | X2 != X0
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_67149,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK5,k1_xboole_0))
    | r2_hidden(X1,sK5)
    | X1 != X0
    | sK5 != k4_xboole_0(sK5,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3897])).

cnf(c_67160,plain,
    ( ~ r2_hidden(sK4,k4_xboole_0(sK5,k1_xboole_0))
    | r2_hidden(sK4,sK5)
    | sK5 != k4_xboole_0(sK5,k1_xboole_0)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_67149])).

cnf(c_22,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | k3_enumset1(X0,X0,X0,X0,X0) = X1
    | sK3(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_30,negated_conjecture,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK5
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_5162,plain,
    ( r2_hidden(sK3(sK4,sK5),sK5)
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6
    | sK3(sK4,sK5) = sK4 ),
    inference(resolution,[status(thm)],[c_22,c_30])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5959,plain,
    ( r2_hidden(sK3(sK4,sK5),sK5)
    | ~ r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK6)
    | ~ r1_tarski(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | sK3(sK4,sK5) = sK4 ),
    inference(resolution,[status(thm)],[c_5162,c_11])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_40,plain,
    ( ~ r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_23,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_43,plain,
    ( r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_10,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_852,plain,
    ( r2_hidden(sK2(sK5),sK5)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_29,negated_conjecture,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1010,plain,
    ( ~ r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK6)
    | ~ r1_tarski(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | k1_xboole_0 != sK5 ),
    inference(resolution,[status(thm)],[c_11,c_29])).

cnf(c_31,negated_conjecture,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_20,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_781,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2217,plain,
    ( r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_31,c_781])).

cnf(c_2223,plain,
    ( r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2217])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2366,plain,
    ( ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(X1,sK5)
    | r1_tarski(k3_enumset1(X1,X1,X1,X1,X0),sK5) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2372,plain,
    ( ~ r2_hidden(sK4,sK5)
    | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_2366])).

cnf(c_399,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2626,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_399])).

cnf(c_0,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2214,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_781])).

cnf(c_3511,plain,
    ( r1_tarski(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_31,c_2214])).

cnf(c_3519,plain,
    ( r1_tarski(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3511])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1021,plain,
    ( r2_hidden(sK2(sK5),X0)
    | ~ r2_hidden(sK2(sK5),sK5)
    | ~ r1_tarski(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3843,plain,
    ( r2_hidden(sK2(sK5),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK2(sK5),sK5)
    | ~ r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_1021])).

cnf(c_1022,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2(sK5),sK5)
    | X0 != sK2(sK5)
    | X1 != sK5 ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_7481,plain,
    ( r2_hidden(X0,sK5)
    | ~ r2_hidden(sK2(sK5),sK5)
    | X0 != sK2(sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1022])).

cnf(c_7483,plain,
    ( ~ r2_hidden(sK2(sK5),sK5)
    | r2_hidden(sK4,sK5)
    | sK5 != sK5
    | sK4 != sK2(sK5) ),
    inference(instantiation,[status(thm)],[c_7481])).

cnf(c_12984,plain,
    ( X0 != X1
    | X0 = sK2(sK5)
    | sK2(sK5) != X1 ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_12985,plain,
    ( sK2(sK5) != sK4
    | sK4 = sK2(sK5)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_12984])).

cnf(c_38682,plain,
    ( ~ r2_hidden(sK2(sK5),k3_enumset1(X0,X0,X0,X0,X0))
    | sK2(sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_38684,plain,
    ( ~ r2_hidden(sK2(sK5),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | sK2(sK5) = sK4 ),
    inference(instantiation,[status(thm)],[c_38682])).

cnf(c_1007,plain,
    ( ~ r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)
    | ~ r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6 ),
    inference(resolution,[status(thm)],[c_11,c_30])).

cnf(c_5166,plain,
    ( r2_hidden(sK3(sK4,sK6),sK6)
    | ~ r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)
    | ~ r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | sK3(sK4,sK6) = sK4 ),
    inference(resolution,[status(thm)],[c_22,c_1007])).

cnf(c_849,plain,
    ( r2_hidden(sK2(sK6),sK6)
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_28,negated_conjecture,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK5
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1006,plain,
    ( ~ r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)
    | ~ r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | k1_xboole_0 != sK6 ),
    inference(resolution,[status(thm)],[c_11,c_28])).

cnf(c_1280,plain,
    ( ~ r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)
    | ~ r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK6)
    | ~ r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | ~ r1_tarski(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(resolution,[status(thm)],[c_1007,c_11])).

cnf(c_1103,plain,
    ( ~ r1_tarski(X0,sK6)
    | ~ r1_tarski(sK6,X0)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1299,plain,
    ( ~ r1_tarski(sK6,sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1103])).

cnf(c_13,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1300,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_974,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2(sK6),sK6)
    | X0 != sK2(sK6)
    | X1 != sK6 ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_1359,plain,
    ( r2_hidden(X0,sK6)
    | ~ r2_hidden(sK2(sK6),sK6)
    | X0 != sK2(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_974])).

cnf(c_1362,plain,
    ( ~ r2_hidden(sK2(sK6),sK6)
    | r2_hidden(sK4,sK6)
    | sK4 != sK2(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1359])).

cnf(c_1564,plain,
    ( ~ r2_hidden(sK4,sK6)
    | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK6) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2793,plain,
    ( X0 != X1
    | X0 = sK2(sK6)
    | sK2(sK6) != X1 ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_2794,plain,
    ( sK2(sK6) != sK4
    | sK4 = sK2(sK6)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2793])).

cnf(c_13064,plain,
    ( ~ r2_hidden(sK2(sK6),k3_enumset1(X0,X0,X0,X0,X0))
    | sK2(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_13066,plain,
    ( ~ r2_hidden(sK2(sK6),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | sK2(sK6) = sK4 ),
    inference(instantiation,[status(thm)],[c_13064])).

cnf(c_973,plain,
    ( r2_hidden(sK2(sK6),X0)
    | ~ r2_hidden(sK2(sK6),sK6)
    | ~ r1_tarski(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_32232,plain,
    ( r2_hidden(sK2(sK6),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK2(sK6),sK6)
    | ~ r1_tarski(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_973])).

cnf(c_55079,plain,
    ( ~ r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5166,c_40,c_43,c_849,c_1006,c_1280,c_1299,c_1300,c_1362,c_1564,c_2223,c_2794,c_3519,c_13066,c_32232])).

cnf(c_56240,plain,
    ( ~ r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5959,c_40,c_43,c_849,c_852,c_1006,c_1010,c_1280,c_1299,c_1300,c_1362,c_1564,c_2223,c_2372,c_2626,c_2794,c_3519,c_3843,c_7483,c_12985,c_13066,c_32232,c_38684])).

cnf(c_1883,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_7486,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1883])).

cnf(c_46546,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_7486])).

cnf(c_18807,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) != X1
    | sK6 != X1
    | sK6 = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_1108])).

cnf(c_44577,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) != k1_xboole_0
    | sK6 = k3_enumset1(X0,X0,X0,X0,X0)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18807])).

cnf(c_44578,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != k1_xboole_0
    | sK6 = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_44577])).

cnf(c_2211,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1108])).

cnf(c_36313,plain,
    ( sK6 != sK6
    | sK6 = k1_xboole_0
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_2211])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1341,plain,
    ( ~ r1_tarski(X0,sK6)
    | k3_tarski(k3_enumset1(X0,X0,X0,X0,sK6)) = sK6 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_30972,plain,
    ( ~ r1_tarski(sK5,sK6)
    | k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) = sK6 ),
    inference(instantiation,[status(thm)],[c_1341])).

cnf(c_4542,plain,
    ( X0 != X1
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != X1
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_15711,plain,
    ( X0 != k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6))
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) = X0
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_4542])).

cnf(c_28955,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6))
    | k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
    | k1_xboole_0 != k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_15711])).

cnf(c_3643,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_15637,plain,
    ( X0 != sK6
    | k1_xboole_0 = X0
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_3643])).

cnf(c_28954,plain,
    ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) != sK6
    | k1_xboole_0 = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6))
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_15637])).

cnf(c_908,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k3_enumset1(X2,X2,X2,X2,X2))
    | X0 != X2
    | X1 != k3_enumset1(X2,X2,X2,X2,X2) ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_18803,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0))
    | r2_hidden(X1,sK6)
    | X1 != X0
    | sK6 != k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_908])).

cnf(c_18809,plain,
    ( ~ r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
    | r2_hidden(sK4,sK6)
    | sK4 != sK4
    | sK6 != k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_18803])).

cnf(c_14023,plain,
    ( k4_xboole_0(sK5,k1_xboole_0) != sK5
    | sK5 = k4_xboole_0(sK5,k1_xboole_0)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_7486])).

cnf(c_1357,plain,
    ( X0 != X1
    | X0 = sK6
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_5570,plain,
    ( sK5 != X0
    | sK5 = sK6
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_1357])).

cnf(c_13489,plain,
    ( sK5 != sK5
    | sK5 = sK6
    | sK6 != sK5 ),
    inference(instantiation,[status(thm)],[c_5570])).

cnf(c_16,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3948,plain,
    ( k4_xboole_0(sK5,k1_xboole_0) = sK5 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3947,plain,
    ( r2_hidden(X0,k4_xboole_0(sK5,k1_xboole_0))
    | ~ r2_hidden(sK2(sK5),sK5)
    | X0 != sK2(sK5)
    | k4_xboole_0(sK5,k1_xboole_0) != sK5 ),
    inference(instantiation,[status(thm)],[c_1022])).

cnf(c_3950,plain,
    ( ~ r2_hidden(sK2(sK5),sK5)
    | r2_hidden(sK4,k4_xboole_0(sK5,k1_xboole_0))
    | k4_xboole_0(sK5,k1_xboole_0) != sK5
    | sK4 != sK2(sK5) ),
    inference(instantiation,[status(thm)],[c_3947])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_237624,c_87060,c_67160,c_56240,c_55079,c_46546,c_44578,c_38684,c_36313,c_32232,c_30972,c_28955,c_28954,c_18809,c_14023,c_13489,c_13066,c_12985,c_3948,c_3950,c_3843,c_3519,c_2794,c_2626,c_2372,c_2223,c_1564,c_1362,c_1300,c_1299,c_852,c_849,c_43,c_40,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 51.83/7.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.83/7.00  
% 51.83/7.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.83/7.00  
% 51.83/7.00  ------  iProver source info
% 51.83/7.00  
% 51.83/7.00  git: date: 2020-06-30 10:37:57 +0100
% 51.83/7.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.83/7.00  git: non_committed_changes: false
% 51.83/7.00  git: last_make_outside_of_git: false
% 51.83/7.00  
% 51.83/7.00  ------ 
% 51.83/7.00  ------ Parsing...
% 51.83/7.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.83/7.00  
% 51.83/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 51.83/7.00  
% 51.83/7.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.83/7.00  
% 51.83/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.83/7.00  ------ Proving...
% 51.83/7.00  ------ Problem Properties 
% 51.83/7.00  
% 51.83/7.00  
% 51.83/7.00  clauses                                 31
% 51.83/7.00  conjectures                             4
% 51.83/7.00  EPR                                     3
% 51.83/7.00  Horn                                    24
% 51.83/7.00  unary                                   10
% 51.83/7.00  binary                                  12
% 51.83/7.00  lits                                    62
% 51.83/7.00  lits eq                                 24
% 51.83/7.00  fd_pure                                 0
% 51.83/7.00  fd_pseudo                               0
% 51.83/7.00  fd_cond                                 1
% 51.83/7.00  fd_pseudo_cond                          6
% 51.83/7.00  AC symbols                              0
% 51.83/7.00  
% 51.83/7.00  ------ Input Options Time Limit: Unbounded
% 51.83/7.00  
% 51.83/7.00  
% 51.83/7.00  ------ 
% 51.83/7.00  Current options:
% 51.83/7.00  ------ 
% 51.83/7.00  
% 51.83/7.00  
% 51.83/7.00  
% 51.83/7.00  
% 51.83/7.00  ------ Proving...
% 51.83/7.00  
% 51.83/7.00  
% 51.83/7.00  % SZS status Theorem for theBenchmark.p
% 51.83/7.00  
% 51.83/7.00  % SZS output start CNFRefutation for theBenchmark.p
% 51.83/7.00  
% 51.83/7.00  fof(f14,axiom,(
% 51.83/7.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 51.83/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.83/7.00  
% 51.83/7.00  fof(f40,plain,(
% 51.83/7.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 51.83/7.00    inference(nnf_transformation,[],[f14])).
% 51.83/7.00  
% 51.83/7.00  fof(f41,plain,(
% 51.83/7.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 51.83/7.00    inference(rectify,[],[f40])).
% 51.83/7.00  
% 51.83/7.00  fof(f42,plain,(
% 51.83/7.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 51.83/7.00    introduced(choice_axiom,[])).
% 51.83/7.00  
% 51.83/7.00  fof(f43,plain,(
% 51.83/7.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 51.83/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).
% 51.83/7.00  
% 51.83/7.00  fof(f71,plain,(
% 51.83/7.00    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)) )),
% 51.83/7.00    inference(cnf_transformation,[],[f43])).
% 51.83/7.00  
% 51.83/7.00  fof(f15,axiom,(
% 51.83/7.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 51.83/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.83/7.00  
% 51.83/7.00  fof(f73,plain,(
% 51.83/7.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 51.83/7.00    inference(cnf_transformation,[],[f15])).
% 51.83/7.00  
% 51.83/7.00  fof(f16,axiom,(
% 51.83/7.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 51.83/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.83/7.00  
% 51.83/7.00  fof(f74,plain,(
% 51.83/7.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 51.83/7.00    inference(cnf_transformation,[],[f16])).
% 51.83/7.00  
% 51.83/7.00  fof(f17,axiom,(
% 51.83/7.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 51.83/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.83/7.00  
% 51.83/7.00  fof(f75,plain,(
% 51.83/7.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 51.83/7.00    inference(cnf_transformation,[],[f17])).
% 51.83/7.00  
% 51.83/7.00  fof(f18,axiom,(
% 51.83/7.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 51.83/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.83/7.00  
% 51.83/7.00  fof(f76,plain,(
% 51.83/7.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 51.83/7.00    inference(cnf_transformation,[],[f18])).
% 51.83/7.00  
% 51.83/7.00  fof(f85,plain,(
% 51.83/7.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 51.83/7.00    inference(definition_unfolding,[],[f75,f76])).
% 51.83/7.00  
% 51.83/7.00  fof(f86,plain,(
% 51.83/7.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 51.83/7.00    inference(definition_unfolding,[],[f74,f85])).
% 51.83/7.00  
% 51.83/7.00  fof(f88,plain,(
% 51.83/7.00    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 51.83/7.00    inference(definition_unfolding,[],[f73,f86])).
% 51.83/7.00  
% 51.83/7.00  fof(f97,plain,(
% 51.83/7.00    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = X1 | sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)) )),
% 51.83/7.00    inference(definition_unfolding,[],[f71,f88])).
% 51.83/7.00  
% 51.83/7.00  fof(f21,conjecture,(
% 51.83/7.00    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 51.83/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.83/7.00  
% 51.83/7.00  fof(f22,negated_conjecture,(
% 51.83/7.00    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 51.83/7.00    inference(negated_conjecture,[],[f21])).
% 51.83/7.00  
% 51.83/7.00  fof(f26,plain,(
% 51.83/7.00    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 51.83/7.00    inference(ennf_transformation,[],[f22])).
% 51.83/7.00  
% 51.83/7.00  fof(f46,plain,(
% 51.83/7.00    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK6 | k1_tarski(sK4) != sK5) & (k1_tarski(sK4) != sK6 | k1_xboole_0 != sK5) & (k1_tarski(sK4) != sK6 | k1_tarski(sK4) != sK5) & k2_xboole_0(sK5,sK6) = k1_tarski(sK4))),
% 51.83/7.00    introduced(choice_axiom,[])).
% 51.83/7.00  
% 51.83/7.00  fof(f47,plain,(
% 51.83/7.00    (k1_xboole_0 != sK6 | k1_tarski(sK4) != sK5) & (k1_tarski(sK4) != sK6 | k1_xboole_0 != sK5) & (k1_tarski(sK4) != sK6 | k1_tarski(sK4) != sK5) & k2_xboole_0(sK5,sK6) = k1_tarski(sK4)),
% 51.83/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f26,f46])).
% 51.83/7.00  
% 51.83/7.00  fof(f82,plain,(
% 51.83/7.00    k1_tarski(sK4) != sK6 | k1_tarski(sK4) != sK5),
% 51.83/7.00    inference(cnf_transformation,[],[f47])).
% 51.83/7.00  
% 51.83/7.00  fof(f105,plain,(
% 51.83/7.00    k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6 | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK5),
% 51.83/7.00    inference(definition_unfolding,[],[f82,f88,f88])).
% 51.83/7.00  
% 51.83/7.00  fof(f6,axiom,(
% 51.83/7.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 51.83/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.83/7.00  
% 51.83/7.00  fof(f38,plain,(
% 51.83/7.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.83/7.00    inference(nnf_transformation,[],[f6])).
% 51.83/7.00  
% 51.83/7.00  fof(f39,plain,(
% 51.83/7.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.83/7.00    inference(flattening,[],[f38])).
% 51.83/7.00  
% 51.83/7.00  fof(f61,plain,(
% 51.83/7.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 51.83/7.00    inference(cnf_transformation,[],[f39])).
% 51.83/7.00  
% 51.83/7.00  fof(f69,plain,(
% 51.83/7.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 51.83/7.00    inference(cnf_transformation,[],[f43])).
% 51.83/7.00  
% 51.83/7.00  fof(f99,plain,(
% 51.83/7.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 51.83/7.00    inference(definition_unfolding,[],[f69,f88])).
% 51.83/7.00  
% 51.83/7.00  fof(f114,plain,(
% 51.83/7.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 51.83/7.00    inference(equality_resolution,[],[f99])).
% 51.83/7.00  
% 51.83/7.00  fof(f70,plain,(
% 51.83/7.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 51.83/7.00    inference(cnf_transformation,[],[f43])).
% 51.83/7.00  
% 51.83/7.00  fof(f98,plain,(
% 51.83/7.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 51.83/7.00    inference(definition_unfolding,[],[f70,f88])).
% 51.83/7.00  
% 51.83/7.00  fof(f112,plain,(
% 51.83/7.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 51.83/7.00    inference(equality_resolution,[],[f98])).
% 51.83/7.00  
% 51.83/7.00  fof(f113,plain,(
% 51.83/7.00    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 51.83/7.00    inference(equality_resolution,[],[f112])).
% 51.83/7.00  
% 51.83/7.00  fof(f5,axiom,(
% 51.83/7.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 51.83/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.83/7.00  
% 51.83/7.00  fof(f24,plain,(
% 51.83/7.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 51.83/7.00    inference(ennf_transformation,[],[f5])).
% 51.83/7.00  
% 51.83/7.00  fof(f36,plain,(
% 51.83/7.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 51.83/7.00    introduced(choice_axiom,[])).
% 51.83/7.00  
% 51.83/7.00  fof(f37,plain,(
% 51.83/7.00    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 51.83/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f36])).
% 51.83/7.00  
% 51.83/7.00  fof(f58,plain,(
% 51.83/7.00    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 51.83/7.00    inference(cnf_transformation,[],[f37])).
% 51.83/7.00  
% 51.83/7.00  fof(f83,plain,(
% 51.83/7.00    k1_tarski(sK4) != sK6 | k1_xboole_0 != sK5),
% 51.83/7.00    inference(cnf_transformation,[],[f47])).
% 51.83/7.00  
% 51.83/7.00  fof(f104,plain,(
% 51.83/7.00    k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6 | k1_xboole_0 != sK5),
% 51.83/7.00    inference(definition_unfolding,[],[f83,f88])).
% 51.83/7.00  
% 51.83/7.00  fof(f81,plain,(
% 51.83/7.00    k2_xboole_0(sK5,sK6) = k1_tarski(sK4)),
% 51.83/7.00    inference(cnf_transformation,[],[f47])).
% 51.83/7.00  
% 51.83/7.00  fof(f19,axiom,(
% 51.83/7.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 51.83/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.83/7.00  
% 51.83/7.00  fof(f77,plain,(
% 51.83/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 51.83/7.00    inference(cnf_transformation,[],[f19])).
% 51.83/7.00  
% 51.83/7.00  fof(f87,plain,(
% 51.83/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 51.83/7.00    inference(definition_unfolding,[],[f77,f86])).
% 51.83/7.00  
% 51.83/7.00  fof(f106,plain,(
% 51.83/7.00    k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6))),
% 51.83/7.00    inference(definition_unfolding,[],[f81,f87,f88])).
% 51.83/7.00  
% 51.83/7.00  fof(f13,axiom,(
% 51.83/7.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 51.83/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.83/7.00  
% 51.83/7.00  fof(f68,plain,(
% 51.83/7.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 51.83/7.00    inference(cnf_transformation,[],[f13])).
% 51.83/7.00  
% 51.83/7.00  fof(f95,plain,(
% 51.83/7.00    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 51.83/7.00    inference(definition_unfolding,[],[f68,f87])).
% 51.83/7.00  
% 51.83/7.00  fof(f20,axiom,(
% 51.83/7.00    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 51.83/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.83/7.00  
% 51.83/7.00  fof(f44,plain,(
% 51.83/7.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 51.83/7.00    inference(nnf_transformation,[],[f20])).
% 51.83/7.00  
% 51.83/7.00  fof(f45,plain,(
% 51.83/7.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 51.83/7.00    inference(flattening,[],[f44])).
% 51.83/7.00  
% 51.83/7.00  fof(f80,plain,(
% 51.83/7.00    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 51.83/7.00    inference(cnf_transformation,[],[f45])).
% 51.83/7.00  
% 51.83/7.00  fof(f100,plain,(
% 51.83/7.00    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 51.83/7.00    inference(definition_unfolding,[],[f80,f86])).
% 51.83/7.00  
% 51.83/7.00  fof(f1,axiom,(
% 51.83/7.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 51.83/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.83/7.00  
% 51.83/7.00  fof(f48,plain,(
% 51.83/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 51.83/7.00    inference(cnf_transformation,[],[f1])).
% 51.83/7.00  
% 51.83/7.00  fof(f89,plain,(
% 51.83/7.00    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 51.83/7.00    inference(definition_unfolding,[],[f48,f87,f87])).
% 51.83/7.00  
% 51.83/7.00  fof(f3,axiom,(
% 51.83/7.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 51.83/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.83/7.00  
% 51.83/7.00  fof(f23,plain,(
% 51.83/7.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 51.83/7.00    inference(ennf_transformation,[],[f3])).
% 51.83/7.00  
% 51.83/7.00  fof(f27,plain,(
% 51.83/7.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 51.83/7.00    inference(nnf_transformation,[],[f23])).
% 51.83/7.00  
% 51.83/7.00  fof(f28,plain,(
% 51.83/7.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 51.83/7.00    inference(rectify,[],[f27])).
% 51.83/7.00  
% 51.83/7.00  fof(f29,plain,(
% 51.83/7.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 51.83/7.00    introduced(choice_axiom,[])).
% 51.83/7.00  
% 51.83/7.00  fof(f30,plain,(
% 51.83/7.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 51.83/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 51.83/7.00  
% 51.83/7.00  fof(f49,plain,(
% 51.83/7.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 51.83/7.00    inference(cnf_transformation,[],[f30])).
% 51.83/7.00  
% 51.83/7.00  fof(f84,plain,(
% 51.83/7.00    k1_xboole_0 != sK6 | k1_tarski(sK4) != sK5),
% 51.83/7.00    inference(cnf_transformation,[],[f47])).
% 51.83/7.00  
% 51.83/7.00  fof(f103,plain,(
% 51.83/7.00    k1_xboole_0 != sK6 | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK5),
% 51.83/7.00    inference(definition_unfolding,[],[f84,f88])).
% 51.83/7.00  
% 51.83/7.00  fof(f59,plain,(
% 51.83/7.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 51.83/7.00    inference(cnf_transformation,[],[f39])).
% 51.83/7.00  
% 51.83/7.00  fof(f111,plain,(
% 51.83/7.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 51.83/7.00    inference(equality_resolution,[],[f59])).
% 51.83/7.00  
% 51.83/7.00  fof(f7,axiom,(
% 51.83/7.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 51.83/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.83/7.00  
% 51.83/7.00  fof(f25,plain,(
% 51.83/7.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 51.83/7.00    inference(ennf_transformation,[],[f7])).
% 51.83/7.00  
% 51.83/7.00  fof(f62,plain,(
% 51.83/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 51.83/7.00    inference(cnf_transformation,[],[f25])).
% 51.83/7.00  
% 51.83/7.00  fof(f90,plain,(
% 51.83/7.00    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 51.83/7.00    inference(definition_unfolding,[],[f62,f87])).
% 51.83/7.00  
% 51.83/7.00  fof(f9,axiom,(
% 51.83/7.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 51.83/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.83/7.00  
% 51.83/7.00  fof(f64,plain,(
% 51.83/7.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 51.83/7.00    inference(cnf_transformation,[],[f9])).
% 51.83/7.00  
% 51.83/7.00  cnf(c_403,plain,
% 51.83/7.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 51.83/7.00      theory(equality) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_1305,plain,
% 51.83/7.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK6) | X2 != X0 | sK6 != X1 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_403]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_2746,plain,
% 51.83/7.00      ( ~ r1_tarski(X0,sK6) | r1_tarski(X1,sK6) | X1 != X0 | sK6 != sK6 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_1305]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_31415,plain,
% 51.83/7.00      ( ~ r1_tarski(X0,sK6)
% 51.83/7.00      | r1_tarski(sK5,sK6)
% 51.83/7.00      | sK5 != X0
% 51.83/7.00      | sK6 != sK6 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_2746]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_237624,plain,
% 51.83/7.00      ( r1_tarski(sK5,sK6)
% 51.83/7.00      | ~ r1_tarski(sK6,sK6)
% 51.83/7.00      | sK5 != sK6
% 51.83/7.00      | sK6 != sK6 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_31415]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_400,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_1108,plain,
% 51.83/7.00      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_400]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_4573,plain,
% 51.83/7.00      ( sK5 != X0 | sK6 != X0 | sK6 = sK5 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_1108]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_87060,plain,
% 51.83/7.00      ( sK5 != k1_xboole_0 | sK6 = sK5 | sK6 != k1_xboole_0 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_4573]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_404,plain,
% 51.83/7.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 51.83/7.00      theory(equality) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_3897,plain,
% 51.83/7.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,sK5) | X2 != X0 | sK5 != X1 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_404]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_67149,plain,
% 51.83/7.00      ( ~ r2_hidden(X0,k4_xboole_0(sK5,k1_xboole_0))
% 51.83/7.00      | r2_hidden(X1,sK5)
% 51.83/7.00      | X1 != X0
% 51.83/7.00      | sK5 != k4_xboole_0(sK5,k1_xboole_0) ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_3897]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_67160,plain,
% 51.83/7.00      ( ~ r2_hidden(sK4,k4_xboole_0(sK5,k1_xboole_0))
% 51.83/7.00      | r2_hidden(sK4,sK5)
% 51.83/7.00      | sK5 != k4_xboole_0(sK5,k1_xboole_0)
% 51.83/7.00      | sK4 != sK4 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_67149]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_22,plain,
% 51.83/7.00      ( r2_hidden(sK3(X0,X1),X1)
% 51.83/7.00      | k3_enumset1(X0,X0,X0,X0,X0) = X1
% 51.83/7.00      | sK3(X0,X1) = X0 ),
% 51.83/7.00      inference(cnf_transformation,[],[f97]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_30,negated_conjecture,
% 51.83/7.00      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK5
% 51.83/7.00      | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6 ),
% 51.83/7.00      inference(cnf_transformation,[],[f105]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_5162,plain,
% 51.83/7.00      ( r2_hidden(sK3(sK4,sK5),sK5)
% 51.83/7.00      | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6
% 51.83/7.00      | sK3(sK4,sK5) = sK4 ),
% 51.83/7.00      inference(resolution,[status(thm)],[c_22,c_30]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_11,plain,
% 51.83/7.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 51.83/7.00      inference(cnf_transformation,[],[f61]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_5959,plain,
% 51.83/7.00      ( r2_hidden(sK3(sK4,sK5),sK5)
% 51.83/7.00      | ~ r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK6)
% 51.83/7.00      | ~ r1_tarski(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 51.83/7.00      | sK3(sK4,sK5) = sK4 ),
% 51.83/7.00      inference(resolution,[status(thm)],[c_5162,c_11]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_24,plain,
% 51.83/7.00      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1 ),
% 51.83/7.00      inference(cnf_transformation,[],[f114]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_40,plain,
% 51.83/7.00      ( ~ r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) | sK4 = sK4 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_24]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_23,plain,
% 51.83/7.00      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
% 51.83/7.00      inference(cnf_transformation,[],[f113]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_43,plain,
% 51.83/7.00      ( r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_23]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_10,plain,
% 51.83/7.00      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 51.83/7.00      inference(cnf_transformation,[],[f58]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_852,plain,
% 51.83/7.00      ( r2_hidden(sK2(sK5),sK5) | k1_xboole_0 = sK5 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_10]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_29,negated_conjecture,
% 51.83/7.00      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6 | k1_xboole_0 != sK5 ),
% 51.83/7.00      inference(cnf_transformation,[],[f104]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_1010,plain,
% 51.83/7.00      ( ~ r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK6)
% 51.83/7.00      | ~ r1_tarski(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 51.83/7.00      | k1_xboole_0 != sK5 ),
% 51.83/7.00      inference(resolution,[status(thm)],[c_11,c_29]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_31,negated_conjecture,
% 51.83/7.00      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
% 51.83/7.00      inference(cnf_transformation,[],[f106]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_20,plain,
% 51.83/7.00      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
% 51.83/7.00      inference(cnf_transformation,[],[f95]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_781,plain,
% 51.83/7.00      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
% 51.83/7.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_2217,plain,
% 51.83/7.00      ( r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 51.83/7.00      inference(superposition,[status(thm)],[c_31,c_781]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_2223,plain,
% 51.83/7.00      ( r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 51.83/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_2217]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_25,plain,
% 51.83/7.00      ( ~ r2_hidden(X0,X1)
% 51.83/7.00      | ~ r2_hidden(X2,X1)
% 51.83/7.00      | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) ),
% 51.83/7.00      inference(cnf_transformation,[],[f100]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_2366,plain,
% 51.83/7.00      ( ~ r2_hidden(X0,sK5)
% 51.83/7.00      | ~ r2_hidden(X1,sK5)
% 51.83/7.00      | r1_tarski(k3_enumset1(X1,X1,X1,X1,X0),sK5) ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_25]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_2372,plain,
% 51.83/7.00      ( ~ r2_hidden(sK4,sK5)
% 51.83/7.00      | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_2366]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_399,plain,( X0 = X0 ),theory(equality) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_2626,plain,
% 51.83/7.00      ( sK5 = sK5 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_399]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_0,plain,
% 51.83/7.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
% 51.83/7.00      inference(cnf_transformation,[],[f89]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_2214,plain,
% 51.83/7.00      ( r1_tarski(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) = iProver_top ),
% 51.83/7.00      inference(superposition,[status(thm)],[c_0,c_781]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_3511,plain,
% 51.83/7.00      ( r1_tarski(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 51.83/7.00      inference(superposition,[status(thm)],[c_31,c_2214]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_3519,plain,
% 51.83/7.00      ( r1_tarski(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 51.83/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_3511]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_3,plain,
% 51.83/7.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 51.83/7.00      inference(cnf_transformation,[],[f49]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_1021,plain,
% 51.83/7.00      ( r2_hidden(sK2(sK5),X0)
% 51.83/7.00      | ~ r2_hidden(sK2(sK5),sK5)
% 51.83/7.00      | ~ r1_tarski(sK5,X0) ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_3]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_3843,plain,
% 51.83/7.00      ( r2_hidden(sK2(sK5),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 51.83/7.00      | ~ r2_hidden(sK2(sK5),sK5)
% 51.83/7.00      | ~ r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_1021]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_1022,plain,
% 51.83/7.00      ( r2_hidden(X0,X1)
% 51.83/7.00      | ~ r2_hidden(sK2(sK5),sK5)
% 51.83/7.00      | X0 != sK2(sK5)
% 51.83/7.00      | X1 != sK5 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_404]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_7481,plain,
% 51.83/7.00      ( r2_hidden(X0,sK5)
% 51.83/7.00      | ~ r2_hidden(sK2(sK5),sK5)
% 51.83/7.00      | X0 != sK2(sK5)
% 51.83/7.00      | sK5 != sK5 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_1022]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_7483,plain,
% 51.83/7.00      ( ~ r2_hidden(sK2(sK5),sK5)
% 51.83/7.00      | r2_hidden(sK4,sK5)
% 51.83/7.00      | sK5 != sK5
% 51.83/7.00      | sK4 != sK2(sK5) ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_7481]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_12984,plain,
% 51.83/7.00      ( X0 != X1 | X0 = sK2(sK5) | sK2(sK5) != X1 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_400]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_12985,plain,
% 51.83/7.00      ( sK2(sK5) != sK4 | sK4 = sK2(sK5) | sK4 != sK4 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_12984]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_38682,plain,
% 51.83/7.00      ( ~ r2_hidden(sK2(sK5),k3_enumset1(X0,X0,X0,X0,X0))
% 51.83/7.00      | sK2(sK5) = X0 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_24]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_38684,plain,
% 51.83/7.00      ( ~ r2_hidden(sK2(sK5),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 51.83/7.00      | sK2(sK5) = sK4 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_38682]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_1007,plain,
% 51.83/7.00      ( ~ r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)
% 51.83/7.00      | ~ r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 51.83/7.00      | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK6 ),
% 51.83/7.00      inference(resolution,[status(thm)],[c_11,c_30]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_5166,plain,
% 51.83/7.00      ( r2_hidden(sK3(sK4,sK6),sK6)
% 51.83/7.00      | ~ r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)
% 51.83/7.00      | ~ r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 51.83/7.00      | sK3(sK4,sK6) = sK4 ),
% 51.83/7.00      inference(resolution,[status(thm)],[c_22,c_1007]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_849,plain,
% 51.83/7.00      ( r2_hidden(sK2(sK6),sK6) | k1_xboole_0 = sK6 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_10]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_28,negated_conjecture,
% 51.83/7.00      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != sK5 | k1_xboole_0 != sK6 ),
% 51.83/7.00      inference(cnf_transformation,[],[f103]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_1006,plain,
% 51.83/7.00      ( ~ r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)
% 51.83/7.00      | ~ r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 51.83/7.00      | k1_xboole_0 != sK6 ),
% 51.83/7.00      inference(resolution,[status(thm)],[c_11,c_28]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_1280,plain,
% 51.83/7.00      ( ~ r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5)
% 51.83/7.00      | ~ r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK6)
% 51.83/7.00      | ~ r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 51.83/7.00      | ~ r1_tarski(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 51.83/7.00      inference(resolution,[status(thm)],[c_1007,c_11]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_1103,plain,
% 51.83/7.00      ( ~ r1_tarski(X0,sK6) | ~ r1_tarski(sK6,X0) | sK6 = X0 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_11]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_1299,plain,
% 51.83/7.00      ( ~ r1_tarski(sK6,sK6) | sK6 = sK6 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_1103]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_13,plain,
% 51.83/7.00      ( r1_tarski(X0,X0) ),
% 51.83/7.00      inference(cnf_transformation,[],[f111]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_1300,plain,
% 51.83/7.00      ( r1_tarski(sK6,sK6) ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_13]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_974,plain,
% 51.83/7.00      ( r2_hidden(X0,X1)
% 51.83/7.00      | ~ r2_hidden(sK2(sK6),sK6)
% 51.83/7.00      | X0 != sK2(sK6)
% 51.83/7.00      | X1 != sK6 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_404]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_1359,plain,
% 51.83/7.00      ( r2_hidden(X0,sK6)
% 51.83/7.00      | ~ r2_hidden(sK2(sK6),sK6)
% 51.83/7.00      | X0 != sK2(sK6)
% 51.83/7.00      | sK6 != sK6 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_974]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_1362,plain,
% 51.83/7.00      ( ~ r2_hidden(sK2(sK6),sK6)
% 51.83/7.00      | r2_hidden(sK4,sK6)
% 51.83/7.00      | sK4 != sK2(sK6)
% 51.83/7.00      | sK6 != sK6 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_1359]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_1564,plain,
% 51.83/7.00      ( ~ r2_hidden(sK4,sK6)
% 51.83/7.00      | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK6) ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_25]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_2793,plain,
% 51.83/7.00      ( X0 != X1 | X0 = sK2(sK6) | sK2(sK6) != X1 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_400]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_2794,plain,
% 51.83/7.00      ( sK2(sK6) != sK4 | sK4 = sK2(sK6) | sK4 != sK4 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_2793]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_13064,plain,
% 51.83/7.00      ( ~ r2_hidden(sK2(sK6),k3_enumset1(X0,X0,X0,X0,X0))
% 51.83/7.00      | sK2(sK6) = X0 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_24]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_13066,plain,
% 51.83/7.00      ( ~ r2_hidden(sK2(sK6),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 51.83/7.00      | sK2(sK6) = sK4 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_13064]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_973,plain,
% 51.83/7.00      ( r2_hidden(sK2(sK6),X0)
% 51.83/7.00      | ~ r2_hidden(sK2(sK6),sK6)
% 51.83/7.00      | ~ r1_tarski(sK6,X0) ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_3]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_32232,plain,
% 51.83/7.00      ( r2_hidden(sK2(sK6),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 51.83/7.00      | ~ r2_hidden(sK2(sK6),sK6)
% 51.83/7.00      | ~ r1_tarski(sK6,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_973]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_55079,plain,
% 51.83/7.00      ( ~ r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) ),
% 51.83/7.00      inference(global_propositional_subsumption,
% 51.83/7.00                [status(thm)],
% 51.83/7.00                [c_5166,c_40,c_43,c_849,c_1006,c_1280,c_1299,c_1300,
% 51.83/7.00                 c_1362,c_1564,c_2223,c_2794,c_3519,c_13066,c_32232]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_56240,plain,
% 51.83/7.00      ( ~ r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK6) ),
% 51.83/7.00      inference(global_propositional_subsumption,
% 51.83/7.00                [status(thm)],
% 51.83/7.00                [c_5959,c_40,c_43,c_849,c_852,c_1006,c_1010,c_1280,
% 51.83/7.00                 c_1299,c_1300,c_1362,c_1564,c_2223,c_2372,c_2626,c_2794,
% 51.83/7.00                 c_3519,c_3843,c_7483,c_12985,c_13066,c_32232,c_38684]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_1883,plain,
% 51.83/7.00      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_400]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_7486,plain,
% 51.83/7.00      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_1883]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_46546,plain,
% 51.83/7.00      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_7486]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_18807,plain,
% 51.83/7.00      ( k3_enumset1(X0,X0,X0,X0,X0) != X1
% 51.83/7.00      | sK6 != X1
% 51.83/7.00      | sK6 = k3_enumset1(X0,X0,X0,X0,X0) ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_1108]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_44577,plain,
% 51.83/7.00      ( k3_enumset1(X0,X0,X0,X0,X0) != k1_xboole_0
% 51.83/7.00      | sK6 = k3_enumset1(X0,X0,X0,X0,X0)
% 51.83/7.00      | sK6 != k1_xboole_0 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_18807]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_44578,plain,
% 51.83/7.00      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != k1_xboole_0
% 51.83/7.00      | sK6 = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 51.83/7.00      | sK6 != k1_xboole_0 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_44577]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_2211,plain,
% 51.83/7.00      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_1108]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_36313,plain,
% 51.83/7.00      ( sK6 != sK6 | sK6 = k1_xboole_0 | k1_xboole_0 != sK6 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_2211]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_14,plain,
% 51.83/7.00      ( ~ r1_tarski(X0,X1)
% 51.83/7.00      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 ),
% 51.83/7.00      inference(cnf_transformation,[],[f90]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_1341,plain,
% 51.83/7.00      ( ~ r1_tarski(X0,sK6)
% 51.83/7.00      | k3_tarski(k3_enumset1(X0,X0,X0,X0,sK6)) = sK6 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_14]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_30972,plain,
% 51.83/7.00      ( ~ r1_tarski(sK5,sK6)
% 51.83/7.00      | k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) = sK6 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_1341]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_4542,plain,
% 51.83/7.00      ( X0 != X1
% 51.83/7.00      | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != X1
% 51.83/7.00      | k3_enumset1(sK4,sK4,sK4,sK4,sK4) = X0 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_400]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_15711,plain,
% 51.83/7.00      ( X0 != k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6))
% 51.83/7.00      | k3_enumset1(sK4,sK4,sK4,sK4,sK4) = X0
% 51.83/7.00      | k3_enumset1(sK4,sK4,sK4,sK4,sK4) != k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_4542]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_28955,plain,
% 51.83/7.00      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6))
% 51.83/7.00      | k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
% 51.83/7.00      | k1_xboole_0 != k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_15711]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_3643,plain,
% 51.83/7.00      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_400]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_15637,plain,
% 51.83/7.00      ( X0 != sK6 | k1_xboole_0 = X0 | k1_xboole_0 != sK6 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_3643]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_28954,plain,
% 51.83/7.00      ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) != sK6
% 51.83/7.00      | k1_xboole_0 = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6))
% 51.83/7.00      | k1_xboole_0 != sK6 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_15637]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_908,plain,
% 51.83/7.00      ( r2_hidden(X0,X1)
% 51.83/7.00      | ~ r2_hidden(X2,k3_enumset1(X2,X2,X2,X2,X2))
% 51.83/7.00      | X0 != X2
% 51.83/7.00      | X1 != k3_enumset1(X2,X2,X2,X2,X2) ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_404]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_18803,plain,
% 51.83/7.00      ( ~ r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0))
% 51.83/7.00      | r2_hidden(X1,sK6)
% 51.83/7.00      | X1 != X0
% 51.83/7.00      | sK6 != k3_enumset1(X0,X0,X0,X0,X0) ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_908]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_18809,plain,
% 51.83/7.00      ( ~ r2_hidden(sK4,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
% 51.83/7.00      | r2_hidden(sK4,sK6)
% 51.83/7.00      | sK4 != sK4
% 51.83/7.00      | sK6 != k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_18803]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_14023,plain,
% 51.83/7.00      ( k4_xboole_0(sK5,k1_xboole_0) != sK5
% 51.83/7.00      | sK5 = k4_xboole_0(sK5,k1_xboole_0)
% 51.83/7.00      | sK5 != sK5 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_7486]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_1357,plain,
% 51.83/7.00      ( X0 != X1 | X0 = sK6 | sK6 != X1 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_400]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_5570,plain,
% 51.83/7.00      ( sK5 != X0 | sK5 = sK6 | sK6 != X0 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_1357]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_13489,plain,
% 51.83/7.00      ( sK5 != sK5 | sK5 = sK6 | sK6 != sK5 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_5570]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_16,plain,
% 51.83/7.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 51.83/7.00      inference(cnf_transformation,[],[f64]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_3948,plain,
% 51.83/7.00      ( k4_xboole_0(sK5,k1_xboole_0) = sK5 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_16]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_3947,plain,
% 51.83/7.00      ( r2_hidden(X0,k4_xboole_0(sK5,k1_xboole_0))
% 51.83/7.00      | ~ r2_hidden(sK2(sK5),sK5)
% 51.83/7.00      | X0 != sK2(sK5)
% 51.83/7.00      | k4_xboole_0(sK5,k1_xboole_0) != sK5 ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_1022]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(c_3950,plain,
% 51.83/7.00      ( ~ r2_hidden(sK2(sK5),sK5)
% 51.83/7.00      | r2_hidden(sK4,k4_xboole_0(sK5,k1_xboole_0))
% 51.83/7.00      | k4_xboole_0(sK5,k1_xboole_0) != sK5
% 51.83/7.00      | sK4 != sK2(sK5) ),
% 51.83/7.00      inference(instantiation,[status(thm)],[c_3947]) ).
% 51.83/7.00  
% 51.83/7.00  cnf(contradiction,plain,
% 51.83/7.00      ( $false ),
% 51.83/7.00      inference(minisat,
% 51.83/7.00                [status(thm)],
% 51.83/7.00                [c_237624,c_87060,c_67160,c_56240,c_55079,c_46546,
% 51.83/7.00                 c_44578,c_38684,c_36313,c_32232,c_30972,c_28955,c_28954,
% 51.83/7.00                 c_18809,c_14023,c_13489,c_13066,c_12985,c_3948,c_3950,
% 51.83/7.00                 c_3843,c_3519,c_2794,c_2626,c_2372,c_2223,c_1564,c_1362,
% 51.83/7.00                 c_1300,c_1299,c_852,c_849,c_43,c_40,c_31]) ).
% 51.83/7.00  
% 51.83/7.00  
% 51.83/7.00  % SZS output end CNFRefutation for theBenchmark.p
% 51.83/7.00  
% 51.83/7.00  ------                               Statistics
% 51.83/7.00  
% 51.83/7.00  ------ Selected
% 51.83/7.00  
% 51.83/7.00  total_time:                             6.448
% 51.83/7.00  
%------------------------------------------------------------------------------
