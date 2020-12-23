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
% DateTime   : Thu Dec  3 11:32:26 EST 2020

% Result     : Theorem 7.62s
% Output     : CNFRefutation 7.62s
% Verified   : 
% Statistics : Number of formulae       :  204 (4137 expanded)
%              Number of clauses        :   97 ( 550 expanded)
%              Number of leaves         :   30 (1248 expanded)
%              Depth                    :   26
%              Number of atoms          :  523 (6340 expanded)
%              Number of equality atoms :  332 (5271 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f46])).

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f54,plain,
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

fof(f55,plain,
    ( ( k1_xboole_0 != sK6
      | k1_tarski(sK4) != sK5 )
    & ( k1_tarski(sK4) != sK6
      | k1_xboole_0 != sK5 )
    & ( k1_tarski(sK4) != sK6
      | k1_tarski(sK4) != sK5 )
    & k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f36,f54])).

fof(f92,plain,(
    k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f101,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f88,f100])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f86,f87])).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f85,f96])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f84,f97])).

fof(f99,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f83,f98])).

fof(f100,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f82,f99])).

fof(f104,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f81,f100])).

fof(f127,plain,(
    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(definition_unfolding,[],[f92,f101,f104])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f41])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & ~ r2_hidden(sK1(X0,X1,X2),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( r2_hidden(sK1(X0,X1,X2),X1)
          | r2_hidden(sK1(X0,X1,X2),X0)
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & ~ r2_hidden(sK1(X0,X1,X2),X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( r2_hidden(sK1(X0,X1,X2),X1)
            | r2_hidden(sK1(X0,X1,X2),X0)
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f108,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f61,f101])).

fof(f128,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f108])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
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

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f120,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f77,f104])).

fof(f133,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f120])).

fof(f94,plain,
    ( k1_tarski(sK4) != sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f55])).

fof(f125,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
    | k1_xboole_0 != sK5 ),
    inference(definition_unfolding,[],[f94,f104])).

fof(f95,plain,
    ( k1_xboole_0 != sK6
    | k1_tarski(sK4) != sK5 ),
    inference(cnf_transformation,[],[f55])).

fof(f124,plain,
    ( k1_xboole_0 != sK6
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5 ),
    inference(definition_unfolding,[],[f95,f104])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f119,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f78,f104])).

fof(f131,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f119])).

fof(f132,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f131])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) != X0
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
      | sK3(X0,X1) != X0
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f80,f104])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f52])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f91,f100])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f115,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f72,f101,f101,f101])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( k1_xboole_0 = k4_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f102,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f76,f101])).

fof(f103,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f69,f102])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f103])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f5])).

fof(f67,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f112,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f67,f102])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f66,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f111,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f66,f101])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f110,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f59,f101])).

fof(f130,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f110])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f118,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f79,f104])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f109,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f60,f101])).

fof(f129,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f109])).

fof(f93,plain,
    ( k1_tarski(sK4) != sK6
    | k1_tarski(sK4) != sK5 ),
    inference(cnf_transformation,[],[f55])).

fof(f126,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5 ),
    inference(definition_unfolding,[],[f93,f104,f104])).

cnf(c_12,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_865,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_29,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_869,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_20907,plain,
    ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_869])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f133])).

cnf(c_858,plain,
    ( X0 = X1
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21019,plain,
    ( sK4 = X0
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_20907,c_858])).

cnf(c_21239,plain,
    ( sK2(sK6) = sK4
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_865,c_21019])).

cnf(c_27,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_26,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f124])).

cnf(c_38,plain,
    ( ~ r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_21,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_41,plain,
    ( r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_40,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_42,plain,
    ( r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_528,plain,
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

cnf(c_533,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_19,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | sK3(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_952,plain,
    ( ~ r2_hidden(sK3(sK4,sK6),sK6)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6
    | sK3(sK4,sK6) != sK4 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_956,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6
    | sK3(sK4,sK6) != sK4
    | r2_hidden(sK3(sK4,sK6),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_952])).

cnf(c_9,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1071,plain,
    ( r2_xboole_0(X0,sK5)
    | ~ r1_tarski(X0,sK5)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1384,plain,
    ( r2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),sK5)
    | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),sK5)
    | sK5 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(instantiation,[status(thm)],[c_1071])).

cnf(c_1385,plain,
    ( sK5 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)
    | r2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),sK5) = iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1384])).

cnf(c_1387,plain,
    ( sK5 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | r2_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = iProver_top
    | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1385])).

cnf(c_527,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1264,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK3(sK4,sK6),sK6)
    | sK3(sK4,sK6) != X0
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_527])).

cnf(c_1776,plain,
    ( ~ r2_hidden(X0,sK6)
    | r2_hidden(sK3(sK4,sK6),sK6)
    | sK3(sK4,sK6) != X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1264])).

cnf(c_1777,plain,
    ( sK3(sK4,sK6) != X0
    | sK6 != sK6
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(sK3(sK4,sK6),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1776])).

cnf(c_1779,plain,
    ( sK3(sK4,sK6) != sK4
    | sK6 != sK6
    | r2_hidden(sK3(sK4,sK6),sK6) = iProver_top
    | r2_hidden(sK4,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1777])).

cnf(c_1269,plain,
    ( ~ r2_hidden(sK6,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1934,plain,
    ( ~ r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_2576,plain,
    ( ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(X1,sK5)
    | r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),sK5) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2577,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK5) != iProver_top
    | r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2576])).

cnf(c_2579,plain,
    ( r2_hidden(sK4,sK5) != iProver_top
    | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2577])).

cnf(c_3729,plain,
    ( r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_525,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_908,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_3981,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_908])).

cnf(c_919,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_10386,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_919])).

cnf(c_939,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_10394,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK5
    | sK5 != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_939])).

cnf(c_15,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1430,plain,
    ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(superposition,[status(thm)],[c_29,c_15])).

cnf(c_1431,plain,
    ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(light_normalisation,[status(thm)],[c_1430,c_29])).

cnf(c_13,plain,
    ( ~ r2_xboole_0(X0,X1)
    | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_864,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) != k1_xboole_0
    | r2_xboole_0(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_18,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_17,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1214,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_18,c_17])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_10,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_876,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_11,c_10,c_18])).

cnf(c_1217,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1214,c_876])).

cnf(c_1226,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = X2 ),
    inference(superposition,[status(thm)],[c_1217,c_17])).

cnf(c_1228,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = X2 ),
    inference(light_normalisation,[status(thm)],[c_1226,c_17])).

cnf(c_2044,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_1228,c_1217])).

cnf(c_1216,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17,c_18])).

cnf(c_1582,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1216,c_1217])).

cnf(c_1222,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_18,c_1217])).

cnf(c_1590,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_1582,c_1222])).

cnf(c_1736,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1590,c_1217])).

cnf(c_1742,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_17,c_1736])).

cnf(c_1741,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_17,c_1736])).

cnf(c_2458,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1222,c_1741])).

cnf(c_3265,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_1742,c_2458])).

cnf(c_1740,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_17,c_1736])).

cnf(c_2680,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_2458,c_1740])).

cnf(c_3287,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_3265,c_2680])).

cnf(c_15876,plain,
    ( k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) != k1_xboole_0
    | r2_xboole_0(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_864,c_2044,c_3287])).

cnf(c_15886,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != k1_xboole_0
    | r2_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1431,c_15876])).

cnf(c_15887,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15886,c_18])).

cnf(c_15888,plain,
    ( r2_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_15887])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_867,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_18999,plain,
    ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_867])).

cnf(c_19011,plain,
    ( r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(sK4,sK5) = iProver_top
    | r2_hidden(sK4,sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_18999])).

cnf(c_524,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_20857,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_524])).

cnf(c_20,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | sK3(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_860,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | sK3(X0,X1) = X0
    | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21240,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK6
    | sK3(X0,sK6) = X0
    | sK3(X0,sK6) = sK4 ),
    inference(superposition,[status(thm)],[c_860,c_21019])).

cnf(c_21253,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6
    | sK3(sK4,sK6) = sK4 ),
    inference(instantiation,[status(thm)],[c_21240])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_868,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_19206,plain,
    ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_868])).

cnf(c_19347,plain,
    ( sK4 = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_19206,c_858])).

cnf(c_19598,plain,
    ( sK2(sK5) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_865,c_19347])).

cnf(c_22204,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_19598,c_865])).

cnf(c_22206,plain,
    ( sK2(sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21239,c_27,c_26,c_38,c_41,c_42,c_533,c_956,c_1387,c_1779,c_1934,c_2579,c_3729,c_3981,c_10386,c_10394,c_15888,c_19011,c_20857,c_21253,c_22204])).

cnf(c_22208,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_22206,c_865])).

cnf(c_28,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 ),
    inference(cnf_transformation,[],[f126])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22208,c_22204,c_21253,c_20857,c_19011,c_15888,c_10394,c_10386,c_3981,c_3729,c_2579,c_1934,c_1779,c_1387,c_956,c_533,c_42,c_41,c_38,c_26,c_27,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:42:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 7.62/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.62/1.48  
% 7.62/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.62/1.48  
% 7.62/1.48  ------  iProver source info
% 7.62/1.48  
% 7.62/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.62/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.62/1.48  git: non_committed_changes: false
% 7.62/1.48  git: last_make_outside_of_git: false
% 7.62/1.48  
% 7.62/1.48  ------ 
% 7.62/1.48  
% 7.62/1.48  ------ Input Options
% 7.62/1.48  
% 7.62/1.48  --out_options                           all
% 7.62/1.48  --tptp_safe_out                         true
% 7.62/1.48  --problem_path                          ""
% 7.62/1.48  --include_path                          ""
% 7.62/1.48  --clausifier                            res/vclausify_rel
% 7.62/1.48  --clausifier_options                    ""
% 7.62/1.48  --stdin                                 false
% 7.62/1.48  --stats_out                             all
% 7.62/1.48  
% 7.62/1.48  ------ General Options
% 7.62/1.48  
% 7.62/1.48  --fof                                   false
% 7.62/1.48  --time_out_real                         305.
% 7.62/1.48  --time_out_virtual                      -1.
% 7.62/1.48  --symbol_type_check                     false
% 7.62/1.48  --clausify_out                          false
% 7.62/1.48  --sig_cnt_out                           false
% 7.62/1.48  --trig_cnt_out                          false
% 7.62/1.48  --trig_cnt_out_tolerance                1.
% 7.62/1.48  --trig_cnt_out_sk_spl                   false
% 7.62/1.48  --abstr_cl_out                          false
% 7.62/1.48  
% 7.62/1.48  ------ Global Options
% 7.62/1.48  
% 7.62/1.48  --schedule                              default
% 7.62/1.48  --add_important_lit                     false
% 7.62/1.48  --prop_solver_per_cl                    1000
% 7.62/1.48  --min_unsat_core                        false
% 7.62/1.48  --soft_assumptions                      false
% 7.62/1.48  --soft_lemma_size                       3
% 7.62/1.48  --prop_impl_unit_size                   0
% 7.62/1.48  --prop_impl_unit                        []
% 7.62/1.48  --share_sel_clauses                     true
% 7.62/1.48  --reset_solvers                         false
% 7.62/1.48  --bc_imp_inh                            [conj_cone]
% 7.62/1.48  --conj_cone_tolerance                   3.
% 7.62/1.48  --extra_neg_conj                        none
% 7.62/1.48  --large_theory_mode                     true
% 7.62/1.48  --prolific_symb_bound                   200
% 7.62/1.48  --lt_threshold                          2000
% 7.62/1.48  --clause_weak_htbl                      true
% 7.62/1.48  --gc_record_bc_elim                     false
% 7.62/1.48  
% 7.62/1.48  ------ Preprocessing Options
% 7.62/1.48  
% 7.62/1.48  --preprocessing_flag                    true
% 7.62/1.48  --time_out_prep_mult                    0.1
% 7.62/1.48  --splitting_mode                        input
% 7.62/1.48  --splitting_grd                         true
% 7.62/1.48  --splitting_cvd                         false
% 7.62/1.48  --splitting_cvd_svl                     false
% 7.62/1.48  --splitting_nvd                         32
% 7.62/1.48  --sub_typing                            true
% 7.62/1.48  --prep_gs_sim                           true
% 7.62/1.48  --prep_unflatten                        true
% 7.62/1.48  --prep_res_sim                          true
% 7.62/1.48  --prep_upred                            true
% 7.62/1.48  --prep_sem_filter                       exhaustive
% 7.62/1.48  --prep_sem_filter_out                   false
% 7.62/1.48  --pred_elim                             true
% 7.62/1.48  --res_sim_input                         true
% 7.62/1.48  --eq_ax_congr_red                       true
% 7.62/1.48  --pure_diseq_elim                       true
% 7.62/1.48  --brand_transform                       false
% 7.62/1.48  --non_eq_to_eq                          false
% 7.62/1.48  --prep_def_merge                        true
% 7.62/1.48  --prep_def_merge_prop_impl              false
% 7.62/1.48  --prep_def_merge_mbd                    true
% 7.62/1.48  --prep_def_merge_tr_red                 false
% 7.62/1.48  --prep_def_merge_tr_cl                  false
% 7.62/1.48  --smt_preprocessing                     true
% 7.62/1.48  --smt_ac_axioms                         fast
% 7.62/1.48  --preprocessed_out                      false
% 7.62/1.48  --preprocessed_stats                    false
% 7.62/1.48  
% 7.62/1.48  ------ Abstraction refinement Options
% 7.62/1.48  
% 7.62/1.48  --abstr_ref                             []
% 7.62/1.48  --abstr_ref_prep                        false
% 7.62/1.48  --abstr_ref_until_sat                   false
% 7.62/1.48  --abstr_ref_sig_restrict                funpre
% 7.62/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.62/1.48  --abstr_ref_under                       []
% 7.62/1.48  
% 7.62/1.48  ------ SAT Options
% 7.62/1.48  
% 7.62/1.48  --sat_mode                              false
% 7.62/1.48  --sat_fm_restart_options                ""
% 7.62/1.48  --sat_gr_def                            false
% 7.62/1.48  --sat_epr_types                         true
% 7.62/1.48  --sat_non_cyclic_types                  false
% 7.62/1.48  --sat_finite_models                     false
% 7.62/1.48  --sat_fm_lemmas                         false
% 7.62/1.48  --sat_fm_prep                           false
% 7.62/1.48  --sat_fm_uc_incr                        true
% 7.62/1.48  --sat_out_model                         small
% 7.62/1.48  --sat_out_clauses                       false
% 7.62/1.48  
% 7.62/1.48  ------ QBF Options
% 7.62/1.48  
% 7.62/1.48  --qbf_mode                              false
% 7.62/1.48  --qbf_elim_univ                         false
% 7.62/1.48  --qbf_dom_inst                          none
% 7.62/1.48  --qbf_dom_pre_inst                      false
% 7.62/1.48  --qbf_sk_in                             false
% 7.62/1.48  --qbf_pred_elim                         true
% 7.62/1.48  --qbf_split                             512
% 7.62/1.48  
% 7.62/1.48  ------ BMC1 Options
% 7.62/1.48  
% 7.62/1.48  --bmc1_incremental                      false
% 7.62/1.48  --bmc1_axioms                           reachable_all
% 7.62/1.48  --bmc1_min_bound                        0
% 7.62/1.48  --bmc1_max_bound                        -1
% 7.62/1.48  --bmc1_max_bound_default                -1
% 7.62/1.48  --bmc1_symbol_reachability              true
% 7.62/1.48  --bmc1_property_lemmas                  false
% 7.62/1.48  --bmc1_k_induction                      false
% 7.62/1.48  --bmc1_non_equiv_states                 false
% 7.62/1.48  --bmc1_deadlock                         false
% 7.62/1.48  --bmc1_ucm                              false
% 7.62/1.48  --bmc1_add_unsat_core                   none
% 7.62/1.48  --bmc1_unsat_core_children              false
% 7.62/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.62/1.48  --bmc1_out_stat                         full
% 7.62/1.48  --bmc1_ground_init                      false
% 7.62/1.48  --bmc1_pre_inst_next_state              false
% 7.62/1.48  --bmc1_pre_inst_state                   false
% 7.62/1.48  --bmc1_pre_inst_reach_state             false
% 7.62/1.48  --bmc1_out_unsat_core                   false
% 7.62/1.48  --bmc1_aig_witness_out                  false
% 7.62/1.48  --bmc1_verbose                          false
% 7.62/1.48  --bmc1_dump_clauses_tptp                false
% 7.62/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.62/1.48  --bmc1_dump_file                        -
% 7.62/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.62/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.62/1.48  --bmc1_ucm_extend_mode                  1
% 7.62/1.48  --bmc1_ucm_init_mode                    2
% 7.62/1.48  --bmc1_ucm_cone_mode                    none
% 7.62/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.62/1.48  --bmc1_ucm_relax_model                  4
% 7.62/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.62/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.62/1.48  --bmc1_ucm_layered_model                none
% 7.62/1.48  --bmc1_ucm_max_lemma_size               10
% 7.62/1.48  
% 7.62/1.48  ------ AIG Options
% 7.62/1.48  
% 7.62/1.48  --aig_mode                              false
% 7.62/1.48  
% 7.62/1.48  ------ Instantiation Options
% 7.62/1.48  
% 7.62/1.48  --instantiation_flag                    true
% 7.62/1.48  --inst_sos_flag                         true
% 7.62/1.48  --inst_sos_phase                        true
% 7.62/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.62/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.62/1.48  --inst_lit_sel_side                     num_symb
% 7.62/1.48  --inst_solver_per_active                1400
% 7.62/1.48  --inst_solver_calls_frac                1.
% 7.62/1.48  --inst_passive_queue_type               priority_queues
% 7.62/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.62/1.48  --inst_passive_queues_freq              [25;2]
% 7.62/1.48  --inst_dismatching                      true
% 7.62/1.48  --inst_eager_unprocessed_to_passive     true
% 7.62/1.48  --inst_prop_sim_given                   true
% 7.62/1.48  --inst_prop_sim_new                     false
% 7.62/1.48  --inst_subs_new                         false
% 7.62/1.48  --inst_eq_res_simp                      false
% 7.62/1.48  --inst_subs_given                       false
% 7.62/1.48  --inst_orphan_elimination               true
% 7.62/1.48  --inst_learning_loop_flag               true
% 7.62/1.48  --inst_learning_start                   3000
% 7.62/1.48  --inst_learning_factor                  2
% 7.62/1.48  --inst_start_prop_sim_after_learn       3
% 7.62/1.48  --inst_sel_renew                        solver
% 7.62/1.48  --inst_lit_activity_flag                true
% 7.62/1.48  --inst_restr_to_given                   false
% 7.62/1.48  --inst_activity_threshold               500
% 7.62/1.48  --inst_out_proof                        true
% 7.62/1.48  
% 7.62/1.48  ------ Resolution Options
% 7.62/1.48  
% 7.62/1.48  --resolution_flag                       true
% 7.62/1.48  --res_lit_sel                           adaptive
% 7.62/1.48  --res_lit_sel_side                      none
% 7.62/1.48  --res_ordering                          kbo
% 7.62/1.48  --res_to_prop_solver                    active
% 7.62/1.48  --res_prop_simpl_new                    false
% 7.62/1.48  --res_prop_simpl_given                  true
% 7.62/1.48  --res_passive_queue_type                priority_queues
% 7.62/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.62/1.48  --res_passive_queues_freq               [15;5]
% 7.62/1.48  --res_forward_subs                      full
% 7.62/1.48  --res_backward_subs                     full
% 7.62/1.48  --res_forward_subs_resolution           true
% 7.62/1.48  --res_backward_subs_resolution          true
% 7.62/1.48  --res_orphan_elimination                true
% 7.62/1.48  --res_time_limit                        2.
% 7.62/1.48  --res_out_proof                         true
% 7.62/1.48  
% 7.62/1.48  ------ Superposition Options
% 7.62/1.48  
% 7.62/1.48  --superposition_flag                    true
% 7.62/1.48  --sup_passive_queue_type                priority_queues
% 7.62/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.62/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.62/1.48  --demod_completeness_check              fast
% 7.62/1.48  --demod_use_ground                      true
% 7.62/1.48  --sup_to_prop_solver                    passive
% 7.62/1.48  --sup_prop_simpl_new                    true
% 7.62/1.48  --sup_prop_simpl_given                  true
% 7.62/1.48  --sup_fun_splitting                     true
% 7.62/1.48  --sup_smt_interval                      50000
% 7.62/1.48  
% 7.62/1.48  ------ Superposition Simplification Setup
% 7.62/1.48  
% 7.62/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.62/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.62/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.62/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.62/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.62/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.62/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.62/1.48  --sup_immed_triv                        [TrivRules]
% 7.62/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.62/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.62/1.48  --sup_immed_bw_main                     []
% 7.62/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.62/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.62/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.62/1.48  --sup_input_bw                          []
% 7.62/1.48  
% 7.62/1.48  ------ Combination Options
% 7.62/1.48  
% 7.62/1.48  --comb_res_mult                         3
% 7.62/1.48  --comb_sup_mult                         2
% 7.62/1.48  --comb_inst_mult                        10
% 7.62/1.48  
% 7.62/1.48  ------ Debug Options
% 7.62/1.48  
% 7.62/1.48  --dbg_backtrace                         false
% 7.62/1.48  --dbg_dump_prop_clauses                 false
% 7.62/1.48  --dbg_dump_prop_clauses_file            -
% 7.62/1.48  --dbg_out_stat                          false
% 7.62/1.48  ------ Parsing...
% 7.62/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.62/1.48  
% 7.62/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.62/1.48  
% 7.62/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.62/1.48  
% 7.62/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.62/1.48  ------ Proving...
% 7.62/1.48  ------ Problem Properties 
% 7.62/1.48  
% 7.62/1.48  
% 7.62/1.48  clauses                                 30
% 7.62/1.48  conjectures                             4
% 7.62/1.48  EPR                                     2
% 7.62/1.48  Horn                                    24
% 7.62/1.48  unary                                   8
% 7.62/1.48  binary                                  13
% 7.62/1.48  lits                                    62
% 7.62/1.48  lits eq                                 24
% 7.62/1.48  fd_pure                                 0
% 7.62/1.48  fd_pseudo                               0
% 7.62/1.48  fd_cond                                 1
% 7.62/1.48  fd_pseudo_cond                          6
% 7.62/1.48  AC symbols                              0
% 7.62/1.48  
% 7.62/1.48  ------ Schedule dynamic 5 is on 
% 7.62/1.48  
% 7.62/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.62/1.48  
% 7.62/1.48  
% 7.62/1.48  ------ 
% 7.62/1.48  Current options:
% 7.62/1.48  ------ 
% 7.62/1.48  
% 7.62/1.48  ------ Input Options
% 7.62/1.48  
% 7.62/1.48  --out_options                           all
% 7.62/1.48  --tptp_safe_out                         true
% 7.62/1.48  --problem_path                          ""
% 7.62/1.48  --include_path                          ""
% 7.62/1.48  --clausifier                            res/vclausify_rel
% 7.62/1.48  --clausifier_options                    ""
% 7.62/1.48  --stdin                                 false
% 7.62/1.48  --stats_out                             all
% 7.62/1.48  
% 7.62/1.48  ------ General Options
% 7.62/1.48  
% 7.62/1.48  --fof                                   false
% 7.62/1.48  --time_out_real                         305.
% 7.62/1.48  --time_out_virtual                      -1.
% 7.62/1.48  --symbol_type_check                     false
% 7.62/1.48  --clausify_out                          false
% 7.62/1.48  --sig_cnt_out                           false
% 7.62/1.48  --trig_cnt_out                          false
% 7.62/1.48  --trig_cnt_out_tolerance                1.
% 7.62/1.48  --trig_cnt_out_sk_spl                   false
% 7.62/1.48  --abstr_cl_out                          false
% 7.62/1.48  
% 7.62/1.48  ------ Global Options
% 7.62/1.48  
% 7.62/1.48  --schedule                              default
% 7.62/1.48  --add_important_lit                     false
% 7.62/1.48  --prop_solver_per_cl                    1000
% 7.62/1.48  --min_unsat_core                        false
% 7.62/1.48  --soft_assumptions                      false
% 7.62/1.48  --soft_lemma_size                       3
% 7.62/1.48  --prop_impl_unit_size                   0
% 7.62/1.48  --prop_impl_unit                        []
% 7.62/1.48  --share_sel_clauses                     true
% 7.62/1.48  --reset_solvers                         false
% 7.62/1.48  --bc_imp_inh                            [conj_cone]
% 7.62/1.48  --conj_cone_tolerance                   3.
% 7.62/1.48  --extra_neg_conj                        none
% 7.62/1.48  --large_theory_mode                     true
% 7.62/1.48  --prolific_symb_bound                   200
% 7.62/1.48  --lt_threshold                          2000
% 7.62/1.48  --clause_weak_htbl                      true
% 7.62/1.48  --gc_record_bc_elim                     false
% 7.62/1.48  
% 7.62/1.48  ------ Preprocessing Options
% 7.62/1.48  
% 7.62/1.48  --preprocessing_flag                    true
% 7.62/1.48  --time_out_prep_mult                    0.1
% 7.62/1.48  --splitting_mode                        input
% 7.62/1.48  --splitting_grd                         true
% 7.62/1.48  --splitting_cvd                         false
% 7.62/1.48  --splitting_cvd_svl                     false
% 7.62/1.48  --splitting_nvd                         32
% 7.62/1.48  --sub_typing                            true
% 7.62/1.48  --prep_gs_sim                           true
% 7.62/1.48  --prep_unflatten                        true
% 7.62/1.48  --prep_res_sim                          true
% 7.62/1.48  --prep_upred                            true
% 7.62/1.48  --prep_sem_filter                       exhaustive
% 7.62/1.48  --prep_sem_filter_out                   false
% 7.62/1.48  --pred_elim                             true
% 7.62/1.48  --res_sim_input                         true
% 7.62/1.48  --eq_ax_congr_red                       true
% 7.62/1.48  --pure_diseq_elim                       true
% 7.62/1.48  --brand_transform                       false
% 7.62/1.48  --non_eq_to_eq                          false
% 7.62/1.48  --prep_def_merge                        true
% 7.62/1.48  --prep_def_merge_prop_impl              false
% 7.62/1.48  --prep_def_merge_mbd                    true
% 7.62/1.48  --prep_def_merge_tr_red                 false
% 7.62/1.48  --prep_def_merge_tr_cl                  false
% 7.62/1.48  --smt_preprocessing                     true
% 7.62/1.48  --smt_ac_axioms                         fast
% 7.62/1.48  --preprocessed_out                      false
% 7.62/1.48  --preprocessed_stats                    false
% 7.62/1.48  
% 7.62/1.48  ------ Abstraction refinement Options
% 7.62/1.48  
% 7.62/1.48  --abstr_ref                             []
% 7.62/1.48  --abstr_ref_prep                        false
% 7.62/1.48  --abstr_ref_until_sat                   false
% 7.62/1.48  --abstr_ref_sig_restrict                funpre
% 7.62/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.62/1.48  --abstr_ref_under                       []
% 7.62/1.48  
% 7.62/1.48  ------ SAT Options
% 7.62/1.48  
% 7.62/1.48  --sat_mode                              false
% 7.62/1.48  --sat_fm_restart_options                ""
% 7.62/1.48  --sat_gr_def                            false
% 7.62/1.48  --sat_epr_types                         true
% 7.62/1.48  --sat_non_cyclic_types                  false
% 7.62/1.48  --sat_finite_models                     false
% 7.62/1.48  --sat_fm_lemmas                         false
% 7.62/1.48  --sat_fm_prep                           false
% 7.62/1.48  --sat_fm_uc_incr                        true
% 7.62/1.48  --sat_out_model                         small
% 7.62/1.48  --sat_out_clauses                       false
% 7.62/1.48  
% 7.62/1.48  ------ QBF Options
% 7.62/1.48  
% 7.62/1.48  --qbf_mode                              false
% 7.62/1.48  --qbf_elim_univ                         false
% 7.62/1.48  --qbf_dom_inst                          none
% 7.62/1.48  --qbf_dom_pre_inst                      false
% 7.62/1.48  --qbf_sk_in                             false
% 7.62/1.48  --qbf_pred_elim                         true
% 7.62/1.48  --qbf_split                             512
% 7.62/1.48  
% 7.62/1.48  ------ BMC1 Options
% 7.62/1.48  
% 7.62/1.48  --bmc1_incremental                      false
% 7.62/1.48  --bmc1_axioms                           reachable_all
% 7.62/1.48  --bmc1_min_bound                        0
% 7.62/1.48  --bmc1_max_bound                        -1
% 7.62/1.48  --bmc1_max_bound_default                -1
% 7.62/1.48  --bmc1_symbol_reachability              true
% 7.62/1.48  --bmc1_property_lemmas                  false
% 7.62/1.48  --bmc1_k_induction                      false
% 7.62/1.48  --bmc1_non_equiv_states                 false
% 7.62/1.48  --bmc1_deadlock                         false
% 7.62/1.48  --bmc1_ucm                              false
% 7.62/1.48  --bmc1_add_unsat_core                   none
% 7.62/1.48  --bmc1_unsat_core_children              false
% 7.62/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.62/1.48  --bmc1_out_stat                         full
% 7.62/1.48  --bmc1_ground_init                      false
% 7.62/1.48  --bmc1_pre_inst_next_state              false
% 7.62/1.48  --bmc1_pre_inst_state                   false
% 7.62/1.48  --bmc1_pre_inst_reach_state             false
% 7.62/1.48  --bmc1_out_unsat_core                   false
% 7.62/1.48  --bmc1_aig_witness_out                  false
% 7.62/1.48  --bmc1_verbose                          false
% 7.62/1.48  --bmc1_dump_clauses_tptp                false
% 7.62/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.62/1.48  --bmc1_dump_file                        -
% 7.62/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.62/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.62/1.48  --bmc1_ucm_extend_mode                  1
% 7.62/1.48  --bmc1_ucm_init_mode                    2
% 7.62/1.48  --bmc1_ucm_cone_mode                    none
% 7.62/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.62/1.48  --bmc1_ucm_relax_model                  4
% 7.62/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.62/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.62/1.48  --bmc1_ucm_layered_model                none
% 7.62/1.48  --bmc1_ucm_max_lemma_size               10
% 7.62/1.48  
% 7.62/1.48  ------ AIG Options
% 7.62/1.48  
% 7.62/1.48  --aig_mode                              false
% 7.62/1.48  
% 7.62/1.48  ------ Instantiation Options
% 7.62/1.48  
% 7.62/1.48  --instantiation_flag                    true
% 7.62/1.48  --inst_sos_flag                         true
% 7.62/1.48  --inst_sos_phase                        true
% 7.62/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.62/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.62/1.48  --inst_lit_sel_side                     none
% 7.62/1.48  --inst_solver_per_active                1400
% 7.62/1.48  --inst_solver_calls_frac                1.
% 7.62/1.48  --inst_passive_queue_type               priority_queues
% 7.62/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.62/1.48  --inst_passive_queues_freq              [25;2]
% 7.62/1.48  --inst_dismatching                      true
% 7.62/1.48  --inst_eager_unprocessed_to_passive     true
% 7.62/1.48  --inst_prop_sim_given                   true
% 7.62/1.48  --inst_prop_sim_new                     false
% 7.62/1.48  --inst_subs_new                         false
% 7.62/1.48  --inst_eq_res_simp                      false
% 7.62/1.48  --inst_subs_given                       false
% 7.62/1.48  --inst_orphan_elimination               true
% 7.62/1.48  --inst_learning_loop_flag               true
% 7.62/1.48  --inst_learning_start                   3000
% 7.62/1.48  --inst_learning_factor                  2
% 7.62/1.48  --inst_start_prop_sim_after_learn       3
% 7.62/1.48  --inst_sel_renew                        solver
% 7.62/1.48  --inst_lit_activity_flag                true
% 7.62/1.48  --inst_restr_to_given                   false
% 7.62/1.48  --inst_activity_threshold               500
% 7.62/1.48  --inst_out_proof                        true
% 7.62/1.48  
% 7.62/1.48  ------ Resolution Options
% 7.62/1.48  
% 7.62/1.48  --resolution_flag                       false
% 7.62/1.48  --res_lit_sel                           adaptive
% 7.62/1.48  --res_lit_sel_side                      none
% 7.62/1.48  --res_ordering                          kbo
% 7.62/1.48  --res_to_prop_solver                    active
% 7.62/1.48  --res_prop_simpl_new                    false
% 7.62/1.48  --res_prop_simpl_given                  true
% 7.62/1.48  --res_passive_queue_type                priority_queues
% 7.62/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.62/1.48  --res_passive_queues_freq               [15;5]
% 7.62/1.48  --res_forward_subs                      full
% 7.62/1.48  --res_backward_subs                     full
% 7.62/1.48  --res_forward_subs_resolution           true
% 7.62/1.48  --res_backward_subs_resolution          true
% 7.62/1.48  --res_orphan_elimination                true
% 7.62/1.48  --res_time_limit                        2.
% 7.62/1.48  --res_out_proof                         true
% 7.62/1.48  
% 7.62/1.48  ------ Superposition Options
% 7.62/1.48  
% 7.62/1.48  --superposition_flag                    true
% 7.62/1.48  --sup_passive_queue_type                priority_queues
% 7.62/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.62/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.62/1.48  --demod_completeness_check              fast
% 7.62/1.48  --demod_use_ground                      true
% 7.62/1.48  --sup_to_prop_solver                    passive
% 7.62/1.48  --sup_prop_simpl_new                    true
% 7.62/1.48  --sup_prop_simpl_given                  true
% 7.62/1.48  --sup_fun_splitting                     true
% 7.62/1.48  --sup_smt_interval                      50000
% 7.62/1.48  
% 7.62/1.48  ------ Superposition Simplification Setup
% 7.62/1.48  
% 7.62/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.62/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.62/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.62/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.62/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.62/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.62/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.62/1.48  --sup_immed_triv                        [TrivRules]
% 7.62/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.62/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.62/1.48  --sup_immed_bw_main                     []
% 7.62/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.62/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.62/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.62/1.48  --sup_input_bw                          []
% 7.62/1.48  
% 7.62/1.48  ------ Combination Options
% 7.62/1.48  
% 7.62/1.48  --comb_res_mult                         3
% 7.62/1.48  --comb_sup_mult                         2
% 7.62/1.48  --comb_inst_mult                        10
% 7.62/1.48  
% 7.62/1.48  ------ Debug Options
% 7.62/1.48  
% 7.62/1.48  --dbg_backtrace                         false
% 7.62/1.48  --dbg_dump_prop_clauses                 false
% 7.62/1.48  --dbg_dump_prop_clauses_file            -
% 7.62/1.48  --dbg_out_stat                          false
% 7.62/1.48  
% 7.62/1.48  
% 7.62/1.48  
% 7.62/1.48  
% 7.62/1.48  ------ Proving...
% 7.62/1.48  
% 7.62/1.48  
% 7.62/1.48  % SZS status Theorem for theBenchmark.p
% 7.62/1.48  
% 7.62/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.62/1.48  
% 7.62/1.48  fof(f6,axiom,(
% 7.62/1.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f33,plain,(
% 7.62/1.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 7.62/1.48    inference(ennf_transformation,[],[f6])).
% 7.62/1.48  
% 7.62/1.48  fof(f46,plain,(
% 7.62/1.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 7.62/1.48    introduced(choice_axiom,[])).
% 7.62/1.48  
% 7.62/1.48  fof(f47,plain,(
% 7.62/1.48    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 7.62/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f46])).
% 7.62/1.48  
% 7.62/1.48  fof(f68,plain,(
% 7.62/1.48    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 7.62/1.48    inference(cnf_transformation,[],[f47])).
% 7.62/1.48  
% 7.62/1.48  fof(f25,conjecture,(
% 7.62/1.48    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f26,negated_conjecture,(
% 7.62/1.48    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 7.62/1.48    inference(negated_conjecture,[],[f25])).
% 7.62/1.48  
% 7.62/1.48  fof(f36,plain,(
% 7.62/1.48    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 7.62/1.48    inference(ennf_transformation,[],[f26])).
% 7.62/1.48  
% 7.62/1.48  fof(f54,plain,(
% 7.62/1.48    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK6 | k1_tarski(sK4) != sK5) & (k1_tarski(sK4) != sK6 | k1_xboole_0 != sK5) & (k1_tarski(sK4) != sK6 | k1_tarski(sK4) != sK5) & k2_xboole_0(sK5,sK6) = k1_tarski(sK4))),
% 7.62/1.48    introduced(choice_axiom,[])).
% 7.62/1.48  
% 7.62/1.48  fof(f55,plain,(
% 7.62/1.48    (k1_xboole_0 != sK6 | k1_tarski(sK4) != sK5) & (k1_tarski(sK4) != sK6 | k1_xboole_0 != sK5) & (k1_tarski(sK4) != sK6 | k1_tarski(sK4) != sK5) & k2_xboole_0(sK5,sK6) = k1_tarski(sK4)),
% 7.62/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f36,f54])).
% 7.62/1.48  
% 7.62/1.48  fof(f92,plain,(
% 7.62/1.48    k2_xboole_0(sK5,sK6) = k1_tarski(sK4)),
% 7.62/1.48    inference(cnf_transformation,[],[f55])).
% 7.62/1.48  
% 7.62/1.48  fof(f23,axiom,(
% 7.62/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f88,plain,(
% 7.62/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.62/1.48    inference(cnf_transformation,[],[f23])).
% 7.62/1.48  
% 7.62/1.48  fof(f101,plain,(
% 7.62/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.62/1.48    inference(definition_unfolding,[],[f88,f100])).
% 7.62/1.48  
% 7.62/1.48  fof(f16,axiom,(
% 7.62/1.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f81,plain,(
% 7.62/1.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.62/1.48    inference(cnf_transformation,[],[f16])).
% 7.62/1.48  
% 7.62/1.48  fof(f17,axiom,(
% 7.62/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f82,plain,(
% 7.62/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.62/1.48    inference(cnf_transformation,[],[f17])).
% 7.62/1.48  
% 7.62/1.48  fof(f18,axiom,(
% 7.62/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f83,plain,(
% 7.62/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.62/1.48    inference(cnf_transformation,[],[f18])).
% 7.62/1.48  
% 7.62/1.48  fof(f19,axiom,(
% 7.62/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f84,plain,(
% 7.62/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.62/1.48    inference(cnf_transformation,[],[f19])).
% 7.62/1.48  
% 7.62/1.48  fof(f20,axiom,(
% 7.62/1.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f85,plain,(
% 7.62/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.62/1.48    inference(cnf_transformation,[],[f20])).
% 7.62/1.48  
% 7.62/1.48  fof(f21,axiom,(
% 7.62/1.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f86,plain,(
% 7.62/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.62/1.48    inference(cnf_transformation,[],[f21])).
% 7.62/1.48  
% 7.62/1.48  fof(f22,axiom,(
% 7.62/1.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f87,plain,(
% 7.62/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.62/1.48    inference(cnf_transformation,[],[f22])).
% 7.62/1.48  
% 7.62/1.48  fof(f96,plain,(
% 7.62/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.62/1.48    inference(definition_unfolding,[],[f86,f87])).
% 7.62/1.48  
% 7.62/1.48  fof(f97,plain,(
% 7.62/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.62/1.48    inference(definition_unfolding,[],[f85,f96])).
% 7.62/1.48  
% 7.62/1.48  fof(f98,plain,(
% 7.62/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.62/1.48    inference(definition_unfolding,[],[f84,f97])).
% 7.62/1.48  
% 7.62/1.48  fof(f99,plain,(
% 7.62/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.62/1.48    inference(definition_unfolding,[],[f83,f98])).
% 7.62/1.48  
% 7.62/1.48  fof(f100,plain,(
% 7.62/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.62/1.48    inference(definition_unfolding,[],[f82,f99])).
% 7.62/1.48  
% 7.62/1.48  fof(f104,plain,(
% 7.62/1.48    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.62/1.48    inference(definition_unfolding,[],[f81,f100])).
% 7.62/1.48  
% 7.62/1.48  fof(f127,plain,(
% 7.62/1.48    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))),
% 7.62/1.48    inference(definition_unfolding,[],[f92,f101,f104])).
% 7.62/1.48  
% 7.62/1.48  fof(f2,axiom,(
% 7.62/1.48    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f41,plain,(
% 7.62/1.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.62/1.48    inference(nnf_transformation,[],[f2])).
% 7.62/1.48  
% 7.62/1.48  fof(f42,plain,(
% 7.62/1.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.62/1.48    inference(flattening,[],[f41])).
% 7.62/1.48  
% 7.62/1.48  fof(f43,plain,(
% 7.62/1.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.62/1.48    inference(rectify,[],[f42])).
% 7.62/1.48  
% 7.62/1.48  fof(f44,plain,(
% 7.62/1.48    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.62/1.48    introduced(choice_axiom,[])).
% 7.62/1.48  
% 7.62/1.48  fof(f45,plain,(
% 7.62/1.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.62/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).
% 7.62/1.48  
% 7.62/1.48  fof(f61,plain,(
% 7.62/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 7.62/1.48    inference(cnf_transformation,[],[f45])).
% 7.62/1.48  
% 7.62/1.48  fof(f108,plain,(
% 7.62/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 7.62/1.48    inference(definition_unfolding,[],[f61,f101])).
% 7.62/1.48  
% 7.62/1.48  fof(f128,plain,(
% 7.62/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 7.62/1.48    inference(equality_resolution,[],[f108])).
% 7.62/1.48  
% 7.62/1.48  fof(f15,axiom,(
% 7.62/1.48    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f48,plain,(
% 7.62/1.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.62/1.48    inference(nnf_transformation,[],[f15])).
% 7.62/1.48  
% 7.62/1.48  fof(f49,plain,(
% 7.62/1.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.62/1.48    inference(rectify,[],[f48])).
% 7.62/1.48  
% 7.62/1.48  fof(f50,plain,(
% 7.62/1.48    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 7.62/1.48    introduced(choice_axiom,[])).
% 7.62/1.48  
% 7.62/1.48  fof(f51,plain,(
% 7.62/1.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.62/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).
% 7.62/1.48  
% 7.62/1.48  fof(f77,plain,(
% 7.62/1.48    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.62/1.48    inference(cnf_transformation,[],[f51])).
% 7.62/1.48  
% 7.62/1.48  fof(f120,plain,(
% 7.62/1.48    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 7.62/1.48    inference(definition_unfolding,[],[f77,f104])).
% 7.62/1.48  
% 7.62/1.48  fof(f133,plain,(
% 7.62/1.48    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 7.62/1.48    inference(equality_resolution,[],[f120])).
% 7.62/1.48  
% 7.62/1.48  fof(f94,plain,(
% 7.62/1.48    k1_tarski(sK4) != sK6 | k1_xboole_0 != sK5),
% 7.62/1.48    inference(cnf_transformation,[],[f55])).
% 7.62/1.48  
% 7.62/1.48  fof(f125,plain,(
% 7.62/1.48    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 | k1_xboole_0 != sK5),
% 7.62/1.48    inference(definition_unfolding,[],[f94,f104])).
% 7.62/1.48  
% 7.62/1.48  fof(f95,plain,(
% 7.62/1.48    k1_xboole_0 != sK6 | k1_tarski(sK4) != sK5),
% 7.62/1.48    inference(cnf_transformation,[],[f55])).
% 7.62/1.48  
% 7.62/1.48  fof(f124,plain,(
% 7.62/1.48    k1_xboole_0 != sK6 | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5),
% 7.62/1.48    inference(definition_unfolding,[],[f95,f104])).
% 7.62/1.48  
% 7.62/1.48  fof(f78,plain,(
% 7.62/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.62/1.48    inference(cnf_transformation,[],[f51])).
% 7.62/1.48  
% 7.62/1.48  fof(f119,plain,(
% 7.62/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 7.62/1.48    inference(definition_unfolding,[],[f78,f104])).
% 7.62/1.48  
% 7.62/1.48  fof(f131,plain,(
% 7.62/1.48    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 7.62/1.48    inference(equality_resolution,[],[f119])).
% 7.62/1.48  
% 7.62/1.48  fof(f132,plain,(
% 7.62/1.48    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 7.62/1.48    inference(equality_resolution,[],[f131])).
% 7.62/1.48  
% 7.62/1.48  fof(f80,plain,(
% 7.62/1.48    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) )),
% 7.62/1.48    inference(cnf_transformation,[],[f51])).
% 7.62/1.48  
% 7.62/1.48  fof(f117,plain,(
% 7.62/1.48    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 | sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) )),
% 7.62/1.48    inference(definition_unfolding,[],[f80,f104])).
% 7.62/1.48  
% 7.62/1.48  fof(f3,axiom,(
% 7.62/1.48    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f29,plain,(
% 7.62/1.48    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 7.62/1.48    inference(unused_predicate_definition_removal,[],[f3])).
% 7.62/1.48  
% 7.62/1.48  fof(f31,plain,(
% 7.62/1.48    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 7.62/1.48    inference(ennf_transformation,[],[f29])).
% 7.62/1.48  
% 7.62/1.48  fof(f32,plain,(
% 7.62/1.48    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 7.62/1.48    inference(flattening,[],[f31])).
% 7.62/1.48  
% 7.62/1.48  fof(f65,plain,(
% 7.62/1.48    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 7.62/1.48    inference(cnf_transformation,[],[f32])).
% 7.62/1.48  
% 7.62/1.48  fof(f24,axiom,(
% 7.62/1.48    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f52,plain,(
% 7.62/1.48    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.62/1.48    inference(nnf_transformation,[],[f24])).
% 7.62/1.48  
% 7.62/1.48  fof(f53,plain,(
% 7.62/1.48    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.62/1.48    inference(flattening,[],[f52])).
% 7.62/1.48  
% 7.62/1.48  fof(f91,plain,(
% 7.62/1.48    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 7.62/1.48    inference(cnf_transformation,[],[f53])).
% 7.62/1.48  
% 7.62/1.48  fof(f121,plain,(
% 7.62/1.48    ( ! [X2,X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 7.62/1.48    inference(definition_unfolding,[],[f91,f100])).
% 7.62/1.48  
% 7.62/1.48  fof(f10,axiom,(
% 7.62/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f72,plain,(
% 7.62/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 7.62/1.48    inference(cnf_transformation,[],[f10])).
% 7.62/1.48  
% 7.62/1.48  fof(f115,plain,(
% 7.62/1.48    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 7.62/1.48    inference(definition_unfolding,[],[f72,f101,f101,f101])).
% 7.62/1.48  
% 7.62/1.48  fof(f8,axiom,(
% 7.62/1.48    ! [X0,X1] : ~(k1_xboole_0 = k4_xboole_0(X1,X0) & r2_xboole_0(X0,X1))),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f34,plain,(
% 7.62/1.48    ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 7.62/1.48    inference(ennf_transformation,[],[f8])).
% 7.62/1.48  
% 7.62/1.48  fof(f70,plain,(
% 7.62/1.48    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1)) )),
% 7.62/1.48    inference(cnf_transformation,[],[f34])).
% 7.62/1.48  
% 7.62/1.48  fof(f7,axiom,(
% 7.62/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f69,plain,(
% 7.62/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.62/1.48    inference(cnf_transformation,[],[f7])).
% 7.62/1.48  
% 7.62/1.48  fof(f14,axiom,(
% 7.62/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f76,plain,(
% 7.62/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 7.62/1.48    inference(cnf_transformation,[],[f14])).
% 7.62/1.48  
% 7.62/1.48  fof(f102,plain,(
% 7.62/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.62/1.48    inference(definition_unfolding,[],[f76,f101])).
% 7.62/1.48  
% 7.62/1.48  fof(f103,plain,(
% 7.62/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 7.62/1.48    inference(definition_unfolding,[],[f69,f102])).
% 7.62/1.48  
% 7.62/1.48  fof(f113,plain,(
% 7.62/1.48    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) | ~r2_xboole_0(X0,X1)) )),
% 7.62/1.48    inference(definition_unfolding,[],[f70,f103])).
% 7.62/1.48  
% 7.62/1.48  fof(f13,axiom,(
% 7.62/1.48    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f75,plain,(
% 7.62/1.48    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 7.62/1.48    inference(cnf_transformation,[],[f13])).
% 7.62/1.48  
% 7.62/1.48  fof(f12,axiom,(
% 7.62/1.48    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f74,plain,(
% 7.62/1.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.62/1.48    inference(cnf_transformation,[],[f12])).
% 7.62/1.48  
% 7.62/1.48  fof(f5,axiom,(
% 7.62/1.48    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f28,plain,(
% 7.62/1.48    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.62/1.48    inference(rectify,[],[f5])).
% 7.62/1.48  
% 7.62/1.48  fof(f67,plain,(
% 7.62/1.48    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.62/1.48    inference(cnf_transformation,[],[f28])).
% 7.62/1.48  
% 7.62/1.48  fof(f112,plain,(
% 7.62/1.48    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 7.62/1.48    inference(definition_unfolding,[],[f67,f102])).
% 7.62/1.48  
% 7.62/1.48  fof(f4,axiom,(
% 7.62/1.48    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 7.62/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.62/1.48  
% 7.62/1.48  fof(f27,plain,(
% 7.62/1.48    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 7.62/1.48    inference(rectify,[],[f4])).
% 7.62/1.48  
% 7.62/1.48  fof(f66,plain,(
% 7.62/1.48    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 7.62/1.48    inference(cnf_transformation,[],[f27])).
% 7.62/1.48  
% 7.62/1.48  fof(f111,plain,(
% 7.62/1.48    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 7.62/1.48    inference(definition_unfolding,[],[f66,f101])).
% 7.62/1.48  
% 7.62/1.48  fof(f59,plain,(
% 7.62/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 7.62/1.48    inference(cnf_transformation,[],[f45])).
% 7.62/1.48  
% 7.62/1.48  fof(f110,plain,(
% 7.62/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 7.62/1.48    inference(definition_unfolding,[],[f59,f101])).
% 7.62/1.48  
% 7.62/1.48  fof(f130,plain,(
% 7.62/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.62/1.48    inference(equality_resolution,[],[f110])).
% 7.62/1.48  
% 7.62/1.48  fof(f79,plain,(
% 7.62/1.48    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)) )),
% 7.62/1.48    inference(cnf_transformation,[],[f51])).
% 7.62/1.48  
% 7.62/1.48  fof(f118,plain,(
% 7.62/1.48    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 | sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)) )),
% 7.62/1.48    inference(definition_unfolding,[],[f79,f104])).
% 7.62/1.48  
% 7.62/1.48  fof(f60,plain,(
% 7.62/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 7.62/1.48    inference(cnf_transformation,[],[f45])).
% 7.62/1.48  
% 7.62/1.48  fof(f109,plain,(
% 7.62/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 7.62/1.48    inference(definition_unfolding,[],[f60,f101])).
% 7.62/1.48  
% 7.62/1.48  fof(f129,plain,(
% 7.62/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 7.62/1.48    inference(equality_resolution,[],[f109])).
% 7.62/1.48  
% 7.62/1.48  fof(f93,plain,(
% 7.62/1.48    k1_tarski(sK4) != sK6 | k1_tarski(sK4) != sK5),
% 7.62/1.48    inference(cnf_transformation,[],[f55])).
% 7.62/1.48  
% 7.62/1.48  fof(f126,plain,(
% 7.62/1.48    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5),
% 7.62/1.48    inference(definition_unfolding,[],[f93,f104,f104])).
% 7.62/1.48  
% 7.62/1.48  cnf(c_12,plain,
% 7.62/1.48      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 7.62/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_865,plain,
% 7.62/1.48      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 7.62/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_29,negated_conjecture,
% 7.62/1.48      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
% 7.62/1.48      inference(cnf_transformation,[],[f127]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_6,plain,
% 7.62/1.48      ( ~ r2_hidden(X0,X1)
% 7.62/1.48      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 7.62/1.48      inference(cnf_transformation,[],[f128]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_869,plain,
% 7.62/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.62/1.48      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 7.62/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_20907,plain,
% 7.62/1.48      ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 7.62/1.48      | r2_hidden(X0,sK6) != iProver_top ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_29,c_869]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_22,plain,
% 7.62/1.48      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 7.62/1.48      inference(cnf_transformation,[],[f133]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_858,plain,
% 7.62/1.48      ( X0 = X1
% 7.62/1.48      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 7.62/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_21019,plain,
% 7.62/1.48      ( sK4 = X0 | r2_hidden(X0,sK6) != iProver_top ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_20907,c_858]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_21239,plain,
% 7.62/1.48      ( sK2(sK6) = sK4 | sK6 = k1_xboole_0 ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_865,c_21019]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_27,negated_conjecture,
% 7.62/1.48      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
% 7.62/1.48      | k1_xboole_0 != sK5 ),
% 7.62/1.48      inference(cnf_transformation,[],[f125]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_26,negated_conjecture,
% 7.62/1.48      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5
% 7.62/1.48      | k1_xboole_0 != sK6 ),
% 7.62/1.48      inference(cnf_transformation,[],[f124]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_38,plain,
% 7.62/1.48      ( ~ r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 7.62/1.48      | sK4 = sK4 ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_22]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_21,plain,
% 7.62/1.48      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 7.62/1.48      inference(cnf_transformation,[],[f132]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_41,plain,
% 7.62/1.48      ( r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_21]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_40,plain,
% 7.62/1.48      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
% 7.62/1.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_42,plain,
% 7.62/1.48      ( r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_40]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_528,plain,
% 7.62/1.48      ( X0 != X1
% 7.62/1.48      | X2 != X3
% 7.62/1.48      | X4 != X5
% 7.62/1.48      | X6 != X7
% 7.62/1.48      | X8 != X9
% 7.62/1.48      | X10 != X11
% 7.62/1.48      | X12 != X13
% 7.62/1.48      | X14 != X15
% 7.62/1.48      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 7.62/1.48      theory(equality) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_533,plain,
% 7.62/1.48      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 7.62/1.48      | sK4 != sK4 ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_528]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_19,plain,
% 7.62/1.48      ( ~ r2_hidden(sK3(X0,X1),X1)
% 7.62/1.48      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 7.62/1.48      | sK3(X0,X1) != X0 ),
% 7.62/1.48      inference(cnf_transformation,[],[f117]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_952,plain,
% 7.62/1.48      ( ~ r2_hidden(sK3(sK4,sK6),sK6)
% 7.62/1.48      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6
% 7.62/1.48      | sK3(sK4,sK6) != sK4 ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_19]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_956,plain,
% 7.62/1.48      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6
% 7.62/1.48      | sK3(sK4,sK6) != sK4
% 7.62/1.48      | r2_hidden(sK3(sK4,sK6),sK6) != iProver_top ),
% 7.62/1.48      inference(predicate_to_equality,[status(thm)],[c_952]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_9,plain,
% 7.62/1.48      ( r2_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | X1 = X0 ),
% 7.62/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1071,plain,
% 7.62/1.48      ( r2_xboole_0(X0,sK5) | ~ r1_tarski(X0,sK5) | sK5 = X0 ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_9]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1384,plain,
% 7.62/1.48      ( r2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),sK5)
% 7.62/1.48      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),sK5)
% 7.62/1.48      | sK5 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_1071]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1385,plain,
% 7.62/1.48      ( sK5 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)
% 7.62/1.48      | r2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),sK5) = iProver_top
% 7.62/1.48      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),sK5) != iProver_top ),
% 7.62/1.48      inference(predicate_to_equality,[status(thm)],[c_1384]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1387,plain,
% 7.62/1.48      ( sK5 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 7.62/1.48      | r2_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = iProver_top
% 7.62/1.48      | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_1385]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_527,plain,
% 7.62/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.62/1.48      theory(equality) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1264,plain,
% 7.62/1.48      ( ~ r2_hidden(X0,X1)
% 7.62/1.48      | r2_hidden(sK3(sK4,sK6),sK6)
% 7.62/1.48      | sK3(sK4,sK6) != X0
% 7.62/1.48      | sK6 != X1 ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_527]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1776,plain,
% 7.62/1.48      ( ~ r2_hidden(X0,sK6)
% 7.62/1.48      | r2_hidden(sK3(sK4,sK6),sK6)
% 7.62/1.48      | sK3(sK4,sK6) != X0
% 7.62/1.48      | sK6 != sK6 ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_1264]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1777,plain,
% 7.62/1.48      ( sK3(sK4,sK6) != X0
% 7.62/1.48      | sK6 != sK6
% 7.62/1.48      | r2_hidden(X0,sK6) != iProver_top
% 7.62/1.48      | r2_hidden(sK3(sK4,sK6),sK6) = iProver_top ),
% 7.62/1.48      inference(predicate_to_equality,[status(thm)],[c_1776]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1779,plain,
% 7.62/1.48      ( sK3(sK4,sK6) != sK4
% 7.62/1.48      | sK6 != sK6
% 7.62/1.48      | r2_hidden(sK3(sK4,sK6),sK6) = iProver_top
% 7.62/1.48      | r2_hidden(sK4,sK6) != iProver_top ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_1777]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1269,plain,
% 7.62/1.48      ( ~ r2_hidden(sK6,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 7.62/1.48      | sK6 = X0 ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_22]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1934,plain,
% 7.62/1.48      ( ~ r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 7.62/1.48      | sK6 = sK6 ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_1269]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_23,plain,
% 7.62/1.48      ( ~ r2_hidden(X0,X1)
% 7.62/1.48      | ~ r2_hidden(X2,X1)
% 7.62/1.48      | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
% 7.62/1.48      inference(cnf_transformation,[],[f121]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_2576,plain,
% 7.62/1.48      ( ~ r2_hidden(X0,sK5)
% 7.62/1.48      | ~ r2_hidden(X1,sK5)
% 7.62/1.48      | r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),sK5) ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_23]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_2577,plain,
% 7.62/1.48      ( r2_hidden(X0,sK5) != iProver_top
% 7.62/1.48      | r2_hidden(X1,sK5) != iProver_top
% 7.62/1.48      | r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0),sK5) = iProver_top ),
% 7.62/1.48      inference(predicate_to_equality,[status(thm)],[c_2576]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_2579,plain,
% 7.62/1.48      ( r2_hidden(sK4,sK5) != iProver_top
% 7.62/1.48      | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = iProver_top ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_2577]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_3729,plain,
% 7.62/1.48      ( r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_21]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_525,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_908,plain,
% 7.62/1.48      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_525]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_3981,plain,
% 7.62/1.48      ( sK6 != k1_xboole_0
% 7.62/1.48      | k1_xboole_0 = sK6
% 7.62/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_908]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_919,plain,
% 7.62/1.48      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_525]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_10386,plain,
% 7.62/1.48      ( sK5 != k1_xboole_0
% 7.62/1.48      | k1_xboole_0 = sK5
% 7.62/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_919]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_939,plain,
% 7.62/1.48      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
% 7.62/1.48      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK5
% 7.62/1.48      | sK5 != X0 ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_525]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_10394,plain,
% 7.62/1.48      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 7.62/1.48      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK5
% 7.62/1.48      | sK5 != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_939]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_15,plain,
% 7.62/1.48      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
% 7.62/1.48      inference(cnf_transformation,[],[f115]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1430,plain,
% 7.62/1.48      ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_29,c_15]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1431,plain,
% 7.62/1.48      ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 7.62/1.48      inference(light_normalisation,[status(thm)],[c_1430,c_29]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_13,plain,
% 7.62/1.48      ( ~ r2_xboole_0(X0,X1)
% 7.62/1.48      | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) != k1_xboole_0 ),
% 7.62/1.48      inference(cnf_transformation,[],[f113]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_864,plain,
% 7.62/1.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) != k1_xboole_0
% 7.62/1.48      | r2_xboole_0(X1,X0) != iProver_top ),
% 7.62/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_18,plain,
% 7.62/1.48      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.62/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_17,plain,
% 7.62/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.62/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1214,plain,
% 7.62/1.48      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_18,c_17]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_11,plain,
% 7.62/1.48      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
% 7.62/1.48      inference(cnf_transformation,[],[f112]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_10,plain,
% 7.62/1.48      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 7.62/1.48      inference(cnf_transformation,[],[f111]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_876,plain,
% 7.62/1.48      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.62/1.48      inference(light_normalisation,[status(thm)],[c_11,c_10,c_18]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1217,plain,
% 7.62/1.48      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 7.62/1.48      inference(demodulation,[status(thm)],[c_1214,c_876]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1226,plain,
% 7.62/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = X2 ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_1217,c_17]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1228,plain,
% 7.62/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = X2 ),
% 7.62/1.48      inference(light_normalisation,[status(thm)],[c_1226,c_17]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_2044,plain,
% 7.62/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_1228,c_1217]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1216,plain,
% 7.62/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_17,c_18]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1582,plain,
% 7.62/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_1216,c_1217]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1222,plain,
% 7.62/1.48      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_18,c_1217]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1590,plain,
% 7.62/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.62/1.48      inference(demodulation,[status(thm)],[c_1582,c_1222]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1736,plain,
% 7.62/1.48      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_1590,c_1217]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1742,plain,
% 7.62/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_17,c_1736]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1741,plain,
% 7.62/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_17,c_1736]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_2458,plain,
% 7.62/1.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_1222,c_1741]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_3265,plain,
% 7.62/1.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X2,X0),X1) ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_1742,c_2458]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_1740,plain,
% 7.62/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_17,c_1736]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_2680,plain,
% 7.62/1.48      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_2458,c_1740]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_3287,plain,
% 7.62/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 7.62/1.48      inference(light_normalisation,[status(thm)],[c_3265,c_2680]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_15876,plain,
% 7.62/1.48      ( k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) != k1_xboole_0
% 7.62/1.48      | r2_xboole_0(X0,X1) != iProver_top ),
% 7.62/1.48      inference(demodulation,[status(thm)],[c_864,c_2044,c_3287]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_15886,plain,
% 7.62/1.48      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != k1_xboole_0
% 7.62/1.48      | r2_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_1431,c_15876]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_15887,plain,
% 7.62/1.48      ( k1_xboole_0 != k1_xboole_0
% 7.62/1.48      | r2_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top ),
% 7.62/1.48      inference(demodulation,[status(thm)],[c_15886,c_18]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_15888,plain,
% 7.62/1.48      ( r2_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top ),
% 7.62/1.48      inference(equality_resolution_simp,[status(thm)],[c_15887]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_8,plain,
% 7.62/1.48      ( r2_hidden(X0,X1)
% 7.62/1.48      | r2_hidden(X0,X2)
% 7.62/1.48      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 7.62/1.48      inference(cnf_transformation,[],[f130]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_867,plain,
% 7.62/1.48      ( r2_hidden(X0,X1) = iProver_top
% 7.62/1.48      | r2_hidden(X0,X2) = iProver_top
% 7.62/1.48      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
% 7.62/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_18999,plain,
% 7.62/1.48      ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
% 7.62/1.48      | r2_hidden(X0,sK5) = iProver_top
% 7.62/1.48      | r2_hidden(X0,sK6) = iProver_top ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_29,c_867]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_19011,plain,
% 7.62/1.48      ( r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
% 7.62/1.48      | r2_hidden(sK4,sK5) = iProver_top
% 7.62/1.48      | r2_hidden(sK4,sK6) = iProver_top ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_18999]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_524,plain,( X0 = X0 ),theory(equality) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_20857,plain,
% 7.62/1.48      ( k1_xboole_0 = k1_xboole_0 ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_524]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_20,plain,
% 7.62/1.48      ( r2_hidden(sK3(X0,X1),X1)
% 7.62/1.48      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 7.62/1.48      | sK3(X0,X1) = X0 ),
% 7.62/1.48      inference(cnf_transformation,[],[f118]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_860,plain,
% 7.62/1.48      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 7.62/1.48      | sK3(X0,X1) = X0
% 7.62/1.48      | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
% 7.62/1.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_21240,plain,
% 7.62/1.48      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK6
% 7.62/1.48      | sK3(X0,sK6) = X0
% 7.62/1.48      | sK3(X0,sK6) = sK4 ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_860,c_21019]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_21253,plain,
% 7.62/1.48      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6
% 7.62/1.48      | sK3(sK4,sK6) = sK4 ),
% 7.62/1.48      inference(instantiation,[status(thm)],[c_21240]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_7,plain,
% 7.62/1.48      ( ~ r2_hidden(X0,X1)
% 7.62/1.48      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 7.62/1.48      inference(cnf_transformation,[],[f129]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_868,plain,
% 7.62/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.62/1.48      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
% 7.62/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_19206,plain,
% 7.62/1.48      ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 7.62/1.48      | r2_hidden(X0,sK5) != iProver_top ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_29,c_868]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_19347,plain,
% 7.62/1.48      ( sK4 = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_19206,c_858]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_19598,plain,
% 7.62/1.48      ( sK2(sK5) = sK4 | sK5 = k1_xboole_0 ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_865,c_19347]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_22204,plain,
% 7.62/1.48      ( sK5 = k1_xboole_0 | r2_hidden(sK4,sK5) = iProver_top ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_19598,c_865]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_22206,plain,
% 7.62/1.48      ( sK2(sK6) = sK4 ),
% 7.62/1.48      inference(global_propositional_subsumption,
% 7.62/1.48                [status(thm)],
% 7.62/1.48                [c_21239,c_27,c_26,c_38,c_41,c_42,c_533,c_956,c_1387,
% 7.62/1.48                 c_1779,c_1934,c_2579,c_3729,c_3981,c_10386,c_10394,
% 7.62/1.48                 c_15888,c_19011,c_20857,c_21253,c_22204]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_22208,plain,
% 7.62/1.48      ( sK6 = k1_xboole_0 | r2_hidden(sK4,sK6) = iProver_top ),
% 7.62/1.48      inference(superposition,[status(thm)],[c_22206,c_865]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(c_28,negated_conjecture,
% 7.62/1.48      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5
% 7.62/1.48      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 ),
% 7.62/1.48      inference(cnf_transformation,[],[f126]) ).
% 7.62/1.48  
% 7.62/1.48  cnf(contradiction,plain,
% 7.62/1.48      ( $false ),
% 7.62/1.48      inference(minisat,
% 7.62/1.48                [status(thm)],
% 7.62/1.48                [c_22208,c_22204,c_21253,c_20857,c_19011,c_15888,c_10394,
% 7.62/1.48                 c_10386,c_3981,c_3729,c_2579,c_1934,c_1779,c_1387,c_956,
% 7.62/1.48                 c_533,c_42,c_41,c_38,c_26,c_27,c_28]) ).
% 7.62/1.48  
% 7.62/1.48  
% 7.62/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.62/1.48  
% 7.62/1.48  ------                               Statistics
% 7.62/1.48  
% 7.62/1.48  ------ General
% 7.62/1.48  
% 7.62/1.48  abstr_ref_over_cycles:                  0
% 7.62/1.48  abstr_ref_under_cycles:                 0
% 7.62/1.48  gc_basic_clause_elim:                   0
% 7.62/1.48  forced_gc_time:                         0
% 7.62/1.48  parsing_time:                           0.011
% 7.62/1.48  unif_index_cands_time:                  0.
% 7.62/1.48  unif_index_add_time:                    0.
% 7.62/1.48  orderings_time:                         0.
% 7.62/1.48  out_proof_time:                         0.012
% 7.62/1.48  total_time:                             0.565
% 7.62/1.48  num_of_symbols:                         45
% 7.62/1.48  num_of_terms:                           27590
% 7.62/1.48  
% 7.62/1.48  ------ Preprocessing
% 7.62/1.48  
% 7.62/1.48  num_of_splits:                          0
% 7.62/1.48  num_of_split_atoms:                     0
% 7.62/1.48  num_of_reused_defs:                     0
% 7.62/1.48  num_eq_ax_congr_red:                    20
% 7.62/1.48  num_of_sem_filtered_clauses:            1
% 7.62/1.48  num_of_subtypes:                        0
% 7.62/1.48  monotx_restored_types:                  0
% 7.62/1.48  sat_num_of_epr_types:                   0
% 7.62/1.48  sat_num_of_non_cyclic_types:            0
% 7.62/1.48  sat_guarded_non_collapsed_types:        0
% 7.62/1.48  num_pure_diseq_elim:                    0
% 7.62/1.48  simp_replaced_by:                       0
% 7.62/1.48  res_preprocessed:                       105
% 7.62/1.48  prep_upred:                             0
% 7.62/1.48  prep_unflattend:                        29
% 7.62/1.48  smt_new_axioms:                         0
% 7.62/1.48  pred_elim_cands:                        3
% 7.62/1.48  pred_elim:                              0
% 7.62/1.48  pred_elim_cl:                           0
% 7.62/1.48  pred_elim_cycles:                       2
% 7.62/1.48  merged_defs:                            0
% 7.62/1.48  merged_defs_ncl:                        0
% 7.62/1.48  bin_hyper_res:                          0
% 7.62/1.48  prep_cycles:                            3
% 7.62/1.48  pred_elim_time:                         0.004
% 7.62/1.48  splitting_time:                         0.
% 7.62/1.48  sem_filter_time:                        0.
% 7.62/1.48  monotx_time:                            0.001
% 7.62/1.48  subtype_inf_time:                       0.
% 7.62/1.48  
% 7.62/1.48  ------ Problem properties
% 7.62/1.48  
% 7.62/1.48  clauses:                                30
% 7.62/1.48  conjectures:                            4
% 7.62/1.48  epr:                                    2
% 7.62/1.48  horn:                                   24
% 7.62/1.48  ground:                                 4
% 7.62/1.48  unary:                                  8
% 7.62/1.48  binary:                                 13
% 7.62/1.48  lits:                                   62
% 7.62/1.48  lits_eq:                                24
% 7.62/1.48  fd_pure:                                0
% 7.62/1.48  fd_pseudo:                              0
% 7.62/1.48  fd_cond:                                1
% 7.62/1.48  fd_pseudo_cond:                         6
% 7.62/1.48  ac_symbols:                             1
% 7.62/1.48  
% 7.62/1.48  ------ Propositional Solver
% 7.62/1.48  
% 7.62/1.48  prop_solver_calls:                      26
% 7.62/1.48  prop_fast_solver_calls:                 735
% 7.62/1.48  smt_solver_calls:                       0
% 7.62/1.48  smt_fast_solver_calls:                  0
% 7.62/1.48  prop_num_of_clauses:                    4748
% 7.62/1.48  prop_preprocess_simplified:             10804
% 7.62/1.48  prop_fo_subsumed:                       2
% 7.62/1.48  prop_solver_time:                       0.
% 7.62/1.48  smt_solver_time:                        0.
% 7.62/1.48  smt_fast_solver_time:                   0.
% 7.62/1.48  prop_fast_solver_time:                  0.
% 7.62/1.48  prop_unsat_core_time:                   0.
% 7.62/1.48  
% 7.62/1.48  ------ QBF
% 7.62/1.48  
% 7.62/1.48  qbf_q_res:                              0
% 7.62/1.48  qbf_num_tautologies:                    0
% 7.62/1.48  qbf_prep_cycles:                        0
% 7.62/1.48  
% 7.62/1.48  ------ BMC1
% 7.62/1.48  
% 7.62/1.48  bmc1_current_bound:                     -1
% 7.62/1.48  bmc1_last_solved_bound:                 -1
% 7.62/1.48  bmc1_unsat_core_size:                   -1
% 7.62/1.48  bmc1_unsat_core_parents_size:           -1
% 7.62/1.48  bmc1_merge_next_fun:                    0
% 7.62/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.62/1.48  
% 7.62/1.48  ------ Instantiation
% 7.62/1.48  
% 7.62/1.48  inst_num_of_clauses:                    1124
% 7.62/1.48  inst_num_in_passive:                    745
% 7.62/1.48  inst_num_in_active:                     290
% 7.62/1.48  inst_num_in_unprocessed:                99
% 7.62/1.48  inst_num_of_loops:                      580
% 7.62/1.48  inst_num_of_learning_restarts:          0
% 7.62/1.48  inst_num_moves_active_passive:          289
% 7.62/1.48  inst_lit_activity:                      0
% 7.62/1.48  inst_lit_activity_moves:                0
% 7.62/1.48  inst_num_tautologies:                   0
% 7.62/1.48  inst_num_prop_implied:                  0
% 7.62/1.48  inst_num_existing_simplified:           0
% 7.62/1.48  inst_num_eq_res_simplified:             0
% 7.62/1.48  inst_num_child_elim:                    0
% 7.62/1.48  inst_num_of_dismatching_blockings:      456
% 7.62/1.48  inst_num_of_non_proper_insts:           1346
% 7.62/1.48  inst_num_of_duplicates:                 0
% 7.62/1.48  inst_inst_num_from_inst_to_res:         0
% 7.62/1.48  inst_dismatching_checking_time:         0.
% 7.62/1.48  
% 7.62/1.48  ------ Resolution
% 7.62/1.48  
% 7.62/1.48  res_num_of_clauses:                     0
% 7.62/1.48  res_num_in_passive:                     0
% 7.62/1.48  res_num_in_active:                      0
% 7.62/1.48  res_num_of_loops:                       108
% 7.62/1.48  res_forward_subset_subsumed:            61
% 7.62/1.48  res_backward_subset_subsumed:           20
% 7.62/1.48  res_forward_subsumed:                   0
% 7.62/1.48  res_backward_subsumed:                  0
% 7.62/1.48  res_forward_subsumption_resolution:     0
% 7.62/1.48  res_backward_subsumption_resolution:    0
% 7.62/1.48  res_clause_to_clause_subsumption:       24928
% 7.62/1.48  res_orphan_elimination:                 0
% 7.62/1.48  res_tautology_del:                      74
% 7.62/1.48  res_num_eq_res_simplified:              0
% 7.62/1.48  res_num_sel_changes:                    0
% 7.62/1.48  res_moves_from_active_to_pass:          0
% 7.62/1.48  
% 7.62/1.48  ------ Superposition
% 7.62/1.48  
% 7.62/1.48  sup_time_total:                         0.
% 7.62/1.48  sup_time_generating:                    0.
% 7.62/1.48  sup_time_sim_full:                      0.
% 7.62/1.48  sup_time_sim_immed:                     0.
% 7.62/1.48  
% 7.62/1.48  sup_num_of_clauses:                     685
% 7.62/1.48  sup_num_in_active:                      111
% 7.62/1.48  sup_num_in_passive:                     574
% 7.62/1.48  sup_num_of_loops:                       114
% 7.62/1.48  sup_fw_superposition:                   5409
% 7.62/1.48  sup_bw_superposition:                   3774
% 7.62/1.48  sup_immediate_simplified:               3488
% 7.62/1.48  sup_given_eliminated:                   2
% 7.62/1.48  comparisons_done:                       0
% 7.62/1.48  comparisons_avoided:                    5
% 7.62/1.48  
% 7.62/1.48  ------ Simplifications
% 7.62/1.48  
% 7.62/1.48  
% 7.62/1.48  sim_fw_subset_subsumed:                 5
% 7.62/1.48  sim_bw_subset_subsumed:                 0
% 7.62/1.48  sim_fw_subsumed:                        155
% 7.62/1.48  sim_bw_subsumed:                        0
% 7.62/1.48  sim_fw_subsumption_res:                 0
% 7.62/1.48  sim_bw_subsumption_res:                 0
% 7.62/1.48  sim_tautology_del:                      25
% 7.62/1.48  sim_eq_tautology_del:                   805
% 7.62/1.48  sim_eq_res_simp:                        9
% 7.62/1.48  sim_fw_demodulated:                     2647
% 7.62/1.48  sim_bw_demodulated:                     13
% 7.62/1.48  sim_light_normalised:                   1061
% 7.62/1.48  sim_joinable_taut:                      206
% 7.62/1.48  sim_joinable_simp:                      0
% 7.62/1.48  sim_ac_normalised:                      0
% 7.62/1.48  sim_smt_subsumption:                    0
% 7.62/1.48  
%------------------------------------------------------------------------------
