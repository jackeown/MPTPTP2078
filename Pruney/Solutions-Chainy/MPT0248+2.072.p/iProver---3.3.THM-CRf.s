%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:18 EST 2020

% Result     : Theorem 51.73s
% Output     : CNFRefutation 51.73s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 756 expanded)
%              Number of clauses        :   96 ( 121 expanded)
%              Number of leaves         :   31 ( 217 expanded)
%              Depth                    :   16
%              Number of atoms          :  526 (1509 expanded)
%              Number of equality atoms :  251 (1018 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f28,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f29])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f37,f54])).

fof(f96,plain,(
    k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f105,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f88,f104])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f78,f79])).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f77,f100])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f76,f101])).

fof(f103,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f75,f102])).

fof(f104,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f74,f103])).

fof(f107,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f73,f104])).

fof(f124,plain,(
    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(definition_unfolding,[],[f96,f105,f107])).

fof(f5,axiom,(
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
    inference(nnf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f126,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f52])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f94,f104])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f45])).

fof(f49,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f46,f49,f48,f47])).

fof(f82,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f127,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f82])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f66,f105])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f92,f107])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f112,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f69,f105])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f62,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f106,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f72,f105])).

fof(f110,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f62,f106])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f87,f107])).

fof(f21,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f86,f107])).

fof(f99,plain,
    ( k1_xboole_0 != sK6
    | k1_tarski(sK4) != sK5 ),
    inference(cnf_transformation,[],[f55])).

fof(f121,plain,
    ( k1_xboole_0 != sK6
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5 ),
    inference(definition_unfolding,[],[f99,f107])).

fof(f98,plain,
    ( k1_tarski(sK4) != sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f55])).

fof(f122,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
    | k1_xboole_0 != sK5 ),
    inference(definition_unfolding,[],[f98,f107])).

fof(f97,plain,
    ( k1_tarski(sK4) != sK6
    | k1_tarski(sK4) != sK5 ),
    inference(cnf_transformation,[],[f55])).

fof(f123,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5 ),
    inference(definition_unfolding,[],[f97,f107,f107])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X2,X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_179326,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(sK6,X0)
    | ~ r1_tarski(sK6,X1)
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_180925,plain,
    ( ~ r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6)
    | ~ r1_tarski(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ r1_tarski(sK6,sK6)
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_179326])).

cnf(c_13613,plain,
    ( ~ r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)
    | ~ r1_tarski(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ r1_tarski(X0,sK5)
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_169314,plain,
    ( ~ r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)
    | ~ r1_tarski(k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ r1_tarski(k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))),sK5)
    | k1_xboole_0 = k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(instantiation,[status(thm)],[c_13613])).

cnf(c_169331,plain,
    ( k1_xboole_0 = k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top
    | r1_tarski(k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
    | r1_tarski(k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_169314])).

cnf(c_808,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1628,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK6)
    | X2 != X0
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_22041,plain,
    ( ~ r1_tarski(X0,sK6)
    | r1_tarski(X1,sK6)
    | X1 != X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1628])).

cnf(c_100024,plain,
    ( ~ r1_tarski(X0,sK6)
    | r1_tarski(sK5,sK6)
    | sK5 != X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_22041])).

cnf(c_156548,plain,
    ( r1_tarski(sK5,sK6)
    | ~ r1_tarski(k1_xboole_0,sK6)
    | sK5 != k1_xboole_0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_100024])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1400,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_34,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_1395,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_29,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1379,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2316,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1395,c_1379])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1387,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_20910,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2316,c_1387])).

cnf(c_143210,plain,
    ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_34,c_20910])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1401,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_143412,plain,
    ( r2_hidden(sK0(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK6) != iProver_top
    | r1_tarski(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_143210,c_1401])).

cnf(c_143905,plain,
    ( r1_tarski(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1400,c_143412])).

cnf(c_143906,plain,
    ( r1_tarski(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_143905])).

cnf(c_1766,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK5)
    | X2 != X0
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_22052,plain,
    ( ~ r1_tarski(X0,sK5)
    | r1_tarski(X1,sK5)
    | X1 != X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1766])).

cnf(c_100068,plain,
    ( r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,sK5)
    | X0 != sK5
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_22052])).

cnf(c_138410,plain,
    ( r1_tarski(k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))),sK5)
    | ~ r1_tarski(sK5,sK5)
    | k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != sK5
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_100068])).

cnf(c_138411,plain,
    ( k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != sK5
    | sK5 != sK5
    | r1_tarski(k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))),sK5) = iProver_top
    | r1_tarski(sK5,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_138410])).

cnf(c_806,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1488,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_5303,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1488])).

cnf(c_17523,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK6)) != sK6
    | sK6 = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK6))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_5303])).

cnf(c_135930,plain,
    ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) != sK6
    | sK6 = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_17523])).

cnf(c_3675,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | X2 != X0
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_22063,plain,
    ( r1_tarski(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ r1_tarski(X1,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)))
    | X0 != X1
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_3675])).

cnf(c_42142,plain,
    ( r1_tarski(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ r1_tarski(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)))
    | X0 != sK5
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_22063])).

cnf(c_113779,plain,
    ( r1_tarski(k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ r1_tarski(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)))
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
    | k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != sK5 ),
    inference(instantiation,[status(thm)],[c_42142])).

cnf(c_113780,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
    | k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != sK5
    | r1_tarski(k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r1_tarski(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_113779])).

cnf(c_1495,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_3697,plain,
    ( sK5 != X0
    | sK5 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_106940,plain,
    ( sK5 != k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | sK5 = k1_xboole_0
    | k1_xboole_0 != k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(instantiation,[status(thm)],[c_3697])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_67370,plain,
    ( ~ r1_tarski(sK5,sK6)
    | k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) = sK6 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1382,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_13,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1391,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11417,plain,
    ( r1_tarski(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_34,c_1391])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1396,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_51433,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK5
    | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_11417,c_1396])).

cnf(c_51446,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK5
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1382,c_51433])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_14,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_801,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_6,c_14,c_0])).

cnf(c_30816,plain,
    ( k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = sK5 ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_14792,plain,
    ( r1_xboole_0(k6_enumset1(sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1809,plain,
    ( r1_tarski(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,X0))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_14690,plain,
    ( r1_tarski(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_1809])).

cnf(c_14693,plain,
    ( r1_tarski(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14690])).

cnf(c_1444,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(sK5,X0)
    | ~ r1_tarski(sK5,X1)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_13616,plain,
    ( ~ r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)
    | ~ r1_tarski(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ r1_tarski(sK5,sK5)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_1444])).

cnf(c_13617,plain,
    ( k1_xboole_0 = sK5
    | r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top
    | r1_tarski(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
    | r1_tarski(sK5,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13616])).

cnf(c_23,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_10730,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK6)
    | r2_hidden(X0,sK6) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_10732,plain,
    ( r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6)
    | r2_hidden(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_10730])).

cnf(c_1788,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_5761,plain,
    ( k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != sK5
    | sK5 = k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1788])).

cnf(c_22,plain,
    ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_4899,plain,
    ( ~ r1_xboole_0(k6_enumset1(sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6)),k1_xboole_0)
    | ~ r2_hidden(sK0(k1_xboole_0,sK6),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1971,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_3289,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6
    | sK6 != k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1971])).

cnf(c_1968,plain,
    ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6)
    | ~ r1_tarski(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1918,plain,
    ( r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)
    | r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1919,plain,
    ( r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1918])).

cnf(c_1817,plain,
    ( ~ r2_hidden(X0,sK6)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK6) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1819,plain,
    ( ~ r2_hidden(sK4,sK6)
    | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) ),
    inference(instantiation,[status(thm)],[c_1817])).

cnf(c_1489,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1757,plain,
    ( ~ r1_tarski(sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1489])).

cnf(c_1723,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1724,plain,
    ( r1_tarski(sK5,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1723])).

cnf(c_1668,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1482,plain,
    ( ~ r1_tarski(X0,sK6)
    | ~ r1_tarski(sK6,X0)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1617,plain,
    ( ~ r1_tarski(sK6,sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1482])).

cnf(c_1579,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK6),k1_xboole_0)
    | r1_tarski(k1_xboole_0,sK6) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_31,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_32,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_33,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 ),
    inference(cnf_transformation,[],[f123])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_180925,c_169331,c_156548,c_143906,c_138411,c_135930,c_113780,c_106940,c_67370,c_51446,c_30816,c_14792,c_14693,c_13617,c_11417,c_10732,c_5761,c_4899,c_3289,c_1968,c_1919,c_1819,c_1757,c_1724,c_1723,c_1668,c_1617,c_1579,c_31,c_32,c_33,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:01:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 51.73/7.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.73/7.00  
% 51.73/7.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.73/7.00  
% 51.73/7.00  ------  iProver source info
% 51.73/7.00  
% 51.73/7.00  git: date: 2020-06-30 10:37:57 +0100
% 51.73/7.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.73/7.00  git: non_committed_changes: false
% 51.73/7.00  git: last_make_outside_of_git: false
% 51.73/7.00  
% 51.73/7.00  ------ 
% 51.73/7.00  
% 51.73/7.00  ------ Input Options
% 51.73/7.00  
% 51.73/7.00  --out_options                           all
% 51.73/7.00  --tptp_safe_out                         true
% 51.73/7.00  --problem_path                          ""
% 51.73/7.00  --include_path                          ""
% 51.73/7.00  --clausifier                            res/vclausify_rel
% 51.73/7.00  --clausifier_options                    ""
% 51.73/7.00  --stdin                                 false
% 51.73/7.00  --stats_out                             all
% 51.73/7.00  
% 51.73/7.00  ------ General Options
% 51.73/7.00  
% 51.73/7.00  --fof                                   false
% 51.73/7.00  --time_out_real                         305.
% 51.73/7.00  --time_out_virtual                      -1.
% 51.73/7.00  --symbol_type_check                     false
% 51.73/7.00  --clausify_out                          false
% 51.73/7.00  --sig_cnt_out                           false
% 51.73/7.00  --trig_cnt_out                          false
% 51.73/7.00  --trig_cnt_out_tolerance                1.
% 51.73/7.00  --trig_cnt_out_sk_spl                   false
% 51.73/7.00  --abstr_cl_out                          false
% 51.73/7.00  
% 51.73/7.00  ------ Global Options
% 51.73/7.00  
% 51.73/7.00  --schedule                              default
% 51.73/7.00  --add_important_lit                     false
% 51.73/7.00  --prop_solver_per_cl                    1000
% 51.73/7.00  --min_unsat_core                        false
% 51.73/7.00  --soft_assumptions                      false
% 51.73/7.00  --soft_lemma_size                       3
% 51.73/7.00  --prop_impl_unit_size                   0
% 51.73/7.00  --prop_impl_unit                        []
% 51.73/7.00  --share_sel_clauses                     true
% 51.73/7.00  --reset_solvers                         false
% 51.73/7.00  --bc_imp_inh                            [conj_cone]
% 51.73/7.00  --conj_cone_tolerance                   3.
% 51.73/7.00  --extra_neg_conj                        none
% 51.73/7.00  --large_theory_mode                     true
% 51.73/7.00  --prolific_symb_bound                   200
% 51.73/7.00  --lt_threshold                          2000
% 51.73/7.00  --clause_weak_htbl                      true
% 51.73/7.00  --gc_record_bc_elim                     false
% 51.73/7.00  
% 51.73/7.00  ------ Preprocessing Options
% 51.73/7.00  
% 51.73/7.00  --preprocessing_flag                    true
% 51.73/7.00  --time_out_prep_mult                    0.1
% 51.73/7.00  --splitting_mode                        input
% 51.73/7.00  --splitting_grd                         true
% 51.73/7.00  --splitting_cvd                         false
% 51.73/7.00  --splitting_cvd_svl                     false
% 51.73/7.00  --splitting_nvd                         32
% 51.73/7.00  --sub_typing                            true
% 51.73/7.00  --prep_gs_sim                           true
% 51.73/7.00  --prep_unflatten                        true
% 51.73/7.00  --prep_res_sim                          true
% 51.73/7.00  --prep_upred                            true
% 51.73/7.00  --prep_sem_filter                       exhaustive
% 51.73/7.00  --prep_sem_filter_out                   false
% 51.73/7.00  --pred_elim                             true
% 51.73/7.00  --res_sim_input                         true
% 51.73/7.00  --eq_ax_congr_red                       true
% 51.73/7.00  --pure_diseq_elim                       true
% 51.73/7.00  --brand_transform                       false
% 51.73/7.00  --non_eq_to_eq                          false
% 51.73/7.00  --prep_def_merge                        true
% 51.73/7.00  --prep_def_merge_prop_impl              false
% 51.73/7.00  --prep_def_merge_mbd                    true
% 51.73/7.00  --prep_def_merge_tr_red                 false
% 51.73/7.00  --prep_def_merge_tr_cl                  false
% 51.73/7.00  --smt_preprocessing                     true
% 51.73/7.00  --smt_ac_axioms                         fast
% 51.73/7.00  --preprocessed_out                      false
% 51.73/7.00  --preprocessed_stats                    false
% 51.73/7.00  
% 51.73/7.00  ------ Abstraction refinement Options
% 51.73/7.00  
% 51.73/7.00  --abstr_ref                             []
% 51.73/7.00  --abstr_ref_prep                        false
% 51.73/7.00  --abstr_ref_until_sat                   false
% 51.73/7.00  --abstr_ref_sig_restrict                funpre
% 51.73/7.00  --abstr_ref_af_restrict_to_split_sk     false
% 51.73/7.00  --abstr_ref_under                       []
% 51.73/7.00  
% 51.73/7.00  ------ SAT Options
% 51.73/7.00  
% 51.73/7.00  --sat_mode                              false
% 51.73/7.00  --sat_fm_restart_options                ""
% 51.73/7.00  --sat_gr_def                            false
% 51.73/7.00  --sat_epr_types                         true
% 51.73/7.00  --sat_non_cyclic_types                  false
% 51.73/7.00  --sat_finite_models                     false
% 51.73/7.00  --sat_fm_lemmas                         false
% 51.73/7.00  --sat_fm_prep                           false
% 51.73/7.00  --sat_fm_uc_incr                        true
% 51.73/7.00  --sat_out_model                         small
% 51.73/7.00  --sat_out_clauses                       false
% 51.73/7.00  
% 51.73/7.00  ------ QBF Options
% 51.73/7.00  
% 51.73/7.00  --qbf_mode                              false
% 51.73/7.00  --qbf_elim_univ                         false
% 51.73/7.00  --qbf_dom_inst                          none
% 51.73/7.00  --qbf_dom_pre_inst                      false
% 51.73/7.00  --qbf_sk_in                             false
% 51.73/7.00  --qbf_pred_elim                         true
% 51.73/7.00  --qbf_split                             512
% 51.73/7.00  
% 51.73/7.00  ------ BMC1 Options
% 51.73/7.00  
% 51.73/7.00  --bmc1_incremental                      false
% 51.73/7.00  --bmc1_axioms                           reachable_all
% 51.73/7.00  --bmc1_min_bound                        0
% 51.73/7.00  --bmc1_max_bound                        -1
% 51.73/7.00  --bmc1_max_bound_default                -1
% 51.73/7.00  --bmc1_symbol_reachability              true
% 51.73/7.00  --bmc1_property_lemmas                  false
% 51.73/7.00  --bmc1_k_induction                      false
% 51.73/7.00  --bmc1_non_equiv_states                 false
% 51.73/7.00  --bmc1_deadlock                         false
% 51.73/7.00  --bmc1_ucm                              false
% 51.73/7.00  --bmc1_add_unsat_core                   none
% 51.73/7.00  --bmc1_unsat_core_children              false
% 51.73/7.00  --bmc1_unsat_core_extrapolate_axioms    false
% 51.73/7.00  --bmc1_out_stat                         full
% 51.73/7.00  --bmc1_ground_init                      false
% 51.73/7.00  --bmc1_pre_inst_next_state              false
% 51.73/7.00  --bmc1_pre_inst_state                   false
% 51.73/7.00  --bmc1_pre_inst_reach_state             false
% 51.73/7.00  --bmc1_out_unsat_core                   false
% 51.73/7.00  --bmc1_aig_witness_out                  false
% 51.73/7.00  --bmc1_verbose                          false
% 51.73/7.00  --bmc1_dump_clauses_tptp                false
% 51.73/7.00  --bmc1_dump_unsat_core_tptp             false
% 51.73/7.00  --bmc1_dump_file                        -
% 51.73/7.00  --bmc1_ucm_expand_uc_limit              128
% 51.73/7.00  --bmc1_ucm_n_expand_iterations          6
% 51.73/7.00  --bmc1_ucm_extend_mode                  1
% 51.73/7.00  --bmc1_ucm_init_mode                    2
% 51.73/7.00  --bmc1_ucm_cone_mode                    none
% 51.73/7.00  --bmc1_ucm_reduced_relation_type        0
% 51.73/7.00  --bmc1_ucm_relax_model                  4
% 51.73/7.00  --bmc1_ucm_full_tr_after_sat            true
% 51.73/7.00  --bmc1_ucm_expand_neg_assumptions       false
% 51.73/7.00  --bmc1_ucm_layered_model                none
% 51.73/7.00  --bmc1_ucm_max_lemma_size               10
% 51.73/7.00  
% 51.73/7.00  ------ AIG Options
% 51.73/7.00  
% 51.73/7.00  --aig_mode                              false
% 51.73/7.00  
% 51.73/7.00  ------ Instantiation Options
% 51.73/7.00  
% 51.73/7.00  --instantiation_flag                    true
% 51.73/7.00  --inst_sos_flag                         true
% 51.73/7.00  --inst_sos_phase                        true
% 51.73/7.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.73/7.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.73/7.00  --inst_lit_sel_side                     num_symb
% 51.73/7.00  --inst_solver_per_active                1400
% 51.73/7.00  --inst_solver_calls_frac                1.
% 51.73/7.00  --inst_passive_queue_type               priority_queues
% 51.73/7.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.73/7.00  --inst_passive_queues_freq              [25;2]
% 51.73/7.00  --inst_dismatching                      true
% 51.73/7.00  --inst_eager_unprocessed_to_passive     true
% 51.73/7.00  --inst_prop_sim_given                   true
% 51.73/7.00  --inst_prop_sim_new                     false
% 51.73/7.00  --inst_subs_new                         false
% 51.73/7.00  --inst_eq_res_simp                      false
% 51.73/7.00  --inst_subs_given                       false
% 51.73/7.00  --inst_orphan_elimination               true
% 51.73/7.00  --inst_learning_loop_flag               true
% 51.73/7.00  --inst_learning_start                   3000
% 51.73/7.00  --inst_learning_factor                  2
% 51.73/7.00  --inst_start_prop_sim_after_learn       3
% 51.73/7.00  --inst_sel_renew                        solver
% 51.73/7.00  --inst_lit_activity_flag                true
% 51.73/7.00  --inst_restr_to_given                   false
% 51.73/7.00  --inst_activity_threshold               500
% 51.73/7.00  --inst_out_proof                        true
% 51.73/7.00  
% 51.73/7.00  ------ Resolution Options
% 51.73/7.00  
% 51.73/7.00  --resolution_flag                       true
% 51.73/7.00  --res_lit_sel                           adaptive
% 51.73/7.00  --res_lit_sel_side                      none
% 51.73/7.00  --res_ordering                          kbo
% 51.73/7.00  --res_to_prop_solver                    active
% 51.73/7.00  --res_prop_simpl_new                    false
% 51.73/7.00  --res_prop_simpl_given                  true
% 51.73/7.00  --res_passive_queue_type                priority_queues
% 51.73/7.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.73/7.00  --res_passive_queues_freq               [15;5]
% 51.73/7.00  --res_forward_subs                      full
% 51.73/7.00  --res_backward_subs                     full
% 51.73/7.00  --res_forward_subs_resolution           true
% 51.73/7.00  --res_backward_subs_resolution          true
% 51.73/7.00  --res_orphan_elimination                true
% 51.73/7.00  --res_time_limit                        2.
% 51.73/7.00  --res_out_proof                         true
% 51.73/7.00  
% 51.73/7.00  ------ Superposition Options
% 51.73/7.00  
% 51.73/7.00  --superposition_flag                    true
% 51.73/7.00  --sup_passive_queue_type                priority_queues
% 51.73/7.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.73/7.00  --sup_passive_queues_freq               [8;1;4]
% 51.73/7.00  --demod_completeness_check              fast
% 51.73/7.00  --demod_use_ground                      true
% 51.73/7.00  --sup_to_prop_solver                    passive
% 51.73/7.00  --sup_prop_simpl_new                    true
% 51.73/7.00  --sup_prop_simpl_given                  true
% 51.73/7.00  --sup_fun_splitting                     true
% 51.73/7.00  --sup_smt_interval                      50000
% 51.73/7.00  
% 51.73/7.00  ------ Superposition Simplification Setup
% 51.73/7.00  
% 51.73/7.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.73/7.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.73/7.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.73/7.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.73/7.00  --sup_full_triv                         [TrivRules;PropSubs]
% 51.73/7.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.73/7.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.73/7.00  --sup_immed_triv                        [TrivRules]
% 51.73/7.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.73/7.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.73/7.00  --sup_immed_bw_main                     []
% 51.73/7.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.73/7.00  --sup_input_triv                        [Unflattening;TrivRules]
% 51.73/7.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.73/7.00  --sup_input_bw                          []
% 51.73/7.00  
% 51.73/7.00  ------ Combination Options
% 51.73/7.00  
% 51.73/7.00  --comb_res_mult                         3
% 51.73/7.00  --comb_sup_mult                         2
% 51.73/7.00  --comb_inst_mult                        10
% 51.73/7.00  
% 51.73/7.00  ------ Debug Options
% 51.73/7.00  
% 51.73/7.00  --dbg_backtrace                         false
% 51.73/7.00  --dbg_dump_prop_clauses                 false
% 51.73/7.00  --dbg_dump_prop_clauses_file            -
% 51.73/7.00  --dbg_out_stat                          false
% 51.73/7.00  ------ Parsing...
% 51.73/7.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.73/7.00  
% 51.73/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 51.73/7.00  
% 51.73/7.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.73/7.00  
% 51.73/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.73/7.00  ------ Proving...
% 51.73/7.00  ------ Problem Properties 
% 51.73/7.00  
% 51.73/7.00  
% 51.73/7.00  clauses                                 34
% 51.73/7.00  conjectures                             4
% 51.73/7.00  EPR                                     5
% 51.73/7.00  Horn                                    30
% 51.73/7.00  unary                                   10
% 51.73/7.00  binary                                  16
% 51.73/7.00  lits                                    68
% 51.73/7.00  lits eq                                 21
% 51.73/7.00  fd_pure                                 0
% 51.73/7.00  fd_pseudo                               0
% 51.73/7.00  fd_cond                                 1
% 51.73/7.00  fd_pseudo_cond                          4
% 51.73/7.00  AC symbols                              1
% 51.73/7.00  
% 51.73/7.00  ------ Schedule dynamic 5 is on 
% 51.73/7.00  
% 51.73/7.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.73/7.00  
% 51.73/7.00  
% 51.73/7.00  ------ 
% 51.73/7.00  Current options:
% 51.73/7.00  ------ 
% 51.73/7.00  
% 51.73/7.00  ------ Input Options
% 51.73/7.00  
% 51.73/7.00  --out_options                           all
% 51.73/7.00  --tptp_safe_out                         true
% 51.73/7.00  --problem_path                          ""
% 51.73/7.00  --include_path                          ""
% 51.73/7.00  --clausifier                            res/vclausify_rel
% 51.73/7.00  --clausifier_options                    ""
% 51.73/7.00  --stdin                                 false
% 51.73/7.00  --stats_out                             all
% 51.73/7.00  
% 51.73/7.00  ------ General Options
% 51.73/7.00  
% 51.73/7.00  --fof                                   false
% 51.73/7.00  --time_out_real                         305.
% 51.73/7.00  --time_out_virtual                      -1.
% 51.73/7.00  --symbol_type_check                     false
% 51.73/7.00  --clausify_out                          false
% 51.73/7.00  --sig_cnt_out                           false
% 51.73/7.00  --trig_cnt_out                          false
% 51.73/7.00  --trig_cnt_out_tolerance                1.
% 51.73/7.00  --trig_cnt_out_sk_spl                   false
% 51.73/7.00  --abstr_cl_out                          false
% 51.73/7.00  
% 51.73/7.00  ------ Global Options
% 51.73/7.00  
% 51.73/7.00  --schedule                              default
% 51.73/7.00  --add_important_lit                     false
% 51.73/7.00  --prop_solver_per_cl                    1000
% 51.73/7.00  --min_unsat_core                        false
% 51.73/7.00  --soft_assumptions                      false
% 51.73/7.00  --soft_lemma_size                       3
% 51.73/7.00  --prop_impl_unit_size                   0
% 51.73/7.00  --prop_impl_unit                        []
% 51.73/7.00  --share_sel_clauses                     true
% 51.73/7.00  --reset_solvers                         false
% 51.73/7.00  --bc_imp_inh                            [conj_cone]
% 51.73/7.00  --conj_cone_tolerance                   3.
% 51.73/7.00  --extra_neg_conj                        none
% 51.73/7.00  --large_theory_mode                     true
% 51.73/7.00  --prolific_symb_bound                   200
% 51.73/7.00  --lt_threshold                          2000
% 51.73/7.00  --clause_weak_htbl                      true
% 51.73/7.00  --gc_record_bc_elim                     false
% 51.73/7.00  
% 51.73/7.00  ------ Preprocessing Options
% 51.73/7.00  
% 51.73/7.00  --preprocessing_flag                    true
% 51.73/7.00  --time_out_prep_mult                    0.1
% 51.73/7.00  --splitting_mode                        input
% 51.73/7.00  --splitting_grd                         true
% 51.73/7.00  --splitting_cvd                         false
% 51.73/7.00  --splitting_cvd_svl                     false
% 51.73/7.00  --splitting_nvd                         32
% 51.73/7.00  --sub_typing                            true
% 51.73/7.00  --prep_gs_sim                           true
% 51.73/7.00  --prep_unflatten                        true
% 51.73/7.00  --prep_res_sim                          true
% 51.73/7.00  --prep_upred                            true
% 51.73/7.00  --prep_sem_filter                       exhaustive
% 51.73/7.00  --prep_sem_filter_out                   false
% 51.73/7.00  --pred_elim                             true
% 51.73/7.00  --res_sim_input                         true
% 51.73/7.00  --eq_ax_congr_red                       true
% 51.73/7.00  --pure_diseq_elim                       true
% 51.73/7.00  --brand_transform                       false
% 51.73/7.00  --non_eq_to_eq                          false
% 51.73/7.00  --prep_def_merge                        true
% 51.73/7.00  --prep_def_merge_prop_impl              false
% 51.73/7.00  --prep_def_merge_mbd                    true
% 51.73/7.00  --prep_def_merge_tr_red                 false
% 51.73/7.00  --prep_def_merge_tr_cl                  false
% 51.73/7.00  --smt_preprocessing                     true
% 51.73/7.00  --smt_ac_axioms                         fast
% 51.73/7.00  --preprocessed_out                      false
% 51.73/7.00  --preprocessed_stats                    false
% 51.73/7.00  
% 51.73/7.00  ------ Abstraction refinement Options
% 51.73/7.00  
% 51.73/7.00  --abstr_ref                             []
% 51.73/7.00  --abstr_ref_prep                        false
% 51.73/7.00  --abstr_ref_until_sat                   false
% 51.73/7.00  --abstr_ref_sig_restrict                funpre
% 51.73/7.00  --abstr_ref_af_restrict_to_split_sk     false
% 51.73/7.00  --abstr_ref_under                       []
% 51.73/7.00  
% 51.73/7.00  ------ SAT Options
% 51.73/7.00  
% 51.73/7.00  --sat_mode                              false
% 51.73/7.00  --sat_fm_restart_options                ""
% 51.73/7.00  --sat_gr_def                            false
% 51.73/7.00  --sat_epr_types                         true
% 51.73/7.00  --sat_non_cyclic_types                  false
% 51.73/7.00  --sat_finite_models                     false
% 51.73/7.00  --sat_fm_lemmas                         false
% 51.73/7.00  --sat_fm_prep                           false
% 51.73/7.00  --sat_fm_uc_incr                        true
% 51.73/7.00  --sat_out_model                         small
% 51.73/7.00  --sat_out_clauses                       false
% 51.73/7.00  
% 51.73/7.00  ------ QBF Options
% 51.73/7.00  
% 51.73/7.00  --qbf_mode                              false
% 51.73/7.00  --qbf_elim_univ                         false
% 51.73/7.00  --qbf_dom_inst                          none
% 51.73/7.00  --qbf_dom_pre_inst                      false
% 51.73/7.00  --qbf_sk_in                             false
% 51.73/7.00  --qbf_pred_elim                         true
% 51.73/7.00  --qbf_split                             512
% 51.73/7.00  
% 51.73/7.00  ------ BMC1 Options
% 51.73/7.00  
% 51.73/7.00  --bmc1_incremental                      false
% 51.73/7.00  --bmc1_axioms                           reachable_all
% 51.73/7.00  --bmc1_min_bound                        0
% 51.73/7.00  --bmc1_max_bound                        -1
% 51.73/7.00  --bmc1_max_bound_default                -1
% 51.73/7.00  --bmc1_symbol_reachability              true
% 51.73/7.00  --bmc1_property_lemmas                  false
% 51.73/7.00  --bmc1_k_induction                      false
% 51.73/7.00  --bmc1_non_equiv_states                 false
% 51.73/7.00  --bmc1_deadlock                         false
% 51.73/7.00  --bmc1_ucm                              false
% 51.73/7.00  --bmc1_add_unsat_core                   none
% 51.73/7.00  --bmc1_unsat_core_children              false
% 51.73/7.00  --bmc1_unsat_core_extrapolate_axioms    false
% 51.73/7.00  --bmc1_out_stat                         full
% 51.73/7.00  --bmc1_ground_init                      false
% 51.73/7.00  --bmc1_pre_inst_next_state              false
% 51.73/7.00  --bmc1_pre_inst_state                   false
% 51.73/7.00  --bmc1_pre_inst_reach_state             false
% 51.73/7.00  --bmc1_out_unsat_core                   false
% 51.73/7.00  --bmc1_aig_witness_out                  false
% 51.73/7.00  --bmc1_verbose                          false
% 51.73/7.00  --bmc1_dump_clauses_tptp                false
% 51.73/7.00  --bmc1_dump_unsat_core_tptp             false
% 51.73/7.00  --bmc1_dump_file                        -
% 51.73/7.00  --bmc1_ucm_expand_uc_limit              128
% 51.73/7.00  --bmc1_ucm_n_expand_iterations          6
% 51.73/7.00  --bmc1_ucm_extend_mode                  1
% 51.73/7.00  --bmc1_ucm_init_mode                    2
% 51.73/7.00  --bmc1_ucm_cone_mode                    none
% 51.73/7.00  --bmc1_ucm_reduced_relation_type        0
% 51.73/7.00  --bmc1_ucm_relax_model                  4
% 51.73/7.00  --bmc1_ucm_full_tr_after_sat            true
% 51.73/7.00  --bmc1_ucm_expand_neg_assumptions       false
% 51.73/7.00  --bmc1_ucm_layered_model                none
% 51.73/7.00  --bmc1_ucm_max_lemma_size               10
% 51.73/7.00  
% 51.73/7.00  ------ AIG Options
% 51.73/7.00  
% 51.73/7.00  --aig_mode                              false
% 51.73/7.00  
% 51.73/7.00  ------ Instantiation Options
% 51.73/7.00  
% 51.73/7.00  --instantiation_flag                    true
% 51.73/7.00  --inst_sos_flag                         true
% 51.73/7.00  --inst_sos_phase                        true
% 51.73/7.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.73/7.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.73/7.00  --inst_lit_sel_side                     none
% 51.73/7.00  --inst_solver_per_active                1400
% 51.73/7.00  --inst_solver_calls_frac                1.
% 51.73/7.00  --inst_passive_queue_type               priority_queues
% 51.73/7.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.73/7.00  --inst_passive_queues_freq              [25;2]
% 51.73/7.00  --inst_dismatching                      true
% 51.73/7.00  --inst_eager_unprocessed_to_passive     true
% 51.73/7.00  --inst_prop_sim_given                   true
% 51.73/7.00  --inst_prop_sim_new                     false
% 51.73/7.00  --inst_subs_new                         false
% 51.73/7.00  --inst_eq_res_simp                      false
% 51.73/7.00  --inst_subs_given                       false
% 51.73/7.00  --inst_orphan_elimination               true
% 51.73/7.00  --inst_learning_loop_flag               true
% 51.73/7.00  --inst_learning_start                   3000
% 51.73/7.00  --inst_learning_factor                  2
% 51.73/7.00  --inst_start_prop_sim_after_learn       3
% 51.73/7.00  --inst_sel_renew                        solver
% 51.73/7.00  --inst_lit_activity_flag                true
% 51.73/7.00  --inst_restr_to_given                   false
% 51.73/7.00  --inst_activity_threshold               500
% 51.73/7.00  --inst_out_proof                        true
% 51.73/7.00  
% 51.73/7.00  ------ Resolution Options
% 51.73/7.00  
% 51.73/7.00  --resolution_flag                       false
% 51.73/7.00  --res_lit_sel                           adaptive
% 51.73/7.00  --res_lit_sel_side                      none
% 51.73/7.00  --res_ordering                          kbo
% 51.73/7.00  --res_to_prop_solver                    active
% 51.73/7.00  --res_prop_simpl_new                    false
% 51.73/7.00  --res_prop_simpl_given                  true
% 51.73/7.00  --res_passive_queue_type                priority_queues
% 51.73/7.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.73/7.00  --res_passive_queues_freq               [15;5]
% 51.73/7.00  --res_forward_subs                      full
% 51.73/7.00  --res_backward_subs                     full
% 51.73/7.00  --res_forward_subs_resolution           true
% 51.73/7.00  --res_backward_subs_resolution          true
% 51.73/7.00  --res_orphan_elimination                true
% 51.73/7.00  --res_time_limit                        2.
% 51.73/7.00  --res_out_proof                         true
% 51.73/7.00  
% 51.73/7.00  ------ Superposition Options
% 51.73/7.00  
% 51.73/7.00  --superposition_flag                    true
% 51.73/7.00  --sup_passive_queue_type                priority_queues
% 51.73/7.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.73/7.00  --sup_passive_queues_freq               [8;1;4]
% 51.73/7.00  --demod_completeness_check              fast
% 51.73/7.00  --demod_use_ground                      true
% 51.73/7.00  --sup_to_prop_solver                    passive
% 51.73/7.00  --sup_prop_simpl_new                    true
% 51.73/7.00  --sup_prop_simpl_given                  true
% 51.73/7.00  --sup_fun_splitting                     true
% 51.73/7.00  --sup_smt_interval                      50000
% 51.73/7.00  
% 51.73/7.00  ------ Superposition Simplification Setup
% 51.73/7.00  
% 51.73/7.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.73/7.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.73/7.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.73/7.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.73/7.00  --sup_full_triv                         [TrivRules;PropSubs]
% 51.73/7.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.73/7.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.73/7.00  --sup_immed_triv                        [TrivRules]
% 51.73/7.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.73/7.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.73/7.00  --sup_immed_bw_main                     []
% 51.73/7.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.73/7.00  --sup_input_triv                        [Unflattening;TrivRules]
% 51.73/7.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.73/7.00  --sup_input_bw                          []
% 51.73/7.00  
% 51.73/7.00  ------ Combination Options
% 51.73/7.00  
% 51.73/7.00  --comb_res_mult                         3
% 51.73/7.00  --comb_sup_mult                         2
% 51.73/7.00  --comb_inst_mult                        10
% 51.73/7.00  
% 51.73/7.00  ------ Debug Options
% 51.73/7.00  
% 51.73/7.00  --dbg_backtrace                         false
% 51.73/7.00  --dbg_dump_prop_clauses                 false
% 51.73/7.00  --dbg_dump_prop_clauses_file            -
% 51.73/7.00  --dbg_out_stat                          false
% 51.73/7.00  
% 51.73/7.00  
% 51.73/7.00  
% 51.73/7.00  
% 51.73/7.00  ------ Proving...
% 51.73/7.00  
% 51.73/7.00  
% 51.73/7.00  % SZS status Theorem for theBenchmark.p
% 51.73/7.00  
% 51.73/7.00  % SZS output start CNFRefutation for theBenchmark.p
% 51.73/7.00  
% 51.73/7.00  fof(f8,axiom,(
% 51.73/7.00    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f33,plain,(
% 51.73/7.00    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 51.73/7.00    inference(ennf_transformation,[],[f8])).
% 51.73/7.00  
% 51.73/7.00  fof(f34,plain,(
% 51.73/7.00    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 51.73/7.00    inference(flattening,[],[f33])).
% 51.73/7.00  
% 51.73/7.00  fof(f68,plain,(
% 51.73/7.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f34])).
% 51.73/7.00  
% 51.73/7.00  fof(f2,axiom,(
% 51.73/7.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f31,plain,(
% 51.73/7.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 51.73/7.00    inference(ennf_transformation,[],[f2])).
% 51.73/7.00  
% 51.73/7.00  fof(f38,plain,(
% 51.73/7.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 51.73/7.00    inference(nnf_transformation,[],[f31])).
% 51.73/7.00  
% 51.73/7.00  fof(f39,plain,(
% 51.73/7.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 51.73/7.00    inference(rectify,[],[f38])).
% 51.73/7.00  
% 51.73/7.00  fof(f40,plain,(
% 51.73/7.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 51.73/7.00    introduced(choice_axiom,[])).
% 51.73/7.00  
% 51.73/7.00  fof(f41,plain,(
% 51.73/7.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 51.73/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 51.73/7.00  
% 51.73/7.00  fof(f58,plain,(
% 51.73/7.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f41])).
% 51.73/7.00  
% 51.73/7.00  fof(f28,conjecture,(
% 51.73/7.00    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f29,negated_conjecture,(
% 51.73/7.00    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 51.73/7.00    inference(negated_conjecture,[],[f28])).
% 51.73/7.00  
% 51.73/7.00  fof(f37,plain,(
% 51.73/7.00    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 51.73/7.00    inference(ennf_transformation,[],[f29])).
% 51.73/7.00  
% 51.73/7.00  fof(f54,plain,(
% 51.73/7.00    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK6 | k1_tarski(sK4) != sK5) & (k1_tarski(sK4) != sK6 | k1_xboole_0 != sK5) & (k1_tarski(sK4) != sK6 | k1_tarski(sK4) != sK5) & k2_xboole_0(sK5,sK6) = k1_tarski(sK4))),
% 51.73/7.00    introduced(choice_axiom,[])).
% 51.73/7.00  
% 51.73/7.00  fof(f55,plain,(
% 51.73/7.00    (k1_xboole_0 != sK6 | k1_tarski(sK4) != sK5) & (k1_tarski(sK4) != sK6 | k1_xboole_0 != sK5) & (k1_tarski(sK4) != sK6 | k1_tarski(sK4) != sK5) & k2_xboole_0(sK5,sK6) = k1_tarski(sK4)),
% 51.73/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f37,f54])).
% 51.73/7.00  
% 51.73/7.00  fof(f96,plain,(
% 51.73/7.00    k2_xboole_0(sK5,sK6) = k1_tarski(sK4)),
% 51.73/7.00    inference(cnf_transformation,[],[f55])).
% 51.73/7.00  
% 51.73/7.00  fof(f23,axiom,(
% 51.73/7.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f88,plain,(
% 51.73/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 51.73/7.00    inference(cnf_transformation,[],[f23])).
% 51.73/7.00  
% 51.73/7.00  fof(f105,plain,(
% 51.73/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 51.73/7.00    inference(definition_unfolding,[],[f88,f104])).
% 51.73/7.00  
% 51.73/7.00  fof(f13,axiom,(
% 51.73/7.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f73,plain,(
% 51.73/7.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f13])).
% 51.73/7.00  
% 51.73/7.00  fof(f14,axiom,(
% 51.73/7.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f74,plain,(
% 51.73/7.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f14])).
% 51.73/7.00  
% 51.73/7.00  fof(f15,axiom,(
% 51.73/7.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f75,plain,(
% 51.73/7.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f15])).
% 51.73/7.00  
% 51.73/7.00  fof(f16,axiom,(
% 51.73/7.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f76,plain,(
% 51.73/7.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f16])).
% 51.73/7.00  
% 51.73/7.00  fof(f17,axiom,(
% 51.73/7.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f77,plain,(
% 51.73/7.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f17])).
% 51.73/7.00  
% 51.73/7.00  fof(f18,axiom,(
% 51.73/7.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f78,plain,(
% 51.73/7.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f18])).
% 51.73/7.00  
% 51.73/7.00  fof(f19,axiom,(
% 51.73/7.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f79,plain,(
% 51.73/7.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f19])).
% 51.73/7.00  
% 51.73/7.00  fof(f100,plain,(
% 51.73/7.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 51.73/7.00    inference(definition_unfolding,[],[f78,f79])).
% 51.73/7.00  
% 51.73/7.00  fof(f101,plain,(
% 51.73/7.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 51.73/7.00    inference(definition_unfolding,[],[f77,f100])).
% 51.73/7.00  
% 51.73/7.00  fof(f102,plain,(
% 51.73/7.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 51.73/7.00    inference(definition_unfolding,[],[f76,f101])).
% 51.73/7.00  
% 51.73/7.00  fof(f103,plain,(
% 51.73/7.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 51.73/7.00    inference(definition_unfolding,[],[f75,f102])).
% 51.73/7.00  
% 51.73/7.00  fof(f104,plain,(
% 51.73/7.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 51.73/7.00    inference(definition_unfolding,[],[f74,f103])).
% 51.73/7.00  
% 51.73/7.00  fof(f107,plain,(
% 51.73/7.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 51.73/7.00    inference(definition_unfolding,[],[f73,f104])).
% 51.73/7.00  
% 51.73/7.00  fof(f124,plain,(
% 51.73/7.00    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))),
% 51.73/7.00    inference(definition_unfolding,[],[f96,f105,f107])).
% 51.73/7.00  
% 51.73/7.00  fof(f5,axiom,(
% 51.73/7.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f43,plain,(
% 51.73/7.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.73/7.00    inference(nnf_transformation,[],[f5])).
% 51.73/7.00  
% 51.73/7.00  fof(f44,plain,(
% 51.73/7.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.73/7.00    inference(flattening,[],[f43])).
% 51.73/7.00  
% 51.73/7.00  fof(f63,plain,(
% 51.73/7.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 51.73/7.00    inference(cnf_transformation,[],[f44])).
% 51.73/7.00  
% 51.73/7.00  fof(f126,plain,(
% 51.73/7.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 51.73/7.00    inference(equality_resolution,[],[f63])).
% 51.73/7.00  
% 51.73/7.00  fof(f27,axiom,(
% 51.73/7.00    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f52,plain,(
% 51.73/7.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 51.73/7.00    inference(nnf_transformation,[],[f27])).
% 51.73/7.00  
% 51.73/7.00  fof(f53,plain,(
% 51.73/7.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 51.73/7.00    inference(flattening,[],[f52])).
% 51.73/7.00  
% 51.73/7.00  fof(f94,plain,(
% 51.73/7.00    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f53])).
% 51.73/7.00  
% 51.73/7.00  fof(f119,plain,(
% 51.73/7.00    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 51.73/7.00    inference(definition_unfolding,[],[f94,f104])).
% 51.73/7.00  
% 51.73/7.00  fof(f20,axiom,(
% 51.73/7.00    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f45,plain,(
% 51.73/7.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 51.73/7.00    inference(nnf_transformation,[],[f20])).
% 51.73/7.00  
% 51.73/7.00  fof(f46,plain,(
% 51.73/7.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 51.73/7.00    inference(rectify,[],[f45])).
% 51.73/7.00  
% 51.73/7.00  fof(f49,plain,(
% 51.73/7.00    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 51.73/7.00    introduced(choice_axiom,[])).
% 51.73/7.00  
% 51.73/7.00  fof(f48,plain,(
% 51.73/7.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 51.73/7.00    introduced(choice_axiom,[])).
% 51.73/7.00  
% 51.73/7.00  fof(f47,plain,(
% 51.73/7.00    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 51.73/7.00    introduced(choice_axiom,[])).
% 51.73/7.00  
% 51.73/7.00  fof(f50,plain,(
% 51.73/7.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 51.73/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f46,f49,f48,f47])).
% 51.73/7.00  
% 51.73/7.00  fof(f82,plain,(
% 51.73/7.00    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 51.73/7.00    inference(cnf_transformation,[],[f50])).
% 51.73/7.00  
% 51.73/7.00  fof(f127,plain,(
% 51.73/7.00    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 51.73/7.00    inference(equality_resolution,[],[f82])).
% 51.73/7.00  
% 51.73/7.00  fof(f59,plain,(
% 51.73/7.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f41])).
% 51.73/7.00  
% 51.73/7.00  fof(f6,axiom,(
% 51.73/7.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f32,plain,(
% 51.73/7.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 51.73/7.00    inference(ennf_transformation,[],[f6])).
% 51.73/7.00  
% 51.73/7.00  fof(f66,plain,(
% 51.73/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f32])).
% 51.73/7.00  
% 51.73/7.00  fof(f111,plain,(
% 51.73/7.00    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 51.73/7.00    inference(definition_unfolding,[],[f66,f105])).
% 51.73/7.00  
% 51.73/7.00  fof(f26,axiom,(
% 51.73/7.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f51,plain,(
% 51.73/7.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 51.73/7.00    inference(nnf_transformation,[],[f26])).
% 51.73/7.00  
% 51.73/7.00  fof(f92,plain,(
% 51.73/7.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f51])).
% 51.73/7.00  
% 51.73/7.00  fof(f116,plain,(
% 51.73/7.00    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 51.73/7.00    inference(definition_unfolding,[],[f92,f107])).
% 51.73/7.00  
% 51.73/7.00  fof(f9,axiom,(
% 51.73/7.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f69,plain,(
% 51.73/7.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 51.73/7.00    inference(cnf_transformation,[],[f9])).
% 51.73/7.00  
% 51.73/7.00  fof(f112,plain,(
% 51.73/7.00    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 51.73/7.00    inference(definition_unfolding,[],[f69,f105])).
% 51.73/7.00  
% 51.73/7.00  fof(f65,plain,(
% 51.73/7.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f44])).
% 51.73/7.00  
% 51.73/7.00  fof(f4,axiom,(
% 51.73/7.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f30,plain,(
% 51.73/7.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 51.73/7.00    inference(rectify,[],[f4])).
% 51.73/7.00  
% 51.73/7.00  fof(f62,plain,(
% 51.73/7.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 51.73/7.00    inference(cnf_transformation,[],[f30])).
% 51.73/7.00  
% 51.73/7.00  fof(f12,axiom,(
% 51.73/7.00    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f72,plain,(
% 51.73/7.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f12])).
% 51.73/7.00  
% 51.73/7.00  fof(f106,plain,(
% 51.73/7.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 51.73/7.00    inference(definition_unfolding,[],[f72,f105])).
% 51.73/7.00  
% 51.73/7.00  fof(f110,plain,(
% 51.73/7.00    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 51.73/7.00    inference(definition_unfolding,[],[f62,f106])).
% 51.73/7.00  
% 51.73/7.00  fof(f10,axiom,(
% 51.73/7.00    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f70,plain,(
% 51.73/7.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f10])).
% 51.73/7.00  
% 51.73/7.00  fof(f1,axiom,(
% 51.73/7.00    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f56,plain,(
% 51.73/7.00    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f1])).
% 51.73/7.00  
% 51.73/7.00  fof(f7,axiom,(
% 51.73/7.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f67,plain,(
% 51.73/7.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f7])).
% 51.73/7.00  
% 51.73/7.00  fof(f22,axiom,(
% 51.73/7.00    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f36,plain,(
% 51.73/7.00    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 51.73/7.00    inference(ennf_transformation,[],[f22])).
% 51.73/7.00  
% 51.73/7.00  fof(f87,plain,(
% 51.73/7.00    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f36])).
% 51.73/7.00  
% 51.73/7.00  fof(f114,plain,(
% 51.73/7.00    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 51.73/7.00    inference(definition_unfolding,[],[f87,f107])).
% 51.73/7.00  
% 51.73/7.00  fof(f21,axiom,(
% 51.73/7.00    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 51.73/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.73/7.00  
% 51.73/7.00  fof(f35,plain,(
% 51.73/7.00    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 51.73/7.00    inference(ennf_transformation,[],[f21])).
% 51.73/7.00  
% 51.73/7.00  fof(f86,plain,(
% 51.73/7.00    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 51.73/7.00    inference(cnf_transformation,[],[f35])).
% 51.73/7.00  
% 51.73/7.00  fof(f113,plain,(
% 51.73/7.00    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 51.73/7.00    inference(definition_unfolding,[],[f86,f107])).
% 51.73/7.00  
% 51.73/7.00  fof(f99,plain,(
% 51.73/7.00    k1_xboole_0 != sK6 | k1_tarski(sK4) != sK5),
% 51.73/7.00    inference(cnf_transformation,[],[f55])).
% 51.73/7.00  
% 51.73/7.00  fof(f121,plain,(
% 51.73/7.00    k1_xboole_0 != sK6 | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5),
% 51.73/7.00    inference(definition_unfolding,[],[f99,f107])).
% 51.73/7.00  
% 51.73/7.00  fof(f98,plain,(
% 51.73/7.00    k1_tarski(sK4) != sK6 | k1_xboole_0 != sK5),
% 51.73/7.00    inference(cnf_transformation,[],[f55])).
% 51.73/7.00  
% 51.73/7.00  fof(f122,plain,(
% 51.73/7.00    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 | k1_xboole_0 != sK5),
% 51.73/7.00    inference(definition_unfolding,[],[f98,f107])).
% 51.73/7.00  
% 51.73/7.00  fof(f97,plain,(
% 51.73/7.00    k1_tarski(sK4) != sK6 | k1_tarski(sK4) != sK5),
% 51.73/7.00    inference(cnf_transformation,[],[f55])).
% 51.73/7.00  
% 51.73/7.00  fof(f123,plain,(
% 51.73/7.00    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5),
% 51.73/7.00    inference(definition_unfolding,[],[f97,f107,f107])).
% 51.73/7.00  
% 51.73/7.00  cnf(c_12,plain,
% 51.73/7.00      ( ~ r1_xboole_0(X0,X1)
% 51.73/7.00      | ~ r1_tarski(X2,X0)
% 51.73/7.00      | ~ r1_tarski(X2,X1)
% 51.73/7.00      | k1_xboole_0 = X2 ),
% 51.73/7.00      inference(cnf_transformation,[],[f68]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_179326,plain,
% 51.73/7.00      ( ~ r1_xboole_0(X0,X1)
% 51.73/7.00      | ~ r1_tarski(sK6,X0)
% 51.73/7.00      | ~ r1_tarski(sK6,X1)
% 51.73/7.00      | k1_xboole_0 = sK6 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_12]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_180925,plain,
% 51.73/7.00      ( ~ r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6)
% 51.73/7.00      | ~ r1_tarski(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 51.73/7.00      | ~ r1_tarski(sK6,sK6)
% 51.73/7.00      | k1_xboole_0 = sK6 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_179326]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_13613,plain,
% 51.73/7.00      ( ~ r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)
% 51.73/7.00      | ~ r1_tarski(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 51.73/7.00      | ~ r1_tarski(X0,sK5)
% 51.73/7.00      | k1_xboole_0 = X0 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_12]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_169314,plain,
% 51.73/7.00      ( ~ r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)
% 51.73/7.00      | ~ r1_tarski(k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 51.73/7.00      | ~ r1_tarski(k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))),sK5)
% 51.73/7.00      | k1_xboole_0 = k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_13613]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_169331,plain,
% 51.73/7.00      ( k1_xboole_0 = k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 51.73/7.00      | r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top
% 51.73/7.00      | r1_tarski(k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
% 51.73/7.00      | r1_tarski(k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))),sK5) != iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_169314]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_808,plain,
% 51.73/7.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 51.73/7.00      theory(equality) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1628,plain,
% 51.73/7.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK6) | X2 != X0 | sK6 != X1 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_808]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_22041,plain,
% 51.73/7.00      ( ~ r1_tarski(X0,sK6) | r1_tarski(X1,sK6) | X1 != X0 | sK6 != sK6 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_1628]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_100024,plain,
% 51.73/7.00      ( ~ r1_tarski(X0,sK6)
% 51.73/7.00      | r1_tarski(sK5,sK6)
% 51.73/7.00      | sK5 != X0
% 51.73/7.00      | sK6 != sK6 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_22041]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_156548,plain,
% 51.73/7.00      ( r1_tarski(sK5,sK6)
% 51.73/7.00      | ~ r1_tarski(k1_xboole_0,sK6)
% 51.73/7.00      | sK5 != k1_xboole_0
% 51.73/7.00      | sK6 != sK6 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_100024]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2,plain,
% 51.73/7.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 51.73/7.00      inference(cnf_transformation,[],[f58]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1400,plain,
% 51.73/7.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 51.73/7.00      | r1_tarski(X0,X1) = iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_34,negated_conjecture,
% 51.73/7.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
% 51.73/7.00      inference(cnf_transformation,[],[f124]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_9,plain,
% 51.73/7.00      ( r1_tarski(X0,X0) ),
% 51.73/7.00      inference(cnf_transformation,[],[f126]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1395,plain,
% 51.73/7.00      ( r1_tarski(X0,X0) = iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_29,plain,
% 51.73/7.00      ( r2_hidden(X0,X1)
% 51.73/7.00      | ~ r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
% 51.73/7.00      inference(cnf_transformation,[],[f119]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1379,plain,
% 51.73/7.00      ( r2_hidden(X0,X1) = iProver_top
% 51.73/7.00      | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) != iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_2316,plain,
% 51.73/7.00      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = iProver_top ),
% 51.73/7.00      inference(superposition,[status(thm)],[c_1395,c_1379]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_19,plain,
% 51.73/7.00      ( ~ r2_hidden(X0,X1)
% 51.73/7.00      | ~ r2_hidden(X2,X0)
% 51.73/7.00      | r2_hidden(X2,k3_tarski(X1)) ),
% 51.73/7.00      inference(cnf_transformation,[],[f127]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1387,plain,
% 51.73/7.00      ( r2_hidden(X0,X1) != iProver_top
% 51.73/7.00      | r2_hidden(X2,X0) != iProver_top
% 51.73/7.00      | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_20910,plain,
% 51.73/7.00      ( r2_hidden(X0,X1) != iProver_top
% 51.73/7.00      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 51.73/7.00      inference(superposition,[status(thm)],[c_2316,c_1387]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_143210,plain,
% 51.73/7.00      ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 51.73/7.00      | r2_hidden(X0,sK6) != iProver_top ),
% 51.73/7.00      inference(superposition,[status(thm)],[c_34,c_20910]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1,plain,
% 51.73/7.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 51.73/7.00      inference(cnf_transformation,[],[f59]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1401,plain,
% 51.73/7.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 51.73/7.00      | r1_tarski(X0,X1) = iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_143412,plain,
% 51.73/7.00      ( r2_hidden(sK0(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK6) != iProver_top
% 51.73/7.00      | r1_tarski(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 51.73/7.00      inference(superposition,[status(thm)],[c_143210,c_1401]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_143905,plain,
% 51.73/7.00      ( r1_tarski(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 51.73/7.00      inference(superposition,[status(thm)],[c_1400,c_143412]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_143906,plain,
% 51.73/7.00      ( r1_tarski(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 51.73/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_143905]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1766,plain,
% 51.73/7.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK5) | X2 != X0 | sK5 != X1 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_808]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_22052,plain,
% 51.73/7.00      ( ~ r1_tarski(X0,sK5) | r1_tarski(X1,sK5) | X1 != X0 | sK5 != sK5 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_1766]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_100068,plain,
% 51.73/7.00      ( r1_tarski(X0,sK5)
% 51.73/7.00      | ~ r1_tarski(sK5,sK5)
% 51.73/7.00      | X0 != sK5
% 51.73/7.00      | sK5 != sK5 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_22052]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_138410,plain,
% 51.73/7.00      ( r1_tarski(k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))),sK5)
% 51.73/7.00      | ~ r1_tarski(sK5,sK5)
% 51.73/7.00      | k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != sK5
% 51.73/7.00      | sK5 != sK5 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_100068]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_138411,plain,
% 51.73/7.00      ( k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != sK5
% 51.73/7.00      | sK5 != sK5
% 51.73/7.00      | r1_tarski(k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))),sK5) = iProver_top
% 51.73/7.00      | r1_tarski(sK5,sK5) != iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_138410]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_806,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1488,plain,
% 51.73/7.00      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_806]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_5303,plain,
% 51.73/7.00      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_1488]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_17523,plain,
% 51.73/7.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK6)) != sK6
% 51.73/7.00      | sK6 = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK6))
% 51.73/7.00      | sK6 != sK6 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_5303]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_135930,plain,
% 51.73/7.00      ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) != sK6
% 51.73/7.00      | sK6 = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
% 51.73/7.00      | sK6 != sK6 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_17523]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_3675,plain,
% 51.73/7.00      ( ~ r1_tarski(X0,X1)
% 51.73/7.00      | r1_tarski(X2,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 51.73/7.00      | X2 != X0
% 51.73/7.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X1 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_808]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_22063,plain,
% 51.73/7.00      ( r1_tarski(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 51.73/7.00      | ~ r1_tarski(X1,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)))
% 51.73/7.00      | X0 != X1
% 51.73/7.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_3675]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_42142,plain,
% 51.73/7.00      ( r1_tarski(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 51.73/7.00      | ~ r1_tarski(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)))
% 51.73/7.00      | X0 != sK5
% 51.73/7.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_22063]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_113779,plain,
% 51.73/7.00      ( r1_tarski(k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 51.73/7.00      | ~ r1_tarski(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)))
% 51.73/7.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
% 51.73/7.00      | k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != sK5 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_42142]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_113780,plain,
% 51.73/7.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
% 51.73/7.00      | k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != sK5
% 51.73/7.00      | r1_tarski(k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 51.73/7.00      | r1_tarski(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) != iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_113779]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1495,plain,
% 51.73/7.00      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_806]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_3697,plain,
% 51.73/7.00      ( sK5 != X0 | sK5 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_1495]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_106940,plain,
% 51.73/7.00      ( sK5 != k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 51.73/7.00      | sK5 = k1_xboole_0
% 51.73/7.00      | k1_xboole_0 != k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_3697]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_10,plain,
% 51.73/7.00      ( ~ r1_tarski(X0,X1)
% 51.73/7.00      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
% 51.73/7.00      inference(cnf_transformation,[],[f111]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_67370,plain,
% 51.73/7.00      ( ~ r1_tarski(sK5,sK6)
% 51.73/7.00      | k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) = sK6 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_10]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_26,plain,
% 51.73/7.00      ( ~ r2_hidden(X0,X1)
% 51.73/7.00      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 51.73/7.00      inference(cnf_transformation,[],[f116]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1382,plain,
% 51.73/7.00      ( r2_hidden(X0,X1) != iProver_top
% 51.73/7.00      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_13,plain,
% 51.73/7.00      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 51.73/7.00      inference(cnf_transformation,[],[f112]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1391,plain,
% 51.73/7.00      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_11417,plain,
% 51.73/7.00      ( r1_tarski(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 51.73/7.00      inference(superposition,[status(thm)],[c_34,c_1391]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_7,plain,
% 51.73/7.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 51.73/7.00      inference(cnf_transformation,[],[f65]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1396,plain,
% 51.73/7.00      ( X0 = X1
% 51.73/7.00      | r1_tarski(X1,X0) != iProver_top
% 51.73/7.00      | r1_tarski(X0,X1) != iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_51433,plain,
% 51.73/7.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK5
% 51.73/7.00      | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top ),
% 51.73/7.00      inference(superposition,[status(thm)],[c_11417,c_1396]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_51446,plain,
% 51.73/7.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK5
% 51.73/7.00      | r2_hidden(sK4,sK5) != iProver_top ),
% 51.73/7.00      inference(superposition,[status(thm)],[c_1382,c_51433]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_6,plain,
% 51.73/7.00      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
% 51.73/7.00      inference(cnf_transformation,[],[f110]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_14,plain,
% 51.73/7.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 51.73/7.00      inference(cnf_transformation,[],[f70]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_0,plain,
% 51.73/7.00      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 51.73/7.00      inference(cnf_transformation,[],[f56]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_801,plain,
% 51.73/7.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = X0 ),
% 51.73/7.00      inference(theory_normalisation,[status(thm)],[c_6,c_14,c_0]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_30816,plain,
% 51.73/7.00      ( k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = sK5 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_801]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_11,plain,
% 51.73/7.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 51.73/7.00      inference(cnf_transformation,[],[f67]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_14792,plain,
% 51.73/7.00      ( r1_xboole_0(k6_enumset1(sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6)),k1_xboole_0) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_11]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1809,plain,
% 51.73/7.00      ( r1_tarski(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,X0))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_13]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_14690,plain,
% 51.73/7.00      ( r1_tarski(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_1809]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_14693,plain,
% 51.73/7.00      ( r1_tarski(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))) = iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_14690]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1444,plain,
% 51.73/7.00      ( ~ r1_xboole_0(X0,X1)
% 51.73/7.00      | ~ r1_tarski(sK5,X0)
% 51.73/7.00      | ~ r1_tarski(sK5,X1)
% 51.73/7.00      | k1_xboole_0 = sK5 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_12]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_13616,plain,
% 51.73/7.00      ( ~ r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)
% 51.73/7.00      | ~ r1_tarski(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 51.73/7.00      | ~ r1_tarski(sK5,sK5)
% 51.73/7.00      | k1_xboole_0 = sK5 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_1444]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_13617,plain,
% 51.73/7.00      ( k1_xboole_0 = sK5
% 51.73/7.00      | r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top
% 51.73/7.00      | r1_tarski(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
% 51.73/7.00      | r1_tarski(sK5,sK5) != iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_13616]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_23,plain,
% 51.73/7.00      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 51.73/7.00      | r2_hidden(X0,X1) ),
% 51.73/7.00      inference(cnf_transformation,[],[f114]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_10730,plain,
% 51.73/7.00      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK6)
% 51.73/7.00      | r2_hidden(X0,sK6) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_23]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_10732,plain,
% 51.73/7.00      ( r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6)
% 51.73/7.00      | r2_hidden(sK4,sK6) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_10730]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1788,plain,
% 51.73/7.00      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_1495]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_5761,plain,
% 51.73/7.00      ( k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != sK5
% 51.73/7.00      | sK5 = k5_xboole_0(sK5,k5_xboole_0(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 51.73/7.00      | sK5 != sK5 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_1788]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_22,plain,
% 51.73/7.00      ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 51.73/7.00      | ~ r2_hidden(X0,X1) ),
% 51.73/7.00      inference(cnf_transformation,[],[f113]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_4899,plain,
% 51.73/7.00      ( ~ r1_xboole_0(k6_enumset1(sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6),sK0(k1_xboole_0,sK6)),k1_xboole_0)
% 51.73/7.00      | ~ r2_hidden(sK0(k1_xboole_0,sK6),k1_xboole_0) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_22]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1971,plain,
% 51.73/7.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
% 51.73/7.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6
% 51.73/7.00      | sK6 != X0 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_806]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_3289,plain,
% 51.73/7.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
% 51.73/7.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6
% 51.73/7.00      | sK6 != k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_1971]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1968,plain,
% 51.73/7.00      ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6)
% 51.73/7.00      | ~ r1_tarski(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 51.73/7.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_7]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1918,plain,
% 51.73/7.00      ( r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)
% 51.73/7.00      | r2_hidden(sK4,sK5) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_23]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1919,plain,
% 51.73/7.00      ( r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = iProver_top
% 51.73/7.00      | r2_hidden(sK4,sK5) = iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_1918]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1817,plain,
% 51.73/7.00      ( ~ r2_hidden(X0,sK6)
% 51.73/7.00      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK6) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_26]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1819,plain,
% 51.73/7.00      ( ~ r2_hidden(sK4,sK6)
% 51.73/7.00      | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_1817]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1489,plain,
% 51.73/7.00      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_7]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1757,plain,
% 51.73/7.00      ( ~ r1_tarski(sK5,sK5) | sK5 = sK5 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_1489]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1723,plain,
% 51.73/7.00      ( r1_tarski(sK5,sK5) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_9]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1724,plain,
% 51.73/7.00      ( r1_tarski(sK5,sK5) = iProver_top ),
% 51.73/7.00      inference(predicate_to_equality,[status(thm)],[c_1723]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1668,plain,
% 51.73/7.00      ( r1_tarski(sK6,sK6) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_9]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1482,plain,
% 51.73/7.00      ( ~ r1_tarski(X0,sK6) | ~ r1_tarski(sK6,X0) | sK6 = X0 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_7]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1617,plain,
% 51.73/7.00      ( ~ r1_tarski(sK6,sK6) | sK6 = sK6 ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_1482]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_1579,plain,
% 51.73/7.00      ( r2_hidden(sK0(k1_xboole_0,sK6),k1_xboole_0)
% 51.73/7.00      | r1_tarski(k1_xboole_0,sK6) ),
% 51.73/7.00      inference(instantiation,[status(thm)],[c_2]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_31,negated_conjecture,
% 51.73/7.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5
% 51.73/7.00      | k1_xboole_0 != sK6 ),
% 51.73/7.00      inference(cnf_transformation,[],[f121]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_32,negated_conjecture,
% 51.73/7.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
% 51.73/7.00      | k1_xboole_0 != sK5 ),
% 51.73/7.00      inference(cnf_transformation,[],[f122]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(c_33,negated_conjecture,
% 51.73/7.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5
% 51.73/7.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 ),
% 51.73/7.00      inference(cnf_transformation,[],[f123]) ).
% 51.73/7.00  
% 51.73/7.00  cnf(contradiction,plain,
% 51.73/7.00      ( $false ),
% 51.73/7.00      inference(minisat,
% 51.73/7.00                [status(thm)],
% 51.73/7.00                [c_180925,c_169331,c_156548,c_143906,c_138411,c_135930,
% 51.73/7.00                 c_113780,c_106940,c_67370,c_51446,c_30816,c_14792,
% 51.73/7.00                 c_14693,c_13617,c_11417,c_10732,c_5761,c_4899,c_3289,
% 51.73/7.00                 c_1968,c_1919,c_1819,c_1757,c_1724,c_1723,c_1668,c_1617,
% 51.73/7.00                 c_1579,c_31,c_32,c_33,c_34]) ).
% 51.73/7.00  
% 51.73/7.00  
% 51.73/7.00  % SZS output end CNFRefutation for theBenchmark.p
% 51.73/7.00  
% 51.73/7.00  ------                               Statistics
% 51.73/7.00  
% 51.73/7.00  ------ General
% 51.73/7.00  
% 51.73/7.00  abstr_ref_over_cycles:                  0
% 51.73/7.00  abstr_ref_under_cycles:                 0
% 51.73/7.00  gc_basic_clause_elim:                   0
% 51.73/7.00  forced_gc_time:                         0
% 51.73/7.00  parsing_time:                           0.01
% 51.73/7.00  unif_index_cands_time:                  0.
% 51.73/7.00  unif_index_add_time:                    0.
% 51.73/7.00  orderings_time:                         0.
% 51.73/7.00  out_proof_time:                         0.013
% 51.73/7.00  total_time:                             6.465
% 51.73/7.00  num_of_symbols:                         46
% 51.73/7.00  num_of_terms:                           311201
% 51.73/7.00  
% 51.73/7.00  ------ Preprocessing
% 51.73/7.00  
% 51.73/7.00  num_of_splits:                          0
% 51.73/7.00  num_of_split_atoms:                     1
% 51.73/7.00  num_of_reused_defs:                     0
% 51.73/7.00  num_eq_ax_congr_red:                    24
% 51.73/7.00  num_of_sem_filtered_clauses:            1
% 51.73/7.00  num_of_subtypes:                        0
% 51.73/7.00  monotx_restored_types:                  0
% 51.73/7.00  sat_num_of_epr_types:                   0
% 51.73/7.00  sat_num_of_non_cyclic_types:            0
% 51.73/7.00  sat_guarded_non_collapsed_types:        0
% 51.73/7.00  num_pure_diseq_elim:                    0
% 51.73/7.00  simp_replaced_by:                       0
% 51.73/7.00  res_preprocessed:                       153
% 51.73/7.00  prep_upred:                             0
% 51.73/7.00  prep_unflattend:                        24
% 51.73/7.00  smt_new_axioms:                         0
% 51.73/7.00  pred_elim_cands:                        3
% 51.73/7.00  pred_elim:                              0
% 51.73/7.00  pred_elim_cl:                           0
% 51.73/7.00  pred_elim_cycles:                       2
% 51.73/7.00  merged_defs:                            24
% 51.73/7.00  merged_defs_ncl:                        0
% 51.73/7.00  bin_hyper_res:                          24
% 51.73/7.00  prep_cycles:                            4
% 51.73/7.00  pred_elim_time:                         0.004
% 51.73/7.00  splitting_time:                         0.
% 51.73/7.00  sem_filter_time:                        0.
% 51.73/7.00  monotx_time:                            0.001
% 51.73/7.00  subtype_inf_time:                       0.
% 51.73/7.00  
% 51.73/7.00  ------ Problem properties
% 51.73/7.00  
% 51.73/7.00  clauses:                                34
% 51.73/7.00  conjectures:                            4
% 51.73/7.00  epr:                                    5
% 51.73/7.00  horn:                                   30
% 51.73/7.00  ground:                                 5
% 51.73/7.00  unary:                                  10
% 51.73/7.00  binary:                                 16
% 51.73/7.00  lits:                                   68
% 51.73/7.00  lits_eq:                                21
% 51.73/7.00  fd_pure:                                0
% 51.73/7.00  fd_pseudo:                              0
% 51.73/7.00  fd_cond:                                1
% 51.73/7.00  fd_pseudo_cond:                         4
% 51.73/7.00  ac_symbols:                             2
% 51.73/7.00  
% 51.73/7.00  ------ Propositional Solver
% 51.73/7.00  
% 51.73/7.00  prop_solver_calls:                      41
% 51.73/7.00  prop_fast_solver_calls:                 2822
% 51.73/7.00  smt_solver_calls:                       0
% 51.73/7.00  smt_fast_solver_calls:                  0
% 51.73/7.00  prop_num_of_clauses:                    35527
% 51.73/7.00  prop_preprocess_simplified:             43435
% 51.73/7.00  prop_fo_subsumed:                       5
% 51.73/7.00  prop_solver_time:                       0.
% 51.73/7.00  smt_solver_time:                        0.
% 51.73/7.00  smt_fast_solver_time:                   0.
% 51.73/7.00  prop_fast_solver_time:                  0.
% 51.73/7.00  prop_unsat_core_time:                   0.003
% 51.73/7.00  
% 51.73/7.00  ------ QBF
% 51.73/7.00  
% 51.73/7.00  qbf_q_res:                              0
% 51.73/7.00  qbf_num_tautologies:                    0
% 51.73/7.00  qbf_prep_cycles:                        0
% 51.73/7.00  
% 51.73/7.00  ------ BMC1
% 51.73/7.00  
% 51.73/7.00  bmc1_current_bound:                     -1
% 51.73/7.00  bmc1_last_solved_bound:                 -1
% 51.73/7.00  bmc1_unsat_core_size:                   -1
% 51.73/7.00  bmc1_unsat_core_parents_size:           -1
% 51.73/7.00  bmc1_merge_next_fun:                    0
% 51.73/7.00  bmc1_unsat_core_clauses_time:           0.
% 51.73/7.00  
% 51.73/7.00  ------ Instantiation
% 51.73/7.00  
% 51.73/7.00  inst_num_of_clauses:                    214
% 51.73/7.00  inst_num_in_passive:                    16
% 51.73/7.00  inst_num_in_active:                     2059
% 51.73/7.00  inst_num_in_unprocessed:                108
% 51.73/7.00  inst_num_of_loops:                      3091
% 51.73/7.00  inst_num_of_learning_restarts:          1
% 51.73/7.00  inst_num_moves_active_passive:          1027
% 51.73/7.00  inst_lit_activity:                      0
% 51.73/7.00  inst_lit_activity_moves:                0
% 51.73/7.00  inst_num_tautologies:                   0
% 51.73/7.00  inst_num_prop_implied:                  0
% 51.73/7.00  inst_num_existing_simplified:           0
% 51.73/7.00  inst_num_eq_res_simplified:             0
% 51.73/7.00  inst_num_child_elim:                    0
% 51.73/7.00  inst_num_of_dismatching_blockings:      5848
% 51.73/7.00  inst_num_of_non_proper_insts:           9327
% 51.73/7.00  inst_num_of_duplicates:                 0
% 51.73/7.00  inst_inst_num_from_inst_to_res:         0
% 51.73/7.00  inst_dismatching_checking_time:         0.
% 51.73/7.00  
% 51.73/7.00  ------ Resolution
% 51.73/7.00  
% 51.73/7.00  res_num_of_clauses:                     42
% 51.73/7.00  res_num_in_passive:                     42
% 51.73/7.00  res_num_in_active:                      0
% 51.73/7.00  res_num_of_loops:                       157
% 51.73/7.00  res_forward_subset_subsumed:            821
% 51.73/7.00  res_backward_subset_subsumed:           20
% 51.73/7.00  res_forward_subsumed:                   0
% 51.73/7.00  res_backward_subsumed:                  0
% 51.73/7.00  res_forward_subsumption_resolution:     0
% 51.73/7.00  res_backward_subsumption_resolution:    0
% 51.73/7.00  res_clause_to_clause_subsumption:       389493
% 51.73/7.00  res_orphan_elimination:                 0
% 51.73/7.00  res_tautology_del:                      607
% 51.73/7.00  res_num_eq_res_simplified:              0
% 51.73/7.00  res_num_sel_changes:                    0
% 51.73/7.00  res_moves_from_active_to_pass:          0
% 51.73/7.00  
% 51.73/7.00  ------ Superposition
% 51.73/7.00  
% 51.73/7.00  sup_time_total:                         0.
% 51.73/7.00  sup_time_generating:                    0.
% 51.73/7.00  sup_time_sim_full:                      0.
% 51.73/7.00  sup_time_sim_immed:                     0.
% 51.73/7.00  
% 51.73/7.00  sup_num_of_clauses:                     8201
% 51.73/7.00  sup_num_in_active:                      487
% 51.73/7.00  sup_num_in_passive:                     7714
% 51.73/7.00  sup_num_of_loops:                       618
% 51.73/7.00  sup_fw_superposition:                   44324
% 51.73/7.00  sup_bw_superposition:                   28653
% 51.73/7.00  sup_immediate_simplified:               37414
% 51.73/7.00  sup_given_eliminated:                   5
% 51.73/7.00  comparisons_done:                       0
% 51.73/7.00  comparisons_avoided:                    0
% 51.73/7.00  
% 51.73/7.00  ------ Simplifications
% 51.73/7.00  
% 51.73/7.00  
% 51.73/7.00  sim_fw_subset_subsumed:                 1147
% 51.73/7.00  sim_bw_subset_subsumed:                 494
% 51.73/7.00  sim_fw_subsumed:                        833
% 51.73/7.00  sim_bw_subsumed:                        34
% 51.73/7.00  sim_fw_subsumption_res:                 0
% 51.73/7.00  sim_bw_subsumption_res:                 0
% 51.73/7.00  sim_tautology_del:                      5
% 51.73/7.00  sim_eq_tautology_del:                   5372
% 51.73/7.00  sim_eq_res_simp:                        1
% 51.73/7.00  sim_fw_demodulated:                     36201
% 51.73/7.00  sim_bw_demodulated:                     344
% 51.73/7.00  sim_light_normalised:                   10978
% 51.73/7.00  sim_joinable_taut:                      1594
% 51.73/7.00  sim_joinable_simp:                      0
% 51.73/7.00  sim_ac_normalised:                      0
% 51.73/7.00  sim_smt_subsumption:                    0
% 51.73/7.00  
%------------------------------------------------------------------------------
