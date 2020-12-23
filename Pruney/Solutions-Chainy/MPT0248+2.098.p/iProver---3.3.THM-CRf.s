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
% DateTime   : Thu Dec  3 11:32:23 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 745 expanded)
%              Number of clauses        :   66 (  96 expanded)
%              Number of leaves         :   21 ( 220 expanded)
%              Depth                    :   16
%              Number of atoms          :  446 (1757 expanded)
%              Number of equality atoms :  253 (1307 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK5
        | k1_tarski(sK3) != sK4 )
      & ( k1_tarski(sK3) != sK5
        | k1_xboole_0 != sK4 )
      & ( k1_tarski(sK3) != sK5
        | k1_tarski(sK3) != sK4 )
      & k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( k1_xboole_0 != sK5
      | k1_tarski(sK3) != sK4 )
    & ( k1_tarski(sK3) != sK5
      | k1_xboole_0 != sK4 )
    & ( k1_tarski(sK3) != sK5
      | k1_tarski(sK3) != sK4 )
    & k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f25,f44])).

fof(f80,plain,(
    k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f74,f85])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f84,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f85,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f84])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f67,f85])).

fof(f114,plain,(
    k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(definition_unfolding,[],[f80,f86,f87])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f98,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f62,f86])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f39])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f71,f87,f87])).

fof(f81,plain,
    ( k1_tarski(sK3) != sK5
    | k1_tarski(sK3) != sK4 ),
    inference(cnf_transformation,[],[f45])).

fof(f113,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4 ),
    inference(definition_unfolding,[],[f81,f87,f87])).

fof(f82,plain,
    ( k1_tarski(sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f45])).

fof(f112,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(definition_unfolding,[],[f82,f87])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f64,f87])).

fof(f120,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f101])).

fof(f121,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f120])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f46,f86])).

fof(f117,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f94])).

fof(f83,plain,
    ( k1_xboole_0 != sK5
    | k1_tarski(sK3) != sK4 ),
    inference(cnf_transformation,[],[f45])).

fof(f111,plain,
    ( k1_xboole_0 != sK5
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4 ),
    inference(definition_unfolding,[],[f83,f87])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f42])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f79,f85])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f31])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f92,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f48,f86])).

fof(f115,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f92])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f63,f87])).

fof(f122,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f102])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f86])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f57,f86])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f119,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

cnf(c_423,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1502,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_423])).

cnf(c_3043,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1502])).

cnf(c_9757,plain,
    ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) != sK5
    | sK5 = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3043])).

cnf(c_31,negated_conjecture,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_15,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_798,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1538,plain,
    ( r1_tarski(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_31,c_798])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_791,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3648,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1538,c_791])).

cnf(c_30,negated_conjecture,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_4137,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3648,c_30])).

cnf(c_29,negated_conjecture,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1082,plain,
    ( ~ r1_tarski(sK4,k3_enumset1(X0,X0,X0,X0,X0))
    | k3_enumset1(X0,X0,X0,X0,X0) = sK4
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1084,plain,
    ( ~ r1_tarski(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1082])).

cnf(c_1544,plain,
    ( r1_tarski(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1538])).

cnf(c_4363,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4137,c_30,c_29,c_1084,c_1544])).

cnf(c_18,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_795,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_804,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3919,plain,
    ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_31,c_804])).

cnf(c_3957,plain,
    ( r2_hidden(sK3,sK4) = iProver_top
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_795,c_3919])).

cnf(c_28,negated_conjecture,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_53,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_55,plain,
    ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_998,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_423])).

cnf(c_1584,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_422,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1585,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_422])).

cnf(c_25,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_790,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_802,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2171,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4
    | r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1538,c_802])).

cnf(c_2664,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_790,c_2171])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_803,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_806,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2747,plain,
    ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_31,c_806])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_794,plain,
    ( X0 = X1
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2758,plain,
    ( sK3 = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2747,c_794])).

cnf(c_2860,plain,
    ( sK1(sK5) = sK3
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_803,c_2758])).

cnf(c_3106,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2860,c_803])).

cnf(c_3949,plain,
    ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(sK3,sK4) = iProver_top
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3919])).

cnf(c_4096,plain,
    ( r2_hidden(sK3,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3957,c_28,c_55,c_1584,c_1585,c_2664,c_3106,c_3949])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_799,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1898,plain,
    ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_1538,c_799])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_800,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2380,plain,
    ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1898,c_800])).

cnf(c_3009,plain,
    ( r1_tarski(sK4,X0) = iProver_top
    | r2_hidden(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_790,c_2380])).

cnf(c_4102,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4096,c_3009])).

cnf(c_10,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_2980,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1491,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2979,plain,
    ( ~ r1_tarski(sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1491])).

cnf(c_1168,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != X0
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_423])).

cnf(c_1857,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5))
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK5
    | sK5 != k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1168])).

cnf(c_1800,plain,
    ( ~ r1_tarski(sK4,sK5)
    | k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1801,plain,
    ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) = sK5
    | r1_tarski(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1800])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9757,c_4363,c_4102,c_2980,c_2979,c_1857,c_1801,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:33:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.26/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/0.92  
% 3.26/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.26/0.92  
% 3.26/0.92  ------  iProver source info
% 3.26/0.92  
% 3.26/0.92  git: date: 2020-06-30 10:37:57 +0100
% 3.26/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.26/0.92  git: non_committed_changes: false
% 3.26/0.92  git: last_make_outside_of_git: false
% 3.26/0.92  
% 3.26/0.92  ------ 
% 3.26/0.92  
% 3.26/0.92  ------ Input Options
% 3.26/0.92  
% 3.26/0.92  --out_options                           all
% 3.26/0.92  --tptp_safe_out                         true
% 3.26/0.92  --problem_path                          ""
% 3.26/0.92  --include_path                          ""
% 3.26/0.92  --clausifier                            res/vclausify_rel
% 3.26/0.92  --clausifier_options                    --mode clausify
% 3.26/0.92  --stdin                                 false
% 3.26/0.92  --stats_out                             all
% 3.26/0.92  
% 3.26/0.92  ------ General Options
% 3.26/0.92  
% 3.26/0.92  --fof                                   false
% 3.26/0.92  --time_out_real                         305.
% 3.26/0.92  --time_out_virtual                      -1.
% 3.26/0.92  --symbol_type_check                     false
% 3.26/0.92  --clausify_out                          false
% 3.26/0.92  --sig_cnt_out                           false
% 3.26/0.92  --trig_cnt_out                          false
% 3.26/0.92  --trig_cnt_out_tolerance                1.
% 3.26/0.92  --trig_cnt_out_sk_spl                   false
% 3.26/0.92  --abstr_cl_out                          false
% 3.26/0.92  
% 3.26/0.92  ------ Global Options
% 3.26/0.92  
% 3.26/0.92  --schedule                              default
% 3.26/0.92  --add_important_lit                     false
% 3.26/0.92  --prop_solver_per_cl                    1000
% 3.26/0.92  --min_unsat_core                        false
% 3.26/0.92  --soft_assumptions                      false
% 3.26/0.92  --soft_lemma_size                       3
% 3.26/0.92  --prop_impl_unit_size                   0
% 3.26/0.92  --prop_impl_unit                        []
% 3.26/0.92  --share_sel_clauses                     true
% 3.26/0.92  --reset_solvers                         false
% 3.26/0.92  --bc_imp_inh                            [conj_cone]
% 3.26/0.92  --conj_cone_tolerance                   3.
% 3.26/0.92  --extra_neg_conj                        none
% 3.26/0.92  --large_theory_mode                     true
% 3.26/0.92  --prolific_symb_bound                   200
% 3.26/0.92  --lt_threshold                          2000
% 3.26/0.92  --clause_weak_htbl                      true
% 3.26/0.92  --gc_record_bc_elim                     false
% 3.26/0.92  
% 3.26/0.92  ------ Preprocessing Options
% 3.26/0.92  
% 3.26/0.92  --preprocessing_flag                    true
% 3.26/0.92  --time_out_prep_mult                    0.1
% 3.26/0.92  --splitting_mode                        input
% 3.26/0.92  --splitting_grd                         true
% 3.26/0.92  --splitting_cvd                         false
% 3.26/0.92  --splitting_cvd_svl                     false
% 3.26/0.92  --splitting_nvd                         32
% 3.26/0.92  --sub_typing                            true
% 3.26/0.92  --prep_gs_sim                           true
% 3.26/0.92  --prep_unflatten                        true
% 3.26/0.92  --prep_res_sim                          true
% 3.26/0.92  --prep_upred                            true
% 3.26/0.92  --prep_sem_filter                       exhaustive
% 3.26/0.92  --prep_sem_filter_out                   false
% 3.26/0.92  --pred_elim                             true
% 3.26/0.92  --res_sim_input                         true
% 3.26/0.92  --eq_ax_congr_red                       true
% 3.26/0.92  --pure_diseq_elim                       true
% 3.26/0.92  --brand_transform                       false
% 3.26/0.92  --non_eq_to_eq                          false
% 3.26/0.92  --prep_def_merge                        true
% 3.26/0.92  --prep_def_merge_prop_impl              false
% 3.26/0.92  --prep_def_merge_mbd                    true
% 3.26/0.92  --prep_def_merge_tr_red                 false
% 3.26/0.92  --prep_def_merge_tr_cl                  false
% 3.26/0.92  --smt_preprocessing                     true
% 3.26/0.92  --smt_ac_axioms                         fast
% 3.26/0.92  --preprocessed_out                      false
% 3.26/0.92  --preprocessed_stats                    false
% 3.26/0.92  
% 3.26/0.92  ------ Abstraction refinement Options
% 3.26/0.92  
% 3.26/0.92  --abstr_ref                             []
% 3.26/0.92  --abstr_ref_prep                        false
% 3.26/0.92  --abstr_ref_until_sat                   false
% 3.26/0.92  --abstr_ref_sig_restrict                funpre
% 3.26/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 3.26/0.92  --abstr_ref_under                       []
% 3.26/0.92  
% 3.26/0.92  ------ SAT Options
% 3.26/0.92  
% 3.26/0.92  --sat_mode                              false
% 3.26/0.92  --sat_fm_restart_options                ""
% 3.26/0.92  --sat_gr_def                            false
% 3.26/0.92  --sat_epr_types                         true
% 3.26/0.92  --sat_non_cyclic_types                  false
% 3.26/0.92  --sat_finite_models                     false
% 3.26/0.92  --sat_fm_lemmas                         false
% 3.26/0.92  --sat_fm_prep                           false
% 3.26/0.92  --sat_fm_uc_incr                        true
% 3.26/0.92  --sat_out_model                         small
% 3.26/0.92  --sat_out_clauses                       false
% 3.26/0.92  
% 3.26/0.92  ------ QBF Options
% 3.26/0.92  
% 3.26/0.92  --qbf_mode                              false
% 3.26/0.92  --qbf_elim_univ                         false
% 3.26/0.92  --qbf_dom_inst                          none
% 3.26/0.92  --qbf_dom_pre_inst                      false
% 3.26/0.92  --qbf_sk_in                             false
% 3.26/0.92  --qbf_pred_elim                         true
% 3.26/0.92  --qbf_split                             512
% 3.26/0.92  
% 3.26/0.92  ------ BMC1 Options
% 3.26/0.92  
% 3.26/0.92  --bmc1_incremental                      false
% 3.26/0.92  --bmc1_axioms                           reachable_all
% 3.26/0.92  --bmc1_min_bound                        0
% 3.26/0.92  --bmc1_max_bound                        -1
% 3.26/0.92  --bmc1_max_bound_default                -1
% 3.26/0.92  --bmc1_symbol_reachability              true
% 3.26/0.92  --bmc1_property_lemmas                  false
% 3.26/0.92  --bmc1_k_induction                      false
% 3.26/0.92  --bmc1_non_equiv_states                 false
% 3.26/0.92  --bmc1_deadlock                         false
% 3.26/0.92  --bmc1_ucm                              false
% 3.26/0.92  --bmc1_add_unsat_core                   none
% 3.26/0.92  --bmc1_unsat_core_children              false
% 3.26/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 3.26/0.92  --bmc1_out_stat                         full
% 3.26/0.92  --bmc1_ground_init                      false
% 3.26/0.92  --bmc1_pre_inst_next_state              false
% 3.26/0.92  --bmc1_pre_inst_state                   false
% 3.26/0.92  --bmc1_pre_inst_reach_state             false
% 3.26/0.92  --bmc1_out_unsat_core                   false
% 3.26/0.92  --bmc1_aig_witness_out                  false
% 3.26/0.92  --bmc1_verbose                          false
% 3.26/0.92  --bmc1_dump_clauses_tptp                false
% 3.26/0.92  --bmc1_dump_unsat_core_tptp             false
% 3.26/0.92  --bmc1_dump_file                        -
% 3.26/0.92  --bmc1_ucm_expand_uc_limit              128
% 3.26/0.92  --bmc1_ucm_n_expand_iterations          6
% 3.26/0.92  --bmc1_ucm_extend_mode                  1
% 3.26/0.92  --bmc1_ucm_init_mode                    2
% 3.26/0.92  --bmc1_ucm_cone_mode                    none
% 3.26/0.92  --bmc1_ucm_reduced_relation_type        0
% 3.26/0.92  --bmc1_ucm_relax_model                  4
% 3.26/0.92  --bmc1_ucm_full_tr_after_sat            true
% 3.26/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 3.26/0.92  --bmc1_ucm_layered_model                none
% 3.26/0.92  --bmc1_ucm_max_lemma_size               10
% 3.26/0.92  
% 3.26/0.92  ------ AIG Options
% 3.26/0.92  
% 3.26/0.92  --aig_mode                              false
% 3.26/0.92  
% 3.26/0.92  ------ Instantiation Options
% 3.26/0.92  
% 3.26/0.92  --instantiation_flag                    true
% 3.26/0.92  --inst_sos_flag                         false
% 3.26/0.92  --inst_sos_phase                        true
% 3.26/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.26/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.26/0.92  --inst_lit_sel_side                     num_symb
% 3.26/0.92  --inst_solver_per_active                1400
% 3.26/0.92  --inst_solver_calls_frac                1.
% 3.26/0.92  --inst_passive_queue_type               priority_queues
% 3.26/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.26/0.92  --inst_passive_queues_freq              [25;2]
% 3.26/0.92  --inst_dismatching                      true
% 3.26/0.92  --inst_eager_unprocessed_to_passive     true
% 3.26/0.92  --inst_prop_sim_given                   true
% 3.26/0.92  --inst_prop_sim_new                     false
% 3.26/0.92  --inst_subs_new                         false
% 3.26/0.92  --inst_eq_res_simp                      false
% 3.26/0.92  --inst_subs_given                       false
% 3.26/0.92  --inst_orphan_elimination               true
% 3.26/0.92  --inst_learning_loop_flag               true
% 3.26/0.92  --inst_learning_start                   3000
% 3.26/0.92  --inst_learning_factor                  2
% 3.26/0.92  --inst_start_prop_sim_after_learn       3
% 3.26/0.92  --inst_sel_renew                        solver
% 3.26/0.92  --inst_lit_activity_flag                true
% 3.26/0.92  --inst_restr_to_given                   false
% 3.26/0.92  --inst_activity_threshold               500
% 3.26/0.92  --inst_out_proof                        true
% 3.26/0.92  
% 3.26/0.92  ------ Resolution Options
% 3.26/0.92  
% 3.26/0.92  --resolution_flag                       true
% 3.26/0.92  --res_lit_sel                           adaptive
% 3.26/0.92  --res_lit_sel_side                      none
% 3.26/0.92  --res_ordering                          kbo
% 3.26/0.92  --res_to_prop_solver                    active
% 3.26/0.92  --res_prop_simpl_new                    false
% 3.26/0.92  --res_prop_simpl_given                  true
% 3.26/0.92  --res_passive_queue_type                priority_queues
% 3.26/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.26/0.92  --res_passive_queues_freq               [15;5]
% 3.26/0.92  --res_forward_subs                      full
% 3.26/0.92  --res_backward_subs                     full
% 3.26/0.92  --res_forward_subs_resolution           true
% 3.26/0.92  --res_backward_subs_resolution          true
% 3.26/0.92  --res_orphan_elimination                true
% 3.26/0.92  --res_time_limit                        2.
% 3.26/0.92  --res_out_proof                         true
% 3.26/0.92  
% 3.26/0.92  ------ Superposition Options
% 3.26/0.92  
% 3.26/0.92  --superposition_flag                    true
% 3.26/0.92  --sup_passive_queue_type                priority_queues
% 3.26/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.26/0.92  --sup_passive_queues_freq               [8;1;4]
% 3.26/0.92  --demod_completeness_check              fast
% 3.26/0.92  --demod_use_ground                      true
% 3.26/0.92  --sup_to_prop_solver                    passive
% 3.26/0.92  --sup_prop_simpl_new                    true
% 3.26/0.92  --sup_prop_simpl_given                  true
% 3.26/0.92  --sup_fun_splitting                     false
% 3.26/0.92  --sup_smt_interval                      50000
% 3.26/0.92  
% 3.26/0.92  ------ Superposition Simplification Setup
% 3.26/0.92  
% 3.26/0.92  --sup_indices_passive                   []
% 3.26/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 3.26/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.92  --sup_full_bw                           [BwDemod]
% 3.26/0.92  --sup_immed_triv                        [TrivRules]
% 3.26/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.92  --sup_immed_bw_main                     []
% 3.26/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 3.26/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.92  
% 3.26/0.92  ------ Combination Options
% 3.26/0.92  
% 3.26/0.92  --comb_res_mult                         3
% 3.26/0.92  --comb_sup_mult                         2
% 3.26/0.92  --comb_inst_mult                        10
% 3.26/0.92  
% 3.26/0.92  ------ Debug Options
% 3.26/0.92  
% 3.26/0.92  --dbg_backtrace                         false
% 3.26/0.92  --dbg_dump_prop_clauses                 false
% 3.26/0.92  --dbg_dump_prop_clauses_file            -
% 3.26/0.92  --dbg_out_stat                          false
% 3.26/0.92  ------ Parsing...
% 3.26/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.26/0.92  
% 3.26/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.26/0.92  
% 3.26/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.26/0.92  
% 3.26/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.26/0.92  ------ Proving...
% 3.26/0.92  ------ Problem Properties 
% 3.26/0.92  
% 3.26/0.92  
% 3.26/0.92  clauses                                 31
% 3.26/0.92  conjectures                             4
% 3.26/0.92  EPR                                     2
% 3.26/0.92  Horn                                    25
% 3.26/0.92  unary                                   10
% 3.26/0.92  binary                                  12
% 3.26/0.92  lits                                    62
% 3.26/0.92  lits eq                                 26
% 3.26/0.92  fd_pure                                 0
% 3.26/0.92  fd_pseudo                               0
% 3.26/0.92  fd_cond                                 1
% 3.26/0.92  fd_pseudo_cond                          8
% 3.26/0.92  AC symbols                              0
% 3.26/0.92  
% 3.26/0.92  ------ Schedule dynamic 5 is on 
% 3.26/0.92  
% 3.26/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.26/0.92  
% 3.26/0.92  
% 3.26/0.92  ------ 
% 3.26/0.92  Current options:
% 3.26/0.92  ------ 
% 3.26/0.92  
% 3.26/0.92  ------ Input Options
% 3.26/0.92  
% 3.26/0.92  --out_options                           all
% 3.26/0.92  --tptp_safe_out                         true
% 3.26/0.92  --problem_path                          ""
% 3.26/0.92  --include_path                          ""
% 3.26/0.92  --clausifier                            res/vclausify_rel
% 3.26/0.92  --clausifier_options                    --mode clausify
% 3.26/0.92  --stdin                                 false
% 3.26/0.92  --stats_out                             all
% 3.26/0.92  
% 3.26/0.92  ------ General Options
% 3.26/0.92  
% 3.26/0.92  --fof                                   false
% 3.26/0.92  --time_out_real                         305.
% 3.26/0.92  --time_out_virtual                      -1.
% 3.26/0.92  --symbol_type_check                     false
% 3.26/0.92  --clausify_out                          false
% 3.26/0.92  --sig_cnt_out                           false
% 3.26/0.92  --trig_cnt_out                          false
% 3.26/0.92  --trig_cnt_out_tolerance                1.
% 3.26/0.92  --trig_cnt_out_sk_spl                   false
% 3.26/0.92  --abstr_cl_out                          false
% 3.26/0.92  
% 3.26/0.92  ------ Global Options
% 3.26/0.92  
% 3.26/0.92  --schedule                              default
% 3.26/0.92  --add_important_lit                     false
% 3.26/0.92  --prop_solver_per_cl                    1000
% 3.26/0.92  --min_unsat_core                        false
% 3.26/0.92  --soft_assumptions                      false
% 3.26/0.92  --soft_lemma_size                       3
% 3.26/0.92  --prop_impl_unit_size                   0
% 3.26/0.92  --prop_impl_unit                        []
% 3.26/0.92  --share_sel_clauses                     true
% 3.26/0.92  --reset_solvers                         false
% 3.26/0.92  --bc_imp_inh                            [conj_cone]
% 3.26/0.92  --conj_cone_tolerance                   3.
% 3.26/0.92  --extra_neg_conj                        none
% 3.26/0.92  --large_theory_mode                     true
% 3.26/0.92  --prolific_symb_bound                   200
% 3.26/0.92  --lt_threshold                          2000
% 3.26/0.92  --clause_weak_htbl                      true
% 3.26/0.92  --gc_record_bc_elim                     false
% 3.26/0.92  
% 3.26/0.92  ------ Preprocessing Options
% 3.26/0.92  
% 3.26/0.92  --preprocessing_flag                    true
% 3.26/0.92  --time_out_prep_mult                    0.1
% 3.26/0.92  --splitting_mode                        input
% 3.26/0.92  --splitting_grd                         true
% 3.26/0.92  --splitting_cvd                         false
% 3.26/0.92  --splitting_cvd_svl                     false
% 3.26/0.92  --splitting_nvd                         32
% 3.26/0.92  --sub_typing                            true
% 3.26/0.92  --prep_gs_sim                           true
% 3.26/0.92  --prep_unflatten                        true
% 3.26/0.92  --prep_res_sim                          true
% 3.26/0.92  --prep_upred                            true
% 3.26/0.92  --prep_sem_filter                       exhaustive
% 3.26/0.92  --prep_sem_filter_out                   false
% 3.26/0.92  --pred_elim                             true
% 3.26/0.92  --res_sim_input                         true
% 3.26/0.92  --eq_ax_congr_red                       true
% 3.26/0.92  --pure_diseq_elim                       true
% 3.26/0.92  --brand_transform                       false
% 3.26/0.92  --non_eq_to_eq                          false
% 3.26/0.92  --prep_def_merge                        true
% 3.26/0.92  --prep_def_merge_prop_impl              false
% 3.26/0.92  --prep_def_merge_mbd                    true
% 3.26/0.92  --prep_def_merge_tr_red                 false
% 3.26/0.92  --prep_def_merge_tr_cl                  false
% 3.26/0.92  --smt_preprocessing                     true
% 3.26/0.92  --smt_ac_axioms                         fast
% 3.26/0.92  --preprocessed_out                      false
% 3.26/0.92  --preprocessed_stats                    false
% 3.26/0.92  
% 3.26/0.92  ------ Abstraction refinement Options
% 3.26/0.92  
% 3.26/0.92  --abstr_ref                             []
% 3.26/0.92  --abstr_ref_prep                        false
% 3.26/0.92  --abstr_ref_until_sat                   false
% 3.26/0.92  --abstr_ref_sig_restrict                funpre
% 3.26/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 3.26/0.92  --abstr_ref_under                       []
% 3.26/0.92  
% 3.26/0.92  ------ SAT Options
% 3.26/0.92  
% 3.26/0.92  --sat_mode                              false
% 3.26/0.92  --sat_fm_restart_options                ""
% 3.26/0.92  --sat_gr_def                            false
% 3.26/0.92  --sat_epr_types                         true
% 3.26/0.92  --sat_non_cyclic_types                  false
% 3.26/0.92  --sat_finite_models                     false
% 3.26/0.92  --sat_fm_lemmas                         false
% 3.26/0.92  --sat_fm_prep                           false
% 3.26/0.92  --sat_fm_uc_incr                        true
% 3.26/0.92  --sat_out_model                         small
% 3.26/0.92  --sat_out_clauses                       false
% 3.26/0.92  
% 3.26/0.92  ------ QBF Options
% 3.26/0.92  
% 3.26/0.92  --qbf_mode                              false
% 3.26/0.92  --qbf_elim_univ                         false
% 3.26/0.92  --qbf_dom_inst                          none
% 3.26/0.92  --qbf_dom_pre_inst                      false
% 3.26/0.92  --qbf_sk_in                             false
% 3.26/0.92  --qbf_pred_elim                         true
% 3.26/0.92  --qbf_split                             512
% 3.26/0.92  
% 3.26/0.92  ------ BMC1 Options
% 3.26/0.92  
% 3.26/0.92  --bmc1_incremental                      false
% 3.26/0.92  --bmc1_axioms                           reachable_all
% 3.26/0.92  --bmc1_min_bound                        0
% 3.26/0.92  --bmc1_max_bound                        -1
% 3.26/0.92  --bmc1_max_bound_default                -1
% 3.26/0.92  --bmc1_symbol_reachability              true
% 3.26/0.92  --bmc1_property_lemmas                  false
% 3.26/0.92  --bmc1_k_induction                      false
% 3.26/0.92  --bmc1_non_equiv_states                 false
% 3.26/0.92  --bmc1_deadlock                         false
% 3.26/0.92  --bmc1_ucm                              false
% 3.26/0.92  --bmc1_add_unsat_core                   none
% 3.26/0.92  --bmc1_unsat_core_children              false
% 3.26/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 3.26/0.92  --bmc1_out_stat                         full
% 3.26/0.92  --bmc1_ground_init                      false
% 3.26/0.92  --bmc1_pre_inst_next_state              false
% 3.26/0.92  --bmc1_pre_inst_state                   false
% 3.26/0.92  --bmc1_pre_inst_reach_state             false
% 3.26/0.92  --bmc1_out_unsat_core                   false
% 3.26/0.92  --bmc1_aig_witness_out                  false
% 3.26/0.92  --bmc1_verbose                          false
% 3.26/0.92  --bmc1_dump_clauses_tptp                false
% 3.26/0.92  --bmc1_dump_unsat_core_tptp             false
% 3.26/0.92  --bmc1_dump_file                        -
% 3.26/0.92  --bmc1_ucm_expand_uc_limit              128
% 3.26/0.92  --bmc1_ucm_n_expand_iterations          6
% 3.26/0.92  --bmc1_ucm_extend_mode                  1
% 3.26/0.92  --bmc1_ucm_init_mode                    2
% 3.26/0.92  --bmc1_ucm_cone_mode                    none
% 3.26/0.92  --bmc1_ucm_reduced_relation_type        0
% 3.26/0.92  --bmc1_ucm_relax_model                  4
% 3.26/0.92  --bmc1_ucm_full_tr_after_sat            true
% 3.26/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 3.26/0.92  --bmc1_ucm_layered_model                none
% 3.26/0.92  --bmc1_ucm_max_lemma_size               10
% 3.26/0.92  
% 3.26/0.92  ------ AIG Options
% 3.26/0.92  
% 3.26/0.92  --aig_mode                              false
% 3.26/0.92  
% 3.26/0.92  ------ Instantiation Options
% 3.26/0.92  
% 3.26/0.92  --instantiation_flag                    true
% 3.26/0.92  --inst_sos_flag                         false
% 3.26/0.92  --inst_sos_phase                        true
% 3.26/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.26/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.26/0.92  --inst_lit_sel_side                     none
% 3.26/0.92  --inst_solver_per_active                1400
% 3.26/0.92  --inst_solver_calls_frac                1.
% 3.26/0.92  --inst_passive_queue_type               priority_queues
% 3.26/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.26/0.92  --inst_passive_queues_freq              [25;2]
% 3.26/0.92  --inst_dismatching                      true
% 3.26/0.92  --inst_eager_unprocessed_to_passive     true
% 3.26/0.92  --inst_prop_sim_given                   true
% 3.26/0.92  --inst_prop_sim_new                     false
% 3.26/0.92  --inst_subs_new                         false
% 3.26/0.92  --inst_eq_res_simp                      false
% 3.26/0.92  --inst_subs_given                       false
% 3.26/0.92  --inst_orphan_elimination               true
% 3.26/0.92  --inst_learning_loop_flag               true
% 3.26/0.92  --inst_learning_start                   3000
% 3.26/0.92  --inst_learning_factor                  2
% 3.26/0.92  --inst_start_prop_sim_after_learn       3
% 3.26/0.92  --inst_sel_renew                        solver
% 3.26/0.92  --inst_lit_activity_flag                true
% 3.26/0.92  --inst_restr_to_given                   false
% 3.26/0.92  --inst_activity_threshold               500
% 3.26/0.92  --inst_out_proof                        true
% 3.26/0.92  
% 3.26/0.92  ------ Resolution Options
% 3.26/0.92  
% 3.26/0.92  --resolution_flag                       false
% 3.26/0.92  --res_lit_sel                           adaptive
% 3.26/0.92  --res_lit_sel_side                      none
% 3.26/0.92  --res_ordering                          kbo
% 3.26/0.92  --res_to_prop_solver                    active
% 3.26/0.92  --res_prop_simpl_new                    false
% 3.26/0.92  --res_prop_simpl_given                  true
% 3.26/0.92  --res_passive_queue_type                priority_queues
% 3.26/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.26/0.92  --res_passive_queues_freq               [15;5]
% 3.26/0.92  --res_forward_subs                      full
% 3.26/0.92  --res_backward_subs                     full
% 3.26/0.92  --res_forward_subs_resolution           true
% 3.26/0.92  --res_backward_subs_resolution          true
% 3.26/0.92  --res_orphan_elimination                true
% 3.26/0.92  --res_time_limit                        2.
% 3.26/0.92  --res_out_proof                         true
% 3.26/0.92  
% 3.26/0.92  ------ Superposition Options
% 3.26/0.92  
% 3.26/0.92  --superposition_flag                    true
% 3.26/0.92  --sup_passive_queue_type                priority_queues
% 3.26/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.26/0.92  --sup_passive_queues_freq               [8;1;4]
% 3.26/0.92  --demod_completeness_check              fast
% 3.26/0.92  --demod_use_ground                      true
% 3.26/0.92  --sup_to_prop_solver                    passive
% 3.26/0.92  --sup_prop_simpl_new                    true
% 3.26/0.92  --sup_prop_simpl_given                  true
% 3.26/0.92  --sup_fun_splitting                     false
% 3.26/0.92  --sup_smt_interval                      50000
% 3.26/0.92  
% 3.26/0.92  ------ Superposition Simplification Setup
% 3.26/0.92  
% 3.26/0.92  --sup_indices_passive                   []
% 3.26/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 3.26/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.92  --sup_full_bw                           [BwDemod]
% 3.26/0.92  --sup_immed_triv                        [TrivRules]
% 3.26/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.92  --sup_immed_bw_main                     []
% 3.26/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 3.26/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.92  
% 3.26/0.92  ------ Combination Options
% 3.26/0.92  
% 3.26/0.92  --comb_res_mult                         3
% 3.26/0.92  --comb_sup_mult                         2
% 3.26/0.92  --comb_inst_mult                        10
% 3.26/0.92  
% 3.26/0.92  ------ Debug Options
% 3.26/0.92  
% 3.26/0.92  --dbg_backtrace                         false
% 3.26/0.92  --dbg_dump_prop_clauses                 false
% 3.26/0.92  --dbg_dump_prop_clauses_file            -
% 3.26/0.92  --dbg_out_stat                          false
% 3.26/0.92  
% 3.26/0.92  
% 3.26/0.92  
% 3.26/0.92  
% 3.26/0.92  ------ Proving...
% 3.26/0.92  
% 3.26/0.92  
% 3.26/0.92  % SZS status Theorem for theBenchmark.p
% 3.26/0.92  
% 3.26/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 3.26/0.92  
% 3.26/0.92  fof(f20,conjecture,(
% 3.26/0.92    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.26/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.92  
% 3.26/0.92  fof(f21,negated_conjecture,(
% 3.26/0.92    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.26/0.92    inference(negated_conjecture,[],[f20])).
% 3.26/0.92  
% 3.26/0.92  fof(f25,plain,(
% 3.26/0.92    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.26/0.92    inference(ennf_transformation,[],[f21])).
% 3.26/0.92  
% 3.26/0.92  fof(f44,plain,(
% 3.26/0.92    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4) & (k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4) & (k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4) & k2_xboole_0(sK4,sK5) = k1_tarski(sK3))),
% 3.26/0.92    introduced(choice_axiom,[])).
% 3.26/0.92  
% 3.26/0.92  fof(f45,plain,(
% 3.26/0.92    (k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4) & (k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4) & (k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4) & k2_xboole_0(sK4,sK5) = k1_tarski(sK3)),
% 3.26/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f25,f44])).
% 3.26/0.92  
% 3.26/0.92  fof(f80,plain,(
% 3.26/0.92    k2_xboole_0(sK4,sK5) = k1_tarski(sK3)),
% 3.26/0.92    inference(cnf_transformation,[],[f45])).
% 3.26/0.92  
% 3.26/0.92  fof(f17,axiom,(
% 3.26/0.92    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.26/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.92  
% 3.26/0.92  fof(f74,plain,(
% 3.26/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.26/0.92    inference(cnf_transformation,[],[f17])).
% 3.26/0.92  
% 3.26/0.92  fof(f86,plain,(
% 3.26/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.26/0.92    inference(definition_unfolding,[],[f74,f85])).
% 3.26/0.92  
% 3.26/0.92  fof(f12,axiom,(
% 3.26/0.92    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.26/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.92  
% 3.26/0.92  fof(f67,plain,(
% 3.26/0.92    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.26/0.92    inference(cnf_transformation,[],[f12])).
% 3.26/0.92  
% 3.26/0.92  fof(f13,axiom,(
% 3.26/0.92    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.26/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.92  
% 3.26/0.92  fof(f68,plain,(
% 3.26/0.92    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.26/0.92    inference(cnf_transformation,[],[f13])).
% 3.26/0.92  
% 3.26/0.92  fof(f14,axiom,(
% 3.26/0.92    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.26/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.92  
% 3.26/0.92  fof(f69,plain,(
% 3.26/0.92    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.26/0.92    inference(cnf_transformation,[],[f14])).
% 3.26/0.92  
% 3.26/0.92  fof(f15,axiom,(
% 3.26/0.92    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.26/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.92  
% 3.26/0.92  fof(f70,plain,(
% 3.26/0.92    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.26/0.92    inference(cnf_transformation,[],[f15])).
% 3.26/0.92  
% 3.26/0.92  fof(f84,plain,(
% 3.26/0.92    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.26/0.92    inference(definition_unfolding,[],[f69,f70])).
% 3.26/0.92  
% 3.26/0.92  fof(f85,plain,(
% 3.26/0.92    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.26/0.92    inference(definition_unfolding,[],[f68,f84])).
% 3.26/0.92  
% 3.26/0.92  fof(f87,plain,(
% 3.26/0.92    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.26/0.92    inference(definition_unfolding,[],[f67,f85])).
% 3.26/0.92  
% 3.26/0.92  fof(f114,plain,(
% 3.26/0.92    k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5))),
% 3.26/0.92    inference(definition_unfolding,[],[f80,f86,f87])).
% 3.26/0.92  
% 3.26/0.92  fof(f10,axiom,(
% 3.26/0.92    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.26/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.92  
% 3.26/0.92  fof(f62,plain,(
% 3.26/0.92    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.26/0.92    inference(cnf_transformation,[],[f10])).
% 3.26/0.92  
% 3.26/0.92  fof(f98,plain,(
% 3.26/0.92    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 3.26/0.92    inference(definition_unfolding,[],[f62,f86])).
% 3.26/0.92  
% 3.26/0.92  fof(f16,axiom,(
% 3.26/0.92    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.26/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.92  
% 3.26/0.92  fof(f39,plain,(
% 3.26/0.92    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.26/0.92    inference(nnf_transformation,[],[f16])).
% 3.26/0.92  
% 3.26/0.92  fof(f40,plain,(
% 3.26/0.92    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.26/0.92    inference(flattening,[],[f39])).
% 3.26/0.92  
% 3.26/0.92  fof(f71,plain,(
% 3.26/0.92    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.26/0.92    inference(cnf_transformation,[],[f40])).
% 3.26/0.92  
% 3.26/0.92  fof(f105,plain,(
% 3.26/0.92    ( ! [X0,X1] : (k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))) )),
% 3.26/0.92    inference(definition_unfolding,[],[f71,f87,f87])).
% 3.26/0.92  
% 3.26/0.92  fof(f81,plain,(
% 3.26/0.92    k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4),
% 3.26/0.92    inference(cnf_transformation,[],[f45])).
% 3.26/0.92  
% 3.26/0.92  fof(f113,plain,(
% 3.26/0.92    k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4),
% 3.26/0.92    inference(definition_unfolding,[],[f81,f87,f87])).
% 3.26/0.92  
% 3.26/0.92  fof(f82,plain,(
% 3.26/0.92    k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4),
% 3.26/0.92    inference(cnf_transformation,[],[f45])).
% 3.26/0.92  
% 3.26/0.92  fof(f112,plain,(
% 3.26/0.92    k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 | k1_xboole_0 != sK4),
% 3.26/0.92    inference(definition_unfolding,[],[f82,f87])).
% 3.26/0.92  
% 3.26/0.92  fof(f11,axiom,(
% 3.26/0.92    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.26/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.92  
% 3.26/0.92  fof(f35,plain,(
% 3.26/0.92    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.26/0.92    inference(nnf_transformation,[],[f11])).
% 3.26/0.92  
% 3.26/0.92  fof(f36,plain,(
% 3.26/0.92    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.26/0.92    inference(rectify,[],[f35])).
% 3.26/0.92  
% 3.26/0.92  fof(f37,plain,(
% 3.26/0.92    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 3.26/0.92    introduced(choice_axiom,[])).
% 3.26/0.92  
% 3.26/0.92  fof(f38,plain,(
% 3.26/0.92    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.26/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 3.26/0.92  
% 3.26/0.92  fof(f64,plain,(
% 3.26/0.92    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.26/0.92    inference(cnf_transformation,[],[f38])).
% 3.26/0.92  
% 3.26/0.92  fof(f101,plain,(
% 3.26/0.92    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 3.26/0.92    inference(definition_unfolding,[],[f64,f87])).
% 3.26/0.92  
% 3.26/0.92  fof(f120,plain,(
% 3.26/0.92    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 3.26/0.92    inference(equality_resolution,[],[f101])).
% 3.26/0.92  
% 3.26/0.92  fof(f121,plain,(
% 3.26/0.92    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 3.26/0.92    inference(equality_resolution,[],[f120])).
% 3.26/0.92  
% 3.26/0.92  fof(f1,axiom,(
% 3.26/0.92    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.26/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.92  
% 3.26/0.92  fof(f26,plain,(
% 3.26/0.92    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.26/0.92    inference(nnf_transformation,[],[f1])).
% 3.26/0.92  
% 3.26/0.92  fof(f27,plain,(
% 3.26/0.92    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.26/0.92    inference(flattening,[],[f26])).
% 3.26/0.92  
% 3.26/0.92  fof(f28,plain,(
% 3.26/0.92    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.26/0.92    inference(rectify,[],[f27])).
% 3.26/0.92  
% 3.26/0.92  fof(f29,plain,(
% 3.26/0.92    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.26/0.92    introduced(choice_axiom,[])).
% 3.26/0.92  
% 3.26/0.92  fof(f30,plain,(
% 3.26/0.92    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.26/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.26/0.92  
% 3.26/0.92  fof(f46,plain,(
% 3.26/0.92    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.26/0.92    inference(cnf_transformation,[],[f30])).
% 3.26/0.92  
% 3.26/0.92  fof(f94,plain,(
% 3.26/0.92    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 3.26/0.92    inference(definition_unfolding,[],[f46,f86])).
% 3.26/0.92  
% 3.26/0.92  fof(f117,plain,(
% 3.26/0.92    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 3.26/0.92    inference(equality_resolution,[],[f94])).
% 3.26/0.92  
% 3.26/0.92  fof(f83,plain,(
% 3.26/0.92    k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4),
% 3.26/0.92    inference(cnf_transformation,[],[f45])).
% 3.26/0.92  
% 3.26/0.92  fof(f111,plain,(
% 3.26/0.92    k1_xboole_0 != sK5 | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4),
% 3.26/0.92    inference(definition_unfolding,[],[f83,f87])).
% 3.26/0.92  
% 3.26/0.92  fof(f19,axiom,(
% 3.26/0.92    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.26/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.92  
% 3.26/0.92  fof(f42,plain,(
% 3.26/0.92    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.26/0.92    inference(nnf_transformation,[],[f19])).
% 3.26/0.92  
% 3.26/0.92  fof(f43,plain,(
% 3.26/0.92    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.26/0.92    inference(flattening,[],[f42])).
% 3.26/0.92  
% 3.26/0.92  fof(f79,plain,(
% 3.26/0.92    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.26/0.92    inference(cnf_transformation,[],[f43])).
% 3.26/0.92  
% 3.26/0.92  fof(f108,plain,(
% 3.26/0.92    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.26/0.92    inference(definition_unfolding,[],[f79,f85])).
% 3.26/0.92  
% 3.26/0.92  fof(f3,axiom,(
% 3.26/0.92    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.26/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.92  
% 3.26/0.92  fof(f33,plain,(
% 3.26/0.92    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.26/0.92    inference(nnf_transformation,[],[f3])).
% 3.26/0.92  
% 3.26/0.92  fof(f34,plain,(
% 3.26/0.92    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.26/0.92    inference(flattening,[],[f33])).
% 3.26/0.92  
% 3.26/0.92  fof(f55,plain,(
% 3.26/0.92    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.26/0.92    inference(cnf_transformation,[],[f34])).
% 3.26/0.92  
% 3.26/0.92  fof(f2,axiom,(
% 3.26/0.92    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.26/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.92  
% 3.26/0.92  fof(f22,plain,(
% 3.26/0.92    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.26/0.92    inference(ennf_transformation,[],[f2])).
% 3.26/0.92  
% 3.26/0.92  fof(f31,plain,(
% 3.26/0.92    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.26/0.92    introduced(choice_axiom,[])).
% 3.26/0.92  
% 3.26/0.92  fof(f32,plain,(
% 3.26/0.92    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 3.26/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f31])).
% 3.26/0.92  
% 3.26/0.92  fof(f52,plain,(
% 3.26/0.92    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.26/0.92    inference(cnf_transformation,[],[f32])).
% 3.26/0.92  
% 3.26/0.92  fof(f48,plain,(
% 3.26/0.92    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.26/0.92    inference(cnf_transformation,[],[f30])).
% 3.26/0.92  
% 3.26/0.92  fof(f92,plain,(
% 3.26/0.92    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 3.26/0.92    inference(definition_unfolding,[],[f48,f86])).
% 3.26/0.92  
% 3.26/0.92  fof(f115,plain,(
% 3.26/0.92    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 3.26/0.92    inference(equality_resolution,[],[f92])).
% 3.26/0.92  
% 3.26/0.92  fof(f63,plain,(
% 3.26/0.92    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.26/0.92    inference(cnf_transformation,[],[f38])).
% 3.26/0.92  
% 3.26/0.92  fof(f102,plain,(
% 3.26/0.92    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 3.26/0.92    inference(definition_unfolding,[],[f63,f87])).
% 3.26/0.92  
% 3.26/0.92  fof(f122,plain,(
% 3.26/0.92    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 3.26/0.92    inference(equality_resolution,[],[f102])).
% 3.26/0.92  
% 3.26/0.92  fof(f6,axiom,(
% 3.26/0.92    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.26/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.92  
% 3.26/0.92  fof(f24,plain,(
% 3.26/0.92    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.26/0.92    inference(ennf_transformation,[],[f6])).
% 3.26/0.92  
% 3.26/0.92  fof(f58,plain,(
% 3.26/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.26/0.92    inference(cnf_transformation,[],[f24])).
% 3.26/0.92  
% 3.26/0.92  fof(f96,plain,(
% 3.26/0.92    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.26/0.92    inference(definition_unfolding,[],[f58,f86])).
% 3.26/0.92  
% 3.26/0.92  fof(f5,axiom,(
% 3.26/0.92    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 3.26/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.92  
% 3.26/0.92  fof(f23,plain,(
% 3.26/0.92    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 3.26/0.92    inference(ennf_transformation,[],[f5])).
% 3.26/0.92  
% 3.26/0.92  fof(f57,plain,(
% 3.26/0.92    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 3.26/0.92    inference(cnf_transformation,[],[f23])).
% 3.26/0.92  
% 3.26/0.92  fof(f95,plain,(
% 3.26/0.92    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X2)) )),
% 3.26/0.92    inference(definition_unfolding,[],[f57,f86])).
% 3.26/0.92  
% 3.26/0.92  fof(f53,plain,(
% 3.26/0.92    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.26/0.92    inference(cnf_transformation,[],[f34])).
% 3.26/0.92  
% 3.26/0.92  fof(f119,plain,(
% 3.26/0.92    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.26/0.92    inference(equality_resolution,[],[f53])).
% 3.26/0.92  
% 3.26/0.92  cnf(c_423,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_1502,plain,
% 3.26/0.92      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 3.26/0.92      inference(instantiation,[status(thm)],[c_423]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_3043,plain,
% 3.26/0.92      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 3.26/0.92      inference(instantiation,[status(thm)],[c_1502]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_9757,plain,
% 3.26/0.92      ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) != sK5
% 3.26/0.92      | sK5 = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5))
% 3.26/0.92      | sK5 != sK5 ),
% 3.26/0.92      inference(instantiation,[status(thm)],[c_3043]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_31,negated_conjecture,
% 3.26/0.92      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
% 3.26/0.92      inference(cnf_transformation,[],[f114]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_15,plain,
% 3.26/0.92      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
% 3.26/0.92      inference(cnf_transformation,[],[f98]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_798,plain,
% 3.26/0.92      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
% 3.26/0.92      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_1538,plain,
% 3.26/0.92      ( r1_tarski(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 3.26/0.92      inference(superposition,[status(thm)],[c_31,c_798]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_22,plain,
% 3.26/0.92      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
% 3.26/0.92      | k3_enumset1(X1,X1,X1,X1,X1) = X0
% 3.26/0.92      | k1_xboole_0 = X0 ),
% 3.26/0.92      inference(cnf_transformation,[],[f105]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_791,plain,
% 3.26/0.92      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 3.26/0.92      | k1_xboole_0 = X1
% 3.26/0.92      | r1_tarski(X1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 3.26/0.92      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_3648,plain,
% 3.26/0.92      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4 | sK4 = k1_xboole_0 ),
% 3.26/0.92      inference(superposition,[status(thm)],[c_1538,c_791]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_30,negated_conjecture,
% 3.26/0.92      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4
% 3.26/0.92      | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 ),
% 3.26/0.92      inference(cnf_transformation,[],[f113]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_4137,plain,
% 3.26/0.92      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 | sK4 = k1_xboole_0 ),
% 3.26/0.92      inference(superposition,[status(thm)],[c_3648,c_30]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_29,negated_conjecture,
% 3.26/0.92      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 | k1_xboole_0 != sK4 ),
% 3.26/0.92      inference(cnf_transformation,[],[f112]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_1082,plain,
% 3.26/0.92      ( ~ r1_tarski(sK4,k3_enumset1(X0,X0,X0,X0,X0))
% 3.26/0.92      | k3_enumset1(X0,X0,X0,X0,X0) = sK4
% 3.26/0.92      | k1_xboole_0 = sK4 ),
% 3.26/0.92      inference(instantiation,[status(thm)],[c_22]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_1084,plain,
% 3.26/0.92      ( ~ r1_tarski(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 3.26/0.92      | k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4
% 3.26/0.92      | k1_xboole_0 = sK4 ),
% 3.26/0.92      inference(instantiation,[status(thm)],[c_1082]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_1544,plain,
% 3.26/0.92      ( r1_tarski(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 3.26/0.92      inference(predicate_to_equality_rev,[status(thm)],[c_1538]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_4363,plain,
% 3.26/0.92      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 ),
% 3.26/0.92      inference(global_propositional_subsumption,
% 3.26/0.92                [status(thm)],
% 3.26/0.92                [c_4137,c_30,c_29,c_1084,c_1544]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_18,plain,
% 3.26/0.92      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
% 3.26/0.92      inference(cnf_transformation,[],[f121]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_795,plain,
% 3.26/0.92      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
% 3.26/0.92      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_6,plain,
% 3.26/0.92      ( r2_hidden(X0,X1)
% 3.26/0.92      | r2_hidden(X0,X2)
% 3.26/0.92      | ~ r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
% 3.26/0.92      inference(cnf_transformation,[],[f117]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_804,plain,
% 3.26/0.92      ( r2_hidden(X0,X1) = iProver_top
% 3.26/0.92      | r2_hidden(X0,X2) = iProver_top
% 3.26/0.92      | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) != iProver_top ),
% 3.26/0.92      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_3919,plain,
% 3.26/0.92      ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top
% 3.26/0.92      | r2_hidden(X0,sK4) = iProver_top
% 3.26/0.92      | r2_hidden(X0,sK5) = iProver_top ),
% 3.26/0.92      inference(superposition,[status(thm)],[c_31,c_804]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_3957,plain,
% 3.26/0.92      ( r2_hidden(sK3,sK4) = iProver_top
% 3.26/0.92      | r2_hidden(sK3,sK5) = iProver_top ),
% 3.26/0.92      inference(superposition,[status(thm)],[c_795,c_3919]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_28,negated_conjecture,
% 3.26/0.92      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4 | k1_xboole_0 != sK5 ),
% 3.26/0.92      inference(cnf_transformation,[],[f111]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_53,plain,
% 3.26/0.92      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
% 3.26/0.92      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_55,plain,
% 3.26/0.92      ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 3.26/0.92      inference(instantiation,[status(thm)],[c_53]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_998,plain,
% 3.26/0.92      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 3.26/0.92      inference(instantiation,[status(thm)],[c_423]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_1584,plain,
% 3.26/0.92      ( sK5 != k1_xboole_0
% 3.26/0.92      | k1_xboole_0 = sK5
% 3.26/0.92      | k1_xboole_0 != k1_xboole_0 ),
% 3.26/0.92      inference(instantiation,[status(thm)],[c_998]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_422,plain,( X0 = X0 ),theory(equality) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_1585,plain,
% 3.26/0.92      ( k1_xboole_0 = k1_xboole_0 ),
% 3.26/0.92      inference(instantiation,[status(thm)],[c_422]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_25,plain,
% 3.26/0.92      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
% 3.26/0.92      | ~ r2_hidden(X1,X2)
% 3.26/0.92      | ~ r2_hidden(X0,X2) ),
% 3.26/0.92      inference(cnf_transformation,[],[f108]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_790,plain,
% 3.26/0.92      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) = iProver_top
% 3.26/0.92      | r2_hidden(X0,X2) != iProver_top
% 3.26/0.92      | r2_hidden(X1,X2) != iProver_top ),
% 3.26/0.92      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_8,plain,
% 3.26/0.92      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.26/0.92      inference(cnf_transformation,[],[f55]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_802,plain,
% 3.26/0.92      ( X0 = X1
% 3.26/0.92      | r1_tarski(X0,X1) != iProver_top
% 3.26/0.92      | r1_tarski(X1,X0) != iProver_top ),
% 3.26/0.92      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_2171,plain,
% 3.26/0.92      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4
% 3.26/0.92      | r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) != iProver_top ),
% 3.26/0.92      inference(superposition,[status(thm)],[c_1538,c_802]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_2664,plain,
% 3.26/0.92      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4
% 3.26/0.92      | r2_hidden(sK3,sK4) != iProver_top ),
% 3.26/0.92      inference(superposition,[status(thm)],[c_790,c_2171]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_7,plain,
% 3.26/0.92      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.26/0.92      inference(cnf_transformation,[],[f52]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_803,plain,
% 3.26/0.92      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.26/0.92      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_4,plain,
% 3.26/0.92      ( ~ r2_hidden(X0,X1)
% 3.26/0.92      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
% 3.26/0.92      inference(cnf_transformation,[],[f115]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_806,plain,
% 3.26/0.92      ( r2_hidden(X0,X1) != iProver_top
% 3.26/0.92      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = iProver_top ),
% 3.26/0.92      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_2747,plain,
% 3.26/0.92      ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
% 3.26/0.92      | r2_hidden(X0,sK5) != iProver_top ),
% 3.26/0.92      inference(superposition,[status(thm)],[c_31,c_806]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_19,plain,
% 3.26/0.92      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1 ),
% 3.26/0.92      inference(cnf_transformation,[],[f122]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_794,plain,
% 3.26/0.92      ( X0 = X1
% 3.26/0.92      | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
% 3.26/0.92      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_2758,plain,
% 3.26/0.92      ( sK3 = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 3.26/0.92      inference(superposition,[status(thm)],[c_2747,c_794]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_2860,plain,
% 3.26/0.92      ( sK1(sK5) = sK3 | sK5 = k1_xboole_0 ),
% 3.26/0.92      inference(superposition,[status(thm)],[c_803,c_2758]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_3106,plain,
% 3.26/0.92      ( sK5 = k1_xboole_0 | r2_hidden(sK3,sK5) = iProver_top ),
% 3.26/0.92      inference(superposition,[status(thm)],[c_2860,c_803]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_3949,plain,
% 3.26/0.92      ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top
% 3.26/0.92      | r2_hidden(sK3,sK4) = iProver_top
% 3.26/0.92      | r2_hidden(sK3,sK5) = iProver_top ),
% 3.26/0.92      inference(instantiation,[status(thm)],[c_3919]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_4096,plain,
% 3.26/0.92      ( r2_hidden(sK3,sK5) = iProver_top ),
% 3.26/0.92      inference(global_propositional_subsumption,
% 3.26/0.92                [status(thm)],
% 3.26/0.92                [c_3957,c_28,c_55,c_1584,c_1585,c_2664,c_3106,c_3949]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_12,plain,
% 3.26/0.92      ( ~ r1_tarski(X0,X1)
% 3.26/0.92      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 ),
% 3.26/0.92      inference(cnf_transformation,[],[f96]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_799,plain,
% 3.26/0.92      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1
% 3.26/0.92      | r1_tarski(X0,X1) != iProver_top ),
% 3.26/0.92      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_1898,plain,
% 3.26/0.92      ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 3.26/0.92      inference(superposition,[status(thm)],[c_1538,c_799]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_11,plain,
% 3.26/0.92      ( r1_tarski(X0,X1)
% 3.26/0.92      | ~ r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) ),
% 3.26/0.92      inference(cnf_transformation,[],[f95]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_800,plain,
% 3.26/0.92      ( r1_tarski(X0,X1) = iProver_top
% 3.26/0.92      | r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) != iProver_top ),
% 3.26/0.92      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_2380,plain,
% 3.26/0.92      ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0) != iProver_top
% 3.26/0.92      | r1_tarski(sK4,X0) = iProver_top ),
% 3.26/0.92      inference(superposition,[status(thm)],[c_1898,c_800]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_3009,plain,
% 3.26/0.92      ( r1_tarski(sK4,X0) = iProver_top
% 3.26/0.92      | r2_hidden(sK3,X0) != iProver_top ),
% 3.26/0.92      inference(superposition,[status(thm)],[c_790,c_2380]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_4102,plain,
% 3.26/0.92      ( r1_tarski(sK4,sK5) = iProver_top ),
% 3.26/0.92      inference(superposition,[status(thm)],[c_4096,c_3009]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_10,plain,
% 3.26/0.92      ( r1_tarski(X0,X0) ),
% 3.26/0.92      inference(cnf_transformation,[],[f119]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_2980,plain,
% 3.26/0.92      ( r1_tarski(sK5,sK5) ),
% 3.26/0.92      inference(instantiation,[status(thm)],[c_10]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_1491,plain,
% 3.26/0.92      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 3.26/0.92      inference(instantiation,[status(thm)],[c_8]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_2979,plain,
% 3.26/0.92      ( ~ r1_tarski(sK5,sK5) | sK5 = sK5 ),
% 3.26/0.92      inference(instantiation,[status(thm)],[c_1491]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_1168,plain,
% 3.26/0.92      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != X0
% 3.26/0.92      | k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK5
% 3.26/0.92      | sK5 != X0 ),
% 3.26/0.92      inference(instantiation,[status(thm)],[c_423]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_1857,plain,
% 3.26/0.92      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5))
% 3.26/0.92      | k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK5
% 3.26/0.92      | sK5 != k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
% 3.26/0.92      inference(instantiation,[status(thm)],[c_1168]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_1800,plain,
% 3.26/0.92      ( ~ r1_tarski(sK4,sK5)
% 3.26/0.92      | k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) = sK5 ),
% 3.26/0.92      inference(instantiation,[status(thm)],[c_12]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(c_1801,plain,
% 3.26/0.92      ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) = sK5
% 3.26/0.92      | r1_tarski(sK4,sK5) != iProver_top ),
% 3.26/0.92      inference(predicate_to_equality,[status(thm)],[c_1800]) ).
% 3.26/0.92  
% 3.26/0.92  cnf(contradiction,plain,
% 3.26/0.92      ( $false ),
% 3.26/0.92      inference(minisat,
% 3.26/0.92                [status(thm)],
% 3.26/0.92                [c_9757,c_4363,c_4102,c_2980,c_2979,c_1857,c_1801,c_31]) ).
% 3.26/0.92  
% 3.26/0.92  
% 3.26/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 3.26/0.92  
% 3.26/0.92  ------                               Statistics
% 3.26/0.92  
% 3.26/0.92  ------ General
% 3.26/0.92  
% 3.26/0.92  abstr_ref_over_cycles:                  0
% 3.26/0.92  abstr_ref_under_cycles:                 0
% 3.26/0.92  gc_basic_clause_elim:                   0
% 3.26/0.92  forced_gc_time:                         0
% 3.26/0.92  parsing_time:                           0.013
% 3.26/0.92  unif_index_cands_time:                  0.
% 3.26/0.92  unif_index_add_time:                    0.
% 3.26/0.92  orderings_time:                         0.
% 3.26/0.92  out_proof_time:                         0.01
% 3.26/0.92  total_time:                             0.355
% 3.26/0.92  num_of_symbols:                         44
% 3.26/0.92  num_of_terms:                           10193
% 3.26/0.92  
% 3.26/0.92  ------ Preprocessing
% 3.26/0.92  
% 3.26/0.92  num_of_splits:                          0
% 3.26/0.92  num_of_split_atoms:                     0
% 3.26/0.92  num_of_reused_defs:                     0
% 3.26/0.92  num_eq_ax_congr_red:                    18
% 3.26/0.92  num_of_sem_filtered_clauses:            1
% 3.26/0.92  num_of_subtypes:                        0
% 3.26/0.92  monotx_restored_types:                  0
% 3.26/0.92  sat_num_of_epr_types:                   0
% 3.26/0.92  sat_num_of_non_cyclic_types:            0
% 3.26/0.92  sat_guarded_non_collapsed_types:        0
% 3.26/0.92  num_pure_diseq_elim:                    0
% 3.26/0.92  simp_replaced_by:                       0
% 3.26/0.92  res_preprocessed:                       141
% 3.26/0.92  prep_upred:                             0
% 3.26/0.92  prep_unflattend:                        0
% 3.26/0.92  smt_new_axioms:                         0
% 3.26/0.92  pred_elim_cands:                        2
% 3.26/0.92  pred_elim:                              0
% 3.26/0.92  pred_elim_cl:                           0
% 3.26/0.92  pred_elim_cycles:                       2
% 3.26/0.92  merged_defs:                            0
% 3.26/0.92  merged_defs_ncl:                        0
% 3.26/0.92  bin_hyper_res:                          0
% 3.26/0.92  prep_cycles:                            4
% 3.26/0.92  pred_elim_time:                         0.
% 3.26/0.92  splitting_time:                         0.
% 3.26/0.92  sem_filter_time:                        0.
% 3.26/0.92  monotx_time:                            0.
% 3.26/0.92  subtype_inf_time:                       0.
% 3.26/0.92  
% 3.26/0.92  ------ Problem properties
% 3.26/0.92  
% 3.26/0.92  clauses:                                31
% 3.26/0.92  conjectures:                            4
% 3.26/0.92  epr:                                    2
% 3.26/0.92  horn:                                   25
% 3.26/0.92  ground:                                 4
% 3.26/0.92  unary:                                  10
% 3.26/0.92  binary:                                 12
% 3.26/0.92  lits:                                   62
% 3.26/0.92  lits_eq:                                26
% 3.26/0.92  fd_pure:                                0
% 3.26/0.92  fd_pseudo:                              0
% 3.26/0.92  fd_cond:                                1
% 3.26/0.92  fd_pseudo_cond:                         8
% 3.26/0.92  ac_symbols:                             0
% 3.26/0.92  
% 3.26/0.92  ------ Propositional Solver
% 3.26/0.92  
% 3.26/0.92  prop_solver_calls:                      27
% 3.26/0.92  prop_fast_solver_calls:                 801
% 3.26/0.92  smt_solver_calls:                       0
% 3.26/0.92  smt_fast_solver_calls:                  0
% 3.26/0.92  prop_num_of_clauses:                    3664
% 3.26/0.92  prop_preprocess_simplified:             8949
% 3.26/0.92  prop_fo_subsumed:                       4
% 3.26/0.92  prop_solver_time:                       0.
% 3.26/0.92  smt_solver_time:                        0.
% 3.26/0.92  smt_fast_solver_time:                   0.
% 3.26/0.92  prop_fast_solver_time:                  0.
% 3.26/0.92  prop_unsat_core_time:                   0.
% 3.26/0.92  
% 3.26/0.92  ------ QBF
% 3.26/0.92  
% 3.26/0.92  qbf_q_res:                              0
% 3.26/0.92  qbf_num_tautologies:                    0
% 3.26/0.92  qbf_prep_cycles:                        0
% 3.26/0.92  
% 3.26/0.92  ------ BMC1
% 3.26/0.92  
% 3.26/0.92  bmc1_current_bound:                     -1
% 3.26/0.92  bmc1_last_solved_bound:                 -1
% 3.26/0.92  bmc1_unsat_core_size:                   -1
% 3.26/0.92  bmc1_unsat_core_parents_size:           -1
% 3.26/0.92  bmc1_merge_next_fun:                    0
% 3.26/0.92  bmc1_unsat_core_clauses_time:           0.
% 3.26/0.92  
% 3.26/0.92  ------ Instantiation
% 3.26/0.92  
% 3.26/0.92  inst_num_of_clauses:                    971
% 3.26/0.92  inst_num_in_passive:                    341
% 3.26/0.92  inst_num_in_active:                     318
% 3.26/0.92  inst_num_in_unprocessed:                314
% 3.26/0.92  inst_num_of_loops:                      434
% 3.26/0.92  inst_num_of_learning_restarts:          0
% 3.26/0.92  inst_num_moves_active_passive:          112
% 3.26/0.92  inst_lit_activity:                      0
% 3.26/0.92  inst_lit_activity_moves:                0
% 3.26/0.92  inst_num_tautologies:                   0
% 3.26/0.92  inst_num_prop_implied:                  0
% 3.26/0.92  inst_num_existing_simplified:           0
% 3.26/0.92  inst_num_eq_res_simplified:             0
% 3.26/0.92  inst_num_child_elim:                    0
% 3.26/0.92  inst_num_of_dismatching_blockings:      662
% 3.26/0.92  inst_num_of_non_proper_insts:           1035
% 3.26/0.92  inst_num_of_duplicates:                 0
% 3.26/0.92  inst_inst_num_from_inst_to_res:         0
% 3.26/0.92  inst_dismatching_checking_time:         0.
% 3.26/0.92  
% 3.26/0.92  ------ Resolution
% 3.26/0.92  
% 3.26/0.92  res_num_of_clauses:                     0
% 3.26/0.92  res_num_in_passive:                     0
% 3.26/0.92  res_num_in_active:                      0
% 3.26/0.92  res_num_of_loops:                       145
% 3.26/0.92  res_forward_subset_subsumed:            120
% 3.26/0.92  res_backward_subset_subsumed:           14
% 3.26/0.92  res_forward_subsumed:                   0
% 3.26/0.92  res_backward_subsumed:                  0
% 3.26/0.92  res_forward_subsumption_resolution:     0
% 3.26/0.92  res_backward_subsumption_resolution:    0
% 3.26/0.92  res_clause_to_clause_subsumption:       1946
% 3.26/0.92  res_orphan_elimination:                 0
% 3.26/0.92  res_tautology_del:                      24
% 3.26/0.92  res_num_eq_res_simplified:              0
% 3.26/0.92  res_num_sel_changes:                    0
% 3.26/0.92  res_moves_from_active_to_pass:          0
% 3.26/0.92  
% 3.26/0.92  ------ Superposition
% 3.26/0.92  
% 3.26/0.92  sup_time_total:                         0.
% 3.26/0.92  sup_time_generating:                    0.
% 3.26/0.92  sup_time_sim_full:                      0.
% 3.26/0.92  sup_time_sim_immed:                     0.
% 3.26/0.92  
% 3.26/0.92  sup_num_of_clauses:                     274
% 3.26/0.92  sup_num_in_active:                      83
% 3.26/0.92  sup_num_in_passive:                     191
% 3.26/0.92  sup_num_of_loops:                       86
% 3.26/0.92  sup_fw_superposition:                   255
% 3.26/0.92  sup_bw_superposition:                   230
% 3.26/0.92  sup_immediate_simplified:               142
% 3.26/0.92  sup_given_eliminated:                   1
% 3.26/0.92  comparisons_done:                       0
% 3.26/0.92  comparisons_avoided:                    40
% 3.26/0.92  
% 3.26/0.92  ------ Simplifications
% 3.26/0.92  
% 3.26/0.92  
% 3.26/0.92  sim_fw_subset_subsumed:                 24
% 3.26/0.92  sim_bw_subset_subsumed:                 1
% 3.26/0.92  sim_fw_subsumed:                        32
% 3.26/0.92  sim_bw_subsumed:                        0
% 3.26/0.92  sim_fw_subsumption_res:                 11
% 3.26/0.92  sim_bw_subsumption_res:                 0
% 3.26/0.92  sim_tautology_del:                      62
% 3.26/0.92  sim_eq_tautology_del:                   40
% 3.26/0.92  sim_eq_res_simp:                        26
% 3.26/0.92  sim_fw_demodulated:                     73
% 3.26/0.92  sim_bw_demodulated:                     2
% 3.26/0.92  sim_light_normalised:                   24
% 3.26/0.92  sim_joinable_taut:                      0
% 3.26/0.92  sim_joinable_simp:                      0
% 3.26/0.92  sim_ac_normalised:                      0
% 3.26/0.92  sim_smt_subsumption:                    0
% 3.26/0.92  
%------------------------------------------------------------------------------
