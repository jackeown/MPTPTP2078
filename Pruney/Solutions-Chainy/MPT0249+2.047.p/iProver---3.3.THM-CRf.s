%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:38 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  118 (2413 expanded)
%              Number of clauses        :   51 ( 247 expanded)
%              Number of leaves         :   20 ( 748 expanded)
%              Depth                    :   28
%              Number of atoms          :  336 (4443 expanded)
%              Number of equality atoms :  201 (3367 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f26])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & sK4 != sK5
      & k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & sK4 != sK5
    & k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f20,f35])).

fof(f63,plain,(
    k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f62,f71])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f67])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f53,f68])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f69])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f70])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f71])).

fof(f91,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
    inference(definition_unfolding,[],[f63,f72,f73])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f81,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f45,f72])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f33])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f59,f73,f73])).

fof(f65,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f39,f72])).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f77])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f46,f73])).

fof(f97,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f85])).

fof(f64,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f36])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f40,f72])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f42,f72])).

fof(f66,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_796,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_21,negated_conjecture,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_8,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_794,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1106,plain,
    ( r1_tarski(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_794])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_785,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1186,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1106,c_785])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_363,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_930,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_363])).

cnf(c_1026,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_930])).

cnf(c_362,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1027,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_362])).

cnf(c_1738,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1186,c_19,c_1026,c_1027])).

cnf(c_1743,plain,
    ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK4 ),
    inference(demodulation,[status(thm)],[c_1738,c_21])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_799,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2530,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1743,c_799])).

cnf(c_2716,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK1(sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_796,c_2530])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_790,plain,
    ( X0 = X1
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1756,plain,
    ( sK3 = X0
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1738,c_790])).

cnf(c_2948,plain,
    ( sK1(sK5) = sK3
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2716,c_1756])).

cnf(c_8668,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2948,c_796])).

cnf(c_20,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_800,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3706,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = sK5
    | r2_hidden(sK0(X0,X1,sK5),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,sK5),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_800,c_2530])).

cnf(c_4973,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) = sK5
    | r2_hidden(sK0(X0,sK5,sK5),X0) = iProver_top
    | r2_hidden(sK0(X0,sK5,sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3706,c_2530])).

cnf(c_1525,plain,
    ( r2_hidden(sK0(X0,X1,sK5),X1)
    | r2_hidden(sK0(X0,X1,sK5),X0)
    | r2_hidden(sK0(X0,X1,sK5),sK5)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = sK5 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3144,plain,
    ( r2_hidden(sK0(X0,sK5,sK5),X0)
    | r2_hidden(sK0(X0,sK5,sK5),sK5)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_1525])).

cnf(c_3147,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) = sK5
    | r2_hidden(sK0(X0,sK5,sK5),X0) = iProver_top
    | r2_hidden(sK0(X0,sK5,sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3144])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1527,plain,
    ( ~ r2_hidden(sK0(X0,X1,sK5),X1)
    | ~ r2_hidden(sK0(X0,X1,sK5),sK5)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = sK5 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3145,plain,
    ( ~ r2_hidden(sK0(X0,sK5,sK5),sK5)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_1527])).

cnf(c_3155,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) = sK5
    | r2_hidden(sK0(X0,sK5,sK5),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3145])).

cnf(c_5100,plain,
    ( r2_hidden(sK0(X0,sK5,sK5),X0) = iProver_top
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4973,c_3147,c_3155])).

cnf(c_5101,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) = sK5
    | r2_hidden(sK0(X0,sK5,sK5),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_5100])).

cnf(c_5110,plain,
    ( sK0(sK4,sK5,sK5) = sK3
    | k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_5101,c_1756])).

cnf(c_5119,plain,
    ( sK0(sK4,sK5,sK5) = sK3
    | sK4 = sK5 ),
    inference(demodulation,[status(thm)],[c_5110,c_1743])).

cnf(c_5216,plain,
    ( sK0(sK4,sK5,sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5119,c_20])).

cnf(c_802,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5222,plain,
    ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK5
    | r2_hidden(sK0(sK4,sK5,sK5),sK5) != iProver_top
    | r2_hidden(sK3,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5216,c_802])).

cnf(c_5244,plain,
    ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK5
    | r2_hidden(sK3,sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5222,c_5216])).

cnf(c_5245,plain,
    ( sK4 = sK5
    | r2_hidden(sK3,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5244,c_1743])).

cnf(c_9390,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8668,c_20,c_5245])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_9418,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9390,c_18])).

cnf(c_9419,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_9418])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:35:20 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.23/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.23/1.00  
% 3.23/1.00  ------  iProver source info
% 3.23/1.00  
% 3.23/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.23/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.23/1.00  git: non_committed_changes: false
% 3.23/1.00  git: last_make_outside_of_git: false
% 3.23/1.00  
% 3.23/1.00  ------ 
% 3.23/1.00  
% 3.23/1.00  ------ Input Options
% 3.23/1.00  
% 3.23/1.00  --out_options                           all
% 3.23/1.00  --tptp_safe_out                         true
% 3.23/1.00  --problem_path                          ""
% 3.23/1.00  --include_path                          ""
% 3.23/1.00  --clausifier                            res/vclausify_rel
% 3.23/1.00  --clausifier_options                    --mode clausify
% 3.23/1.00  --stdin                                 false
% 3.23/1.00  --stats_out                             all
% 3.23/1.00  
% 3.23/1.00  ------ General Options
% 3.23/1.00  
% 3.23/1.00  --fof                                   false
% 3.23/1.00  --time_out_real                         305.
% 3.23/1.00  --time_out_virtual                      -1.
% 3.23/1.00  --symbol_type_check                     false
% 3.23/1.00  --clausify_out                          false
% 3.23/1.00  --sig_cnt_out                           false
% 3.23/1.00  --trig_cnt_out                          false
% 3.23/1.00  --trig_cnt_out_tolerance                1.
% 3.23/1.00  --trig_cnt_out_sk_spl                   false
% 3.23/1.00  --abstr_cl_out                          false
% 3.23/1.00  
% 3.23/1.00  ------ Global Options
% 3.23/1.00  
% 3.23/1.00  --schedule                              default
% 3.23/1.00  --add_important_lit                     false
% 3.23/1.00  --prop_solver_per_cl                    1000
% 3.23/1.00  --min_unsat_core                        false
% 3.23/1.00  --soft_assumptions                      false
% 3.23/1.00  --soft_lemma_size                       3
% 3.23/1.00  --prop_impl_unit_size                   0
% 3.23/1.00  --prop_impl_unit                        []
% 3.23/1.00  --share_sel_clauses                     true
% 3.23/1.00  --reset_solvers                         false
% 3.23/1.00  --bc_imp_inh                            [conj_cone]
% 3.23/1.00  --conj_cone_tolerance                   3.
% 3.23/1.00  --extra_neg_conj                        none
% 3.23/1.00  --large_theory_mode                     true
% 3.23/1.00  --prolific_symb_bound                   200
% 3.23/1.00  --lt_threshold                          2000
% 3.23/1.00  --clause_weak_htbl                      true
% 3.23/1.00  --gc_record_bc_elim                     false
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing Options
% 3.23/1.00  
% 3.23/1.00  --preprocessing_flag                    true
% 3.23/1.00  --time_out_prep_mult                    0.1
% 3.23/1.00  --splitting_mode                        input
% 3.23/1.00  --splitting_grd                         true
% 3.23/1.00  --splitting_cvd                         false
% 3.23/1.00  --splitting_cvd_svl                     false
% 3.23/1.00  --splitting_nvd                         32
% 3.23/1.00  --sub_typing                            true
% 3.23/1.00  --prep_gs_sim                           true
% 3.23/1.00  --prep_unflatten                        true
% 3.23/1.00  --prep_res_sim                          true
% 3.23/1.00  --prep_upred                            true
% 3.23/1.00  --prep_sem_filter                       exhaustive
% 3.23/1.00  --prep_sem_filter_out                   false
% 3.23/1.00  --pred_elim                             true
% 3.23/1.00  --res_sim_input                         true
% 3.23/1.00  --eq_ax_congr_red                       true
% 3.23/1.00  --pure_diseq_elim                       true
% 3.23/1.00  --brand_transform                       false
% 3.23/1.00  --non_eq_to_eq                          false
% 3.23/1.00  --prep_def_merge                        true
% 3.23/1.00  --prep_def_merge_prop_impl              false
% 3.23/1.00  --prep_def_merge_mbd                    true
% 3.23/1.00  --prep_def_merge_tr_red                 false
% 3.23/1.00  --prep_def_merge_tr_cl                  false
% 3.23/1.00  --smt_preprocessing                     true
% 3.23/1.00  --smt_ac_axioms                         fast
% 3.23/1.00  --preprocessed_out                      false
% 3.23/1.00  --preprocessed_stats                    false
% 3.23/1.00  
% 3.23/1.00  ------ Abstraction refinement Options
% 3.23/1.00  
% 3.23/1.00  --abstr_ref                             []
% 3.23/1.00  --abstr_ref_prep                        false
% 3.23/1.00  --abstr_ref_until_sat                   false
% 3.23/1.00  --abstr_ref_sig_restrict                funpre
% 3.23/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/1.00  --abstr_ref_under                       []
% 3.23/1.00  
% 3.23/1.00  ------ SAT Options
% 3.23/1.00  
% 3.23/1.00  --sat_mode                              false
% 3.23/1.00  --sat_fm_restart_options                ""
% 3.23/1.00  --sat_gr_def                            false
% 3.23/1.00  --sat_epr_types                         true
% 3.23/1.00  --sat_non_cyclic_types                  false
% 3.23/1.00  --sat_finite_models                     false
% 3.23/1.00  --sat_fm_lemmas                         false
% 3.23/1.00  --sat_fm_prep                           false
% 3.23/1.00  --sat_fm_uc_incr                        true
% 3.23/1.00  --sat_out_model                         small
% 3.23/1.00  --sat_out_clauses                       false
% 3.23/1.00  
% 3.23/1.00  ------ QBF Options
% 3.23/1.00  
% 3.23/1.00  --qbf_mode                              false
% 3.23/1.00  --qbf_elim_univ                         false
% 3.23/1.00  --qbf_dom_inst                          none
% 3.23/1.00  --qbf_dom_pre_inst                      false
% 3.23/1.00  --qbf_sk_in                             false
% 3.23/1.00  --qbf_pred_elim                         true
% 3.23/1.00  --qbf_split                             512
% 3.23/1.00  
% 3.23/1.00  ------ BMC1 Options
% 3.23/1.00  
% 3.23/1.00  --bmc1_incremental                      false
% 3.23/1.00  --bmc1_axioms                           reachable_all
% 3.23/1.00  --bmc1_min_bound                        0
% 3.23/1.00  --bmc1_max_bound                        -1
% 3.23/1.00  --bmc1_max_bound_default                -1
% 3.23/1.00  --bmc1_symbol_reachability              true
% 3.23/1.00  --bmc1_property_lemmas                  false
% 3.23/1.00  --bmc1_k_induction                      false
% 3.23/1.00  --bmc1_non_equiv_states                 false
% 3.23/1.00  --bmc1_deadlock                         false
% 3.23/1.00  --bmc1_ucm                              false
% 3.23/1.00  --bmc1_add_unsat_core                   none
% 3.23/1.00  --bmc1_unsat_core_children              false
% 3.23/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/1.00  --bmc1_out_stat                         full
% 3.23/1.00  --bmc1_ground_init                      false
% 3.23/1.00  --bmc1_pre_inst_next_state              false
% 3.23/1.00  --bmc1_pre_inst_state                   false
% 3.23/1.00  --bmc1_pre_inst_reach_state             false
% 3.23/1.00  --bmc1_out_unsat_core                   false
% 3.23/1.00  --bmc1_aig_witness_out                  false
% 3.23/1.00  --bmc1_verbose                          false
% 3.23/1.00  --bmc1_dump_clauses_tptp                false
% 3.23/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.23/1.00  --bmc1_dump_file                        -
% 3.23/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.23/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.23/1.00  --bmc1_ucm_extend_mode                  1
% 3.23/1.00  --bmc1_ucm_init_mode                    2
% 3.23/1.00  --bmc1_ucm_cone_mode                    none
% 3.23/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.23/1.00  --bmc1_ucm_relax_model                  4
% 3.23/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.23/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/1.00  --bmc1_ucm_layered_model                none
% 3.23/1.00  --bmc1_ucm_max_lemma_size               10
% 3.23/1.00  
% 3.23/1.00  ------ AIG Options
% 3.23/1.00  
% 3.23/1.00  --aig_mode                              false
% 3.23/1.00  
% 3.23/1.00  ------ Instantiation Options
% 3.23/1.00  
% 3.23/1.00  --instantiation_flag                    true
% 3.23/1.00  --inst_sos_flag                         false
% 3.23/1.00  --inst_sos_phase                        true
% 3.23/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel_side                     num_symb
% 3.23/1.00  --inst_solver_per_active                1400
% 3.23/1.00  --inst_solver_calls_frac                1.
% 3.23/1.00  --inst_passive_queue_type               priority_queues
% 3.23/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/1.00  --inst_passive_queues_freq              [25;2]
% 3.23/1.00  --inst_dismatching                      true
% 3.23/1.00  --inst_eager_unprocessed_to_passive     true
% 3.23/1.00  --inst_prop_sim_given                   true
% 3.23/1.00  --inst_prop_sim_new                     false
% 3.23/1.00  --inst_subs_new                         false
% 3.23/1.00  --inst_eq_res_simp                      false
% 3.23/1.00  --inst_subs_given                       false
% 3.23/1.00  --inst_orphan_elimination               true
% 3.23/1.00  --inst_learning_loop_flag               true
% 3.23/1.00  --inst_learning_start                   3000
% 3.23/1.00  --inst_learning_factor                  2
% 3.23/1.00  --inst_start_prop_sim_after_learn       3
% 3.23/1.00  --inst_sel_renew                        solver
% 3.23/1.00  --inst_lit_activity_flag                true
% 3.23/1.00  --inst_restr_to_given                   false
% 3.23/1.00  --inst_activity_threshold               500
% 3.23/1.00  --inst_out_proof                        true
% 3.23/1.00  
% 3.23/1.00  ------ Resolution Options
% 3.23/1.00  
% 3.23/1.00  --resolution_flag                       true
% 3.23/1.00  --res_lit_sel                           adaptive
% 3.23/1.00  --res_lit_sel_side                      none
% 3.23/1.00  --res_ordering                          kbo
% 3.23/1.00  --res_to_prop_solver                    active
% 3.23/1.00  --res_prop_simpl_new                    false
% 3.23/1.00  --res_prop_simpl_given                  true
% 3.23/1.00  --res_passive_queue_type                priority_queues
% 3.23/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/1.00  --res_passive_queues_freq               [15;5]
% 3.23/1.00  --res_forward_subs                      full
% 3.23/1.00  --res_backward_subs                     full
% 3.23/1.00  --res_forward_subs_resolution           true
% 3.23/1.00  --res_backward_subs_resolution          true
% 3.23/1.00  --res_orphan_elimination                true
% 3.23/1.00  --res_time_limit                        2.
% 3.23/1.00  --res_out_proof                         true
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Options
% 3.23/1.00  
% 3.23/1.00  --superposition_flag                    true
% 3.23/1.00  --sup_passive_queue_type                priority_queues
% 3.23/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.23/1.00  --demod_completeness_check              fast
% 3.23/1.00  --demod_use_ground                      true
% 3.23/1.00  --sup_to_prop_solver                    passive
% 3.23/1.00  --sup_prop_simpl_new                    true
% 3.23/1.00  --sup_prop_simpl_given                  true
% 3.23/1.00  --sup_fun_splitting                     false
% 3.23/1.00  --sup_smt_interval                      50000
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Simplification Setup
% 3.23/1.00  
% 3.23/1.00  --sup_indices_passive                   []
% 3.23/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_full_bw                           [BwDemod]
% 3.23/1.00  --sup_immed_triv                        [TrivRules]
% 3.23/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_immed_bw_main                     []
% 3.23/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  
% 3.23/1.00  ------ Combination Options
% 3.23/1.00  
% 3.23/1.00  --comb_res_mult                         3
% 3.23/1.00  --comb_sup_mult                         2
% 3.23/1.00  --comb_inst_mult                        10
% 3.23/1.00  
% 3.23/1.00  ------ Debug Options
% 3.23/1.00  
% 3.23/1.00  --dbg_backtrace                         false
% 3.23/1.00  --dbg_dump_prop_clauses                 false
% 3.23/1.00  --dbg_dump_prop_clauses_file            -
% 3.23/1.00  --dbg_out_stat                          false
% 3.23/1.00  ------ Parsing...
% 3.23/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.23/1.00  ------ Proving...
% 3.23/1.00  ------ Problem Properties 
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  clauses                                 22
% 3.23/1.00  conjectures                             4
% 3.23/1.00  EPR                                     3
% 3.23/1.00  Horn                                    17
% 3.23/1.00  unary                                   8
% 3.23/1.00  binary                                  7
% 3.23/1.00  lits                                    44
% 3.23/1.00  lits eq                                 16
% 3.23/1.00  fd_pure                                 0
% 3.23/1.00  fd_pseudo                               0
% 3.23/1.00  fd_cond                                 1
% 3.23/1.00  fd_pseudo_cond                          6
% 3.23/1.00  AC symbols                              0
% 3.23/1.00  
% 3.23/1.00  ------ Schedule dynamic 5 is on 
% 3.23/1.00  
% 3.23/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  ------ 
% 3.23/1.00  Current options:
% 3.23/1.00  ------ 
% 3.23/1.00  
% 3.23/1.00  ------ Input Options
% 3.23/1.00  
% 3.23/1.00  --out_options                           all
% 3.23/1.00  --tptp_safe_out                         true
% 3.23/1.00  --problem_path                          ""
% 3.23/1.00  --include_path                          ""
% 3.23/1.00  --clausifier                            res/vclausify_rel
% 3.23/1.00  --clausifier_options                    --mode clausify
% 3.23/1.00  --stdin                                 false
% 3.23/1.00  --stats_out                             all
% 3.23/1.00  
% 3.23/1.00  ------ General Options
% 3.23/1.00  
% 3.23/1.00  --fof                                   false
% 3.23/1.00  --time_out_real                         305.
% 3.23/1.00  --time_out_virtual                      -1.
% 3.23/1.00  --symbol_type_check                     false
% 3.23/1.00  --clausify_out                          false
% 3.23/1.00  --sig_cnt_out                           false
% 3.23/1.00  --trig_cnt_out                          false
% 3.23/1.00  --trig_cnt_out_tolerance                1.
% 3.23/1.00  --trig_cnt_out_sk_spl                   false
% 3.23/1.00  --abstr_cl_out                          false
% 3.23/1.00  
% 3.23/1.00  ------ Global Options
% 3.23/1.00  
% 3.23/1.00  --schedule                              default
% 3.23/1.00  --add_important_lit                     false
% 3.23/1.00  --prop_solver_per_cl                    1000
% 3.23/1.00  --min_unsat_core                        false
% 3.23/1.00  --soft_assumptions                      false
% 3.23/1.00  --soft_lemma_size                       3
% 3.23/1.00  --prop_impl_unit_size                   0
% 3.23/1.00  --prop_impl_unit                        []
% 3.23/1.00  --share_sel_clauses                     true
% 3.23/1.00  --reset_solvers                         false
% 3.23/1.00  --bc_imp_inh                            [conj_cone]
% 3.23/1.00  --conj_cone_tolerance                   3.
% 3.23/1.00  --extra_neg_conj                        none
% 3.23/1.00  --large_theory_mode                     true
% 3.23/1.00  --prolific_symb_bound                   200
% 3.23/1.00  --lt_threshold                          2000
% 3.23/1.00  --clause_weak_htbl                      true
% 3.23/1.00  --gc_record_bc_elim                     false
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing Options
% 3.23/1.00  
% 3.23/1.00  --preprocessing_flag                    true
% 3.23/1.00  --time_out_prep_mult                    0.1
% 3.23/1.00  --splitting_mode                        input
% 3.23/1.00  --splitting_grd                         true
% 3.23/1.00  --splitting_cvd                         false
% 3.23/1.00  --splitting_cvd_svl                     false
% 3.23/1.00  --splitting_nvd                         32
% 3.23/1.00  --sub_typing                            true
% 3.23/1.00  --prep_gs_sim                           true
% 3.23/1.00  --prep_unflatten                        true
% 3.23/1.00  --prep_res_sim                          true
% 3.23/1.00  --prep_upred                            true
% 3.23/1.00  --prep_sem_filter                       exhaustive
% 3.23/1.00  --prep_sem_filter_out                   false
% 3.23/1.00  --pred_elim                             true
% 3.23/1.00  --res_sim_input                         true
% 3.23/1.00  --eq_ax_congr_red                       true
% 3.23/1.00  --pure_diseq_elim                       true
% 3.23/1.00  --brand_transform                       false
% 3.23/1.00  --non_eq_to_eq                          false
% 3.23/1.00  --prep_def_merge                        true
% 3.23/1.00  --prep_def_merge_prop_impl              false
% 3.23/1.00  --prep_def_merge_mbd                    true
% 3.23/1.00  --prep_def_merge_tr_red                 false
% 3.23/1.00  --prep_def_merge_tr_cl                  false
% 3.23/1.00  --smt_preprocessing                     true
% 3.23/1.00  --smt_ac_axioms                         fast
% 3.23/1.00  --preprocessed_out                      false
% 3.23/1.00  --preprocessed_stats                    false
% 3.23/1.00  
% 3.23/1.00  ------ Abstraction refinement Options
% 3.23/1.00  
% 3.23/1.00  --abstr_ref                             []
% 3.23/1.00  --abstr_ref_prep                        false
% 3.23/1.00  --abstr_ref_until_sat                   false
% 3.23/1.00  --abstr_ref_sig_restrict                funpre
% 3.23/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/1.00  --abstr_ref_under                       []
% 3.23/1.00  
% 3.23/1.00  ------ SAT Options
% 3.23/1.00  
% 3.23/1.00  --sat_mode                              false
% 3.23/1.00  --sat_fm_restart_options                ""
% 3.23/1.00  --sat_gr_def                            false
% 3.23/1.01  --sat_epr_types                         true
% 3.23/1.01  --sat_non_cyclic_types                  false
% 3.23/1.01  --sat_finite_models                     false
% 3.23/1.01  --sat_fm_lemmas                         false
% 3.23/1.01  --sat_fm_prep                           false
% 3.23/1.01  --sat_fm_uc_incr                        true
% 3.23/1.01  --sat_out_model                         small
% 3.23/1.01  --sat_out_clauses                       false
% 3.23/1.01  
% 3.23/1.01  ------ QBF Options
% 3.23/1.01  
% 3.23/1.01  --qbf_mode                              false
% 3.23/1.01  --qbf_elim_univ                         false
% 3.23/1.01  --qbf_dom_inst                          none
% 3.23/1.01  --qbf_dom_pre_inst                      false
% 3.23/1.01  --qbf_sk_in                             false
% 3.23/1.01  --qbf_pred_elim                         true
% 3.23/1.01  --qbf_split                             512
% 3.23/1.01  
% 3.23/1.01  ------ BMC1 Options
% 3.23/1.01  
% 3.23/1.01  --bmc1_incremental                      false
% 3.23/1.01  --bmc1_axioms                           reachable_all
% 3.23/1.01  --bmc1_min_bound                        0
% 3.23/1.01  --bmc1_max_bound                        -1
% 3.23/1.01  --bmc1_max_bound_default                -1
% 3.23/1.01  --bmc1_symbol_reachability              true
% 3.23/1.01  --bmc1_property_lemmas                  false
% 3.23/1.01  --bmc1_k_induction                      false
% 3.23/1.01  --bmc1_non_equiv_states                 false
% 3.23/1.01  --bmc1_deadlock                         false
% 3.23/1.01  --bmc1_ucm                              false
% 3.23/1.01  --bmc1_add_unsat_core                   none
% 3.23/1.01  --bmc1_unsat_core_children              false
% 3.23/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/1.01  --bmc1_out_stat                         full
% 3.23/1.01  --bmc1_ground_init                      false
% 3.23/1.01  --bmc1_pre_inst_next_state              false
% 3.23/1.01  --bmc1_pre_inst_state                   false
% 3.23/1.01  --bmc1_pre_inst_reach_state             false
% 3.23/1.01  --bmc1_out_unsat_core                   false
% 3.23/1.01  --bmc1_aig_witness_out                  false
% 3.23/1.01  --bmc1_verbose                          false
% 3.23/1.01  --bmc1_dump_clauses_tptp                false
% 3.23/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.23/1.01  --bmc1_dump_file                        -
% 3.23/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.23/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.23/1.01  --bmc1_ucm_extend_mode                  1
% 3.23/1.01  --bmc1_ucm_init_mode                    2
% 3.23/1.01  --bmc1_ucm_cone_mode                    none
% 3.23/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.23/1.01  --bmc1_ucm_relax_model                  4
% 3.23/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.23/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/1.01  --bmc1_ucm_layered_model                none
% 3.23/1.01  --bmc1_ucm_max_lemma_size               10
% 3.23/1.01  
% 3.23/1.01  ------ AIG Options
% 3.23/1.01  
% 3.23/1.01  --aig_mode                              false
% 3.23/1.01  
% 3.23/1.01  ------ Instantiation Options
% 3.23/1.01  
% 3.23/1.01  --instantiation_flag                    true
% 3.23/1.01  --inst_sos_flag                         false
% 3.23/1.01  --inst_sos_phase                        true
% 3.23/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/1.01  --inst_lit_sel_side                     none
% 3.23/1.01  --inst_solver_per_active                1400
% 3.23/1.01  --inst_solver_calls_frac                1.
% 3.23/1.01  --inst_passive_queue_type               priority_queues
% 3.23/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/1.01  --inst_passive_queues_freq              [25;2]
% 3.23/1.01  --inst_dismatching                      true
% 3.23/1.01  --inst_eager_unprocessed_to_passive     true
% 3.23/1.01  --inst_prop_sim_given                   true
% 3.23/1.01  --inst_prop_sim_new                     false
% 3.23/1.01  --inst_subs_new                         false
% 3.23/1.01  --inst_eq_res_simp                      false
% 3.23/1.01  --inst_subs_given                       false
% 3.23/1.01  --inst_orphan_elimination               true
% 3.23/1.01  --inst_learning_loop_flag               true
% 3.23/1.01  --inst_learning_start                   3000
% 3.23/1.01  --inst_learning_factor                  2
% 3.23/1.01  --inst_start_prop_sim_after_learn       3
% 3.23/1.01  --inst_sel_renew                        solver
% 3.23/1.01  --inst_lit_activity_flag                true
% 3.23/1.01  --inst_restr_to_given                   false
% 3.23/1.01  --inst_activity_threshold               500
% 3.23/1.01  --inst_out_proof                        true
% 3.23/1.01  
% 3.23/1.01  ------ Resolution Options
% 3.23/1.01  
% 3.23/1.01  --resolution_flag                       false
% 3.23/1.01  --res_lit_sel                           adaptive
% 3.23/1.01  --res_lit_sel_side                      none
% 3.23/1.01  --res_ordering                          kbo
% 3.23/1.01  --res_to_prop_solver                    active
% 3.23/1.01  --res_prop_simpl_new                    false
% 3.23/1.01  --res_prop_simpl_given                  true
% 3.23/1.01  --res_passive_queue_type                priority_queues
% 3.23/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/1.01  --res_passive_queues_freq               [15;5]
% 3.23/1.01  --res_forward_subs                      full
% 3.23/1.01  --res_backward_subs                     full
% 3.23/1.01  --res_forward_subs_resolution           true
% 3.23/1.01  --res_backward_subs_resolution          true
% 3.23/1.01  --res_orphan_elimination                true
% 3.23/1.01  --res_time_limit                        2.
% 3.23/1.01  --res_out_proof                         true
% 3.23/1.01  
% 3.23/1.01  ------ Superposition Options
% 3.23/1.01  
% 3.23/1.01  --superposition_flag                    true
% 3.23/1.01  --sup_passive_queue_type                priority_queues
% 3.23/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.23/1.01  --demod_completeness_check              fast
% 3.23/1.01  --demod_use_ground                      true
% 3.23/1.01  --sup_to_prop_solver                    passive
% 3.23/1.01  --sup_prop_simpl_new                    true
% 3.23/1.01  --sup_prop_simpl_given                  true
% 3.23/1.01  --sup_fun_splitting                     false
% 3.23/1.01  --sup_smt_interval                      50000
% 3.23/1.01  
% 3.23/1.01  ------ Superposition Simplification Setup
% 3.23/1.01  
% 3.23/1.01  --sup_indices_passive                   []
% 3.23/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.01  --sup_full_bw                           [BwDemod]
% 3.23/1.01  --sup_immed_triv                        [TrivRules]
% 3.23/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.01  --sup_immed_bw_main                     []
% 3.23/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.01  
% 3.23/1.01  ------ Combination Options
% 3.23/1.01  
% 3.23/1.01  --comb_res_mult                         3
% 3.23/1.01  --comb_sup_mult                         2
% 3.23/1.01  --comb_inst_mult                        10
% 3.23/1.01  
% 3.23/1.01  ------ Debug Options
% 3.23/1.01  
% 3.23/1.01  --dbg_backtrace                         false
% 3.23/1.01  --dbg_dump_prop_clauses                 false
% 3.23/1.01  --dbg_dump_prop_clauses_file            -
% 3.23/1.01  --dbg_out_stat                          false
% 3.23/1.01  
% 3.23/1.01  
% 3.23/1.01  
% 3.23/1.01  
% 3.23/1.01  ------ Proving...
% 3.23/1.01  
% 3.23/1.01  
% 3.23/1.01  % SZS status Theorem for theBenchmark.p
% 3.23/1.01  
% 3.23/1.01   Resolution empty clause
% 3.23/1.01  
% 3.23/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.23/1.01  
% 3.23/1.01  fof(f2,axiom,(
% 3.23/1.01    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f18,plain,(
% 3.23/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.23/1.01    inference(ennf_transformation,[],[f2])).
% 3.23/1.01  
% 3.23/1.01  fof(f26,plain,(
% 3.23/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.23/1.01    introduced(choice_axiom,[])).
% 3.23/1.01  
% 3.23/1.01  fof(f27,plain,(
% 3.23/1.01    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 3.23/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f26])).
% 3.23/1.01  
% 3.23/1.01  fof(f43,plain,(
% 3.23/1.01    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.23/1.01    inference(cnf_transformation,[],[f27])).
% 3.23/1.01  
% 3.23/1.01  fof(f16,conjecture,(
% 3.23/1.01    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f17,negated_conjecture,(
% 3.23/1.01    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.23/1.01    inference(negated_conjecture,[],[f16])).
% 3.23/1.01  
% 3.23/1.01  fof(f20,plain,(
% 3.23/1.01    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.23/1.01    inference(ennf_transformation,[],[f17])).
% 3.23/1.01  
% 3.23/1.01  fof(f35,plain,(
% 3.23/1.01    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0)) => (k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & sK4 != sK5 & k2_xboole_0(sK4,sK5) = k1_tarski(sK3))),
% 3.23/1.01    introduced(choice_axiom,[])).
% 3.23/1.01  
% 3.23/1.01  fof(f36,plain,(
% 3.23/1.01    k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & sK4 != sK5 & k2_xboole_0(sK4,sK5) = k1_tarski(sK3)),
% 3.23/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f20,f35])).
% 3.23/1.01  
% 3.23/1.01  fof(f63,plain,(
% 3.23/1.01    k2_xboole_0(sK4,sK5) = k1_tarski(sK3)),
% 3.23/1.01    inference(cnf_transformation,[],[f36])).
% 3.23/1.01  
% 3.23/1.01  fof(f15,axiom,(
% 3.23/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f62,plain,(
% 3.23/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.23/1.01    inference(cnf_transformation,[],[f15])).
% 3.23/1.01  
% 3.23/1.01  fof(f72,plain,(
% 3.23/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.23/1.01    inference(definition_unfolding,[],[f62,f71])).
% 3.23/1.01  
% 3.23/1.01  fof(f6,axiom,(
% 3.23/1.01    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f50,plain,(
% 3.23/1.01    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.23/1.01    inference(cnf_transformation,[],[f6])).
% 3.23/1.01  
% 3.23/1.01  fof(f7,axiom,(
% 3.23/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f51,plain,(
% 3.23/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.23/1.01    inference(cnf_transformation,[],[f7])).
% 3.23/1.01  
% 3.23/1.01  fof(f8,axiom,(
% 3.23/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f52,plain,(
% 3.23/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.23/1.01    inference(cnf_transformation,[],[f8])).
% 3.23/1.01  
% 3.23/1.01  fof(f9,axiom,(
% 3.23/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f53,plain,(
% 3.23/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.23/1.01    inference(cnf_transformation,[],[f9])).
% 3.23/1.01  
% 3.23/1.01  fof(f10,axiom,(
% 3.23/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f54,plain,(
% 3.23/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.23/1.01    inference(cnf_transformation,[],[f10])).
% 3.23/1.01  
% 3.23/1.01  fof(f11,axiom,(
% 3.23/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f55,plain,(
% 3.23/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.23/1.01    inference(cnf_transformation,[],[f11])).
% 3.23/1.01  
% 3.23/1.01  fof(f12,axiom,(
% 3.23/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f56,plain,(
% 3.23/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.23/1.01    inference(cnf_transformation,[],[f12])).
% 3.23/1.01  
% 3.23/1.01  fof(f67,plain,(
% 3.23/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.23/1.01    inference(definition_unfolding,[],[f55,f56])).
% 3.23/1.01  
% 3.23/1.01  fof(f68,plain,(
% 3.23/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.23/1.01    inference(definition_unfolding,[],[f54,f67])).
% 3.23/1.01  
% 3.23/1.01  fof(f69,plain,(
% 3.23/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.23/1.01    inference(definition_unfolding,[],[f53,f68])).
% 3.23/1.01  
% 3.23/1.01  fof(f70,plain,(
% 3.23/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.23/1.01    inference(definition_unfolding,[],[f52,f69])).
% 3.23/1.01  
% 3.23/1.01  fof(f71,plain,(
% 3.23/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.23/1.01    inference(definition_unfolding,[],[f51,f70])).
% 3.23/1.01  
% 3.23/1.01  fof(f73,plain,(
% 3.23/1.01    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.23/1.01    inference(definition_unfolding,[],[f50,f71])).
% 3.23/1.01  
% 3.23/1.01  fof(f91,plain,(
% 3.23/1.01    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),
% 3.23/1.01    inference(definition_unfolding,[],[f63,f72,f73])).
% 3.23/1.01  
% 3.23/1.01  fof(f4,axiom,(
% 3.23/1.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f45,plain,(
% 3.23/1.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.23/1.01    inference(cnf_transformation,[],[f4])).
% 3.23/1.01  
% 3.23/1.01  fof(f81,plain,(
% 3.23/1.01    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.23/1.01    inference(definition_unfolding,[],[f45,f72])).
% 3.23/1.01  
% 3.23/1.01  fof(f14,axiom,(
% 3.23/1.01    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f33,plain,(
% 3.23/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.23/1.01    inference(nnf_transformation,[],[f14])).
% 3.23/1.01  
% 3.23/1.01  fof(f34,plain,(
% 3.23/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.23/1.01    inference(flattening,[],[f33])).
% 3.23/1.01  
% 3.23/1.01  fof(f59,plain,(
% 3.23/1.01    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.23/1.01    inference(cnf_transformation,[],[f34])).
% 3.23/1.01  
% 3.23/1.01  fof(f90,plain,(
% 3.23/1.01    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 3.23/1.01    inference(definition_unfolding,[],[f59,f73,f73])).
% 3.23/1.01  
% 3.23/1.01  fof(f65,plain,(
% 3.23/1.01    k1_xboole_0 != sK4),
% 3.23/1.01    inference(cnf_transformation,[],[f36])).
% 3.23/1.01  
% 3.23/1.01  fof(f1,axiom,(
% 3.23/1.01    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f21,plain,(
% 3.23/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.23/1.01    inference(nnf_transformation,[],[f1])).
% 3.23/1.01  
% 3.23/1.01  fof(f22,plain,(
% 3.23/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.23/1.01    inference(flattening,[],[f21])).
% 3.23/1.01  
% 3.23/1.01  fof(f23,plain,(
% 3.23/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.23/1.01    inference(rectify,[],[f22])).
% 3.23/1.01  
% 3.23/1.01  fof(f24,plain,(
% 3.23/1.01    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.23/1.01    introduced(choice_axiom,[])).
% 3.23/1.01  
% 3.23/1.01  fof(f25,plain,(
% 3.23/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.23/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 3.23/1.01  
% 3.23/1.01  fof(f39,plain,(
% 3.23/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.23/1.01    inference(cnf_transformation,[],[f25])).
% 3.23/1.01  
% 3.23/1.01  fof(f77,plain,(
% 3.23/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.23/1.01    inference(definition_unfolding,[],[f39,f72])).
% 3.23/1.01  
% 3.23/1.01  fof(f92,plain,(
% 3.23/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 3.23/1.01    inference(equality_resolution,[],[f77])).
% 3.23/1.01  
% 3.23/1.01  fof(f5,axiom,(
% 3.23/1.01    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.23/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f28,plain,(
% 3.23/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.23/1.01    inference(nnf_transformation,[],[f5])).
% 3.23/1.01  
% 3.23/1.01  fof(f29,plain,(
% 3.23/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.23/1.01    inference(rectify,[],[f28])).
% 3.23/1.01  
% 3.23/1.01  fof(f30,plain,(
% 3.23/1.01    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 3.23/1.01    introduced(choice_axiom,[])).
% 3.23/1.01  
% 3.23/1.01  fof(f31,plain,(
% 3.23/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.23/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 3.23/1.01  
% 3.23/1.01  fof(f46,plain,(
% 3.23/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.23/1.01    inference(cnf_transformation,[],[f31])).
% 3.23/1.01  
% 3.23/1.01  fof(f85,plain,(
% 3.23/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 3.23/1.01    inference(definition_unfolding,[],[f46,f73])).
% 3.23/1.01  
% 3.23/1.01  fof(f97,plain,(
% 3.23/1.01    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 3.23/1.01    inference(equality_resolution,[],[f85])).
% 3.23/1.01  
% 3.23/1.01  fof(f64,plain,(
% 3.23/1.01    sK4 != sK5),
% 3.23/1.01    inference(cnf_transformation,[],[f36])).
% 3.23/1.01  
% 3.23/1.01  fof(f40,plain,(
% 3.23/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.23/1.01    inference(cnf_transformation,[],[f25])).
% 3.23/1.01  
% 3.23/1.01  fof(f76,plain,(
% 3.23/1.01    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.23/1.01    inference(definition_unfolding,[],[f40,f72])).
% 3.23/1.01  
% 3.23/1.01  fof(f42,plain,(
% 3.23/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.23/1.01    inference(cnf_transformation,[],[f25])).
% 3.23/1.01  
% 3.23/1.01  fof(f74,plain,(
% 3.23/1.01    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.23/1.01    inference(definition_unfolding,[],[f42,f72])).
% 3.23/1.01  
% 3.23/1.01  fof(f66,plain,(
% 3.23/1.01    k1_xboole_0 != sK5),
% 3.23/1.01    inference(cnf_transformation,[],[f36])).
% 3.23/1.01  
% 3.23/1.01  cnf(c_6,plain,
% 3.23/1.01      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.23/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_796,plain,
% 3.23/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.23/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_21,negated_conjecture,
% 3.23/1.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
% 3.23/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_8,plain,
% 3.23/1.01      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 3.23/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_794,plain,
% 3.23/1.01      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 3.23/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_1106,plain,
% 3.23/1.01      ( r1_tarski(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 3.23/1.01      inference(superposition,[status(thm)],[c_21,c_794]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_17,plain,
% 3.23/1.01      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 3.23/1.01      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 3.23/1.01      | k1_xboole_0 = X0 ),
% 3.23/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_785,plain,
% 3.23/1.01      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 3.23/1.01      | k1_xboole_0 = X1
% 3.23/1.01      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 3.23/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_1186,plain,
% 3.23/1.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4
% 3.23/1.01      | sK4 = k1_xboole_0 ),
% 3.23/1.01      inference(superposition,[status(thm)],[c_1106,c_785]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_19,negated_conjecture,
% 3.23/1.01      ( k1_xboole_0 != sK4 ),
% 3.23/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_363,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_930,plain,
% 3.23/1.01      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 3.23/1.01      inference(instantiation,[status(thm)],[c_363]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_1026,plain,
% 3.23/1.01      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 3.23/1.01      inference(instantiation,[status(thm)],[c_930]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_362,plain,( X0 = X0 ),theory(equality) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_1027,plain,
% 3.23/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 3.23/1.01      inference(instantiation,[status(thm)],[c_362]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_1738,plain,
% 3.23/1.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4 ),
% 3.23/1.01      inference(global_propositional_subsumption,
% 3.23/1.01                [status(thm)],
% 3.23/1.01                [c_1186,c_19,c_1026,c_1027]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_1743,plain,
% 3.23/1.01      ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK4 ),
% 3.23/1.01      inference(demodulation,[status(thm)],[c_1738,c_21]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_3,plain,
% 3.23/1.01      ( ~ r2_hidden(X0,X1)
% 3.23/1.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 3.23/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_799,plain,
% 3.23/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.23/1.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 3.23/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_2530,plain,
% 3.23/1.01      ( r2_hidden(X0,sK4) = iProver_top | r2_hidden(X0,sK5) != iProver_top ),
% 3.23/1.01      inference(superposition,[status(thm)],[c_1743,c_799]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_2716,plain,
% 3.23/1.01      ( sK5 = k1_xboole_0 | r2_hidden(sK1(sK5),sK4) = iProver_top ),
% 3.23/1.01      inference(superposition,[status(thm)],[c_796,c_2530]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_12,plain,
% 3.23/1.01      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 3.23/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_790,plain,
% 3.23/1.01      ( X0 = X1
% 3.23/1.01      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 3.23/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_1756,plain,
% 3.23/1.01      ( sK3 = X0 | r2_hidden(X0,sK4) != iProver_top ),
% 3.23/1.01      inference(superposition,[status(thm)],[c_1738,c_790]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_2948,plain,
% 3.23/1.01      ( sK1(sK5) = sK3 | sK5 = k1_xboole_0 ),
% 3.23/1.01      inference(superposition,[status(thm)],[c_2716,c_1756]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_8668,plain,
% 3.23/1.01      ( sK5 = k1_xboole_0 | r2_hidden(sK3,sK5) = iProver_top ),
% 3.23/1.01      inference(superposition,[status(thm)],[c_2948,c_796]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_20,negated_conjecture,
% 3.23/1.01      ( sK4 != sK5 ),
% 3.23/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_2,plain,
% 3.23/1.01      ( r2_hidden(sK0(X0,X1,X2),X1)
% 3.23/1.01      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.23/1.01      | r2_hidden(sK0(X0,X1,X2),X0)
% 3.23/1.01      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2 ),
% 3.23/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_800,plain,
% 3.23/1.01      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2
% 3.23/1.01      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
% 3.23/1.01      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 3.23/1.01      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
% 3.23/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_3706,plain,
% 3.23/1.01      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = sK5
% 3.23/1.01      | r2_hidden(sK0(X0,X1,sK5),X1) = iProver_top
% 3.23/1.01      | r2_hidden(sK0(X0,X1,sK5),X0) = iProver_top
% 3.23/1.01      | r2_hidden(sK0(X0,X1,sK5),sK4) = iProver_top ),
% 3.23/1.01      inference(superposition,[status(thm)],[c_800,c_2530]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_4973,plain,
% 3.23/1.01      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) = sK5
% 3.23/1.01      | r2_hidden(sK0(X0,sK5,sK5),X0) = iProver_top
% 3.23/1.01      | r2_hidden(sK0(X0,sK5,sK5),sK4) = iProver_top ),
% 3.23/1.01      inference(superposition,[status(thm)],[c_3706,c_2530]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_1525,plain,
% 3.23/1.01      ( r2_hidden(sK0(X0,X1,sK5),X1)
% 3.23/1.01      | r2_hidden(sK0(X0,X1,sK5),X0)
% 3.23/1.01      | r2_hidden(sK0(X0,X1,sK5),sK5)
% 3.23/1.01      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = sK5 ),
% 3.23/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_3144,plain,
% 3.23/1.01      ( r2_hidden(sK0(X0,sK5,sK5),X0)
% 3.23/1.01      | r2_hidden(sK0(X0,sK5,sK5),sK5)
% 3.23/1.01      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) = sK5 ),
% 3.23/1.01      inference(instantiation,[status(thm)],[c_1525]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_3147,plain,
% 3.23/1.01      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) = sK5
% 3.23/1.01      | r2_hidden(sK0(X0,sK5,sK5),X0) = iProver_top
% 3.23/1.01      | r2_hidden(sK0(X0,sK5,sK5),sK5) = iProver_top ),
% 3.23/1.01      inference(predicate_to_equality,[status(thm)],[c_3144]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_0,plain,
% 3.23/1.01      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 3.23/1.01      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.23/1.01      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2 ),
% 3.23/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_1527,plain,
% 3.23/1.01      ( ~ r2_hidden(sK0(X0,X1,sK5),X1)
% 3.23/1.01      | ~ r2_hidden(sK0(X0,X1,sK5),sK5)
% 3.23/1.01      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = sK5 ),
% 3.23/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_3145,plain,
% 3.23/1.01      ( ~ r2_hidden(sK0(X0,sK5,sK5),sK5)
% 3.23/1.01      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) = sK5 ),
% 3.23/1.01      inference(instantiation,[status(thm)],[c_1527]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_3155,plain,
% 3.23/1.01      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) = sK5
% 3.23/1.01      | r2_hidden(sK0(X0,sK5,sK5),sK5) != iProver_top ),
% 3.23/1.01      inference(predicate_to_equality,[status(thm)],[c_3145]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_5100,plain,
% 3.23/1.01      ( r2_hidden(sK0(X0,sK5,sK5),X0) = iProver_top
% 3.23/1.01      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) = sK5 ),
% 3.23/1.01      inference(global_propositional_subsumption,
% 3.23/1.01                [status(thm)],
% 3.23/1.01                [c_4973,c_3147,c_3155]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_5101,plain,
% 3.23/1.01      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) = sK5
% 3.23/1.01      | r2_hidden(sK0(X0,sK5,sK5),X0) = iProver_top ),
% 3.23/1.01      inference(renaming,[status(thm)],[c_5100]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_5110,plain,
% 3.23/1.01      ( sK0(sK4,sK5,sK5) = sK3
% 3.23/1.01      | k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK5 ),
% 3.23/1.01      inference(superposition,[status(thm)],[c_5101,c_1756]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_5119,plain,
% 3.23/1.01      ( sK0(sK4,sK5,sK5) = sK3 | sK4 = sK5 ),
% 3.23/1.01      inference(demodulation,[status(thm)],[c_5110,c_1743]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_5216,plain,
% 3.23/1.01      ( sK0(sK4,sK5,sK5) = sK3 ),
% 3.23/1.01      inference(global_propositional_subsumption,[status(thm)],[c_5119,c_20]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_802,plain,
% 3.23/1.01      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X2
% 3.23/1.01      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 3.23/1.01      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
% 3.23/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_5222,plain,
% 3.23/1.01      ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK5
% 3.23/1.01      | r2_hidden(sK0(sK4,sK5,sK5),sK5) != iProver_top
% 3.23/1.01      | r2_hidden(sK3,sK5) != iProver_top ),
% 3.23/1.01      inference(superposition,[status(thm)],[c_5216,c_802]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_5244,plain,
% 3.23/1.01      ( k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = sK5
% 3.23/1.01      | r2_hidden(sK3,sK5) != iProver_top ),
% 3.23/1.01      inference(light_normalisation,[status(thm)],[c_5222,c_5216]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_5245,plain,
% 3.23/1.01      ( sK4 = sK5 | r2_hidden(sK3,sK5) != iProver_top ),
% 3.23/1.01      inference(demodulation,[status(thm)],[c_5244,c_1743]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_9390,plain,
% 3.23/1.01      ( sK5 = k1_xboole_0 ),
% 3.23/1.01      inference(global_propositional_subsumption,
% 3.23/1.01                [status(thm)],
% 3.23/1.01                [c_8668,c_20,c_5245]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_18,negated_conjecture,
% 3.23/1.01      ( k1_xboole_0 != sK5 ),
% 3.23/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_9418,plain,
% 3.23/1.01      ( k1_xboole_0 != k1_xboole_0 ),
% 3.23/1.01      inference(demodulation,[status(thm)],[c_9390,c_18]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_9419,plain,
% 3.23/1.01      ( $false ),
% 3.23/1.01      inference(equality_resolution_simp,[status(thm)],[c_9418]) ).
% 3.23/1.01  
% 3.23/1.01  
% 3.23/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.23/1.01  
% 3.23/1.01  ------                               Statistics
% 3.23/1.01  
% 3.23/1.01  ------ General
% 3.23/1.01  
% 3.23/1.01  abstr_ref_over_cycles:                  0
% 3.23/1.01  abstr_ref_under_cycles:                 0
% 3.23/1.01  gc_basic_clause_elim:                   0
% 3.23/1.01  forced_gc_time:                         0
% 3.23/1.01  parsing_time:                           0.011
% 3.23/1.01  unif_index_cands_time:                  0.
% 3.23/1.01  unif_index_add_time:                    0.
% 3.23/1.01  orderings_time:                         0.
% 3.23/1.01  out_proof_time:                         0.011
% 3.23/1.01  total_time:                             0.436
% 3.23/1.01  num_of_symbols:                         42
% 3.23/1.01  num_of_terms:                           10427
% 3.23/1.01  
% 3.23/1.01  ------ Preprocessing
% 3.23/1.01  
% 3.23/1.01  num_of_splits:                          0
% 3.23/1.01  num_of_split_atoms:                     0
% 3.23/1.01  num_of_reused_defs:                     0
% 3.23/1.01  num_eq_ax_congr_red:                    12
% 3.23/1.01  num_of_sem_filtered_clauses:            1
% 3.23/1.01  num_of_subtypes:                        0
% 3.23/1.01  monotx_restored_types:                  0
% 3.23/1.01  sat_num_of_epr_types:                   0
% 3.23/1.01  sat_num_of_non_cyclic_types:            0
% 3.23/1.01  sat_guarded_non_collapsed_types:        0
% 3.23/1.01  num_pure_diseq_elim:                    0
% 3.23/1.01  simp_replaced_by:                       0
% 3.23/1.01  res_preprocessed:                       79
% 3.23/1.01  prep_upred:                             0
% 3.23/1.01  prep_unflattend:                        17
% 3.23/1.01  smt_new_axioms:                         0
% 3.23/1.01  pred_elim_cands:                        2
% 3.23/1.01  pred_elim:                              0
% 3.23/1.01  pred_elim_cl:                           0
% 3.23/1.01  pred_elim_cycles:                       1
% 3.23/1.01  merged_defs:                            6
% 3.23/1.01  merged_defs_ncl:                        0
% 3.23/1.01  bin_hyper_res:                          6
% 3.23/1.01  prep_cycles:                            3
% 3.23/1.01  pred_elim_time:                         0.002
% 3.23/1.01  splitting_time:                         0.
% 3.23/1.01  sem_filter_time:                        0.
% 3.23/1.01  monotx_time:                            0.001
% 3.23/1.01  subtype_inf_time:                       0.
% 3.23/1.01  
% 3.23/1.01  ------ Problem properties
% 3.23/1.01  
% 3.23/1.01  clauses:                                22
% 3.23/1.01  conjectures:                            4
% 3.23/1.01  epr:                                    3
% 3.23/1.01  horn:                                   17
% 3.23/1.01  ground:                                 4
% 3.23/1.01  unary:                                  8
% 3.23/1.01  binary:                                 7
% 3.23/1.01  lits:                                   44
% 3.23/1.01  lits_eq:                                16
% 3.23/1.01  fd_pure:                                0
% 3.23/1.01  fd_pseudo:                              0
% 3.23/1.01  fd_cond:                                1
% 3.23/1.01  fd_pseudo_cond:                         6
% 3.23/1.01  ac_symbols:                             0
% 3.23/1.01  
% 3.23/1.01  ------ Propositional Solver
% 3.23/1.01  
% 3.23/1.01  prop_solver_calls:                      23
% 3.23/1.01  prop_fast_solver_calls:                 564
% 3.23/1.01  smt_solver_calls:                       0
% 3.23/1.01  smt_fast_solver_calls:                  0
% 3.23/1.01  prop_num_of_clauses:                    3538
% 3.23/1.01  prop_preprocess_simplified:             7814
% 3.23/1.01  prop_fo_subsumed:                       10
% 3.23/1.01  prop_solver_time:                       0.
% 3.23/1.01  smt_solver_time:                        0.
% 3.23/1.01  smt_fast_solver_time:                   0.
% 3.23/1.01  prop_fast_solver_time:                  0.
% 3.23/1.01  prop_unsat_core_time:                   0.
% 3.23/1.01  
% 3.23/1.01  ------ QBF
% 3.23/1.01  
% 3.23/1.01  qbf_q_res:                              0
% 3.23/1.01  qbf_num_tautologies:                    0
% 3.23/1.01  qbf_prep_cycles:                        0
% 3.23/1.01  
% 3.23/1.01  ------ BMC1
% 3.23/1.01  
% 3.23/1.01  bmc1_current_bound:                     -1
% 3.23/1.01  bmc1_last_solved_bound:                 -1
% 3.23/1.01  bmc1_unsat_core_size:                   -1
% 3.23/1.01  bmc1_unsat_core_parents_size:           -1
% 3.23/1.01  bmc1_merge_next_fun:                    0
% 3.23/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.23/1.01  
% 3.23/1.01  ------ Instantiation
% 3.23/1.01  
% 3.23/1.01  inst_num_of_clauses:                    968
% 3.23/1.01  inst_num_in_passive:                    178
% 3.23/1.01  inst_num_in_active:                     376
% 3.23/1.01  inst_num_in_unprocessed:                414
% 3.23/1.01  inst_num_of_loops:                      430
% 3.23/1.01  inst_num_of_learning_restarts:          0
% 3.23/1.01  inst_num_moves_active_passive:          53
% 3.23/1.01  inst_lit_activity:                      0
% 3.23/1.01  inst_lit_activity_moves:                0
% 3.23/1.01  inst_num_tautologies:                   0
% 3.23/1.01  inst_num_prop_implied:                  0
% 3.23/1.01  inst_num_existing_simplified:           0
% 3.23/1.01  inst_num_eq_res_simplified:             0
% 3.23/1.01  inst_num_child_elim:                    0
% 3.23/1.01  inst_num_of_dismatching_blockings:      564
% 3.23/1.01  inst_num_of_non_proper_insts:           1017
% 3.23/1.01  inst_num_of_duplicates:                 0
% 3.23/1.01  inst_inst_num_from_inst_to_res:         0
% 3.23/1.01  inst_dismatching_checking_time:         0.
% 3.23/1.01  
% 3.23/1.01  ------ Resolution
% 3.23/1.01  
% 3.23/1.01  res_num_of_clauses:                     0
% 3.23/1.01  res_num_in_passive:                     0
% 3.23/1.01  res_num_in_active:                      0
% 3.23/1.01  res_num_of_loops:                       82
% 3.23/1.01  res_forward_subset_subsumed:            78
% 3.23/1.01  res_backward_subset_subsumed:           0
% 3.23/1.01  res_forward_subsumed:                   0
% 3.23/1.01  res_backward_subsumed:                  0
% 3.23/1.01  res_forward_subsumption_resolution:     0
% 3.23/1.01  res_backward_subsumption_resolution:    0
% 3.23/1.01  res_clause_to_clause_subsumption:       1045
% 3.23/1.01  res_orphan_elimination:                 0
% 3.23/1.01  res_tautology_del:                      48
% 3.23/1.01  res_num_eq_res_simplified:              0
% 3.23/1.01  res_num_sel_changes:                    0
% 3.23/1.01  res_moves_from_active_to_pass:          0
% 3.23/1.01  
% 3.23/1.01  ------ Superposition
% 3.23/1.01  
% 3.23/1.01  sup_time_total:                         0.
% 3.23/1.01  sup_time_generating:                    0.
% 3.23/1.01  sup_time_sim_full:                      0.
% 3.23/1.01  sup_time_sim_immed:                     0.
% 3.23/1.01  
% 3.23/1.01  sup_num_of_clauses:                     176
% 3.23/1.01  sup_num_in_active:                      50
% 3.23/1.01  sup_num_in_passive:                     126
% 3.23/1.01  sup_num_of_loops:                       85
% 3.23/1.01  sup_fw_superposition:                   160
% 3.23/1.01  sup_bw_superposition:                   391
% 3.23/1.01  sup_immediate_simplified:               250
% 3.23/1.01  sup_given_eliminated:                   2
% 3.23/1.01  comparisons_done:                       0
% 3.23/1.01  comparisons_avoided:                    19
% 3.23/1.01  
% 3.23/1.01  ------ Simplifications
% 3.23/1.01  
% 3.23/1.01  
% 3.23/1.01  sim_fw_subset_subsumed:                 192
% 3.23/1.01  sim_bw_subset_subsumed:                 4
% 3.23/1.01  sim_fw_subsumed:                        40
% 3.23/1.01  sim_bw_subsumed:                        2
% 3.23/1.01  sim_fw_subsumption_res:                 6
% 3.23/1.01  sim_bw_subsumption_res:                 0
% 3.23/1.01  sim_tautology_del:                      39
% 3.23/1.01  sim_eq_tautology_del:                   17
% 3.23/1.01  sim_eq_res_simp:                        34
% 3.23/1.01  sim_fw_demodulated:                     30
% 3.23/1.01  sim_bw_demodulated:                     32
% 3.23/1.01  sim_light_normalised:                   36
% 3.23/1.01  sim_joinable_taut:                      0
% 3.23/1.01  sim_joinable_simp:                      0
% 3.23/1.01  sim_ac_normalised:                      0
% 3.23/1.01  sim_smt_subsumption:                    0
% 3.23/1.01  
%------------------------------------------------------------------------------
