%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:23 EST 2020

% Result     : Theorem 11.89s
% Output     : CNFRefutation 11.89s
% Verified   : 
% Statistics : Number of formulae       :  155 (1964 expanded)
%              Number of clauses        :   69 ( 193 expanded)
%              Number of leaves         :   21 ( 586 expanded)
%              Depth                    :   18
%              Number of atoms          :  459 (4463 expanded)
%              Number of equality atoms :  267 (3131 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f35])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK2(X0,X1) = X0
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f74,f75])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f73,f85])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f72,f86])).

fof(f88,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f71,f87])).

fof(f89,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f70,f88])).

fof(f93,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f69,f89])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
      | sK2(X0,X1) = X0
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f67,f93])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f45,plain,
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

fof(f46,plain,
    ( ( k1_xboole_0 != sK5
      | k1_tarski(sK3) != sK4 )
    & ( k1_tarski(sK3) != sK5
      | k1_xboole_0 != sK4 )
    & ( k1_tarski(sK3) != sK5
      | k1_tarski(sK3) != sK4 )
    & k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f45])).

fof(f81,plain,(
    k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f90,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f78,f89])).

fof(f114,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
    inference(definition_unfolding,[],[f81,f90,f93])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f48,f90])).

fof(f116,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f106,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f65,f93])).

fof(f122,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f106])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f49,f90])).

fof(f115,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f97])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK2(X0,X1) != X0
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
      | sK2(X0,X1) != X0
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f68,f93])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f105,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f66,f93])).

fof(f120,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f105])).

fof(f121,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f120])).

fof(f82,plain,
    ( k1_tarski(sK3) != sK5
    | k1_tarski(sK3) != sK4 ),
    inference(cnf_transformation,[],[f46])).

fof(f113,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4 ),
    inference(definition_unfolding,[],[f82,f93,f93])).

fof(f83,plain,
    ( k1_tarski(sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f46])).

fof(f112,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(definition_unfolding,[],[f83,f93])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f77,f93])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f119,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f59,f90])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f99,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f47,f90])).

fof(f117,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f99])).

fof(f84,plain,
    ( k1_xboole_0 != sK5
    | k1_tarski(sK3) != sK4 ),
    inference(cnf_transformation,[],[f46])).

fof(f111,plain,
    ( k1_xboole_0 != sK5
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4 ),
    inference(definition_unfolding,[],[f84,f93])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_849,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_17,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | sK2(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_843,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | sK2(X0,X1) = X0
    | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_27,negated_conjecture,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_851,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_24497,plain,
    ( r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_851])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_841,plain,
    ( X0 = X1
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_28555,plain,
    ( sK3 = X0
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_24497,c_841])).

cnf(c_28561,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK4
    | sK2(X0,sK4) = X0
    | sK2(X0,sK4) = sK3 ),
    inference(superposition,[status(thm)],[c_843,c_28555])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_852,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_29202,plain,
    ( r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_852])).

cnf(c_31822,plain,
    ( sK2(sK3,sK4) = sK3
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_28561,c_29202])).

cnf(c_16,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | sK2(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_933,plain,
    ( ~ r2_hidden(sK2(sK3,sK5),sK5)
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
    | sK2(sK3,sK5) != sK3 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_937,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
    | sK2(sK3,sK5) != sK3
    | r2_hidden(sK2(sK3,sK5),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_933])).

cnf(c_18,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_7404,plain,
    ( r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_435,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6289,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2(sK3,sK5),sK5)
    | sK2(sK3,sK5) != X0
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_20407,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK2(sK3,sK5),sK5)
    | sK2(sK3,sK5) != X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_6289])).

cnf(c_20408,plain,
    ( sK2(sK3,sK5) != X0
    | sK5 != sK5
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK2(sK3,sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20407])).

cnf(c_20410,plain,
    ( sK2(sK3,sK5) != sK3
    | sK5 != sK5
    | r2_hidden(sK2(sK3,sK5),sK5) = iProver_top
    | r2_hidden(sK3,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_20408])).

cnf(c_3556,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_21270,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_3556])).

cnf(c_6352,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK3,sK5)
    | sK3 != X0
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_28631,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK3,sK5)
    | sK3 != X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_6352])).

cnf(c_28632,plain,
    ( sK3 != X0
    | sK5 != sK5
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28631])).

cnf(c_26,negated_conjecture,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_28938,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5
    | sK2(sK3,sK4) = sK3 ),
    inference(superposition,[status(thm)],[c_28561,c_26])).

cnf(c_25,negated_conjecture,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_907,plain,
    ( ~ r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)
    | ~ r1_tarski(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_908,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4
    | r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4) != iProver_top
    | r1_tarski(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_907])).

cnf(c_20,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_959,plain,
    ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)
    | ~ r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_960,plain,
    ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4) = iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_959])).

cnf(c_432,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_897,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_1244,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_897])).

cnf(c_10,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1968,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1234,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X0)
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2039,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_847,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_846,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_17668,plain,
    ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_846])).

cnf(c_19243,plain,
    ( r1_tarski(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_847,c_17668])).

cnf(c_28560,plain,
    ( sK1(sK4) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_849,c_28555])).

cnf(c_28671,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_28560,c_849])).

cnf(c_29118,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_28938,c_26,c_25,c_908,c_960,c_1244,c_1968,c_2039,c_19243,c_28671])).

cnf(c_31823,plain,
    ( sK3 = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_29202,c_841])).

cnf(c_31934,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK5
    | sK2(X0,sK5) = X0
    | sK2(X0,sK5) = sK3 ),
    inference(superposition,[status(thm)],[c_843,c_31823])).

cnf(c_31935,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
    | sK2(sK3,sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_31934])).

cnf(c_32082,plain,
    ( r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31822,c_26,c_25,c_908,c_937,c_960,c_1244,c_1968,c_2039,c_7404,c_19243,c_20410,c_21270,c_28632,c_28671,c_31823,c_31935])).

cnf(c_32088,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_849,c_32082])).

cnf(c_842,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_850,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_20483,plain,
    ( r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_850])).

cnf(c_24163,plain,
    ( r2_hidden(sK3,sK4) = iProver_top
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_842,c_20483])).

cnf(c_885,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_5348,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_885])).

cnf(c_24,negated_conjecture,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f111])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32088,c_31935,c_29118,c_24163,c_21270,c_20410,c_19243,c_7404,c_5348,c_2039,c_1968,c_960,c_937,c_908,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:16:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 11.89/2.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.89/2.01  
% 11.89/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.89/2.01  
% 11.89/2.01  ------  iProver source info
% 11.89/2.01  
% 11.89/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.89/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.89/2.01  git: non_committed_changes: false
% 11.89/2.01  git: last_make_outside_of_git: false
% 11.89/2.01  
% 11.89/2.01  ------ 
% 11.89/2.01  
% 11.89/2.01  ------ Input Options
% 11.89/2.01  
% 11.89/2.01  --out_options                           all
% 11.89/2.01  --tptp_safe_out                         true
% 11.89/2.01  --problem_path                          ""
% 11.89/2.01  --include_path                          ""
% 11.89/2.01  --clausifier                            res/vclausify_rel
% 11.89/2.01  --clausifier_options                    ""
% 11.89/2.01  --stdin                                 false
% 11.89/2.01  --stats_out                             all
% 11.89/2.01  
% 11.89/2.01  ------ General Options
% 11.89/2.01  
% 11.89/2.01  --fof                                   false
% 11.89/2.01  --time_out_real                         305.
% 11.89/2.01  --time_out_virtual                      -1.
% 11.89/2.01  --symbol_type_check                     false
% 11.89/2.01  --clausify_out                          false
% 11.89/2.01  --sig_cnt_out                           false
% 11.89/2.01  --trig_cnt_out                          false
% 11.89/2.01  --trig_cnt_out_tolerance                1.
% 11.89/2.01  --trig_cnt_out_sk_spl                   false
% 11.89/2.01  --abstr_cl_out                          false
% 11.89/2.01  
% 11.89/2.01  ------ Global Options
% 11.89/2.01  
% 11.89/2.01  --schedule                              default
% 11.89/2.01  --add_important_lit                     false
% 11.89/2.01  --prop_solver_per_cl                    1000
% 11.89/2.01  --min_unsat_core                        false
% 11.89/2.01  --soft_assumptions                      false
% 11.89/2.01  --soft_lemma_size                       3
% 11.89/2.01  --prop_impl_unit_size                   0
% 11.89/2.01  --prop_impl_unit                        []
% 11.89/2.01  --share_sel_clauses                     true
% 11.89/2.01  --reset_solvers                         false
% 11.89/2.01  --bc_imp_inh                            [conj_cone]
% 11.89/2.01  --conj_cone_tolerance                   3.
% 11.89/2.01  --extra_neg_conj                        none
% 11.89/2.01  --large_theory_mode                     true
% 11.89/2.01  --prolific_symb_bound                   200
% 11.89/2.01  --lt_threshold                          2000
% 11.89/2.01  --clause_weak_htbl                      true
% 11.89/2.01  --gc_record_bc_elim                     false
% 11.89/2.01  
% 11.89/2.01  ------ Preprocessing Options
% 11.89/2.01  
% 11.89/2.01  --preprocessing_flag                    true
% 11.89/2.01  --time_out_prep_mult                    0.1
% 11.89/2.01  --splitting_mode                        input
% 11.89/2.01  --splitting_grd                         true
% 11.89/2.01  --splitting_cvd                         false
% 11.89/2.01  --splitting_cvd_svl                     false
% 11.89/2.01  --splitting_nvd                         32
% 11.89/2.01  --sub_typing                            true
% 11.89/2.01  --prep_gs_sim                           true
% 11.89/2.01  --prep_unflatten                        true
% 11.89/2.01  --prep_res_sim                          true
% 11.89/2.01  --prep_upred                            true
% 11.89/2.01  --prep_sem_filter                       exhaustive
% 11.89/2.01  --prep_sem_filter_out                   false
% 11.89/2.01  --pred_elim                             true
% 11.89/2.01  --res_sim_input                         true
% 11.89/2.01  --eq_ax_congr_red                       true
% 11.89/2.01  --pure_diseq_elim                       true
% 11.89/2.01  --brand_transform                       false
% 11.89/2.01  --non_eq_to_eq                          false
% 11.89/2.01  --prep_def_merge                        true
% 11.89/2.01  --prep_def_merge_prop_impl              false
% 11.89/2.01  --prep_def_merge_mbd                    true
% 11.89/2.01  --prep_def_merge_tr_red                 false
% 11.89/2.01  --prep_def_merge_tr_cl                  false
% 11.89/2.01  --smt_preprocessing                     true
% 11.89/2.01  --smt_ac_axioms                         fast
% 11.89/2.01  --preprocessed_out                      false
% 11.89/2.01  --preprocessed_stats                    false
% 11.89/2.01  
% 11.89/2.01  ------ Abstraction refinement Options
% 11.89/2.01  
% 11.89/2.01  --abstr_ref                             []
% 11.89/2.01  --abstr_ref_prep                        false
% 11.89/2.01  --abstr_ref_until_sat                   false
% 11.89/2.01  --abstr_ref_sig_restrict                funpre
% 11.89/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.89/2.01  --abstr_ref_under                       []
% 11.89/2.01  
% 11.89/2.01  ------ SAT Options
% 11.89/2.01  
% 11.89/2.01  --sat_mode                              false
% 11.89/2.01  --sat_fm_restart_options                ""
% 11.89/2.01  --sat_gr_def                            false
% 11.89/2.01  --sat_epr_types                         true
% 11.89/2.01  --sat_non_cyclic_types                  false
% 11.89/2.01  --sat_finite_models                     false
% 11.89/2.01  --sat_fm_lemmas                         false
% 11.89/2.01  --sat_fm_prep                           false
% 11.89/2.01  --sat_fm_uc_incr                        true
% 11.89/2.01  --sat_out_model                         small
% 11.89/2.01  --sat_out_clauses                       false
% 11.89/2.01  
% 11.89/2.01  ------ QBF Options
% 11.89/2.01  
% 11.89/2.01  --qbf_mode                              false
% 11.89/2.01  --qbf_elim_univ                         false
% 11.89/2.01  --qbf_dom_inst                          none
% 11.89/2.01  --qbf_dom_pre_inst                      false
% 11.89/2.01  --qbf_sk_in                             false
% 11.89/2.01  --qbf_pred_elim                         true
% 11.89/2.01  --qbf_split                             512
% 11.89/2.01  
% 11.89/2.01  ------ BMC1 Options
% 11.89/2.01  
% 11.89/2.01  --bmc1_incremental                      false
% 11.89/2.01  --bmc1_axioms                           reachable_all
% 11.89/2.01  --bmc1_min_bound                        0
% 11.89/2.01  --bmc1_max_bound                        -1
% 11.89/2.01  --bmc1_max_bound_default                -1
% 11.89/2.01  --bmc1_symbol_reachability              true
% 11.89/2.01  --bmc1_property_lemmas                  false
% 11.89/2.01  --bmc1_k_induction                      false
% 11.89/2.01  --bmc1_non_equiv_states                 false
% 11.89/2.01  --bmc1_deadlock                         false
% 11.89/2.01  --bmc1_ucm                              false
% 11.89/2.01  --bmc1_add_unsat_core                   none
% 11.89/2.01  --bmc1_unsat_core_children              false
% 11.89/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.89/2.01  --bmc1_out_stat                         full
% 11.89/2.01  --bmc1_ground_init                      false
% 11.89/2.01  --bmc1_pre_inst_next_state              false
% 11.89/2.01  --bmc1_pre_inst_state                   false
% 11.89/2.01  --bmc1_pre_inst_reach_state             false
% 11.89/2.01  --bmc1_out_unsat_core                   false
% 11.89/2.01  --bmc1_aig_witness_out                  false
% 11.89/2.01  --bmc1_verbose                          false
% 11.89/2.01  --bmc1_dump_clauses_tptp                false
% 11.89/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.89/2.01  --bmc1_dump_file                        -
% 11.89/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.89/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.89/2.01  --bmc1_ucm_extend_mode                  1
% 11.89/2.01  --bmc1_ucm_init_mode                    2
% 11.89/2.01  --bmc1_ucm_cone_mode                    none
% 11.89/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.89/2.01  --bmc1_ucm_relax_model                  4
% 11.89/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.89/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.89/2.01  --bmc1_ucm_layered_model                none
% 11.89/2.01  --bmc1_ucm_max_lemma_size               10
% 11.89/2.01  
% 11.89/2.01  ------ AIG Options
% 11.89/2.01  
% 11.89/2.01  --aig_mode                              false
% 11.89/2.01  
% 11.89/2.01  ------ Instantiation Options
% 11.89/2.01  
% 11.89/2.01  --instantiation_flag                    true
% 11.89/2.01  --inst_sos_flag                         true
% 11.89/2.01  --inst_sos_phase                        true
% 11.89/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.89/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.89/2.01  --inst_lit_sel_side                     num_symb
% 11.89/2.01  --inst_solver_per_active                1400
% 11.89/2.01  --inst_solver_calls_frac                1.
% 11.89/2.01  --inst_passive_queue_type               priority_queues
% 11.89/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.89/2.01  --inst_passive_queues_freq              [25;2]
% 11.89/2.01  --inst_dismatching                      true
% 11.89/2.01  --inst_eager_unprocessed_to_passive     true
% 11.89/2.01  --inst_prop_sim_given                   true
% 11.89/2.01  --inst_prop_sim_new                     false
% 11.89/2.01  --inst_subs_new                         false
% 11.89/2.01  --inst_eq_res_simp                      false
% 11.89/2.01  --inst_subs_given                       false
% 11.89/2.01  --inst_orphan_elimination               true
% 11.89/2.01  --inst_learning_loop_flag               true
% 11.89/2.01  --inst_learning_start                   3000
% 11.89/2.01  --inst_learning_factor                  2
% 11.89/2.01  --inst_start_prop_sim_after_learn       3
% 11.89/2.01  --inst_sel_renew                        solver
% 11.89/2.01  --inst_lit_activity_flag                true
% 11.89/2.01  --inst_restr_to_given                   false
% 11.89/2.01  --inst_activity_threshold               500
% 11.89/2.01  --inst_out_proof                        true
% 11.89/2.01  
% 11.89/2.01  ------ Resolution Options
% 11.89/2.01  
% 11.89/2.01  --resolution_flag                       true
% 11.89/2.01  --res_lit_sel                           adaptive
% 11.89/2.01  --res_lit_sel_side                      none
% 11.89/2.01  --res_ordering                          kbo
% 11.89/2.01  --res_to_prop_solver                    active
% 11.89/2.01  --res_prop_simpl_new                    false
% 11.89/2.01  --res_prop_simpl_given                  true
% 11.89/2.01  --res_passive_queue_type                priority_queues
% 11.89/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.89/2.01  --res_passive_queues_freq               [15;5]
% 11.89/2.01  --res_forward_subs                      full
% 11.89/2.01  --res_backward_subs                     full
% 11.89/2.01  --res_forward_subs_resolution           true
% 11.89/2.01  --res_backward_subs_resolution          true
% 11.89/2.01  --res_orphan_elimination                true
% 11.89/2.01  --res_time_limit                        2.
% 11.89/2.01  --res_out_proof                         true
% 11.89/2.01  
% 11.89/2.01  ------ Superposition Options
% 11.89/2.01  
% 11.89/2.01  --superposition_flag                    true
% 11.89/2.01  --sup_passive_queue_type                priority_queues
% 11.89/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.89/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.89/2.01  --demod_completeness_check              fast
% 11.89/2.01  --demod_use_ground                      true
% 11.89/2.01  --sup_to_prop_solver                    passive
% 11.89/2.01  --sup_prop_simpl_new                    true
% 11.89/2.01  --sup_prop_simpl_given                  true
% 11.89/2.01  --sup_fun_splitting                     true
% 11.89/2.01  --sup_smt_interval                      50000
% 11.89/2.01  
% 11.89/2.01  ------ Superposition Simplification Setup
% 11.89/2.01  
% 11.89/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.89/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.89/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.89/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.89/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.89/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.89/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.89/2.01  --sup_immed_triv                        [TrivRules]
% 11.89/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.89/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.89/2.01  --sup_immed_bw_main                     []
% 11.89/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.89/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.89/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.89/2.01  --sup_input_bw                          []
% 11.89/2.01  
% 11.89/2.01  ------ Combination Options
% 11.89/2.01  
% 11.89/2.01  --comb_res_mult                         3
% 11.89/2.01  --comb_sup_mult                         2
% 11.89/2.01  --comb_inst_mult                        10
% 11.89/2.01  
% 11.89/2.01  ------ Debug Options
% 11.89/2.01  
% 11.89/2.01  --dbg_backtrace                         false
% 11.89/2.01  --dbg_dump_prop_clauses                 false
% 11.89/2.01  --dbg_dump_prop_clauses_file            -
% 11.89/2.01  --dbg_out_stat                          false
% 11.89/2.01  ------ Parsing...
% 11.89/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.89/2.01  
% 11.89/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.89/2.01  
% 11.89/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.89/2.01  
% 11.89/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.89/2.01  ------ Proving...
% 11.89/2.01  ------ Problem Properties 
% 11.89/2.01  
% 11.89/2.01  
% 11.89/2.01  clauses                                 27
% 11.89/2.01  conjectures                             4
% 11.89/2.01  EPR                                     2
% 11.89/2.01  Horn                                    22
% 11.89/2.01  unary                                   8
% 11.89/2.01  binary                                  12
% 11.89/2.01  lits                                    54
% 11.89/2.01  lits eq                                 25
% 11.89/2.01  fd_pure                                 0
% 11.89/2.01  fd_pseudo                               0
% 11.89/2.01  fd_cond                                 1
% 11.89/2.01  fd_pseudo_cond                          7
% 11.89/2.01  AC symbols                              0
% 11.89/2.01  
% 11.89/2.01  ------ Schedule dynamic 5 is on 
% 11.89/2.01  
% 11.89/2.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.89/2.01  
% 11.89/2.01  
% 11.89/2.01  ------ 
% 11.89/2.01  Current options:
% 11.89/2.01  ------ 
% 11.89/2.01  
% 11.89/2.01  ------ Input Options
% 11.89/2.01  
% 11.89/2.01  --out_options                           all
% 11.89/2.01  --tptp_safe_out                         true
% 11.89/2.01  --problem_path                          ""
% 11.89/2.01  --include_path                          ""
% 11.89/2.01  --clausifier                            res/vclausify_rel
% 11.89/2.01  --clausifier_options                    ""
% 11.89/2.01  --stdin                                 false
% 11.89/2.01  --stats_out                             all
% 11.89/2.01  
% 11.89/2.01  ------ General Options
% 11.89/2.01  
% 11.89/2.01  --fof                                   false
% 11.89/2.01  --time_out_real                         305.
% 11.89/2.01  --time_out_virtual                      -1.
% 11.89/2.01  --symbol_type_check                     false
% 11.89/2.01  --clausify_out                          false
% 11.89/2.01  --sig_cnt_out                           false
% 11.89/2.01  --trig_cnt_out                          false
% 11.89/2.01  --trig_cnt_out_tolerance                1.
% 11.89/2.01  --trig_cnt_out_sk_spl                   false
% 11.89/2.01  --abstr_cl_out                          false
% 11.89/2.01  
% 11.89/2.01  ------ Global Options
% 11.89/2.01  
% 11.89/2.01  --schedule                              default
% 11.89/2.01  --add_important_lit                     false
% 11.89/2.01  --prop_solver_per_cl                    1000
% 11.89/2.01  --min_unsat_core                        false
% 11.89/2.01  --soft_assumptions                      false
% 11.89/2.01  --soft_lemma_size                       3
% 11.89/2.01  --prop_impl_unit_size                   0
% 11.89/2.01  --prop_impl_unit                        []
% 11.89/2.01  --share_sel_clauses                     true
% 11.89/2.01  --reset_solvers                         false
% 11.89/2.01  --bc_imp_inh                            [conj_cone]
% 11.89/2.01  --conj_cone_tolerance                   3.
% 11.89/2.01  --extra_neg_conj                        none
% 11.89/2.01  --large_theory_mode                     true
% 11.89/2.01  --prolific_symb_bound                   200
% 11.89/2.01  --lt_threshold                          2000
% 11.89/2.01  --clause_weak_htbl                      true
% 11.89/2.01  --gc_record_bc_elim                     false
% 11.89/2.01  
% 11.89/2.01  ------ Preprocessing Options
% 11.89/2.01  
% 11.89/2.01  --preprocessing_flag                    true
% 11.89/2.01  --time_out_prep_mult                    0.1
% 11.89/2.01  --splitting_mode                        input
% 11.89/2.01  --splitting_grd                         true
% 11.89/2.01  --splitting_cvd                         false
% 11.89/2.01  --splitting_cvd_svl                     false
% 11.89/2.01  --splitting_nvd                         32
% 11.89/2.01  --sub_typing                            true
% 11.89/2.01  --prep_gs_sim                           true
% 11.89/2.01  --prep_unflatten                        true
% 11.89/2.01  --prep_res_sim                          true
% 11.89/2.01  --prep_upred                            true
% 11.89/2.01  --prep_sem_filter                       exhaustive
% 11.89/2.01  --prep_sem_filter_out                   false
% 11.89/2.01  --pred_elim                             true
% 11.89/2.01  --res_sim_input                         true
% 11.89/2.01  --eq_ax_congr_red                       true
% 11.89/2.01  --pure_diseq_elim                       true
% 11.89/2.01  --brand_transform                       false
% 11.89/2.01  --non_eq_to_eq                          false
% 11.89/2.01  --prep_def_merge                        true
% 11.89/2.01  --prep_def_merge_prop_impl              false
% 11.89/2.01  --prep_def_merge_mbd                    true
% 11.89/2.01  --prep_def_merge_tr_red                 false
% 11.89/2.01  --prep_def_merge_tr_cl                  false
% 11.89/2.01  --smt_preprocessing                     true
% 11.89/2.01  --smt_ac_axioms                         fast
% 11.89/2.01  --preprocessed_out                      false
% 11.89/2.01  --preprocessed_stats                    false
% 11.89/2.01  
% 11.89/2.01  ------ Abstraction refinement Options
% 11.89/2.01  
% 11.89/2.01  --abstr_ref                             []
% 11.89/2.01  --abstr_ref_prep                        false
% 11.89/2.01  --abstr_ref_until_sat                   false
% 11.89/2.01  --abstr_ref_sig_restrict                funpre
% 11.89/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.89/2.01  --abstr_ref_under                       []
% 11.89/2.01  
% 11.89/2.01  ------ SAT Options
% 11.89/2.01  
% 11.89/2.01  --sat_mode                              false
% 11.89/2.01  --sat_fm_restart_options                ""
% 11.89/2.01  --sat_gr_def                            false
% 11.89/2.01  --sat_epr_types                         true
% 11.89/2.01  --sat_non_cyclic_types                  false
% 11.89/2.01  --sat_finite_models                     false
% 11.89/2.01  --sat_fm_lemmas                         false
% 11.89/2.01  --sat_fm_prep                           false
% 11.89/2.01  --sat_fm_uc_incr                        true
% 11.89/2.01  --sat_out_model                         small
% 11.89/2.01  --sat_out_clauses                       false
% 11.89/2.01  
% 11.89/2.01  ------ QBF Options
% 11.89/2.01  
% 11.89/2.01  --qbf_mode                              false
% 11.89/2.01  --qbf_elim_univ                         false
% 11.89/2.01  --qbf_dom_inst                          none
% 11.89/2.01  --qbf_dom_pre_inst                      false
% 11.89/2.01  --qbf_sk_in                             false
% 11.89/2.01  --qbf_pred_elim                         true
% 11.89/2.01  --qbf_split                             512
% 11.89/2.01  
% 11.89/2.01  ------ BMC1 Options
% 11.89/2.01  
% 11.89/2.01  --bmc1_incremental                      false
% 11.89/2.01  --bmc1_axioms                           reachable_all
% 11.89/2.01  --bmc1_min_bound                        0
% 11.89/2.01  --bmc1_max_bound                        -1
% 11.89/2.01  --bmc1_max_bound_default                -1
% 11.89/2.01  --bmc1_symbol_reachability              true
% 11.89/2.01  --bmc1_property_lemmas                  false
% 11.89/2.01  --bmc1_k_induction                      false
% 11.89/2.01  --bmc1_non_equiv_states                 false
% 11.89/2.01  --bmc1_deadlock                         false
% 11.89/2.01  --bmc1_ucm                              false
% 11.89/2.01  --bmc1_add_unsat_core                   none
% 11.89/2.01  --bmc1_unsat_core_children              false
% 11.89/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.89/2.01  --bmc1_out_stat                         full
% 11.89/2.01  --bmc1_ground_init                      false
% 11.89/2.01  --bmc1_pre_inst_next_state              false
% 11.89/2.01  --bmc1_pre_inst_state                   false
% 11.89/2.01  --bmc1_pre_inst_reach_state             false
% 11.89/2.01  --bmc1_out_unsat_core                   false
% 11.89/2.01  --bmc1_aig_witness_out                  false
% 11.89/2.01  --bmc1_verbose                          false
% 11.89/2.01  --bmc1_dump_clauses_tptp                false
% 11.89/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.89/2.01  --bmc1_dump_file                        -
% 11.89/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.89/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.89/2.01  --bmc1_ucm_extend_mode                  1
% 11.89/2.01  --bmc1_ucm_init_mode                    2
% 11.89/2.01  --bmc1_ucm_cone_mode                    none
% 11.89/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.89/2.01  --bmc1_ucm_relax_model                  4
% 11.89/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.89/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.89/2.01  --bmc1_ucm_layered_model                none
% 11.89/2.01  --bmc1_ucm_max_lemma_size               10
% 11.89/2.01  
% 11.89/2.01  ------ AIG Options
% 11.89/2.01  
% 11.89/2.01  --aig_mode                              false
% 11.89/2.01  
% 11.89/2.01  ------ Instantiation Options
% 11.89/2.01  
% 11.89/2.01  --instantiation_flag                    true
% 11.89/2.01  --inst_sos_flag                         true
% 11.89/2.01  --inst_sos_phase                        true
% 11.89/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.89/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.89/2.01  --inst_lit_sel_side                     none
% 11.89/2.01  --inst_solver_per_active                1400
% 11.89/2.01  --inst_solver_calls_frac                1.
% 11.89/2.01  --inst_passive_queue_type               priority_queues
% 11.89/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.89/2.01  --inst_passive_queues_freq              [25;2]
% 11.89/2.01  --inst_dismatching                      true
% 11.89/2.01  --inst_eager_unprocessed_to_passive     true
% 11.89/2.01  --inst_prop_sim_given                   true
% 11.89/2.01  --inst_prop_sim_new                     false
% 11.89/2.01  --inst_subs_new                         false
% 11.89/2.01  --inst_eq_res_simp                      false
% 11.89/2.01  --inst_subs_given                       false
% 11.89/2.01  --inst_orphan_elimination               true
% 11.89/2.01  --inst_learning_loop_flag               true
% 11.89/2.01  --inst_learning_start                   3000
% 11.89/2.01  --inst_learning_factor                  2
% 11.89/2.01  --inst_start_prop_sim_after_learn       3
% 11.89/2.01  --inst_sel_renew                        solver
% 11.89/2.01  --inst_lit_activity_flag                true
% 11.89/2.01  --inst_restr_to_given                   false
% 11.89/2.01  --inst_activity_threshold               500
% 11.89/2.01  --inst_out_proof                        true
% 11.89/2.01  
% 11.89/2.01  ------ Resolution Options
% 11.89/2.01  
% 11.89/2.01  --resolution_flag                       false
% 11.89/2.01  --res_lit_sel                           adaptive
% 11.89/2.01  --res_lit_sel_side                      none
% 11.89/2.01  --res_ordering                          kbo
% 11.89/2.01  --res_to_prop_solver                    active
% 11.89/2.01  --res_prop_simpl_new                    false
% 11.89/2.01  --res_prop_simpl_given                  true
% 11.89/2.01  --res_passive_queue_type                priority_queues
% 11.89/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.89/2.01  --res_passive_queues_freq               [15;5]
% 11.89/2.01  --res_forward_subs                      full
% 11.89/2.01  --res_backward_subs                     full
% 11.89/2.01  --res_forward_subs_resolution           true
% 11.89/2.01  --res_backward_subs_resolution          true
% 11.89/2.01  --res_orphan_elimination                true
% 11.89/2.01  --res_time_limit                        2.
% 11.89/2.01  --res_out_proof                         true
% 11.89/2.01  
% 11.89/2.01  ------ Superposition Options
% 11.89/2.01  
% 11.89/2.01  --superposition_flag                    true
% 11.89/2.01  --sup_passive_queue_type                priority_queues
% 11.89/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.89/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.89/2.01  --demod_completeness_check              fast
% 11.89/2.01  --demod_use_ground                      true
% 11.89/2.01  --sup_to_prop_solver                    passive
% 11.89/2.01  --sup_prop_simpl_new                    true
% 11.89/2.01  --sup_prop_simpl_given                  true
% 11.89/2.01  --sup_fun_splitting                     true
% 11.89/2.01  --sup_smt_interval                      50000
% 11.89/2.01  
% 11.89/2.01  ------ Superposition Simplification Setup
% 11.89/2.01  
% 11.89/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.89/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.89/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.89/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.89/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.89/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.89/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.89/2.01  --sup_immed_triv                        [TrivRules]
% 11.89/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.89/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.89/2.01  --sup_immed_bw_main                     []
% 11.89/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.89/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.89/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.89/2.01  --sup_input_bw                          []
% 11.89/2.01  
% 11.89/2.01  ------ Combination Options
% 11.89/2.01  
% 11.89/2.01  --comb_res_mult                         3
% 11.89/2.01  --comb_sup_mult                         2
% 11.89/2.01  --comb_inst_mult                        10
% 11.89/2.01  
% 11.89/2.01  ------ Debug Options
% 11.89/2.01  
% 11.89/2.01  --dbg_backtrace                         false
% 11.89/2.01  --dbg_dump_prop_clauses                 false
% 11.89/2.01  --dbg_dump_prop_clauses_file            -
% 11.89/2.01  --dbg_out_stat                          false
% 11.89/2.01  
% 11.89/2.01  
% 11.89/2.01  
% 11.89/2.01  
% 11.89/2.01  ------ Proving...
% 11.89/2.01  
% 11.89/2.01  
% 11.89/2.01  % SZS status Theorem for theBenchmark.p
% 11.89/2.01  
% 11.89/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.89/2.01  
% 11.89/2.01  fof(f3,axiom,(
% 11.89/2.01    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 11.89/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.89/2.01  
% 11.89/2.01  fof(f26,plain,(
% 11.89/2.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 11.89/2.01    inference(ennf_transformation,[],[f3])).
% 11.89/2.01  
% 11.89/2.01  fof(f35,plain,(
% 11.89/2.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 11.89/2.01    introduced(choice_axiom,[])).
% 11.89/2.01  
% 11.89/2.01  fof(f36,plain,(
% 11.89/2.01    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 11.89/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f35])).
% 11.89/2.01  
% 11.89/2.01  fof(f54,plain,(
% 11.89/2.01    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 11.89/2.01    inference(cnf_transformation,[],[f36])).
% 11.89/2.01  
% 11.89/2.01  fof(f12,axiom,(
% 11.89/2.01    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 11.89/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.89/2.01  
% 11.89/2.01  fof(f39,plain,(
% 11.89/2.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 11.89/2.01    inference(nnf_transformation,[],[f12])).
% 11.89/2.01  
% 11.89/2.01  fof(f40,plain,(
% 11.89/2.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.89/2.01    inference(rectify,[],[f39])).
% 11.89/2.01  
% 11.89/2.01  fof(f41,plain,(
% 11.89/2.01    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 11.89/2.01    introduced(choice_axiom,[])).
% 11.89/2.01  
% 11.89/2.01  fof(f42,plain,(
% 11.89/2.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.89/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).
% 11.89/2.01  
% 11.89/2.01  fof(f67,plain,(
% 11.89/2.01    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)) )),
% 11.89/2.01    inference(cnf_transformation,[],[f42])).
% 11.89/2.01  
% 11.89/2.01  fof(f13,axiom,(
% 11.89/2.01    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 11.89/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.89/2.01  
% 11.89/2.01  fof(f69,plain,(
% 11.89/2.01    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 11.89/2.01    inference(cnf_transformation,[],[f13])).
% 11.89/2.01  
% 11.89/2.01  fof(f14,axiom,(
% 11.89/2.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.89/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.89/2.01  
% 11.89/2.01  fof(f70,plain,(
% 11.89/2.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.89/2.01    inference(cnf_transformation,[],[f14])).
% 11.89/2.01  
% 11.89/2.01  fof(f15,axiom,(
% 11.89/2.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.89/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.89/2.01  
% 11.89/2.01  fof(f71,plain,(
% 11.89/2.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.89/2.01    inference(cnf_transformation,[],[f15])).
% 11.89/2.01  
% 11.89/2.01  fof(f16,axiom,(
% 11.89/2.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.89/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.89/2.01  
% 11.89/2.01  fof(f72,plain,(
% 11.89/2.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.89/2.01    inference(cnf_transformation,[],[f16])).
% 11.89/2.01  
% 11.89/2.01  fof(f17,axiom,(
% 11.89/2.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.89/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.89/2.01  
% 11.89/2.01  fof(f73,plain,(
% 11.89/2.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.89/2.01    inference(cnf_transformation,[],[f17])).
% 11.89/2.01  
% 11.89/2.01  fof(f18,axiom,(
% 11.89/2.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.89/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.89/2.01  
% 11.89/2.01  fof(f74,plain,(
% 11.89/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.89/2.01    inference(cnf_transformation,[],[f18])).
% 11.89/2.01  
% 11.89/2.01  fof(f19,axiom,(
% 11.89/2.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.89/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.89/2.01  
% 11.89/2.01  fof(f75,plain,(
% 11.89/2.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.89/2.01    inference(cnf_transformation,[],[f19])).
% 11.89/2.01  
% 11.89/2.01  fof(f85,plain,(
% 11.89/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.89/2.01    inference(definition_unfolding,[],[f74,f75])).
% 11.89/2.01  
% 11.89/2.01  fof(f86,plain,(
% 11.89/2.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.89/2.01    inference(definition_unfolding,[],[f73,f85])).
% 11.89/2.01  
% 11.89/2.01  fof(f87,plain,(
% 11.89/2.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.89/2.01    inference(definition_unfolding,[],[f72,f86])).
% 11.89/2.01  
% 11.89/2.01  fof(f88,plain,(
% 11.89/2.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.89/2.01    inference(definition_unfolding,[],[f71,f87])).
% 11.89/2.01  
% 11.89/2.01  fof(f89,plain,(
% 11.89/2.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.89/2.01    inference(definition_unfolding,[],[f70,f88])).
% 11.89/2.01  
% 11.89/2.01  fof(f93,plain,(
% 11.89/2.01    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.89/2.01    inference(definition_unfolding,[],[f69,f89])).
% 11.89/2.01  
% 11.89/2.01  fof(f104,plain,(
% 11.89/2.01    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 | sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)) )),
% 11.89/2.01    inference(definition_unfolding,[],[f67,f93])).
% 11.89/2.01  
% 11.89/2.01  fof(f23,conjecture,(
% 11.89/2.01    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 11.89/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.89/2.01  
% 11.89/2.01  fof(f24,negated_conjecture,(
% 11.89/2.01    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 11.89/2.01    inference(negated_conjecture,[],[f23])).
% 11.89/2.01  
% 11.89/2.01  fof(f29,plain,(
% 11.89/2.01    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 11.89/2.01    inference(ennf_transformation,[],[f24])).
% 11.89/2.01  
% 11.89/2.01  fof(f45,plain,(
% 11.89/2.01    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4) & (k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4) & (k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4) & k2_xboole_0(sK4,sK5) = k1_tarski(sK3))),
% 11.89/2.01    introduced(choice_axiom,[])).
% 11.89/2.01  
% 11.89/2.01  fof(f46,plain,(
% 11.89/2.01    (k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4) & (k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4) & (k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4) & k2_xboole_0(sK4,sK5) = k1_tarski(sK3)),
% 11.89/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f45])).
% 11.89/2.01  
% 11.89/2.01  fof(f81,plain,(
% 11.89/2.01    k2_xboole_0(sK4,sK5) = k1_tarski(sK3)),
% 11.89/2.01    inference(cnf_transformation,[],[f46])).
% 11.89/2.01  
% 11.89/2.01  fof(f21,axiom,(
% 11.89/2.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.89/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.89/2.01  
% 11.89/2.01  fof(f78,plain,(
% 11.89/2.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.89/2.01    inference(cnf_transformation,[],[f21])).
% 11.89/2.01  
% 11.89/2.01  fof(f90,plain,(
% 11.89/2.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 11.89/2.01    inference(definition_unfolding,[],[f78,f89])).
% 11.89/2.01  
% 11.89/2.01  fof(f114,plain,(
% 11.89/2.01    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))),
% 11.89/2.01    inference(definition_unfolding,[],[f81,f90,f93])).
% 11.89/2.01  
% 11.89/2.01  fof(f1,axiom,(
% 11.89/2.01    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 11.89/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.89/2.01  
% 11.89/2.01  fof(f30,plain,(
% 11.89/2.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.89/2.01    inference(nnf_transformation,[],[f1])).
% 11.89/2.01  
% 11.89/2.01  fof(f31,plain,(
% 11.89/2.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.89/2.01    inference(flattening,[],[f30])).
% 11.89/2.01  
% 11.89/2.01  fof(f32,plain,(
% 11.89/2.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.89/2.01    inference(rectify,[],[f31])).
% 11.89/2.01  
% 11.89/2.01  fof(f33,plain,(
% 11.89/2.01    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 11.89/2.01    introduced(choice_axiom,[])).
% 11.89/2.01  
% 11.89/2.01  fof(f34,plain,(
% 11.89/2.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.89/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 11.89/2.01  
% 11.89/2.01  fof(f48,plain,(
% 11.89/2.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 11.89/2.01    inference(cnf_transformation,[],[f34])).
% 11.89/2.01  
% 11.89/2.01  fof(f98,plain,(
% 11.89/2.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 11.89/2.01    inference(definition_unfolding,[],[f48,f90])).
% 11.89/2.01  
% 11.89/2.01  fof(f116,plain,(
% 11.89/2.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 11.89/2.01    inference(equality_resolution,[],[f98])).
% 11.89/2.01  
% 11.89/2.01  fof(f65,plain,(
% 11.89/2.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 11.89/2.01    inference(cnf_transformation,[],[f42])).
% 11.89/2.01  
% 11.89/2.01  fof(f106,plain,(
% 11.89/2.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 11.89/2.01    inference(definition_unfolding,[],[f65,f93])).
% 11.89/2.01  
% 11.89/2.01  fof(f122,plain,(
% 11.89/2.01    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 11.89/2.01    inference(equality_resolution,[],[f106])).
% 11.89/2.01  
% 11.89/2.01  fof(f49,plain,(
% 11.89/2.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 11.89/2.01    inference(cnf_transformation,[],[f34])).
% 11.89/2.01  
% 11.89/2.01  fof(f97,plain,(
% 11.89/2.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 11.89/2.01    inference(definition_unfolding,[],[f49,f90])).
% 11.89/2.01  
% 11.89/2.01  fof(f115,plain,(
% 11.89/2.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 11.89/2.01    inference(equality_resolution,[],[f97])).
% 11.89/2.01  
% 11.89/2.01  fof(f68,plain,(
% 11.89/2.01    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) )),
% 11.89/2.01    inference(cnf_transformation,[],[f42])).
% 11.89/2.01  
% 11.89/2.01  fof(f103,plain,(
% 11.89/2.01    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 | sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) )),
% 11.89/2.01    inference(definition_unfolding,[],[f68,f93])).
% 11.89/2.01  
% 11.89/2.01  fof(f66,plain,(
% 11.89/2.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 11.89/2.01    inference(cnf_transformation,[],[f42])).
% 11.89/2.01  
% 11.89/2.01  fof(f105,plain,(
% 11.89/2.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 11.89/2.01    inference(definition_unfolding,[],[f66,f93])).
% 11.89/2.01  
% 11.89/2.01  fof(f120,plain,(
% 11.89/2.01    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 11.89/2.01    inference(equality_resolution,[],[f105])).
% 11.89/2.01  
% 11.89/2.01  fof(f121,plain,(
% 11.89/2.01    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 11.89/2.01    inference(equality_resolution,[],[f120])).
% 11.89/2.01  
% 11.89/2.01  fof(f82,plain,(
% 11.89/2.01    k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4),
% 11.89/2.01    inference(cnf_transformation,[],[f46])).
% 11.89/2.01  
% 11.89/2.01  fof(f113,plain,(
% 11.89/2.01    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5 | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4),
% 11.89/2.01    inference(definition_unfolding,[],[f82,f93,f93])).
% 11.89/2.01  
% 11.89/2.01  fof(f83,plain,(
% 11.89/2.01    k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4),
% 11.89/2.01    inference(cnf_transformation,[],[f46])).
% 11.89/2.01  
% 11.89/2.01  fof(f112,plain,(
% 11.89/2.01    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5 | k1_xboole_0 != sK4),
% 11.89/2.01    inference(definition_unfolding,[],[f83,f93])).
% 11.89/2.01  
% 11.89/2.01  fof(f4,axiom,(
% 11.89/2.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.89/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.89/2.01  
% 11.89/2.01  fof(f37,plain,(
% 11.89/2.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.89/2.01    inference(nnf_transformation,[],[f4])).
% 11.89/2.01  
% 11.89/2.01  fof(f38,plain,(
% 11.89/2.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.89/2.01    inference(flattening,[],[f37])).
% 11.89/2.01  
% 11.89/2.01  fof(f57,plain,(
% 11.89/2.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.89/2.01    inference(cnf_transformation,[],[f38])).
% 11.89/2.01  
% 11.89/2.01  fof(f20,axiom,(
% 11.89/2.01    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 11.89/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.89/2.01  
% 11.89/2.01  fof(f43,plain,(
% 11.89/2.01    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 11.89/2.01    inference(nnf_transformation,[],[f20])).
% 11.89/2.01  
% 11.89/2.01  fof(f77,plain,(
% 11.89/2.01    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 11.89/2.01    inference(cnf_transformation,[],[f43])).
% 11.89/2.01  
% 11.89/2.01  fof(f107,plain,(
% 11.89/2.01    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 11.89/2.01    inference(definition_unfolding,[],[f77,f93])).
% 11.89/2.01  
% 11.89/2.01  fof(f55,plain,(
% 11.89/2.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.89/2.01    inference(cnf_transformation,[],[f38])).
% 11.89/2.01  
% 11.89/2.01  fof(f119,plain,(
% 11.89/2.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.89/2.01    inference(equality_resolution,[],[f55])).
% 11.89/2.01  
% 11.89/2.01  fof(f6,axiom,(
% 11.89/2.01    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 11.89/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.89/2.01  
% 11.89/2.01  fof(f27,plain,(
% 11.89/2.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 11.89/2.01    inference(ennf_transformation,[],[f6])).
% 11.89/2.01  
% 11.89/2.01  fof(f59,plain,(
% 11.89/2.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 11.89/2.01    inference(cnf_transformation,[],[f27])).
% 11.89/2.01  
% 11.89/2.01  fof(f101,plain,(
% 11.89/2.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) )),
% 11.89/2.01    inference(definition_unfolding,[],[f59,f90])).
% 11.89/2.01  
% 11.89/2.01  fof(f47,plain,(
% 11.89/2.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 11.89/2.01    inference(cnf_transformation,[],[f34])).
% 11.89/2.01  
% 11.89/2.01  fof(f99,plain,(
% 11.89/2.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 11.89/2.01    inference(definition_unfolding,[],[f47,f90])).
% 11.89/2.01  
% 11.89/2.01  fof(f117,plain,(
% 11.89/2.01    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 11.89/2.01    inference(equality_resolution,[],[f99])).
% 11.89/2.01  
% 11.89/2.01  fof(f84,plain,(
% 11.89/2.01    k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4),
% 11.89/2.01    inference(cnf_transformation,[],[f46])).
% 11.89/2.01  
% 11.89/2.01  fof(f111,plain,(
% 11.89/2.01    k1_xboole_0 != sK5 | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4),
% 11.89/2.01    inference(definition_unfolding,[],[f84,f93])).
% 11.89/2.01  
% 11.89/2.01  cnf(c_7,plain,
% 11.89/2.01      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 11.89/2.01      inference(cnf_transformation,[],[f54]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_849,plain,
% 11.89/2.01      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 11.89/2.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_17,plain,
% 11.89/2.01      ( r2_hidden(sK2(X0,X1),X1)
% 11.89/2.01      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 11.89/2.01      | sK2(X0,X1) = X0 ),
% 11.89/2.01      inference(cnf_transformation,[],[f104]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_843,plain,
% 11.89/2.01      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 11.89/2.01      | sK2(X0,X1) = X0
% 11.89/2.01      | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
% 11.89/2.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_27,negated_conjecture,
% 11.89/2.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
% 11.89/2.01      inference(cnf_transformation,[],[f114]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_4,plain,
% 11.89/2.01      ( ~ r2_hidden(X0,X1)
% 11.89/2.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 11.89/2.01      inference(cnf_transformation,[],[f116]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_851,plain,
% 11.89/2.01      ( r2_hidden(X0,X1) != iProver_top
% 11.89/2.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
% 11.89/2.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_24497,plain,
% 11.89/2.01      ( r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top
% 11.89/2.01      | r2_hidden(X0,sK4) != iProver_top ),
% 11.89/2.01      inference(superposition,[status(thm)],[c_27,c_851]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_19,plain,
% 11.89/2.01      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 11.89/2.01      inference(cnf_transformation,[],[f122]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_841,plain,
% 11.89/2.01      ( X0 = X1
% 11.89/2.01      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 11.89/2.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_28555,plain,
% 11.89/2.01      ( sK3 = X0 | r2_hidden(X0,sK4) != iProver_top ),
% 11.89/2.01      inference(superposition,[status(thm)],[c_24497,c_841]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_28561,plain,
% 11.89/2.01      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK4
% 11.89/2.01      | sK2(X0,sK4) = X0
% 11.89/2.01      | sK2(X0,sK4) = sK3 ),
% 11.89/2.01      inference(superposition,[status(thm)],[c_843,c_28555]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_3,plain,
% 11.89/2.01      ( ~ r2_hidden(X0,X1)
% 11.89/2.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 11.89/2.01      inference(cnf_transformation,[],[f115]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_852,plain,
% 11.89/2.01      ( r2_hidden(X0,X1) != iProver_top
% 11.89/2.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 11.89/2.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_29202,plain,
% 11.89/2.01      ( r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top
% 11.89/2.01      | r2_hidden(X0,sK5) != iProver_top ),
% 11.89/2.01      inference(superposition,[status(thm)],[c_27,c_852]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_31822,plain,
% 11.89/2.01      ( sK2(sK3,sK4) = sK3
% 11.89/2.01      | r2_hidden(X0,sK4) = iProver_top
% 11.89/2.01      | r2_hidden(X0,sK5) != iProver_top ),
% 11.89/2.01      inference(superposition,[status(thm)],[c_28561,c_29202]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_16,plain,
% 11.89/2.01      ( ~ r2_hidden(sK2(X0,X1),X1)
% 11.89/2.01      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 11.89/2.01      | sK2(X0,X1) != X0 ),
% 11.89/2.01      inference(cnf_transformation,[],[f103]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_933,plain,
% 11.89/2.01      ( ~ r2_hidden(sK2(sK3,sK5),sK5)
% 11.89/2.01      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
% 11.89/2.01      | sK2(sK3,sK5) != sK3 ),
% 11.89/2.01      inference(instantiation,[status(thm)],[c_16]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_937,plain,
% 11.89/2.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
% 11.89/2.01      | sK2(sK3,sK5) != sK3
% 11.89/2.01      | r2_hidden(sK2(sK3,sK5),sK5) != iProver_top ),
% 11.89/2.01      inference(predicate_to_equality,[status(thm)],[c_933]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_18,plain,
% 11.89/2.01      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 11.89/2.01      inference(cnf_transformation,[],[f121]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_7404,plain,
% 11.89/2.01      ( r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
% 11.89/2.01      inference(instantiation,[status(thm)],[c_18]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_435,plain,
% 11.89/2.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.89/2.01      theory(equality) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_6289,plain,
% 11.89/2.01      ( ~ r2_hidden(X0,X1)
% 11.89/2.01      | r2_hidden(sK2(sK3,sK5),sK5)
% 11.89/2.01      | sK2(sK3,sK5) != X0
% 11.89/2.01      | sK5 != X1 ),
% 11.89/2.01      inference(instantiation,[status(thm)],[c_435]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_20407,plain,
% 11.89/2.01      ( ~ r2_hidden(X0,sK5)
% 11.89/2.01      | r2_hidden(sK2(sK3,sK5),sK5)
% 11.89/2.01      | sK2(sK3,sK5) != X0
% 11.89/2.01      | sK5 != sK5 ),
% 11.89/2.01      inference(instantiation,[status(thm)],[c_6289]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_20408,plain,
% 11.89/2.01      ( sK2(sK3,sK5) != X0
% 11.89/2.01      | sK5 != sK5
% 11.89/2.01      | r2_hidden(X0,sK5) != iProver_top
% 11.89/2.01      | r2_hidden(sK2(sK3,sK5),sK5) = iProver_top ),
% 11.89/2.01      inference(predicate_to_equality,[status(thm)],[c_20407]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_20410,plain,
% 11.89/2.01      ( sK2(sK3,sK5) != sK3
% 11.89/2.01      | sK5 != sK5
% 11.89/2.01      | r2_hidden(sK2(sK3,sK5),sK5) = iProver_top
% 11.89/2.01      | r2_hidden(sK3,sK5) != iProver_top ),
% 11.89/2.01      inference(instantiation,[status(thm)],[c_20408]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_3556,plain,
% 11.89/2.01      ( ~ r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 11.89/2.01      | sK5 = X0 ),
% 11.89/2.01      inference(instantiation,[status(thm)],[c_19]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_21270,plain,
% 11.89/2.01      ( ~ r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 11.89/2.01      | sK5 = sK5 ),
% 11.89/2.01      inference(instantiation,[status(thm)],[c_3556]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_6352,plain,
% 11.89/2.01      ( ~ r2_hidden(X0,X1) | r2_hidden(sK3,sK5) | sK3 != X0 | sK5 != X1 ),
% 11.89/2.01      inference(instantiation,[status(thm)],[c_435]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_28631,plain,
% 11.89/2.01      ( ~ r2_hidden(X0,sK5)
% 11.89/2.01      | r2_hidden(sK3,sK5)
% 11.89/2.01      | sK3 != X0
% 11.89/2.01      | sK5 != sK5 ),
% 11.89/2.01      inference(instantiation,[status(thm)],[c_6352]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_28632,plain,
% 11.89/2.01      ( sK3 != X0
% 11.89/2.01      | sK5 != sK5
% 11.89/2.01      | r2_hidden(X0,sK5) != iProver_top
% 11.89/2.01      | r2_hidden(sK3,sK5) = iProver_top ),
% 11.89/2.01      inference(predicate_to_equality,[status(thm)],[c_28631]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_26,negated_conjecture,
% 11.89/2.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4
% 11.89/2.01      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5 ),
% 11.89/2.01      inference(cnf_transformation,[],[f113]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_28938,plain,
% 11.89/2.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5
% 11.89/2.01      | sK2(sK3,sK4) = sK3 ),
% 11.89/2.01      inference(superposition,[status(thm)],[c_28561,c_26]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_25,negated_conjecture,
% 11.89/2.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5
% 11.89/2.01      | k1_xboole_0 != sK4 ),
% 11.89/2.01      inference(cnf_transformation,[],[f112]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_8,plain,
% 11.89/2.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.89/2.01      inference(cnf_transformation,[],[f57]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_907,plain,
% 11.89/2.01      ( ~ r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)
% 11.89/2.01      | ~ r1_tarski(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))
% 11.89/2.01      | k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4 ),
% 11.89/2.01      inference(instantiation,[status(thm)],[c_8]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_908,plain,
% 11.89/2.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK4
% 11.89/2.01      | r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4) != iProver_top
% 11.89/2.01      | r1_tarski(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
% 11.89/2.01      inference(predicate_to_equality,[status(thm)],[c_907]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_20,plain,
% 11.89/2.01      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 11.89/2.01      | ~ r2_hidden(X0,X1) ),
% 11.89/2.01      inference(cnf_transformation,[],[f107]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_959,plain,
% 11.89/2.01      ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)
% 11.89/2.01      | ~ r2_hidden(sK3,sK4) ),
% 11.89/2.01      inference(instantiation,[status(thm)],[c_20]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_960,plain,
% 11.89/2.01      ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4) = iProver_top
% 11.89/2.01      | r2_hidden(sK3,sK4) != iProver_top ),
% 11.89/2.01      inference(predicate_to_equality,[status(thm)],[c_959]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_432,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_897,plain,
% 11.89/2.01      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 11.89/2.01      inference(instantiation,[status(thm)],[c_432]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_1244,plain,
% 11.89/2.01      ( sK4 != k1_xboole_0
% 11.89/2.01      | k1_xboole_0 = sK4
% 11.89/2.01      | k1_xboole_0 != k1_xboole_0 ),
% 11.89/2.01      inference(instantiation,[status(thm)],[c_897]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_10,plain,
% 11.89/2.01      ( r1_tarski(X0,X0) ),
% 11.89/2.01      inference(cnf_transformation,[],[f119]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_1968,plain,
% 11.89/2.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 11.89/2.01      inference(instantiation,[status(thm)],[c_10]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_1234,plain,
% 11.89/2.01      ( ~ r1_tarski(X0,k1_xboole_0)
% 11.89/2.01      | ~ r1_tarski(k1_xboole_0,X0)
% 11.89/2.01      | k1_xboole_0 = X0 ),
% 11.89/2.01      inference(instantiation,[status(thm)],[c_8]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_2039,plain,
% 11.89/2.01      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 11.89/2.01      | k1_xboole_0 = k1_xboole_0 ),
% 11.89/2.01      inference(instantiation,[status(thm)],[c_1234]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_847,plain,
% 11.89/2.01      ( r1_tarski(X0,X0) = iProver_top ),
% 11.89/2.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_11,plain,
% 11.89/2.01      ( r1_tarski(X0,X1)
% 11.89/2.01      | ~ r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ),
% 11.89/2.01      inference(cnf_transformation,[],[f101]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_846,plain,
% 11.89/2.01      ( r1_tarski(X0,X1) = iProver_top
% 11.89/2.01      | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) != iProver_top ),
% 11.89/2.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_17668,plain,
% 11.89/2.01      ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0) != iProver_top
% 11.89/2.01      | r1_tarski(sK4,X0) = iProver_top ),
% 11.89/2.01      inference(superposition,[status(thm)],[c_27,c_846]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_19243,plain,
% 11.89/2.01      ( r1_tarski(sK4,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 11.89/2.01      inference(superposition,[status(thm)],[c_847,c_17668]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_28560,plain,
% 11.89/2.01      ( sK1(sK4) = sK3 | sK4 = k1_xboole_0 ),
% 11.89/2.01      inference(superposition,[status(thm)],[c_849,c_28555]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_28671,plain,
% 11.89/2.01      ( sK4 = k1_xboole_0 | r2_hidden(sK3,sK4) = iProver_top ),
% 11.89/2.01      inference(superposition,[status(thm)],[c_28560,c_849]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_29118,plain,
% 11.89/2.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK5 ),
% 11.89/2.01      inference(global_propositional_subsumption,
% 11.89/2.01                [status(thm)],
% 11.89/2.01                [c_28938,c_26,c_25,c_908,c_960,c_1244,c_1968,c_2039,
% 11.89/2.01                 c_19243,c_28671]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_31823,plain,
% 11.89/2.01      ( sK3 = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 11.89/2.01      inference(superposition,[status(thm)],[c_29202,c_841]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_31934,plain,
% 11.89/2.01      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK5
% 11.89/2.01      | sK2(X0,sK5) = X0
% 11.89/2.01      | sK2(X0,sK5) = sK3 ),
% 11.89/2.01      inference(superposition,[status(thm)],[c_843,c_31823]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_31935,plain,
% 11.89/2.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = sK5
% 11.89/2.01      | sK2(sK3,sK5) = sK3 ),
% 11.89/2.01      inference(instantiation,[status(thm)],[c_31934]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_32082,plain,
% 11.89/2.01      ( r2_hidden(X0,sK5) != iProver_top ),
% 11.89/2.01      inference(global_propositional_subsumption,
% 11.89/2.01                [status(thm)],
% 11.89/2.01                [c_31822,c_26,c_25,c_908,c_937,c_960,c_1244,c_1968,
% 11.89/2.01                 c_2039,c_7404,c_19243,c_20410,c_21270,c_28632,c_28671,
% 11.89/2.01                 c_31823,c_31935]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_32088,plain,
% 11.89/2.01      ( sK5 = k1_xboole_0 ),
% 11.89/2.01      inference(superposition,[status(thm)],[c_849,c_32082]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_842,plain,
% 11.89/2.01      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
% 11.89/2.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_5,plain,
% 11.89/2.01      ( r2_hidden(X0,X1)
% 11.89/2.01      | r2_hidden(X0,X2)
% 11.89/2.01      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 11.89/2.01      inference(cnf_transformation,[],[f117]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_850,plain,
% 11.89/2.01      ( r2_hidden(X0,X1) = iProver_top
% 11.89/2.01      | r2_hidden(X0,X2) = iProver_top
% 11.89/2.01      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
% 11.89/2.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_20483,plain,
% 11.89/2.01      ( r2_hidden(X0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top
% 11.89/2.01      | r2_hidden(X0,sK4) = iProver_top
% 11.89/2.01      | r2_hidden(X0,sK5) = iProver_top ),
% 11.89/2.01      inference(superposition,[status(thm)],[c_27,c_850]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_24163,plain,
% 11.89/2.01      ( r2_hidden(sK3,sK4) = iProver_top
% 11.89/2.01      | r2_hidden(sK3,sK5) = iProver_top ),
% 11.89/2.01      inference(superposition,[status(thm)],[c_842,c_20483]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_885,plain,
% 11.89/2.01      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 11.89/2.01      inference(instantiation,[status(thm)],[c_432]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_5348,plain,
% 11.89/2.01      ( sK5 != k1_xboole_0
% 11.89/2.01      | k1_xboole_0 = sK5
% 11.89/2.01      | k1_xboole_0 != k1_xboole_0 ),
% 11.89/2.01      inference(instantiation,[status(thm)],[c_885]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(c_24,negated_conjecture,
% 11.89/2.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != sK4
% 11.89/2.01      | k1_xboole_0 != sK5 ),
% 11.89/2.01      inference(cnf_transformation,[],[f111]) ).
% 11.89/2.01  
% 11.89/2.01  cnf(contradiction,plain,
% 11.89/2.01      ( $false ),
% 11.89/2.01      inference(minisat,
% 11.89/2.01                [status(thm)],
% 11.89/2.01                [c_32088,c_31935,c_29118,c_24163,c_21270,c_20410,c_19243,
% 11.89/2.01                 c_7404,c_5348,c_2039,c_1968,c_960,c_937,c_908,c_24]) ).
% 11.89/2.01  
% 11.89/2.01  
% 11.89/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.89/2.01  
% 11.89/2.01  ------                               Statistics
% 11.89/2.01  
% 11.89/2.01  ------ General
% 11.89/2.01  
% 11.89/2.01  abstr_ref_over_cycles:                  0
% 11.89/2.01  abstr_ref_under_cycles:                 0
% 11.89/2.01  gc_basic_clause_elim:                   0
% 11.89/2.01  forced_gc_time:                         0
% 11.89/2.01  parsing_time:                           0.01
% 11.89/2.01  unif_index_cands_time:                  0.
% 11.89/2.01  unif_index_add_time:                    0.
% 11.89/2.01  orderings_time:                         0.
% 11.89/2.01  out_proof_time:                         0.015
% 11.89/2.01  total_time:                             1.337
% 11.89/2.01  num_of_symbols:                         43
% 11.89/2.01  num_of_terms:                           57705
% 11.89/2.01  
% 11.89/2.01  ------ Preprocessing
% 11.89/2.01  
% 11.89/2.01  num_of_splits:                          0
% 11.89/2.01  num_of_split_atoms:                     0
% 11.89/2.01  num_of_reused_defs:                     0
% 11.89/2.01  num_eq_ax_congr_red:                    21
% 11.89/2.01  num_of_sem_filtered_clauses:            1
% 11.89/2.01  num_of_subtypes:                        0
% 11.89/2.01  monotx_restored_types:                  0
% 11.89/2.01  sat_num_of_epr_types:                   0
% 11.89/2.01  sat_num_of_non_cyclic_types:            0
% 11.89/2.01  sat_guarded_non_collapsed_types:        0
% 11.89/2.01  num_pure_diseq_elim:                    0
% 11.89/2.01  simp_replaced_by:                       0
% 11.89/2.01  res_preprocessed:                       123
% 11.89/2.01  prep_upred:                             0
% 11.89/2.01  prep_unflattend:                        0
% 11.89/2.01  smt_new_axioms:                         0
% 11.89/2.01  pred_elim_cands:                        2
% 11.89/2.01  pred_elim:                              0
% 11.89/2.01  pred_elim_cl:                           0
% 11.89/2.01  pred_elim_cycles:                       2
% 11.89/2.01  merged_defs:                            8
% 11.89/2.01  merged_defs_ncl:                        0
% 11.89/2.01  bin_hyper_res:                          8
% 11.89/2.01  prep_cycles:                            4
% 11.89/2.01  pred_elim_time:                         0.001
% 11.89/2.01  splitting_time:                         0.
% 11.89/2.01  sem_filter_time:                        0.
% 11.89/2.01  monotx_time:                            0.
% 11.89/2.01  subtype_inf_time:                       0.
% 11.89/2.01  
% 11.89/2.01  ------ Problem properties
% 11.89/2.01  
% 11.89/2.01  clauses:                                27
% 11.89/2.01  conjectures:                            4
% 11.89/2.01  epr:                                    2
% 11.89/2.01  horn:                                   22
% 11.89/2.01  ground:                                 4
% 11.89/2.01  unary:                                  8
% 11.89/2.01  binary:                                 12
% 11.89/2.01  lits:                                   54
% 11.89/2.01  lits_eq:                                25
% 11.89/2.01  fd_pure:                                0
% 11.89/2.01  fd_pseudo:                              0
% 11.89/2.01  fd_cond:                                1
% 11.89/2.01  fd_pseudo_cond:                         7
% 11.89/2.01  ac_symbols:                             1
% 11.89/2.01  
% 11.89/2.01  ------ Propositional Solver
% 11.89/2.01  
% 11.89/2.01  prop_solver_calls:                      30
% 11.89/2.01  prop_fast_solver_calls:                 727
% 11.89/2.01  smt_solver_calls:                       0
% 11.89/2.01  smt_fast_solver_calls:                  0
% 11.89/2.01  prop_num_of_clauses:                    3974
% 11.89/2.01  prop_preprocess_simplified:             8700
% 11.89/2.01  prop_fo_subsumed:                       3
% 11.89/2.01  prop_solver_time:                       0.
% 11.89/2.01  smt_solver_time:                        0.
% 11.89/2.01  smt_fast_solver_time:                   0.
% 11.89/2.01  prop_fast_solver_time:                  0.
% 11.89/2.01  prop_unsat_core_time:                   0.
% 11.89/2.01  
% 11.89/2.01  ------ QBF
% 11.89/2.01  
% 11.89/2.01  qbf_q_res:                              0
% 11.89/2.01  qbf_num_tautologies:                    0
% 11.89/2.01  qbf_prep_cycles:                        0
% 11.89/2.01  
% 11.89/2.01  ------ BMC1
% 11.89/2.01  
% 11.89/2.01  bmc1_current_bound:                     -1
% 11.89/2.01  bmc1_last_solved_bound:                 -1
% 11.89/2.01  bmc1_unsat_core_size:                   -1
% 11.89/2.01  bmc1_unsat_core_parents_size:           -1
% 11.89/2.01  bmc1_merge_next_fun:                    0
% 11.89/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.89/2.01  
% 11.89/2.01  ------ Instantiation
% 11.89/2.01  
% 11.89/2.01  inst_num_of_clauses:                    963
% 11.89/2.01  inst_num_in_passive:                    218
% 11.89/2.01  inst_num_in_active:                     385
% 11.89/2.01  inst_num_in_unprocessed:                360
% 11.89/2.01  inst_num_of_loops:                      610
% 11.89/2.01  inst_num_of_learning_restarts:          0
% 11.89/2.01  inst_num_moves_active_passive:          223
% 11.89/2.01  inst_lit_activity:                      0
% 11.89/2.01  inst_lit_activity_moves:                0
% 11.89/2.01  inst_num_tautologies:                   0
% 11.89/2.01  inst_num_prop_implied:                  0
% 11.89/2.01  inst_num_existing_simplified:           0
% 11.89/2.01  inst_num_eq_res_simplified:             0
% 11.89/2.01  inst_num_child_elim:                    0
% 11.89/2.01  inst_num_of_dismatching_blockings:      530
% 11.89/2.01  inst_num_of_non_proper_insts:           1310
% 11.89/2.01  inst_num_of_duplicates:                 0
% 11.89/2.01  inst_inst_num_from_inst_to_res:         0
% 11.89/2.01  inst_dismatching_checking_time:         0.
% 11.89/2.01  
% 11.89/2.01  ------ Resolution
% 11.89/2.01  
% 11.89/2.01  res_num_of_clauses:                     0
% 11.89/2.01  res_num_in_passive:                     0
% 11.89/2.01  res_num_in_active:                      0
% 11.89/2.01  res_num_of_loops:                       127
% 11.89/2.01  res_forward_subset_subsumed:            107
% 11.89/2.01  res_backward_subset_subsumed:           0
% 11.89/2.01  res_forward_subsumed:                   0
% 11.89/2.01  res_backward_subsumed:                  0
% 11.89/2.01  res_forward_subsumption_resolution:     0
% 11.89/2.01  res_backward_subsumption_resolution:    0
% 11.89/2.01  res_clause_to_clause_subsumption:       56662
% 11.89/2.01  res_orphan_elimination:                 0
% 11.89/2.01  res_tautology_del:                      135
% 11.89/2.01  res_num_eq_res_simplified:              0
% 11.89/2.01  res_num_sel_changes:                    0
% 11.89/2.01  res_moves_from_active_to_pass:          0
% 11.89/2.01  
% 11.89/2.01  ------ Superposition
% 11.89/2.01  
% 11.89/2.01  sup_time_total:                         0.
% 11.89/2.01  sup_time_generating:                    0.
% 11.89/2.01  sup_time_sim_full:                      0.
% 11.89/2.01  sup_time_sim_immed:                     0.
% 11.89/2.01  
% 11.89/2.01  sup_num_of_clauses:                     1046
% 11.89/2.01  sup_num_in_active:                      112
% 11.89/2.01  sup_num_in_passive:                     934
% 11.89/2.01  sup_num_of_loops:                       120
% 11.89/2.01  sup_fw_superposition:                   9346
% 11.89/2.01  sup_bw_superposition:                   6143
% 11.89/2.01  sup_immediate_simplified:               7721
% 11.89/2.01  sup_given_eliminated:                   3
% 11.89/2.01  comparisons_done:                       0
% 11.89/2.01  comparisons_avoided:                    15
% 11.89/2.01  
% 11.89/2.01  ------ Simplifications
% 11.89/2.01  
% 11.89/2.01  
% 11.89/2.01  sim_fw_subset_subsumed:                 4
% 11.89/2.01  sim_bw_subset_subsumed:                 2
% 11.89/2.01  sim_fw_subsumed:                        215
% 11.89/2.01  sim_bw_subsumed:                        4
% 11.89/2.01  sim_fw_subsumption_res:                 0
% 11.89/2.01  sim_bw_subsumption_res:                 0
% 11.89/2.01  sim_tautology_del:                      15
% 11.89/2.01  sim_eq_tautology_del:                   770
% 11.89/2.01  sim_eq_res_simp:                        0
% 11.89/2.01  sim_fw_demodulated:                     7302
% 11.89/2.01  sim_bw_demodulated:                     18
% 11.89/2.01  sim_light_normalised:                   1775
% 11.89/2.01  sim_joinable_taut:                      446
% 11.89/2.01  sim_joinable_simp:                      0
% 11.89/2.01  sim_ac_normalised:                      0
% 11.89/2.01  sim_smt_subsumption:                    0
% 11.89/2.01  
%------------------------------------------------------------------------------
