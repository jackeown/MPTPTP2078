%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:27 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :  129 (2436 expanded)
%              Number of clauses        :   52 ( 234 expanded)
%              Number of leaves         :   18 ( 734 expanded)
%              Depth                    :   21
%              Number of atoms          :  413 (5298 expanded)
%              Number of equality atoms :  264 (4430 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK2(X0,X1) = X0
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f72])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f73])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
      | sK2(X0,X1) = X0
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f52,f75])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2))
      | k3_enumset1(X2,X2,X2,X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f65,f73,f75])).

fof(f110,plain,(
    ! [X2,X1] : r1_tarski(k3_enumset1(X2,X2,X2,X2,X2),k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f93])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,
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

fof(f39,plain,
    ( ( k1_xboole_0 != sK5
      | k1_tarski(sK3) != sK4 )
    & ( k1_tarski(sK3) != sK5
      | k1_xboole_0 != sK4 )
    & ( k1_tarski(sK3) != sK5
      | k1_tarski(sK3) != sK4 )
    & k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f38])).

fof(f68,plain,(
    k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f67,f73])).

fof(f100,plain,(
    k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(definition_unfolding,[],[f68,f74,f75])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f47,f74])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k3_enumset1(X1,X1,X1,X1,X2) = X0
      | k3_enumset1(X2,X2,X2,X2,X2) = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f62,f73,f75,f75,f73])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f42,f74])).

fof(f101,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f79])).

fof(f71,plain,
    ( k1_xboole_0 != sK5
    | k1_tarski(sK3) != sK4 ),
    inference(cnf_transformation,[],[f39])).

fof(f97,plain,
    ( k1_xboole_0 != sK5
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4 ),
    inference(definition_unfolding,[],[f71,f75])).

fof(f69,plain,
    ( k1_tarski(sK3) != sK5
    | k1_tarski(sK3) != sK4 ),
    inference(cnf_transformation,[],[f39])).

fof(f99,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4 ),
    inference(definition_unfolding,[],[f69,f75,f75])).

fof(f70,plain,
    ( k1_tarski(sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f39])).

fof(f98,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(definition_unfolding,[],[f70,f75])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f34])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f59,f75,f75])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f28])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f50,f75])).

fof(f106,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f87])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK2(X0,X1) != X0
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
      | sK2(X0,X1) != X0
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f53,f75])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f74])).

cnf(c_11,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | k3_enumset1(X0,X0,X0,X0,X0) = X1
    | sK2(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_643,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | sK2(X0,X1) = X0
    | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_19,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_635,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_26,negated_conjecture,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_647,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1435,plain,
    ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_647])).

cnf(c_1450,plain,
    ( r1_tarski(sK4,k3_enumset1(X0,X0,X0,X0,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_635,c_1435])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2))
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | k3_enumset1(X1,X1,X1,X1,X2) = X0
    | k3_enumset1(X2,X2,X2,X2,X2) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_632,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | k3_enumset1(X0,X0,X0,X0,X2) = X1
    | k3_enumset1(X2,X2,X2,X2,X2) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k3_enumset1(X0,X0,X0,X0,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1568,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = sK4
    | k3_enumset1(X0,X0,X0,X0,sK3) = sK4
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1450,c_632])).

cnf(c_1580,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4
    | sK4 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1568])).

cnf(c_1772,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1568,c_1580])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_651,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2110,plain,
    ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_651])).

cnf(c_2336,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1772,c_2110])).

cnf(c_2990,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = sK5
    | sK2(X0,sK5) = X0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2(X0,sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_643,c_2336])).

cnf(c_23,negated_conjecture,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1789,plain,
    ( sK4 = k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1772,c_23])).

cnf(c_25,negated_conjecture,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1787,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1772,c_25])).

cnf(c_24,negated_conjecture,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_881,plain,
    ( ~ r1_tarski(sK4,k3_enumset1(X0,X0,X0,X0,X0))
    | k3_enumset1(X0,X0,X0,X0,X0) = sK4
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_883,plain,
    ( ~ r1_tarski(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_881])).

cnf(c_1456,plain,
    ( r1_tarski(sK4,k3_enumset1(X0,X0,X0,X0,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1450])).

cnf(c_1458,plain,
    ( r1_tarski(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_1456])).

cnf(c_1998,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1787,c_25,c_24,c_883,c_1458])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_648,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_641,plain,
    ( X0 = X1
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2337,plain,
    ( sK3 = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2110,c_641])).

cnf(c_2460,plain,
    ( sK1(sK5) = sK3
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_648,c_2337])).

cnf(c_2704,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2460,c_648])).

cnf(c_2991,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = sK5
    | sK2(X0,sK5) = X0
    | sK2(X0,sK5) = sK3 ),
    inference(superposition,[status(thm)],[c_643,c_2337])).

cnf(c_3652,plain,
    ( sK2(sK3,sK5) = sK3 ),
    inference(superposition,[status(thm)],[c_2991,c_1998])).

cnf(c_10,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | k3_enumset1(X0,X0,X0,X0,X0) = X1
    | sK2(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_644,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | sK2(X0,X1) != X0
    | r2_hidden(sK2(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3794,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK5
    | r2_hidden(sK2(sK3,sK5),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3652,c_644])).

cnf(c_3798,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK5
    | r2_hidden(sK3,sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3794,c_3652])).

cnf(c_3961,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2990,c_25,c_24,c_883,c_1458,c_1789,c_2704,c_3798])).

cnf(c_3976,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK5)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_3961,c_26])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_645,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_646,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1327,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_645,c_646])).

cnf(c_3983,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK5 ),
    inference(demodulation,[status(thm)],[c_3976,c_1327])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3983,c_1998])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:01:12 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 2.27/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/0.99  
% 2.27/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.27/0.99  
% 2.27/0.99  ------  iProver source info
% 2.27/0.99  
% 2.27/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.27/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.27/0.99  git: non_committed_changes: false
% 2.27/0.99  git: last_make_outside_of_git: false
% 2.27/0.99  
% 2.27/0.99  ------ 
% 2.27/0.99  
% 2.27/0.99  ------ Input Options
% 2.27/0.99  
% 2.27/0.99  --out_options                           all
% 2.27/0.99  --tptp_safe_out                         true
% 2.27/0.99  --problem_path                          ""
% 2.27/0.99  --include_path                          ""
% 2.27/0.99  --clausifier                            res/vclausify_rel
% 2.27/0.99  --clausifier_options                    --mode clausify
% 2.27/0.99  --stdin                                 false
% 2.27/0.99  --stats_out                             all
% 2.27/0.99  
% 2.27/0.99  ------ General Options
% 2.27/0.99  
% 2.27/0.99  --fof                                   false
% 2.27/0.99  --time_out_real                         305.
% 2.27/0.99  --time_out_virtual                      -1.
% 2.27/0.99  --symbol_type_check                     false
% 2.27/0.99  --clausify_out                          false
% 2.27/0.99  --sig_cnt_out                           false
% 2.27/0.99  --trig_cnt_out                          false
% 2.27/0.99  --trig_cnt_out_tolerance                1.
% 2.27/0.99  --trig_cnt_out_sk_spl                   false
% 2.27/0.99  --abstr_cl_out                          false
% 2.27/0.99  
% 2.27/0.99  ------ Global Options
% 2.27/0.99  
% 2.27/0.99  --schedule                              default
% 2.27/0.99  --add_important_lit                     false
% 2.27/0.99  --prop_solver_per_cl                    1000
% 2.27/0.99  --min_unsat_core                        false
% 2.27/0.99  --soft_assumptions                      false
% 2.27/0.99  --soft_lemma_size                       3
% 2.27/0.99  --prop_impl_unit_size                   0
% 2.27/0.99  --prop_impl_unit                        []
% 2.27/0.99  --share_sel_clauses                     true
% 2.27/0.99  --reset_solvers                         false
% 2.27/0.99  --bc_imp_inh                            [conj_cone]
% 2.27/0.99  --conj_cone_tolerance                   3.
% 2.27/0.99  --extra_neg_conj                        none
% 2.27/0.99  --large_theory_mode                     true
% 2.27/0.99  --prolific_symb_bound                   200
% 2.27/0.99  --lt_threshold                          2000
% 2.27/0.99  --clause_weak_htbl                      true
% 2.27/0.99  --gc_record_bc_elim                     false
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing Options
% 2.27/0.99  
% 2.27/0.99  --preprocessing_flag                    true
% 2.27/0.99  --time_out_prep_mult                    0.1
% 2.27/0.99  --splitting_mode                        input
% 2.27/0.99  --splitting_grd                         true
% 2.27/0.99  --splitting_cvd                         false
% 2.27/0.99  --splitting_cvd_svl                     false
% 2.27/0.99  --splitting_nvd                         32
% 2.27/0.99  --sub_typing                            true
% 2.27/0.99  --prep_gs_sim                           true
% 2.27/0.99  --prep_unflatten                        true
% 2.27/0.99  --prep_res_sim                          true
% 2.27/0.99  --prep_upred                            true
% 2.27/0.99  --prep_sem_filter                       exhaustive
% 2.27/0.99  --prep_sem_filter_out                   false
% 2.27/0.99  --pred_elim                             true
% 2.27/0.99  --res_sim_input                         true
% 2.27/0.99  --eq_ax_congr_red                       true
% 2.27/0.99  --pure_diseq_elim                       true
% 2.27/0.99  --brand_transform                       false
% 2.27/0.99  --non_eq_to_eq                          false
% 2.27/0.99  --prep_def_merge                        true
% 2.27/0.99  --prep_def_merge_prop_impl              false
% 2.27/0.99  --prep_def_merge_mbd                    true
% 2.27/0.99  --prep_def_merge_tr_red                 false
% 2.27/0.99  --prep_def_merge_tr_cl                  false
% 2.27/0.99  --smt_preprocessing                     true
% 2.27/0.99  --smt_ac_axioms                         fast
% 2.27/0.99  --preprocessed_out                      false
% 2.27/0.99  --preprocessed_stats                    false
% 2.27/0.99  
% 2.27/0.99  ------ Abstraction refinement Options
% 2.27/0.99  
% 2.27/0.99  --abstr_ref                             []
% 2.27/0.99  --abstr_ref_prep                        false
% 2.27/0.99  --abstr_ref_until_sat                   false
% 2.27/0.99  --abstr_ref_sig_restrict                funpre
% 2.27/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/0.99  --abstr_ref_under                       []
% 2.27/0.99  
% 2.27/0.99  ------ SAT Options
% 2.27/0.99  
% 2.27/0.99  --sat_mode                              false
% 2.27/0.99  --sat_fm_restart_options                ""
% 2.27/0.99  --sat_gr_def                            false
% 2.27/0.99  --sat_epr_types                         true
% 2.27/0.99  --sat_non_cyclic_types                  false
% 2.27/0.99  --sat_finite_models                     false
% 2.27/0.99  --sat_fm_lemmas                         false
% 2.27/0.99  --sat_fm_prep                           false
% 2.27/0.99  --sat_fm_uc_incr                        true
% 2.27/0.99  --sat_out_model                         small
% 2.27/0.99  --sat_out_clauses                       false
% 2.27/0.99  
% 2.27/0.99  ------ QBF Options
% 2.27/0.99  
% 2.27/0.99  --qbf_mode                              false
% 2.27/0.99  --qbf_elim_univ                         false
% 2.27/0.99  --qbf_dom_inst                          none
% 2.27/0.99  --qbf_dom_pre_inst                      false
% 2.27/0.99  --qbf_sk_in                             false
% 2.27/0.99  --qbf_pred_elim                         true
% 2.27/0.99  --qbf_split                             512
% 2.27/0.99  
% 2.27/0.99  ------ BMC1 Options
% 2.27/0.99  
% 2.27/0.99  --bmc1_incremental                      false
% 2.27/0.99  --bmc1_axioms                           reachable_all
% 2.27/0.99  --bmc1_min_bound                        0
% 2.27/0.99  --bmc1_max_bound                        -1
% 2.27/0.99  --bmc1_max_bound_default                -1
% 2.27/0.99  --bmc1_symbol_reachability              true
% 2.27/0.99  --bmc1_property_lemmas                  false
% 2.27/0.99  --bmc1_k_induction                      false
% 2.27/0.99  --bmc1_non_equiv_states                 false
% 2.27/0.99  --bmc1_deadlock                         false
% 2.27/0.99  --bmc1_ucm                              false
% 2.27/0.99  --bmc1_add_unsat_core                   none
% 2.27/0.99  --bmc1_unsat_core_children              false
% 2.27/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/0.99  --bmc1_out_stat                         full
% 2.27/0.99  --bmc1_ground_init                      false
% 2.27/0.99  --bmc1_pre_inst_next_state              false
% 2.27/0.99  --bmc1_pre_inst_state                   false
% 2.27/0.99  --bmc1_pre_inst_reach_state             false
% 2.27/0.99  --bmc1_out_unsat_core                   false
% 2.27/0.99  --bmc1_aig_witness_out                  false
% 2.27/0.99  --bmc1_verbose                          false
% 2.27/0.99  --bmc1_dump_clauses_tptp                false
% 2.27/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.27/0.99  --bmc1_dump_file                        -
% 2.27/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.27/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.27/0.99  --bmc1_ucm_extend_mode                  1
% 2.27/0.99  --bmc1_ucm_init_mode                    2
% 2.27/0.99  --bmc1_ucm_cone_mode                    none
% 2.27/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.27/0.99  --bmc1_ucm_relax_model                  4
% 2.27/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.27/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/0.99  --bmc1_ucm_layered_model                none
% 2.27/0.99  --bmc1_ucm_max_lemma_size               10
% 2.27/0.99  
% 2.27/0.99  ------ AIG Options
% 2.27/0.99  
% 2.27/0.99  --aig_mode                              false
% 2.27/0.99  
% 2.27/0.99  ------ Instantiation Options
% 2.27/0.99  
% 2.27/0.99  --instantiation_flag                    true
% 2.27/0.99  --inst_sos_flag                         false
% 2.27/0.99  --inst_sos_phase                        true
% 2.27/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/0.99  --inst_lit_sel_side                     num_symb
% 2.27/0.99  --inst_solver_per_active                1400
% 2.27/0.99  --inst_solver_calls_frac                1.
% 2.27/0.99  --inst_passive_queue_type               priority_queues
% 2.27/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/0.99  --inst_passive_queues_freq              [25;2]
% 2.27/0.99  --inst_dismatching                      true
% 2.27/0.99  --inst_eager_unprocessed_to_passive     true
% 2.27/0.99  --inst_prop_sim_given                   true
% 2.27/0.99  --inst_prop_sim_new                     false
% 2.27/0.99  --inst_subs_new                         false
% 2.27/0.99  --inst_eq_res_simp                      false
% 2.27/0.99  --inst_subs_given                       false
% 2.27/0.99  --inst_orphan_elimination               true
% 2.27/0.99  --inst_learning_loop_flag               true
% 2.27/0.99  --inst_learning_start                   3000
% 2.27/0.99  --inst_learning_factor                  2
% 2.27/0.99  --inst_start_prop_sim_after_learn       3
% 2.27/0.99  --inst_sel_renew                        solver
% 2.27/0.99  --inst_lit_activity_flag                true
% 2.27/0.99  --inst_restr_to_given                   false
% 2.27/0.99  --inst_activity_threshold               500
% 2.27/0.99  --inst_out_proof                        true
% 2.27/0.99  
% 2.27/0.99  ------ Resolution Options
% 2.27/0.99  
% 2.27/0.99  --resolution_flag                       true
% 2.27/0.99  --res_lit_sel                           adaptive
% 2.27/0.99  --res_lit_sel_side                      none
% 2.27/0.99  --res_ordering                          kbo
% 2.27/0.99  --res_to_prop_solver                    active
% 2.27/0.99  --res_prop_simpl_new                    false
% 2.27/0.99  --res_prop_simpl_given                  true
% 2.27/0.99  --res_passive_queue_type                priority_queues
% 2.27/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/0.99  --res_passive_queues_freq               [15;5]
% 2.27/0.99  --res_forward_subs                      full
% 2.27/0.99  --res_backward_subs                     full
% 2.27/0.99  --res_forward_subs_resolution           true
% 2.27/0.99  --res_backward_subs_resolution          true
% 2.27/0.99  --res_orphan_elimination                true
% 2.27/0.99  --res_time_limit                        2.
% 2.27/0.99  --res_out_proof                         true
% 2.27/0.99  
% 2.27/0.99  ------ Superposition Options
% 2.27/0.99  
% 2.27/0.99  --superposition_flag                    true
% 2.27/0.99  --sup_passive_queue_type                priority_queues
% 2.27/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.27/0.99  --demod_completeness_check              fast
% 2.27/0.99  --demod_use_ground                      true
% 2.27/0.99  --sup_to_prop_solver                    passive
% 2.27/0.99  --sup_prop_simpl_new                    true
% 2.27/0.99  --sup_prop_simpl_given                  true
% 2.27/0.99  --sup_fun_splitting                     false
% 2.27/0.99  --sup_smt_interval                      50000
% 2.27/0.99  
% 2.27/0.99  ------ Superposition Simplification Setup
% 2.27/0.99  
% 2.27/0.99  --sup_indices_passive                   []
% 2.27/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_full_bw                           [BwDemod]
% 2.27/0.99  --sup_immed_triv                        [TrivRules]
% 2.27/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_immed_bw_main                     []
% 2.27/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.99  
% 2.27/0.99  ------ Combination Options
% 2.27/0.99  
% 2.27/0.99  --comb_res_mult                         3
% 2.27/0.99  --comb_sup_mult                         2
% 2.27/0.99  --comb_inst_mult                        10
% 2.27/0.99  
% 2.27/0.99  ------ Debug Options
% 2.27/0.99  
% 2.27/0.99  --dbg_backtrace                         false
% 2.27/0.99  --dbg_dump_prop_clauses                 false
% 2.27/0.99  --dbg_dump_prop_clauses_file            -
% 2.27/0.99  --dbg_out_stat                          false
% 2.27/0.99  ------ Parsing...
% 2.27/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.27/0.99  ------ Proving...
% 2.27/0.99  ------ Problem Properties 
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  clauses                                 27
% 2.27/0.99  conjectures                             4
% 2.27/0.99  EPR                                     1
% 2.27/0.99  Horn                                    21
% 2.27/0.99  unary                                   9
% 2.27/0.99  binary                                  10
% 2.27/0.99  lits                                    56
% 2.27/0.99  lits eq                                 24
% 2.27/0.99  fd_pure                                 0
% 2.27/0.99  fd_pseudo                               0
% 2.27/0.99  fd_cond                                 1
% 2.27/0.99  fd_pseudo_cond                          7
% 2.27/0.99  AC symbols                              0
% 2.27/0.99  
% 2.27/0.99  ------ Schedule dynamic 5 is on 
% 2.27/0.99  
% 2.27/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  ------ 
% 2.27/0.99  Current options:
% 2.27/0.99  ------ 
% 2.27/0.99  
% 2.27/0.99  ------ Input Options
% 2.27/0.99  
% 2.27/0.99  --out_options                           all
% 2.27/0.99  --tptp_safe_out                         true
% 2.27/0.99  --problem_path                          ""
% 2.27/0.99  --include_path                          ""
% 2.27/0.99  --clausifier                            res/vclausify_rel
% 2.27/0.99  --clausifier_options                    --mode clausify
% 2.27/0.99  --stdin                                 false
% 2.27/0.99  --stats_out                             all
% 2.27/0.99  
% 2.27/0.99  ------ General Options
% 2.27/0.99  
% 2.27/0.99  --fof                                   false
% 2.27/0.99  --time_out_real                         305.
% 2.27/0.99  --time_out_virtual                      -1.
% 2.27/0.99  --symbol_type_check                     false
% 2.27/0.99  --clausify_out                          false
% 2.27/0.99  --sig_cnt_out                           false
% 2.27/0.99  --trig_cnt_out                          false
% 2.27/0.99  --trig_cnt_out_tolerance                1.
% 2.27/0.99  --trig_cnt_out_sk_spl                   false
% 2.27/0.99  --abstr_cl_out                          false
% 2.27/0.99  
% 2.27/0.99  ------ Global Options
% 2.27/0.99  
% 2.27/0.99  --schedule                              default
% 2.27/0.99  --add_important_lit                     false
% 2.27/0.99  --prop_solver_per_cl                    1000
% 2.27/0.99  --min_unsat_core                        false
% 2.27/0.99  --soft_assumptions                      false
% 2.27/0.99  --soft_lemma_size                       3
% 2.27/0.99  --prop_impl_unit_size                   0
% 2.27/0.99  --prop_impl_unit                        []
% 2.27/0.99  --share_sel_clauses                     true
% 2.27/0.99  --reset_solvers                         false
% 2.27/0.99  --bc_imp_inh                            [conj_cone]
% 2.27/0.99  --conj_cone_tolerance                   3.
% 2.27/0.99  --extra_neg_conj                        none
% 2.27/0.99  --large_theory_mode                     true
% 2.27/0.99  --prolific_symb_bound                   200
% 2.27/0.99  --lt_threshold                          2000
% 2.27/0.99  --clause_weak_htbl                      true
% 2.27/0.99  --gc_record_bc_elim                     false
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing Options
% 2.27/0.99  
% 2.27/0.99  --preprocessing_flag                    true
% 2.27/0.99  --time_out_prep_mult                    0.1
% 2.27/0.99  --splitting_mode                        input
% 2.27/0.99  --splitting_grd                         true
% 2.27/0.99  --splitting_cvd                         false
% 2.27/0.99  --splitting_cvd_svl                     false
% 2.27/0.99  --splitting_nvd                         32
% 2.27/0.99  --sub_typing                            true
% 2.27/0.99  --prep_gs_sim                           true
% 2.27/0.99  --prep_unflatten                        true
% 2.27/0.99  --prep_res_sim                          true
% 2.27/0.99  --prep_upred                            true
% 2.27/0.99  --prep_sem_filter                       exhaustive
% 2.27/0.99  --prep_sem_filter_out                   false
% 2.27/0.99  --pred_elim                             true
% 2.27/0.99  --res_sim_input                         true
% 2.27/0.99  --eq_ax_congr_red                       true
% 2.27/0.99  --pure_diseq_elim                       true
% 2.27/0.99  --brand_transform                       false
% 2.27/0.99  --non_eq_to_eq                          false
% 2.27/0.99  --prep_def_merge                        true
% 2.27/0.99  --prep_def_merge_prop_impl              false
% 2.27/0.99  --prep_def_merge_mbd                    true
% 2.27/0.99  --prep_def_merge_tr_red                 false
% 2.27/0.99  --prep_def_merge_tr_cl                  false
% 2.27/0.99  --smt_preprocessing                     true
% 2.27/0.99  --smt_ac_axioms                         fast
% 2.27/0.99  --preprocessed_out                      false
% 2.27/0.99  --preprocessed_stats                    false
% 2.27/0.99  
% 2.27/0.99  ------ Abstraction refinement Options
% 2.27/0.99  
% 2.27/0.99  --abstr_ref                             []
% 2.27/0.99  --abstr_ref_prep                        false
% 2.27/0.99  --abstr_ref_until_sat                   false
% 2.27/0.99  --abstr_ref_sig_restrict                funpre
% 2.27/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/0.99  --abstr_ref_under                       []
% 2.27/0.99  
% 2.27/0.99  ------ SAT Options
% 2.27/0.99  
% 2.27/0.99  --sat_mode                              false
% 2.27/0.99  --sat_fm_restart_options                ""
% 2.27/0.99  --sat_gr_def                            false
% 2.27/0.99  --sat_epr_types                         true
% 2.27/0.99  --sat_non_cyclic_types                  false
% 2.27/0.99  --sat_finite_models                     false
% 2.27/0.99  --sat_fm_lemmas                         false
% 2.27/0.99  --sat_fm_prep                           false
% 2.27/0.99  --sat_fm_uc_incr                        true
% 2.27/0.99  --sat_out_model                         small
% 2.27/0.99  --sat_out_clauses                       false
% 2.27/0.99  
% 2.27/0.99  ------ QBF Options
% 2.27/0.99  
% 2.27/0.99  --qbf_mode                              false
% 2.27/0.99  --qbf_elim_univ                         false
% 2.27/0.99  --qbf_dom_inst                          none
% 2.27/0.99  --qbf_dom_pre_inst                      false
% 2.27/0.99  --qbf_sk_in                             false
% 2.27/0.99  --qbf_pred_elim                         true
% 2.27/0.99  --qbf_split                             512
% 2.27/0.99  
% 2.27/0.99  ------ BMC1 Options
% 2.27/0.99  
% 2.27/0.99  --bmc1_incremental                      false
% 2.27/0.99  --bmc1_axioms                           reachable_all
% 2.27/0.99  --bmc1_min_bound                        0
% 2.27/0.99  --bmc1_max_bound                        -1
% 2.27/0.99  --bmc1_max_bound_default                -1
% 2.27/0.99  --bmc1_symbol_reachability              true
% 2.27/0.99  --bmc1_property_lemmas                  false
% 2.27/0.99  --bmc1_k_induction                      false
% 2.27/0.99  --bmc1_non_equiv_states                 false
% 2.27/0.99  --bmc1_deadlock                         false
% 2.27/0.99  --bmc1_ucm                              false
% 2.27/0.99  --bmc1_add_unsat_core                   none
% 2.27/0.99  --bmc1_unsat_core_children              false
% 2.27/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/0.99  --bmc1_out_stat                         full
% 2.27/0.99  --bmc1_ground_init                      false
% 2.27/0.99  --bmc1_pre_inst_next_state              false
% 2.27/0.99  --bmc1_pre_inst_state                   false
% 2.27/0.99  --bmc1_pre_inst_reach_state             false
% 2.27/0.99  --bmc1_out_unsat_core                   false
% 2.27/0.99  --bmc1_aig_witness_out                  false
% 2.27/0.99  --bmc1_verbose                          false
% 2.27/0.99  --bmc1_dump_clauses_tptp                false
% 2.27/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.27/0.99  --bmc1_dump_file                        -
% 2.27/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.27/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.27/0.99  --bmc1_ucm_extend_mode                  1
% 2.27/0.99  --bmc1_ucm_init_mode                    2
% 2.27/0.99  --bmc1_ucm_cone_mode                    none
% 2.27/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.27/0.99  --bmc1_ucm_relax_model                  4
% 2.27/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.27/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/0.99  --bmc1_ucm_layered_model                none
% 2.27/0.99  --bmc1_ucm_max_lemma_size               10
% 2.27/0.99  
% 2.27/0.99  ------ AIG Options
% 2.27/0.99  
% 2.27/0.99  --aig_mode                              false
% 2.27/0.99  
% 2.27/0.99  ------ Instantiation Options
% 2.27/0.99  
% 2.27/0.99  --instantiation_flag                    true
% 2.27/0.99  --inst_sos_flag                         false
% 2.27/0.99  --inst_sos_phase                        true
% 2.27/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/0.99  --inst_lit_sel_side                     none
% 2.27/0.99  --inst_solver_per_active                1400
% 2.27/0.99  --inst_solver_calls_frac                1.
% 2.27/0.99  --inst_passive_queue_type               priority_queues
% 2.27/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/0.99  --inst_passive_queues_freq              [25;2]
% 2.27/0.99  --inst_dismatching                      true
% 2.27/0.99  --inst_eager_unprocessed_to_passive     true
% 2.27/0.99  --inst_prop_sim_given                   true
% 2.27/0.99  --inst_prop_sim_new                     false
% 2.27/0.99  --inst_subs_new                         false
% 2.27/0.99  --inst_eq_res_simp                      false
% 2.27/0.99  --inst_subs_given                       false
% 2.27/0.99  --inst_orphan_elimination               true
% 2.27/0.99  --inst_learning_loop_flag               true
% 2.27/0.99  --inst_learning_start                   3000
% 2.27/0.99  --inst_learning_factor                  2
% 2.27/0.99  --inst_start_prop_sim_after_learn       3
% 2.27/0.99  --inst_sel_renew                        solver
% 2.27/0.99  --inst_lit_activity_flag                true
% 2.27/0.99  --inst_restr_to_given                   false
% 2.27/0.99  --inst_activity_threshold               500
% 2.27/0.99  --inst_out_proof                        true
% 2.27/0.99  
% 2.27/0.99  ------ Resolution Options
% 2.27/0.99  
% 2.27/0.99  --resolution_flag                       false
% 2.27/0.99  --res_lit_sel                           adaptive
% 2.27/0.99  --res_lit_sel_side                      none
% 2.27/0.99  --res_ordering                          kbo
% 2.27/0.99  --res_to_prop_solver                    active
% 2.27/0.99  --res_prop_simpl_new                    false
% 2.27/0.99  --res_prop_simpl_given                  true
% 2.27/0.99  --res_passive_queue_type                priority_queues
% 2.27/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/0.99  --res_passive_queues_freq               [15;5]
% 2.27/0.99  --res_forward_subs                      full
% 2.27/0.99  --res_backward_subs                     full
% 2.27/0.99  --res_forward_subs_resolution           true
% 2.27/0.99  --res_backward_subs_resolution          true
% 2.27/0.99  --res_orphan_elimination                true
% 2.27/0.99  --res_time_limit                        2.
% 2.27/0.99  --res_out_proof                         true
% 2.27/0.99  
% 2.27/0.99  ------ Superposition Options
% 2.27/0.99  
% 2.27/0.99  --superposition_flag                    true
% 2.27/0.99  --sup_passive_queue_type                priority_queues
% 2.27/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.27/0.99  --demod_completeness_check              fast
% 2.27/0.99  --demod_use_ground                      true
% 2.27/0.99  --sup_to_prop_solver                    passive
% 2.27/0.99  --sup_prop_simpl_new                    true
% 2.27/0.99  --sup_prop_simpl_given                  true
% 2.27/0.99  --sup_fun_splitting                     false
% 2.27/0.99  --sup_smt_interval                      50000
% 2.27/0.99  
% 2.27/0.99  ------ Superposition Simplification Setup
% 2.27/0.99  
% 2.27/0.99  --sup_indices_passive                   []
% 2.27/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_full_bw                           [BwDemod]
% 2.27/0.99  --sup_immed_triv                        [TrivRules]
% 2.27/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_immed_bw_main                     []
% 2.27/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.99  
% 2.27/0.99  ------ Combination Options
% 2.27/0.99  
% 2.27/0.99  --comb_res_mult                         3
% 2.27/0.99  --comb_sup_mult                         2
% 2.27/0.99  --comb_inst_mult                        10
% 2.27/0.99  
% 2.27/0.99  ------ Debug Options
% 2.27/0.99  
% 2.27/0.99  --dbg_backtrace                         false
% 2.27/0.99  --dbg_dump_prop_clauses                 false
% 2.27/0.99  --dbg_dump_prop_clauses_file            -
% 2.27/0.99  --dbg_out_stat                          false
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  ------ Proving...
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  % SZS status Theorem for theBenchmark.p
% 2.27/0.99  
% 2.27/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.27/0.99  
% 2.27/0.99  fof(f6,axiom,(
% 2.27/0.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f30,plain,(
% 2.27/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.27/0.99    inference(nnf_transformation,[],[f6])).
% 2.27/0.99  
% 2.27/0.99  fof(f31,plain,(
% 2.27/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.27/0.99    inference(rectify,[],[f30])).
% 2.27/0.99  
% 2.27/0.99  fof(f32,plain,(
% 2.27/0.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 2.27/0.99    introduced(choice_axiom,[])).
% 2.27/0.99  
% 2.27/0.99  fof(f33,plain,(
% 2.27/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 2.27/0.99  
% 2.27/0.99  fof(f52,plain,(
% 2.27/0.99    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f33])).
% 2.27/0.99  
% 2.27/0.99  fof(f7,axiom,(
% 2.27/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f54,plain,(
% 2.27/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f7])).
% 2.27/0.99  
% 2.27/0.99  fof(f8,axiom,(
% 2.27/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f55,plain,(
% 2.27/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f8])).
% 2.27/0.99  
% 2.27/0.99  fof(f9,axiom,(
% 2.27/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f56,plain,(
% 2.27/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f9])).
% 2.27/0.99  
% 2.27/0.99  fof(f10,axiom,(
% 2.27/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f57,plain,(
% 2.27/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f10])).
% 2.27/0.99  
% 2.27/0.99  fof(f72,plain,(
% 2.27/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.27/0.99    inference(definition_unfolding,[],[f56,f57])).
% 2.27/0.99  
% 2.27/0.99  fof(f73,plain,(
% 2.27/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.27/0.99    inference(definition_unfolding,[],[f55,f72])).
% 2.27/0.99  
% 2.27/0.99  fof(f75,plain,(
% 2.27/0.99    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.27/0.99    inference(definition_unfolding,[],[f54,f73])).
% 2.27/0.99  
% 2.27/0.99  fof(f85,plain,(
% 2.27/0.99    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = X1 | sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)) )),
% 2.27/0.99    inference(definition_unfolding,[],[f52,f75])).
% 2.27/0.99  
% 2.27/0.99  fof(f13,axiom,(
% 2.27/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f21,plain,(
% 2.27/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.27/0.99    inference(ennf_transformation,[],[f13])).
% 2.27/0.99  
% 2.27/0.99  fof(f36,plain,(
% 2.27/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.27/0.99    inference(nnf_transformation,[],[f21])).
% 2.27/0.99  
% 2.27/0.99  fof(f37,plain,(
% 2.27/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.27/0.99    inference(flattening,[],[f36])).
% 2.27/0.99  
% 2.27/0.99  fof(f65,plain,(
% 2.27/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 2.27/0.99    inference(cnf_transformation,[],[f37])).
% 2.27/0.99  
% 2.27/0.99  fof(f93,plain,(
% 2.27/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2)) | k3_enumset1(X2,X2,X2,X2,X2) != X0) )),
% 2.27/0.99    inference(definition_unfolding,[],[f65,f73,f75])).
% 2.27/0.99  
% 2.27/0.99  fof(f110,plain,(
% 2.27/0.99    ( ! [X2,X1] : (r1_tarski(k3_enumset1(X2,X2,X2,X2,X2),k3_enumset1(X1,X1,X1,X1,X2))) )),
% 2.27/0.99    inference(equality_resolution,[],[f93])).
% 2.27/0.99  
% 2.27/0.99  fof(f15,conjecture,(
% 2.27/0.99    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f16,negated_conjecture,(
% 2.27/0.99    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.27/0.99    inference(negated_conjecture,[],[f15])).
% 2.27/0.99  
% 2.27/0.99  fof(f22,plain,(
% 2.27/0.99    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.27/1.00    inference(ennf_transformation,[],[f16])).
% 2.27/1.00  
% 2.27/1.00  fof(f38,plain,(
% 2.27/1.00    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4) & (k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4) & (k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4) & k2_xboole_0(sK4,sK5) = k1_tarski(sK3))),
% 2.27/1.00    introduced(choice_axiom,[])).
% 2.27/1.00  
% 2.27/1.00  fof(f39,plain,(
% 2.27/1.00    (k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4) & (k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4) & (k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4) & k2_xboole_0(sK4,sK5) = k1_tarski(sK3)),
% 2.27/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f38])).
% 2.27/1.00  
% 2.27/1.00  fof(f68,plain,(
% 2.27/1.00    k2_xboole_0(sK4,sK5) = k1_tarski(sK3)),
% 2.27/1.00    inference(cnf_transformation,[],[f39])).
% 2.27/1.00  
% 2.27/1.00  fof(f14,axiom,(
% 2.27/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f67,plain,(
% 2.27/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.27/1.00    inference(cnf_transformation,[],[f14])).
% 2.27/1.00  
% 2.27/1.00  fof(f74,plain,(
% 2.27/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 2.27/1.00    inference(definition_unfolding,[],[f67,f73])).
% 2.27/1.00  
% 2.27/1.00  fof(f100,plain,(
% 2.27/1.00    k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5))),
% 2.27/1.00    inference(definition_unfolding,[],[f68,f74,f75])).
% 2.27/1.00  
% 2.27/1.00  fof(f3,axiom,(
% 2.27/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f18,plain,(
% 2.27/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.27/1.00    inference(ennf_transformation,[],[f3])).
% 2.27/1.00  
% 2.27/1.00  fof(f47,plain,(
% 2.27/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f18])).
% 2.27/1.00  
% 2.27/1.00  fof(f82,plain,(
% 2.27/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X2)) )),
% 2.27/1.00    inference(definition_unfolding,[],[f47,f74])).
% 2.27/1.00  
% 2.27/1.00  fof(f62,plain,(
% 2.27/1.00    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 2.27/1.00    inference(cnf_transformation,[],[f37])).
% 2.27/1.00  
% 2.27/1.00  fof(f96,plain,(
% 2.27/1.00    ( ! [X2,X0,X1] : (k3_enumset1(X1,X1,X1,X1,X2) = X0 | k3_enumset1(X2,X2,X2,X2,X2) = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2))) )),
% 2.27/1.00    inference(definition_unfolding,[],[f62,f73,f75,f75,f73])).
% 2.27/1.00  
% 2.27/1.00  fof(f1,axiom,(
% 2.27/1.00    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f23,plain,(
% 2.27/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.27/1.00    inference(nnf_transformation,[],[f1])).
% 2.27/1.00  
% 2.27/1.00  fof(f24,plain,(
% 2.27/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.27/1.00    inference(flattening,[],[f23])).
% 2.27/1.00  
% 2.27/1.00  fof(f25,plain,(
% 2.27/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.27/1.00    inference(rectify,[],[f24])).
% 2.27/1.00  
% 2.27/1.00  fof(f26,plain,(
% 2.27/1.00    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.27/1.00    introduced(choice_axiom,[])).
% 2.27/1.00  
% 2.27/1.00  fof(f27,plain,(
% 2.27/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.27/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 2.27/1.00  
% 2.27/1.00  fof(f42,plain,(
% 2.27/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.27/1.00    inference(cnf_transformation,[],[f27])).
% 2.27/1.00  
% 2.27/1.00  fof(f79,plain,(
% 2.27/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 2.27/1.00    inference(definition_unfolding,[],[f42,f74])).
% 2.27/1.00  
% 2.27/1.00  fof(f101,plain,(
% 2.27/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.27/1.00    inference(equality_resolution,[],[f79])).
% 2.27/1.00  
% 2.27/1.00  fof(f71,plain,(
% 2.27/1.00    k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4),
% 2.27/1.00    inference(cnf_transformation,[],[f39])).
% 2.27/1.00  
% 2.27/1.00  fof(f97,plain,(
% 2.27/1.00    k1_xboole_0 != sK5 | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4),
% 2.27/1.00    inference(definition_unfolding,[],[f71,f75])).
% 2.27/1.00  
% 2.27/1.00  fof(f69,plain,(
% 2.27/1.00    k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4),
% 2.27/1.00    inference(cnf_transformation,[],[f39])).
% 2.27/1.00  
% 2.27/1.00  fof(f99,plain,(
% 2.27/1.00    k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4),
% 2.27/1.00    inference(definition_unfolding,[],[f69,f75,f75])).
% 2.27/1.00  
% 2.27/1.00  fof(f70,plain,(
% 2.27/1.00    k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4),
% 2.27/1.00    inference(cnf_transformation,[],[f39])).
% 2.27/1.00  
% 2.27/1.00  fof(f98,plain,(
% 2.27/1.00    k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 | k1_xboole_0 != sK4),
% 2.27/1.00    inference(definition_unfolding,[],[f70,f75])).
% 2.27/1.00  
% 2.27/1.00  fof(f12,axiom,(
% 2.27/1.00    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f34,plain,(
% 2.27/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.27/1.00    inference(nnf_transformation,[],[f12])).
% 2.27/1.00  
% 2.27/1.00  fof(f35,plain,(
% 2.27/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.27/1.00    inference(flattening,[],[f34])).
% 2.27/1.00  
% 2.27/1.00  fof(f59,plain,(
% 2.27/1.00    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.27/1.00    inference(cnf_transformation,[],[f35])).
% 2.27/1.00  
% 2.27/1.00  fof(f91,plain,(
% 2.27/1.00    ( ! [X0,X1] : (k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))) )),
% 2.27/1.00    inference(definition_unfolding,[],[f59,f75,f75])).
% 2.27/1.00  
% 2.27/1.00  fof(f2,axiom,(
% 2.27/1.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f17,plain,(
% 2.27/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.27/1.00    inference(ennf_transformation,[],[f2])).
% 2.27/1.00  
% 2.27/1.00  fof(f28,plain,(
% 2.27/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 2.27/1.00    introduced(choice_axiom,[])).
% 2.27/1.00  
% 2.27/1.00  fof(f29,plain,(
% 2.27/1.00    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 2.27/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f28])).
% 2.27/1.00  
% 2.27/1.00  fof(f46,plain,(
% 2.27/1.00    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.27/1.00    inference(cnf_transformation,[],[f29])).
% 2.27/1.00  
% 2.27/1.00  fof(f50,plain,(
% 2.27/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.27/1.00    inference(cnf_transformation,[],[f33])).
% 2.27/1.00  
% 2.27/1.00  fof(f87,plain,(
% 2.27/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 2.27/1.00    inference(definition_unfolding,[],[f50,f75])).
% 2.27/1.00  
% 2.27/1.00  fof(f106,plain,(
% 2.27/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 2.27/1.00    inference(equality_resolution,[],[f87])).
% 2.27/1.00  
% 2.27/1.00  fof(f53,plain,(
% 2.27/1.00    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f33])).
% 2.27/1.00  
% 2.27/1.00  fof(f84,plain,(
% 2.27/1.00    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = X1 | sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) )),
% 2.27/1.00    inference(definition_unfolding,[],[f53,f75])).
% 2.27/1.00  
% 2.27/1.00  fof(f5,axiom,(
% 2.27/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f49,plain,(
% 2.27/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f5])).
% 2.27/1.00  
% 2.27/1.00  fof(f4,axiom,(
% 2.27/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f19,plain,(
% 2.27/1.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.27/1.00    inference(ennf_transformation,[],[f4])).
% 2.27/1.00  
% 2.27/1.00  fof(f48,plain,(
% 2.27/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f19])).
% 2.27/1.00  
% 2.27/1.00  fof(f83,plain,(
% 2.27/1.00    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.27/1.00    inference(definition_unfolding,[],[f48,f74])).
% 2.27/1.00  
% 2.27/1.00  cnf(c_11,plain,
% 2.27/1.00      ( r2_hidden(sK2(X0,X1),X1)
% 2.27/1.00      | k3_enumset1(X0,X0,X0,X0,X0) = X1
% 2.27/1.00      | sK2(X0,X1) = X0 ),
% 2.27/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_643,plain,
% 2.27/1.00      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 2.27/1.00      | sK2(X0,X1) = X0
% 2.27/1.00      | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_19,plain,
% 2.27/1.00      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X0)) ),
% 2.27/1.00      inference(cnf_transformation,[],[f110]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_635,plain,
% 2.27/1.00      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X0)) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_26,negated_conjecture,
% 2.27/1.00      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
% 2.27/1.00      inference(cnf_transformation,[],[f100]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_7,plain,
% 2.27/1.00      ( r1_tarski(X0,X1)
% 2.27/1.00      | ~ r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) ),
% 2.27/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_647,plain,
% 2.27/1.00      ( r1_tarski(X0,X1) = iProver_top
% 2.27/1.00      | r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1435,plain,
% 2.27/1.00      ( r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),X0) != iProver_top
% 2.27/1.00      | r1_tarski(sK4,X0) = iProver_top ),
% 2.27/1.00      inference(superposition,[status(thm)],[c_26,c_647]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1450,plain,
% 2.27/1.00      ( r1_tarski(sK4,k3_enumset1(X0,X0,X0,X0,sK3)) = iProver_top ),
% 2.27/1.00      inference(superposition,[status(thm)],[c_635,c_1435]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_22,plain,
% 2.27/1.00      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2))
% 2.27/1.00      | k3_enumset1(X1,X1,X1,X1,X1) = X0
% 2.27/1.00      | k3_enumset1(X1,X1,X1,X1,X2) = X0
% 2.27/1.00      | k3_enumset1(X2,X2,X2,X2,X2) = X0
% 2.27/1.00      | k1_xboole_0 = X0 ),
% 2.27/1.00      inference(cnf_transformation,[],[f96]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_632,plain,
% 2.27/1.00      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 2.27/1.00      | k3_enumset1(X0,X0,X0,X0,X2) = X1
% 2.27/1.00      | k3_enumset1(X2,X2,X2,X2,X2) = X1
% 2.27/1.00      | k1_xboole_0 = X1
% 2.27/1.00      | r1_tarski(X1,k3_enumset1(X0,X0,X0,X0,X2)) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1568,plain,
% 2.27/1.00      ( k3_enumset1(X0,X0,X0,X0,X0) = sK4
% 2.27/1.00      | k3_enumset1(X0,X0,X0,X0,sK3) = sK4
% 2.27/1.00      | k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4
% 2.27/1.00      | sK4 = k1_xboole_0 ),
% 2.27/1.00      inference(superposition,[status(thm)],[c_1450,c_632]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1580,plain,
% 2.27/1.00      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4 | sK4 = k1_xboole_0 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1568]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1772,plain,
% 2.27/1.00      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4 | sK4 = k1_xboole_0 ),
% 2.27/1.00      inference(global_propositional_subsumption,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_1568,c_1580]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3,plain,
% 2.27/1.00      ( ~ r2_hidden(X0,X1)
% 2.27/1.00      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
% 2.27/1.00      inference(cnf_transformation,[],[f101]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_651,plain,
% 2.27/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.27/1.00      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2110,plain,
% 2.27/1.00      ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
% 2.27/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 2.27/1.00      inference(superposition,[status(thm)],[c_26,c_651]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2336,plain,
% 2.27/1.00      ( sK4 = k1_xboole_0
% 2.27/1.00      | r2_hidden(X0,sK4) = iProver_top
% 2.27/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 2.27/1.00      inference(superposition,[status(thm)],[c_1772,c_2110]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2990,plain,
% 2.27/1.00      ( k3_enumset1(X0,X0,X0,X0,X0) = sK5
% 2.27/1.00      | sK2(X0,sK5) = X0
% 2.27/1.00      | sK4 = k1_xboole_0
% 2.27/1.00      | r2_hidden(sK2(X0,sK5),sK4) = iProver_top ),
% 2.27/1.00      inference(superposition,[status(thm)],[c_643,c_2336]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_23,negated_conjecture,
% 2.27/1.00      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4 | k1_xboole_0 != sK5 ),
% 2.27/1.00      inference(cnf_transformation,[],[f97]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1789,plain,
% 2.27/1.00      ( sK4 = k1_xboole_0 | sK5 != k1_xboole_0 ),
% 2.27/1.00      inference(superposition,[status(thm)],[c_1772,c_23]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_25,negated_conjecture,
% 2.27/1.00      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4
% 2.27/1.00      | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 ),
% 2.27/1.00      inference(cnf_transformation,[],[f99]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1787,plain,
% 2.27/1.00      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 | sK4 = k1_xboole_0 ),
% 2.27/1.00      inference(superposition,[status(thm)],[c_1772,c_25]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_24,negated_conjecture,
% 2.27/1.00      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 | k1_xboole_0 != sK4 ),
% 2.27/1.00      inference(cnf_transformation,[],[f98]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_17,plain,
% 2.27/1.00      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
% 2.27/1.00      | k3_enumset1(X1,X1,X1,X1,X1) = X0
% 2.27/1.00      | k1_xboole_0 = X0 ),
% 2.27/1.00      inference(cnf_transformation,[],[f91]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_881,plain,
% 2.27/1.00      ( ~ r1_tarski(sK4,k3_enumset1(X0,X0,X0,X0,X0))
% 2.27/1.00      | k3_enumset1(X0,X0,X0,X0,X0) = sK4
% 2.27/1.00      | k1_xboole_0 = sK4 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_883,plain,
% 2.27/1.00      ( ~ r1_tarski(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 2.27/1.00      | k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4
% 2.27/1.00      | k1_xboole_0 = sK4 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_881]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1456,plain,
% 2.27/1.00      ( r1_tarski(sK4,k3_enumset1(X0,X0,X0,X0,sK3)) ),
% 2.27/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1450]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1458,plain,
% 2.27/1.00      ( r1_tarski(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_1456]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1998,plain,
% 2.27/1.00      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 ),
% 2.27/1.00      inference(global_propositional_subsumption,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_1787,c_25,c_24,c_883,c_1458]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_6,plain,
% 2.27/1.00      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 2.27/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_648,plain,
% 2.27/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_13,plain,
% 2.27/1.00      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1 ),
% 2.27/1.00      inference(cnf_transformation,[],[f106]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_641,plain,
% 2.27/1.00      ( X0 = X1
% 2.27/1.00      | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2337,plain,
% 2.27/1.00      ( sK3 = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 2.27/1.00      inference(superposition,[status(thm)],[c_2110,c_641]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2460,plain,
% 2.27/1.00      ( sK1(sK5) = sK3 | sK5 = k1_xboole_0 ),
% 2.27/1.00      inference(superposition,[status(thm)],[c_648,c_2337]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2704,plain,
% 2.27/1.00      ( sK5 = k1_xboole_0 | r2_hidden(sK3,sK5) = iProver_top ),
% 2.27/1.00      inference(superposition,[status(thm)],[c_2460,c_648]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2991,plain,
% 2.27/1.00      ( k3_enumset1(X0,X0,X0,X0,X0) = sK5
% 2.27/1.00      | sK2(X0,sK5) = X0
% 2.27/1.00      | sK2(X0,sK5) = sK3 ),
% 2.27/1.00      inference(superposition,[status(thm)],[c_643,c_2337]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3652,plain,
% 2.27/1.00      ( sK2(sK3,sK5) = sK3 ),
% 2.27/1.00      inference(superposition,[status(thm)],[c_2991,c_1998]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_10,plain,
% 2.27/1.00      ( ~ r2_hidden(sK2(X0,X1),X1)
% 2.27/1.00      | k3_enumset1(X0,X0,X0,X0,X0) = X1
% 2.27/1.00      | sK2(X0,X1) != X0 ),
% 2.27/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_644,plain,
% 2.27/1.00      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 2.27/1.00      | sK2(X0,X1) != X0
% 2.27/1.00      | r2_hidden(sK2(X0,X1),X1) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3794,plain,
% 2.27/1.00      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK5
% 2.27/1.00      | r2_hidden(sK2(sK3,sK5),sK5) != iProver_top ),
% 2.27/1.00      inference(superposition,[status(thm)],[c_3652,c_644]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3798,plain,
% 2.27/1.00      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK5
% 2.27/1.00      | r2_hidden(sK3,sK5) != iProver_top ),
% 2.27/1.00      inference(light_normalisation,[status(thm)],[c_3794,c_3652]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3961,plain,
% 2.27/1.00      ( sK4 = k1_xboole_0 ),
% 2.27/1.00      inference(global_propositional_subsumption,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_2990,c_25,c_24,c_883,c_1458,c_1789,c_2704,c_3798]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3976,plain,
% 2.27/1.00      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK5)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 2.27/1.00      inference(demodulation,[status(thm)],[c_3961,c_26]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_9,plain,
% 2.27/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.27/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_645,plain,
% 2.27/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_8,plain,
% 2.27/1.00      ( ~ r1_tarski(X0,X1)
% 2.27/1.00      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 ),
% 2.27/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_646,plain,
% 2.27/1.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1
% 2.27/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1327,plain,
% 2.27/1.00      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 2.27/1.00      inference(superposition,[status(thm)],[c_645,c_646]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3983,plain,
% 2.27/1.00      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK5 ),
% 2.27/1.00      inference(demodulation,[status(thm)],[c_3976,c_1327]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(contradiction,plain,
% 2.27/1.00      ( $false ),
% 2.27/1.00      inference(minisat,[status(thm)],[c_3983,c_1998]) ).
% 2.27/1.00  
% 2.27/1.00  
% 2.27/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.27/1.00  
% 2.27/1.00  ------                               Statistics
% 2.27/1.00  
% 2.27/1.00  ------ General
% 2.27/1.00  
% 2.27/1.00  abstr_ref_over_cycles:                  0
% 2.27/1.00  abstr_ref_under_cycles:                 0
% 2.27/1.00  gc_basic_clause_elim:                   0
% 2.27/1.00  forced_gc_time:                         0
% 2.27/1.00  parsing_time:                           0.01
% 2.27/1.00  unif_index_cands_time:                  0.
% 2.27/1.00  unif_index_add_time:                    0.
% 2.27/1.00  orderings_time:                         0.
% 2.27/1.00  out_proof_time:                         0.008
% 2.27/1.00  total_time:                             0.154
% 2.27/1.00  num_of_symbols:                         42
% 2.27/1.00  num_of_terms:                           4065
% 2.27/1.00  
% 2.27/1.00  ------ Preprocessing
% 2.27/1.00  
% 2.27/1.00  num_of_splits:                          0
% 2.27/1.00  num_of_split_atoms:                     0
% 2.27/1.00  num_of_reused_defs:                     0
% 2.27/1.00  num_eq_ax_congr_red:                    12
% 2.27/1.00  num_of_sem_filtered_clauses:            1
% 2.27/1.00  num_of_subtypes:                        0
% 2.27/1.00  monotx_restored_types:                  0
% 2.27/1.00  sat_num_of_epr_types:                   0
% 2.27/1.00  sat_num_of_non_cyclic_types:            0
% 2.27/1.00  sat_guarded_non_collapsed_types:        0
% 2.27/1.00  num_pure_diseq_elim:                    0
% 2.27/1.00  simp_replaced_by:                       0
% 2.27/1.00  res_preprocessed:                       94
% 2.27/1.00  prep_upred:                             0
% 2.27/1.00  prep_unflattend:                        0
% 2.27/1.00  smt_new_axioms:                         0
% 2.27/1.00  pred_elim_cands:                        2
% 2.27/1.00  pred_elim:                              0
% 2.27/1.00  pred_elim_cl:                           0
% 2.27/1.00  pred_elim_cycles:                       1
% 2.27/1.00  merged_defs:                            0
% 2.27/1.00  merged_defs_ncl:                        0
% 2.27/1.00  bin_hyper_res:                          0
% 2.27/1.00  prep_cycles:                            3
% 2.27/1.00  pred_elim_time:                         0.
% 2.27/1.00  splitting_time:                         0.
% 2.27/1.00  sem_filter_time:                        0.
% 2.27/1.00  monotx_time:                            0.
% 2.27/1.00  subtype_inf_time:                       0.
% 2.27/1.00  
% 2.27/1.00  ------ Problem properties
% 2.27/1.00  
% 2.27/1.00  clauses:                                27
% 2.27/1.00  conjectures:                            4
% 2.27/1.00  epr:                                    1
% 2.27/1.00  horn:                                   21
% 2.27/1.00  ground:                                 4
% 2.27/1.00  unary:                                  9
% 2.27/1.00  binary:                                 10
% 2.27/1.00  lits:                                   56
% 2.27/1.00  lits_eq:                                24
% 2.27/1.00  fd_pure:                                0
% 2.27/1.00  fd_pseudo:                              0
% 2.27/1.00  fd_cond:                                1
% 2.27/1.00  fd_pseudo_cond:                         7
% 2.27/1.00  ac_symbols:                             0
% 2.27/1.00  
% 2.27/1.00  ------ Propositional Solver
% 2.27/1.00  
% 2.27/1.00  prop_solver_calls:                      22
% 2.27/1.00  prop_fast_solver_calls:                 529
% 2.27/1.00  smt_solver_calls:                       0
% 2.27/1.00  smt_fast_solver_calls:                  0
% 2.27/1.00  prop_num_of_clauses:                    1535
% 2.27/1.00  prop_preprocess_simplified:             5212
% 2.27/1.00  prop_fo_subsumed:                       10
% 2.27/1.00  prop_solver_time:                       0.
% 2.27/1.00  smt_solver_time:                        0.
% 2.27/1.00  smt_fast_solver_time:                   0.
% 2.27/1.00  prop_fast_solver_time:                  0.
% 2.27/1.00  prop_unsat_core_time:                   0.
% 2.27/1.00  
% 2.27/1.00  ------ QBF
% 2.27/1.00  
% 2.27/1.00  qbf_q_res:                              0
% 2.27/1.00  qbf_num_tautologies:                    0
% 2.27/1.00  qbf_prep_cycles:                        0
% 2.27/1.00  
% 2.27/1.00  ------ BMC1
% 2.27/1.00  
% 2.27/1.00  bmc1_current_bound:                     -1
% 2.27/1.00  bmc1_last_solved_bound:                 -1
% 2.27/1.00  bmc1_unsat_core_size:                   -1
% 2.27/1.00  bmc1_unsat_core_parents_size:           -1
% 2.27/1.00  bmc1_merge_next_fun:                    0
% 2.27/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.27/1.00  
% 2.27/1.00  ------ Instantiation
% 2.27/1.00  
% 2.27/1.00  inst_num_of_clauses:                    441
% 2.27/1.00  inst_num_in_passive:                    107
% 2.27/1.00  inst_num_in_active:                     185
% 2.27/1.00  inst_num_in_unprocessed:                150
% 2.27/1.00  inst_num_of_loops:                      230
% 2.27/1.00  inst_num_of_learning_restarts:          0
% 2.27/1.00  inst_num_moves_active_passive:          43
% 2.27/1.00  inst_lit_activity:                      0
% 2.27/1.00  inst_lit_activity_moves:                0
% 2.27/1.00  inst_num_tautologies:                   0
% 2.27/1.00  inst_num_prop_implied:                  0
% 2.27/1.00  inst_num_existing_simplified:           0
% 2.27/1.00  inst_num_eq_res_simplified:             0
% 2.27/1.00  inst_num_child_elim:                    0
% 2.27/1.00  inst_num_of_dismatching_blockings:      119
% 2.27/1.00  inst_num_of_non_proper_insts:           421
% 2.27/1.00  inst_num_of_duplicates:                 0
% 2.27/1.00  inst_inst_num_from_inst_to_res:         0
% 2.27/1.00  inst_dismatching_checking_time:         0.
% 2.27/1.00  
% 2.27/1.00  ------ Resolution
% 2.27/1.00  
% 2.27/1.00  res_num_of_clauses:                     0
% 2.27/1.00  res_num_in_passive:                     0
% 2.27/1.00  res_num_in_active:                      0
% 2.27/1.00  res_num_of_loops:                       97
% 2.27/1.00  res_forward_subset_subsumed:            34
% 2.27/1.00  res_backward_subset_subsumed:           6
% 2.27/1.00  res_forward_subsumed:                   0
% 2.27/1.00  res_backward_subsumed:                  0
% 2.27/1.00  res_forward_subsumption_resolution:     0
% 2.27/1.00  res_backward_subsumption_resolution:    0
% 2.27/1.00  res_clause_to_clause_subsumption:       221
% 2.27/1.00  res_orphan_elimination:                 0
% 2.27/1.00  res_tautology_del:                      17
% 2.27/1.00  res_num_eq_res_simplified:              0
% 2.27/1.00  res_num_sel_changes:                    0
% 2.27/1.00  res_moves_from_active_to_pass:          0
% 2.27/1.00  
% 2.27/1.00  ------ Superposition
% 2.27/1.00  
% 2.27/1.00  sup_time_total:                         0.
% 2.27/1.00  sup_time_generating:                    0.
% 2.27/1.00  sup_time_sim_full:                      0.
% 2.27/1.00  sup_time_sim_immed:                     0.
% 2.27/1.00  
% 2.27/1.00  sup_num_of_clauses:                     73
% 2.27/1.00  sup_num_in_active:                      26
% 2.27/1.00  sup_num_in_passive:                     47
% 2.27/1.00  sup_num_of_loops:                       45
% 2.27/1.00  sup_fw_superposition:                   61
% 2.27/1.00  sup_bw_superposition:                   65
% 2.27/1.00  sup_immediate_simplified:               26
% 2.27/1.00  sup_given_eliminated:                   0
% 2.27/1.00  comparisons_done:                       0
% 2.27/1.00  comparisons_avoided:                    13
% 2.27/1.00  
% 2.27/1.00  ------ Simplifications
% 2.27/1.00  
% 2.27/1.00  
% 2.27/1.00  sim_fw_subset_subsumed:                 8
% 2.27/1.00  sim_bw_subset_subsumed:                 16
% 2.27/1.00  sim_fw_subsumed:                        11
% 2.27/1.00  sim_bw_subsumed:                        0
% 2.27/1.00  sim_fw_subsumption_res:                 1
% 2.27/1.00  sim_bw_subsumption_res:                 0
% 2.27/1.00  sim_tautology_del:                      14
% 2.27/1.00  sim_eq_tautology_del:                   9
% 2.27/1.00  sim_eq_res_simp:                        0
% 2.27/1.00  sim_fw_demodulated:                     3
% 2.27/1.00  sim_bw_demodulated:                     15
% 2.27/1.00  sim_light_normalised:                   4
% 2.27/1.00  sim_joinable_taut:                      0
% 2.27/1.00  sim_joinable_simp:                      0
% 2.27/1.00  sim_ac_normalised:                      0
% 2.27/1.00  sim_smt_subsumption:                    0
% 2.27/1.00  
%------------------------------------------------------------------------------
