%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:26 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  152 (1209 expanded)
%              Number of clauses        :   75 ( 148 expanded)
%              Number of leaves         :   19 ( 353 expanded)
%              Depth                    :   16
%              Number of atoms          :  454 (3343 expanded)
%              Number of equality atoms :  269 (2074 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

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
    inference(flattening,[],[f25])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f69])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f64,f70])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f44,f71])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f17])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f24,f38])).

fof(f65,plain,(
    k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f70])).

fof(f93,plain,(
    k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(definition_unfolding,[],[f65,f71,f72])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f41,f71])).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f78])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f43,f71])).

fof(f94,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f76])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f46,f71])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f42,f71])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f81,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f51,f71])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f30])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f52,f72])).

fof(f99,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f85])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f53,f72])).

fof(f97,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f84])).

fof(f98,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f97])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f36])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f61,f72,f72])).

fof(f68,plain,
    ( k1_xboole_0 != sK5
    | k1_tarski(sK3) != sK4 ),
    inference(cnf_transformation,[],[f39])).

fof(f90,plain,
    ( k1_xboole_0 != sK5
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4 ),
    inference(definition_unfolding,[],[f68,f72])).

fof(f66,plain,
    ( k1_tarski(sK3) != sK5
    | k1_tarski(sK3) != sK4 ),
    inference(cnf_transformation,[],[f39])).

fof(f92,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4 ),
    inference(definition_unfolding,[],[f66,f72,f72])).

fof(f67,plain,
    ( k1_tarski(sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f39])).

fof(f91,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(definition_unfolding,[],[f67,f72])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_708,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_23,negated_conjecture,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_705,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3034,plain,
    ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_705])).

cnf(c_3728,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(sK0(X0,X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sK4) = iProver_top
    | r2_hidden(sK0(X0,X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_708,c_3034])).

cnf(c_6158,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(sK0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0) = iProver_top
    | r2_hidden(sK0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sK4) = iProver_top
    | r2_hidden(sK0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3728,c_3034])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_707,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2756,plain,
    ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_707])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_710,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4288,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = X1
    | r2_hidden(sK0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1),X1) != iProver_top
    | r2_hidden(sK0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2756,c_710])).

cnf(c_4861,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(sK0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2756,c_4288])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_706,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2147,plain,
    ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_706])).

cnf(c_4289,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = X1
    | r2_hidden(sK0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1),X1) != iProver_top
    | r2_hidden(sK0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2147,c_710])).

cnf(c_5266,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(sK0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2147,c_4289])).

cnf(c_7030,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(sK0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6158,c_4861,c_5266])).

cnf(c_7058,plain,
    ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_7030,c_4861])).

cnf(c_11,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_701,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8259,plain,
    ( r1_tarski(sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7058,c_701])).

cnf(c_376,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1821,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k1_xboole_0)
    | X2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_376])).

cnf(c_5753,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(X1,k1_xboole_0)
    | X1 != X0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_1821])).

cnf(c_5757,plain,
    ( ~ r2_hidden(sK3,sK5)
    | r2_hidden(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_5753])).

cnf(c_8,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_704,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_697,plain,
    ( X0 = X1
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2857,plain,
    ( sK3 = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2756,c_697])).

cnf(c_3209,plain,
    ( sK1(sK5) = sK3
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_704,c_2857])).

cnf(c_3705,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3209,c_704])).

cnf(c_37,plain,
    ( ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_40,plain,
    ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_7,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_234,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_7])).

cnf(c_235,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_234])).

cnf(c_236,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_235])).

cnf(c_238,plain,
    ( r2_hidden(sK3,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_236])).

cnf(c_692,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_235])).

cnf(c_1031,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_704,c_692])).

cnf(c_1006,plain,
    ( r1_tarski(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_701])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_693,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1183,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1006,c_693])).

cnf(c_20,negated_conjecture,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1433,plain,
    ( sK4 = k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1183,c_20])).

cnf(c_375,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_861,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_1778,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_698,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3083,plain,
    ( r2_hidden(sK3,sK4) = iProver_top
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_698,c_3034])).

cnf(c_3688,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(X1,k1_xboole_0)
    | X1 != X0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1821])).

cnf(c_3689,plain,
    ( X0 != X1
    | k1_xboole_0 != sK4
    | r2_hidden(X1,sK4) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3688])).

cnf(c_3691,plain,
    ( sK3 != sK3
    | k1_xboole_0 != sK4
    | r2_hidden(sK3,sK4) != iProver_top
    | r2_hidden(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3689])).

cnf(c_4513,plain,
    ( r2_hidden(sK3,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3705,c_37,c_40,c_238,c_1031,c_1433,c_1778,c_3083,c_3691])).

cnf(c_4515,plain,
    ( r2_hidden(sK3,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4513])).

cnf(c_22,negated_conjecture,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1431,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1183,c_22])).

cnf(c_21,negated_conjecture,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_926,plain,
    ( ~ r1_tarski(sK4,k3_enumset1(X0,X0,X0,X0,X0))
    | k3_enumset1(X0,X0,X0,X0,X0) = sK4
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_928,plain,
    ( ~ r1_tarski(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_926])).

cnf(c_1007,plain,
    ( r1_tarski(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1006])).

cnf(c_1496,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1431,c_22,c_21,c_928,c_1007])).

cnf(c_921,plain,
    ( ~ r1_tarski(sK5,k3_enumset1(X0,X0,X0,X0,X0))
    | k3_enumset1(X0,X0,X0,X0,X0) = sK5
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_922,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = sK5
    | k1_xboole_0 = sK5
    | r1_tarski(sK5,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_921])).

cnf(c_924,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK5
    | k1_xboole_0 = sK5
    | r1_tarski(sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_922])).

cnf(c_237,plain,
    ( ~ r2_hidden(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_235])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8259,c_5757,c_4515,c_1496,c_924,c_237,c_40,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.70/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.00  
% 2.70/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.70/1.00  
% 2.70/1.00  ------  iProver source info
% 2.70/1.00  
% 2.70/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.70/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.70/1.00  git: non_committed_changes: false
% 2.70/1.00  git: last_make_outside_of_git: false
% 2.70/1.00  
% 2.70/1.00  ------ 
% 2.70/1.00  
% 2.70/1.00  ------ Input Options
% 2.70/1.00  
% 2.70/1.00  --out_options                           all
% 2.70/1.00  --tptp_safe_out                         true
% 2.70/1.00  --problem_path                          ""
% 2.70/1.00  --include_path                          ""
% 2.70/1.00  --clausifier                            res/vclausify_rel
% 2.70/1.00  --clausifier_options                    --mode clausify
% 2.70/1.00  --stdin                                 false
% 2.70/1.00  --stats_out                             all
% 2.70/1.00  
% 2.70/1.00  ------ General Options
% 2.70/1.00  
% 2.70/1.00  --fof                                   false
% 2.70/1.00  --time_out_real                         305.
% 2.70/1.00  --time_out_virtual                      -1.
% 2.70/1.00  --symbol_type_check                     false
% 2.70/1.00  --clausify_out                          false
% 2.70/1.00  --sig_cnt_out                           false
% 2.70/1.00  --trig_cnt_out                          false
% 2.70/1.00  --trig_cnt_out_tolerance                1.
% 2.70/1.00  --trig_cnt_out_sk_spl                   false
% 2.70/1.00  --abstr_cl_out                          false
% 2.70/1.00  
% 2.70/1.00  ------ Global Options
% 2.70/1.00  
% 2.70/1.00  --schedule                              default
% 2.70/1.00  --add_important_lit                     false
% 2.70/1.00  --prop_solver_per_cl                    1000
% 2.70/1.00  --min_unsat_core                        false
% 2.70/1.00  --soft_assumptions                      false
% 2.70/1.00  --soft_lemma_size                       3
% 2.70/1.00  --prop_impl_unit_size                   0
% 2.70/1.00  --prop_impl_unit                        []
% 2.70/1.00  --share_sel_clauses                     true
% 2.70/1.00  --reset_solvers                         false
% 2.70/1.00  --bc_imp_inh                            [conj_cone]
% 2.70/1.00  --conj_cone_tolerance                   3.
% 2.70/1.00  --extra_neg_conj                        none
% 2.70/1.00  --large_theory_mode                     true
% 2.70/1.00  --prolific_symb_bound                   200
% 2.70/1.00  --lt_threshold                          2000
% 2.70/1.00  --clause_weak_htbl                      true
% 2.70/1.00  --gc_record_bc_elim                     false
% 2.70/1.00  
% 2.70/1.00  ------ Preprocessing Options
% 2.70/1.00  
% 2.70/1.00  --preprocessing_flag                    true
% 2.70/1.00  --time_out_prep_mult                    0.1
% 2.70/1.00  --splitting_mode                        input
% 2.70/1.00  --splitting_grd                         true
% 2.70/1.00  --splitting_cvd                         false
% 2.70/1.00  --splitting_cvd_svl                     false
% 2.70/1.00  --splitting_nvd                         32
% 2.70/1.00  --sub_typing                            true
% 2.70/1.00  --prep_gs_sim                           true
% 2.70/1.00  --prep_unflatten                        true
% 2.70/1.00  --prep_res_sim                          true
% 2.70/1.00  --prep_upred                            true
% 2.70/1.00  --prep_sem_filter                       exhaustive
% 2.70/1.00  --prep_sem_filter_out                   false
% 2.70/1.00  --pred_elim                             true
% 2.70/1.00  --res_sim_input                         true
% 2.70/1.00  --eq_ax_congr_red                       true
% 2.70/1.00  --pure_diseq_elim                       true
% 2.70/1.00  --brand_transform                       false
% 2.70/1.00  --non_eq_to_eq                          false
% 2.70/1.00  --prep_def_merge                        true
% 2.70/1.00  --prep_def_merge_prop_impl              false
% 2.70/1.00  --prep_def_merge_mbd                    true
% 2.70/1.00  --prep_def_merge_tr_red                 false
% 2.70/1.00  --prep_def_merge_tr_cl                  false
% 2.70/1.00  --smt_preprocessing                     true
% 2.70/1.00  --smt_ac_axioms                         fast
% 2.70/1.00  --preprocessed_out                      false
% 2.70/1.00  --preprocessed_stats                    false
% 2.70/1.00  
% 2.70/1.00  ------ Abstraction refinement Options
% 2.70/1.00  
% 2.70/1.00  --abstr_ref                             []
% 2.70/1.00  --abstr_ref_prep                        false
% 2.70/1.00  --abstr_ref_until_sat                   false
% 2.70/1.00  --abstr_ref_sig_restrict                funpre
% 2.70/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/1.00  --abstr_ref_under                       []
% 2.70/1.00  
% 2.70/1.00  ------ SAT Options
% 2.70/1.00  
% 2.70/1.00  --sat_mode                              false
% 2.70/1.00  --sat_fm_restart_options                ""
% 2.70/1.00  --sat_gr_def                            false
% 2.70/1.00  --sat_epr_types                         true
% 2.70/1.00  --sat_non_cyclic_types                  false
% 2.70/1.00  --sat_finite_models                     false
% 2.70/1.00  --sat_fm_lemmas                         false
% 2.70/1.00  --sat_fm_prep                           false
% 2.70/1.00  --sat_fm_uc_incr                        true
% 2.70/1.00  --sat_out_model                         small
% 2.70/1.00  --sat_out_clauses                       false
% 2.70/1.00  
% 2.70/1.00  ------ QBF Options
% 2.70/1.00  
% 2.70/1.00  --qbf_mode                              false
% 2.70/1.00  --qbf_elim_univ                         false
% 2.70/1.00  --qbf_dom_inst                          none
% 2.70/1.00  --qbf_dom_pre_inst                      false
% 2.70/1.00  --qbf_sk_in                             false
% 2.70/1.00  --qbf_pred_elim                         true
% 2.70/1.00  --qbf_split                             512
% 2.70/1.00  
% 2.70/1.00  ------ BMC1 Options
% 2.70/1.00  
% 2.70/1.00  --bmc1_incremental                      false
% 2.70/1.00  --bmc1_axioms                           reachable_all
% 2.70/1.00  --bmc1_min_bound                        0
% 2.70/1.00  --bmc1_max_bound                        -1
% 2.70/1.00  --bmc1_max_bound_default                -1
% 2.70/1.00  --bmc1_symbol_reachability              true
% 2.70/1.00  --bmc1_property_lemmas                  false
% 2.70/1.00  --bmc1_k_induction                      false
% 2.70/1.00  --bmc1_non_equiv_states                 false
% 2.70/1.00  --bmc1_deadlock                         false
% 2.70/1.00  --bmc1_ucm                              false
% 2.70/1.00  --bmc1_add_unsat_core                   none
% 2.70/1.00  --bmc1_unsat_core_children              false
% 2.70/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/1.00  --bmc1_out_stat                         full
% 2.70/1.00  --bmc1_ground_init                      false
% 2.70/1.00  --bmc1_pre_inst_next_state              false
% 2.70/1.00  --bmc1_pre_inst_state                   false
% 2.70/1.00  --bmc1_pre_inst_reach_state             false
% 2.70/1.00  --bmc1_out_unsat_core                   false
% 2.70/1.00  --bmc1_aig_witness_out                  false
% 2.70/1.00  --bmc1_verbose                          false
% 2.70/1.00  --bmc1_dump_clauses_tptp                false
% 2.70/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.70/1.00  --bmc1_dump_file                        -
% 2.70/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.70/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.70/1.00  --bmc1_ucm_extend_mode                  1
% 2.70/1.00  --bmc1_ucm_init_mode                    2
% 2.70/1.00  --bmc1_ucm_cone_mode                    none
% 2.70/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.70/1.00  --bmc1_ucm_relax_model                  4
% 2.70/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.70/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/1.00  --bmc1_ucm_layered_model                none
% 2.70/1.00  --bmc1_ucm_max_lemma_size               10
% 2.70/1.00  
% 2.70/1.00  ------ AIG Options
% 2.70/1.00  
% 2.70/1.00  --aig_mode                              false
% 2.70/1.00  
% 2.70/1.00  ------ Instantiation Options
% 2.70/1.00  
% 2.70/1.00  --instantiation_flag                    true
% 2.70/1.00  --inst_sos_flag                         false
% 2.70/1.00  --inst_sos_phase                        true
% 2.70/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/1.00  --inst_lit_sel_side                     num_symb
% 2.70/1.00  --inst_solver_per_active                1400
% 2.70/1.00  --inst_solver_calls_frac                1.
% 2.70/1.00  --inst_passive_queue_type               priority_queues
% 2.70/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/1.00  --inst_passive_queues_freq              [25;2]
% 2.70/1.00  --inst_dismatching                      true
% 2.70/1.00  --inst_eager_unprocessed_to_passive     true
% 2.70/1.00  --inst_prop_sim_given                   true
% 2.70/1.00  --inst_prop_sim_new                     false
% 2.70/1.00  --inst_subs_new                         false
% 2.70/1.00  --inst_eq_res_simp                      false
% 2.70/1.00  --inst_subs_given                       false
% 2.70/1.00  --inst_orphan_elimination               true
% 2.70/1.00  --inst_learning_loop_flag               true
% 2.70/1.00  --inst_learning_start                   3000
% 2.70/1.00  --inst_learning_factor                  2
% 2.70/1.00  --inst_start_prop_sim_after_learn       3
% 2.70/1.00  --inst_sel_renew                        solver
% 2.70/1.00  --inst_lit_activity_flag                true
% 2.70/1.00  --inst_restr_to_given                   false
% 2.70/1.00  --inst_activity_threshold               500
% 2.70/1.00  --inst_out_proof                        true
% 2.70/1.00  
% 2.70/1.00  ------ Resolution Options
% 2.70/1.00  
% 2.70/1.00  --resolution_flag                       true
% 2.70/1.00  --res_lit_sel                           adaptive
% 2.70/1.00  --res_lit_sel_side                      none
% 2.70/1.00  --res_ordering                          kbo
% 2.70/1.00  --res_to_prop_solver                    active
% 2.70/1.00  --res_prop_simpl_new                    false
% 2.70/1.00  --res_prop_simpl_given                  true
% 2.70/1.00  --res_passive_queue_type                priority_queues
% 2.70/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/1.00  --res_passive_queues_freq               [15;5]
% 2.70/1.00  --res_forward_subs                      full
% 2.70/1.00  --res_backward_subs                     full
% 2.70/1.00  --res_forward_subs_resolution           true
% 2.70/1.00  --res_backward_subs_resolution          true
% 2.70/1.00  --res_orphan_elimination                true
% 2.70/1.00  --res_time_limit                        2.
% 2.70/1.00  --res_out_proof                         true
% 2.70/1.00  
% 2.70/1.00  ------ Superposition Options
% 2.70/1.00  
% 2.70/1.00  --superposition_flag                    true
% 2.70/1.00  --sup_passive_queue_type                priority_queues
% 2.70/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.70/1.00  --demod_completeness_check              fast
% 2.70/1.00  --demod_use_ground                      true
% 2.70/1.00  --sup_to_prop_solver                    passive
% 2.70/1.00  --sup_prop_simpl_new                    true
% 2.70/1.00  --sup_prop_simpl_given                  true
% 2.70/1.00  --sup_fun_splitting                     false
% 2.70/1.00  --sup_smt_interval                      50000
% 2.70/1.00  
% 2.70/1.00  ------ Superposition Simplification Setup
% 2.70/1.00  
% 2.70/1.00  --sup_indices_passive                   []
% 2.70/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.00  --sup_full_bw                           [BwDemod]
% 2.70/1.00  --sup_immed_triv                        [TrivRules]
% 2.70/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.00  --sup_immed_bw_main                     []
% 2.70/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/1.00  
% 2.70/1.00  ------ Combination Options
% 2.70/1.00  
% 2.70/1.00  --comb_res_mult                         3
% 2.70/1.00  --comb_sup_mult                         2
% 2.70/1.00  --comb_inst_mult                        10
% 2.70/1.00  
% 2.70/1.00  ------ Debug Options
% 2.70/1.00  
% 2.70/1.00  --dbg_backtrace                         false
% 2.70/1.00  --dbg_dump_prop_clauses                 false
% 2.70/1.00  --dbg_dump_prop_clauses_file            -
% 2.70/1.00  --dbg_out_stat                          false
% 2.70/1.00  ------ Parsing...
% 2.70/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.70/1.00  
% 2.70/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.70/1.00  
% 2.70/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.70/1.00  
% 2.70/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.70/1.00  ------ Proving...
% 2.70/1.00  ------ Problem Properties 
% 2.70/1.00  
% 2.70/1.00  
% 2.70/1.00  clauses                                 23
% 2.70/1.00  conjectures                             4
% 2.70/1.00  EPR                                     1
% 2.70/1.00  Horn                                    18
% 2.70/1.00  unary                                   6
% 2.70/1.00  binary                                  10
% 2.70/1.00  lits                                    48
% 2.70/1.00  lits eq                                 20
% 2.70/1.00  fd_pure                                 0
% 2.70/1.00  fd_pseudo                               0
% 2.70/1.00  fd_cond                                 1
% 2.70/1.00  fd_pseudo_cond                          6
% 2.70/1.00  AC symbols                              0
% 2.70/1.00  
% 2.70/1.00  ------ Schedule dynamic 5 is on 
% 2.70/1.00  
% 2.70/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.70/1.00  
% 2.70/1.00  
% 2.70/1.00  ------ 
% 2.70/1.00  Current options:
% 2.70/1.00  ------ 
% 2.70/1.00  
% 2.70/1.00  ------ Input Options
% 2.70/1.00  
% 2.70/1.00  --out_options                           all
% 2.70/1.00  --tptp_safe_out                         true
% 2.70/1.00  --problem_path                          ""
% 2.70/1.00  --include_path                          ""
% 2.70/1.00  --clausifier                            res/vclausify_rel
% 2.70/1.00  --clausifier_options                    --mode clausify
% 2.70/1.00  --stdin                                 false
% 2.70/1.00  --stats_out                             all
% 2.70/1.00  
% 2.70/1.00  ------ General Options
% 2.70/1.00  
% 2.70/1.00  --fof                                   false
% 2.70/1.00  --time_out_real                         305.
% 2.70/1.00  --time_out_virtual                      -1.
% 2.70/1.00  --symbol_type_check                     false
% 2.70/1.00  --clausify_out                          false
% 2.70/1.00  --sig_cnt_out                           false
% 2.70/1.00  --trig_cnt_out                          false
% 2.70/1.00  --trig_cnt_out_tolerance                1.
% 2.70/1.00  --trig_cnt_out_sk_spl                   false
% 2.70/1.00  --abstr_cl_out                          false
% 2.70/1.00  
% 2.70/1.00  ------ Global Options
% 2.70/1.00  
% 2.70/1.00  --schedule                              default
% 2.70/1.00  --add_important_lit                     false
% 2.70/1.00  --prop_solver_per_cl                    1000
% 2.70/1.00  --min_unsat_core                        false
% 2.70/1.00  --soft_assumptions                      false
% 2.70/1.00  --soft_lemma_size                       3
% 2.70/1.00  --prop_impl_unit_size                   0
% 2.70/1.00  --prop_impl_unit                        []
% 2.70/1.00  --share_sel_clauses                     true
% 2.70/1.00  --reset_solvers                         false
% 2.70/1.00  --bc_imp_inh                            [conj_cone]
% 2.70/1.00  --conj_cone_tolerance                   3.
% 2.70/1.00  --extra_neg_conj                        none
% 2.70/1.00  --large_theory_mode                     true
% 2.70/1.00  --prolific_symb_bound                   200
% 2.70/1.00  --lt_threshold                          2000
% 2.70/1.00  --clause_weak_htbl                      true
% 2.70/1.00  --gc_record_bc_elim                     false
% 2.70/1.00  
% 2.70/1.00  ------ Preprocessing Options
% 2.70/1.00  
% 2.70/1.00  --preprocessing_flag                    true
% 2.70/1.00  --time_out_prep_mult                    0.1
% 2.70/1.00  --splitting_mode                        input
% 2.70/1.00  --splitting_grd                         true
% 2.70/1.00  --splitting_cvd                         false
% 2.70/1.00  --splitting_cvd_svl                     false
% 2.70/1.00  --splitting_nvd                         32
% 2.70/1.00  --sub_typing                            true
% 2.70/1.00  --prep_gs_sim                           true
% 2.70/1.00  --prep_unflatten                        true
% 2.70/1.00  --prep_res_sim                          true
% 2.70/1.00  --prep_upred                            true
% 2.70/1.00  --prep_sem_filter                       exhaustive
% 2.70/1.00  --prep_sem_filter_out                   false
% 2.70/1.00  --pred_elim                             true
% 2.70/1.00  --res_sim_input                         true
% 2.70/1.00  --eq_ax_congr_red                       true
% 2.70/1.00  --pure_diseq_elim                       true
% 2.70/1.00  --brand_transform                       false
% 2.70/1.00  --non_eq_to_eq                          false
% 2.70/1.00  --prep_def_merge                        true
% 2.70/1.00  --prep_def_merge_prop_impl              false
% 2.70/1.00  --prep_def_merge_mbd                    true
% 2.70/1.00  --prep_def_merge_tr_red                 false
% 2.70/1.00  --prep_def_merge_tr_cl                  false
% 2.70/1.00  --smt_preprocessing                     true
% 2.70/1.00  --smt_ac_axioms                         fast
% 2.70/1.00  --preprocessed_out                      false
% 2.70/1.00  --preprocessed_stats                    false
% 2.70/1.00  
% 2.70/1.00  ------ Abstraction refinement Options
% 2.70/1.00  
% 2.70/1.00  --abstr_ref                             []
% 2.70/1.00  --abstr_ref_prep                        false
% 2.70/1.00  --abstr_ref_until_sat                   false
% 2.70/1.00  --abstr_ref_sig_restrict                funpre
% 2.70/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/1.00  --abstr_ref_under                       []
% 2.70/1.00  
% 2.70/1.00  ------ SAT Options
% 2.70/1.00  
% 2.70/1.00  --sat_mode                              false
% 2.70/1.00  --sat_fm_restart_options                ""
% 2.70/1.00  --sat_gr_def                            false
% 2.70/1.00  --sat_epr_types                         true
% 2.70/1.00  --sat_non_cyclic_types                  false
% 2.70/1.00  --sat_finite_models                     false
% 2.70/1.00  --sat_fm_lemmas                         false
% 2.70/1.00  --sat_fm_prep                           false
% 2.70/1.00  --sat_fm_uc_incr                        true
% 2.70/1.00  --sat_out_model                         small
% 2.70/1.00  --sat_out_clauses                       false
% 2.70/1.00  
% 2.70/1.00  ------ QBF Options
% 2.70/1.00  
% 2.70/1.00  --qbf_mode                              false
% 2.70/1.00  --qbf_elim_univ                         false
% 2.70/1.00  --qbf_dom_inst                          none
% 2.70/1.00  --qbf_dom_pre_inst                      false
% 2.70/1.00  --qbf_sk_in                             false
% 2.70/1.00  --qbf_pred_elim                         true
% 2.70/1.00  --qbf_split                             512
% 2.70/1.00  
% 2.70/1.00  ------ BMC1 Options
% 2.70/1.00  
% 2.70/1.00  --bmc1_incremental                      false
% 2.70/1.00  --bmc1_axioms                           reachable_all
% 2.70/1.00  --bmc1_min_bound                        0
% 2.70/1.00  --bmc1_max_bound                        -1
% 2.70/1.00  --bmc1_max_bound_default                -1
% 2.70/1.00  --bmc1_symbol_reachability              true
% 2.70/1.00  --bmc1_property_lemmas                  false
% 2.70/1.00  --bmc1_k_induction                      false
% 2.70/1.00  --bmc1_non_equiv_states                 false
% 2.70/1.00  --bmc1_deadlock                         false
% 2.70/1.00  --bmc1_ucm                              false
% 2.70/1.00  --bmc1_add_unsat_core                   none
% 2.70/1.00  --bmc1_unsat_core_children              false
% 2.70/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/1.00  --bmc1_out_stat                         full
% 2.70/1.00  --bmc1_ground_init                      false
% 2.70/1.00  --bmc1_pre_inst_next_state              false
% 2.70/1.00  --bmc1_pre_inst_state                   false
% 2.70/1.00  --bmc1_pre_inst_reach_state             false
% 2.70/1.00  --bmc1_out_unsat_core                   false
% 2.70/1.00  --bmc1_aig_witness_out                  false
% 2.70/1.00  --bmc1_verbose                          false
% 2.70/1.00  --bmc1_dump_clauses_tptp                false
% 2.70/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.70/1.00  --bmc1_dump_file                        -
% 2.70/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.70/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.70/1.00  --bmc1_ucm_extend_mode                  1
% 2.70/1.00  --bmc1_ucm_init_mode                    2
% 2.70/1.00  --bmc1_ucm_cone_mode                    none
% 2.70/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.70/1.00  --bmc1_ucm_relax_model                  4
% 2.70/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.70/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/1.00  --bmc1_ucm_layered_model                none
% 2.70/1.00  --bmc1_ucm_max_lemma_size               10
% 2.70/1.00  
% 2.70/1.00  ------ AIG Options
% 2.70/1.00  
% 2.70/1.00  --aig_mode                              false
% 2.70/1.00  
% 2.70/1.00  ------ Instantiation Options
% 2.70/1.00  
% 2.70/1.00  --instantiation_flag                    true
% 2.70/1.00  --inst_sos_flag                         false
% 2.70/1.00  --inst_sos_phase                        true
% 2.70/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/1.00  --inst_lit_sel_side                     none
% 2.70/1.00  --inst_solver_per_active                1400
% 2.70/1.00  --inst_solver_calls_frac                1.
% 2.70/1.00  --inst_passive_queue_type               priority_queues
% 2.70/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/1.00  --inst_passive_queues_freq              [25;2]
% 2.70/1.00  --inst_dismatching                      true
% 2.70/1.00  --inst_eager_unprocessed_to_passive     true
% 2.70/1.00  --inst_prop_sim_given                   true
% 2.70/1.00  --inst_prop_sim_new                     false
% 2.70/1.00  --inst_subs_new                         false
% 2.70/1.00  --inst_eq_res_simp                      false
% 2.70/1.00  --inst_subs_given                       false
% 2.70/1.00  --inst_orphan_elimination               true
% 2.70/1.00  --inst_learning_loop_flag               true
% 2.70/1.00  --inst_learning_start                   3000
% 2.70/1.00  --inst_learning_factor                  2
% 2.70/1.00  --inst_start_prop_sim_after_learn       3
% 2.70/1.00  --inst_sel_renew                        solver
% 2.70/1.00  --inst_lit_activity_flag                true
% 2.70/1.00  --inst_restr_to_given                   false
% 2.70/1.00  --inst_activity_threshold               500
% 2.70/1.00  --inst_out_proof                        true
% 2.70/1.00  
% 2.70/1.00  ------ Resolution Options
% 2.70/1.00  
% 2.70/1.00  --resolution_flag                       false
% 2.70/1.00  --res_lit_sel                           adaptive
% 2.70/1.00  --res_lit_sel_side                      none
% 2.70/1.00  --res_ordering                          kbo
% 2.70/1.00  --res_to_prop_solver                    active
% 2.70/1.00  --res_prop_simpl_new                    false
% 2.70/1.00  --res_prop_simpl_given                  true
% 2.70/1.00  --res_passive_queue_type                priority_queues
% 2.70/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/1.00  --res_passive_queues_freq               [15;5]
% 2.70/1.00  --res_forward_subs                      full
% 2.70/1.00  --res_backward_subs                     full
% 2.70/1.00  --res_forward_subs_resolution           true
% 2.70/1.00  --res_backward_subs_resolution          true
% 2.70/1.00  --res_orphan_elimination                true
% 2.70/1.00  --res_time_limit                        2.
% 2.70/1.00  --res_out_proof                         true
% 2.70/1.00  
% 2.70/1.00  ------ Superposition Options
% 2.70/1.00  
% 2.70/1.00  --superposition_flag                    true
% 2.70/1.00  --sup_passive_queue_type                priority_queues
% 2.70/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.70/1.00  --demod_completeness_check              fast
% 2.70/1.00  --demod_use_ground                      true
% 2.70/1.00  --sup_to_prop_solver                    passive
% 2.70/1.00  --sup_prop_simpl_new                    true
% 2.70/1.00  --sup_prop_simpl_given                  true
% 2.70/1.00  --sup_fun_splitting                     false
% 2.70/1.00  --sup_smt_interval                      50000
% 2.70/1.00  
% 2.70/1.00  ------ Superposition Simplification Setup
% 2.70/1.00  
% 2.70/1.00  --sup_indices_passive                   []
% 2.70/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.00  --sup_full_bw                           [BwDemod]
% 2.70/1.00  --sup_immed_triv                        [TrivRules]
% 2.70/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.00  --sup_immed_bw_main                     []
% 2.70/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/1.00  
% 2.70/1.00  ------ Combination Options
% 2.70/1.00  
% 2.70/1.00  --comb_res_mult                         3
% 2.70/1.00  --comb_sup_mult                         2
% 2.70/1.00  --comb_inst_mult                        10
% 2.70/1.00  
% 2.70/1.00  ------ Debug Options
% 2.70/1.00  
% 2.70/1.00  --dbg_backtrace                         false
% 2.70/1.00  --dbg_dump_prop_clauses                 false
% 2.70/1.00  --dbg_dump_prop_clauses_file            -
% 2.70/1.00  --dbg_out_stat                          false
% 2.70/1.00  
% 2.70/1.00  
% 2.70/1.00  
% 2.70/1.00  
% 2.70/1.00  ------ Proving...
% 2.70/1.00  
% 2.70/1.00  
% 2.70/1.00  % SZS status Theorem for theBenchmark.p
% 2.70/1.00  
% 2.70/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.70/1.00  
% 2.70/1.00  fof(f2,axiom,(
% 2.70/1.00    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f25,plain,(
% 2.70/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.70/1.00    inference(nnf_transformation,[],[f2])).
% 2.70/1.00  
% 2.70/1.00  fof(f26,plain,(
% 2.70/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.70/1.00    inference(flattening,[],[f25])).
% 2.70/1.00  
% 2.70/1.00  fof(f27,plain,(
% 2.70/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.70/1.00    inference(rectify,[],[f26])).
% 2.70/1.00  
% 2.70/1.00  fof(f28,plain,(
% 2.70/1.00    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.70/1.00    introduced(choice_axiom,[])).
% 2.70/1.00  
% 2.70/1.00  fof(f29,plain,(
% 2.70/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.70/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 2.70/1.00  
% 2.70/1.00  fof(f44,plain,(
% 2.70/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.70/1.00    inference(cnf_transformation,[],[f29])).
% 2.70/1.00  
% 2.70/1.00  fof(f15,axiom,(
% 2.70/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f64,plain,(
% 2.70/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.70/1.00    inference(cnf_transformation,[],[f15])).
% 2.70/1.00  
% 2.70/1.00  fof(f10,axiom,(
% 2.70/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f57,plain,(
% 2.70/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.70/1.00    inference(cnf_transformation,[],[f10])).
% 2.70/1.00  
% 2.70/1.00  fof(f11,axiom,(
% 2.70/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f58,plain,(
% 2.70/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.70/1.00    inference(cnf_transformation,[],[f11])).
% 2.70/1.00  
% 2.70/1.00  fof(f12,axiom,(
% 2.70/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f59,plain,(
% 2.70/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.70/1.00    inference(cnf_transformation,[],[f12])).
% 2.70/1.00  
% 2.70/1.00  fof(f69,plain,(
% 2.70/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.70/1.00    inference(definition_unfolding,[],[f58,f59])).
% 2.70/1.00  
% 2.70/1.00  fof(f70,plain,(
% 2.70/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.70/1.00    inference(definition_unfolding,[],[f57,f69])).
% 2.70/1.00  
% 2.70/1.00  fof(f71,plain,(
% 2.70/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 2.70/1.00    inference(definition_unfolding,[],[f64,f70])).
% 2.70/1.00  
% 2.70/1.00  fof(f75,plain,(
% 2.70/1.00    ( ! [X2,X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.70/1.00    inference(definition_unfolding,[],[f44,f71])).
% 2.70/1.00  
% 2.70/1.00  fof(f16,conjecture,(
% 2.70/1.00    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f17,negated_conjecture,(
% 2.70/1.00    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.70/1.00    inference(negated_conjecture,[],[f16])).
% 2.70/1.00  
% 2.70/1.00  fof(f24,plain,(
% 2.70/1.00    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.70/1.00    inference(ennf_transformation,[],[f17])).
% 2.70/1.00  
% 2.70/1.00  fof(f38,plain,(
% 2.70/1.00    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4) & (k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4) & (k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4) & k2_xboole_0(sK4,sK5) = k1_tarski(sK3))),
% 2.70/1.00    introduced(choice_axiom,[])).
% 2.70/1.00  
% 2.70/1.00  fof(f39,plain,(
% 2.70/1.00    (k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4) & (k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4) & (k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4) & k2_xboole_0(sK4,sK5) = k1_tarski(sK3)),
% 2.70/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f24,f38])).
% 2.70/1.00  
% 2.70/1.00  fof(f65,plain,(
% 2.70/1.00    k2_xboole_0(sK4,sK5) = k1_tarski(sK3)),
% 2.70/1.00    inference(cnf_transformation,[],[f39])).
% 2.70/1.00  
% 2.70/1.00  fof(f9,axiom,(
% 2.70/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f56,plain,(
% 2.70/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.70/1.00    inference(cnf_transformation,[],[f9])).
% 2.70/1.00  
% 2.70/1.00  fof(f72,plain,(
% 2.70/1.00    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.70/1.00    inference(definition_unfolding,[],[f56,f70])).
% 2.70/1.00  
% 2.70/1.00  fof(f93,plain,(
% 2.70/1.00    k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5))),
% 2.70/1.00    inference(definition_unfolding,[],[f65,f71,f72])).
% 2.70/1.00  
% 2.70/1.00  fof(f41,plain,(
% 2.70/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.70/1.00    inference(cnf_transformation,[],[f29])).
% 2.70/1.00  
% 2.70/1.00  fof(f78,plain,(
% 2.70/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 2.70/1.00    inference(definition_unfolding,[],[f41,f71])).
% 2.70/1.00  
% 2.70/1.00  fof(f96,plain,(
% 2.70/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 2.70/1.00    inference(equality_resolution,[],[f78])).
% 2.70/1.00  
% 2.70/1.00  fof(f43,plain,(
% 2.70/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.70/1.00    inference(cnf_transformation,[],[f29])).
% 2.70/1.00  
% 2.70/1.00  fof(f76,plain,(
% 2.70/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 2.70/1.00    inference(definition_unfolding,[],[f43,f71])).
% 2.70/1.00  
% 2.70/1.00  fof(f94,plain,(
% 2.70/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.70/1.00    inference(equality_resolution,[],[f76])).
% 2.70/1.00  
% 2.70/1.00  fof(f46,plain,(
% 2.70/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.70/1.00    inference(cnf_transformation,[],[f29])).
% 2.70/1.00  
% 2.70/1.00  fof(f73,plain,(
% 2.70/1.00    ( ! [X2,X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.70/1.00    inference(definition_unfolding,[],[f46,f71])).
% 2.70/1.00  
% 2.70/1.00  fof(f42,plain,(
% 2.70/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 2.70/1.00    inference(cnf_transformation,[],[f29])).
% 2.70/1.00  
% 2.70/1.00  fof(f77,plain,(
% 2.70/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 2.70/1.00    inference(definition_unfolding,[],[f42,f71])).
% 2.70/1.00  
% 2.70/1.00  fof(f95,plain,(
% 2.70/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 2.70/1.00    inference(equality_resolution,[],[f77])).
% 2.70/1.00  
% 2.70/1.00  fof(f7,axiom,(
% 2.70/1.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f51,plain,(
% 2.70/1.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.70/1.00    inference(cnf_transformation,[],[f7])).
% 2.70/1.00  
% 2.70/1.00  fof(f81,plain,(
% 2.70/1.00    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 2.70/1.00    inference(definition_unfolding,[],[f51,f71])).
% 2.70/1.00  
% 2.70/1.00  fof(f4,axiom,(
% 2.70/1.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f20,plain,(
% 2.70/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.70/1.00    inference(ennf_transformation,[],[f4])).
% 2.70/1.00  
% 2.70/1.00  fof(f30,plain,(
% 2.70/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 2.70/1.00    introduced(choice_axiom,[])).
% 2.70/1.00  
% 2.70/1.00  fof(f31,plain,(
% 2.70/1.00    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 2.70/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f30])).
% 2.70/1.00  
% 2.70/1.00  fof(f48,plain,(
% 2.70/1.00    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.70/1.00    inference(cnf_transformation,[],[f31])).
% 2.70/1.00  
% 2.70/1.00  fof(f8,axiom,(
% 2.70/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f32,plain,(
% 2.70/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.70/1.00    inference(nnf_transformation,[],[f8])).
% 2.70/1.00  
% 2.70/1.00  fof(f33,plain,(
% 2.70/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.70/1.00    inference(rectify,[],[f32])).
% 2.70/1.00  
% 2.70/1.00  fof(f34,plain,(
% 2.70/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 2.70/1.00    introduced(choice_axiom,[])).
% 2.70/1.00  
% 2.70/1.00  fof(f35,plain,(
% 2.70/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.70/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 2.70/1.00  
% 2.70/1.00  fof(f52,plain,(
% 2.70/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.70/1.00    inference(cnf_transformation,[],[f35])).
% 2.70/1.00  
% 2.70/1.00  fof(f85,plain,(
% 2.70/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 2.70/1.00    inference(definition_unfolding,[],[f52,f72])).
% 2.70/1.00  
% 2.70/1.00  fof(f99,plain,(
% 2.70/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 2.70/1.00    inference(equality_resolution,[],[f85])).
% 2.70/1.00  
% 2.70/1.00  fof(f53,plain,(
% 2.70/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.70/1.00    inference(cnf_transformation,[],[f35])).
% 2.70/1.00  
% 2.70/1.00  fof(f84,plain,(
% 2.70/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 2.70/1.00    inference(definition_unfolding,[],[f53,f72])).
% 2.70/1.00  
% 2.70/1.00  fof(f97,plain,(
% 2.70/1.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 2.70/1.00    inference(equality_resolution,[],[f84])).
% 2.70/1.00  
% 2.70/1.00  fof(f98,plain,(
% 2.70/1.00    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 2.70/1.00    inference(equality_resolution,[],[f97])).
% 2.70/1.00  
% 2.70/1.00  fof(f1,axiom,(
% 2.70/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f18,plain,(
% 2.70/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.70/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 2.70/1.00  
% 2.70/1.00  fof(f19,plain,(
% 2.70/1.00    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.70/1.00    inference(ennf_transformation,[],[f18])).
% 2.70/1.00  
% 2.70/1.00  fof(f40,plain,(
% 2.70/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.70/1.00    inference(cnf_transformation,[],[f19])).
% 2.70/1.00  
% 2.70/1.00  fof(f3,axiom,(
% 2.70/1.00    v1_xboole_0(k1_xboole_0)),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f47,plain,(
% 2.70/1.00    v1_xboole_0(k1_xboole_0)),
% 2.70/1.00    inference(cnf_transformation,[],[f3])).
% 2.70/1.00  
% 2.70/1.00  fof(f14,axiom,(
% 2.70/1.00    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.70/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/1.00  
% 2.70/1.00  fof(f36,plain,(
% 2.70/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.70/1.00    inference(nnf_transformation,[],[f14])).
% 2.70/1.00  
% 2.70/1.00  fof(f37,plain,(
% 2.70/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.70/1.00    inference(flattening,[],[f36])).
% 2.70/1.00  
% 2.70/1.00  fof(f61,plain,(
% 2.70/1.00    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.70/1.00    inference(cnf_transformation,[],[f37])).
% 2.70/1.00  
% 2.70/1.00  fof(f89,plain,(
% 2.70/1.00    ( ! [X0,X1] : (k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))) )),
% 2.70/1.00    inference(definition_unfolding,[],[f61,f72,f72])).
% 2.70/1.00  
% 2.70/1.00  fof(f68,plain,(
% 2.70/1.00    k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4),
% 2.70/1.00    inference(cnf_transformation,[],[f39])).
% 2.70/1.00  
% 2.70/1.00  fof(f90,plain,(
% 2.70/1.00    k1_xboole_0 != sK5 | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4),
% 2.70/1.00    inference(definition_unfolding,[],[f68,f72])).
% 2.70/1.00  
% 2.70/1.00  fof(f66,plain,(
% 2.70/1.00    k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4),
% 2.70/1.00    inference(cnf_transformation,[],[f39])).
% 2.70/1.00  
% 2.70/1.00  fof(f92,plain,(
% 2.70/1.00    k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4),
% 2.70/1.00    inference(definition_unfolding,[],[f66,f72,f72])).
% 2.70/1.00  
% 2.70/1.00  fof(f67,plain,(
% 2.70/1.00    k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4),
% 2.70/1.00    inference(cnf_transformation,[],[f39])).
% 2.70/1.00  
% 2.70/1.00  fof(f91,plain,(
% 2.70/1.00    k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 | k1_xboole_0 != sK4),
% 2.70/1.00    inference(definition_unfolding,[],[f67,f72])).
% 2.70/1.00  
% 2.70/1.00  cnf(c_3,plain,
% 2.70/1.00      ( r2_hidden(sK0(X0,X1,X2),X1)
% 2.70/1.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.70/1.00      | r2_hidden(sK0(X0,X1,X2),X0)
% 2.70/1.00      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2 ),
% 2.70/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_708,plain,
% 2.70/1.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2
% 2.70/1.00      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
% 2.70/1.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 2.70/1.00      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_23,negated_conjecture,
% 2.70/1.00      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
% 2.70/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_6,plain,
% 2.70/1.00      ( r2_hidden(X0,X1)
% 2.70/1.00      | r2_hidden(X0,X2)
% 2.70/1.00      | ~ r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
% 2.70/1.00      inference(cnf_transformation,[],[f96]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_705,plain,
% 2.70/1.00      ( r2_hidden(X0,X1) = iProver_top
% 2.70/1.00      | r2_hidden(X0,X2) = iProver_top
% 2.70/1.00      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) != iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_3034,plain,
% 2.70/1.00      ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top
% 2.70/1.00      | r2_hidden(X0,sK4) = iProver_top
% 2.70/1.00      | r2_hidden(X0,sK5) = iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_23,c_705]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_3728,plain,
% 2.70/1.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
% 2.70/1.00      | r2_hidden(sK0(X0,X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X1) = iProver_top
% 2.70/1.00      | r2_hidden(sK0(X0,X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0) = iProver_top
% 2.70/1.00      | r2_hidden(sK0(X0,X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sK4) = iProver_top
% 2.70/1.00      | r2_hidden(sK0(X0,X1,k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sK5) = iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_708,c_3034]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_6158,plain,
% 2.70/1.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
% 2.70/1.00      | r2_hidden(sK0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0) = iProver_top
% 2.70/1.00      | r2_hidden(sK0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sK4) = iProver_top
% 2.70/1.00      | r2_hidden(sK0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sK5) = iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_3728,c_3034]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_4,plain,
% 2.70/1.00      ( ~ r2_hidden(X0,X1)
% 2.70/1.00      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
% 2.70/1.00      inference(cnf_transformation,[],[f94]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_707,plain,
% 2.70/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.70/1.00      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_2756,plain,
% 2.70/1.00      ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
% 2.70/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_23,c_707]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1,plain,
% 2.70/1.00      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 2.70/1.00      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 2.70/1.00      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2 ),
% 2.70/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_710,plain,
% 2.70/1.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2
% 2.70/1.00      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 2.70/1.00      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_4288,plain,
% 2.70/1.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = X1
% 2.70/1.00      | r2_hidden(sK0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1),X1) != iProver_top
% 2.70/1.00      | r2_hidden(sK0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1),sK5) != iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_2756,c_710]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_4861,plain,
% 2.70/1.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
% 2.70/1.00      | r2_hidden(sK0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sK5) != iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_2756,c_4288]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_5,plain,
% 2.70/1.00      ( ~ r2_hidden(X0,X1)
% 2.70/1.00      | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
% 2.70/1.00      inference(cnf_transformation,[],[f95]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_706,plain,
% 2.70/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.70/1.00      | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_2147,plain,
% 2.70/1.00      ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top
% 2.70/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_23,c_706]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_4289,plain,
% 2.70/1.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = X1
% 2.70/1.00      | r2_hidden(sK0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1),X1) != iProver_top
% 2.70/1.00      | r2_hidden(sK0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3),X1),sK4) != iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_2147,c_710]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_5266,plain,
% 2.70/1.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
% 2.70/1.00      | r2_hidden(sK0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),sK4) != iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_2147,c_4289]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_7030,plain,
% 2.70/1.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
% 2.70/1.00      | r2_hidden(sK0(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)),X0) = iProver_top ),
% 2.70/1.00      inference(global_propositional_subsumption,
% 2.70/1.00                [status(thm)],
% 2.70/1.00                [c_6158,c_4861,c_5266]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_7058,plain,
% 2.70/1.00      ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_7030,c_4861]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_11,plain,
% 2.70/1.00      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
% 2.70/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_701,plain,
% 2.70/1.00      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_8259,plain,
% 2.70/1.00      ( r1_tarski(sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_7058,c_701]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_376,plain,
% 2.70/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.70/1.00      theory(equality) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1821,plain,
% 2.70/1.00      ( ~ r2_hidden(X0,X1)
% 2.70/1.00      | r2_hidden(X2,k1_xboole_0)
% 2.70/1.00      | X2 != X0
% 2.70/1.00      | k1_xboole_0 != X1 ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_376]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_5753,plain,
% 2.70/1.00      ( ~ r2_hidden(X0,sK5)
% 2.70/1.00      | r2_hidden(X1,k1_xboole_0)
% 2.70/1.00      | X1 != X0
% 2.70/1.00      | k1_xboole_0 != sK5 ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_1821]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_5757,plain,
% 2.70/1.00      ( ~ r2_hidden(sK3,sK5)
% 2.70/1.00      | r2_hidden(sK3,k1_xboole_0)
% 2.70/1.00      | sK3 != sK3
% 2.70/1.00      | k1_xboole_0 != sK5 ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_5753]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_8,plain,
% 2.70/1.00      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 2.70/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_704,plain,
% 2.70/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_15,plain,
% 2.70/1.00      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1 ),
% 2.70/1.00      inference(cnf_transformation,[],[f99]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_697,plain,
% 2.70/1.00      ( X0 = X1
% 2.70/1.00      | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_2857,plain,
% 2.70/1.00      ( sK3 = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_2756,c_697]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_3209,plain,
% 2.70/1.00      ( sK1(sK5) = sK3 | sK5 = k1_xboole_0 ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_704,c_2857]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_3705,plain,
% 2.70/1.00      ( sK5 = k1_xboole_0 | r2_hidden(sK3,sK5) = iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_3209,c_704]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_37,plain,
% 2.70/1.00      ( ~ r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) | sK3 = sK3 ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_14,plain,
% 2.70/1.00      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
% 2.70/1.00      inference(cnf_transformation,[],[f98]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_40,plain,
% 2.70/1.00      ( r2_hidden(sK3,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_0,plain,
% 2.70/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.70/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_7,plain,
% 2.70/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.70/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_234,plain,
% 2.70/1.00      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 2.70/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_7]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_235,plain,
% 2.70/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.70/1.00      inference(unflattening,[status(thm)],[c_234]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_236,plain,
% 2.70/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_235]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_238,plain,
% 2.70/1.00      ( r2_hidden(sK3,k1_xboole_0) != iProver_top ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_236]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_692,plain,
% 2.70/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_235]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1031,plain,
% 2.70/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_704,c_692]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1006,plain,
% 2.70/1.00      ( r1_tarski(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_23,c_701]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_19,plain,
% 2.70/1.00      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
% 2.70/1.00      | k3_enumset1(X1,X1,X1,X1,X1) = X0
% 2.70/1.00      | k1_xboole_0 = X0 ),
% 2.70/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_693,plain,
% 2.70/1.00      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 2.70/1.00      | k1_xboole_0 = X1
% 2.70/1.00      | r1_tarski(X1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1183,plain,
% 2.70/1.00      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4 | sK4 = k1_xboole_0 ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_1006,c_693]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_20,negated_conjecture,
% 2.70/1.00      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4 | k1_xboole_0 != sK5 ),
% 2.70/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1433,plain,
% 2.70/1.00      ( sK4 = k1_xboole_0 | sK5 != k1_xboole_0 ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_1183,c_20]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_375,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_861,plain,
% 2.70/1.00      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_375]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1778,plain,
% 2.70/1.00      ( sK4 != k1_xboole_0
% 2.70/1.00      | k1_xboole_0 = sK4
% 2.70/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_861]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_698,plain,
% 2.70/1.00      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_3083,plain,
% 2.70/1.00      ( r2_hidden(sK3,sK4) = iProver_top
% 2.70/1.00      | r2_hidden(sK3,sK5) = iProver_top ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_698,c_3034]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_3688,plain,
% 2.70/1.00      ( ~ r2_hidden(X0,sK4)
% 2.70/1.00      | r2_hidden(X1,k1_xboole_0)
% 2.70/1.00      | X1 != X0
% 2.70/1.00      | k1_xboole_0 != sK4 ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_1821]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_3689,plain,
% 2.70/1.00      ( X0 != X1
% 2.70/1.00      | k1_xboole_0 != sK4
% 2.70/1.00      | r2_hidden(X1,sK4) != iProver_top
% 2.70/1.00      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_3688]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_3691,plain,
% 2.70/1.00      ( sK3 != sK3
% 2.70/1.00      | k1_xboole_0 != sK4
% 2.70/1.00      | r2_hidden(sK3,sK4) != iProver_top
% 2.70/1.00      | r2_hidden(sK3,k1_xboole_0) = iProver_top ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_3689]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_4513,plain,
% 2.70/1.00      ( r2_hidden(sK3,sK5) = iProver_top ),
% 2.70/1.00      inference(global_propositional_subsumption,
% 2.70/1.00                [status(thm)],
% 2.70/1.00                [c_3705,c_37,c_40,c_238,c_1031,c_1433,c_1778,c_3083,
% 2.70/1.00                 c_3691]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_4515,plain,
% 2.70/1.00      ( r2_hidden(sK3,sK5) ),
% 2.70/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4513]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_22,negated_conjecture,
% 2.70/1.00      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4
% 2.70/1.00      | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 ),
% 2.70/1.00      inference(cnf_transformation,[],[f92]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1431,plain,
% 2.70/1.00      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 | sK4 = k1_xboole_0 ),
% 2.70/1.00      inference(superposition,[status(thm)],[c_1183,c_22]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_21,negated_conjecture,
% 2.70/1.00      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 | k1_xboole_0 != sK4 ),
% 2.70/1.00      inference(cnf_transformation,[],[f91]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_926,plain,
% 2.70/1.00      ( ~ r1_tarski(sK4,k3_enumset1(X0,X0,X0,X0,X0))
% 2.70/1.00      | k3_enumset1(X0,X0,X0,X0,X0) = sK4
% 2.70/1.00      | k1_xboole_0 = sK4 ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_928,plain,
% 2.70/1.00      ( ~ r1_tarski(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))
% 2.70/1.00      | k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4
% 2.70/1.00      | k1_xboole_0 = sK4 ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_926]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1007,plain,
% 2.70/1.00      ( r1_tarski(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 2.70/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1006]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_1496,plain,
% 2.70/1.00      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 ),
% 2.70/1.00      inference(global_propositional_subsumption,
% 2.70/1.00                [status(thm)],
% 2.70/1.00                [c_1431,c_22,c_21,c_928,c_1007]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_921,plain,
% 2.70/1.00      ( ~ r1_tarski(sK5,k3_enumset1(X0,X0,X0,X0,X0))
% 2.70/1.00      | k3_enumset1(X0,X0,X0,X0,X0) = sK5
% 2.70/1.00      | k1_xboole_0 = sK5 ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_922,plain,
% 2.70/1.00      ( k3_enumset1(X0,X0,X0,X0,X0) = sK5
% 2.70/1.00      | k1_xboole_0 = sK5
% 2.70/1.00      | r1_tarski(sK5,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 2.70/1.00      inference(predicate_to_equality,[status(thm)],[c_921]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_924,plain,
% 2.70/1.00      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK5
% 2.70/1.00      | k1_xboole_0 = sK5
% 2.70/1.00      | r1_tarski(sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_922]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(c_237,plain,
% 2.70/1.00      ( ~ r2_hidden(sK3,k1_xboole_0) ),
% 2.70/1.00      inference(instantiation,[status(thm)],[c_235]) ).
% 2.70/1.00  
% 2.70/1.00  cnf(contradiction,plain,
% 2.70/1.00      ( $false ),
% 2.70/1.00      inference(minisat,
% 2.70/1.00                [status(thm)],
% 2.70/1.00                [c_8259,c_5757,c_4515,c_1496,c_924,c_237,c_40,c_37]) ).
% 2.70/1.00  
% 2.70/1.00  
% 2.70/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.70/1.00  
% 2.70/1.00  ------                               Statistics
% 2.70/1.00  
% 2.70/1.00  ------ General
% 2.70/1.00  
% 2.70/1.00  abstr_ref_over_cycles:                  0
% 2.70/1.01  abstr_ref_under_cycles:                 0
% 2.70/1.01  gc_basic_clause_elim:                   0
% 2.70/1.01  forced_gc_time:                         0
% 2.70/1.01  parsing_time:                           0.017
% 2.70/1.01  unif_index_cands_time:                  0.
% 2.70/1.01  unif_index_add_time:                    0.
% 2.70/1.01  orderings_time:                         0.
% 2.70/1.01  out_proof_time:                         0.01
% 2.70/1.01  total_time:                             0.313
% 2.70/1.01  num_of_symbols:                         43
% 2.70/1.01  num_of_terms:                           8063
% 2.70/1.01  
% 2.70/1.01  ------ Preprocessing
% 2.70/1.01  
% 2.70/1.01  num_of_splits:                          0
% 2.70/1.01  num_of_split_atoms:                     0
% 2.70/1.01  num_of_reused_defs:                     0
% 2.70/1.01  num_eq_ax_congr_red:                    18
% 2.70/1.01  num_of_sem_filtered_clauses:            1
% 2.70/1.01  num_of_subtypes:                        0
% 2.70/1.01  monotx_restored_types:                  0
% 2.70/1.01  sat_num_of_epr_types:                   0
% 2.70/1.01  sat_num_of_non_cyclic_types:            0
% 2.70/1.01  sat_guarded_non_collapsed_types:        0
% 2.70/1.01  num_pure_diseq_elim:                    0
% 2.70/1.01  simp_replaced_by:                       0
% 2.70/1.01  res_preprocessed:                       106
% 2.70/1.01  prep_upred:                             0
% 2.70/1.01  prep_unflattend:                        1
% 2.70/1.01  smt_new_axioms:                         0
% 2.70/1.01  pred_elim_cands:                        2
% 2.70/1.01  pred_elim:                              1
% 2.70/1.01  pred_elim_cl:                           1
% 2.70/1.01  pred_elim_cycles:                       3
% 2.70/1.01  merged_defs:                            0
% 2.70/1.01  merged_defs_ncl:                        0
% 2.70/1.01  bin_hyper_res:                          0
% 2.70/1.01  prep_cycles:                            4
% 2.70/1.01  pred_elim_time:                         0.001
% 2.70/1.01  splitting_time:                         0.
% 2.70/1.01  sem_filter_time:                        0.
% 2.70/1.01  monotx_time:                            0.
% 2.70/1.01  subtype_inf_time:                       0.
% 2.70/1.01  
% 2.70/1.01  ------ Problem properties
% 2.70/1.01  
% 2.70/1.01  clauses:                                23
% 2.70/1.01  conjectures:                            4
% 2.70/1.01  epr:                                    1
% 2.70/1.01  horn:                                   18
% 2.70/1.01  ground:                                 4
% 2.70/1.01  unary:                                  6
% 2.70/1.01  binary:                                 10
% 2.70/1.01  lits:                                   48
% 2.70/1.01  lits_eq:                                20
% 2.70/1.01  fd_pure:                                0
% 2.70/1.01  fd_pseudo:                              0
% 2.70/1.01  fd_cond:                                1
% 2.70/1.01  fd_pseudo_cond:                         6
% 2.70/1.01  ac_symbols:                             0
% 2.70/1.01  
% 2.70/1.01  ------ Propositional Solver
% 2.70/1.01  
% 2.70/1.01  prop_solver_calls:                      27
% 2.70/1.01  prop_fast_solver_calls:                 654
% 2.70/1.01  smt_solver_calls:                       0
% 2.70/1.01  smt_fast_solver_calls:                  0
% 2.70/1.01  prop_num_of_clauses:                    2928
% 2.70/1.01  prop_preprocess_simplified:             6923
% 2.70/1.01  prop_fo_subsumed:                       11
% 2.70/1.01  prop_solver_time:                       0.
% 2.70/1.01  smt_solver_time:                        0.
% 2.70/1.01  smt_fast_solver_time:                   0.
% 2.70/1.01  prop_fast_solver_time:                  0.
% 2.70/1.01  prop_unsat_core_time:                   0.
% 2.70/1.01  
% 2.70/1.01  ------ QBF
% 2.70/1.01  
% 2.70/1.01  qbf_q_res:                              0
% 2.70/1.01  qbf_num_tautologies:                    0
% 2.70/1.01  qbf_prep_cycles:                        0
% 2.70/1.01  
% 2.70/1.01  ------ BMC1
% 2.70/1.01  
% 2.70/1.01  bmc1_current_bound:                     -1
% 2.70/1.01  bmc1_last_solved_bound:                 -1
% 2.70/1.01  bmc1_unsat_core_size:                   -1
% 2.70/1.01  bmc1_unsat_core_parents_size:           -1
% 2.70/1.01  bmc1_merge_next_fun:                    0
% 2.70/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.70/1.01  
% 2.70/1.01  ------ Instantiation
% 2.70/1.01  
% 2.70/1.01  inst_num_of_clauses:                    715
% 2.70/1.01  inst_num_in_passive:                    218
% 2.70/1.01  inst_num_in_active:                     300
% 2.70/1.01  inst_num_in_unprocessed:                197
% 2.70/1.01  inst_num_of_loops:                      370
% 2.70/1.01  inst_num_of_learning_restarts:          0
% 2.70/1.01  inst_num_moves_active_passive:          68
% 2.70/1.01  inst_lit_activity:                      0
% 2.70/1.01  inst_lit_activity_moves:                0
% 2.70/1.01  inst_num_tautologies:                   0
% 2.70/1.01  inst_num_prop_implied:                  0
% 2.70/1.01  inst_num_existing_simplified:           0
% 2.70/1.01  inst_num_eq_res_simplified:             0
% 2.70/1.01  inst_num_child_elim:                    0
% 2.70/1.01  inst_num_of_dismatching_blockings:      360
% 2.70/1.01  inst_num_of_non_proper_insts:           701
% 2.70/1.01  inst_num_of_duplicates:                 0
% 2.70/1.01  inst_inst_num_from_inst_to_res:         0
% 2.70/1.01  inst_dismatching_checking_time:         0.
% 2.70/1.01  
% 2.70/1.01  ------ Resolution
% 2.70/1.01  
% 2.70/1.01  res_num_of_clauses:                     0
% 2.70/1.01  res_num_in_passive:                     0
% 2.70/1.01  res_num_in_active:                      0
% 2.70/1.01  res_num_of_loops:                       110
% 2.70/1.01  res_forward_subset_subsumed:            55
% 2.70/1.01  res_backward_subset_subsumed:           4
% 2.70/1.01  res_forward_subsumed:                   0
% 2.70/1.01  res_backward_subsumed:                  0
% 2.70/1.01  res_forward_subsumption_resolution:     0
% 2.70/1.01  res_backward_subsumption_resolution:    0
% 2.70/1.01  res_clause_to_clause_subsumption:       1619
% 2.70/1.01  res_orphan_elimination:                 0
% 2.70/1.01  res_tautology_del:                      35
% 2.70/1.01  res_num_eq_res_simplified:              0
% 2.70/1.01  res_num_sel_changes:                    0
% 2.70/1.01  res_moves_from_active_to_pass:          0
% 2.70/1.01  
% 2.70/1.01  ------ Superposition
% 2.70/1.01  
% 2.70/1.01  sup_time_total:                         0.
% 2.70/1.01  sup_time_generating:                    0.
% 2.70/1.01  sup_time_sim_full:                      0.
% 2.70/1.01  sup_time_sim_immed:                     0.
% 2.70/1.01  
% 2.70/1.01  sup_num_of_clauses:                     274
% 2.70/1.01  sup_num_in_active:                      72
% 2.70/1.01  sup_num_in_passive:                     202
% 2.70/1.01  sup_num_of_loops:                       72
% 2.70/1.01  sup_fw_superposition:                   164
% 2.70/1.01  sup_bw_superposition:                   339
% 2.70/1.01  sup_immediate_simplified:               93
% 2.70/1.01  sup_given_eliminated:                   0
% 2.70/1.01  comparisons_done:                       0
% 2.70/1.01  comparisons_avoided:                    13
% 2.70/1.01  
% 2.70/1.01  ------ Simplifications
% 2.70/1.01  
% 2.70/1.01  
% 2.70/1.01  sim_fw_subset_subsumed:                 63
% 2.70/1.01  sim_bw_subset_subsumed:                 28
% 2.70/1.01  sim_fw_subsumed:                        30
% 2.70/1.01  sim_bw_subsumed:                        2
% 2.70/1.01  sim_fw_subsumption_res:                 5
% 2.70/1.01  sim_bw_subsumption_res:                 1
% 2.70/1.01  sim_tautology_del:                      73
% 2.70/1.01  sim_eq_tautology_del:                   7
% 2.70/1.01  sim_eq_res_simp:                        25
% 2.70/1.01  sim_fw_demodulated:                     4
% 2.70/1.01  sim_bw_demodulated:                     0
% 2.70/1.01  sim_light_normalised:                   2
% 2.70/1.01  sim_joinable_taut:                      0
% 2.70/1.01  sim_joinable_simp:                      0
% 2.70/1.01  sim_ac_normalised:                      0
% 2.70/1.01  sim_smt_subsumption:                    0
% 2.70/1.01  
%------------------------------------------------------------------------------
