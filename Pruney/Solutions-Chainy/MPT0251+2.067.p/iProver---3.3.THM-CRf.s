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
% DateTime   : Thu Dec  3 11:33:13 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 414 expanded)
%              Number of clauses        :   51 ( 138 expanded)
%              Number of leaves         :   21 (  86 expanded)
%              Depth                    :   19
%              Number of atoms          :  319 (1074 expanded)
%              Number of equality atoms :  113 ( 349 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f47,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK4),sK5) != sK5
      & r2_hidden(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( k2_xboole_0(k1_tarski(sK4),sK5) != sK5
    & r2_hidden(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f26,f47])).

fof(f86,plain,(
    r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f89,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f81,f82])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f80,f89])).

fof(f91,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f79,f90])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f84,f91])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f88,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f78,f74])).

fof(f92,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f49,f88,f88])).

fof(f87,plain,(
    k2_xboole_0(k1_tarski(sK4),sK5) != sK5 ),
    inference(cnf_transformation,[],[f48])).

fof(f103,plain,(
    k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k5_xboole_0(sK5,k3_xboole_0(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) != sK5 ),
    inference(definition_unfolding,[],[f87,f88,f91])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

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
    inference(nnf_transformation,[],[f22])).

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

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f111,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f42])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f99,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f75,f88])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f60,f74])).

fof(f108,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f97])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f59,f74])).

fof(f109,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f98])).

cnf(c_32,negated_conjecture,
    ( r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1087,plain,
    ( r2_hidden(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1089,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_26,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1091,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2502,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k3_enumset1(X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1089,c_1091])).

cnf(c_17310,plain,
    ( k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
    inference(superposition,[status(thm)],[c_1087,c_2502])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_31,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k5_xboole_0(sK5,k3_xboole_0(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) != sK5 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1646,plain,
    ( k5_xboole_0(sK5,k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5))) != sK5 ),
    inference(demodulation,[status(thm)],[c_0,c_31])).

cnf(c_18100,plain,
    ( k5_xboole_0(sK5,k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4))) != sK5 ),
    inference(demodulation,[status(thm)],[c_17310,c_1646])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1113,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_27,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1090,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_24,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1092,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1431,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1092,c_1091])).

cnf(c_20,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1095,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3023,plain,
    ( r1_xboole_0(X0,X0) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1431,c_1095])).

cnf(c_3039,plain,
    ( r1_xboole_0(X0,X0) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1113,c_3023])).

cnf(c_3312,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1090,c_3039])).

cnf(c_3482,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3312,c_1091])).

cnf(c_25,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_3485,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_3482,c_25])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1099,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7730,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3485,c_1099])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1097,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6548,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3485,c_1097])).

cnf(c_8063,plain,
    ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7730,c_6548])).

cnf(c_8070,plain,
    ( r1_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1113,c_8063])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1093,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4426,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3312,c_1093])).

cnf(c_8082,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8070,c_4426])).

cnf(c_9060,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_8082,c_3485])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1101,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6577,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1431,c_1101])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1100,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4409,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1431,c_1100])).

cnf(c_9730,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6577,c_4409])).

cnf(c_9737,plain,
    ( r1_tarski(k5_xboole_0(X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1113,c_9730])).

cnf(c_11615,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9737,c_4426])).

cnf(c_18101,plain,
    ( sK5 != sK5 ),
    inference(demodulation,[status(thm)],[c_18100,c_9060,c_11615])).

cnf(c_18102,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_18101])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:06:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.82/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.03  
% 3.82/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.82/1.03  
% 3.82/1.03  ------  iProver source info
% 3.82/1.03  
% 3.82/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.82/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.82/1.03  git: non_committed_changes: false
% 3.82/1.03  git: last_make_outside_of_git: false
% 3.82/1.03  
% 3.82/1.03  ------ 
% 3.82/1.03  ------ Parsing...
% 3.82/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.82/1.03  
% 3.82/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.82/1.03  
% 3.82/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.82/1.03  
% 3.82/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.82/1.03  ------ Proving...
% 3.82/1.03  ------ Problem Properties 
% 3.82/1.03  
% 3.82/1.03  
% 3.82/1.03  clauses                                 32
% 3.82/1.03  conjectures                             2
% 3.82/1.03  EPR                                     5
% 3.82/1.03  Horn                                    21
% 3.82/1.03  unary                                   7
% 3.82/1.03  binary                                  11
% 3.82/1.03  lits                                    73
% 3.82/1.03  lits eq                                 12
% 3.82/1.03  fd_pure                                 0
% 3.82/1.03  fd_pseudo                               0
% 3.82/1.03  fd_cond                                 0
% 3.82/1.03  fd_pseudo_cond                          7
% 3.82/1.03  AC symbols                              0
% 3.82/1.03  
% 3.82/1.03  ------ Input Options Time Limit: Unbounded
% 3.82/1.03  
% 3.82/1.03  
% 3.82/1.03  ------ 
% 3.82/1.03  Current options:
% 3.82/1.03  ------ 
% 3.82/1.03  
% 3.82/1.03  
% 3.82/1.03  
% 3.82/1.03  
% 3.82/1.03  ------ Proving...
% 3.82/1.03  
% 3.82/1.03  
% 3.82/1.03  % SZS status Theorem for theBenchmark.p
% 3.82/1.03  
% 3.82/1.03   Resolution empty clause
% 3.82/1.03  
% 3.82/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.82/1.03  
% 3.82/1.03  fof(f19,conjecture,(
% 3.82/1.03    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.82/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.03  
% 3.82/1.03  fof(f20,negated_conjecture,(
% 3.82/1.03    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.82/1.03    inference(negated_conjecture,[],[f19])).
% 3.82/1.03  
% 3.82/1.03  fof(f26,plain,(
% 3.82/1.03    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 3.82/1.03    inference(ennf_transformation,[],[f20])).
% 3.82/1.03  
% 3.82/1.03  fof(f47,plain,(
% 3.82/1.03    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK4),sK5) != sK5 & r2_hidden(sK4,sK5))),
% 3.82/1.03    introduced(choice_axiom,[])).
% 3.82/1.03  
% 3.82/1.03  fof(f48,plain,(
% 3.82/1.03    k2_xboole_0(k1_tarski(sK4),sK5) != sK5 & r2_hidden(sK4,sK5)),
% 3.82/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f26,f47])).
% 3.82/1.03  
% 3.82/1.03  fof(f86,plain,(
% 3.82/1.03    r2_hidden(sK4,sK5)),
% 3.82/1.03    inference(cnf_transformation,[],[f48])).
% 3.82/1.03  
% 3.82/1.03  fof(f17,axiom,(
% 3.82/1.03    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.82/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.03  
% 3.82/1.03  fof(f46,plain,(
% 3.82/1.03    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.82/1.03    inference(nnf_transformation,[],[f17])).
% 3.82/1.03  
% 3.82/1.03  fof(f84,plain,(
% 3.82/1.03    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.82/1.03    inference(cnf_transformation,[],[f46])).
% 3.82/1.03  
% 3.82/1.03  fof(f13,axiom,(
% 3.82/1.03    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.82/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.03  
% 3.82/1.03  fof(f79,plain,(
% 3.82/1.03    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.82/1.03    inference(cnf_transformation,[],[f13])).
% 3.82/1.03  
% 3.82/1.03  fof(f14,axiom,(
% 3.82/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.82/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.03  
% 3.82/1.03  fof(f80,plain,(
% 3.82/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.82/1.03    inference(cnf_transformation,[],[f14])).
% 3.82/1.03  
% 3.82/1.03  fof(f15,axiom,(
% 3.82/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.82/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.03  
% 3.82/1.03  fof(f81,plain,(
% 3.82/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.82/1.03    inference(cnf_transformation,[],[f15])).
% 3.82/1.03  
% 3.82/1.03  fof(f16,axiom,(
% 3.82/1.03    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.82/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.03  
% 3.82/1.03  fof(f82,plain,(
% 3.82/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.82/1.03    inference(cnf_transformation,[],[f16])).
% 3.82/1.03  
% 3.82/1.03  fof(f89,plain,(
% 3.82/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.82/1.03    inference(definition_unfolding,[],[f81,f82])).
% 3.82/1.03  
% 3.82/1.03  fof(f90,plain,(
% 3.82/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.82/1.03    inference(definition_unfolding,[],[f80,f89])).
% 3.82/1.03  
% 3.82/1.03  fof(f91,plain,(
% 3.82/1.03    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.82/1.03    inference(definition_unfolding,[],[f79,f90])).
% 3.82/1.03  
% 3.82/1.03  fof(f100,plain,(
% 3.82/1.03    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.82/1.03    inference(definition_unfolding,[],[f84,f91])).
% 3.82/1.03  
% 3.82/1.03  fof(f10,axiom,(
% 3.82/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.82/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.03  
% 3.82/1.03  fof(f25,plain,(
% 3.82/1.03    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.82/1.03    inference(ennf_transformation,[],[f10])).
% 3.82/1.03  
% 3.82/1.03  fof(f76,plain,(
% 3.82/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.82/1.03    inference(cnf_transformation,[],[f25])).
% 3.82/1.03  
% 3.82/1.03  fof(f1,axiom,(
% 3.82/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.82/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.03  
% 3.82/1.03  fof(f49,plain,(
% 3.82/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.82/1.03    inference(cnf_transformation,[],[f1])).
% 3.82/1.03  
% 3.82/1.03  fof(f12,axiom,(
% 3.82/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.82/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.03  
% 3.82/1.03  fof(f78,plain,(
% 3.82/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.82/1.03    inference(cnf_transformation,[],[f12])).
% 3.82/1.03  
% 3.82/1.03  fof(f8,axiom,(
% 3.82/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.82/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.03  
% 3.82/1.03  fof(f74,plain,(
% 3.82/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.82/1.03    inference(cnf_transformation,[],[f8])).
% 3.82/1.03  
% 3.82/1.03  fof(f88,plain,(
% 3.82/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.82/1.03    inference(definition_unfolding,[],[f78,f74])).
% 3.82/1.03  
% 3.82/1.03  fof(f92,plain,(
% 3.82/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.82/1.03    inference(definition_unfolding,[],[f49,f88,f88])).
% 3.82/1.03  
% 3.82/1.03  fof(f87,plain,(
% 3.82/1.03    k2_xboole_0(k1_tarski(sK4),sK5) != sK5),
% 3.82/1.03    inference(cnf_transformation,[],[f48])).
% 3.82/1.03  
% 3.82/1.03  fof(f103,plain,(
% 3.82/1.03    k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k5_xboole_0(sK5,k3_xboole_0(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) != sK5),
% 3.82/1.03    inference(definition_unfolding,[],[f87,f88,f91])).
% 3.82/1.03  
% 3.82/1.03  fof(f2,axiom,(
% 3.82/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.82/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.03  
% 3.82/1.03  fof(f22,plain,(
% 3.82/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.82/1.03    inference(ennf_transformation,[],[f2])).
% 3.82/1.03  
% 3.82/1.03  fof(f27,plain,(
% 3.82/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.82/1.03    inference(nnf_transformation,[],[f22])).
% 3.82/1.03  
% 3.82/1.03  fof(f28,plain,(
% 3.82/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.82/1.03    inference(rectify,[],[f27])).
% 3.82/1.03  
% 3.82/1.03  fof(f29,plain,(
% 3.82/1.03    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.82/1.03    introduced(choice_axiom,[])).
% 3.82/1.03  
% 3.82/1.03  fof(f30,plain,(
% 3.82/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.82/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.82/1.03  
% 3.82/1.03  fof(f51,plain,(
% 3.82/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.82/1.03    inference(cnf_transformation,[],[f30])).
% 3.82/1.03  
% 3.82/1.03  fof(f11,axiom,(
% 3.82/1.03    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.82/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.03  
% 3.82/1.03  fof(f77,plain,(
% 3.82/1.03    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.82/1.03    inference(cnf_transformation,[],[f11])).
% 3.82/1.03  
% 3.82/1.03  fof(f7,axiom,(
% 3.82/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.82/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.03  
% 3.82/1.03  fof(f44,plain,(
% 3.82/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.82/1.03    inference(nnf_transformation,[],[f7])).
% 3.82/1.03  
% 3.82/1.03  fof(f45,plain,(
% 3.82/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.82/1.03    inference(flattening,[],[f44])).
% 3.82/1.03  
% 3.82/1.03  fof(f71,plain,(
% 3.82/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.82/1.03    inference(cnf_transformation,[],[f45])).
% 3.82/1.03  
% 3.82/1.03  fof(f111,plain,(
% 3.82/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.82/1.03    inference(equality_resolution,[],[f71])).
% 3.82/1.03  
% 3.82/1.03  fof(f6,axiom,(
% 3.82/1.03    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.82/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.03  
% 3.82/1.03  fof(f21,plain,(
% 3.82/1.03    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.82/1.03    inference(rectify,[],[f6])).
% 3.82/1.03  
% 3.82/1.03  fof(f24,plain,(
% 3.82/1.03    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.82/1.03    inference(ennf_transformation,[],[f21])).
% 3.82/1.03  
% 3.82/1.03  fof(f42,plain,(
% 3.82/1.03    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 3.82/1.03    introduced(choice_axiom,[])).
% 3.82/1.03  
% 3.82/1.03  fof(f43,plain,(
% 3.82/1.03    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.82/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f42])).
% 3.82/1.03  
% 3.82/1.03  fof(f70,plain,(
% 3.82/1.03    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.82/1.03    inference(cnf_transformation,[],[f43])).
% 3.82/1.03  
% 3.82/1.03  fof(f9,axiom,(
% 3.82/1.03    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.82/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.03  
% 3.82/1.03  fof(f75,plain,(
% 3.82/1.03    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.82/1.03    inference(cnf_transformation,[],[f9])).
% 3.82/1.03  
% 3.82/1.03  fof(f99,plain,(
% 3.82/1.03    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 3.82/1.03    inference(definition_unfolding,[],[f75,f88])).
% 3.82/1.03  
% 3.82/1.03  fof(f5,axiom,(
% 3.82/1.03    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 3.82/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.03  
% 3.82/1.03  fof(f23,plain,(
% 3.82/1.03    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 3.82/1.03    inference(ennf_transformation,[],[f5])).
% 3.82/1.03  
% 3.82/1.03  fof(f41,plain,(
% 3.82/1.03    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 3.82/1.03    inference(nnf_transformation,[],[f23])).
% 3.82/1.03  
% 3.82/1.03  fof(f68,plain,(
% 3.82/1.03    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 3.82/1.03    inference(cnf_transformation,[],[f41])).
% 3.82/1.03  
% 3.82/1.03  fof(f66,plain,(
% 3.82/1.03    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 3.82/1.03    inference(cnf_transformation,[],[f41])).
% 3.82/1.03  
% 3.82/1.03  fof(f73,plain,(
% 3.82/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.82/1.03    inference(cnf_transformation,[],[f45])).
% 3.82/1.03  
% 3.82/1.03  fof(f4,axiom,(
% 3.82/1.03    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.82/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/1.03  
% 3.82/1.03  fof(f36,plain,(
% 3.82/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.82/1.03    inference(nnf_transformation,[],[f4])).
% 3.82/1.03  
% 3.82/1.03  fof(f37,plain,(
% 3.82/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.82/1.03    inference(flattening,[],[f36])).
% 3.82/1.03  
% 3.82/1.03  fof(f38,plain,(
% 3.82/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.82/1.03    inference(rectify,[],[f37])).
% 3.82/1.03  
% 3.82/1.03  fof(f39,plain,(
% 3.82/1.03    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.82/1.03    introduced(choice_axiom,[])).
% 3.82/1.03  
% 3.82/1.03  fof(f40,plain,(
% 3.82/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.82/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 3.82/1.03  
% 3.82/1.03  fof(f60,plain,(
% 3.82/1.03    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.82/1.03    inference(cnf_transformation,[],[f40])).
% 3.82/1.03  
% 3.82/1.03  fof(f97,plain,(
% 3.82/1.03    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.82/1.03    inference(definition_unfolding,[],[f60,f74])).
% 3.82/1.03  
% 3.82/1.03  fof(f108,plain,(
% 3.82/1.03    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.82/1.03    inference(equality_resolution,[],[f97])).
% 3.82/1.03  
% 3.82/1.03  fof(f59,plain,(
% 3.82/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.82/1.03    inference(cnf_transformation,[],[f40])).
% 3.82/1.03  
% 3.82/1.03  fof(f98,plain,(
% 3.82/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.82/1.03    inference(definition_unfolding,[],[f59,f74])).
% 3.82/1.03  
% 3.82/1.03  fof(f109,plain,(
% 3.82/1.03    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.82/1.03    inference(equality_resolution,[],[f98])).
% 3.82/1.03  
% 3.82/1.03  cnf(c_32,negated_conjecture,
% 3.82/1.03      ( r2_hidden(sK4,sK5) ),
% 3.82/1.03      inference(cnf_transformation,[],[f86]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_1087,plain,
% 3.82/1.03      ( r2_hidden(sK4,sK5) = iProver_top ),
% 3.82/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_28,plain,
% 3.82/1.03      ( ~ r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 3.82/1.03      inference(cnf_transformation,[],[f100]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_1089,plain,
% 3.82/1.03      ( r2_hidden(X0,X1) != iProver_top
% 3.82/1.03      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
% 3.82/1.03      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_26,plain,
% 3.82/1.03      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.82/1.03      inference(cnf_transformation,[],[f76]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_1091,plain,
% 3.82/1.03      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.82/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_2502,plain,
% 3.82/1.03      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k3_enumset1(X0,X0,X0,X0,X0)
% 3.82/1.03      | r2_hidden(X0,X1) != iProver_top ),
% 3.82/1.03      inference(superposition,[status(thm)],[c_1089,c_1091]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_17310,plain,
% 3.82/1.03      ( k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
% 3.82/1.03      inference(superposition,[status(thm)],[c_1087,c_2502]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_0,plain,
% 3.82/1.03      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 3.82/1.03      inference(cnf_transformation,[],[f92]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_31,negated_conjecture,
% 3.82/1.03      ( k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k5_xboole_0(sK5,k3_xboole_0(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) != sK5 ),
% 3.82/1.03      inference(cnf_transformation,[],[f103]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_1646,plain,
% 3.82/1.03      ( k5_xboole_0(sK5,k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5))) != sK5 ),
% 3.82/1.03      inference(demodulation,[status(thm)],[c_0,c_31]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_18100,plain,
% 3.82/1.03      ( k5_xboole_0(sK5,k5_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4))) != sK5 ),
% 3.82/1.03      inference(demodulation,[status(thm)],[c_17310,c_1646]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_2,plain,
% 3.82/1.03      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.82/1.03      inference(cnf_transformation,[],[f51]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_1113,plain,
% 3.82/1.03      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.82/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 3.82/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_27,plain,
% 3.82/1.03      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.82/1.03      inference(cnf_transformation,[],[f77]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_1090,plain,
% 3.82/1.03      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.82/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_24,plain,
% 3.82/1.03      ( r1_tarski(X0,X0) ),
% 3.82/1.03      inference(cnf_transformation,[],[f111]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_1092,plain,
% 3.82/1.03      ( r1_tarski(X0,X0) = iProver_top ),
% 3.82/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_1431,plain,
% 3.82/1.03      ( k3_xboole_0(X0,X0) = X0 ),
% 3.82/1.03      inference(superposition,[status(thm)],[c_1092,c_1091]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_20,plain,
% 3.82/1.03      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 3.82/1.03      inference(cnf_transformation,[],[f70]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_1095,plain,
% 3.82/1.03      ( r1_xboole_0(X0,X1) != iProver_top
% 3.82/1.03      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 3.82/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_3023,plain,
% 3.82/1.03      ( r1_xboole_0(X0,X0) != iProver_top | r2_hidden(X1,X0) != iProver_top ),
% 3.82/1.03      inference(superposition,[status(thm)],[c_1431,c_1095]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_3039,plain,
% 3.82/1.03      ( r1_xboole_0(X0,X0) != iProver_top | r1_tarski(X0,X1) = iProver_top ),
% 3.82/1.03      inference(superposition,[status(thm)],[c_1113,c_3023]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_3312,plain,
% 3.82/1.03      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.82/1.03      inference(superposition,[status(thm)],[c_1090,c_3039]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_3482,plain,
% 3.82/1.03      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.82/1.03      inference(superposition,[status(thm)],[c_3312,c_1091]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_25,plain,
% 3.82/1.03      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 3.82/1.03      inference(cnf_transformation,[],[f99]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_3485,plain,
% 3.82/1.03      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
% 3.82/1.03      inference(demodulation,[status(thm)],[c_3482,c_25]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_16,plain,
% 3.82/1.03      ( ~ r2_hidden(X0,X1)
% 3.82/1.03      | r2_hidden(X0,X2)
% 3.82/1.03      | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 3.82/1.03      inference(cnf_transformation,[],[f68]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_1099,plain,
% 3.82/1.03      ( r2_hidden(X0,X1) != iProver_top
% 3.82/1.03      | r2_hidden(X0,X2) = iProver_top
% 3.82/1.03      | r2_hidden(X0,k5_xboole_0(X2,X1)) = iProver_top ),
% 3.82/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_7730,plain,
% 3.82/1.03      ( r2_hidden(X0,X1) = iProver_top
% 3.82/1.03      | r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.82/1.03      inference(superposition,[status(thm)],[c_3485,c_1099]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_18,plain,
% 3.82/1.03      ( ~ r2_hidden(X0,X1)
% 3.82/1.03      | ~ r2_hidden(X0,X2)
% 3.82/1.03      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 3.82/1.03      inference(cnf_transformation,[],[f66]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_1097,plain,
% 3.82/1.03      ( r2_hidden(X0,X1) != iProver_top
% 3.82/1.03      | r2_hidden(X0,X2) != iProver_top
% 3.82/1.03      | r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top ),
% 3.82/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_6548,plain,
% 3.82/1.03      ( r2_hidden(X0,X1) != iProver_top
% 3.82/1.03      | r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.82/1.03      inference(superposition,[status(thm)],[c_3485,c_1097]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_8063,plain,
% 3.82/1.03      ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.82/1.03      inference(global_propositional_subsumption,[status(thm)],[c_7730,c_6548]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_8070,plain,
% 3.82/1.03      ( r1_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),X0) = iProver_top ),
% 3.82/1.03      inference(superposition,[status(thm)],[c_1113,c_8063]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_22,plain,
% 3.82/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.82/1.03      inference(cnf_transformation,[],[f73]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_1093,plain,
% 3.82/1.03      ( X0 = X1
% 3.82/1.03      | r1_tarski(X1,X0) != iProver_top
% 3.82/1.03      | r1_tarski(X0,X1) != iProver_top ),
% 3.82/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_4426,plain,
% 3.82/1.03      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.82/1.03      inference(superposition,[status(thm)],[c_3312,c_1093]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_8082,plain,
% 3.82/1.03      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.82/1.03      inference(superposition,[status(thm)],[c_8070,c_4426]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_9060,plain,
% 3.82/1.03      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.82/1.03      inference(demodulation,[status(thm)],[c_8082,c_3485]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_14,plain,
% 3.82/1.03      ( ~ r2_hidden(X0,X1)
% 3.82/1.03      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 3.82/1.03      inference(cnf_transformation,[],[f108]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_1101,plain,
% 3.82/1.03      ( r2_hidden(X0,X1) != iProver_top
% 3.82/1.03      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 3.82/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_6577,plain,
% 3.82/1.03      ( r2_hidden(X0,X1) != iProver_top
% 3.82/1.03      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 3.82/1.03      inference(superposition,[status(thm)],[c_1431,c_1101]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_15,plain,
% 3.82/1.03      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.82/1.03      inference(cnf_transformation,[],[f109]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_1100,plain,
% 3.82/1.03      ( r2_hidden(X0,X1) = iProver_top
% 3.82/1.03      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 3.82/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_4409,plain,
% 3.82/1.03      ( r2_hidden(X0,X1) = iProver_top
% 3.82/1.03      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 3.82/1.03      inference(superposition,[status(thm)],[c_1431,c_1100]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_9730,plain,
% 3.82/1.03      ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 3.82/1.03      inference(global_propositional_subsumption,[status(thm)],[c_6577,c_4409]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_9737,plain,
% 3.82/1.03      ( r1_tarski(k5_xboole_0(X0,X0),X1) = iProver_top ),
% 3.82/1.03      inference(superposition,[status(thm)],[c_1113,c_9730]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_11615,plain,
% 3.82/1.03      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.82/1.03      inference(superposition,[status(thm)],[c_9737,c_4426]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_18101,plain,
% 3.82/1.03      ( sK5 != sK5 ),
% 3.82/1.03      inference(demodulation,[status(thm)],[c_18100,c_9060,c_11615]) ).
% 3.82/1.03  
% 3.82/1.03  cnf(c_18102,plain,
% 3.82/1.03      ( $false ),
% 3.82/1.03      inference(equality_resolution_simp,[status(thm)],[c_18101]) ).
% 3.82/1.03  
% 3.82/1.03  
% 3.82/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.82/1.03  
% 3.82/1.03  ------                               Statistics
% 3.82/1.03  
% 3.82/1.03  ------ Selected
% 3.82/1.03  
% 3.82/1.03  total_time:                             0.451
% 3.82/1.03  
%------------------------------------------------------------------------------
