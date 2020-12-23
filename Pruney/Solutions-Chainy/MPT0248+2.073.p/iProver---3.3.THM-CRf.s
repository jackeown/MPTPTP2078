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
% DateTime   : Thu Dec  3 11:32:18 EST 2020

% Result     : Theorem 55.77s
% Output     : CNFRefutation 55.77s
% Verified   : 
% Statistics : Number of formulae       :  201 (6484 expanded)
%              Number of clauses        :   98 ( 636 expanded)
%              Number of leaves         :   30 (2015 expanded)
%              Depth                    :   29
%              Number of atoms          :  433 (10431 expanded)
%              Number of equality atoms :  296 (9273 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f17,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f22])).

fof(f94,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f80,f81])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f79,f94])).

fof(f96,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f78,f95])).

fof(f97,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f77,f96])).

fof(f100,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f76,f97])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f84,f100])).

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

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f52,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK4
        | k1_tarski(sK2) != sK3 )
      & ( k1_tarski(sK2) != sK4
        | k1_xboole_0 != sK3 )
      & ( k1_tarski(sK2) != sK4
        | k1_tarski(sK2) != sK3 )
      & k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( k1_xboole_0 != sK4
      | k1_tarski(sK2) != sK3 )
    & ( k1_tarski(sK2) != sK4
      | k1_xboole_0 != sK3 )
    & ( k1_tarski(sK2) != sK4
      | k1_tarski(sK2) != sK3 )
    & k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f52])).

fof(f90,plain,(
    k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f27,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f98,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f89,f97])).

fof(f121,plain,(
    k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f90,f98,f100])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f110,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f70,f98])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f50])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f86,f100,f100])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f123,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f91,plain,
    ( k1_tarski(sK2) != sK4
    | k1_tarski(sK2) != sK3 ),
    inference(cnf_transformation,[],[f53])).

fof(f120,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3 ),
    inference(definition_unfolding,[],[f91,f100,f100])).

fof(f92,plain,
    ( k1_tarski(sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f53])).

fof(f119,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f92,f100])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f98])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f45])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f99,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f73,f98])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) ) ),
    inference(definition_unfolding,[],[f63,f99])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) != k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f59,f99])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f85,f100])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f60,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f105,plain,(
    ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f60,f98])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f99])).

fof(f93,plain,
    ( k1_xboole_0 != sK4
    | k1_tarski(sK2) != sK3 ),
    inference(cnf_transformation,[],[f53])).

fof(f118,plain,
    ( k1_xboole_0 != sK4
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3 ),
    inference(definition_unfolding,[],[f93,f100])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f102,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) ),
    inference(definition_unfolding,[],[f74,f98,f81,f100])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f16])).

fof(f101,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X7))) ),
    inference(definition_unfolding,[],[f75,f98,f81,f97])).

fof(f111,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) ),
    inference(definition_unfolding,[],[f82,f101])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_947,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_936,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_30,negated_conjecture,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_17,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_937,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5825,plain,
    ( r1_tarski(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_30,c_937])).

cnf(c_26,plain,
    ( ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
    | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_931,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5834,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5825,c_931])).

cnf(c_6229,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = X0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5834,c_931])).

cnf(c_8052,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
    | sK3 = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_936,c_6229])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1022,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1124,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1022])).

cnf(c_13,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1217,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_475,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1337,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X0
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_475])).

cnf(c_1629,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK4
    | sK4 != k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1337])).

cnf(c_29,negated_conjecture,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_6238,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5834,c_29])).

cnf(c_28,negated_conjecture,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_984,plain,
    ( ~ r1_tarski(sK3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
    | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = sK3
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_986,plain,
    ( ~ r1_tarski(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_984])).

cnf(c_5829,plain,
    ( r1_tarski(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5825])).

cnf(c_6310,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6238,c_29,c_28,c_986,c_5829])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_939,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8350,plain,
    ( k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_5825,c_939])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_18,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_469,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))) ),
    inference(theory_normalisation,[status(thm)],[c_9,c_18,c_1])).

cnf(c_943,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_469])).

cnf(c_12758,plain,
    ( r1_xboole_0(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(X0,k5_xboole_0(sK3,k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8350,c_943])).

cnf(c_15,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_19,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_12767,plain,
    ( r1_xboole_0(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12758,c_15,c_19])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,X1)
    | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_472,plain,
    ( r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) != k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_5,c_18,c_1])).

cnf(c_945,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_472])).

cnf(c_19033,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_xboole_0
    | r1_xboole_0(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8350,c_945])).

cnf(c_19042,plain,
    ( sK3 != k1_xboole_0
    | r1_xboole_0(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19033,c_15,c_19])).

cnf(c_1028,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_475])).

cnf(c_1313,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_3298,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,sK4)) != sK4
    | sK4 = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_28835,plain,
    ( k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != sK4
    | sK4 = k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3298])).

cnf(c_23,plain,
    ( r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_934,plain,
    ( r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6226,plain,
    ( sK3 = k1_xboole_0
    | r1_xboole_0(sK3,X0) = iProver_top
    | r2_hidden(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5834,c_934])).

cnf(c_7,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_468,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))) ),
    inference(theory_normalisation,[status(thm)],[c_10,c_18,c_1])).

cnf(c_942,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_10307,plain,
    ( r1_xboole_0(X0,X0) = iProver_top
    | r2_hidden(sK1(X0,X0),k5_xboole_0(X0,k5_xboole_0(X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_942])).

cnf(c_10321,plain,
    ( r1_xboole_0(X0,X0) = iProver_top
    | r2_hidden(sK1(X0,X0),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10307,c_15,c_19])).

cnf(c_12753,plain,
    ( r1_xboole_0(sK3,sK4) != iProver_top
    | r2_hidden(X0,k5_xboole_0(sK3,k5_xboole_0(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_30,c_943])).

cnf(c_14725,plain,
    ( r1_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k5_xboole_0(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = iProver_top
    | r1_xboole_0(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_10321,c_12753])).

cnf(c_15226,plain,
    ( sK3 = k1_xboole_0
    | r1_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k5_xboole_0(sK4,sK3))) = iProver_top
    | r1_xboole_0(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5834,c_14725])).

cnf(c_1440,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_19,c_18])).

cnf(c_1317,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_15,c_1])).

cnf(c_1446,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1440,c_1317])).

cnf(c_1594,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_1446])).

cnf(c_15228,plain,
    ( sK3 = k1_xboole_0
    | r1_xboole_0(sK3,sK4) != iProver_top
    | r1_xboole_0(sK4,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15226,c_1594])).

cnf(c_27,negated_conjecture,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_6240,plain,
    ( sK3 = k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5834,c_27])).

cnf(c_14729,plain,
    ( sK3 = k1_xboole_0
    | r1_xboole_0(sK3,sK4) != iProver_top
    | r2_hidden(X0,k5_xboole_0(sK3,k5_xboole_0(sK4,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5834,c_12753])).

cnf(c_14730,plain,
    ( sK3 = k1_xboole_0
    | r1_xboole_0(sK3,sK4) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14729,c_1594])).

cnf(c_14742,plain,
    ( sK3 = k1_xboole_0
    | r1_xboole_0(sK3,sK4) != iProver_top
    | r2_hidden(sK2,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14730])).

cnf(c_14723,plain,
    ( r1_xboole_0(sK3,sK4) != iProver_top
    | r1_tarski(k5_xboole_0(sK3,k5_xboole_0(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_947,c_12753])).

cnf(c_14925,plain,
    ( sK3 = k1_xboole_0
    | r1_xboole_0(sK3,sK4) != iProver_top
    | r1_tarski(k5_xboole_0(sK3,k5_xboole_0(sK4,sK3)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5834,c_14723])).

cnf(c_14929,plain,
    ( sK3 = k1_xboole_0
    | r1_xboole_0(sK3,sK4) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14925,c_1594])).

cnf(c_28107,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK2,sK4) = iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6226,c_14929])).

cnf(c_28113,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = sK4
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_28107,c_931])).

cnf(c_28122,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK4
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_28113])).

cnf(c_36327,plain,
    ( r1_xboole_0(sK3,sK4) != iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15228,c_29,c_28,c_986,c_5829,c_6240,c_14742,c_28122])).

cnf(c_36328,plain,
    ( sK3 = k1_xboole_0
    | r1_xboole_0(sK3,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_36327])).

cnf(c_36331,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6226,c_36328])).

cnf(c_6689,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK2,X0) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5834,c_936])).

cnf(c_36334,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_36331,c_6689])).

cnf(c_36745,plain,
    ( k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = sK4
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_36334,c_939])).

cnf(c_52031,plain,
    ( r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8052,c_30,c_29,c_28,c_986,c_1124,c_1217,c_1629,c_5829,c_12767,c_19042,c_28835,c_36745])).

cnf(c_0,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_6223,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),sK3)) = k5_enumset1(X0,X1,X2,X3,X4,X5,sK2)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5834,c_0])).

cnf(c_8231,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X1,X2,X3,X4,X5,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6223,c_937])).

cnf(c_36749,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8231,c_30,c_29,c_28,c_986,c_1124,c_1217,c_1629,c_5829,c_28835,c_36745])).

cnf(c_52037,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_52031,c_36749])).

cnf(c_52039,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_947,c_52037])).

cnf(c_164895,plain,
    ( k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_52039,c_939])).

cnf(c_20,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1549,plain,
    ( k5_enumset1(X0,X1,X2,X3,X4,X5,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(superposition,[status(thm)],[c_20,c_0])).

cnf(c_20555,plain,
    ( k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK4,sK4)) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_1549,c_30])).

cnf(c_36764,plain,
    ( k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK4,sK4)) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_36749,c_20555])).

cnf(c_36967,plain,
    ( k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK4)) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_1549,c_36764])).

cnf(c_190855,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK4 ),
    inference(demodulation,[status(thm)],[c_164895,c_36967])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_190855,c_6310])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:47:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 55.77/7.54  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 55.77/7.54  
% 55.77/7.54  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.77/7.54  
% 55.77/7.54  ------  iProver source info
% 55.77/7.54  
% 55.77/7.54  git: date: 2020-06-30 10:37:57 +0100
% 55.77/7.54  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.77/7.54  git: non_committed_changes: false
% 55.77/7.54  git: last_make_outside_of_git: false
% 55.77/7.54  
% 55.77/7.54  ------ 
% 55.77/7.54  
% 55.77/7.54  ------ Input Options
% 55.77/7.54  
% 55.77/7.54  --out_options                           all
% 55.77/7.54  --tptp_safe_out                         true
% 55.77/7.54  --problem_path                          ""
% 55.77/7.54  --include_path                          ""
% 55.77/7.54  --clausifier                            res/vclausify_rel
% 55.77/7.54  --clausifier_options                    ""
% 55.77/7.54  --stdin                                 false
% 55.77/7.54  --stats_out                             all
% 55.77/7.54  
% 55.77/7.54  ------ General Options
% 55.77/7.54  
% 55.77/7.54  --fof                                   false
% 55.77/7.54  --time_out_real                         305.
% 55.77/7.54  --time_out_virtual                      -1.
% 55.77/7.54  --symbol_type_check                     false
% 55.77/7.54  --clausify_out                          false
% 55.77/7.54  --sig_cnt_out                           false
% 55.77/7.54  --trig_cnt_out                          false
% 55.77/7.54  --trig_cnt_out_tolerance                1.
% 55.77/7.54  --trig_cnt_out_sk_spl                   false
% 55.77/7.54  --abstr_cl_out                          false
% 55.77/7.54  
% 55.77/7.54  ------ Global Options
% 55.77/7.54  
% 55.77/7.54  --schedule                              default
% 55.77/7.54  --add_important_lit                     false
% 55.77/7.54  --prop_solver_per_cl                    1000
% 55.77/7.54  --min_unsat_core                        false
% 55.77/7.54  --soft_assumptions                      false
% 55.77/7.54  --soft_lemma_size                       3
% 55.77/7.54  --prop_impl_unit_size                   0
% 55.77/7.54  --prop_impl_unit                        []
% 55.77/7.54  --share_sel_clauses                     true
% 55.77/7.54  --reset_solvers                         false
% 55.77/7.54  --bc_imp_inh                            [conj_cone]
% 55.77/7.54  --conj_cone_tolerance                   3.
% 55.77/7.54  --extra_neg_conj                        none
% 55.77/7.54  --large_theory_mode                     true
% 55.77/7.54  --prolific_symb_bound                   200
% 55.77/7.54  --lt_threshold                          2000
% 55.77/7.54  --clause_weak_htbl                      true
% 55.77/7.54  --gc_record_bc_elim                     false
% 55.77/7.54  
% 55.77/7.54  ------ Preprocessing Options
% 55.77/7.54  
% 55.77/7.54  --preprocessing_flag                    true
% 55.77/7.54  --time_out_prep_mult                    0.1
% 55.77/7.54  --splitting_mode                        input
% 55.77/7.54  --splitting_grd                         true
% 55.77/7.54  --splitting_cvd                         false
% 55.77/7.54  --splitting_cvd_svl                     false
% 55.77/7.54  --splitting_nvd                         32
% 55.77/7.54  --sub_typing                            true
% 55.77/7.54  --prep_gs_sim                           true
% 55.77/7.54  --prep_unflatten                        true
% 55.77/7.54  --prep_res_sim                          true
% 55.77/7.54  --prep_upred                            true
% 55.77/7.54  --prep_sem_filter                       exhaustive
% 55.77/7.54  --prep_sem_filter_out                   false
% 55.77/7.54  --pred_elim                             true
% 55.77/7.54  --res_sim_input                         true
% 55.77/7.54  --eq_ax_congr_red                       true
% 55.77/7.54  --pure_diseq_elim                       true
% 55.77/7.54  --brand_transform                       false
% 55.77/7.54  --non_eq_to_eq                          false
% 55.77/7.54  --prep_def_merge                        true
% 55.77/7.54  --prep_def_merge_prop_impl              false
% 55.77/7.54  --prep_def_merge_mbd                    true
% 55.77/7.54  --prep_def_merge_tr_red                 false
% 55.77/7.54  --prep_def_merge_tr_cl                  false
% 55.77/7.54  --smt_preprocessing                     true
% 55.77/7.54  --smt_ac_axioms                         fast
% 55.77/7.54  --preprocessed_out                      false
% 55.77/7.54  --preprocessed_stats                    false
% 55.77/7.54  
% 55.77/7.54  ------ Abstraction refinement Options
% 55.77/7.54  
% 55.77/7.54  --abstr_ref                             []
% 55.77/7.54  --abstr_ref_prep                        false
% 55.77/7.54  --abstr_ref_until_sat                   false
% 55.77/7.54  --abstr_ref_sig_restrict                funpre
% 55.77/7.54  --abstr_ref_af_restrict_to_split_sk     false
% 55.77/7.54  --abstr_ref_under                       []
% 55.77/7.54  
% 55.77/7.54  ------ SAT Options
% 55.77/7.54  
% 55.77/7.54  --sat_mode                              false
% 55.77/7.54  --sat_fm_restart_options                ""
% 55.77/7.54  --sat_gr_def                            false
% 55.77/7.54  --sat_epr_types                         true
% 55.77/7.54  --sat_non_cyclic_types                  false
% 55.77/7.54  --sat_finite_models                     false
% 55.77/7.54  --sat_fm_lemmas                         false
% 55.77/7.54  --sat_fm_prep                           false
% 55.77/7.54  --sat_fm_uc_incr                        true
% 55.77/7.54  --sat_out_model                         small
% 55.77/7.54  --sat_out_clauses                       false
% 55.77/7.54  
% 55.77/7.54  ------ QBF Options
% 55.77/7.54  
% 55.77/7.54  --qbf_mode                              false
% 55.77/7.54  --qbf_elim_univ                         false
% 55.77/7.54  --qbf_dom_inst                          none
% 55.77/7.54  --qbf_dom_pre_inst                      false
% 55.77/7.54  --qbf_sk_in                             false
% 55.77/7.54  --qbf_pred_elim                         true
% 55.77/7.54  --qbf_split                             512
% 55.77/7.54  
% 55.77/7.54  ------ BMC1 Options
% 55.77/7.54  
% 55.77/7.54  --bmc1_incremental                      false
% 55.77/7.54  --bmc1_axioms                           reachable_all
% 55.77/7.54  --bmc1_min_bound                        0
% 55.77/7.54  --bmc1_max_bound                        -1
% 55.77/7.54  --bmc1_max_bound_default                -1
% 55.77/7.54  --bmc1_symbol_reachability              true
% 55.77/7.54  --bmc1_property_lemmas                  false
% 55.77/7.54  --bmc1_k_induction                      false
% 55.77/7.54  --bmc1_non_equiv_states                 false
% 55.77/7.54  --bmc1_deadlock                         false
% 55.77/7.54  --bmc1_ucm                              false
% 55.77/7.54  --bmc1_add_unsat_core                   none
% 55.77/7.54  --bmc1_unsat_core_children              false
% 55.77/7.54  --bmc1_unsat_core_extrapolate_axioms    false
% 55.77/7.54  --bmc1_out_stat                         full
% 55.77/7.54  --bmc1_ground_init                      false
% 55.77/7.54  --bmc1_pre_inst_next_state              false
% 55.77/7.54  --bmc1_pre_inst_state                   false
% 55.77/7.54  --bmc1_pre_inst_reach_state             false
% 55.77/7.54  --bmc1_out_unsat_core                   false
% 55.77/7.54  --bmc1_aig_witness_out                  false
% 55.77/7.54  --bmc1_verbose                          false
% 55.77/7.54  --bmc1_dump_clauses_tptp                false
% 55.77/7.54  --bmc1_dump_unsat_core_tptp             false
% 55.77/7.54  --bmc1_dump_file                        -
% 55.77/7.54  --bmc1_ucm_expand_uc_limit              128
% 55.77/7.54  --bmc1_ucm_n_expand_iterations          6
% 55.77/7.54  --bmc1_ucm_extend_mode                  1
% 55.77/7.54  --bmc1_ucm_init_mode                    2
% 55.77/7.54  --bmc1_ucm_cone_mode                    none
% 55.77/7.54  --bmc1_ucm_reduced_relation_type        0
% 55.77/7.54  --bmc1_ucm_relax_model                  4
% 55.77/7.54  --bmc1_ucm_full_tr_after_sat            true
% 55.77/7.54  --bmc1_ucm_expand_neg_assumptions       false
% 55.77/7.54  --bmc1_ucm_layered_model                none
% 55.77/7.54  --bmc1_ucm_max_lemma_size               10
% 55.77/7.54  
% 55.77/7.54  ------ AIG Options
% 55.77/7.54  
% 55.77/7.54  --aig_mode                              false
% 55.77/7.54  
% 55.77/7.54  ------ Instantiation Options
% 55.77/7.54  
% 55.77/7.54  --instantiation_flag                    true
% 55.77/7.54  --inst_sos_flag                         true
% 55.77/7.54  --inst_sos_phase                        true
% 55.77/7.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.77/7.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.77/7.54  --inst_lit_sel_side                     num_symb
% 55.77/7.54  --inst_solver_per_active                1400
% 55.77/7.54  --inst_solver_calls_frac                1.
% 55.77/7.54  --inst_passive_queue_type               priority_queues
% 55.77/7.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.77/7.54  --inst_passive_queues_freq              [25;2]
% 55.77/7.54  --inst_dismatching                      true
% 55.77/7.54  --inst_eager_unprocessed_to_passive     true
% 55.77/7.54  --inst_prop_sim_given                   true
% 55.77/7.54  --inst_prop_sim_new                     false
% 55.77/7.54  --inst_subs_new                         false
% 55.77/7.54  --inst_eq_res_simp                      false
% 55.77/7.54  --inst_subs_given                       false
% 55.77/7.54  --inst_orphan_elimination               true
% 55.77/7.54  --inst_learning_loop_flag               true
% 55.77/7.54  --inst_learning_start                   3000
% 55.77/7.54  --inst_learning_factor                  2
% 55.77/7.54  --inst_start_prop_sim_after_learn       3
% 55.77/7.54  --inst_sel_renew                        solver
% 55.77/7.54  --inst_lit_activity_flag                true
% 55.77/7.54  --inst_restr_to_given                   false
% 55.77/7.54  --inst_activity_threshold               500
% 55.77/7.54  --inst_out_proof                        true
% 55.77/7.54  
% 55.77/7.54  ------ Resolution Options
% 55.77/7.54  
% 55.77/7.54  --resolution_flag                       true
% 55.77/7.54  --res_lit_sel                           adaptive
% 55.77/7.54  --res_lit_sel_side                      none
% 55.77/7.54  --res_ordering                          kbo
% 55.77/7.54  --res_to_prop_solver                    active
% 55.77/7.54  --res_prop_simpl_new                    false
% 55.77/7.54  --res_prop_simpl_given                  true
% 55.77/7.54  --res_passive_queue_type                priority_queues
% 55.77/7.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.77/7.54  --res_passive_queues_freq               [15;5]
% 55.77/7.54  --res_forward_subs                      full
% 55.77/7.54  --res_backward_subs                     full
% 55.77/7.54  --res_forward_subs_resolution           true
% 55.77/7.54  --res_backward_subs_resolution          true
% 55.77/7.54  --res_orphan_elimination                true
% 55.77/7.54  --res_time_limit                        2.
% 55.77/7.54  --res_out_proof                         true
% 55.77/7.54  
% 55.77/7.54  ------ Superposition Options
% 55.77/7.54  
% 55.77/7.54  --superposition_flag                    true
% 55.77/7.54  --sup_passive_queue_type                priority_queues
% 55.77/7.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.77/7.54  --sup_passive_queues_freq               [8;1;4]
% 55.77/7.54  --demod_completeness_check              fast
% 55.77/7.54  --demod_use_ground                      true
% 55.77/7.54  --sup_to_prop_solver                    passive
% 55.77/7.54  --sup_prop_simpl_new                    true
% 55.77/7.54  --sup_prop_simpl_given                  true
% 55.77/7.54  --sup_fun_splitting                     true
% 55.77/7.54  --sup_smt_interval                      50000
% 55.77/7.54  
% 55.77/7.54  ------ Superposition Simplification Setup
% 55.77/7.54  
% 55.77/7.54  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.77/7.54  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.77/7.54  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.77/7.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.77/7.54  --sup_full_triv                         [TrivRules;PropSubs]
% 55.77/7.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.77/7.54  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.77/7.54  --sup_immed_triv                        [TrivRules]
% 55.77/7.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.77/7.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.77/7.54  --sup_immed_bw_main                     []
% 55.77/7.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.77/7.54  --sup_input_triv                        [Unflattening;TrivRules]
% 55.77/7.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.77/7.54  --sup_input_bw                          []
% 55.77/7.54  
% 55.77/7.54  ------ Combination Options
% 55.77/7.54  
% 55.77/7.54  --comb_res_mult                         3
% 55.77/7.54  --comb_sup_mult                         2
% 55.77/7.54  --comb_inst_mult                        10
% 55.77/7.54  
% 55.77/7.54  ------ Debug Options
% 55.77/7.54  
% 55.77/7.54  --dbg_backtrace                         false
% 55.77/7.54  --dbg_dump_prop_clauses                 false
% 55.77/7.54  --dbg_dump_prop_clauses_file            -
% 55.77/7.54  --dbg_out_stat                          false
% 55.77/7.54  ------ Parsing...
% 55.77/7.54  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.77/7.54  
% 55.77/7.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 55.77/7.54  
% 55.77/7.54  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.77/7.54  
% 55.77/7.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.77/7.54  ------ Proving...
% 55.77/7.54  ------ Problem Properties 
% 55.77/7.54  
% 55.77/7.54  
% 55.77/7.54  clauses                                 30
% 55.77/7.54  conjectures                             4
% 55.77/7.54  EPR                                     4
% 55.77/7.54  Horn                                    26
% 55.77/7.54  unary                                   13
% 55.77/7.54  binary                                  13
% 55.77/7.54  lits                                    51
% 55.77/7.54  lits eq                                 21
% 55.77/7.54  fd_pure                                 0
% 55.77/7.54  fd_pseudo                               0
% 55.77/7.54  fd_cond                                 0
% 55.77/7.54  fd_pseudo_cond                          2
% 55.77/7.54  AC symbols                              1
% 55.77/7.54  
% 55.77/7.54  ------ Schedule dynamic 5 is on 
% 55.77/7.54  
% 55.77/7.54  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 55.77/7.54  
% 55.77/7.54  
% 55.77/7.54  ------ 
% 55.77/7.54  Current options:
% 55.77/7.54  ------ 
% 55.77/7.54  
% 55.77/7.54  ------ Input Options
% 55.77/7.54  
% 55.77/7.54  --out_options                           all
% 55.77/7.54  --tptp_safe_out                         true
% 55.77/7.54  --problem_path                          ""
% 55.77/7.54  --include_path                          ""
% 55.77/7.54  --clausifier                            res/vclausify_rel
% 55.77/7.54  --clausifier_options                    ""
% 55.77/7.54  --stdin                                 false
% 55.77/7.54  --stats_out                             all
% 55.77/7.54  
% 55.77/7.54  ------ General Options
% 55.77/7.54  
% 55.77/7.54  --fof                                   false
% 55.77/7.54  --time_out_real                         305.
% 55.77/7.54  --time_out_virtual                      -1.
% 55.77/7.54  --symbol_type_check                     false
% 55.77/7.54  --clausify_out                          false
% 55.77/7.54  --sig_cnt_out                           false
% 55.77/7.54  --trig_cnt_out                          false
% 55.77/7.54  --trig_cnt_out_tolerance                1.
% 55.77/7.54  --trig_cnt_out_sk_spl                   false
% 55.77/7.54  --abstr_cl_out                          false
% 55.77/7.54  
% 55.77/7.54  ------ Global Options
% 55.77/7.54  
% 55.77/7.54  --schedule                              default
% 55.77/7.54  --add_important_lit                     false
% 55.77/7.54  --prop_solver_per_cl                    1000
% 55.77/7.54  --min_unsat_core                        false
% 55.77/7.54  --soft_assumptions                      false
% 55.77/7.54  --soft_lemma_size                       3
% 55.77/7.54  --prop_impl_unit_size                   0
% 55.77/7.54  --prop_impl_unit                        []
% 55.77/7.54  --share_sel_clauses                     true
% 55.77/7.54  --reset_solvers                         false
% 55.77/7.54  --bc_imp_inh                            [conj_cone]
% 55.77/7.54  --conj_cone_tolerance                   3.
% 55.77/7.54  --extra_neg_conj                        none
% 55.77/7.54  --large_theory_mode                     true
% 55.77/7.54  --prolific_symb_bound                   200
% 55.77/7.54  --lt_threshold                          2000
% 55.77/7.54  --clause_weak_htbl                      true
% 55.77/7.54  --gc_record_bc_elim                     false
% 55.77/7.54  
% 55.77/7.54  ------ Preprocessing Options
% 55.77/7.54  
% 55.77/7.54  --preprocessing_flag                    true
% 55.77/7.54  --time_out_prep_mult                    0.1
% 55.77/7.54  --splitting_mode                        input
% 55.77/7.54  --splitting_grd                         true
% 55.77/7.54  --splitting_cvd                         false
% 55.77/7.54  --splitting_cvd_svl                     false
% 55.77/7.54  --splitting_nvd                         32
% 55.77/7.54  --sub_typing                            true
% 55.77/7.54  --prep_gs_sim                           true
% 55.77/7.54  --prep_unflatten                        true
% 55.77/7.54  --prep_res_sim                          true
% 55.77/7.54  --prep_upred                            true
% 55.77/7.54  --prep_sem_filter                       exhaustive
% 55.77/7.54  --prep_sem_filter_out                   false
% 55.77/7.54  --pred_elim                             true
% 55.77/7.54  --res_sim_input                         true
% 55.77/7.54  --eq_ax_congr_red                       true
% 55.77/7.54  --pure_diseq_elim                       true
% 55.77/7.54  --brand_transform                       false
% 55.77/7.54  --non_eq_to_eq                          false
% 55.77/7.54  --prep_def_merge                        true
% 55.77/7.54  --prep_def_merge_prop_impl              false
% 55.77/7.54  --prep_def_merge_mbd                    true
% 55.77/7.54  --prep_def_merge_tr_red                 false
% 55.77/7.54  --prep_def_merge_tr_cl                  false
% 55.77/7.54  --smt_preprocessing                     true
% 55.77/7.54  --smt_ac_axioms                         fast
% 55.77/7.54  --preprocessed_out                      false
% 55.77/7.54  --preprocessed_stats                    false
% 55.77/7.54  
% 55.77/7.54  ------ Abstraction refinement Options
% 55.77/7.54  
% 55.77/7.54  --abstr_ref                             []
% 55.77/7.54  --abstr_ref_prep                        false
% 55.77/7.54  --abstr_ref_until_sat                   false
% 55.77/7.54  --abstr_ref_sig_restrict                funpre
% 55.77/7.54  --abstr_ref_af_restrict_to_split_sk     false
% 55.77/7.54  --abstr_ref_under                       []
% 55.77/7.54  
% 55.77/7.54  ------ SAT Options
% 55.77/7.54  
% 55.77/7.54  --sat_mode                              false
% 55.77/7.54  --sat_fm_restart_options                ""
% 55.77/7.54  --sat_gr_def                            false
% 55.77/7.54  --sat_epr_types                         true
% 55.77/7.54  --sat_non_cyclic_types                  false
% 55.77/7.54  --sat_finite_models                     false
% 55.77/7.54  --sat_fm_lemmas                         false
% 55.77/7.54  --sat_fm_prep                           false
% 55.77/7.54  --sat_fm_uc_incr                        true
% 55.77/7.54  --sat_out_model                         small
% 55.77/7.54  --sat_out_clauses                       false
% 55.77/7.54  
% 55.77/7.54  ------ QBF Options
% 55.77/7.54  
% 55.77/7.54  --qbf_mode                              false
% 55.77/7.54  --qbf_elim_univ                         false
% 55.77/7.54  --qbf_dom_inst                          none
% 55.77/7.54  --qbf_dom_pre_inst                      false
% 55.77/7.54  --qbf_sk_in                             false
% 55.77/7.54  --qbf_pred_elim                         true
% 55.77/7.54  --qbf_split                             512
% 55.77/7.54  
% 55.77/7.54  ------ BMC1 Options
% 55.77/7.54  
% 55.77/7.54  --bmc1_incremental                      false
% 55.77/7.54  --bmc1_axioms                           reachable_all
% 55.77/7.54  --bmc1_min_bound                        0
% 55.77/7.54  --bmc1_max_bound                        -1
% 55.77/7.54  --bmc1_max_bound_default                -1
% 55.77/7.54  --bmc1_symbol_reachability              true
% 55.77/7.54  --bmc1_property_lemmas                  false
% 55.77/7.54  --bmc1_k_induction                      false
% 55.77/7.54  --bmc1_non_equiv_states                 false
% 55.77/7.54  --bmc1_deadlock                         false
% 55.77/7.54  --bmc1_ucm                              false
% 55.77/7.54  --bmc1_add_unsat_core                   none
% 55.77/7.54  --bmc1_unsat_core_children              false
% 55.77/7.54  --bmc1_unsat_core_extrapolate_axioms    false
% 55.77/7.54  --bmc1_out_stat                         full
% 55.77/7.54  --bmc1_ground_init                      false
% 55.77/7.54  --bmc1_pre_inst_next_state              false
% 55.77/7.54  --bmc1_pre_inst_state                   false
% 55.77/7.54  --bmc1_pre_inst_reach_state             false
% 55.77/7.54  --bmc1_out_unsat_core                   false
% 55.77/7.54  --bmc1_aig_witness_out                  false
% 55.77/7.54  --bmc1_verbose                          false
% 55.77/7.54  --bmc1_dump_clauses_tptp                false
% 55.77/7.54  --bmc1_dump_unsat_core_tptp             false
% 55.77/7.54  --bmc1_dump_file                        -
% 55.77/7.54  --bmc1_ucm_expand_uc_limit              128
% 55.77/7.54  --bmc1_ucm_n_expand_iterations          6
% 55.77/7.54  --bmc1_ucm_extend_mode                  1
% 55.77/7.54  --bmc1_ucm_init_mode                    2
% 55.77/7.54  --bmc1_ucm_cone_mode                    none
% 55.77/7.54  --bmc1_ucm_reduced_relation_type        0
% 55.77/7.54  --bmc1_ucm_relax_model                  4
% 55.77/7.54  --bmc1_ucm_full_tr_after_sat            true
% 55.77/7.54  --bmc1_ucm_expand_neg_assumptions       false
% 55.77/7.54  --bmc1_ucm_layered_model                none
% 55.77/7.54  --bmc1_ucm_max_lemma_size               10
% 55.77/7.54  
% 55.77/7.54  ------ AIG Options
% 55.77/7.54  
% 55.77/7.54  --aig_mode                              false
% 55.77/7.54  
% 55.77/7.54  ------ Instantiation Options
% 55.77/7.54  
% 55.77/7.54  --instantiation_flag                    true
% 55.77/7.54  --inst_sos_flag                         true
% 55.77/7.54  --inst_sos_phase                        true
% 55.77/7.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.77/7.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.77/7.54  --inst_lit_sel_side                     none
% 55.77/7.54  --inst_solver_per_active                1400
% 55.77/7.54  --inst_solver_calls_frac                1.
% 55.77/7.54  --inst_passive_queue_type               priority_queues
% 55.77/7.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.77/7.54  --inst_passive_queues_freq              [25;2]
% 55.77/7.54  --inst_dismatching                      true
% 55.77/7.54  --inst_eager_unprocessed_to_passive     true
% 55.77/7.54  --inst_prop_sim_given                   true
% 55.77/7.54  --inst_prop_sim_new                     false
% 55.77/7.54  --inst_subs_new                         false
% 55.77/7.54  --inst_eq_res_simp                      false
% 55.77/7.54  --inst_subs_given                       false
% 55.77/7.54  --inst_orphan_elimination               true
% 55.77/7.54  --inst_learning_loop_flag               true
% 55.77/7.54  --inst_learning_start                   3000
% 55.77/7.54  --inst_learning_factor                  2
% 55.77/7.54  --inst_start_prop_sim_after_learn       3
% 55.77/7.54  --inst_sel_renew                        solver
% 55.77/7.54  --inst_lit_activity_flag                true
% 55.77/7.54  --inst_restr_to_given                   false
% 55.77/7.54  --inst_activity_threshold               500
% 55.77/7.54  --inst_out_proof                        true
% 55.77/7.54  
% 55.77/7.54  ------ Resolution Options
% 55.77/7.54  
% 55.77/7.54  --resolution_flag                       false
% 55.77/7.54  --res_lit_sel                           adaptive
% 55.77/7.54  --res_lit_sel_side                      none
% 55.77/7.54  --res_ordering                          kbo
% 55.77/7.54  --res_to_prop_solver                    active
% 55.77/7.54  --res_prop_simpl_new                    false
% 55.77/7.54  --res_prop_simpl_given                  true
% 55.77/7.54  --res_passive_queue_type                priority_queues
% 55.77/7.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.77/7.54  --res_passive_queues_freq               [15;5]
% 55.77/7.54  --res_forward_subs                      full
% 55.77/7.54  --res_backward_subs                     full
% 55.77/7.54  --res_forward_subs_resolution           true
% 55.77/7.54  --res_backward_subs_resolution          true
% 55.77/7.54  --res_orphan_elimination                true
% 55.77/7.54  --res_time_limit                        2.
% 55.77/7.54  --res_out_proof                         true
% 55.77/7.54  
% 55.77/7.54  ------ Superposition Options
% 55.77/7.54  
% 55.77/7.54  --superposition_flag                    true
% 55.77/7.54  --sup_passive_queue_type                priority_queues
% 55.77/7.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.77/7.54  --sup_passive_queues_freq               [8;1;4]
% 55.77/7.54  --demod_completeness_check              fast
% 55.77/7.54  --demod_use_ground                      true
% 55.77/7.54  --sup_to_prop_solver                    passive
% 55.77/7.54  --sup_prop_simpl_new                    true
% 55.77/7.54  --sup_prop_simpl_given                  true
% 55.77/7.54  --sup_fun_splitting                     true
% 55.77/7.54  --sup_smt_interval                      50000
% 55.77/7.54  
% 55.77/7.54  ------ Superposition Simplification Setup
% 55.77/7.54  
% 55.77/7.54  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.77/7.54  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.77/7.54  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.77/7.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.77/7.54  --sup_full_triv                         [TrivRules;PropSubs]
% 55.77/7.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.77/7.54  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.77/7.54  --sup_immed_triv                        [TrivRules]
% 55.77/7.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.77/7.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.77/7.54  --sup_immed_bw_main                     []
% 55.77/7.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.77/7.54  --sup_input_triv                        [Unflattening;TrivRules]
% 55.77/7.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.77/7.54  --sup_input_bw                          []
% 55.77/7.54  
% 55.77/7.54  ------ Combination Options
% 55.77/7.54  
% 55.77/7.54  --comb_res_mult                         3
% 55.77/7.54  --comb_sup_mult                         2
% 55.77/7.54  --comb_inst_mult                        10
% 55.77/7.54  
% 55.77/7.54  ------ Debug Options
% 55.77/7.54  
% 55.77/7.54  --dbg_backtrace                         false
% 55.77/7.54  --dbg_dump_prop_clauses                 false
% 55.77/7.54  --dbg_dump_prop_clauses_file            -
% 55.77/7.54  --dbg_out_stat                          false
% 55.77/7.54  
% 55.77/7.54  
% 55.77/7.54  
% 55.77/7.54  
% 55.77/7.54  ------ Proving...
% 55.77/7.54  
% 55.77/7.54  
% 55.77/7.54  % SZS status Theorem for theBenchmark.p
% 55.77/7.54  
% 55.77/7.54  % SZS output start CNFRefutation for theBenchmark.p
% 55.77/7.54  
% 55.77/7.54  fof(f2,axiom,(
% 55.77/7.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f33,plain,(
% 55.77/7.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 55.77/7.54    inference(ennf_transformation,[],[f2])).
% 55.77/7.54  
% 55.77/7.54  fof(f40,plain,(
% 55.77/7.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 55.77/7.54    inference(nnf_transformation,[],[f33])).
% 55.77/7.54  
% 55.77/7.54  fof(f41,plain,(
% 55.77/7.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 55.77/7.54    inference(rectify,[],[f40])).
% 55.77/7.54  
% 55.77/7.54  fof(f42,plain,(
% 55.77/7.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 55.77/7.54    introduced(choice_axiom,[])).
% 55.77/7.54  
% 55.77/7.54  fof(f43,plain,(
% 55.77/7.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 55.77/7.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 55.77/7.54  
% 55.77/7.54  fof(f56,plain,(
% 55.77/7.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 55.77/7.54    inference(cnf_transformation,[],[f43])).
% 55.77/7.54  
% 55.77/7.54  fof(f24,axiom,(
% 55.77/7.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f49,plain,(
% 55.77/7.54    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 55.77/7.54    inference(nnf_transformation,[],[f24])).
% 55.77/7.54  
% 55.77/7.54  fof(f84,plain,(
% 55.77/7.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 55.77/7.54    inference(cnf_transformation,[],[f49])).
% 55.77/7.54  
% 55.77/7.54  fof(f17,axiom,(
% 55.77/7.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f76,plain,(
% 55.77/7.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 55.77/7.54    inference(cnf_transformation,[],[f17])).
% 55.77/7.54  
% 55.77/7.54  fof(f18,axiom,(
% 55.77/7.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f77,plain,(
% 55.77/7.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 55.77/7.54    inference(cnf_transformation,[],[f18])).
% 55.77/7.54  
% 55.77/7.54  fof(f19,axiom,(
% 55.77/7.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f78,plain,(
% 55.77/7.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 55.77/7.54    inference(cnf_transformation,[],[f19])).
% 55.77/7.54  
% 55.77/7.54  fof(f20,axiom,(
% 55.77/7.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f79,plain,(
% 55.77/7.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 55.77/7.54    inference(cnf_transformation,[],[f20])).
% 55.77/7.54  
% 55.77/7.54  fof(f21,axiom,(
% 55.77/7.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f80,plain,(
% 55.77/7.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 55.77/7.54    inference(cnf_transformation,[],[f21])).
% 55.77/7.54  
% 55.77/7.54  fof(f22,axiom,(
% 55.77/7.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f81,plain,(
% 55.77/7.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 55.77/7.54    inference(cnf_transformation,[],[f22])).
% 55.77/7.54  
% 55.77/7.54  fof(f94,plain,(
% 55.77/7.54    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 55.77/7.54    inference(definition_unfolding,[],[f80,f81])).
% 55.77/7.54  
% 55.77/7.54  fof(f95,plain,(
% 55.77/7.54    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 55.77/7.54    inference(definition_unfolding,[],[f79,f94])).
% 55.77/7.54  
% 55.77/7.54  fof(f96,plain,(
% 55.77/7.54    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 55.77/7.54    inference(definition_unfolding,[],[f78,f95])).
% 55.77/7.54  
% 55.77/7.54  fof(f97,plain,(
% 55.77/7.54    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 55.77/7.54    inference(definition_unfolding,[],[f77,f96])).
% 55.77/7.54  
% 55.77/7.54  fof(f100,plain,(
% 55.77/7.54    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 55.77/7.54    inference(definition_unfolding,[],[f76,f97])).
% 55.77/7.54  
% 55.77/7.54  fof(f112,plain,(
% 55.77/7.54    ( ! [X0,X1] : (r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 55.77/7.54    inference(definition_unfolding,[],[f84,f100])).
% 55.77/7.54  
% 55.77/7.54  fof(f28,conjecture,(
% 55.77/7.54    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f29,negated_conjecture,(
% 55.77/7.54    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 55.77/7.54    inference(negated_conjecture,[],[f28])).
% 55.77/7.54  
% 55.77/7.54  fof(f39,plain,(
% 55.77/7.54    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 55.77/7.54    inference(ennf_transformation,[],[f29])).
% 55.77/7.54  
% 55.77/7.54  fof(f52,plain,(
% 55.77/7.54    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3) & (k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3) & (k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3) & k2_xboole_0(sK3,sK4) = k1_tarski(sK2))),
% 55.77/7.54    introduced(choice_axiom,[])).
% 55.77/7.54  
% 55.77/7.54  fof(f53,plain,(
% 55.77/7.54    (k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3) & (k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3) & (k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3) & k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 55.77/7.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f52])).
% 55.77/7.54  
% 55.77/7.54  fof(f90,plain,(
% 55.77/7.54    k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 55.77/7.54    inference(cnf_transformation,[],[f53])).
% 55.77/7.54  
% 55.77/7.54  fof(f27,axiom,(
% 55.77/7.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f89,plain,(
% 55.77/7.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 55.77/7.54    inference(cnf_transformation,[],[f27])).
% 55.77/7.54  
% 55.77/7.54  fof(f98,plain,(
% 55.77/7.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 55.77/7.54    inference(definition_unfolding,[],[f89,f97])).
% 55.77/7.54  
% 55.77/7.54  fof(f121,plain,(
% 55.77/7.54    k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 55.77/7.54    inference(definition_unfolding,[],[f90,f98,f100])).
% 55.77/7.54  
% 55.77/7.54  fof(f11,axiom,(
% 55.77/7.54    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f70,plain,(
% 55.77/7.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 55.77/7.54    inference(cnf_transformation,[],[f11])).
% 55.77/7.54  
% 55.77/7.54  fof(f110,plain,(
% 55.77/7.54    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 55.77/7.54    inference(definition_unfolding,[],[f70,f98])).
% 55.77/7.54  
% 55.77/7.54  fof(f26,axiom,(
% 55.77/7.54    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f50,plain,(
% 55.77/7.54    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 55.77/7.54    inference(nnf_transformation,[],[f26])).
% 55.77/7.54  
% 55.77/7.54  fof(f51,plain,(
% 55.77/7.54    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 55.77/7.54    inference(flattening,[],[f50])).
% 55.77/7.54  
% 55.77/7.54  fof(f86,plain,(
% 55.77/7.54    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 55.77/7.54    inference(cnf_transformation,[],[f51])).
% 55.77/7.54  
% 55.77/7.54  fof(f117,plain,(
% 55.77/7.54    ( ! [X0,X1] : (k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) )),
% 55.77/7.54    inference(definition_unfolding,[],[f86,f100,f100])).
% 55.77/7.54  
% 55.77/7.54  fof(f7,axiom,(
% 55.77/7.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f47,plain,(
% 55.77/7.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 55.77/7.54    inference(nnf_transformation,[],[f7])).
% 55.77/7.54  
% 55.77/7.54  fof(f48,plain,(
% 55.77/7.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 55.77/7.54    inference(flattening,[],[f47])).
% 55.77/7.54  
% 55.77/7.54  fof(f66,plain,(
% 55.77/7.54    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 55.77/7.54    inference(cnf_transformation,[],[f48])).
% 55.77/7.54  
% 55.77/7.54  fof(f64,plain,(
% 55.77/7.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 55.77/7.54    inference(cnf_transformation,[],[f48])).
% 55.77/7.54  
% 55.77/7.54  fof(f123,plain,(
% 55.77/7.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 55.77/7.54    inference(equality_resolution,[],[f64])).
% 55.77/7.54  
% 55.77/7.54  fof(f91,plain,(
% 55.77/7.54    k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3),
% 55.77/7.54    inference(cnf_transformation,[],[f53])).
% 55.77/7.54  
% 55.77/7.54  fof(f120,plain,(
% 55.77/7.54    k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3),
% 55.77/7.54    inference(definition_unfolding,[],[f91,f100,f100])).
% 55.77/7.54  
% 55.77/7.54  fof(f92,plain,(
% 55.77/7.54    k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3),
% 55.77/7.54    inference(cnf_transformation,[],[f53])).
% 55.77/7.54  
% 55.77/7.54  fof(f119,plain,(
% 55.77/7.54    k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 | k1_xboole_0 != sK3),
% 55.77/7.54    inference(definition_unfolding,[],[f92,f100])).
% 55.77/7.54  
% 55.77/7.54  fof(f8,axiom,(
% 55.77/7.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f35,plain,(
% 55.77/7.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 55.77/7.54    inference(ennf_transformation,[],[f8])).
% 55.77/7.54  
% 55.77/7.54  fof(f67,plain,(
% 55.77/7.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 55.77/7.54    inference(cnf_transformation,[],[f35])).
% 55.77/7.54  
% 55.77/7.54  fof(f109,plain,(
% 55.77/7.54    ( ! [X0,X1] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 55.77/7.54    inference(definition_unfolding,[],[f67,f98])).
% 55.77/7.54  
% 55.77/7.54  fof(f6,axiom,(
% 55.77/7.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f32,plain,(
% 55.77/7.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 55.77/7.54    inference(rectify,[],[f6])).
% 55.77/7.54  
% 55.77/7.54  fof(f34,plain,(
% 55.77/7.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 55.77/7.54    inference(ennf_transformation,[],[f32])).
% 55.77/7.54  
% 55.77/7.54  fof(f45,plain,(
% 55.77/7.54    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 55.77/7.54    introduced(choice_axiom,[])).
% 55.77/7.54  
% 55.77/7.54  fof(f46,plain,(
% 55.77/7.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 55.77/7.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f45])).
% 55.77/7.54  
% 55.77/7.54  fof(f63,plain,(
% 55.77/7.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 55.77/7.54    inference(cnf_transformation,[],[f46])).
% 55.77/7.54  
% 55.77/7.54  fof(f14,axiom,(
% 55.77/7.54    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f73,plain,(
% 55.77/7.54    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 55.77/7.54    inference(cnf_transformation,[],[f14])).
% 55.77/7.54  
% 55.77/7.54  fof(f99,plain,(
% 55.77/7.54    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 55.77/7.54    inference(definition_unfolding,[],[f73,f98])).
% 55.77/7.54  
% 55.77/7.54  fof(f107,plain,(
% 55.77/7.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))) )),
% 55.77/7.54    inference(definition_unfolding,[],[f63,f99])).
% 55.77/7.54  
% 55.77/7.54  fof(f12,axiom,(
% 55.77/7.54    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f71,plain,(
% 55.77/7.54    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 55.77/7.54    inference(cnf_transformation,[],[f12])).
% 55.77/7.54  
% 55.77/7.54  fof(f1,axiom,(
% 55.77/7.54    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f54,plain,(
% 55.77/7.54    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 55.77/7.54    inference(cnf_transformation,[],[f1])).
% 55.77/7.54  
% 55.77/7.54  fof(f9,axiom,(
% 55.77/7.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f68,plain,(
% 55.77/7.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 55.77/7.54    inference(cnf_transformation,[],[f9])).
% 55.77/7.54  
% 55.77/7.54  fof(f13,axiom,(
% 55.77/7.54    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f72,plain,(
% 55.77/7.54    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 55.77/7.54    inference(cnf_transformation,[],[f13])).
% 55.77/7.54  
% 55.77/7.54  fof(f3,axiom,(
% 55.77/7.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f44,plain,(
% 55.77/7.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 55.77/7.54    inference(nnf_transformation,[],[f3])).
% 55.77/7.54  
% 55.77/7.54  fof(f59,plain,(
% 55.77/7.54    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 55.77/7.54    inference(cnf_transformation,[],[f44])).
% 55.77/7.54  
% 55.77/7.54  fof(f103,plain,(
% 55.77/7.54    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) != k1_xboole_0) )),
% 55.77/7.54    inference(definition_unfolding,[],[f59,f99])).
% 55.77/7.54  
% 55.77/7.54  fof(f25,axiom,(
% 55.77/7.54    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f38,plain,(
% 55.77/7.54    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 55.77/7.54    inference(ennf_transformation,[],[f25])).
% 55.77/7.54  
% 55.77/7.54  fof(f85,plain,(
% 55.77/7.54    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 55.77/7.54    inference(cnf_transformation,[],[f38])).
% 55.77/7.54  
% 55.77/7.54  fof(f114,plain,(
% 55.77/7.54    ( ! [X0,X1] : (r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 55.77/7.54    inference(definition_unfolding,[],[f85,f100])).
% 55.77/7.54  
% 55.77/7.54  fof(f4,axiom,(
% 55.77/7.54    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f30,plain,(
% 55.77/7.54    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 55.77/7.54    inference(rectify,[],[f4])).
% 55.77/7.54  
% 55.77/7.54  fof(f60,plain,(
% 55.77/7.54    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 55.77/7.54    inference(cnf_transformation,[],[f30])).
% 55.77/7.54  
% 55.77/7.54  fof(f105,plain,(
% 55.77/7.54    ( ! [X0] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 55.77/7.54    inference(definition_unfolding,[],[f60,f98])).
% 55.77/7.54  
% 55.77/7.54  fof(f62,plain,(
% 55.77/7.54    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 55.77/7.54    inference(cnf_transformation,[],[f46])).
% 55.77/7.54  
% 55.77/7.54  fof(f108,plain,(
% 55.77/7.54    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) | r1_xboole_0(X0,X1)) )),
% 55.77/7.54    inference(definition_unfolding,[],[f62,f99])).
% 55.77/7.54  
% 55.77/7.54  fof(f93,plain,(
% 55.77/7.54    k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3),
% 55.77/7.54    inference(cnf_transformation,[],[f53])).
% 55.77/7.54  
% 55.77/7.54  fof(f118,plain,(
% 55.77/7.54    k1_xboole_0 != sK4 | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3),
% 55.77/7.54    inference(definition_unfolding,[],[f93,f100])).
% 55.77/7.54  
% 55.77/7.54  fof(f15,axiom,(
% 55.77/7.54    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f74,plain,(
% 55.77/7.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 55.77/7.54    inference(cnf_transformation,[],[f15])).
% 55.77/7.54  
% 55.77/7.54  fof(f102,plain,(
% 55.77/7.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)))) )),
% 55.77/7.54    inference(definition_unfolding,[],[f74,f98,f81,f100])).
% 55.77/7.54  
% 55.77/7.54  fof(f23,axiom,(
% 55.77/7.54    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f82,plain,(
% 55.77/7.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 55.77/7.54    inference(cnf_transformation,[],[f23])).
% 55.77/7.54  
% 55.77/7.54  fof(f16,axiom,(
% 55.77/7.54    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 55.77/7.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.54  
% 55.77/7.54  fof(f75,plain,(
% 55.77/7.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 55.77/7.54    inference(cnf_transformation,[],[f16])).
% 55.77/7.54  
% 55.77/7.54  fof(f101,plain,(
% 55.77/7.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X7)))) )),
% 55.77/7.54    inference(definition_unfolding,[],[f75,f98,f81,f97])).
% 55.77/7.54  
% 55.77/7.54  fof(f111,plain,(
% 55.77/7.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6)))) )),
% 55.77/7.54    inference(definition_unfolding,[],[f82,f101])).
% 55.77/7.54  
% 55.77/7.54  cnf(c_3,plain,
% 55.77/7.54      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 55.77/7.54      inference(cnf_transformation,[],[f56]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_947,plain,
% 55.77/7.54      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 55.77/7.54      | r1_tarski(X0,X1) = iProver_top ),
% 55.77/7.54      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_21,plain,
% 55.77/7.54      ( ~ r2_hidden(X0,X1)
% 55.77/7.54      | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) ),
% 55.77/7.54      inference(cnf_transformation,[],[f112]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_936,plain,
% 55.77/7.54      ( r2_hidden(X0,X1) != iProver_top
% 55.77/7.54      | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 55.77/7.54      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_30,negated_conjecture,
% 55.77/7.54      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 55.77/7.54      inference(cnf_transformation,[],[f121]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_17,plain,
% 55.77/7.54      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
% 55.77/7.54      inference(cnf_transformation,[],[f110]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_937,plain,
% 55.77/7.54      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 55.77/7.54      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_5825,plain,
% 55.77/7.54      ( r1_tarski(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_30,c_937]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_26,plain,
% 55.77/7.54      ( ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
% 55.77/7.54      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
% 55.77/7.54      | k1_xboole_0 = X0 ),
% 55.77/7.54      inference(cnf_transformation,[],[f117]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_931,plain,
% 55.77/7.54      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X1
% 55.77/7.54      | k1_xboole_0 = X1
% 55.77/7.54      | r1_tarski(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 55.77/7.54      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_5834,plain,
% 55.77/7.54      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
% 55.77/7.54      | sK3 = k1_xboole_0 ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_5825,c_931]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_6229,plain,
% 55.77/7.54      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = X0
% 55.77/7.54      | sK3 = k1_xboole_0
% 55.77/7.54      | k1_xboole_0 = X0
% 55.77/7.54      | r1_tarski(X0,sK3) != iProver_top ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_5834,c_931]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_8052,plain,
% 55.77/7.54      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 55.77/7.54      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
% 55.77/7.54      | sK3 = k1_xboole_0
% 55.77/7.54      | r2_hidden(X0,sK3) != iProver_top ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_936,c_6229]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_11,plain,
% 55.77/7.54      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 55.77/7.54      inference(cnf_transformation,[],[f66]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_1022,plain,
% 55.77/7.54      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 55.77/7.54      inference(instantiation,[status(thm)],[c_11]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_1124,plain,
% 55.77/7.54      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 55.77/7.54      inference(instantiation,[status(thm)],[c_1022]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_13,plain,
% 55.77/7.54      ( r1_tarski(X0,X0) ),
% 55.77/7.54      inference(cnf_transformation,[],[f123]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_1217,plain,
% 55.77/7.54      ( r1_tarski(sK4,sK4) ),
% 55.77/7.54      inference(instantiation,[status(thm)],[c_13]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_475,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_1337,plain,
% 55.77/7.54      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X0
% 55.77/7.54      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK4
% 55.77/7.54      | sK4 != X0 ),
% 55.77/7.54      inference(instantiation,[status(thm)],[c_475]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_1629,plain,
% 55.77/7.54      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 55.77/7.54      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK4
% 55.77/7.54      | sK4 != k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 55.77/7.54      inference(instantiation,[status(thm)],[c_1337]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_29,negated_conjecture,
% 55.77/7.54      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
% 55.77/7.54      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
% 55.77/7.54      inference(cnf_transformation,[],[f120]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_6238,plain,
% 55.77/7.54      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
% 55.77/7.54      | sK3 = k1_xboole_0 ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_5834,c_29]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_28,negated_conjecture,
% 55.77/7.54      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4
% 55.77/7.54      | k1_xboole_0 != sK3 ),
% 55.77/7.54      inference(cnf_transformation,[],[f119]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_984,plain,
% 55.77/7.54      ( ~ r1_tarski(sK3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
% 55.77/7.54      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = sK3
% 55.77/7.54      | k1_xboole_0 = sK3 ),
% 55.77/7.54      inference(instantiation,[status(thm)],[c_26]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_986,plain,
% 55.77/7.54      ( ~ r1_tarski(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 55.77/7.54      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK3
% 55.77/7.54      | k1_xboole_0 = sK3 ),
% 55.77/7.54      inference(instantiation,[status(thm)],[c_984]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_5829,plain,
% 55.77/7.54      ( r1_tarski(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 55.77/7.54      inference(predicate_to_equality_rev,[status(thm)],[c_5825]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_6310,plain,
% 55.77/7.54      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK4 ),
% 55.77/7.54      inference(global_propositional_subsumption,
% 55.77/7.54                [status(thm)],
% 55.77/7.54                [c_6238,c_29,c_28,c_986,c_5829]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_14,plain,
% 55.77/7.54      ( ~ r1_tarski(X0,X1)
% 55.77/7.54      | k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X1 ),
% 55.77/7.54      inference(cnf_transformation,[],[f109]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_939,plain,
% 55.77/7.54      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X1
% 55.77/7.54      | r1_tarski(X0,X1) != iProver_top ),
% 55.77/7.54      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_8350,plain,
% 55.77/7.54      ( k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_5825,c_939]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_9,plain,
% 55.77/7.54      ( ~ r1_xboole_0(X0,X1)
% 55.77/7.54      | ~ r2_hidden(X2,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) ),
% 55.77/7.54      inference(cnf_transformation,[],[f107]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_18,plain,
% 55.77/7.54      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 55.77/7.54      inference(cnf_transformation,[],[f71]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_1,plain,
% 55.77/7.54      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 55.77/7.54      inference(cnf_transformation,[],[f54]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_469,plain,
% 55.77/7.54      ( ~ r1_xboole_0(X0,X1)
% 55.77/7.54      | ~ r2_hidden(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))) ),
% 55.77/7.54      inference(theory_normalisation,[status(thm)],[c_9,c_18,c_1]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_943,plain,
% 55.77/7.54      ( r1_xboole_0(X0,X1) != iProver_top
% 55.77/7.54      | r2_hidden(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))) != iProver_top ),
% 55.77/7.54      inference(predicate_to_equality,[status(thm)],[c_469]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_12758,plain,
% 55.77/7.54      ( r1_xboole_0(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 55.77/7.54      | r2_hidden(X0,k5_xboole_0(sK3,k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != iProver_top ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_8350,c_943]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_15,plain,
% 55.77/7.54      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 55.77/7.54      inference(cnf_transformation,[],[f68]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_19,plain,
% 55.77/7.54      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 55.77/7.54      inference(cnf_transformation,[],[f72]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_12767,plain,
% 55.77/7.54      ( r1_xboole_0(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 55.77/7.54      | r2_hidden(X0,sK3) != iProver_top ),
% 55.77/7.54      inference(demodulation,[status(thm)],[c_12758,c_15,c_19]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_5,plain,
% 55.77/7.54      ( r1_xboole_0(X0,X1)
% 55.77/7.54      | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) != k1_xboole_0 ),
% 55.77/7.54      inference(cnf_transformation,[],[f103]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_472,plain,
% 55.77/7.54      ( r1_xboole_0(X0,X1)
% 55.77/7.54      | k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) != k1_xboole_0 ),
% 55.77/7.54      inference(theory_normalisation,[status(thm)],[c_5,c_18,c_1]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_945,plain,
% 55.77/7.54      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) != k1_xboole_0
% 55.77/7.54      | r1_xboole_0(X0,X1) = iProver_top ),
% 55.77/7.54      inference(predicate_to_equality,[status(thm)],[c_472]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_19033,plain,
% 55.77/7.54      ( k5_xboole_0(sK3,k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))) != k1_xboole_0
% 55.77/7.54      | r1_xboole_0(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_8350,c_945]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_19042,plain,
% 55.77/7.54      ( sK3 != k1_xboole_0
% 55.77/7.54      | r1_xboole_0(sK3,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 55.77/7.54      inference(demodulation,[status(thm)],[c_19033,c_15,c_19]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_1028,plain,
% 55.77/7.54      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 55.77/7.54      inference(instantiation,[status(thm)],[c_475]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_1313,plain,
% 55.77/7.54      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 55.77/7.54      inference(instantiation,[status(thm)],[c_1028]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_3298,plain,
% 55.77/7.54      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,sK4)) != sK4
% 55.77/7.54      | sK4 = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,sK4))
% 55.77/7.54      | sK4 != sK4 ),
% 55.77/7.54      inference(instantiation,[status(thm)],[c_1313]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_28835,plain,
% 55.77/7.54      ( k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != sK4
% 55.77/7.54      | sK4 = k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4))
% 55.77/7.54      | sK4 != sK4 ),
% 55.77/7.54      inference(instantiation,[status(thm)],[c_3298]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_23,plain,
% 55.77/7.54      ( r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
% 55.77/7.54      | r2_hidden(X0,X1) ),
% 55.77/7.54      inference(cnf_transformation,[],[f114]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_934,plain,
% 55.77/7.54      ( r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
% 55.77/7.54      | r2_hidden(X0,X1) = iProver_top ),
% 55.77/7.54      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_6226,plain,
% 55.77/7.54      ( sK3 = k1_xboole_0
% 55.77/7.54      | r1_xboole_0(sK3,X0) = iProver_top
% 55.77/7.54      | r2_hidden(sK2,X0) = iProver_top ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_5834,c_934]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_7,plain,
% 55.77/7.54      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 55.77/7.54      inference(cnf_transformation,[],[f105]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_10,plain,
% 55.77/7.54      ( r1_xboole_0(X0,X1)
% 55.77/7.54      | r2_hidden(sK1(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) ),
% 55.77/7.54      inference(cnf_transformation,[],[f108]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_468,plain,
% 55.77/7.54      ( r1_xboole_0(X0,X1)
% 55.77/7.54      | r2_hidden(sK1(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))) ),
% 55.77/7.54      inference(theory_normalisation,[status(thm)],[c_10,c_18,c_1]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_942,plain,
% 55.77/7.54      ( r1_xboole_0(X0,X1) = iProver_top
% 55.77/7.54      | r2_hidden(sK1(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))) = iProver_top ),
% 55.77/7.54      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_10307,plain,
% 55.77/7.54      ( r1_xboole_0(X0,X0) = iProver_top
% 55.77/7.54      | r2_hidden(sK1(X0,X0),k5_xboole_0(X0,k5_xboole_0(X0,X0))) = iProver_top ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_7,c_942]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_10321,plain,
% 55.77/7.54      ( r1_xboole_0(X0,X0) = iProver_top
% 55.77/7.54      | r2_hidden(sK1(X0,X0),X0) = iProver_top ),
% 55.77/7.54      inference(light_normalisation,[status(thm)],[c_10307,c_15,c_19]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_12753,plain,
% 55.77/7.54      ( r1_xboole_0(sK3,sK4) != iProver_top
% 55.77/7.54      | r2_hidden(X0,k5_xboole_0(sK3,k5_xboole_0(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != iProver_top ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_30,c_943]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_14725,plain,
% 55.77/7.54      ( r1_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(sK3,k5_xboole_0(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = iProver_top
% 55.77/7.54      | r1_xboole_0(sK3,sK4) != iProver_top ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_10321,c_12753]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_15226,plain,
% 55.77/7.54      ( sK3 = k1_xboole_0
% 55.77/7.54      | r1_xboole_0(k5_xboole_0(sK3,k5_xboole_0(sK4,sK3)),k5_xboole_0(sK3,k5_xboole_0(sK4,sK3))) = iProver_top
% 55.77/7.54      | r1_xboole_0(sK3,sK4) != iProver_top ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_5834,c_14725]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_1440,plain,
% 55.77/7.54      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_19,c_18]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_1317,plain,
% 55.77/7.54      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_15,c_1]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_1446,plain,
% 55.77/7.54      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 55.77/7.54      inference(demodulation,[status(thm)],[c_1440,c_1317]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_1594,plain,
% 55.77/7.54      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_1,c_1446]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_15228,plain,
% 55.77/7.54      ( sK3 = k1_xboole_0
% 55.77/7.54      | r1_xboole_0(sK3,sK4) != iProver_top
% 55.77/7.54      | r1_xboole_0(sK4,sK4) = iProver_top ),
% 55.77/7.54      inference(demodulation,[status(thm)],[c_15226,c_1594]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_27,negated_conjecture,
% 55.77/7.54      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != sK3
% 55.77/7.54      | k1_xboole_0 != sK4 ),
% 55.77/7.54      inference(cnf_transformation,[],[f118]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_6240,plain,
% 55.77/7.54      ( sK3 = k1_xboole_0 | sK4 != k1_xboole_0 ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_5834,c_27]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_14729,plain,
% 55.77/7.54      ( sK3 = k1_xboole_0
% 55.77/7.54      | r1_xboole_0(sK3,sK4) != iProver_top
% 55.77/7.54      | r2_hidden(X0,k5_xboole_0(sK3,k5_xboole_0(sK4,sK3))) != iProver_top ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_5834,c_12753]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_14730,plain,
% 55.77/7.54      ( sK3 = k1_xboole_0
% 55.77/7.54      | r1_xboole_0(sK3,sK4) != iProver_top
% 55.77/7.54      | r2_hidden(X0,sK4) != iProver_top ),
% 55.77/7.54      inference(demodulation,[status(thm)],[c_14729,c_1594]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_14742,plain,
% 55.77/7.54      ( sK3 = k1_xboole_0
% 55.77/7.54      | r1_xboole_0(sK3,sK4) != iProver_top
% 55.77/7.54      | r2_hidden(sK2,sK4) != iProver_top ),
% 55.77/7.54      inference(instantiation,[status(thm)],[c_14730]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_14723,plain,
% 55.77/7.54      ( r1_xboole_0(sK3,sK4) != iProver_top
% 55.77/7.54      | r1_tarski(k5_xboole_0(sK3,k5_xboole_0(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))),X0) = iProver_top ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_947,c_12753]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_14925,plain,
% 55.77/7.54      ( sK3 = k1_xboole_0
% 55.77/7.54      | r1_xboole_0(sK3,sK4) != iProver_top
% 55.77/7.54      | r1_tarski(k5_xboole_0(sK3,k5_xboole_0(sK4,sK3)),X0) = iProver_top ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_5834,c_14723]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_14929,plain,
% 55.77/7.54      ( sK3 = k1_xboole_0
% 55.77/7.54      | r1_xboole_0(sK3,sK4) != iProver_top
% 55.77/7.54      | r1_tarski(sK4,X0) = iProver_top ),
% 55.77/7.54      inference(demodulation,[status(thm)],[c_14925,c_1594]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_28107,plain,
% 55.77/7.54      ( sK3 = k1_xboole_0
% 55.77/7.54      | r2_hidden(sK2,sK4) = iProver_top
% 55.77/7.54      | r1_tarski(sK4,X0) = iProver_top ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_6226,c_14929]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_28113,plain,
% 55.77/7.54      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = sK4
% 55.77/7.54      | sK3 = k1_xboole_0
% 55.77/7.54      | sK4 = k1_xboole_0
% 55.77/7.54      | r2_hidden(sK2,sK4) = iProver_top ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_28107,c_931]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_28122,plain,
% 55.77/7.54      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK4
% 55.77/7.54      | sK3 = k1_xboole_0
% 55.77/7.54      | sK4 = k1_xboole_0
% 55.77/7.54      | r2_hidden(sK2,sK4) = iProver_top ),
% 55.77/7.54      inference(instantiation,[status(thm)],[c_28113]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_36327,plain,
% 55.77/7.54      ( r1_xboole_0(sK3,sK4) != iProver_top | sK3 = k1_xboole_0 ),
% 55.77/7.54      inference(global_propositional_subsumption,
% 55.77/7.54                [status(thm)],
% 55.77/7.54                [c_15228,c_29,c_28,c_986,c_5829,c_6240,c_14742,c_28122]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_36328,plain,
% 55.77/7.54      ( sK3 = k1_xboole_0 | r1_xboole_0(sK3,sK4) != iProver_top ),
% 55.77/7.54      inference(renaming,[status(thm)],[c_36327]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_36331,plain,
% 55.77/7.54      ( sK3 = k1_xboole_0 | r2_hidden(sK2,sK4) = iProver_top ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_6226,c_36328]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_6689,plain,
% 55.77/7.54      ( sK3 = k1_xboole_0
% 55.77/7.54      | r2_hidden(sK2,X0) != iProver_top
% 55.77/7.54      | r1_tarski(sK3,X0) = iProver_top ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_5834,c_936]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_36334,plain,
% 55.77/7.54      ( sK3 = k1_xboole_0 | r1_tarski(sK3,sK4) = iProver_top ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_36331,c_6689]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_36745,plain,
% 55.77/7.54      ( k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = sK4
% 55.77/7.54      | sK3 = k1_xboole_0 ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_36334,c_939]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_52031,plain,
% 55.77/7.54      ( r2_hidden(X0,sK3) != iProver_top ),
% 55.77/7.54      inference(global_propositional_subsumption,
% 55.77/7.54                [status(thm)],
% 55.77/7.54                [c_8052,c_30,c_29,c_28,c_986,c_1124,c_1217,c_1629,c_5829,
% 55.77/7.54                 c_12767,c_19042,c_28835,c_36745]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_0,plain,
% 55.77/7.54      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 55.77/7.54      inference(cnf_transformation,[],[f102]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_6223,plain,
% 55.77/7.54      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),sK3)) = k5_enumset1(X0,X1,X2,X3,X4,X5,sK2)
% 55.77/7.54      | sK3 = k1_xboole_0 ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_5834,c_0]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_8231,plain,
% 55.77/7.54      ( sK3 = k1_xboole_0
% 55.77/7.54      | r1_tarski(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X1,X2,X3,X4,X5,sK2)) = iProver_top ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_6223,c_937]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_36749,plain,
% 55.77/7.54      ( sK3 = k1_xboole_0 ),
% 55.77/7.54      inference(global_propositional_subsumption,
% 55.77/7.54                [status(thm)],
% 55.77/7.54                [c_8231,c_30,c_29,c_28,c_986,c_1124,c_1217,c_1629,c_5829,
% 55.77/7.54                 c_28835,c_36745]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_52037,plain,
% 55.77/7.54      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 55.77/7.54      inference(light_normalisation,[status(thm)],[c_52031,c_36749]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_52039,plain,
% 55.77/7.54      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_947,c_52037]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_164895,plain,
% 55.77/7.54      ( k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_52039,c_939]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_20,plain,
% 55.77/7.54      ( k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 55.77/7.54      inference(cnf_transformation,[],[f111]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_1549,plain,
% 55.77/7.54      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_20,c_0]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_20555,plain,
% 55.77/7.54      ( k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK4,sK4)) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 55.77/7.54      inference(demodulation,[status(thm)],[c_1549,c_30]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_36764,plain,
% 55.77/7.54      ( k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK4,sK4)) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 55.77/7.54      inference(demodulation,[status(thm)],[c_36749,c_20555]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_36967,plain,
% 55.77/7.54      ( k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK4)) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 55.77/7.54      inference(superposition,[status(thm)],[c_1549,c_36764]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(c_190855,plain,
% 55.77/7.54      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = sK4 ),
% 55.77/7.54      inference(demodulation,[status(thm)],[c_164895,c_36967]) ).
% 55.77/7.54  
% 55.77/7.54  cnf(contradiction,plain,
% 55.77/7.54      ( $false ),
% 55.77/7.54      inference(minisat,[status(thm)],[c_190855,c_6310]) ).
% 55.77/7.54  
% 55.77/7.54  
% 55.77/7.54  % SZS output end CNFRefutation for theBenchmark.p
% 55.77/7.54  
% 55.77/7.54  ------                               Statistics
% 55.77/7.54  
% 55.77/7.54  ------ General
% 55.77/7.54  
% 55.77/7.54  abstr_ref_over_cycles:                  0
% 55.77/7.54  abstr_ref_under_cycles:                 0
% 55.77/7.54  gc_basic_clause_elim:                   0
% 55.77/7.54  forced_gc_time:                         0
% 55.77/7.54  parsing_time:                           0.009
% 55.77/7.54  unif_index_cands_time:                  0.
% 55.77/7.54  unif_index_add_time:                    0.
% 55.77/7.54  orderings_time:                         0.
% 55.77/7.54  out_proof_time:                         0.016
% 55.77/7.54  total_time:                             6.752
% 55.77/7.54  num_of_symbols:                         43
% 55.77/7.54  num_of_terms:                           866724
% 55.77/7.54  
% 55.77/7.54  ------ Preprocessing
% 55.77/7.54  
% 55.77/7.54  num_of_splits:                          0
% 55.77/7.54  num_of_split_atoms:                     0
% 55.77/7.54  num_of_reused_defs:                     0
% 55.77/7.54  num_eq_ax_congr_red:                    15
% 55.77/7.54  num_of_sem_filtered_clauses:            1
% 55.77/7.54  num_of_subtypes:                        0
% 55.77/7.54  monotx_restored_types:                  0
% 55.77/7.54  sat_num_of_epr_types:                   0
% 55.77/7.54  sat_num_of_non_cyclic_types:            0
% 55.77/7.54  sat_guarded_non_collapsed_types:        0
% 55.77/7.54  num_pure_diseq_elim:                    0
% 55.77/7.54  simp_replaced_by:                       0
% 55.77/7.54  res_preprocessed:                       137
% 55.77/7.54  prep_upred:                             0
% 55.77/7.54  prep_unflattend:                        0
% 55.77/7.54  smt_new_axioms:                         0
% 55.77/7.54  pred_elim_cands:                        3
% 55.77/7.54  pred_elim:                              0
% 55.77/7.54  pred_elim_cl:                           0
% 55.77/7.54  pred_elim_cycles:                       2
% 55.77/7.54  merged_defs:                            16
% 55.77/7.54  merged_defs_ncl:                        0
% 55.77/7.54  bin_hyper_res:                          16
% 55.77/7.54  prep_cycles:                            4
% 55.77/7.54  pred_elim_time:                         0.
% 55.77/7.54  splitting_time:                         0.
% 55.77/7.54  sem_filter_time:                        0.
% 55.77/7.54  monotx_time:                            0.
% 55.77/7.54  subtype_inf_time:                       0.
% 55.77/7.54  
% 55.77/7.54  ------ Problem properties
% 55.77/7.54  
% 55.77/7.54  clauses:                                30
% 55.77/7.54  conjectures:                            4
% 55.77/7.54  epr:                                    4
% 55.77/7.54  horn:                                   26
% 55.77/7.54  ground:                                 4
% 55.77/7.54  unary:                                  13
% 55.77/7.54  binary:                                 13
% 55.77/7.54  lits:                                   51
% 55.77/7.54  lits_eq:                                21
% 55.77/7.54  fd_pure:                                0
% 55.77/7.54  fd_pseudo:                              0
% 55.77/7.54  fd_cond:                                0
% 55.77/7.54  fd_pseudo_cond:                         2
% 55.77/7.54  ac_symbols:                             1
% 55.77/7.54  
% 55.77/7.54  ------ Propositional Solver
% 55.77/7.54  
% 55.77/7.54  prop_solver_calls:                      33
% 55.77/7.54  prop_fast_solver_calls:                 1282
% 55.77/7.54  smt_solver_calls:                       0
% 55.77/7.54  smt_fast_solver_calls:                  0
% 55.77/7.54  prop_num_of_clauses:                    14485
% 55.77/7.54  prop_preprocess_simplified:             23552
% 55.77/7.54  prop_fo_subsumed:                       104
% 55.77/7.54  prop_solver_time:                       0.
% 55.77/7.54  smt_solver_time:                        0.
% 55.77/7.54  smt_fast_solver_time:                   0.
% 55.77/7.54  prop_fast_solver_time:                  0.
% 55.77/7.54  prop_unsat_core_time:                   0.001
% 55.77/7.54  
% 55.77/7.54  ------ QBF
% 55.77/7.54  
% 55.77/7.54  qbf_q_res:                              0
% 55.77/7.54  qbf_num_tautologies:                    0
% 55.77/7.54  qbf_prep_cycles:                        0
% 55.77/7.54  
% 55.77/7.54  ------ BMC1
% 55.77/7.54  
% 55.77/7.54  bmc1_current_bound:                     -1
% 55.77/7.54  bmc1_last_solved_bound:                 -1
% 55.77/7.54  bmc1_unsat_core_size:                   -1
% 55.77/7.54  bmc1_unsat_core_parents_size:           -1
% 55.77/7.54  bmc1_merge_next_fun:                    0
% 55.77/7.54  bmc1_unsat_core_clauses_time:           0.
% 55.77/7.54  
% 55.77/7.54  ------ Instantiation
% 55.77/7.54  
% 55.77/7.54  inst_num_of_clauses:                    3073
% 55.77/7.54  inst_num_in_passive:                    557
% 55.77/7.54  inst_num_in_active:                     1135
% 55.77/7.54  inst_num_in_unprocessed:                1381
% 55.77/7.54  inst_num_of_loops:                      1490
% 55.77/7.54  inst_num_of_learning_restarts:          0
% 55.77/7.54  inst_num_moves_active_passive:          352
% 55.77/7.54  inst_lit_activity:                      0
% 55.77/7.54  inst_lit_activity_moves:                0
% 55.77/7.54  inst_num_tautologies:                   0
% 55.77/7.54  inst_num_prop_implied:                  0
% 55.77/7.54  inst_num_existing_simplified:           0
% 55.77/7.54  inst_num_eq_res_simplified:             0
% 55.77/7.54  inst_num_child_elim:                    0
% 55.77/7.54  inst_num_of_dismatching_blockings:      1332
% 55.77/7.54  inst_num_of_non_proper_insts:           3603
% 55.77/7.54  inst_num_of_duplicates:                 0
% 55.77/7.54  inst_inst_num_from_inst_to_res:         0
% 55.77/7.54  inst_dismatching_checking_time:         0.
% 55.77/7.54  
% 55.77/7.54  ------ Resolution
% 55.77/7.54  
% 55.77/7.54  res_num_of_clauses:                     0
% 55.77/7.54  res_num_in_passive:                     0
% 55.77/7.54  res_num_in_active:                      0
% 55.77/7.54  res_num_of_loops:                       141
% 55.77/7.54  res_forward_subset_subsumed:            245
% 55.77/7.54  res_backward_subset_subsumed:           0
% 55.77/7.54  res_forward_subsumed:                   0
% 55.77/7.54  res_backward_subsumed:                  0
% 55.77/7.54  res_forward_subsumption_resolution:     0
% 55.77/7.54  res_backward_subsumption_resolution:    0
% 55.77/7.54  res_clause_to_clause_subsumption:       524398
% 55.77/7.54  res_orphan_elimination:                 0
% 55.77/7.54  res_tautology_del:                      257
% 55.77/7.54  res_num_eq_res_simplified:              0
% 55.77/7.54  res_num_sel_changes:                    0
% 55.77/7.54  res_moves_from_active_to_pass:          0
% 55.77/7.54  
% 55.77/7.54  ------ Superposition
% 55.77/7.54  
% 55.77/7.54  sup_time_total:                         0.
% 55.77/7.54  sup_time_generating:                    0.
% 55.77/7.54  sup_time_sim_full:                      0.
% 55.77/7.54  sup_time_sim_immed:                     0.
% 55.77/7.54  
% 55.77/7.54  sup_num_of_clauses:                     5087
% 55.77/7.54  sup_num_in_active:                      206
% 55.77/7.54  sup_num_in_passive:                     4881
% 55.77/7.54  sup_num_of_loops:                       296
% 55.77/7.54  sup_fw_superposition:                   41716
% 55.77/7.54  sup_bw_superposition:                   26884
% 55.77/7.54  sup_immediate_simplified:               63065
% 55.77/7.54  sup_given_eliminated:                   1
% 55.77/7.54  comparisons_done:                       0
% 55.77/7.54  comparisons_avoided:                    27
% 55.77/7.54  
% 55.77/7.54  ------ Simplifications
% 55.77/7.54  
% 55.77/7.54  
% 55.77/7.54  sim_fw_subset_subsumed:                 20
% 55.77/7.54  sim_bw_subset_subsumed:                 105
% 55.77/7.54  sim_fw_subsumed:                        699
% 55.77/7.54  sim_bw_subsumed:                        20
% 55.77/7.54  sim_fw_subsumption_res:                 0
% 55.77/7.54  sim_bw_subsumption_res:                 0
% 55.77/7.54  sim_tautology_del:                      18
% 55.77/7.54  sim_eq_tautology_del:                   12163
% 55.77/7.54  sim_eq_res_simp:                        2
% 55.77/7.54  sim_fw_demodulated:                     92072
% 55.77/7.54  sim_bw_demodulated:                     58
% 55.77/7.54  sim_light_normalised:                   8432
% 55.77/7.54  sim_joinable_taut:                      2083
% 55.77/7.54  sim_joinable_simp:                      0
% 55.77/7.54  sim_ac_normalised:                      0
% 55.77/7.54  sim_smt_subsumption:                    0
% 55.77/7.54  
%------------------------------------------------------------------------------
