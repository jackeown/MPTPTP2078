%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:07 EST 2020

% Result     : Theorem 7.63s
% Output     : CNFRefutation 7.63s
% Verified   : 
% Statistics : Number of formulae       :  175 (5435 expanded)
%              Number of clauses        :   97 ( 710 expanded)
%              Number of leaves         :   21 (1634 expanded)
%              Depth                    :   24
%              Number of atoms          :  377 (10578 expanded)
%              Number of equality atoms :  256 (8162 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,
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

fof(f38,plain,
    ( ( k1_xboole_0 != sK5
      | k1_tarski(sK3) != sK4 )
    & ( k1_tarski(sK3) != sK5
      | k1_xboole_0 != sK4 )
    & ( k1_tarski(sK3) != sK5
      | k1_tarski(sK3) != sK4 )
    & k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f37])).

fof(f63,plain,(
    k2_xboole_0(sK4,sK5) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f68])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f67])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f68])).

fof(f86,plain,(
    k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(definition_unfolding,[],[f63,f69,f70])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f49,f69])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f27])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f51,f70])).

fof(f91,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f64,plain,
    ( k1_tarski(sK3) != sK5
    | k1_tarski(sK3) != sK4 ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4 ),
    inference(definition_unfolding,[],[f64,f70,f70])).

fof(f66,plain,
    ( k1_xboole_0 != sK5
    | k1_tarski(sK3) != sK4 ),
    inference(cnf_transformation,[],[f38])).

fof(f83,plain,
    ( k1_xboole_0 != sK5
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4 ),
    inference(definition_unfolding,[],[f66,f70])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f35])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f62,f68])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f50,f68,f68])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f52,f70])).

fof(f89,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f78])).

fof(f90,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f89])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1) ),
    inference(definition_unfolding,[],[f48,f69])).

fof(f65,plain,
    ( k1_tarski(sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f38])).

fof(f84,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(definition_unfolding,[],[f65,f70])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f72,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f47,f69,f69])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f69])).

cnf(c_22,negated_conjecture,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_10,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_546,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_873,plain,
    ( r1_tarski(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_546])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_550,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_551,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4239,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_550,c_551])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_542,plain,
    ( X0 = X1
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12251,plain,
    ( sK1(X0) = X1
    | k1_xboole_0 = X0
    | r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4239,c_542])).

cnf(c_21799,plain,
    ( sK1(sK4) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_873,c_12251])).

cnf(c_21967,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK3,X0) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_21799,c_4239])).

cnf(c_21,negated_conjecture,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4
    | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_19,negated_conjecture,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_541,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1048,plain,
    ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK4)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_11,c_22])).

cnf(c_1287,plain,
    ( r1_tarski(sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1048,c_546])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_549,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3251,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK5
    | r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1287,c_549])).

cnf(c_3665,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK5
    | r2_hidden(sK3,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_541,c_3251])).

cnf(c_14,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_5214,plain,
    ( r2_hidden(k1_xboole_0,k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2435,plain,
    ( ~ r2_hidden(k1_xboole_0,k3_enumset1(X0,X0,X0,X0,X0))
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_7188,plain,
    ( ~ r2_hidden(k1_xboole_0,k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2435])).

cnf(c_294,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_578,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_21756,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_578])).

cnf(c_21968,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_21799,c_550])).

cnf(c_3250,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4
    | r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_873,c_549])).

cnf(c_3417,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_541,c_3250])).

cnf(c_21976,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_21968,c_3417])).

cnf(c_21800,plain,
    ( sK1(sK5) = sK3
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1287,c_12251])).

cnf(c_22171,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_21800,c_550])).

cnf(c_22379,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21967,c_21,c_19,c_3665,c_5214,c_7188,c_21756,c_21976,c_22171])).

cnf(c_9,plain,
    ( k4_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1286,plain,
    ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k4_xboole_0(sK5,sK4) ),
    inference(superposition,[status(thm)],[c_1048,c_9])).

cnf(c_22473,plain,
    ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k1_xboole_0) = k4_xboole_0(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_22379,c_1286])).

cnf(c_20,negated_conjecture,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_589,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_4459,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_589])).

cnf(c_22938,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22171,c_21,c_20,c_19,c_3665,c_4459,c_5214,c_7188,c_21756,c_21976])).

cnf(c_23276,plain,
    ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_22473,c_22473,c_22938])).

cnf(c_8,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_23283,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_23276,c_8])).

cnf(c_1420,plain,
    ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k4_xboole_0(sK5,sK4))) ),
    inference(superposition,[status(thm)],[c_1286,c_8])).

cnf(c_1421,plain,
    ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_1420,c_8])).

cnf(c_1476,plain,
    ( k4_xboole_0(k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_1421,c_9])).

cnf(c_1534,plain,
    ( k4_xboole_0(k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK4)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_11,c_1476])).

cnf(c_948,plain,
    ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK5) = k4_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_22,c_9])).

cnf(c_1228,plain,
    ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k4_xboole_0(sK4,sK5))) ),
    inference(superposition,[status(thm)],[c_948,c_8])).

cnf(c_1229,plain,
    ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_1228,c_8,c_1048])).

cnf(c_1422,plain,
    ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k4_xboole_0(sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_1229,c_9])).

cnf(c_1538,plain,
    ( k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k4_xboole_0(sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_1534,c_1048,c_1422])).

cnf(c_1845,plain,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k4_xboole_0(sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) ),
    inference(superposition,[status(thm)],[c_1538,c_8])).

cnf(c_1847,plain,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) = k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK5)) ),
    inference(demodulation,[status(thm)],[c_1845,c_8])).

cnf(c_2067,plain,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK5)) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(superposition,[status(thm)],[c_11,c_1847])).

cnf(c_2077,plain,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK5)) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_2067,c_1421])).

cnf(c_2841,plain,
    ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_11,c_2077])).

cnf(c_2852,plain,
    ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(light_normalisation,[status(thm)],[c_2841,c_1229])).

cnf(c_2860,plain,
    ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_2852,c_1421])).

cnf(c_22453,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_22379,c_2860])).

cnf(c_23303,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(light_normalisation,[status(thm)],[c_23283,c_22453])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_548,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_547,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3088,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_548,c_547])).

cnf(c_1056,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_9,c_8])).

cnf(c_1059,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(demodulation,[status(thm)],[c_1056,c_8])).

cnf(c_4417,plain,
    ( k4_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) = k4_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_1059,c_9])).

cnf(c_4688,plain,
    ( k4_xboole_0(k3_tarski(k3_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X1)),k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) = k4_xboole_0(k4_xboole_0(X0,X1),k3_tarski(k3_enumset1(X1,X1,X1,X1,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_8,c_4417])).

cnf(c_4404,plain,
    ( k3_tarski(k3_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))) = k3_tarski(k3_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X1)) ),
    inference(superposition,[status(thm)],[c_8,c_1059])).

cnf(c_1053,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_546])).

cnf(c_1573,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1053])).

cnf(c_3094,plain,
    ( k3_tarski(k3_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_1573,c_547])).

cnf(c_4431,plain,
    ( k3_tarski(k3_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_4404,c_3094])).

cnf(c_4726,plain,
    ( k4_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k4_xboole_0(k4_xboole_0(X1,X0),k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X1,X0)))) ),
    inference(light_normalisation,[status(thm)],[c_4688,c_4431])).

cnf(c_1052,plain,
    ( k4_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_11,c_9])).

cnf(c_1724,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1052,c_8])).

cnf(c_1725,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_1724,c_8])).

cnf(c_4641,plain,
    ( k4_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k4_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_1725,c_9])).

cnf(c_4727,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) = k4_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) ),
    inference(demodulation,[status(thm)],[c_4726,c_8,c_4641])).

cnf(c_4772,plain,
    ( k3_tarski(k3_enumset1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k4_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))))) = k3_tarski(k3_enumset1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_4727,c_8])).

cnf(c_4643,plain,
    ( k3_tarski(k3_enumset1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) = k3_tarski(k3_enumset1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X0)) ),
    inference(superposition,[status(thm)],[c_1725,c_1059])).

cnf(c_4650,plain,
    ( k3_tarski(k3_enumset1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X0)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(demodulation,[status(thm)],[c_4643,c_3088])).

cnf(c_4782,plain,
    ( k3_tarski(k3_enumset1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k4_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(demodulation,[status(thm)],[c_4772,c_8,c_4650])).

cnf(c_8817,plain,
    ( k3_tarski(k3_enumset1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k4_xboole_0(X0,X1))) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_11,c_4782])).

cnf(c_10845,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X0,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(superposition,[status(thm)],[c_3088,c_8817])).

cnf(c_10877,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X0,X0))) = X0 ),
    inference(demodulation,[status(thm)],[c_10845,c_3088])).

cnf(c_23304,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_23303,c_10877])).

cnf(c_22479,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != k1_xboole_0
    | sK5 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_22379,c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23304,c_22479,c_22379,c_22171,c_7188,c_5214,c_4459,c_3665,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.63/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.63/1.50  
% 7.63/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.63/1.50  
% 7.63/1.50  ------  iProver source info
% 7.63/1.50  
% 7.63/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.63/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.63/1.50  git: non_committed_changes: false
% 7.63/1.50  git: last_make_outside_of_git: false
% 7.63/1.50  
% 7.63/1.50  ------ 
% 7.63/1.50  
% 7.63/1.50  ------ Input Options
% 7.63/1.50  
% 7.63/1.50  --out_options                           all
% 7.63/1.50  --tptp_safe_out                         true
% 7.63/1.50  --problem_path                          ""
% 7.63/1.50  --include_path                          ""
% 7.63/1.50  --clausifier                            res/vclausify_rel
% 7.63/1.50  --clausifier_options                    ""
% 7.63/1.50  --stdin                                 false
% 7.63/1.50  --stats_out                             all
% 7.63/1.50  
% 7.63/1.50  ------ General Options
% 7.63/1.50  
% 7.63/1.50  --fof                                   false
% 7.63/1.50  --time_out_real                         305.
% 7.63/1.50  --time_out_virtual                      -1.
% 7.63/1.50  --symbol_type_check                     false
% 7.63/1.50  --clausify_out                          false
% 7.63/1.50  --sig_cnt_out                           false
% 7.63/1.50  --trig_cnt_out                          false
% 7.63/1.50  --trig_cnt_out_tolerance                1.
% 7.63/1.50  --trig_cnt_out_sk_spl                   false
% 7.63/1.50  --abstr_cl_out                          false
% 7.63/1.50  
% 7.63/1.50  ------ Global Options
% 7.63/1.50  
% 7.63/1.50  --schedule                              default
% 7.63/1.50  --add_important_lit                     false
% 7.63/1.50  --prop_solver_per_cl                    1000
% 7.63/1.50  --min_unsat_core                        false
% 7.63/1.50  --soft_assumptions                      false
% 7.63/1.50  --soft_lemma_size                       3
% 7.63/1.50  --prop_impl_unit_size                   0
% 7.63/1.50  --prop_impl_unit                        []
% 7.63/1.50  --share_sel_clauses                     true
% 7.63/1.50  --reset_solvers                         false
% 7.63/1.50  --bc_imp_inh                            [conj_cone]
% 7.63/1.50  --conj_cone_tolerance                   3.
% 7.63/1.50  --extra_neg_conj                        none
% 7.63/1.50  --large_theory_mode                     true
% 7.63/1.50  --prolific_symb_bound                   200
% 7.63/1.50  --lt_threshold                          2000
% 7.63/1.50  --clause_weak_htbl                      true
% 7.63/1.50  --gc_record_bc_elim                     false
% 7.63/1.50  
% 7.63/1.50  ------ Preprocessing Options
% 7.63/1.50  
% 7.63/1.50  --preprocessing_flag                    true
% 7.63/1.50  --time_out_prep_mult                    0.1
% 7.63/1.50  --splitting_mode                        input
% 7.63/1.50  --splitting_grd                         true
% 7.63/1.50  --splitting_cvd                         false
% 7.63/1.50  --splitting_cvd_svl                     false
% 7.63/1.50  --splitting_nvd                         32
% 7.63/1.50  --sub_typing                            true
% 7.63/1.50  --prep_gs_sim                           true
% 7.63/1.50  --prep_unflatten                        true
% 7.63/1.50  --prep_res_sim                          true
% 7.63/1.50  --prep_upred                            true
% 7.63/1.50  --prep_sem_filter                       exhaustive
% 7.63/1.50  --prep_sem_filter_out                   false
% 7.63/1.50  --pred_elim                             true
% 7.63/1.50  --res_sim_input                         true
% 7.63/1.50  --eq_ax_congr_red                       true
% 7.63/1.50  --pure_diseq_elim                       true
% 7.63/1.50  --brand_transform                       false
% 7.63/1.50  --non_eq_to_eq                          false
% 7.63/1.50  --prep_def_merge                        true
% 7.63/1.50  --prep_def_merge_prop_impl              false
% 7.63/1.50  --prep_def_merge_mbd                    true
% 7.63/1.50  --prep_def_merge_tr_red                 false
% 7.63/1.50  --prep_def_merge_tr_cl                  false
% 7.63/1.50  --smt_preprocessing                     true
% 7.63/1.50  --smt_ac_axioms                         fast
% 7.63/1.50  --preprocessed_out                      false
% 7.63/1.50  --preprocessed_stats                    false
% 7.63/1.50  
% 7.63/1.50  ------ Abstraction refinement Options
% 7.63/1.50  
% 7.63/1.50  --abstr_ref                             []
% 7.63/1.50  --abstr_ref_prep                        false
% 7.63/1.50  --abstr_ref_until_sat                   false
% 7.63/1.50  --abstr_ref_sig_restrict                funpre
% 7.63/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.63/1.50  --abstr_ref_under                       []
% 7.63/1.50  
% 7.63/1.50  ------ SAT Options
% 7.63/1.50  
% 7.63/1.50  --sat_mode                              false
% 7.63/1.50  --sat_fm_restart_options                ""
% 7.63/1.50  --sat_gr_def                            false
% 7.63/1.50  --sat_epr_types                         true
% 7.63/1.50  --sat_non_cyclic_types                  false
% 7.63/1.50  --sat_finite_models                     false
% 7.63/1.50  --sat_fm_lemmas                         false
% 7.63/1.50  --sat_fm_prep                           false
% 7.63/1.50  --sat_fm_uc_incr                        true
% 7.63/1.50  --sat_out_model                         small
% 7.63/1.50  --sat_out_clauses                       false
% 7.63/1.50  
% 7.63/1.50  ------ QBF Options
% 7.63/1.50  
% 7.63/1.50  --qbf_mode                              false
% 7.63/1.50  --qbf_elim_univ                         false
% 7.63/1.50  --qbf_dom_inst                          none
% 7.63/1.50  --qbf_dom_pre_inst                      false
% 7.63/1.50  --qbf_sk_in                             false
% 7.63/1.50  --qbf_pred_elim                         true
% 7.63/1.50  --qbf_split                             512
% 7.63/1.50  
% 7.63/1.50  ------ BMC1 Options
% 7.63/1.50  
% 7.63/1.50  --bmc1_incremental                      false
% 7.63/1.50  --bmc1_axioms                           reachable_all
% 7.63/1.50  --bmc1_min_bound                        0
% 7.63/1.50  --bmc1_max_bound                        -1
% 7.63/1.50  --bmc1_max_bound_default                -1
% 7.63/1.50  --bmc1_symbol_reachability              true
% 7.63/1.50  --bmc1_property_lemmas                  false
% 7.63/1.50  --bmc1_k_induction                      false
% 7.63/1.50  --bmc1_non_equiv_states                 false
% 7.63/1.50  --bmc1_deadlock                         false
% 7.63/1.50  --bmc1_ucm                              false
% 7.63/1.50  --bmc1_add_unsat_core                   none
% 7.63/1.50  --bmc1_unsat_core_children              false
% 7.63/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.63/1.50  --bmc1_out_stat                         full
% 7.63/1.50  --bmc1_ground_init                      false
% 7.63/1.50  --bmc1_pre_inst_next_state              false
% 7.63/1.50  --bmc1_pre_inst_state                   false
% 7.63/1.50  --bmc1_pre_inst_reach_state             false
% 7.63/1.50  --bmc1_out_unsat_core                   false
% 7.63/1.50  --bmc1_aig_witness_out                  false
% 7.63/1.50  --bmc1_verbose                          false
% 7.63/1.50  --bmc1_dump_clauses_tptp                false
% 7.63/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.63/1.50  --bmc1_dump_file                        -
% 7.63/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.63/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.63/1.50  --bmc1_ucm_extend_mode                  1
% 7.63/1.50  --bmc1_ucm_init_mode                    2
% 7.63/1.50  --bmc1_ucm_cone_mode                    none
% 7.63/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.63/1.50  --bmc1_ucm_relax_model                  4
% 7.63/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.63/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.63/1.50  --bmc1_ucm_layered_model                none
% 7.63/1.50  --bmc1_ucm_max_lemma_size               10
% 7.63/1.50  
% 7.63/1.50  ------ AIG Options
% 7.63/1.50  
% 7.63/1.50  --aig_mode                              false
% 7.63/1.50  
% 7.63/1.50  ------ Instantiation Options
% 7.63/1.50  
% 7.63/1.50  --instantiation_flag                    true
% 7.63/1.50  --inst_sos_flag                         true
% 7.63/1.50  --inst_sos_phase                        true
% 7.63/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.63/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.63/1.50  --inst_lit_sel_side                     num_symb
% 7.63/1.50  --inst_solver_per_active                1400
% 7.63/1.50  --inst_solver_calls_frac                1.
% 7.63/1.50  --inst_passive_queue_type               priority_queues
% 7.63/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.63/1.50  --inst_passive_queues_freq              [25;2]
% 7.63/1.50  --inst_dismatching                      true
% 7.63/1.50  --inst_eager_unprocessed_to_passive     true
% 7.63/1.50  --inst_prop_sim_given                   true
% 7.63/1.50  --inst_prop_sim_new                     false
% 7.63/1.50  --inst_subs_new                         false
% 7.63/1.50  --inst_eq_res_simp                      false
% 7.63/1.50  --inst_subs_given                       false
% 7.63/1.50  --inst_orphan_elimination               true
% 7.63/1.50  --inst_learning_loop_flag               true
% 7.63/1.50  --inst_learning_start                   3000
% 7.63/1.50  --inst_learning_factor                  2
% 7.63/1.50  --inst_start_prop_sim_after_learn       3
% 7.63/1.50  --inst_sel_renew                        solver
% 7.63/1.50  --inst_lit_activity_flag                true
% 7.63/1.50  --inst_restr_to_given                   false
% 7.63/1.50  --inst_activity_threshold               500
% 7.63/1.50  --inst_out_proof                        true
% 7.63/1.50  
% 7.63/1.50  ------ Resolution Options
% 7.63/1.50  
% 7.63/1.50  --resolution_flag                       true
% 7.63/1.50  --res_lit_sel                           adaptive
% 7.63/1.50  --res_lit_sel_side                      none
% 7.63/1.50  --res_ordering                          kbo
% 7.63/1.50  --res_to_prop_solver                    active
% 7.63/1.50  --res_prop_simpl_new                    false
% 7.63/1.50  --res_prop_simpl_given                  true
% 7.63/1.50  --res_passive_queue_type                priority_queues
% 7.63/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.63/1.50  --res_passive_queues_freq               [15;5]
% 7.63/1.50  --res_forward_subs                      full
% 7.63/1.50  --res_backward_subs                     full
% 7.63/1.50  --res_forward_subs_resolution           true
% 7.63/1.50  --res_backward_subs_resolution          true
% 7.63/1.50  --res_orphan_elimination                true
% 7.63/1.50  --res_time_limit                        2.
% 7.63/1.50  --res_out_proof                         true
% 7.63/1.50  
% 7.63/1.50  ------ Superposition Options
% 7.63/1.50  
% 7.63/1.50  --superposition_flag                    true
% 7.63/1.50  --sup_passive_queue_type                priority_queues
% 7.63/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.63/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.63/1.50  --demod_completeness_check              fast
% 7.63/1.50  --demod_use_ground                      true
% 7.63/1.50  --sup_to_prop_solver                    passive
% 7.63/1.50  --sup_prop_simpl_new                    true
% 7.63/1.50  --sup_prop_simpl_given                  true
% 7.63/1.50  --sup_fun_splitting                     true
% 7.63/1.50  --sup_smt_interval                      50000
% 7.63/1.50  
% 7.63/1.50  ------ Superposition Simplification Setup
% 7.63/1.50  
% 7.63/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.63/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.63/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.63/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.63/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.63/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.63/1.50  --sup_immed_triv                        [TrivRules]
% 7.63/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.63/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.63/1.50  --sup_immed_bw_main                     []
% 7.63/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.63/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.63/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.63/1.50  --sup_input_bw                          []
% 7.63/1.50  
% 7.63/1.50  ------ Combination Options
% 7.63/1.50  
% 7.63/1.50  --comb_res_mult                         3
% 7.63/1.50  --comb_sup_mult                         2
% 7.63/1.50  --comb_inst_mult                        10
% 7.63/1.50  
% 7.63/1.50  ------ Debug Options
% 7.63/1.50  
% 7.63/1.50  --dbg_backtrace                         false
% 7.63/1.50  --dbg_dump_prop_clauses                 false
% 7.63/1.50  --dbg_dump_prop_clauses_file            -
% 7.63/1.50  --dbg_out_stat                          false
% 7.63/1.50  ------ Parsing...
% 7.63/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.63/1.50  
% 7.63/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.63/1.50  
% 7.63/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.63/1.50  
% 7.63/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.63/1.50  ------ Proving...
% 7.63/1.50  ------ Problem Properties 
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  clauses                                 22
% 7.63/1.50  conjectures                             4
% 7.63/1.50  EPR                                     3
% 7.63/1.50  Horn                                    19
% 7.63/1.50  unary                                   7
% 7.63/1.50  binary                                  10
% 7.63/1.50  lits                                    42
% 7.63/1.50  lits eq                                 18
% 7.63/1.50  fd_pure                                 0
% 7.63/1.50  fd_pseudo                               0
% 7.63/1.50  fd_cond                                 1
% 7.63/1.50  fd_pseudo_cond                          3
% 7.63/1.50  AC symbols                              0
% 7.63/1.50  
% 7.63/1.50  ------ Schedule dynamic 5 is on 
% 7.63/1.50  
% 7.63/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  ------ 
% 7.63/1.50  Current options:
% 7.63/1.50  ------ 
% 7.63/1.50  
% 7.63/1.50  ------ Input Options
% 7.63/1.50  
% 7.63/1.50  --out_options                           all
% 7.63/1.50  --tptp_safe_out                         true
% 7.63/1.50  --problem_path                          ""
% 7.63/1.50  --include_path                          ""
% 7.63/1.50  --clausifier                            res/vclausify_rel
% 7.63/1.50  --clausifier_options                    ""
% 7.63/1.50  --stdin                                 false
% 7.63/1.50  --stats_out                             all
% 7.63/1.50  
% 7.63/1.50  ------ General Options
% 7.63/1.50  
% 7.63/1.50  --fof                                   false
% 7.63/1.50  --time_out_real                         305.
% 7.63/1.50  --time_out_virtual                      -1.
% 7.63/1.50  --symbol_type_check                     false
% 7.63/1.50  --clausify_out                          false
% 7.63/1.50  --sig_cnt_out                           false
% 7.63/1.50  --trig_cnt_out                          false
% 7.63/1.50  --trig_cnt_out_tolerance                1.
% 7.63/1.50  --trig_cnt_out_sk_spl                   false
% 7.63/1.50  --abstr_cl_out                          false
% 7.63/1.50  
% 7.63/1.50  ------ Global Options
% 7.63/1.50  
% 7.63/1.50  --schedule                              default
% 7.63/1.50  --add_important_lit                     false
% 7.63/1.50  --prop_solver_per_cl                    1000
% 7.63/1.50  --min_unsat_core                        false
% 7.63/1.50  --soft_assumptions                      false
% 7.63/1.50  --soft_lemma_size                       3
% 7.63/1.50  --prop_impl_unit_size                   0
% 7.63/1.50  --prop_impl_unit                        []
% 7.63/1.50  --share_sel_clauses                     true
% 7.63/1.50  --reset_solvers                         false
% 7.63/1.50  --bc_imp_inh                            [conj_cone]
% 7.63/1.50  --conj_cone_tolerance                   3.
% 7.63/1.50  --extra_neg_conj                        none
% 7.63/1.50  --large_theory_mode                     true
% 7.63/1.50  --prolific_symb_bound                   200
% 7.63/1.50  --lt_threshold                          2000
% 7.63/1.50  --clause_weak_htbl                      true
% 7.63/1.50  --gc_record_bc_elim                     false
% 7.63/1.50  
% 7.63/1.50  ------ Preprocessing Options
% 7.63/1.50  
% 7.63/1.50  --preprocessing_flag                    true
% 7.63/1.50  --time_out_prep_mult                    0.1
% 7.63/1.50  --splitting_mode                        input
% 7.63/1.50  --splitting_grd                         true
% 7.63/1.50  --splitting_cvd                         false
% 7.63/1.50  --splitting_cvd_svl                     false
% 7.63/1.50  --splitting_nvd                         32
% 7.63/1.50  --sub_typing                            true
% 7.63/1.50  --prep_gs_sim                           true
% 7.63/1.50  --prep_unflatten                        true
% 7.63/1.50  --prep_res_sim                          true
% 7.63/1.50  --prep_upred                            true
% 7.63/1.50  --prep_sem_filter                       exhaustive
% 7.63/1.50  --prep_sem_filter_out                   false
% 7.63/1.50  --pred_elim                             true
% 7.63/1.50  --res_sim_input                         true
% 7.63/1.50  --eq_ax_congr_red                       true
% 7.63/1.50  --pure_diseq_elim                       true
% 7.63/1.50  --brand_transform                       false
% 7.63/1.50  --non_eq_to_eq                          false
% 7.63/1.50  --prep_def_merge                        true
% 7.63/1.50  --prep_def_merge_prop_impl              false
% 7.63/1.50  --prep_def_merge_mbd                    true
% 7.63/1.50  --prep_def_merge_tr_red                 false
% 7.63/1.50  --prep_def_merge_tr_cl                  false
% 7.63/1.50  --smt_preprocessing                     true
% 7.63/1.50  --smt_ac_axioms                         fast
% 7.63/1.50  --preprocessed_out                      false
% 7.63/1.50  --preprocessed_stats                    false
% 7.63/1.50  
% 7.63/1.50  ------ Abstraction refinement Options
% 7.63/1.50  
% 7.63/1.50  --abstr_ref                             []
% 7.63/1.50  --abstr_ref_prep                        false
% 7.63/1.50  --abstr_ref_until_sat                   false
% 7.63/1.50  --abstr_ref_sig_restrict                funpre
% 7.63/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.63/1.50  --abstr_ref_under                       []
% 7.63/1.50  
% 7.63/1.50  ------ SAT Options
% 7.63/1.50  
% 7.63/1.50  --sat_mode                              false
% 7.63/1.50  --sat_fm_restart_options                ""
% 7.63/1.50  --sat_gr_def                            false
% 7.63/1.50  --sat_epr_types                         true
% 7.63/1.50  --sat_non_cyclic_types                  false
% 7.63/1.50  --sat_finite_models                     false
% 7.63/1.50  --sat_fm_lemmas                         false
% 7.63/1.50  --sat_fm_prep                           false
% 7.63/1.50  --sat_fm_uc_incr                        true
% 7.63/1.50  --sat_out_model                         small
% 7.63/1.50  --sat_out_clauses                       false
% 7.63/1.50  
% 7.63/1.50  ------ QBF Options
% 7.63/1.50  
% 7.63/1.50  --qbf_mode                              false
% 7.63/1.50  --qbf_elim_univ                         false
% 7.63/1.50  --qbf_dom_inst                          none
% 7.63/1.50  --qbf_dom_pre_inst                      false
% 7.63/1.50  --qbf_sk_in                             false
% 7.63/1.50  --qbf_pred_elim                         true
% 7.63/1.50  --qbf_split                             512
% 7.63/1.50  
% 7.63/1.50  ------ BMC1 Options
% 7.63/1.50  
% 7.63/1.50  --bmc1_incremental                      false
% 7.63/1.50  --bmc1_axioms                           reachable_all
% 7.63/1.50  --bmc1_min_bound                        0
% 7.63/1.50  --bmc1_max_bound                        -1
% 7.63/1.50  --bmc1_max_bound_default                -1
% 7.63/1.50  --bmc1_symbol_reachability              true
% 7.63/1.50  --bmc1_property_lemmas                  false
% 7.63/1.50  --bmc1_k_induction                      false
% 7.63/1.50  --bmc1_non_equiv_states                 false
% 7.63/1.50  --bmc1_deadlock                         false
% 7.63/1.50  --bmc1_ucm                              false
% 7.63/1.50  --bmc1_add_unsat_core                   none
% 7.63/1.50  --bmc1_unsat_core_children              false
% 7.63/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.63/1.50  --bmc1_out_stat                         full
% 7.63/1.50  --bmc1_ground_init                      false
% 7.63/1.50  --bmc1_pre_inst_next_state              false
% 7.63/1.50  --bmc1_pre_inst_state                   false
% 7.63/1.50  --bmc1_pre_inst_reach_state             false
% 7.63/1.50  --bmc1_out_unsat_core                   false
% 7.63/1.50  --bmc1_aig_witness_out                  false
% 7.63/1.50  --bmc1_verbose                          false
% 7.63/1.50  --bmc1_dump_clauses_tptp                false
% 7.63/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.63/1.50  --bmc1_dump_file                        -
% 7.63/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.63/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.63/1.50  --bmc1_ucm_extend_mode                  1
% 7.63/1.50  --bmc1_ucm_init_mode                    2
% 7.63/1.50  --bmc1_ucm_cone_mode                    none
% 7.63/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.63/1.50  --bmc1_ucm_relax_model                  4
% 7.63/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.63/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.63/1.50  --bmc1_ucm_layered_model                none
% 7.63/1.50  --bmc1_ucm_max_lemma_size               10
% 7.63/1.50  
% 7.63/1.50  ------ AIG Options
% 7.63/1.50  
% 7.63/1.50  --aig_mode                              false
% 7.63/1.50  
% 7.63/1.50  ------ Instantiation Options
% 7.63/1.50  
% 7.63/1.50  --instantiation_flag                    true
% 7.63/1.50  --inst_sos_flag                         true
% 7.63/1.50  --inst_sos_phase                        true
% 7.63/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.63/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.63/1.50  --inst_lit_sel_side                     none
% 7.63/1.50  --inst_solver_per_active                1400
% 7.63/1.50  --inst_solver_calls_frac                1.
% 7.63/1.50  --inst_passive_queue_type               priority_queues
% 7.63/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.63/1.50  --inst_passive_queues_freq              [25;2]
% 7.63/1.50  --inst_dismatching                      true
% 7.63/1.50  --inst_eager_unprocessed_to_passive     true
% 7.63/1.50  --inst_prop_sim_given                   true
% 7.63/1.50  --inst_prop_sim_new                     false
% 7.63/1.50  --inst_subs_new                         false
% 7.63/1.50  --inst_eq_res_simp                      false
% 7.63/1.50  --inst_subs_given                       false
% 7.63/1.50  --inst_orphan_elimination               true
% 7.63/1.50  --inst_learning_loop_flag               true
% 7.63/1.50  --inst_learning_start                   3000
% 7.63/1.50  --inst_learning_factor                  2
% 7.63/1.50  --inst_start_prop_sim_after_learn       3
% 7.63/1.50  --inst_sel_renew                        solver
% 7.63/1.50  --inst_lit_activity_flag                true
% 7.63/1.50  --inst_restr_to_given                   false
% 7.63/1.50  --inst_activity_threshold               500
% 7.63/1.50  --inst_out_proof                        true
% 7.63/1.50  
% 7.63/1.50  ------ Resolution Options
% 7.63/1.50  
% 7.63/1.50  --resolution_flag                       false
% 7.63/1.50  --res_lit_sel                           adaptive
% 7.63/1.50  --res_lit_sel_side                      none
% 7.63/1.50  --res_ordering                          kbo
% 7.63/1.50  --res_to_prop_solver                    active
% 7.63/1.50  --res_prop_simpl_new                    false
% 7.63/1.50  --res_prop_simpl_given                  true
% 7.63/1.50  --res_passive_queue_type                priority_queues
% 7.63/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.63/1.50  --res_passive_queues_freq               [15;5]
% 7.63/1.50  --res_forward_subs                      full
% 7.63/1.50  --res_backward_subs                     full
% 7.63/1.50  --res_forward_subs_resolution           true
% 7.63/1.50  --res_backward_subs_resolution          true
% 7.63/1.50  --res_orphan_elimination                true
% 7.63/1.50  --res_time_limit                        2.
% 7.63/1.50  --res_out_proof                         true
% 7.63/1.50  
% 7.63/1.50  ------ Superposition Options
% 7.63/1.50  
% 7.63/1.50  --superposition_flag                    true
% 7.63/1.50  --sup_passive_queue_type                priority_queues
% 7.63/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.63/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.63/1.50  --demod_completeness_check              fast
% 7.63/1.50  --demod_use_ground                      true
% 7.63/1.50  --sup_to_prop_solver                    passive
% 7.63/1.50  --sup_prop_simpl_new                    true
% 7.63/1.50  --sup_prop_simpl_given                  true
% 7.63/1.50  --sup_fun_splitting                     true
% 7.63/1.50  --sup_smt_interval                      50000
% 7.63/1.50  
% 7.63/1.50  ------ Superposition Simplification Setup
% 7.63/1.50  
% 7.63/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.63/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.63/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.63/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.63/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.63/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.63/1.50  --sup_immed_triv                        [TrivRules]
% 7.63/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.63/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.63/1.50  --sup_immed_bw_main                     []
% 7.63/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.63/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.63/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.63/1.50  --sup_input_bw                          []
% 7.63/1.50  
% 7.63/1.50  ------ Combination Options
% 7.63/1.50  
% 7.63/1.50  --comb_res_mult                         3
% 7.63/1.50  --comb_sup_mult                         2
% 7.63/1.50  --comb_inst_mult                        10
% 7.63/1.50  
% 7.63/1.50  ------ Debug Options
% 7.63/1.50  
% 7.63/1.50  --dbg_backtrace                         false
% 7.63/1.50  --dbg_dump_prop_clauses                 false
% 7.63/1.50  --dbg_dump_prop_clauses_file            -
% 7.63/1.50  --dbg_out_stat                          false
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  ------ Proving...
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  % SZS status Theorem for theBenchmark.p
% 7.63/1.50  
% 7.63/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.63/1.50  
% 7.63/1.50  fof(f17,conjecture,(
% 7.63/1.50    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f18,negated_conjecture,(
% 7.63/1.50    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 7.63/1.50    inference(negated_conjecture,[],[f17])).
% 7.63/1.50  
% 7.63/1.50  fof(f22,plain,(
% 7.63/1.50    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 7.63/1.50    inference(ennf_transformation,[],[f18])).
% 7.63/1.50  
% 7.63/1.50  fof(f37,plain,(
% 7.63/1.50    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4) & (k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4) & (k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4) & k2_xboole_0(sK4,sK5) = k1_tarski(sK3))),
% 7.63/1.50    introduced(choice_axiom,[])).
% 7.63/1.50  
% 7.63/1.50  fof(f38,plain,(
% 7.63/1.50    (k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4) & (k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4) & (k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4) & k2_xboole_0(sK4,sK5) = k1_tarski(sK3)),
% 7.63/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f37])).
% 7.63/1.50  
% 7.63/1.50  fof(f63,plain,(
% 7.63/1.50    k2_xboole_0(sK4,sK5) = k1_tarski(sK3)),
% 7.63/1.50    inference(cnf_transformation,[],[f38])).
% 7.63/1.50  
% 7.63/1.50  fof(f15,axiom,(
% 7.63/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f59,plain,(
% 7.63/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.63/1.50    inference(cnf_transformation,[],[f15])).
% 7.63/1.50  
% 7.63/1.50  fof(f69,plain,(
% 7.63/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 7.63/1.50    inference(definition_unfolding,[],[f59,f68])).
% 7.63/1.50  
% 7.63/1.50  fof(f11,axiom,(
% 7.63/1.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f55,plain,(
% 7.63/1.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f11])).
% 7.63/1.50  
% 7.63/1.50  fof(f12,axiom,(
% 7.63/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f56,plain,(
% 7.63/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f12])).
% 7.63/1.50  
% 7.63/1.50  fof(f13,axiom,(
% 7.63/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f57,plain,(
% 7.63/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f13])).
% 7.63/1.50  
% 7.63/1.50  fof(f14,axiom,(
% 7.63/1.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f58,plain,(
% 7.63/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f14])).
% 7.63/1.50  
% 7.63/1.50  fof(f67,plain,(
% 7.63/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 7.63/1.50    inference(definition_unfolding,[],[f57,f58])).
% 7.63/1.50  
% 7.63/1.50  fof(f68,plain,(
% 7.63/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 7.63/1.50    inference(definition_unfolding,[],[f56,f67])).
% 7.63/1.50  
% 7.63/1.50  fof(f70,plain,(
% 7.63/1.50    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 7.63/1.50    inference(definition_unfolding,[],[f55,f68])).
% 7.63/1.50  
% 7.63/1.50  fof(f86,plain,(
% 7.63/1.50    k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5))),
% 7.63/1.50    inference(definition_unfolding,[],[f63,f69,f70])).
% 7.63/1.50  
% 7.63/1.50  fof(f8,axiom,(
% 7.63/1.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f49,plain,(
% 7.63/1.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.63/1.50    inference(cnf_transformation,[],[f8])).
% 7.63/1.50  
% 7.63/1.50  fof(f74,plain,(
% 7.63/1.50    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 7.63/1.50    inference(definition_unfolding,[],[f49,f69])).
% 7.63/1.50  
% 7.63/1.50  fof(f3,axiom,(
% 7.63/1.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f20,plain,(
% 7.63/1.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 7.63/1.50    inference(ennf_transformation,[],[f3])).
% 7.63/1.50  
% 7.63/1.50  fof(f27,plain,(
% 7.63/1.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 7.63/1.50    introduced(choice_axiom,[])).
% 7.63/1.50  
% 7.63/1.50  fof(f28,plain,(
% 7.63/1.50    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 7.63/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f27])).
% 7.63/1.50  
% 7.63/1.50  fof(f42,plain,(
% 7.63/1.50    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 7.63/1.50    inference(cnf_transformation,[],[f28])).
% 7.63/1.50  
% 7.63/1.50  fof(f2,axiom,(
% 7.63/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f19,plain,(
% 7.63/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.63/1.50    inference(ennf_transformation,[],[f2])).
% 7.63/1.50  
% 7.63/1.50  fof(f23,plain,(
% 7.63/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.63/1.50    inference(nnf_transformation,[],[f19])).
% 7.63/1.50  
% 7.63/1.50  fof(f24,plain,(
% 7.63/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.63/1.50    inference(rectify,[],[f23])).
% 7.63/1.50  
% 7.63/1.50  fof(f25,plain,(
% 7.63/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.63/1.50    introduced(choice_axiom,[])).
% 7.63/1.50  
% 7.63/1.50  fof(f26,plain,(
% 7.63/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.63/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 7.63/1.50  
% 7.63/1.50  fof(f39,plain,(
% 7.63/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f26])).
% 7.63/1.50  
% 7.63/1.50  fof(f10,axiom,(
% 7.63/1.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f31,plain,(
% 7.63/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.63/1.50    inference(nnf_transformation,[],[f10])).
% 7.63/1.50  
% 7.63/1.50  fof(f32,plain,(
% 7.63/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.63/1.50    inference(rectify,[],[f31])).
% 7.63/1.50  
% 7.63/1.50  fof(f33,plain,(
% 7.63/1.50    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 7.63/1.50    introduced(choice_axiom,[])).
% 7.63/1.50  
% 7.63/1.50  fof(f34,plain,(
% 7.63/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.63/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 7.63/1.50  
% 7.63/1.50  fof(f51,plain,(
% 7.63/1.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.63/1.50    inference(cnf_transformation,[],[f34])).
% 7.63/1.50  
% 7.63/1.50  fof(f79,plain,(
% 7.63/1.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 7.63/1.50    inference(definition_unfolding,[],[f51,f70])).
% 7.63/1.50  
% 7.63/1.50  fof(f91,plain,(
% 7.63/1.50    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 7.63/1.50    inference(equality_resolution,[],[f79])).
% 7.63/1.50  
% 7.63/1.50  fof(f64,plain,(
% 7.63/1.50    k1_tarski(sK3) != sK5 | k1_tarski(sK3) != sK4),
% 7.63/1.50    inference(cnf_transformation,[],[f38])).
% 7.63/1.50  
% 7.63/1.50  fof(f85,plain,(
% 7.63/1.50    k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4),
% 7.63/1.50    inference(definition_unfolding,[],[f64,f70,f70])).
% 7.63/1.50  
% 7.63/1.50  fof(f66,plain,(
% 7.63/1.50    k1_xboole_0 != sK5 | k1_tarski(sK3) != sK4),
% 7.63/1.50    inference(cnf_transformation,[],[f38])).
% 7.63/1.50  
% 7.63/1.50  fof(f83,plain,(
% 7.63/1.50    k1_xboole_0 != sK5 | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4),
% 7.63/1.50    inference(definition_unfolding,[],[f66,f70])).
% 7.63/1.50  
% 7.63/1.50  fof(f16,axiom,(
% 7.63/1.50    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f35,plain,(
% 7.63/1.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.63/1.50    inference(nnf_transformation,[],[f16])).
% 7.63/1.50  
% 7.63/1.50  fof(f36,plain,(
% 7.63/1.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.63/1.50    inference(flattening,[],[f35])).
% 7.63/1.50  
% 7.63/1.50  fof(f62,plain,(
% 7.63/1.50    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f36])).
% 7.63/1.50  
% 7.63/1.50  fof(f80,plain,(
% 7.63/1.50    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 7.63/1.50    inference(definition_unfolding,[],[f62,f68])).
% 7.63/1.50  
% 7.63/1.50  fof(f9,axiom,(
% 7.63/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f50,plain,(
% 7.63/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f9])).
% 7.63/1.50  
% 7.63/1.50  fof(f75,plain,(
% 7.63/1.50    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 7.63/1.50    inference(definition_unfolding,[],[f50,f68,f68])).
% 7.63/1.50  
% 7.63/1.50  fof(f4,axiom,(
% 7.63/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f29,plain,(
% 7.63/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.63/1.50    inference(nnf_transformation,[],[f4])).
% 7.63/1.50  
% 7.63/1.50  fof(f30,plain,(
% 7.63/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.63/1.50    inference(flattening,[],[f29])).
% 7.63/1.50  
% 7.63/1.50  fof(f45,plain,(
% 7.63/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f30])).
% 7.63/1.50  
% 7.63/1.50  fof(f52,plain,(
% 7.63/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.63/1.50    inference(cnf_transformation,[],[f34])).
% 7.63/1.50  
% 7.63/1.50  fof(f78,plain,(
% 7.63/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 7.63/1.50    inference(definition_unfolding,[],[f52,f70])).
% 7.63/1.50  
% 7.63/1.50  fof(f89,plain,(
% 7.63/1.50    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 7.63/1.50    inference(equality_resolution,[],[f78])).
% 7.63/1.50  
% 7.63/1.50  fof(f90,plain,(
% 7.63/1.50    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 7.63/1.50    inference(equality_resolution,[],[f89])).
% 7.63/1.50  
% 7.63/1.50  fof(f7,axiom,(
% 7.63/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f48,plain,(
% 7.63/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f7])).
% 7.63/1.50  
% 7.63/1.50  fof(f73,plain,(
% 7.63/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) )),
% 7.63/1.50    inference(definition_unfolding,[],[f48,f69])).
% 7.63/1.50  
% 7.63/1.50  fof(f65,plain,(
% 7.63/1.50    k1_tarski(sK3) != sK5 | k1_xboole_0 != sK4),
% 7.63/1.50    inference(cnf_transformation,[],[f38])).
% 7.63/1.50  
% 7.63/1.50  fof(f84,plain,(
% 7.63/1.50    k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 | k1_xboole_0 != sK4),
% 7.63/1.50    inference(definition_unfolding,[],[f65,f70])).
% 7.63/1.50  
% 7.63/1.50  fof(f6,axiom,(
% 7.63/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f47,plain,(
% 7.63/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.63/1.50    inference(cnf_transformation,[],[f6])).
% 7.63/1.50  
% 7.63/1.50  fof(f72,plain,(
% 7.63/1.50    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X1,X0)))) )),
% 7.63/1.50    inference(definition_unfolding,[],[f47,f69,f69])).
% 7.63/1.50  
% 7.63/1.50  fof(f43,plain,(
% 7.63/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.63/1.50    inference(cnf_transformation,[],[f30])).
% 7.63/1.50  
% 7.63/1.50  fof(f88,plain,(
% 7.63/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.63/1.50    inference(equality_resolution,[],[f43])).
% 7.63/1.50  
% 7.63/1.50  fof(f5,axiom,(
% 7.63/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f21,plain,(
% 7.63/1.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.63/1.50    inference(ennf_transformation,[],[f5])).
% 7.63/1.50  
% 7.63/1.50  fof(f46,plain,(
% 7.63/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f21])).
% 7.63/1.50  
% 7.63/1.50  fof(f71,plain,(
% 7.63/1.50    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 7.63/1.50    inference(definition_unfolding,[],[f46,f69])).
% 7.63/1.50  
% 7.63/1.50  cnf(c_22,negated_conjecture,
% 7.63/1.50      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
% 7.63/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_10,plain,
% 7.63/1.50      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
% 7.63/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_546,plain,
% 7.63/1.50      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_873,plain,
% 7.63/1.50      ( r1_tarski(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_22,c_546]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3,plain,
% 7.63/1.50      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 7.63/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_550,plain,
% 7.63/1.50      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2,plain,
% 7.63/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.63/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_551,plain,
% 7.63/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.63/1.50      | r2_hidden(X0,X2) = iProver_top
% 7.63/1.50      | r1_tarski(X1,X2) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4239,plain,
% 7.63/1.50      ( k1_xboole_0 = X0
% 7.63/1.50      | r2_hidden(sK1(X0),X1) = iProver_top
% 7.63/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_550,c_551]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_15,plain,
% 7.63/1.50      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1 ),
% 7.63/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_542,plain,
% 7.63/1.50      ( X0 = X1
% 7.63/1.50      | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_12251,plain,
% 7.63/1.50      ( sK1(X0) = X1
% 7.63/1.50      | k1_xboole_0 = X0
% 7.63/1.50      | r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_4239,c_542]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_21799,plain,
% 7.63/1.50      ( sK1(sK4) = sK3 | sK4 = k1_xboole_0 ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_873,c_12251]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_21967,plain,
% 7.63/1.50      ( sK4 = k1_xboole_0
% 7.63/1.50      | r2_hidden(sK3,X0) = iProver_top
% 7.63/1.50      | r1_tarski(sK4,X0) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_21799,c_4239]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_21,negated_conjecture,
% 7.63/1.50      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4
% 7.63/1.50      | k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 ),
% 7.63/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_19,negated_conjecture,
% 7.63/1.50      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK4 | k1_xboole_0 != sK5 ),
% 7.63/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_16,plain,
% 7.63/1.50      ( ~ r2_hidden(X0,X1)
% 7.63/1.50      | ~ r2_hidden(X2,X1)
% 7.63/1.50      | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) ),
% 7.63/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_541,plain,
% 7.63/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.63/1.50      | r2_hidden(X2,X1) != iProver_top
% 7.63/1.50      | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_11,plain,
% 7.63/1.50      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1048,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK4)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_11,c_22]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1287,plain,
% 7.63/1.50      ( r1_tarski(sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_1048,c_546]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4,plain,
% 7.63/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.63/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_549,plain,
% 7.63/1.50      ( X0 = X1
% 7.63/1.50      | r1_tarski(X1,X0) != iProver_top
% 7.63/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3251,plain,
% 7.63/1.50      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK5
% 7.63/1.50      | r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK5) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_1287,c_549]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3665,plain,
% 7.63/1.50      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK5
% 7.63/1.50      | r2_hidden(sK3,sK5) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_541,c_3251]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_14,plain,
% 7.63/1.50      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
% 7.63/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_5214,plain,
% 7.63/1.50      ( r2_hidden(k1_xboole_0,k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2435,plain,
% 7.63/1.50      ( ~ r2_hidden(k1_xboole_0,k3_enumset1(X0,X0,X0,X0,X0))
% 7.63/1.50      | k1_xboole_0 = X0 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_15]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_7188,plain,
% 7.63/1.50      ( ~ r2_hidden(k1_xboole_0,k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 7.63/1.50      | k1_xboole_0 = k1_xboole_0 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_2435]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_294,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_578,plain,
% 7.63/1.50      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_294]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_21756,plain,
% 7.63/1.50      ( sK5 != k1_xboole_0
% 7.63/1.50      | k1_xboole_0 = sK5
% 7.63/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_578]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_21968,plain,
% 7.63/1.50      ( sK4 = k1_xboole_0 | r2_hidden(sK3,sK4) = iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_21799,c_550]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3250,plain,
% 7.63/1.50      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4
% 7.63/1.50      | r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_873,c_549]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3417,plain,
% 7.63/1.50      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4
% 7.63/1.50      | r2_hidden(sK3,sK4) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_541,c_3250]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_21976,plain,
% 7.63/1.50      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = sK4 | sK4 = k1_xboole_0 ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_21968,c_3417]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_21800,plain,
% 7.63/1.50      ( sK1(sK5) = sK3 | sK5 = k1_xboole_0 ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_1287,c_12251]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_22171,plain,
% 7.63/1.50      ( sK5 = k1_xboole_0 | r2_hidden(sK3,sK5) = iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_21800,c_550]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_22379,plain,
% 7.63/1.50      ( sK4 = k1_xboole_0 ),
% 7.63/1.50      inference(global_propositional_subsumption,
% 7.63/1.50                [status(thm)],
% 7.63/1.50                [c_21967,c_21,c_19,c_3665,c_5214,c_7188,c_21756,c_21976,
% 7.63/1.50                 c_22171]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_9,plain,
% 7.63/1.50      ( k4_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1) = k4_xboole_0(X0,X1) ),
% 7.63/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1286,plain,
% 7.63/1.50      ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) = k4_xboole_0(sK5,sK4) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_1048,c_9]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_22473,plain,
% 7.63/1.50      ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k1_xboole_0) = k4_xboole_0(sK5,k1_xboole_0) ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_22379,c_1286]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_20,negated_conjecture,
% 7.63/1.50      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != sK5 | k1_xboole_0 != sK4 ),
% 7.63/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_589,plain,
% 7.63/1.50      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_294]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4459,plain,
% 7.63/1.50      ( sK4 != k1_xboole_0
% 7.63/1.50      | k1_xboole_0 = sK4
% 7.63/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_589]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_22938,plain,
% 7.63/1.50      ( sK5 = k1_xboole_0 ),
% 7.63/1.50      inference(global_propositional_subsumption,
% 7.63/1.50                [status(thm)],
% 7.63/1.50                [c_22171,c_21,c_20,c_19,c_3665,c_4459,c_5214,c_7188,
% 7.63/1.50                 c_21756,c_21976]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_23276,plain,
% 7.63/1.50      ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 7.63/1.50      inference(light_normalisation,
% 7.63/1.50                [status(thm)],
% 7.63/1.50                [c_22473,c_22473,c_22938]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_8,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 7.63/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_23283,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_23276,c_8]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1420,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k4_xboole_0(sK5,sK4))) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_1286,c_8]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1421,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_1420,c_8]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1476,plain,
% 7.63/1.50      ( k4_xboole_0(k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_1421,c_9]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1534,plain,
% 7.63/1.50      ( k4_xboole_0(k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK4)),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_11,c_1476]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_948,plain,
% 7.63/1.50      ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK5) = k4_xboole_0(sK4,sK5) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_22,c_9]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1228,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k4_xboole_0(sK4,sK5))) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_948,c_8]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1229,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_1228,c_8,c_1048]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1422,plain,
% 7.63/1.50      ( k4_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k4_xboole_0(sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_1229,c_9]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1538,plain,
% 7.63/1.50      ( k4_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) = k4_xboole_0(sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
% 7.63/1.50      inference(light_normalisation,[status(thm)],[c_1534,c_1048,c_1422]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1845,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k4_xboole_0(sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_1538,c_8]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1847,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)) = k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK5)) ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_1845,c_8]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2067,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK5)) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_11,c_1847]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2077,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK5)) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
% 7.63/1.50      inference(light_normalisation,[status(thm)],[c_2067,c_1421]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2841,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_11,c_2077]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2852,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK5)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 7.63/1.50      inference(light_normalisation,[status(thm)],[c_2841,c_1229]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2860,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_2852,c_1421]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_22453,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_22379,c_2860]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_23303,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 7.63/1.50      inference(light_normalisation,[status(thm)],[c_23283,c_22453]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_6,plain,
% 7.63/1.50      ( r1_tarski(X0,X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_548,plain,
% 7.63/1.50      ( r1_tarski(X0,X0) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_7,plain,
% 7.63/1.50      ( ~ r1_tarski(X0,X1)
% 7.63/1.50      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 ),
% 7.63/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_547,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1
% 7.63/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3088,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_548,c_547]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1056,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X1,X0))) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_9,c_8]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1059,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_1056,c_8]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4417,plain,
% 7.63/1.50      ( k4_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) = k4_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_1059,c_9]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4688,plain,
% 7.63/1.50      ( k4_xboole_0(k3_tarski(k3_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X1)),k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) = k4_xboole_0(k4_xboole_0(X0,X1),k3_tarski(k3_enumset1(X1,X1,X1,X1,k4_xboole_0(X0,X1)))) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_8,c_4417]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4404,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))) = k3_tarski(k3_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X1)) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_8,c_1059]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1053,plain,
% 7.63/1.50      ( r1_tarski(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) = iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_11,c_546]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1573,plain,
% 7.63/1.50      ( r1_tarski(k4_xboole_0(X0,X1),k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) = iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_8,c_1053]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3094,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_1573,c_547]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4431,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
% 7.63/1.50      inference(light_normalisation,[status(thm)],[c_4404,c_3094]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4726,plain,
% 7.63/1.50      ( k4_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k4_xboole_0(k4_xboole_0(X1,X0),k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X1,X0)))) ),
% 7.63/1.50      inference(light_normalisation,[status(thm)],[c_4688,c_4431]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1052,plain,
% 7.63/1.50      ( k4_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X0) = k4_xboole_0(X1,X0) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_11,c_9]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1724,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X1,X0))) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_1052,c_8]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1725,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 7.63/1.50      inference(light_normalisation,[status(thm)],[c_1724,c_8]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4641,plain,
% 7.63/1.50      ( k4_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k4_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_1725,c_9]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4727,plain,
% 7.63/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) = k4_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_4726,c_8,c_4641]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4772,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k4_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))))) = k3_tarski(k3_enumset1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k4_xboole_0(X1,X0))) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_4727,c_8]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4643,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) = k3_tarski(k3_enumset1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X0)) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_1725,c_1059]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4650,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X0)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_4643,c_3088]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4782,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k4_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_4772,c_8,c_4650]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_8817,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k4_xboole_0(X0,X1))) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_11,c_4782]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_10845,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X0,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_3088,c_8817]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_10877,plain,
% 7.63/1.50      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X0,X0))) = X0 ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_10845,c_3088]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_23304,plain,
% 7.63/1.50      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_xboole_0 ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_23303,c_10877]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_22479,plain,
% 7.63/1.50      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != k1_xboole_0
% 7.63/1.50      | sK5 != k1_xboole_0 ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_22379,c_19]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(contradiction,plain,
% 7.63/1.50      ( $false ),
% 7.63/1.50      inference(minisat,
% 7.63/1.50                [status(thm)],
% 7.63/1.50                [c_23304,c_22479,c_22379,c_22171,c_7188,c_5214,c_4459,
% 7.63/1.50                 c_3665,c_20]) ).
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.63/1.50  
% 7.63/1.50  ------                               Statistics
% 7.63/1.50  
% 7.63/1.50  ------ General
% 7.63/1.50  
% 7.63/1.50  abstr_ref_over_cycles:                  0
% 7.63/1.50  abstr_ref_under_cycles:                 0
% 7.63/1.50  gc_basic_clause_elim:                   0
% 7.63/1.50  forced_gc_time:                         0
% 7.63/1.50  parsing_time:                           0.011
% 7.63/1.50  unif_index_cands_time:                  0.
% 7.63/1.50  unif_index_add_time:                    0.
% 7.63/1.50  orderings_time:                         0.
% 7.63/1.50  out_proof_time:                         0.012
% 7.63/1.50  total_time:                             0.686
% 7.63/1.50  num_of_symbols:                         43
% 7.63/1.50  num_of_terms:                           18771
% 7.63/1.50  
% 7.63/1.50  ------ Preprocessing
% 7.63/1.50  
% 7.63/1.50  num_of_splits:                          0
% 7.63/1.50  num_of_split_atoms:                     0
% 7.63/1.50  num_of_reused_defs:                     0
% 7.63/1.50  num_eq_ax_congr_red:                    18
% 7.63/1.50  num_of_sem_filtered_clauses:            1
% 7.63/1.50  num_of_subtypes:                        0
% 7.63/1.50  monotx_restored_types:                  0
% 7.63/1.50  sat_num_of_epr_types:                   0
% 7.63/1.50  sat_num_of_non_cyclic_types:            0
% 7.63/1.50  sat_guarded_non_collapsed_types:        0
% 7.63/1.50  num_pure_diseq_elim:                    0
% 7.63/1.50  simp_replaced_by:                       0
% 7.63/1.50  res_preprocessed:                       103
% 7.63/1.50  prep_upred:                             0
% 7.63/1.50  prep_unflattend:                        0
% 7.63/1.50  smt_new_axioms:                         0
% 7.63/1.50  pred_elim_cands:                        2
% 7.63/1.50  pred_elim:                              0
% 7.63/1.50  pred_elim_cl:                           0
% 7.63/1.50  pred_elim_cycles:                       2
% 7.63/1.50  merged_defs:                            0
% 7.63/1.50  merged_defs_ncl:                        0
% 7.63/1.50  bin_hyper_res:                          0
% 7.63/1.50  prep_cycles:                            4
% 7.63/1.50  pred_elim_time:                         0.
% 7.63/1.50  splitting_time:                         0.
% 7.63/1.50  sem_filter_time:                        0.
% 7.63/1.50  monotx_time:                            0.
% 7.63/1.50  subtype_inf_time:                       0.
% 7.63/1.50  
% 7.63/1.50  ------ Problem properties
% 7.63/1.50  
% 7.63/1.50  clauses:                                22
% 7.63/1.50  conjectures:                            4
% 7.63/1.50  epr:                                    3
% 7.63/1.50  horn:                                   19
% 7.63/1.50  ground:                                 4
% 7.63/1.50  unary:                                  7
% 7.63/1.50  binary:                                 10
% 7.63/1.50  lits:                                   42
% 7.63/1.50  lits_eq:                                18
% 7.63/1.50  fd_pure:                                0
% 7.63/1.50  fd_pseudo:                              0
% 7.63/1.50  fd_cond:                                1
% 7.63/1.50  fd_pseudo_cond:                         3
% 7.63/1.50  ac_symbols:                             0
% 7.63/1.50  
% 7.63/1.50  ------ Propositional Solver
% 7.63/1.50  
% 7.63/1.50  prop_solver_calls:                      31
% 7.63/1.50  prop_fast_solver_calls:                 838
% 7.63/1.50  smt_solver_calls:                       0
% 7.63/1.50  smt_fast_solver_calls:                  0
% 7.63/1.50  prop_num_of_clauses:                    7829
% 7.63/1.50  prop_preprocess_simplified:             17313
% 7.63/1.50  prop_fo_subsumed:                       4
% 7.63/1.50  prop_solver_time:                       0.
% 7.63/1.50  smt_solver_time:                        0.
% 7.63/1.50  smt_fast_solver_time:                   0.
% 7.63/1.50  prop_fast_solver_time:                  0.
% 7.63/1.50  prop_unsat_core_time:                   0.
% 7.63/1.50  
% 7.63/1.50  ------ QBF
% 7.63/1.50  
% 7.63/1.50  qbf_q_res:                              0
% 7.63/1.50  qbf_num_tautologies:                    0
% 7.63/1.50  qbf_prep_cycles:                        0
% 7.63/1.50  
% 7.63/1.50  ------ BMC1
% 7.63/1.50  
% 7.63/1.50  bmc1_current_bound:                     -1
% 7.63/1.50  bmc1_last_solved_bound:                 -1
% 7.63/1.50  bmc1_unsat_core_size:                   -1
% 7.63/1.50  bmc1_unsat_core_parents_size:           -1
% 7.63/1.50  bmc1_merge_next_fun:                    0
% 7.63/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.63/1.50  
% 7.63/1.50  ------ Instantiation
% 7.63/1.50  
% 7.63/1.50  inst_num_of_clauses:                    2149
% 7.63/1.50  inst_num_in_passive:                    1284
% 7.63/1.50  inst_num_in_active:                     691
% 7.63/1.50  inst_num_in_unprocessed:                175
% 7.63/1.50  inst_num_of_loops:                      1120
% 7.63/1.50  inst_num_of_learning_restarts:          0
% 7.63/1.50  inst_num_moves_active_passive:          428
% 7.63/1.50  inst_lit_activity:                      0
% 7.63/1.50  inst_lit_activity_moves:                0
% 7.63/1.50  inst_num_tautologies:                   0
% 7.63/1.50  inst_num_prop_implied:                  0
% 7.63/1.50  inst_num_existing_simplified:           0
% 7.63/1.50  inst_num_eq_res_simplified:             0
% 7.63/1.50  inst_num_child_elim:                    0
% 7.63/1.50  inst_num_of_dismatching_blockings:      1885
% 7.63/1.50  inst_num_of_non_proper_insts:           3080
% 7.63/1.50  inst_num_of_duplicates:                 0
% 7.63/1.50  inst_inst_num_from_inst_to_res:         0
% 7.63/1.50  inst_dismatching_checking_time:         0.
% 7.63/1.50  
% 7.63/1.50  ------ Resolution
% 7.63/1.50  
% 7.63/1.50  res_num_of_clauses:                     0
% 7.63/1.50  res_num_in_passive:                     0
% 7.63/1.50  res_num_in_active:                      0
% 7.63/1.50  res_num_of_loops:                       107
% 7.63/1.50  res_forward_subset_subsumed:            124
% 7.63/1.50  res_backward_subset_subsumed:           8
% 7.63/1.50  res_forward_subsumed:                   0
% 7.63/1.50  res_backward_subsumed:                  0
% 7.63/1.50  res_forward_subsumption_resolution:     0
% 7.63/1.50  res_backward_subsumption_resolution:    0
% 7.63/1.50  res_clause_to_clause_subsumption:       6202
% 7.63/1.50  res_orphan_elimination:                 0
% 7.63/1.50  res_tautology_del:                      117
% 7.63/1.50  res_num_eq_res_simplified:              0
% 7.63/1.50  res_num_sel_changes:                    0
% 7.63/1.50  res_moves_from_active_to_pass:          0
% 7.63/1.50  
% 7.63/1.50  ------ Superposition
% 7.63/1.50  
% 7.63/1.50  sup_time_total:                         0.
% 7.63/1.50  sup_time_generating:                    0.
% 7.63/1.50  sup_time_sim_full:                      0.
% 7.63/1.50  sup_time_sim_immed:                     0.
% 7.63/1.50  
% 7.63/1.50  sup_num_of_clauses:                     713
% 7.63/1.50  sup_num_in_active:                      77
% 7.63/1.50  sup_num_in_passive:                     636
% 7.63/1.50  sup_num_of_loops:                       223
% 7.63/1.50  sup_fw_superposition:                   1744
% 7.63/1.50  sup_bw_superposition:                   2623
% 7.63/1.50  sup_immediate_simplified:               1787
% 7.63/1.50  sup_given_eliminated:                   4
% 7.63/1.50  comparisons_done:                       0
% 7.63/1.50  comparisons_avoided:                    55
% 7.63/1.50  
% 7.63/1.50  ------ Simplifications
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  sim_fw_subset_subsumed:                 21
% 7.63/1.50  sim_bw_subset_subsumed:                 7
% 7.63/1.50  sim_fw_subsumed:                        123
% 7.63/1.50  sim_bw_subsumed:                        7
% 7.63/1.50  sim_fw_subsumption_res:                 0
% 7.63/1.50  sim_bw_subsumption_res:                 0
% 7.63/1.50  sim_tautology_del:                      3
% 7.63/1.50  sim_eq_tautology_del:                   498
% 7.63/1.50  sim_eq_res_simp:                        7
% 7.63/1.50  sim_fw_demodulated:                     597
% 7.63/1.50  sim_bw_demodulated:                     176
% 7.63/1.50  sim_light_normalised:                   1243
% 7.63/1.50  sim_joinable_taut:                      0
% 7.63/1.50  sim_joinable_simp:                      0
% 7.63/1.50  sim_ac_normalised:                      0
% 7.63/1.50  sim_smt_subsumption:                    0
% 7.63/1.50  
%------------------------------------------------------------------------------
