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
% DateTime   : Thu Dec  3 11:31:31 EST 2020

% Result     : Theorem 7.88s
% Output     : CNFRefutation 7.88s
% Verified   : 
% Statistics : Number of formulae       :  127 (1673 expanded)
%              Number of clauses        :   58 ( 313 expanded)
%              Number of leaves         :   18 ( 451 expanded)
%              Depth                    :   28
%              Number of atoms          :  400 (5913 expanded)
%              Number of equality atoms :  296 (4436 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f86,plain,(
    ! [X0,X1] : r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f62,f56,f67])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK2 != sK5
      & sK2 != sK4
      & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( sK2 != sK5
    & sK2 != sK4
    & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f34])).

fof(f64,plain,(
    r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f88,plain,(
    r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
    inference(definition_unfolding,[],[f64,f67,f67])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = X0
      | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) = X0
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f57,f67,f56,f56,f67])).

fof(f65,plain,(
    sK2 != sK4 ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    sK2 != sK5 ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f48,f67])).

fof(f98,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f49,f67])).

fof(f96,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k5_enumset1(X4,X4,X4,X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f79])).

fof(f97,plain,(
    ! [X4,X1] : r2_hidden(X4,k5_enumset1(X4,X4,X4,X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f96])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f44,f56])).

fof(f93,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
      | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f60,f67,f56])).

fof(f100,plain,(
    ! [X2,X1] : r1_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f82])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f43,f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f87,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) != k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f63,f56,f56,f56])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_22,plain,
    ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1637,plain,
    ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1634,plain,
    ( r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
    | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = X0
    | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) = X0
    | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1635,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X1
    | k5_enumset1(X0,X0,X0,X0,X0,X0,X2) = X1
    | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2038,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1634,c_1635])).

cnf(c_2449,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = X0
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2038,c_1635])).

cnf(c_2761,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1637,c_2449])).

cnf(c_25,negated_conjecture,
    ( sK2 != sK4 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_24,negated_conjecture,
    ( sK2 != sK5 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_42,plain,
    ( ~ r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_15,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_45,plain,
    ( r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1164,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1799,plain,
    ( sK5 != X0
    | sK2 != X0
    | sK2 = sK5 ),
    inference(instantiation,[status(thm)],[c_1164])).

cnf(c_1800,plain,
    ( sK5 != sK2
    | sK2 = sK5
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1799])).

cnf(c_1801,plain,
    ( sK4 != X0
    | sK2 != X0
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_1164])).

cnf(c_1802,plain,
    ( sK4 != sK2
    | sK2 = sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1801])).

cnf(c_1641,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2757,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
    | r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2038,c_1637])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1646,plain,
    ( X0 = X1
    | r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2977,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
    | sK4 = X0
    | r2_hidden(X0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2038,c_1646])).

cnf(c_3349,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
    | sK4 = sK2 ),
    inference(superposition,[status(thm)],[c_1641,c_2977])).

cnf(c_3368,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
    | k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2757,c_25,c_42,c_45,c_1802,c_3349])).

cnf(c_3369,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3368])).

cnf(c_1640,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3910,plain,
    ( k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
    | sK4 = X0
    | sK5 = X0
    | r2_hidden(X0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3369,c_1640])).

cnf(c_4341,plain,
    ( k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
    | sK4 = sK2
    | sK5 = sK2 ),
    inference(superposition,[status(thm)],[c_1641,c_3910])).

cnf(c_4414,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
    | k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2761,c_25,c_24,c_42,c_45,c_1800,c_1802,c_4341])).

cnf(c_4415,plain,
    ( k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4414])).

cnf(c_18,plain,
    ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1638,plain,
    ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4418,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
    | r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(X0,X0,X0,X0,X0,X0,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4415,c_1638])).

cnf(c_4428,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
    | sK5 = X0
    | r2_hidden(X0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4415,c_1640])).

cnf(c_4585,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
    | sK5 = sK2 ),
    inference(superposition,[status(thm)],[c_1641,c_4428])).

cnf(c_4605,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4418,c_24,c_42,c_45,c_1800,c_4585])).

cnf(c_4623,plain,
    ( r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4605,c_1637])).

cnf(c_6,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1651,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2298,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1651])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1654,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3267,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2298,c_1654])).

cnf(c_5824,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4623,c_3267])).

cnf(c_23,plain,
    ( X0 = X1
    | k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) != k5_enumset1(X1,X1,X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_6196,plain,
    ( k3_xboole_0(k1_xboole_0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK2 = X0 ),
    inference(superposition,[status(thm)],[c_5824,c_23])).

cnf(c_6209,plain,
    ( k3_xboole_0(k1_xboole_0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) != k1_xboole_0
    | sK2 = X0 ),
    inference(light_normalisation,[status(thm)],[c_6196,c_5824])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1650,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2398,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2298,c_1650])).

cnf(c_6212,plain,
    ( sK2 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6209,c_2398])).

cnf(c_6213,plain,
    ( sK2 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6212])).

cnf(c_29102,plain,
    ( sK2 != sK2 ),
    inference(demodulation,[status(thm)],[c_6213,c_25])).

cnf(c_29143,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_29102])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.88/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.88/1.50  
% 7.88/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.88/1.50  
% 7.88/1.50  ------  iProver source info
% 7.88/1.50  
% 7.88/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.88/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.88/1.50  git: non_committed_changes: false
% 7.88/1.50  git: last_make_outside_of_git: false
% 7.88/1.50  
% 7.88/1.50  ------ 
% 7.88/1.50  
% 7.88/1.50  ------ Input Options
% 7.88/1.50  
% 7.88/1.50  --out_options                           all
% 7.88/1.50  --tptp_safe_out                         true
% 7.88/1.50  --problem_path                          ""
% 7.88/1.50  --include_path                          ""
% 7.88/1.50  --clausifier                            res/vclausify_rel
% 7.88/1.50  --clausifier_options                    --mode clausify
% 7.88/1.50  --stdin                                 false
% 7.88/1.50  --stats_out                             all
% 7.88/1.50  
% 7.88/1.50  ------ General Options
% 7.88/1.50  
% 7.88/1.50  --fof                                   false
% 7.88/1.50  --time_out_real                         305.
% 7.88/1.50  --time_out_virtual                      -1.
% 7.88/1.50  --symbol_type_check                     false
% 7.88/1.50  --clausify_out                          false
% 7.88/1.50  --sig_cnt_out                           false
% 7.88/1.50  --trig_cnt_out                          false
% 7.88/1.50  --trig_cnt_out_tolerance                1.
% 7.88/1.50  --trig_cnt_out_sk_spl                   false
% 7.88/1.50  --abstr_cl_out                          false
% 7.88/1.50  
% 7.88/1.50  ------ Global Options
% 7.88/1.50  
% 7.88/1.50  --schedule                              default
% 7.88/1.50  --add_important_lit                     false
% 7.88/1.50  --prop_solver_per_cl                    1000
% 7.88/1.50  --min_unsat_core                        false
% 7.88/1.50  --soft_assumptions                      false
% 7.88/1.50  --soft_lemma_size                       3
% 7.88/1.50  --prop_impl_unit_size                   0
% 7.88/1.50  --prop_impl_unit                        []
% 7.88/1.50  --share_sel_clauses                     true
% 7.88/1.50  --reset_solvers                         false
% 7.88/1.50  --bc_imp_inh                            [conj_cone]
% 7.88/1.50  --conj_cone_tolerance                   3.
% 7.88/1.50  --extra_neg_conj                        none
% 7.88/1.50  --large_theory_mode                     true
% 7.88/1.50  --prolific_symb_bound                   200
% 7.88/1.50  --lt_threshold                          2000
% 7.88/1.50  --clause_weak_htbl                      true
% 7.88/1.50  --gc_record_bc_elim                     false
% 7.88/1.50  
% 7.88/1.50  ------ Preprocessing Options
% 7.88/1.50  
% 7.88/1.50  --preprocessing_flag                    true
% 7.88/1.50  --time_out_prep_mult                    0.1
% 7.88/1.50  --splitting_mode                        input
% 7.88/1.50  --splitting_grd                         true
% 7.88/1.50  --splitting_cvd                         false
% 7.88/1.50  --splitting_cvd_svl                     false
% 7.88/1.50  --splitting_nvd                         32
% 7.88/1.50  --sub_typing                            true
% 7.88/1.50  --prep_gs_sim                           true
% 7.88/1.50  --prep_unflatten                        true
% 7.88/1.50  --prep_res_sim                          true
% 7.88/1.50  --prep_upred                            true
% 7.88/1.50  --prep_sem_filter                       exhaustive
% 7.88/1.50  --prep_sem_filter_out                   false
% 7.88/1.50  --pred_elim                             true
% 7.88/1.50  --res_sim_input                         true
% 7.88/1.50  --eq_ax_congr_red                       true
% 7.88/1.50  --pure_diseq_elim                       true
% 7.88/1.50  --brand_transform                       false
% 7.88/1.50  --non_eq_to_eq                          false
% 7.88/1.50  --prep_def_merge                        true
% 7.88/1.50  --prep_def_merge_prop_impl              false
% 7.88/1.50  --prep_def_merge_mbd                    true
% 7.88/1.50  --prep_def_merge_tr_red                 false
% 7.88/1.50  --prep_def_merge_tr_cl                  false
% 7.88/1.50  --smt_preprocessing                     true
% 7.88/1.50  --smt_ac_axioms                         fast
% 7.88/1.50  --preprocessed_out                      false
% 7.88/1.50  --preprocessed_stats                    false
% 7.88/1.50  
% 7.88/1.50  ------ Abstraction refinement Options
% 7.88/1.50  
% 7.88/1.50  --abstr_ref                             []
% 7.88/1.50  --abstr_ref_prep                        false
% 7.88/1.50  --abstr_ref_until_sat                   false
% 7.88/1.50  --abstr_ref_sig_restrict                funpre
% 7.88/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.88/1.50  --abstr_ref_under                       []
% 7.88/1.50  
% 7.88/1.50  ------ SAT Options
% 7.88/1.50  
% 7.88/1.50  --sat_mode                              false
% 7.88/1.50  --sat_fm_restart_options                ""
% 7.88/1.50  --sat_gr_def                            false
% 7.88/1.50  --sat_epr_types                         true
% 7.88/1.50  --sat_non_cyclic_types                  false
% 7.88/1.50  --sat_finite_models                     false
% 7.88/1.50  --sat_fm_lemmas                         false
% 7.88/1.50  --sat_fm_prep                           false
% 7.88/1.50  --sat_fm_uc_incr                        true
% 7.88/1.50  --sat_out_model                         small
% 7.88/1.50  --sat_out_clauses                       false
% 7.88/1.50  
% 7.88/1.50  ------ QBF Options
% 7.88/1.50  
% 7.88/1.50  --qbf_mode                              false
% 7.88/1.50  --qbf_elim_univ                         false
% 7.88/1.50  --qbf_dom_inst                          none
% 7.88/1.50  --qbf_dom_pre_inst                      false
% 7.88/1.50  --qbf_sk_in                             false
% 7.88/1.50  --qbf_pred_elim                         true
% 7.88/1.50  --qbf_split                             512
% 7.88/1.50  
% 7.88/1.50  ------ BMC1 Options
% 7.88/1.50  
% 7.88/1.50  --bmc1_incremental                      false
% 7.88/1.50  --bmc1_axioms                           reachable_all
% 7.88/1.50  --bmc1_min_bound                        0
% 7.88/1.50  --bmc1_max_bound                        -1
% 7.88/1.50  --bmc1_max_bound_default                -1
% 7.88/1.50  --bmc1_symbol_reachability              true
% 7.88/1.50  --bmc1_property_lemmas                  false
% 7.88/1.50  --bmc1_k_induction                      false
% 7.88/1.50  --bmc1_non_equiv_states                 false
% 7.88/1.50  --bmc1_deadlock                         false
% 7.88/1.50  --bmc1_ucm                              false
% 7.88/1.50  --bmc1_add_unsat_core                   none
% 7.88/1.50  --bmc1_unsat_core_children              false
% 7.88/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.88/1.50  --bmc1_out_stat                         full
% 7.88/1.50  --bmc1_ground_init                      false
% 7.88/1.50  --bmc1_pre_inst_next_state              false
% 7.88/1.50  --bmc1_pre_inst_state                   false
% 7.88/1.50  --bmc1_pre_inst_reach_state             false
% 7.88/1.50  --bmc1_out_unsat_core                   false
% 7.88/1.50  --bmc1_aig_witness_out                  false
% 7.88/1.50  --bmc1_verbose                          false
% 7.88/1.50  --bmc1_dump_clauses_tptp                false
% 7.88/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.88/1.50  --bmc1_dump_file                        -
% 7.88/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.88/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.88/1.50  --bmc1_ucm_extend_mode                  1
% 7.88/1.50  --bmc1_ucm_init_mode                    2
% 7.88/1.50  --bmc1_ucm_cone_mode                    none
% 7.88/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.88/1.50  --bmc1_ucm_relax_model                  4
% 7.88/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.88/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.88/1.50  --bmc1_ucm_layered_model                none
% 7.88/1.50  --bmc1_ucm_max_lemma_size               10
% 7.88/1.50  
% 7.88/1.50  ------ AIG Options
% 7.88/1.50  
% 7.88/1.50  --aig_mode                              false
% 7.88/1.50  
% 7.88/1.50  ------ Instantiation Options
% 7.88/1.50  
% 7.88/1.50  --instantiation_flag                    true
% 7.88/1.50  --inst_sos_flag                         false
% 7.88/1.50  --inst_sos_phase                        true
% 7.88/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.88/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.88/1.50  --inst_lit_sel_side                     num_symb
% 7.88/1.50  --inst_solver_per_active                1400
% 7.88/1.50  --inst_solver_calls_frac                1.
% 7.88/1.50  --inst_passive_queue_type               priority_queues
% 7.88/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.88/1.50  --inst_passive_queues_freq              [25;2]
% 7.88/1.50  --inst_dismatching                      true
% 7.88/1.50  --inst_eager_unprocessed_to_passive     true
% 7.88/1.50  --inst_prop_sim_given                   true
% 7.88/1.50  --inst_prop_sim_new                     false
% 7.88/1.50  --inst_subs_new                         false
% 7.88/1.50  --inst_eq_res_simp                      false
% 7.88/1.50  --inst_subs_given                       false
% 7.88/1.50  --inst_orphan_elimination               true
% 7.88/1.50  --inst_learning_loop_flag               true
% 7.88/1.50  --inst_learning_start                   3000
% 7.88/1.50  --inst_learning_factor                  2
% 7.88/1.50  --inst_start_prop_sim_after_learn       3
% 7.88/1.50  --inst_sel_renew                        solver
% 7.88/1.50  --inst_lit_activity_flag                true
% 7.88/1.50  --inst_restr_to_given                   false
% 7.88/1.50  --inst_activity_threshold               500
% 7.88/1.50  --inst_out_proof                        true
% 7.88/1.50  
% 7.88/1.50  ------ Resolution Options
% 7.88/1.50  
% 7.88/1.50  --resolution_flag                       true
% 7.88/1.50  --res_lit_sel                           adaptive
% 7.88/1.50  --res_lit_sel_side                      none
% 7.88/1.50  --res_ordering                          kbo
% 7.88/1.50  --res_to_prop_solver                    active
% 7.88/1.50  --res_prop_simpl_new                    false
% 7.88/1.50  --res_prop_simpl_given                  true
% 7.88/1.50  --res_passive_queue_type                priority_queues
% 7.88/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.88/1.50  --res_passive_queues_freq               [15;5]
% 7.88/1.50  --res_forward_subs                      full
% 7.88/1.50  --res_backward_subs                     full
% 7.88/1.50  --res_forward_subs_resolution           true
% 7.88/1.50  --res_backward_subs_resolution          true
% 7.88/1.50  --res_orphan_elimination                true
% 7.88/1.50  --res_time_limit                        2.
% 7.88/1.50  --res_out_proof                         true
% 7.88/1.50  
% 7.88/1.50  ------ Superposition Options
% 7.88/1.50  
% 7.88/1.50  --superposition_flag                    true
% 7.88/1.50  --sup_passive_queue_type                priority_queues
% 7.88/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.88/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.88/1.50  --demod_completeness_check              fast
% 7.88/1.50  --demod_use_ground                      true
% 7.88/1.50  --sup_to_prop_solver                    passive
% 7.88/1.50  --sup_prop_simpl_new                    true
% 7.88/1.50  --sup_prop_simpl_given                  true
% 7.88/1.50  --sup_fun_splitting                     false
% 7.88/1.50  --sup_smt_interval                      50000
% 7.88/1.50  
% 7.88/1.50  ------ Superposition Simplification Setup
% 7.88/1.50  
% 7.88/1.50  --sup_indices_passive                   []
% 7.88/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.88/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.50  --sup_full_bw                           [BwDemod]
% 7.88/1.50  --sup_immed_triv                        [TrivRules]
% 7.88/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.50  --sup_immed_bw_main                     []
% 7.88/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.88/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.88/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.88/1.50  
% 7.88/1.50  ------ Combination Options
% 7.88/1.50  
% 7.88/1.50  --comb_res_mult                         3
% 7.88/1.50  --comb_sup_mult                         2
% 7.88/1.50  --comb_inst_mult                        10
% 7.88/1.50  
% 7.88/1.50  ------ Debug Options
% 7.88/1.50  
% 7.88/1.50  --dbg_backtrace                         false
% 7.88/1.50  --dbg_dump_prop_clauses                 false
% 7.88/1.50  --dbg_dump_prop_clauses_file            -
% 7.88/1.50  --dbg_out_stat                          false
% 7.88/1.50  ------ Parsing...
% 7.88/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.88/1.50  
% 7.88/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.88/1.50  
% 7.88/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.88/1.50  
% 7.88/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.88/1.50  ------ Proving...
% 7.88/1.50  ------ Problem Properties 
% 7.88/1.50  
% 7.88/1.50  
% 7.88/1.50  clauses                                 25
% 7.88/1.50  conjectures                             3
% 7.88/1.50  EPR                                     4
% 7.88/1.50  Horn                                    21
% 7.88/1.50  unary                                   12
% 7.88/1.50  binary                                  5
% 7.88/1.50  lits                                    49
% 7.88/1.50  lits eq                                 27
% 7.88/1.50  fd_pure                                 0
% 7.88/1.50  fd_pseudo                               0
% 7.88/1.50  fd_cond                                 0
% 7.88/1.50  fd_pseudo_cond                          8
% 7.88/1.50  AC symbols                              0
% 7.88/1.50  
% 7.88/1.50  ------ Schedule dynamic 5 is on 
% 7.88/1.50  
% 7.88/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.88/1.50  
% 7.88/1.50  
% 7.88/1.50  ------ 
% 7.88/1.50  Current options:
% 7.88/1.50  ------ 
% 7.88/1.50  
% 7.88/1.50  ------ Input Options
% 7.88/1.50  
% 7.88/1.50  --out_options                           all
% 7.88/1.50  --tptp_safe_out                         true
% 7.88/1.50  --problem_path                          ""
% 7.88/1.50  --include_path                          ""
% 7.88/1.50  --clausifier                            res/vclausify_rel
% 7.88/1.50  --clausifier_options                    --mode clausify
% 7.88/1.50  --stdin                                 false
% 7.88/1.50  --stats_out                             all
% 7.88/1.50  
% 7.88/1.50  ------ General Options
% 7.88/1.50  
% 7.88/1.50  --fof                                   false
% 7.88/1.50  --time_out_real                         305.
% 7.88/1.50  --time_out_virtual                      -1.
% 7.88/1.50  --symbol_type_check                     false
% 7.88/1.50  --clausify_out                          false
% 7.88/1.50  --sig_cnt_out                           false
% 7.88/1.50  --trig_cnt_out                          false
% 7.88/1.50  --trig_cnt_out_tolerance                1.
% 7.88/1.50  --trig_cnt_out_sk_spl                   false
% 7.88/1.50  --abstr_cl_out                          false
% 7.88/1.50  
% 7.88/1.50  ------ Global Options
% 7.88/1.50  
% 7.88/1.50  --schedule                              default
% 7.88/1.50  --add_important_lit                     false
% 7.88/1.50  --prop_solver_per_cl                    1000
% 7.88/1.50  --min_unsat_core                        false
% 7.88/1.50  --soft_assumptions                      false
% 7.88/1.50  --soft_lemma_size                       3
% 7.88/1.50  --prop_impl_unit_size                   0
% 7.88/1.50  --prop_impl_unit                        []
% 7.88/1.50  --share_sel_clauses                     true
% 7.88/1.50  --reset_solvers                         false
% 7.88/1.50  --bc_imp_inh                            [conj_cone]
% 7.88/1.50  --conj_cone_tolerance                   3.
% 7.88/1.50  --extra_neg_conj                        none
% 7.88/1.50  --large_theory_mode                     true
% 7.88/1.50  --prolific_symb_bound                   200
% 7.88/1.50  --lt_threshold                          2000
% 7.88/1.50  --clause_weak_htbl                      true
% 7.88/1.50  --gc_record_bc_elim                     false
% 7.88/1.50  
% 7.88/1.50  ------ Preprocessing Options
% 7.88/1.50  
% 7.88/1.50  --preprocessing_flag                    true
% 7.88/1.50  --time_out_prep_mult                    0.1
% 7.88/1.50  --splitting_mode                        input
% 7.88/1.50  --splitting_grd                         true
% 7.88/1.50  --splitting_cvd                         false
% 7.88/1.50  --splitting_cvd_svl                     false
% 7.88/1.50  --splitting_nvd                         32
% 7.88/1.50  --sub_typing                            true
% 7.88/1.50  --prep_gs_sim                           true
% 7.88/1.50  --prep_unflatten                        true
% 7.88/1.50  --prep_res_sim                          true
% 7.88/1.50  --prep_upred                            true
% 7.88/1.50  --prep_sem_filter                       exhaustive
% 7.88/1.50  --prep_sem_filter_out                   false
% 7.88/1.50  --pred_elim                             true
% 7.88/1.50  --res_sim_input                         true
% 7.88/1.50  --eq_ax_congr_red                       true
% 7.88/1.50  --pure_diseq_elim                       true
% 7.88/1.50  --brand_transform                       false
% 7.88/1.50  --non_eq_to_eq                          false
% 7.88/1.50  --prep_def_merge                        true
% 7.88/1.50  --prep_def_merge_prop_impl              false
% 7.88/1.50  --prep_def_merge_mbd                    true
% 7.88/1.50  --prep_def_merge_tr_red                 false
% 7.88/1.50  --prep_def_merge_tr_cl                  false
% 7.88/1.50  --smt_preprocessing                     true
% 7.88/1.50  --smt_ac_axioms                         fast
% 7.88/1.50  --preprocessed_out                      false
% 7.88/1.50  --preprocessed_stats                    false
% 7.88/1.50  
% 7.88/1.50  ------ Abstraction refinement Options
% 7.88/1.50  
% 7.88/1.50  --abstr_ref                             []
% 7.88/1.50  --abstr_ref_prep                        false
% 7.88/1.50  --abstr_ref_until_sat                   false
% 7.88/1.50  --abstr_ref_sig_restrict                funpre
% 7.88/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.88/1.50  --abstr_ref_under                       []
% 7.88/1.50  
% 7.88/1.50  ------ SAT Options
% 7.88/1.50  
% 7.88/1.50  --sat_mode                              false
% 7.88/1.50  --sat_fm_restart_options                ""
% 7.88/1.50  --sat_gr_def                            false
% 7.88/1.50  --sat_epr_types                         true
% 7.88/1.50  --sat_non_cyclic_types                  false
% 7.88/1.50  --sat_finite_models                     false
% 7.88/1.50  --sat_fm_lemmas                         false
% 7.88/1.50  --sat_fm_prep                           false
% 7.88/1.50  --sat_fm_uc_incr                        true
% 7.88/1.50  --sat_out_model                         small
% 7.88/1.50  --sat_out_clauses                       false
% 7.88/1.50  
% 7.88/1.50  ------ QBF Options
% 7.88/1.50  
% 7.88/1.50  --qbf_mode                              false
% 7.88/1.50  --qbf_elim_univ                         false
% 7.88/1.50  --qbf_dom_inst                          none
% 7.88/1.50  --qbf_dom_pre_inst                      false
% 7.88/1.50  --qbf_sk_in                             false
% 7.88/1.50  --qbf_pred_elim                         true
% 7.88/1.50  --qbf_split                             512
% 7.88/1.50  
% 7.88/1.50  ------ BMC1 Options
% 7.88/1.50  
% 7.88/1.50  --bmc1_incremental                      false
% 7.88/1.50  --bmc1_axioms                           reachable_all
% 7.88/1.50  --bmc1_min_bound                        0
% 7.88/1.50  --bmc1_max_bound                        -1
% 7.88/1.50  --bmc1_max_bound_default                -1
% 7.88/1.50  --bmc1_symbol_reachability              true
% 7.88/1.50  --bmc1_property_lemmas                  false
% 7.88/1.50  --bmc1_k_induction                      false
% 7.88/1.50  --bmc1_non_equiv_states                 false
% 7.88/1.50  --bmc1_deadlock                         false
% 7.88/1.50  --bmc1_ucm                              false
% 7.88/1.50  --bmc1_add_unsat_core                   none
% 7.88/1.50  --bmc1_unsat_core_children              false
% 7.88/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.88/1.50  --bmc1_out_stat                         full
% 7.88/1.50  --bmc1_ground_init                      false
% 7.88/1.50  --bmc1_pre_inst_next_state              false
% 7.88/1.50  --bmc1_pre_inst_state                   false
% 7.88/1.50  --bmc1_pre_inst_reach_state             false
% 7.88/1.50  --bmc1_out_unsat_core                   false
% 7.88/1.50  --bmc1_aig_witness_out                  false
% 7.88/1.50  --bmc1_verbose                          false
% 7.88/1.50  --bmc1_dump_clauses_tptp                false
% 7.88/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.88/1.50  --bmc1_dump_file                        -
% 7.88/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.88/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.88/1.50  --bmc1_ucm_extend_mode                  1
% 7.88/1.50  --bmc1_ucm_init_mode                    2
% 7.88/1.50  --bmc1_ucm_cone_mode                    none
% 7.88/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.88/1.50  --bmc1_ucm_relax_model                  4
% 7.88/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.88/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.88/1.50  --bmc1_ucm_layered_model                none
% 7.88/1.50  --bmc1_ucm_max_lemma_size               10
% 7.88/1.50  
% 7.88/1.50  ------ AIG Options
% 7.88/1.50  
% 7.88/1.50  --aig_mode                              false
% 7.88/1.50  
% 7.88/1.50  ------ Instantiation Options
% 7.88/1.50  
% 7.88/1.50  --instantiation_flag                    true
% 7.88/1.50  --inst_sos_flag                         false
% 7.88/1.50  --inst_sos_phase                        true
% 7.88/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.88/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.88/1.50  --inst_lit_sel_side                     none
% 7.88/1.50  --inst_solver_per_active                1400
% 7.88/1.50  --inst_solver_calls_frac                1.
% 7.88/1.50  --inst_passive_queue_type               priority_queues
% 7.88/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.88/1.50  --inst_passive_queues_freq              [25;2]
% 7.88/1.50  --inst_dismatching                      true
% 7.88/1.50  --inst_eager_unprocessed_to_passive     true
% 7.88/1.50  --inst_prop_sim_given                   true
% 7.88/1.50  --inst_prop_sim_new                     false
% 7.88/1.50  --inst_subs_new                         false
% 7.88/1.50  --inst_eq_res_simp                      false
% 7.88/1.50  --inst_subs_given                       false
% 7.88/1.50  --inst_orphan_elimination               true
% 7.88/1.50  --inst_learning_loop_flag               true
% 7.88/1.50  --inst_learning_start                   3000
% 7.88/1.50  --inst_learning_factor                  2
% 7.88/1.50  --inst_start_prop_sim_after_learn       3
% 7.88/1.50  --inst_sel_renew                        solver
% 7.88/1.50  --inst_lit_activity_flag                true
% 7.88/1.50  --inst_restr_to_given                   false
% 7.88/1.50  --inst_activity_threshold               500
% 7.88/1.50  --inst_out_proof                        true
% 7.88/1.50  
% 7.88/1.50  ------ Resolution Options
% 7.88/1.50  
% 7.88/1.50  --resolution_flag                       false
% 7.88/1.50  --res_lit_sel                           adaptive
% 7.88/1.50  --res_lit_sel_side                      none
% 7.88/1.50  --res_ordering                          kbo
% 7.88/1.51  --res_to_prop_solver                    active
% 7.88/1.51  --res_prop_simpl_new                    false
% 7.88/1.51  --res_prop_simpl_given                  true
% 7.88/1.51  --res_passive_queue_type                priority_queues
% 7.88/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.88/1.51  --res_passive_queues_freq               [15;5]
% 7.88/1.51  --res_forward_subs                      full
% 7.88/1.51  --res_backward_subs                     full
% 7.88/1.51  --res_forward_subs_resolution           true
% 7.88/1.51  --res_backward_subs_resolution          true
% 7.88/1.51  --res_orphan_elimination                true
% 7.88/1.51  --res_time_limit                        2.
% 7.88/1.51  --res_out_proof                         true
% 7.88/1.51  
% 7.88/1.51  ------ Superposition Options
% 7.88/1.51  
% 7.88/1.51  --superposition_flag                    true
% 7.88/1.51  --sup_passive_queue_type                priority_queues
% 7.88/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.88/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.88/1.51  --demod_completeness_check              fast
% 7.88/1.51  --demod_use_ground                      true
% 7.88/1.51  --sup_to_prop_solver                    passive
% 7.88/1.51  --sup_prop_simpl_new                    true
% 7.88/1.51  --sup_prop_simpl_given                  true
% 7.88/1.51  --sup_fun_splitting                     false
% 7.88/1.51  --sup_smt_interval                      50000
% 7.88/1.51  
% 7.88/1.51  ------ Superposition Simplification Setup
% 7.88/1.51  
% 7.88/1.51  --sup_indices_passive                   []
% 7.88/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.88/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.51  --sup_full_bw                           [BwDemod]
% 7.88/1.51  --sup_immed_triv                        [TrivRules]
% 7.88/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.51  --sup_immed_bw_main                     []
% 7.88/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.88/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.88/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.88/1.51  
% 7.88/1.51  ------ Combination Options
% 7.88/1.51  
% 7.88/1.51  --comb_res_mult                         3
% 7.88/1.51  --comb_sup_mult                         2
% 7.88/1.51  --comb_inst_mult                        10
% 7.88/1.51  
% 7.88/1.51  ------ Debug Options
% 7.88/1.51  
% 7.88/1.51  --dbg_backtrace                         false
% 7.88/1.51  --dbg_dump_prop_clauses                 false
% 7.88/1.51  --dbg_dump_prop_clauses_file            -
% 7.88/1.51  --dbg_out_stat                          false
% 7.88/1.51  
% 7.88/1.51  
% 7.88/1.51  
% 7.88/1.51  
% 7.88/1.51  ------ Proving...
% 7.88/1.51  
% 7.88/1.51  
% 7.88/1.51  % SZS status Theorem for theBenchmark.p
% 7.88/1.51  
% 7.88/1.51   Resolution empty clause
% 7.88/1.51  
% 7.88/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.88/1.51  
% 7.88/1.51  fof(f12,axiom,(
% 7.88/1.51    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 7.88/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.51  
% 7.88/1.51  fof(f62,plain,(
% 7.88/1.51    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 7.88/1.51    inference(cnf_transformation,[],[f12])).
% 7.88/1.51  
% 7.88/1.51  fof(f10,axiom,(
% 7.88/1.51    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)),
% 7.88/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.51  
% 7.88/1.51  fof(f56,plain,(
% 7.88/1.51    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 7.88/1.51    inference(cnf_transformation,[],[f10])).
% 7.88/1.51  
% 7.88/1.51  fof(f8,axiom,(
% 7.88/1.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.88/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.51  
% 7.88/1.51  fof(f54,plain,(
% 7.88/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.88/1.51    inference(cnf_transformation,[],[f8])).
% 7.88/1.51  
% 7.88/1.51  fof(f9,axiom,(
% 7.88/1.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)),
% 7.88/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.51  
% 7.88/1.51  fof(f55,plain,(
% 7.88/1.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 7.88/1.51    inference(cnf_transformation,[],[f9])).
% 7.88/1.51  
% 7.88/1.51  fof(f67,plain,(
% 7.88/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 7.88/1.51    inference(definition_unfolding,[],[f54,f55])).
% 7.88/1.51  
% 7.88/1.51  fof(f86,plain,(
% 7.88/1.51    ( ! [X0,X1] : (r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 7.88/1.51    inference(definition_unfolding,[],[f62,f56,f67])).
% 7.88/1.51  
% 7.88/1.51  fof(f14,conjecture,(
% 7.88/1.51    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 7.88/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.51  
% 7.88/1.51  fof(f15,negated_conjecture,(
% 7.88/1.51    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 7.88/1.51    inference(negated_conjecture,[],[f14])).
% 7.88/1.51  
% 7.88/1.51  fof(f19,plain,(
% 7.88/1.51    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 7.88/1.51    inference(ennf_transformation,[],[f15])).
% 7.88/1.51  
% 7.88/1.51  fof(f34,plain,(
% 7.88/1.51    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK2 != sK5 & sK2 != sK4 & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)))),
% 7.88/1.51    introduced(choice_axiom,[])).
% 7.88/1.51  
% 7.88/1.51  fof(f35,plain,(
% 7.88/1.51    sK2 != sK5 & sK2 != sK4 & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5))),
% 7.88/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f34])).
% 7.88/1.51  
% 7.88/1.51  fof(f64,plain,(
% 7.88/1.51    r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5))),
% 7.88/1.51    inference(cnf_transformation,[],[f35])).
% 7.88/1.51  
% 7.88/1.51  fof(f88,plain,(
% 7.88/1.51    r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5))),
% 7.88/1.51    inference(definition_unfolding,[],[f64,f67,f67])).
% 7.88/1.51  
% 7.88/1.51  fof(f11,axiom,(
% 7.88/1.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 7.88/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.51  
% 7.88/1.51  fof(f17,plain,(
% 7.88/1.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.88/1.51    inference(ennf_transformation,[],[f11])).
% 7.88/1.51  
% 7.88/1.51  fof(f32,plain,(
% 7.88/1.51    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 7.88/1.51    inference(nnf_transformation,[],[f17])).
% 7.88/1.51  
% 7.88/1.51  fof(f33,plain,(
% 7.88/1.51    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 7.88/1.51    inference(flattening,[],[f32])).
% 7.88/1.51  
% 7.88/1.51  fof(f57,plain,(
% 7.88/1.51    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 7.88/1.51    inference(cnf_transformation,[],[f33])).
% 7.88/1.51  
% 7.88/1.51  fof(f85,plain,(
% 7.88/1.51    ( ! [X2,X0,X1] : (k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = X0 | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) = X0 | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) )),
% 7.88/1.51    inference(definition_unfolding,[],[f57,f67,f56,f56,f67])).
% 7.88/1.51  
% 7.88/1.51  fof(f65,plain,(
% 7.88/1.51    sK2 != sK4),
% 7.88/1.51    inference(cnf_transformation,[],[f35])).
% 7.88/1.51  
% 7.88/1.51  fof(f66,plain,(
% 7.88/1.51    sK2 != sK5),
% 7.88/1.51    inference(cnf_transformation,[],[f35])).
% 7.88/1.51  
% 7.88/1.51  fof(f7,axiom,(
% 7.88/1.51    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.88/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.51  
% 7.88/1.51  fof(f27,plain,(
% 7.88/1.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.88/1.51    inference(nnf_transformation,[],[f7])).
% 7.88/1.51  
% 7.88/1.51  fof(f28,plain,(
% 7.88/1.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.88/1.51    inference(flattening,[],[f27])).
% 7.88/1.51  
% 7.88/1.51  fof(f29,plain,(
% 7.88/1.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.88/1.51    inference(rectify,[],[f28])).
% 7.88/1.51  
% 7.88/1.51  fof(f30,plain,(
% 7.88/1.51    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.88/1.51    introduced(choice_axiom,[])).
% 7.88/1.51  
% 7.88/1.51  fof(f31,plain,(
% 7.88/1.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.88/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 7.88/1.51  
% 7.88/1.51  fof(f48,plain,(
% 7.88/1.51    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 7.88/1.51    inference(cnf_transformation,[],[f31])).
% 7.88/1.51  
% 7.88/1.51  fof(f80,plain,(
% 7.88/1.51    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 7.88/1.51    inference(definition_unfolding,[],[f48,f67])).
% 7.88/1.51  
% 7.88/1.51  fof(f98,plain,(
% 7.88/1.51    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 7.88/1.51    inference(equality_resolution,[],[f80])).
% 7.88/1.51  
% 7.88/1.51  fof(f49,plain,(
% 7.88/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.88/1.51    inference(cnf_transformation,[],[f31])).
% 7.88/1.51  
% 7.88/1.51  fof(f79,plain,(
% 7.88/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 7.88/1.51    inference(definition_unfolding,[],[f49,f67])).
% 7.88/1.51  
% 7.88/1.51  fof(f96,plain,(
% 7.88/1.51    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k5_enumset1(X4,X4,X4,X4,X4,X4,X1) != X2) )),
% 7.88/1.51    inference(equality_resolution,[],[f79])).
% 7.88/1.51  
% 7.88/1.51  fof(f97,plain,(
% 7.88/1.51    ( ! [X4,X1] : (r2_hidden(X4,k5_enumset1(X4,X4,X4,X4,X4,X4,X1))) )),
% 7.88/1.51    inference(equality_resolution,[],[f96])).
% 7.88/1.51  
% 7.88/1.51  fof(f6,axiom,(
% 7.88/1.51    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.88/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.51  
% 7.88/1.51  fof(f23,plain,(
% 7.88/1.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.88/1.51    inference(nnf_transformation,[],[f6])).
% 7.88/1.51  
% 7.88/1.51  fof(f24,plain,(
% 7.88/1.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.88/1.51    inference(rectify,[],[f23])).
% 7.88/1.51  
% 7.88/1.51  fof(f25,plain,(
% 7.88/1.51    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 7.88/1.51    introduced(choice_axiom,[])).
% 7.88/1.51  
% 7.88/1.51  fof(f26,plain,(
% 7.88/1.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.88/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 7.88/1.51  
% 7.88/1.51  fof(f44,plain,(
% 7.88/1.51    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.88/1.51    inference(cnf_transformation,[],[f26])).
% 7.88/1.51  
% 7.88/1.51  fof(f74,plain,(
% 7.88/1.51    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 7.88/1.51    inference(definition_unfolding,[],[f44,f56])).
% 7.88/1.51  
% 7.88/1.51  fof(f93,plain,(
% 7.88/1.51    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) )),
% 7.88/1.51    inference(equality_resolution,[],[f74])).
% 7.88/1.51  
% 7.88/1.51  fof(f60,plain,(
% 7.88/1.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 7.88/1.51    inference(cnf_transformation,[],[f33])).
% 7.88/1.51  
% 7.88/1.51  fof(f82,plain,(
% 7.88/1.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) != X0) )),
% 7.88/1.51    inference(definition_unfolding,[],[f60,f67,f56])).
% 7.88/1.51  
% 7.88/1.51  fof(f100,plain,(
% 7.88/1.51    ( ! [X2,X1] : (r1_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) )),
% 7.88/1.51    inference(equality_resolution,[],[f82])).
% 7.88/1.51  
% 7.88/1.51  fof(f5,axiom,(
% 7.88/1.51    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 7.88/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.51  
% 7.88/1.51  fof(f43,plain,(
% 7.88/1.51    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 7.88/1.51    inference(cnf_transformation,[],[f5])).
% 7.88/1.51  
% 7.88/1.51  fof(f3,axiom,(
% 7.88/1.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.88/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.51  
% 7.88/1.51  fof(f41,plain,(
% 7.88/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.88/1.51    inference(cnf_transformation,[],[f3])).
% 7.88/1.51  
% 7.88/1.51  fof(f70,plain,(
% 7.88/1.51    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 7.88/1.51    inference(definition_unfolding,[],[f43,f41])).
% 7.88/1.51  
% 7.88/1.51  fof(f2,axiom,(
% 7.88/1.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 7.88/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.51  
% 7.88/1.51  fof(f22,plain,(
% 7.88/1.51    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 7.88/1.51    inference(nnf_transformation,[],[f2])).
% 7.88/1.51  
% 7.88/1.51  fof(f39,plain,(
% 7.88/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.88/1.51    inference(cnf_transformation,[],[f22])).
% 7.88/1.51  
% 7.88/1.51  fof(f69,plain,(
% 7.88/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.88/1.51    inference(definition_unfolding,[],[f39,f41])).
% 7.88/1.51  
% 7.88/1.51  fof(f1,axiom,(
% 7.88/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.88/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.51  
% 7.88/1.51  fof(f20,plain,(
% 7.88/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.88/1.51    inference(nnf_transformation,[],[f1])).
% 7.88/1.51  
% 7.88/1.51  fof(f21,plain,(
% 7.88/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.88/1.51    inference(flattening,[],[f20])).
% 7.88/1.51  
% 7.88/1.51  fof(f38,plain,(
% 7.88/1.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.88/1.51    inference(cnf_transformation,[],[f21])).
% 7.88/1.51  
% 7.88/1.51  fof(f13,axiom,(
% 7.88/1.51    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 7.88/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.51  
% 7.88/1.51  fof(f18,plain,(
% 7.88/1.51    ! [X0,X1] : (X0 = X1 | k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0))),
% 7.88/1.51    inference(ennf_transformation,[],[f13])).
% 7.88/1.51  
% 7.88/1.51  fof(f63,plain,(
% 7.88/1.51    ( ! [X0,X1] : (X0 = X1 | k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 7.88/1.51    inference(cnf_transformation,[],[f18])).
% 7.88/1.51  
% 7.88/1.51  fof(f87,plain,(
% 7.88/1.51    ( ! [X0,X1] : (X0 = X1 | k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) != k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 7.88/1.51    inference(definition_unfolding,[],[f63,f56,f56,f56])).
% 7.88/1.51  
% 7.88/1.51  fof(f4,axiom,(
% 7.88/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.88/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.88/1.51  
% 7.88/1.51  fof(f16,plain,(
% 7.88/1.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.88/1.51    inference(ennf_transformation,[],[f4])).
% 7.88/1.51  
% 7.88/1.51  fof(f42,plain,(
% 7.88/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.88/1.51    inference(cnf_transformation,[],[f16])).
% 7.88/1.51  
% 7.88/1.51  cnf(c_22,plain,
% 7.88/1.51      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
% 7.88/1.51      inference(cnf_transformation,[],[f86]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_1637,plain,
% 7.88/1.51      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 7.88/1.51      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_26,negated_conjecture,
% 7.88/1.51      ( r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)) ),
% 7.88/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_1634,plain,
% 7.88/1.51      ( r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = iProver_top ),
% 7.88/1.51      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_21,plain,
% 7.88/1.51      ( ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
% 7.88/1.51      | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = X0
% 7.88/1.51      | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) = X0
% 7.88/1.51      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
% 7.88/1.51      | k1_xboole_0 = X0 ),
% 7.88/1.51      inference(cnf_transformation,[],[f85]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_1635,plain,
% 7.88/1.51      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X1
% 7.88/1.51      | k5_enumset1(X0,X0,X0,X0,X0,X0,X2) = X1
% 7.88/1.51      | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) = X1
% 7.88/1.51      | k1_xboole_0 = X1
% 7.88/1.51      | r1_tarski(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X2)) != iProver_top ),
% 7.88/1.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_2038,plain,
% 7.88/1.51      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 7.88/1.51      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 7.88/1.51      | k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 7.88/1.51      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0 ),
% 7.88/1.51      inference(superposition,[status(thm)],[c_1634,c_1635]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_2449,plain,
% 7.88/1.51      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = X0
% 7.88/1.51      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 7.88/1.51      | k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 7.88/1.51      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
% 7.88/1.51      | k1_xboole_0 = X0
% 7.88/1.51      | r1_tarski(X0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top ),
% 7.88/1.51      inference(superposition,[status(thm)],[c_2038,c_1635]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_2761,plain,
% 7.88/1.51      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 7.88/1.51      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 7.88/1.51      | k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 7.88/1.51      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
% 7.88/1.51      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 7.88/1.51      inference(superposition,[status(thm)],[c_1637,c_2449]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_25,negated_conjecture,
% 7.88/1.51      ( sK2 != sK4 ),
% 7.88/1.51      inference(cnf_transformation,[],[f65]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_24,negated_conjecture,
% 7.88/1.51      ( sK2 != sK5 ),
% 7.88/1.51      inference(cnf_transformation,[],[f66]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_16,plain,
% 7.88/1.51      ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 7.88/1.51      inference(cnf_transformation,[],[f98]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_42,plain,
% 7.88/1.51      ( ~ r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | sK2 = sK2 ),
% 7.88/1.51      inference(instantiation,[status(thm)],[c_16]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_15,plain,
% 7.88/1.51      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
% 7.88/1.51      inference(cnf_transformation,[],[f97]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_45,plain,
% 7.88/1.51      ( r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 7.88/1.51      inference(instantiation,[status(thm)],[c_15]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_1164,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_1799,plain,
% 7.88/1.51      ( sK5 != X0 | sK2 != X0 | sK2 = sK5 ),
% 7.88/1.51      inference(instantiation,[status(thm)],[c_1164]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_1800,plain,
% 7.88/1.51      ( sK5 != sK2 | sK2 = sK5 | sK2 != sK2 ),
% 7.88/1.51      inference(instantiation,[status(thm)],[c_1799]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_1801,plain,
% 7.88/1.51      ( sK4 != X0 | sK2 != X0 | sK2 = sK4 ),
% 7.88/1.51      inference(instantiation,[status(thm)],[c_1164]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_1802,plain,
% 7.88/1.51      ( sK4 != sK2 | sK2 = sK4 | sK2 != sK2 ),
% 7.88/1.51      inference(instantiation,[status(thm)],[c_1801]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_1641,plain,
% 7.88/1.51      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 7.88/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_2757,plain,
% 7.88/1.51      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 7.88/1.51      | k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 7.88/1.51      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
% 7.88/1.51      | r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,X0)) = iProver_top ),
% 7.88/1.51      inference(superposition,[status(thm)],[c_2038,c_1637]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_10,plain,
% 7.88/1.51      ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 7.88/1.51      inference(cnf_transformation,[],[f93]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_1646,plain,
% 7.88/1.51      ( X0 = X1
% 7.88/1.51      | r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 7.88/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_2977,plain,
% 7.88/1.51      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 7.88/1.51      | k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 7.88/1.51      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
% 7.88/1.51      | sK4 = X0
% 7.88/1.51      | r2_hidden(X0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top ),
% 7.88/1.51      inference(superposition,[status(thm)],[c_2038,c_1646]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_3349,plain,
% 7.88/1.51      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 7.88/1.51      | k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 7.88/1.51      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
% 7.88/1.51      | sK4 = sK2 ),
% 7.88/1.51      inference(superposition,[status(thm)],[c_1641,c_2977]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_3368,plain,
% 7.88/1.51      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
% 7.88/1.51      | k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 7.88/1.51      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 7.88/1.51      inference(global_propositional_subsumption,
% 7.88/1.51                [status(thm)],
% 7.88/1.51                [c_2757,c_25,c_42,c_45,c_1802,c_3349]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_3369,plain,
% 7.88/1.51      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 7.88/1.51      | k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 7.88/1.51      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0 ),
% 7.88/1.51      inference(renaming,[status(thm)],[c_3368]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_1640,plain,
% 7.88/1.51      ( X0 = X1
% 7.88/1.51      | X0 = X2
% 7.88/1.51      | r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) != iProver_top ),
% 7.88/1.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_3910,plain,
% 7.88/1.51      ( k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 7.88/1.51      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
% 7.88/1.51      | sK4 = X0
% 7.88/1.51      | sK5 = X0
% 7.88/1.51      | r2_hidden(X0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top ),
% 7.88/1.51      inference(superposition,[status(thm)],[c_3369,c_1640]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_4341,plain,
% 7.88/1.51      ( k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 7.88/1.51      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
% 7.88/1.51      | sK4 = sK2
% 7.88/1.51      | sK5 = sK2 ),
% 7.88/1.51      inference(superposition,[status(thm)],[c_1641,c_3910]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_4414,plain,
% 7.88/1.51      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
% 7.88/1.51      | k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
% 7.88/1.51      inference(global_propositional_subsumption,
% 7.88/1.51                [status(thm)],
% 7.88/1.51                [c_2761,c_25,c_24,c_42,c_45,c_1800,c_1802,c_4341]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_4415,plain,
% 7.88/1.51      ( k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
% 7.88/1.51      | k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0 ),
% 7.88/1.51      inference(renaming,[status(thm)],[c_4414]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_18,plain,
% 7.88/1.51      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) ),
% 7.88/1.51      inference(cnf_transformation,[],[f100]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_1638,plain,
% 7.88/1.51      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) = iProver_top ),
% 7.88/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_4418,plain,
% 7.88/1.51      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
% 7.88/1.51      | r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3),k5_enumset1(X0,X0,X0,X0,X0,X0,sK5)) = iProver_top ),
% 7.88/1.51      inference(superposition,[status(thm)],[c_4415,c_1638]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_4428,plain,
% 7.88/1.51      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0
% 7.88/1.51      | sK5 = X0
% 7.88/1.51      | r2_hidden(X0,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) != iProver_top ),
% 7.88/1.51      inference(superposition,[status(thm)],[c_4415,c_1640]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_4585,plain,
% 7.88/1.51      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0 | sK5 = sK2 ),
% 7.88/1.51      inference(superposition,[status(thm)],[c_1641,c_4428]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_4605,plain,
% 7.88/1.51      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k1_xboole_0 ),
% 7.88/1.51      inference(global_propositional_subsumption,
% 7.88/1.51                [status(thm)],
% 7.88/1.51                [c_4418,c_24,c_42,c_45,c_1800,c_4585]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_4623,plain,
% 7.88/1.51      ( r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k1_xboole_0) = iProver_top ),
% 7.88/1.51      inference(superposition,[status(thm)],[c_4605,c_1637]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_6,plain,
% 7.88/1.51      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 7.88/1.51      inference(cnf_transformation,[],[f70]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_4,plain,
% 7.88/1.51      ( r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 7.88/1.51      inference(cnf_transformation,[],[f69]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_1651,plain,
% 7.88/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 7.88/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 7.88/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_2298,plain,
% 7.88/1.51      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.88/1.51      inference(superposition,[status(thm)],[c_6,c_1651]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_0,plain,
% 7.88/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.88/1.51      inference(cnf_transformation,[],[f38]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_1654,plain,
% 7.88/1.51      ( X0 = X1
% 7.88/1.51      | r1_tarski(X0,X1) != iProver_top
% 7.88/1.51      | r1_tarski(X1,X0) != iProver_top ),
% 7.88/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_3267,plain,
% 7.88/1.51      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.88/1.51      inference(superposition,[status(thm)],[c_2298,c_1654]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_5824,plain,
% 7.88/1.51      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 7.88/1.51      inference(superposition,[status(thm)],[c_4623,c_3267]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_23,plain,
% 7.88/1.51      ( X0 = X1
% 7.88/1.51      | k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) != k5_enumset1(X1,X1,X1,X1,X1,X1,X1) ),
% 7.88/1.51      inference(cnf_transformation,[],[f87]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_6196,plain,
% 7.88/1.51      ( k3_xboole_0(k1_xboole_0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) != k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 7.88/1.51      | sK2 = X0 ),
% 7.88/1.51      inference(superposition,[status(thm)],[c_5824,c_23]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_6209,plain,
% 7.88/1.51      ( k3_xboole_0(k1_xboole_0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) != k1_xboole_0
% 7.88/1.51      | sK2 = X0 ),
% 7.88/1.51      inference(light_normalisation,[status(thm)],[c_6196,c_5824]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_5,plain,
% 7.88/1.51      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.88/1.51      inference(cnf_transformation,[],[f42]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_1650,plain,
% 7.88/1.51      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.88/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_2398,plain,
% 7.88/1.51      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.88/1.51      inference(superposition,[status(thm)],[c_2298,c_1650]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_6212,plain,
% 7.88/1.51      ( sK2 = X0 | k1_xboole_0 != k1_xboole_0 ),
% 7.88/1.51      inference(demodulation,[status(thm)],[c_6209,c_2398]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_6213,plain,
% 7.88/1.51      ( sK2 = X0 ),
% 7.88/1.51      inference(equality_resolution_simp,[status(thm)],[c_6212]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_29102,plain,
% 7.88/1.51      ( sK2 != sK2 ),
% 7.88/1.51      inference(demodulation,[status(thm)],[c_6213,c_25]) ).
% 7.88/1.51  
% 7.88/1.51  cnf(c_29143,plain,
% 7.88/1.51      ( $false ),
% 7.88/1.51      inference(equality_resolution_simp,[status(thm)],[c_29102]) ).
% 7.88/1.51  
% 7.88/1.51  
% 7.88/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.88/1.51  
% 7.88/1.51  ------                               Statistics
% 7.88/1.51  
% 7.88/1.51  ------ General
% 7.88/1.51  
% 7.88/1.51  abstr_ref_over_cycles:                  0
% 7.88/1.51  abstr_ref_under_cycles:                 0
% 7.88/1.51  gc_basic_clause_elim:                   0
% 7.88/1.51  forced_gc_time:                         0
% 7.88/1.51  parsing_time:                           0.011
% 7.88/1.51  unif_index_cands_time:                  0.
% 7.88/1.51  unif_index_add_time:                    0.
% 7.88/1.51  orderings_time:                         0.
% 7.88/1.51  out_proof_time:                         0.011
% 7.88/1.51  total_time:                             0.942
% 7.88/1.51  num_of_symbols:                         43
% 7.88/1.51  num_of_terms:                           13988
% 7.88/1.51  
% 7.88/1.51  ------ Preprocessing
% 7.88/1.51  
% 7.88/1.51  num_of_splits:                          0
% 7.88/1.51  num_of_split_atoms:                     0
% 7.88/1.51  num_of_reused_defs:                     0
% 7.88/1.51  num_eq_ax_congr_red:                    15
% 7.88/1.51  num_of_sem_filtered_clauses:            1
% 7.88/1.51  num_of_subtypes:                        0
% 7.88/1.51  monotx_restored_types:                  0
% 7.88/1.51  sat_num_of_epr_types:                   0
% 7.88/1.51  sat_num_of_non_cyclic_types:            0
% 7.88/1.51  sat_guarded_non_collapsed_types:        0
% 7.88/1.51  num_pure_diseq_elim:                    0
% 7.88/1.51  simp_replaced_by:                       0
% 7.88/1.51  res_preprocessed:                       115
% 7.88/1.51  prep_upred:                             0
% 7.88/1.51  prep_unflattend:                        52
% 7.88/1.51  smt_new_axioms:                         0
% 7.88/1.51  pred_elim_cands:                        2
% 7.88/1.51  pred_elim:                              0
% 7.88/1.51  pred_elim_cl:                           0
% 7.88/1.51  pred_elim_cycles:                       2
% 7.88/1.51  merged_defs:                            8
% 7.88/1.51  merged_defs_ncl:                        0
% 7.88/1.51  bin_hyper_res:                          8
% 7.88/1.51  prep_cycles:                            4
% 7.88/1.51  pred_elim_time:                         0.01
% 7.88/1.51  splitting_time:                         0.
% 7.88/1.51  sem_filter_time:                        0.
% 7.88/1.51  monotx_time:                            0.
% 7.88/1.51  subtype_inf_time:                       0.
% 7.88/1.51  
% 7.88/1.51  ------ Problem properties
% 7.88/1.51  
% 7.88/1.51  clauses:                                25
% 7.88/1.51  conjectures:                            3
% 7.88/1.51  epr:                                    4
% 7.88/1.51  horn:                                   21
% 7.88/1.51  ground:                                 3
% 7.88/1.51  unary:                                  12
% 7.88/1.51  binary:                                 5
% 7.88/1.51  lits:                                   49
% 7.88/1.51  lits_eq:                                27
% 7.88/1.51  fd_pure:                                0
% 7.88/1.51  fd_pseudo:                              0
% 7.88/1.51  fd_cond:                                0
% 7.88/1.51  fd_pseudo_cond:                         8
% 7.88/1.51  ac_symbols:                             0
% 7.88/1.51  
% 7.88/1.51  ------ Propositional Solver
% 7.88/1.51  
% 7.88/1.51  prop_solver_calls:                      28
% 7.88/1.51  prop_fast_solver_calls:                 1190
% 7.88/1.51  smt_solver_calls:                       0
% 7.88/1.51  smt_fast_solver_calls:                  0
% 7.88/1.51  prop_num_of_clauses:                    5399
% 7.88/1.51  prop_preprocess_simplified:             14350
% 7.88/1.51  prop_fo_subsumed:                       59
% 7.88/1.51  prop_solver_time:                       0.
% 7.88/1.51  smt_solver_time:                        0.
% 7.88/1.51  smt_fast_solver_time:                   0.
% 7.88/1.51  prop_fast_solver_time:                  0.
% 7.88/1.51  prop_unsat_core_time:                   0.
% 7.88/1.51  
% 7.88/1.51  ------ QBF
% 7.88/1.51  
% 7.88/1.51  qbf_q_res:                              0
% 7.88/1.51  qbf_num_tautologies:                    0
% 7.88/1.51  qbf_prep_cycles:                        0
% 7.88/1.51  
% 7.88/1.51  ------ BMC1
% 7.88/1.51  
% 7.88/1.51  bmc1_current_bound:                     -1
% 7.88/1.51  bmc1_last_solved_bound:                 -1
% 7.88/1.51  bmc1_unsat_core_size:                   -1
% 7.88/1.51  bmc1_unsat_core_parents_size:           -1
% 7.88/1.51  bmc1_merge_next_fun:                    0
% 7.88/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.88/1.51  
% 7.88/1.51  ------ Instantiation
% 7.88/1.51  
% 7.88/1.51  inst_num_of_clauses:                    1620
% 7.88/1.51  inst_num_in_passive:                    661
% 7.88/1.51  inst_num_in_active:                     523
% 7.88/1.51  inst_num_in_unprocessed:                436
% 7.88/1.51  inst_num_of_loops:                      660
% 7.88/1.51  inst_num_of_learning_restarts:          0
% 7.88/1.51  inst_num_moves_active_passive:          136
% 7.88/1.51  inst_lit_activity:                      0
% 7.88/1.51  inst_lit_activity_moves:                0
% 7.88/1.51  inst_num_tautologies:                   0
% 7.88/1.51  inst_num_prop_implied:                  0
% 7.88/1.51  inst_num_existing_simplified:           0
% 7.88/1.51  inst_num_eq_res_simplified:             0
% 7.88/1.51  inst_num_child_elim:                    0
% 7.88/1.51  inst_num_of_dismatching_blockings:      1108
% 7.88/1.51  inst_num_of_non_proper_insts:           2156
% 7.88/1.51  inst_num_of_duplicates:                 0
% 7.88/1.51  inst_inst_num_from_inst_to_res:         0
% 7.88/1.51  inst_dismatching_checking_time:         0.
% 7.88/1.51  
% 7.88/1.51  ------ Resolution
% 7.88/1.51  
% 7.88/1.51  res_num_of_clauses:                     0
% 7.88/1.51  res_num_in_passive:                     0
% 7.88/1.51  res_num_in_active:                      0
% 7.88/1.51  res_num_of_loops:                       119
% 7.88/1.51  res_forward_subset_subsumed:            278
% 7.88/1.51  res_backward_subset_subsumed:           0
% 7.88/1.51  res_forward_subsumed:                   0
% 7.88/1.51  res_backward_subsumed:                  2
% 7.88/1.51  res_forward_subsumption_resolution:     0
% 7.88/1.51  res_backward_subsumption_resolution:    0
% 7.88/1.51  res_clause_to_clause_subsumption:       20310
% 7.88/1.51  res_orphan_elimination:                 0
% 7.88/1.51  res_tautology_del:                      134
% 7.88/1.51  res_num_eq_res_simplified:              0
% 7.88/1.51  res_num_sel_changes:                    0
% 7.88/1.51  res_moves_from_active_to_pass:          0
% 7.88/1.51  
% 7.88/1.51  ------ Superposition
% 7.88/1.51  
% 7.88/1.51  sup_time_total:                         0.
% 7.88/1.51  sup_time_generating:                    0.
% 7.88/1.51  sup_time_sim_full:                      0.
% 7.88/1.51  sup_time_sim_immed:                     0.
% 7.88/1.51  
% 7.88/1.51  sup_num_of_clauses:                     681
% 7.88/1.51  sup_num_in_active:                      11
% 7.88/1.51  sup_num_in_passive:                     670
% 7.88/1.51  sup_num_of_loops:                       131
% 7.88/1.51  sup_fw_superposition:                   1656
% 7.88/1.51  sup_bw_superposition:                   1807
% 7.88/1.51  sup_immediate_simplified:               1113
% 7.88/1.51  sup_given_eliminated:                   5
% 7.88/1.51  comparisons_done:                       0
% 7.88/1.51  comparisons_avoided:                    154
% 7.88/1.51  
% 7.88/1.51  ------ Simplifications
% 7.88/1.51  
% 7.88/1.51  
% 7.88/1.51  sim_fw_subset_subsumed:                 481
% 7.88/1.51  sim_bw_subset_subsumed:                 110
% 7.88/1.51  sim_fw_subsumed:                        310
% 7.88/1.51  sim_bw_subsumed:                        31
% 7.88/1.51  sim_fw_subsumption_res:                 17
% 7.88/1.51  sim_bw_subsumption_res:                 8
% 7.88/1.51  sim_tautology_del:                      1
% 7.88/1.51  sim_eq_tautology_del:                   234
% 7.88/1.51  sim_eq_res_simp:                        13
% 7.88/1.51  sim_fw_demodulated:                     214
% 7.88/1.51  sim_bw_demodulated:                     92
% 7.88/1.51  sim_light_normalised:                   108
% 7.88/1.51  sim_joinable_taut:                      0
% 7.88/1.51  sim_joinable_simp:                      0
% 7.88/1.51  sim_ac_normalised:                      0
% 7.88/1.51  sim_smt_subsumption:                    0
% 7.88/1.51  
%------------------------------------------------------------------------------
