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
% DateTime   : Thu Dec  3 11:32:36 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :  152 (3265 expanded)
%              Number of clauses        :   65 ( 527 expanded)
%              Number of leaves         :   24 ( 927 expanded)
%              Depth                    :   30
%              Number of atoms          :  452 (8096 expanded)
%              Number of equality atoms :  229 (5339 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f1])).

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
    inference(flattening,[],[f24])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f74,f75])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f73,f83])).

fof(f85,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f78,f84])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f48,f85])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f34])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( k1_xboole_0 != sK6
      & k1_xboole_0 != sK5
      & sK5 != sK6
      & k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( k1_xboole_0 != sK6
    & k1_xboole_0 != sK5
    & sK5 != sK6
    & k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f23,f43])).

fof(f79,plain,(
    k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f86,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f72,f84])).

fof(f110,plain,(
    k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
    inference(definition_unfolding,[],[f79,f85,f86])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f102,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f64,f85])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f52,f65])).

fof(f115,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f98])).

fof(f7,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f101,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f63,f65])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f87,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f61,f65])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f107,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f68,f86])).

fof(f121,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f107])).

fof(f81,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f106,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f69,f86])).

fof(f119,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f106])).

fof(f120,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f119])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f77,f86])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f103,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f67,f85])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f47,f85])).

fof(f111,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f91])).

fof(f80,plain,(
    sK5 != sK6 ),
    inference(cnf_transformation,[],[f44])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f50,f85])).

fof(f82,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1063,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_13,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1053,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_31,negated_conjecture,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_19,plain,
    ( k4_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1994,plain,
    ( k4_xboole_0(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_31,c_19])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1055,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2631,plain,
    ( r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(X0,k4_xboole_0(sK5,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1994,c_1055])).

cnf(c_18,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1878,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_18,c_0])).

cnf(c_20,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1881,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1878,c_20])).

cnf(c_2633,plain,
    ( r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2631,c_1881])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1045,plain,
    ( X0 = X1
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2883,plain,
    ( sK4 = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2633,c_1045])).

cnf(c_2922,plain,
    ( sK2(sK5) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1053,c_2883])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_39,plain,
    ( ~ r2_hidden(k1_xboole_0,k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_24,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_42,plain,
    ( r2_hidden(k1_xboole_0,k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_544,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1109,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_544])).

cnf(c_1110,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1109])).

cnf(c_2923,plain,
    ( sK2(sK5) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2922,c_29,c_39,c_42,c_1110])).

cnf(c_2925,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2923,c_1053])).

cnf(c_2964,plain,
    ( r2_hidden(sK4,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2925,c_29,c_39,c_42,c_1110])).

cnf(c_26,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1044,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_21,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1049,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2196,plain,
    ( r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_31,c_1049])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1052,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2770,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5
    | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2196,c_1052])).

cnf(c_2777,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1044,c_2770])).

cnf(c_2969,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5 ),
    inference(superposition,[status(thm)],[c_2964,c_2777])).

cnf(c_2974,plain,
    ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) = sK5 ),
    inference(demodulation,[status(thm)],[c_2969,c_31])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1062,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3174,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2974,c_1062])).

cnf(c_5203,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = sK6
    | r2_hidden(sK0(X0,X1,sK6),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,sK6),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,sK6),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1063,c_3174])).

cnf(c_6746,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,sK6)) = sK6
    | r2_hidden(sK0(X0,sK6,sK6),X0) = iProver_top
    | r2_hidden(sK0(X0,sK6,sK6),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5203,c_3174])).

cnf(c_6808,plain,
    ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) = sK6
    | r2_hidden(sK0(sK5,sK6,sK6),sK5) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_6746])).

cnf(c_6810,plain,
    ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) = sK6
    | r2_hidden(sK0(sK5,sK6,sK6),sK5) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6808])).

cnf(c_6811,plain,
    ( sK5 = sK6
    | r2_hidden(sK0(sK5,sK6,sK6),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6810,c_2974])).

cnf(c_30,negated_conjecture,
    ( sK5 != sK6 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_6892,plain,
    ( r2_hidden(sK0(sK5,sK6,sK6),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6811,c_30])).

cnf(c_6896,plain,
    ( sK0(sK5,sK6,sK6) = sK4 ),
    inference(superposition,[status(thm)],[c_6892,c_2883])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1065,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6898,plain,
    ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) = sK6
    | r2_hidden(sK0(sK5,sK6,sK6),sK6) != iProver_top
    | r2_hidden(sK4,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6896,c_1065])).

cnf(c_6914,plain,
    ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) = sK6
    | r2_hidden(sK4,sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6898,c_6896])).

cnf(c_6915,plain,
    ( sK5 = sK6
    | r2_hidden(sK4,sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6914,c_2974])).

cnf(c_3250,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK2(sK6),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_3174])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1098,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_544])).

cnf(c_1099,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1098])).

cnf(c_3363,plain,
    ( r2_hidden(sK2(sK6),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3250,c_28,c_39,c_42,c_1099])).

cnf(c_3367,plain,
    ( sK2(sK6) = sK4 ),
    inference(superposition,[status(thm)],[c_3363,c_2883])).

cnf(c_3463,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3367,c_1053])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6915,c_3463,c_1099,c_42,c_39,c_28,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:07:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 4.04/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.01  
% 4.04/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.04/1.01  
% 4.04/1.01  ------  iProver source info
% 4.04/1.01  
% 4.04/1.01  git: date: 2020-06-30 10:37:57 +0100
% 4.04/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.04/1.01  git: non_committed_changes: false
% 4.04/1.01  git: last_make_outside_of_git: false
% 4.04/1.01  
% 4.04/1.01  ------ 
% 4.04/1.01  
% 4.04/1.01  ------ Input Options
% 4.04/1.01  
% 4.04/1.01  --out_options                           all
% 4.04/1.01  --tptp_safe_out                         true
% 4.04/1.01  --problem_path                          ""
% 4.04/1.01  --include_path                          ""
% 4.04/1.01  --clausifier                            res/vclausify_rel
% 4.04/1.01  --clausifier_options                    ""
% 4.04/1.01  --stdin                                 false
% 4.04/1.01  --stats_out                             all
% 4.04/1.01  
% 4.04/1.01  ------ General Options
% 4.04/1.01  
% 4.04/1.01  --fof                                   false
% 4.04/1.01  --time_out_real                         305.
% 4.04/1.01  --time_out_virtual                      -1.
% 4.04/1.01  --symbol_type_check                     false
% 4.04/1.01  --clausify_out                          false
% 4.04/1.01  --sig_cnt_out                           false
% 4.04/1.01  --trig_cnt_out                          false
% 4.04/1.01  --trig_cnt_out_tolerance                1.
% 4.04/1.01  --trig_cnt_out_sk_spl                   false
% 4.04/1.01  --abstr_cl_out                          false
% 4.04/1.01  
% 4.04/1.01  ------ Global Options
% 4.04/1.01  
% 4.04/1.01  --schedule                              default
% 4.04/1.01  --add_important_lit                     false
% 4.04/1.01  --prop_solver_per_cl                    1000
% 4.04/1.01  --min_unsat_core                        false
% 4.04/1.01  --soft_assumptions                      false
% 4.04/1.01  --soft_lemma_size                       3
% 4.04/1.01  --prop_impl_unit_size                   0
% 4.04/1.01  --prop_impl_unit                        []
% 4.04/1.01  --share_sel_clauses                     true
% 4.04/1.01  --reset_solvers                         false
% 4.04/1.01  --bc_imp_inh                            [conj_cone]
% 4.04/1.01  --conj_cone_tolerance                   3.
% 4.04/1.01  --extra_neg_conj                        none
% 4.04/1.01  --large_theory_mode                     true
% 4.04/1.01  --prolific_symb_bound                   200
% 4.04/1.01  --lt_threshold                          2000
% 4.04/1.01  --clause_weak_htbl                      true
% 4.04/1.01  --gc_record_bc_elim                     false
% 4.04/1.01  
% 4.04/1.01  ------ Preprocessing Options
% 4.04/1.01  
% 4.04/1.01  --preprocessing_flag                    true
% 4.04/1.01  --time_out_prep_mult                    0.1
% 4.04/1.01  --splitting_mode                        input
% 4.04/1.01  --splitting_grd                         true
% 4.04/1.01  --splitting_cvd                         false
% 4.04/1.01  --splitting_cvd_svl                     false
% 4.04/1.01  --splitting_nvd                         32
% 4.04/1.01  --sub_typing                            true
% 4.04/1.01  --prep_gs_sim                           true
% 4.04/1.01  --prep_unflatten                        true
% 4.04/1.01  --prep_res_sim                          true
% 4.04/1.01  --prep_upred                            true
% 4.04/1.01  --prep_sem_filter                       exhaustive
% 4.04/1.01  --prep_sem_filter_out                   false
% 4.04/1.01  --pred_elim                             true
% 4.04/1.01  --res_sim_input                         true
% 4.04/1.01  --eq_ax_congr_red                       true
% 4.04/1.01  --pure_diseq_elim                       true
% 4.04/1.01  --brand_transform                       false
% 4.04/1.01  --non_eq_to_eq                          false
% 4.04/1.01  --prep_def_merge                        true
% 4.04/1.01  --prep_def_merge_prop_impl              false
% 4.04/1.01  --prep_def_merge_mbd                    true
% 4.04/1.01  --prep_def_merge_tr_red                 false
% 4.04/1.01  --prep_def_merge_tr_cl                  false
% 4.04/1.01  --smt_preprocessing                     true
% 4.04/1.01  --smt_ac_axioms                         fast
% 4.04/1.01  --preprocessed_out                      false
% 4.04/1.01  --preprocessed_stats                    false
% 4.04/1.01  
% 4.04/1.01  ------ Abstraction refinement Options
% 4.04/1.01  
% 4.04/1.01  --abstr_ref                             []
% 4.04/1.01  --abstr_ref_prep                        false
% 4.04/1.01  --abstr_ref_until_sat                   false
% 4.04/1.01  --abstr_ref_sig_restrict                funpre
% 4.04/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 4.04/1.01  --abstr_ref_under                       []
% 4.04/1.01  
% 4.04/1.01  ------ SAT Options
% 4.04/1.01  
% 4.04/1.01  --sat_mode                              false
% 4.04/1.01  --sat_fm_restart_options                ""
% 4.04/1.01  --sat_gr_def                            false
% 4.04/1.01  --sat_epr_types                         true
% 4.04/1.01  --sat_non_cyclic_types                  false
% 4.04/1.01  --sat_finite_models                     false
% 4.04/1.01  --sat_fm_lemmas                         false
% 4.04/1.01  --sat_fm_prep                           false
% 4.04/1.01  --sat_fm_uc_incr                        true
% 4.04/1.01  --sat_out_model                         small
% 4.04/1.01  --sat_out_clauses                       false
% 4.04/1.01  
% 4.04/1.01  ------ QBF Options
% 4.04/1.01  
% 4.04/1.01  --qbf_mode                              false
% 4.04/1.01  --qbf_elim_univ                         false
% 4.04/1.01  --qbf_dom_inst                          none
% 4.04/1.01  --qbf_dom_pre_inst                      false
% 4.04/1.01  --qbf_sk_in                             false
% 4.04/1.01  --qbf_pred_elim                         true
% 4.04/1.01  --qbf_split                             512
% 4.04/1.01  
% 4.04/1.01  ------ BMC1 Options
% 4.04/1.01  
% 4.04/1.01  --bmc1_incremental                      false
% 4.04/1.01  --bmc1_axioms                           reachable_all
% 4.04/1.01  --bmc1_min_bound                        0
% 4.04/1.01  --bmc1_max_bound                        -1
% 4.04/1.01  --bmc1_max_bound_default                -1
% 4.04/1.01  --bmc1_symbol_reachability              true
% 4.04/1.01  --bmc1_property_lemmas                  false
% 4.04/1.01  --bmc1_k_induction                      false
% 4.04/1.01  --bmc1_non_equiv_states                 false
% 4.04/1.01  --bmc1_deadlock                         false
% 4.04/1.01  --bmc1_ucm                              false
% 4.04/1.01  --bmc1_add_unsat_core                   none
% 4.04/1.01  --bmc1_unsat_core_children              false
% 4.04/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 4.04/1.01  --bmc1_out_stat                         full
% 4.04/1.01  --bmc1_ground_init                      false
% 4.04/1.01  --bmc1_pre_inst_next_state              false
% 4.04/1.01  --bmc1_pre_inst_state                   false
% 4.04/1.01  --bmc1_pre_inst_reach_state             false
% 4.04/1.01  --bmc1_out_unsat_core                   false
% 4.04/1.01  --bmc1_aig_witness_out                  false
% 4.04/1.01  --bmc1_verbose                          false
% 4.04/1.01  --bmc1_dump_clauses_tptp                false
% 4.04/1.01  --bmc1_dump_unsat_core_tptp             false
% 4.04/1.01  --bmc1_dump_file                        -
% 4.04/1.01  --bmc1_ucm_expand_uc_limit              128
% 4.04/1.01  --bmc1_ucm_n_expand_iterations          6
% 4.04/1.01  --bmc1_ucm_extend_mode                  1
% 4.04/1.01  --bmc1_ucm_init_mode                    2
% 4.04/1.01  --bmc1_ucm_cone_mode                    none
% 4.04/1.01  --bmc1_ucm_reduced_relation_type        0
% 4.04/1.01  --bmc1_ucm_relax_model                  4
% 4.04/1.01  --bmc1_ucm_full_tr_after_sat            true
% 4.04/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 4.04/1.01  --bmc1_ucm_layered_model                none
% 4.04/1.01  --bmc1_ucm_max_lemma_size               10
% 4.04/1.01  
% 4.04/1.01  ------ AIG Options
% 4.04/1.01  
% 4.04/1.01  --aig_mode                              false
% 4.04/1.01  
% 4.04/1.01  ------ Instantiation Options
% 4.04/1.01  
% 4.04/1.01  --instantiation_flag                    true
% 4.04/1.01  --inst_sos_flag                         true
% 4.04/1.01  --inst_sos_phase                        true
% 4.04/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.04/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.04/1.01  --inst_lit_sel_side                     num_symb
% 4.04/1.01  --inst_solver_per_active                1400
% 4.04/1.01  --inst_solver_calls_frac                1.
% 4.04/1.01  --inst_passive_queue_type               priority_queues
% 4.04/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.04/1.01  --inst_passive_queues_freq              [25;2]
% 4.04/1.01  --inst_dismatching                      true
% 4.04/1.01  --inst_eager_unprocessed_to_passive     true
% 4.04/1.01  --inst_prop_sim_given                   true
% 4.04/1.01  --inst_prop_sim_new                     false
% 4.04/1.01  --inst_subs_new                         false
% 4.04/1.01  --inst_eq_res_simp                      false
% 4.04/1.01  --inst_subs_given                       false
% 4.04/1.01  --inst_orphan_elimination               true
% 4.04/1.01  --inst_learning_loop_flag               true
% 4.04/1.01  --inst_learning_start                   3000
% 4.04/1.01  --inst_learning_factor                  2
% 4.04/1.01  --inst_start_prop_sim_after_learn       3
% 4.04/1.01  --inst_sel_renew                        solver
% 4.04/1.01  --inst_lit_activity_flag                true
% 4.04/1.01  --inst_restr_to_given                   false
% 4.04/1.01  --inst_activity_threshold               500
% 4.04/1.01  --inst_out_proof                        true
% 4.04/1.01  
% 4.04/1.01  ------ Resolution Options
% 4.04/1.01  
% 4.04/1.01  --resolution_flag                       true
% 4.04/1.01  --res_lit_sel                           adaptive
% 4.04/1.01  --res_lit_sel_side                      none
% 4.04/1.01  --res_ordering                          kbo
% 4.04/1.01  --res_to_prop_solver                    active
% 4.04/1.01  --res_prop_simpl_new                    false
% 4.04/1.01  --res_prop_simpl_given                  true
% 4.04/1.01  --res_passive_queue_type                priority_queues
% 4.04/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.04/1.01  --res_passive_queues_freq               [15;5]
% 4.04/1.01  --res_forward_subs                      full
% 4.04/1.01  --res_backward_subs                     full
% 4.04/1.01  --res_forward_subs_resolution           true
% 4.04/1.01  --res_backward_subs_resolution          true
% 4.04/1.01  --res_orphan_elimination                true
% 4.04/1.01  --res_time_limit                        2.
% 4.04/1.01  --res_out_proof                         true
% 4.04/1.01  
% 4.04/1.01  ------ Superposition Options
% 4.04/1.01  
% 4.04/1.01  --superposition_flag                    true
% 4.04/1.01  --sup_passive_queue_type                priority_queues
% 4.04/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.04/1.01  --sup_passive_queues_freq               [8;1;4]
% 4.04/1.01  --demod_completeness_check              fast
% 4.04/1.01  --demod_use_ground                      true
% 4.04/1.01  --sup_to_prop_solver                    passive
% 4.04/1.01  --sup_prop_simpl_new                    true
% 4.04/1.01  --sup_prop_simpl_given                  true
% 4.04/1.01  --sup_fun_splitting                     true
% 4.04/1.01  --sup_smt_interval                      50000
% 4.04/1.01  
% 4.04/1.01  ------ Superposition Simplification Setup
% 4.04/1.01  
% 4.04/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.04/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.04/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.04/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 4.04/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.04/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.04/1.01  --sup_immed_triv                        [TrivRules]
% 4.04/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/1.01  --sup_immed_bw_main                     []
% 4.04/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.04/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 4.04/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/1.01  --sup_input_bw                          []
% 4.04/1.01  
% 4.04/1.01  ------ Combination Options
% 4.04/1.01  
% 4.04/1.01  --comb_res_mult                         3
% 4.04/1.01  --comb_sup_mult                         2
% 4.04/1.01  --comb_inst_mult                        10
% 4.04/1.01  
% 4.04/1.01  ------ Debug Options
% 4.04/1.01  
% 4.04/1.01  --dbg_backtrace                         false
% 4.04/1.01  --dbg_dump_prop_clauses                 false
% 4.04/1.01  --dbg_dump_prop_clauses_file            -
% 4.04/1.01  --dbg_out_stat                          false
% 4.04/1.01  ------ Parsing...
% 4.04/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.04/1.01  
% 4.04/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.04/1.01  
% 4.04/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.04/1.01  
% 4.04/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.04/1.01  ------ Proving...
% 4.04/1.01  ------ Problem Properties 
% 4.04/1.01  
% 4.04/1.01  
% 4.04/1.01  clauses                                 31
% 4.04/1.01  conjectures                             4
% 4.04/1.01  EPR                                     5
% 4.04/1.01  Horn                                    25
% 4.04/1.01  unary                                   11
% 4.04/1.01  binary                                  9
% 4.04/1.01  lits                                    64
% 4.04/1.01  lits eq                                 22
% 4.04/1.01  fd_pure                                 0
% 4.04/1.01  fd_pseudo                               0
% 4.04/1.01  fd_cond                                 1
% 4.04/1.01  fd_pseudo_cond                          9
% 4.04/1.01  AC symbols                              0
% 4.04/1.01  
% 4.04/1.01  ------ Schedule dynamic 5 is on 
% 4.04/1.01  
% 4.04/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.04/1.01  
% 4.04/1.01  
% 4.04/1.01  ------ 
% 4.04/1.01  Current options:
% 4.04/1.01  ------ 
% 4.04/1.01  
% 4.04/1.01  ------ Input Options
% 4.04/1.01  
% 4.04/1.01  --out_options                           all
% 4.04/1.01  --tptp_safe_out                         true
% 4.04/1.01  --problem_path                          ""
% 4.04/1.01  --include_path                          ""
% 4.04/1.01  --clausifier                            res/vclausify_rel
% 4.04/1.01  --clausifier_options                    ""
% 4.04/1.01  --stdin                                 false
% 4.04/1.01  --stats_out                             all
% 4.04/1.01  
% 4.04/1.01  ------ General Options
% 4.04/1.01  
% 4.04/1.01  --fof                                   false
% 4.04/1.01  --time_out_real                         305.
% 4.04/1.01  --time_out_virtual                      -1.
% 4.04/1.01  --symbol_type_check                     false
% 4.04/1.01  --clausify_out                          false
% 4.04/1.01  --sig_cnt_out                           false
% 4.04/1.01  --trig_cnt_out                          false
% 4.04/1.01  --trig_cnt_out_tolerance                1.
% 4.04/1.01  --trig_cnt_out_sk_spl                   false
% 4.04/1.01  --abstr_cl_out                          false
% 4.04/1.01  
% 4.04/1.01  ------ Global Options
% 4.04/1.01  
% 4.04/1.01  --schedule                              default
% 4.04/1.01  --add_important_lit                     false
% 4.04/1.01  --prop_solver_per_cl                    1000
% 4.04/1.01  --min_unsat_core                        false
% 4.04/1.01  --soft_assumptions                      false
% 4.04/1.01  --soft_lemma_size                       3
% 4.04/1.01  --prop_impl_unit_size                   0
% 4.04/1.01  --prop_impl_unit                        []
% 4.04/1.01  --share_sel_clauses                     true
% 4.04/1.01  --reset_solvers                         false
% 4.04/1.01  --bc_imp_inh                            [conj_cone]
% 4.04/1.01  --conj_cone_tolerance                   3.
% 4.04/1.01  --extra_neg_conj                        none
% 4.04/1.01  --large_theory_mode                     true
% 4.04/1.01  --prolific_symb_bound                   200
% 4.04/1.01  --lt_threshold                          2000
% 4.04/1.01  --clause_weak_htbl                      true
% 4.04/1.01  --gc_record_bc_elim                     false
% 4.04/1.01  
% 4.04/1.01  ------ Preprocessing Options
% 4.04/1.01  
% 4.04/1.01  --preprocessing_flag                    true
% 4.04/1.01  --time_out_prep_mult                    0.1
% 4.04/1.01  --splitting_mode                        input
% 4.04/1.01  --splitting_grd                         true
% 4.04/1.01  --splitting_cvd                         false
% 4.04/1.01  --splitting_cvd_svl                     false
% 4.04/1.01  --splitting_nvd                         32
% 4.04/1.01  --sub_typing                            true
% 4.04/1.01  --prep_gs_sim                           true
% 4.04/1.01  --prep_unflatten                        true
% 4.04/1.01  --prep_res_sim                          true
% 4.04/1.01  --prep_upred                            true
% 4.04/1.01  --prep_sem_filter                       exhaustive
% 4.04/1.01  --prep_sem_filter_out                   false
% 4.04/1.01  --pred_elim                             true
% 4.04/1.01  --res_sim_input                         true
% 4.04/1.01  --eq_ax_congr_red                       true
% 4.04/1.01  --pure_diseq_elim                       true
% 4.04/1.01  --brand_transform                       false
% 4.04/1.01  --non_eq_to_eq                          false
% 4.04/1.01  --prep_def_merge                        true
% 4.04/1.01  --prep_def_merge_prop_impl              false
% 4.04/1.01  --prep_def_merge_mbd                    true
% 4.04/1.01  --prep_def_merge_tr_red                 false
% 4.04/1.01  --prep_def_merge_tr_cl                  false
% 4.04/1.01  --smt_preprocessing                     true
% 4.04/1.01  --smt_ac_axioms                         fast
% 4.04/1.01  --preprocessed_out                      false
% 4.04/1.01  --preprocessed_stats                    false
% 4.04/1.01  
% 4.04/1.01  ------ Abstraction refinement Options
% 4.04/1.01  
% 4.04/1.01  --abstr_ref                             []
% 4.04/1.01  --abstr_ref_prep                        false
% 4.04/1.01  --abstr_ref_until_sat                   false
% 4.04/1.01  --abstr_ref_sig_restrict                funpre
% 4.04/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 4.04/1.01  --abstr_ref_under                       []
% 4.04/1.01  
% 4.04/1.01  ------ SAT Options
% 4.04/1.01  
% 4.04/1.01  --sat_mode                              false
% 4.04/1.01  --sat_fm_restart_options                ""
% 4.04/1.01  --sat_gr_def                            false
% 4.04/1.01  --sat_epr_types                         true
% 4.04/1.01  --sat_non_cyclic_types                  false
% 4.04/1.01  --sat_finite_models                     false
% 4.04/1.01  --sat_fm_lemmas                         false
% 4.04/1.01  --sat_fm_prep                           false
% 4.04/1.01  --sat_fm_uc_incr                        true
% 4.04/1.01  --sat_out_model                         small
% 4.04/1.01  --sat_out_clauses                       false
% 4.04/1.01  
% 4.04/1.01  ------ QBF Options
% 4.04/1.01  
% 4.04/1.01  --qbf_mode                              false
% 4.04/1.01  --qbf_elim_univ                         false
% 4.04/1.01  --qbf_dom_inst                          none
% 4.04/1.01  --qbf_dom_pre_inst                      false
% 4.04/1.01  --qbf_sk_in                             false
% 4.04/1.01  --qbf_pred_elim                         true
% 4.04/1.01  --qbf_split                             512
% 4.04/1.01  
% 4.04/1.01  ------ BMC1 Options
% 4.04/1.01  
% 4.04/1.01  --bmc1_incremental                      false
% 4.04/1.01  --bmc1_axioms                           reachable_all
% 4.04/1.01  --bmc1_min_bound                        0
% 4.04/1.01  --bmc1_max_bound                        -1
% 4.04/1.01  --bmc1_max_bound_default                -1
% 4.04/1.01  --bmc1_symbol_reachability              true
% 4.04/1.01  --bmc1_property_lemmas                  false
% 4.04/1.01  --bmc1_k_induction                      false
% 4.04/1.01  --bmc1_non_equiv_states                 false
% 4.04/1.01  --bmc1_deadlock                         false
% 4.04/1.01  --bmc1_ucm                              false
% 4.04/1.01  --bmc1_add_unsat_core                   none
% 4.04/1.01  --bmc1_unsat_core_children              false
% 4.04/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 4.04/1.01  --bmc1_out_stat                         full
% 4.04/1.01  --bmc1_ground_init                      false
% 4.04/1.01  --bmc1_pre_inst_next_state              false
% 4.04/1.01  --bmc1_pre_inst_state                   false
% 4.04/1.01  --bmc1_pre_inst_reach_state             false
% 4.04/1.01  --bmc1_out_unsat_core                   false
% 4.04/1.01  --bmc1_aig_witness_out                  false
% 4.04/1.01  --bmc1_verbose                          false
% 4.04/1.01  --bmc1_dump_clauses_tptp                false
% 4.04/1.01  --bmc1_dump_unsat_core_tptp             false
% 4.04/1.01  --bmc1_dump_file                        -
% 4.04/1.01  --bmc1_ucm_expand_uc_limit              128
% 4.04/1.01  --bmc1_ucm_n_expand_iterations          6
% 4.04/1.01  --bmc1_ucm_extend_mode                  1
% 4.04/1.01  --bmc1_ucm_init_mode                    2
% 4.04/1.01  --bmc1_ucm_cone_mode                    none
% 4.04/1.01  --bmc1_ucm_reduced_relation_type        0
% 4.04/1.01  --bmc1_ucm_relax_model                  4
% 4.04/1.01  --bmc1_ucm_full_tr_after_sat            true
% 4.04/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 4.04/1.01  --bmc1_ucm_layered_model                none
% 4.04/1.01  --bmc1_ucm_max_lemma_size               10
% 4.04/1.01  
% 4.04/1.01  ------ AIG Options
% 4.04/1.01  
% 4.04/1.01  --aig_mode                              false
% 4.04/1.01  
% 4.04/1.01  ------ Instantiation Options
% 4.04/1.01  
% 4.04/1.01  --instantiation_flag                    true
% 4.04/1.01  --inst_sos_flag                         true
% 4.04/1.01  --inst_sos_phase                        true
% 4.04/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.04/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.04/1.01  --inst_lit_sel_side                     none
% 4.04/1.01  --inst_solver_per_active                1400
% 4.04/1.01  --inst_solver_calls_frac                1.
% 4.04/1.01  --inst_passive_queue_type               priority_queues
% 4.04/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.04/1.01  --inst_passive_queues_freq              [25;2]
% 4.04/1.01  --inst_dismatching                      true
% 4.04/1.01  --inst_eager_unprocessed_to_passive     true
% 4.04/1.01  --inst_prop_sim_given                   true
% 4.04/1.01  --inst_prop_sim_new                     false
% 4.04/1.01  --inst_subs_new                         false
% 4.04/1.01  --inst_eq_res_simp                      false
% 4.04/1.01  --inst_subs_given                       false
% 4.04/1.01  --inst_orphan_elimination               true
% 4.04/1.01  --inst_learning_loop_flag               true
% 4.04/1.01  --inst_learning_start                   3000
% 4.04/1.01  --inst_learning_factor                  2
% 4.04/1.01  --inst_start_prop_sim_after_learn       3
% 4.04/1.01  --inst_sel_renew                        solver
% 4.04/1.01  --inst_lit_activity_flag                true
% 4.04/1.01  --inst_restr_to_given                   false
% 4.04/1.01  --inst_activity_threshold               500
% 4.04/1.01  --inst_out_proof                        true
% 4.04/1.01  
% 4.04/1.01  ------ Resolution Options
% 4.04/1.01  
% 4.04/1.01  --resolution_flag                       false
% 4.04/1.01  --res_lit_sel                           adaptive
% 4.04/1.01  --res_lit_sel_side                      none
% 4.04/1.01  --res_ordering                          kbo
% 4.04/1.01  --res_to_prop_solver                    active
% 4.04/1.01  --res_prop_simpl_new                    false
% 4.04/1.01  --res_prop_simpl_given                  true
% 4.04/1.01  --res_passive_queue_type                priority_queues
% 4.04/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.04/1.01  --res_passive_queues_freq               [15;5]
% 4.04/1.01  --res_forward_subs                      full
% 4.04/1.01  --res_backward_subs                     full
% 4.04/1.01  --res_forward_subs_resolution           true
% 4.04/1.01  --res_backward_subs_resolution          true
% 4.04/1.01  --res_orphan_elimination                true
% 4.04/1.01  --res_time_limit                        2.
% 4.04/1.01  --res_out_proof                         true
% 4.04/1.01  
% 4.04/1.01  ------ Superposition Options
% 4.04/1.01  
% 4.04/1.01  --superposition_flag                    true
% 4.04/1.01  --sup_passive_queue_type                priority_queues
% 4.04/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.04/1.01  --sup_passive_queues_freq               [8;1;4]
% 4.04/1.01  --demod_completeness_check              fast
% 4.04/1.01  --demod_use_ground                      true
% 4.04/1.01  --sup_to_prop_solver                    passive
% 4.04/1.01  --sup_prop_simpl_new                    true
% 4.04/1.01  --sup_prop_simpl_given                  true
% 4.04/1.01  --sup_fun_splitting                     true
% 4.04/1.01  --sup_smt_interval                      50000
% 4.04/1.01  
% 4.04/1.01  ------ Superposition Simplification Setup
% 4.04/1.01  
% 4.04/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.04/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.04/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.04/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 4.04/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.04/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.04/1.01  --sup_immed_triv                        [TrivRules]
% 4.04/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/1.01  --sup_immed_bw_main                     []
% 4.04/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.04/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 4.04/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/1.01  --sup_input_bw                          []
% 4.04/1.01  
% 4.04/1.01  ------ Combination Options
% 4.04/1.01  
% 4.04/1.01  --comb_res_mult                         3
% 4.04/1.01  --comb_sup_mult                         2
% 4.04/1.01  --comb_inst_mult                        10
% 4.04/1.01  
% 4.04/1.01  ------ Debug Options
% 4.04/1.01  
% 4.04/1.01  --dbg_backtrace                         false
% 4.04/1.01  --dbg_dump_prop_clauses                 false
% 4.04/1.01  --dbg_dump_prop_clauses_file            -
% 4.04/1.01  --dbg_out_stat                          false
% 4.04/1.01  
% 4.04/1.01  
% 4.04/1.01  
% 4.04/1.01  
% 4.04/1.01  ------ Proving...
% 4.04/1.01  
% 4.04/1.01  
% 4.04/1.01  % SZS status Theorem for theBenchmark.p
% 4.04/1.01  
% 4.04/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 4.04/1.01  
% 4.04/1.01  fof(f1,axiom,(
% 4.04/1.01    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f24,plain,(
% 4.04/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.04/1.01    inference(nnf_transformation,[],[f1])).
% 4.04/1.01  
% 4.04/1.01  fof(f25,plain,(
% 4.04/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.04/1.01    inference(flattening,[],[f24])).
% 4.04/1.01  
% 4.04/1.01  fof(f26,plain,(
% 4.04/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.04/1.01    inference(rectify,[],[f25])).
% 4.04/1.01  
% 4.04/1.01  fof(f27,plain,(
% 4.04/1.01    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 4.04/1.01    introduced(choice_axiom,[])).
% 4.04/1.01  
% 4.04/1.01  fof(f28,plain,(
% 4.04/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.04/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 4.04/1.01  
% 4.04/1.01  fof(f48,plain,(
% 4.04/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 4.04/1.01    inference(cnf_transformation,[],[f28])).
% 4.04/1.01  
% 4.04/1.01  fof(f18,axiom,(
% 4.04/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f78,plain,(
% 4.04/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 4.04/1.01    inference(cnf_transformation,[],[f18])).
% 4.04/1.01  
% 4.04/1.01  fof(f14,axiom,(
% 4.04/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f73,plain,(
% 4.04/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.04/1.01    inference(cnf_transformation,[],[f14])).
% 4.04/1.01  
% 4.04/1.01  fof(f15,axiom,(
% 4.04/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f74,plain,(
% 4.04/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.04/1.01    inference(cnf_transformation,[],[f15])).
% 4.04/1.01  
% 4.04/1.01  fof(f16,axiom,(
% 4.04/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f75,plain,(
% 4.04/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.04/1.01    inference(cnf_transformation,[],[f16])).
% 4.04/1.01  
% 4.04/1.01  fof(f83,plain,(
% 4.04/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 4.04/1.01    inference(definition_unfolding,[],[f74,f75])).
% 4.04/1.01  
% 4.04/1.01  fof(f84,plain,(
% 4.04/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 4.04/1.01    inference(definition_unfolding,[],[f73,f83])).
% 4.04/1.01  
% 4.04/1.01  fof(f85,plain,(
% 4.04/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 4.04/1.01    inference(definition_unfolding,[],[f78,f84])).
% 4.04/1.01  
% 4.04/1.01  fof(f90,plain,(
% 4.04/1.01    ( ! [X2,X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 4.04/1.01    inference(definition_unfolding,[],[f48,f85])).
% 4.04/1.01  
% 4.04/1.01  fof(f3,axiom,(
% 4.04/1.01    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f21,plain,(
% 4.04/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 4.04/1.01    inference(ennf_transformation,[],[f3])).
% 4.04/1.01  
% 4.04/1.01  fof(f34,plain,(
% 4.04/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 4.04/1.01    introduced(choice_axiom,[])).
% 4.04/1.01  
% 4.04/1.01  fof(f35,plain,(
% 4.04/1.01    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 4.04/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f34])).
% 4.04/1.01  
% 4.04/1.01  fof(f57,plain,(
% 4.04/1.01    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 4.04/1.01    inference(cnf_transformation,[],[f35])).
% 4.04/1.01  
% 4.04/1.01  fof(f19,conjecture,(
% 4.04/1.01    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f20,negated_conjecture,(
% 4.04/1.01    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 4.04/1.01    inference(negated_conjecture,[],[f19])).
% 4.04/1.01  
% 4.04/1.01  fof(f23,plain,(
% 4.04/1.01    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 4.04/1.01    inference(ennf_transformation,[],[f20])).
% 4.04/1.01  
% 4.04/1.01  fof(f43,plain,(
% 4.04/1.01    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0)) => (k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & sK5 != sK6 & k2_xboole_0(sK5,sK6) = k1_tarski(sK4))),
% 4.04/1.01    introduced(choice_axiom,[])).
% 4.04/1.01  
% 4.04/1.01  fof(f44,plain,(
% 4.04/1.01    k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & sK5 != sK6 & k2_xboole_0(sK5,sK6) = k1_tarski(sK4)),
% 4.04/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f23,f43])).
% 4.04/1.01  
% 4.04/1.01  fof(f79,plain,(
% 4.04/1.01    k2_xboole_0(sK5,sK6) = k1_tarski(sK4)),
% 4.04/1.01    inference(cnf_transformation,[],[f44])).
% 4.04/1.01  
% 4.04/1.01  fof(f13,axiom,(
% 4.04/1.01    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f72,plain,(
% 4.04/1.01    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 4.04/1.01    inference(cnf_transformation,[],[f13])).
% 4.04/1.01  
% 4.04/1.01  fof(f86,plain,(
% 4.04/1.01    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 4.04/1.01    inference(definition_unfolding,[],[f72,f84])).
% 4.04/1.01  
% 4.04/1.01  fof(f110,plain,(
% 4.04/1.01    k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6))),
% 4.04/1.01    inference(definition_unfolding,[],[f79,f85,f86])).
% 4.04/1.01  
% 4.04/1.01  fof(f8,axiom,(
% 4.04/1.01    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f64,plain,(
% 4.04/1.01    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 4.04/1.01    inference(cnf_transformation,[],[f8])).
% 4.04/1.01  
% 4.04/1.01  fof(f102,plain,(
% 4.04/1.01    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 4.04/1.01    inference(definition_unfolding,[],[f64,f85])).
% 4.04/1.01  
% 4.04/1.01  fof(f2,axiom,(
% 4.04/1.01    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f29,plain,(
% 4.04/1.01    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.04/1.01    inference(nnf_transformation,[],[f2])).
% 4.04/1.01  
% 4.04/1.01  fof(f30,plain,(
% 4.04/1.01    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.04/1.01    inference(flattening,[],[f29])).
% 4.04/1.01  
% 4.04/1.01  fof(f31,plain,(
% 4.04/1.01    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.04/1.01    inference(rectify,[],[f30])).
% 4.04/1.01  
% 4.04/1.01  fof(f32,plain,(
% 4.04/1.01    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 4.04/1.01    introduced(choice_axiom,[])).
% 4.04/1.01  
% 4.04/1.01  fof(f33,plain,(
% 4.04/1.01    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.04/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 4.04/1.01  
% 4.04/1.01  fof(f52,plain,(
% 4.04/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 4.04/1.01    inference(cnf_transformation,[],[f33])).
% 4.04/1.01  
% 4.04/1.01  fof(f9,axiom,(
% 4.04/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f65,plain,(
% 4.04/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.04/1.01    inference(cnf_transformation,[],[f9])).
% 4.04/1.01  
% 4.04/1.01  fof(f98,plain,(
% 4.04/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 4.04/1.01    inference(definition_unfolding,[],[f52,f65])).
% 4.04/1.01  
% 4.04/1.01  fof(f115,plain,(
% 4.04/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 4.04/1.01    inference(equality_resolution,[],[f98])).
% 4.04/1.01  
% 4.04/1.01  fof(f7,axiom,(
% 4.04/1.01    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f63,plain,(
% 4.04/1.01    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 4.04/1.01    inference(cnf_transformation,[],[f7])).
% 4.04/1.01  
% 4.04/1.01  fof(f101,plain,(
% 4.04/1.01    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 4.04/1.01    inference(definition_unfolding,[],[f63,f65])).
% 4.04/1.01  
% 4.04/1.01  fof(f5,axiom,(
% 4.04/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f61,plain,(
% 4.04/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.04/1.01    inference(cnf_transformation,[],[f5])).
% 4.04/1.01  
% 4.04/1.01  fof(f87,plain,(
% 4.04/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 4.04/1.01    inference(definition_unfolding,[],[f61,f65])).
% 4.04/1.01  
% 4.04/1.01  fof(f10,axiom,(
% 4.04/1.01    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f66,plain,(
% 4.04/1.01    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.04/1.01    inference(cnf_transformation,[],[f10])).
% 4.04/1.01  
% 4.04/1.01  fof(f12,axiom,(
% 4.04/1.01    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f38,plain,(
% 4.04/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 4.04/1.01    inference(nnf_transformation,[],[f12])).
% 4.04/1.01  
% 4.04/1.01  fof(f39,plain,(
% 4.04/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 4.04/1.01    inference(rectify,[],[f38])).
% 4.04/1.01  
% 4.04/1.01  fof(f40,plain,(
% 4.04/1.01    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 4.04/1.01    introduced(choice_axiom,[])).
% 4.04/1.01  
% 4.04/1.01  fof(f41,plain,(
% 4.04/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 4.04/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 4.04/1.01  
% 4.04/1.01  fof(f68,plain,(
% 4.04/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 4.04/1.01    inference(cnf_transformation,[],[f41])).
% 4.04/1.01  
% 4.04/1.01  fof(f107,plain,(
% 4.04/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 4.04/1.01    inference(definition_unfolding,[],[f68,f86])).
% 4.04/1.01  
% 4.04/1.01  fof(f121,plain,(
% 4.04/1.01    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 4.04/1.01    inference(equality_resolution,[],[f107])).
% 4.04/1.01  
% 4.04/1.01  fof(f81,plain,(
% 4.04/1.01    k1_xboole_0 != sK5),
% 4.04/1.01    inference(cnf_transformation,[],[f44])).
% 4.04/1.01  
% 4.04/1.01  fof(f69,plain,(
% 4.04/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 4.04/1.01    inference(cnf_transformation,[],[f41])).
% 4.04/1.01  
% 4.04/1.01  fof(f106,plain,(
% 4.04/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 4.04/1.01    inference(definition_unfolding,[],[f69,f86])).
% 4.04/1.01  
% 4.04/1.01  fof(f119,plain,(
% 4.04/1.01    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 4.04/1.01    inference(equality_resolution,[],[f106])).
% 4.04/1.01  
% 4.04/1.01  fof(f120,plain,(
% 4.04/1.01    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 4.04/1.01    inference(equality_resolution,[],[f119])).
% 4.04/1.01  
% 4.04/1.01  fof(f17,axiom,(
% 4.04/1.01    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f42,plain,(
% 4.04/1.01    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 4.04/1.01    inference(nnf_transformation,[],[f17])).
% 4.04/1.01  
% 4.04/1.01  fof(f77,plain,(
% 4.04/1.01    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 4.04/1.01    inference(cnf_transformation,[],[f42])).
% 4.04/1.01  
% 4.04/1.01  fof(f108,plain,(
% 4.04/1.01    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 4.04/1.01    inference(definition_unfolding,[],[f77,f86])).
% 4.04/1.01  
% 4.04/1.01  fof(f11,axiom,(
% 4.04/1.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f67,plain,(
% 4.04/1.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.04/1.01    inference(cnf_transformation,[],[f11])).
% 4.04/1.01  
% 4.04/1.01  fof(f103,plain,(
% 4.04/1.01    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 4.04/1.01    inference(definition_unfolding,[],[f67,f85])).
% 4.04/1.01  
% 4.04/1.01  fof(f4,axiom,(
% 4.04/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.04/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/1.01  
% 4.04/1.01  fof(f36,plain,(
% 4.04/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.04/1.01    inference(nnf_transformation,[],[f4])).
% 4.04/1.01  
% 4.04/1.01  fof(f37,plain,(
% 4.04/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.04/1.01    inference(flattening,[],[f36])).
% 4.04/1.01  
% 4.04/1.01  fof(f60,plain,(
% 4.04/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.04/1.01    inference(cnf_transformation,[],[f37])).
% 4.04/1.01  
% 4.04/1.01  fof(f47,plain,(
% 4.04/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 4.04/1.01    inference(cnf_transformation,[],[f28])).
% 4.04/1.01  
% 4.04/1.01  fof(f91,plain,(
% 4.04/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 4.04/1.01    inference(definition_unfolding,[],[f47,f85])).
% 4.04/1.01  
% 4.04/1.01  fof(f111,plain,(
% 4.04/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 4.04/1.01    inference(equality_resolution,[],[f91])).
% 4.04/1.01  
% 4.04/1.01  fof(f80,plain,(
% 4.04/1.01    sK5 != sK6),
% 4.04/1.01    inference(cnf_transformation,[],[f44])).
% 4.04/1.01  
% 4.04/1.01  fof(f50,plain,(
% 4.04/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 4.04/1.01    inference(cnf_transformation,[],[f28])).
% 4.04/1.01  
% 4.04/1.01  fof(f88,plain,(
% 4.04/1.01    ( ! [X2,X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 4.04/1.01    inference(definition_unfolding,[],[f50,f85])).
% 4.04/1.01  
% 4.04/1.01  fof(f82,plain,(
% 4.04/1.01    k1_xboole_0 != sK6),
% 4.04/1.01    inference(cnf_transformation,[],[f44])).
% 4.04/1.01  
% 4.04/1.01  cnf(c_3,plain,
% 4.04/1.01      ( r2_hidden(sK0(X0,X1,X2),X1)
% 4.04/1.01      | r2_hidden(sK0(X0,X1,X2),X2)
% 4.04/1.01      | r2_hidden(sK0(X0,X1,X2),X0)
% 4.04/1.01      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2 ),
% 4.04/1.01      inference(cnf_transformation,[],[f90]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1063,plain,
% 4.04/1.01      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2
% 4.04/1.01      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
% 4.04/1.01      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 4.04/1.01      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_13,plain,
% 4.04/1.01      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 4.04/1.01      inference(cnf_transformation,[],[f57]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1053,plain,
% 4.04/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_31,negated_conjecture,
% 4.04/1.01      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) ),
% 4.04/1.01      inference(cnf_transformation,[],[f110]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_19,plain,
% 4.04/1.01      ( k4_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k1_xboole_0 ),
% 4.04/1.01      inference(cnf_transformation,[],[f102]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1994,plain,
% 4.04/1.01      ( k4_xboole_0(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = k1_xboole_0 ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_31,c_19]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_11,plain,
% 4.04/1.01      ( r2_hidden(X0,X1)
% 4.04/1.01      | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 4.04/1.01      inference(cnf_transformation,[],[f115]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1055,plain,
% 4.04/1.01      ( r2_hidden(X0,X1) = iProver_top
% 4.04/1.01      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_2631,plain,
% 4.04/1.01      ( r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 4.04/1.01      | r2_hidden(X0,k4_xboole_0(sK5,k1_xboole_0)) != iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_1994,c_1055]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_18,plain,
% 4.04/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 4.04/1.01      inference(cnf_transformation,[],[f101]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_0,plain,
% 4.04/1.01      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 4.04/1.01      inference(cnf_transformation,[],[f87]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1878,plain,
% 4.04/1.01      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_18,c_0]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_20,plain,
% 4.04/1.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.04/1.01      inference(cnf_transformation,[],[f66]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1881,plain,
% 4.04/1.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.04/1.01      inference(light_normalisation,[status(thm)],[c_1878,c_20]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_2633,plain,
% 4.04/1.01      ( r2_hidden(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 4.04/1.01      | r2_hidden(X0,sK5) != iProver_top ),
% 4.04/1.01      inference(demodulation,[status(thm)],[c_2631,c_1881]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_25,plain,
% 4.04/1.01      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1 ),
% 4.04/1.01      inference(cnf_transformation,[],[f121]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1045,plain,
% 4.04/1.01      ( X0 = X1
% 4.04/1.01      | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_2883,plain,
% 4.04/1.01      ( sK4 = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_2633,c_1045]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_2922,plain,
% 4.04/1.01      ( sK2(sK5) = sK4 | sK5 = k1_xboole_0 ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_1053,c_2883]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_29,negated_conjecture,
% 4.04/1.01      ( k1_xboole_0 != sK5 ),
% 4.04/1.01      inference(cnf_transformation,[],[f81]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_39,plain,
% 4.04/1.01      ( ~ r2_hidden(k1_xboole_0,k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 4.04/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 4.04/1.01      inference(instantiation,[status(thm)],[c_25]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_24,plain,
% 4.04/1.01      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
% 4.04/1.01      inference(cnf_transformation,[],[f120]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_42,plain,
% 4.04/1.01      ( r2_hidden(k1_xboole_0,k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 4.04/1.01      inference(instantiation,[status(thm)],[c_24]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_544,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1109,plain,
% 4.04/1.01      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 4.04/1.01      inference(instantiation,[status(thm)],[c_544]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1110,plain,
% 4.04/1.01      ( sK5 != k1_xboole_0
% 4.04/1.01      | k1_xboole_0 = sK5
% 4.04/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 4.04/1.01      inference(instantiation,[status(thm)],[c_1109]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_2923,plain,
% 4.04/1.01      ( sK2(sK5) = sK4 ),
% 4.04/1.01      inference(global_propositional_subsumption,
% 4.04/1.01                [status(thm)],
% 4.04/1.01                [c_2922,c_29,c_39,c_42,c_1110]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_2925,plain,
% 4.04/1.01      ( sK5 = k1_xboole_0 | r2_hidden(sK4,sK5) = iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_2923,c_1053]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_2964,plain,
% 4.04/1.01      ( r2_hidden(sK4,sK5) = iProver_top ),
% 4.04/1.01      inference(global_propositional_subsumption,
% 4.04/1.01                [status(thm)],
% 4.04/1.01                [c_2925,c_29,c_39,c_42,c_1110]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_26,plain,
% 4.04/1.01      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~ r2_hidden(X0,X1) ),
% 4.04/1.01      inference(cnf_transformation,[],[f108]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1044,plain,
% 4.04/1.01      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top
% 4.04/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_21,plain,
% 4.04/1.01      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
% 4.04/1.01      inference(cnf_transformation,[],[f103]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1049,plain,
% 4.04/1.01      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_2196,plain,
% 4.04/1.01      ( r1_tarski(sK5,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_31,c_1049]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_14,plain,
% 4.04/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.04/1.01      inference(cnf_transformation,[],[f60]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1052,plain,
% 4.04/1.01      ( X0 = X1
% 4.04/1.01      | r1_tarski(X0,X1) != iProver_top
% 4.04/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_2770,plain,
% 4.04/1.01      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5
% 4.04/1.01      | r1_tarski(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_2196,c_1052]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_2777,plain,
% 4.04/1.01      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5
% 4.04/1.01      | r2_hidden(sK4,sK5) != iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_1044,c_2770]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_2969,plain,
% 4.04/1.01      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = sK5 ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_2964,c_2777]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_2974,plain,
% 4.04/1.01      ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) = sK5 ),
% 4.04/1.01      inference(demodulation,[status(thm)],[c_2969,c_31]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_4,plain,
% 4.04/1.01      ( ~ r2_hidden(X0,X1)
% 4.04/1.01      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
% 4.04/1.01      inference(cnf_transformation,[],[f111]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1062,plain,
% 4.04/1.01      ( r2_hidden(X0,X1) != iProver_top
% 4.04/1.01      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_3174,plain,
% 4.04/1.01      ( r2_hidden(X0,sK5) = iProver_top
% 4.04/1.01      | r2_hidden(X0,sK6) != iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_2974,c_1062]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_5203,plain,
% 4.04/1.01      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = sK6
% 4.04/1.01      | r2_hidden(sK0(X0,X1,sK6),X1) = iProver_top
% 4.04/1.01      | r2_hidden(sK0(X0,X1,sK6),X0) = iProver_top
% 4.04/1.01      | r2_hidden(sK0(X0,X1,sK6),sK5) = iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_1063,c_3174]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_6746,plain,
% 4.04/1.01      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,sK6)) = sK6
% 4.04/1.01      | r2_hidden(sK0(X0,sK6,sK6),X0) = iProver_top
% 4.04/1.01      | r2_hidden(sK0(X0,sK6,sK6),sK5) = iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_5203,c_3174]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_6808,plain,
% 4.04/1.01      ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) = sK6
% 4.04/1.01      | r2_hidden(sK0(sK5,sK6,sK6),sK5) = iProver_top
% 4.04/1.01      | iProver_top != iProver_top ),
% 4.04/1.01      inference(equality_factoring,[status(thm)],[c_6746]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_6810,plain,
% 4.04/1.01      ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) = sK6
% 4.04/1.01      | r2_hidden(sK0(sK5,sK6,sK6),sK5) = iProver_top ),
% 4.04/1.01      inference(equality_resolution_simp,[status(thm)],[c_6808]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_6811,plain,
% 4.04/1.01      ( sK5 = sK6 | r2_hidden(sK0(sK5,sK6,sK6),sK5) = iProver_top ),
% 4.04/1.01      inference(demodulation,[status(thm)],[c_6810,c_2974]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_30,negated_conjecture,
% 4.04/1.01      ( sK5 != sK6 ),
% 4.04/1.01      inference(cnf_transformation,[],[f80]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_6892,plain,
% 4.04/1.01      ( r2_hidden(sK0(sK5,sK6,sK6),sK5) = iProver_top ),
% 4.04/1.01      inference(global_propositional_subsumption,
% 4.04/1.01                [status(thm)],
% 4.04/1.01                [c_6811,c_30]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_6896,plain,
% 4.04/1.01      ( sK0(sK5,sK6,sK6) = sK4 ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_6892,c_2883]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1,plain,
% 4.04/1.01      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 4.04/1.01      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 4.04/1.01      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2 ),
% 4.04/1.01      inference(cnf_transformation,[],[f88]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1065,plain,
% 4.04/1.01      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X2
% 4.04/1.01      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 4.04/1.01      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
% 4.04/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_6898,plain,
% 4.04/1.01      ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) = sK6
% 4.04/1.01      | r2_hidden(sK0(sK5,sK6,sK6),sK6) != iProver_top
% 4.04/1.01      | r2_hidden(sK4,sK6) != iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_6896,c_1065]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_6914,plain,
% 4.04/1.01      ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,sK6)) = sK6
% 4.04/1.01      | r2_hidden(sK4,sK6) != iProver_top ),
% 4.04/1.01      inference(light_normalisation,[status(thm)],[c_6898,c_6896]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_6915,plain,
% 4.04/1.01      ( sK5 = sK6 | r2_hidden(sK4,sK6) != iProver_top ),
% 4.04/1.01      inference(demodulation,[status(thm)],[c_6914,c_2974]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_3250,plain,
% 4.04/1.01      ( sK6 = k1_xboole_0 | r2_hidden(sK2(sK6),sK5) = iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_1053,c_3174]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_28,negated_conjecture,
% 4.04/1.01      ( k1_xboole_0 != sK6 ),
% 4.04/1.01      inference(cnf_transformation,[],[f82]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1098,plain,
% 4.04/1.01      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 4.04/1.01      inference(instantiation,[status(thm)],[c_544]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_1099,plain,
% 4.04/1.01      ( sK6 != k1_xboole_0
% 4.04/1.01      | k1_xboole_0 = sK6
% 4.04/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 4.04/1.01      inference(instantiation,[status(thm)],[c_1098]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_3363,plain,
% 4.04/1.01      ( r2_hidden(sK2(sK6),sK5) = iProver_top ),
% 4.04/1.01      inference(global_propositional_subsumption,
% 4.04/1.01                [status(thm)],
% 4.04/1.01                [c_3250,c_28,c_39,c_42,c_1099]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_3367,plain,
% 4.04/1.01      ( sK2(sK6) = sK4 ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_3363,c_2883]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(c_3463,plain,
% 4.04/1.01      ( sK6 = k1_xboole_0 | r2_hidden(sK4,sK6) = iProver_top ),
% 4.04/1.01      inference(superposition,[status(thm)],[c_3367,c_1053]) ).
% 4.04/1.01  
% 4.04/1.01  cnf(contradiction,plain,
% 4.04/1.01      ( $false ),
% 4.04/1.01      inference(minisat,
% 4.04/1.01                [status(thm)],
% 4.04/1.01                [c_6915,c_3463,c_1099,c_42,c_39,c_28,c_30]) ).
% 4.04/1.01  
% 4.04/1.01  
% 4.04/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 4.04/1.01  
% 4.04/1.01  ------                               Statistics
% 4.04/1.01  
% 4.04/1.01  ------ General
% 4.04/1.01  
% 4.04/1.01  abstr_ref_over_cycles:                  0
% 4.04/1.01  abstr_ref_under_cycles:                 0
% 4.04/1.01  gc_basic_clause_elim:                   0
% 4.04/1.01  forced_gc_time:                         0
% 4.04/1.01  parsing_time:                           0.009
% 4.04/1.01  unif_index_cands_time:                  0.
% 4.04/1.01  unif_index_add_time:                    0.
% 4.04/1.01  orderings_time:                         0.
% 4.04/1.01  out_proof_time:                         0.017
% 4.04/1.01  total_time:                             0.29
% 4.04/1.01  num_of_symbols:                         45
% 4.04/1.01  num_of_terms:                           9754
% 4.04/1.01  
% 4.04/1.01  ------ Preprocessing
% 4.04/1.01  
% 4.04/1.01  num_of_splits:                          0
% 4.04/1.01  num_of_split_atoms:                     0
% 4.04/1.01  num_of_reused_defs:                     0
% 4.04/1.01  num_eq_ax_congr_red:                    33
% 4.04/1.01  num_of_sem_filtered_clauses:            1
% 4.04/1.01  num_of_subtypes:                        0
% 4.04/1.01  monotx_restored_types:                  0
% 4.04/1.01  sat_num_of_epr_types:                   0
% 4.04/1.01  sat_num_of_non_cyclic_types:            0
% 4.04/1.01  sat_guarded_non_collapsed_types:        0
% 4.04/1.01  num_pure_diseq_elim:                    0
% 4.04/1.01  simp_replaced_by:                       0
% 4.04/1.01  res_preprocessed:                       141
% 4.04/1.01  prep_upred:                             0
% 4.04/1.01  prep_unflattend:                        0
% 4.04/1.01  smt_new_axioms:                         0
% 4.04/1.01  pred_elim_cands:                        2
% 4.04/1.01  pred_elim:                              0
% 4.04/1.01  pred_elim_cl:                           0
% 4.04/1.01  pred_elim_cycles:                       2
% 4.04/1.01  merged_defs:                            8
% 4.04/1.01  merged_defs_ncl:                        0
% 4.04/1.01  bin_hyper_res:                          8
% 4.04/1.01  prep_cycles:                            4
% 4.04/1.01  pred_elim_time:                         0.
% 4.04/1.01  splitting_time:                         0.
% 4.04/1.01  sem_filter_time:                        0.
% 4.04/1.01  monotx_time:                            0.
% 4.04/1.01  subtype_inf_time:                       0.
% 4.04/1.01  
% 4.04/1.01  ------ Problem properties
% 4.04/1.01  
% 4.04/1.01  clauses:                                31
% 4.04/1.01  conjectures:                            4
% 4.04/1.01  epr:                                    5
% 4.04/1.01  horn:                                   25
% 4.04/1.01  ground:                                 4
% 4.04/1.01  unary:                                  11
% 4.04/1.01  binary:                                 9
% 4.04/1.01  lits:                                   64
% 4.04/1.01  lits_eq:                                22
% 4.04/1.01  fd_pure:                                0
% 4.04/1.01  fd_pseudo:                              0
% 4.04/1.01  fd_cond:                                1
% 4.04/1.01  fd_pseudo_cond:                         9
% 4.04/1.01  ac_symbols:                             0
% 4.04/1.01  
% 4.04/1.01  ------ Propositional Solver
% 4.04/1.01  
% 4.04/1.01  prop_solver_calls:                      28
% 4.04/1.01  prop_fast_solver_calls:                 756
% 4.04/1.01  smt_solver_calls:                       0
% 4.04/1.01  smt_fast_solver_calls:                  0
% 4.04/1.01  prop_num_of_clauses:                    3729
% 4.04/1.01  prop_preprocess_simplified:             7904
% 4.04/1.01  prop_fo_subsumed:                       4
% 4.04/1.01  prop_solver_time:                       0.
% 4.04/1.01  smt_solver_time:                        0.
% 4.04/1.01  smt_fast_solver_time:                   0.
% 4.04/1.01  prop_fast_solver_time:                  0.
% 4.04/1.01  prop_unsat_core_time:                   0.
% 4.04/1.01  
% 4.04/1.01  ------ QBF
% 4.04/1.01  
% 4.04/1.01  qbf_q_res:                              0
% 4.04/1.01  qbf_num_tautologies:                    0
% 4.04/1.01  qbf_prep_cycles:                        0
% 4.04/1.01  
% 4.04/1.01  ------ BMC1
% 4.04/1.01  
% 4.04/1.01  bmc1_current_bound:                     -1
% 4.04/1.01  bmc1_last_solved_bound:                 -1
% 4.04/1.01  bmc1_unsat_core_size:                   -1
% 4.04/1.01  bmc1_unsat_core_parents_size:           -1
% 4.04/1.01  bmc1_merge_next_fun:                    0
% 4.04/1.01  bmc1_unsat_core_clauses_time:           0.
% 4.04/1.01  
% 4.04/1.01  ------ Instantiation
% 4.04/1.01  
% 4.04/1.01  inst_num_of_clauses:                    900
% 4.04/1.01  inst_num_in_passive:                    192
% 4.04/1.01  inst_num_in_active:                     280
% 4.04/1.01  inst_num_in_unprocessed:                428
% 4.04/1.01  inst_num_of_loops:                      350
% 4.04/1.01  inst_num_of_learning_restarts:          0
% 4.04/1.01  inst_num_moves_active_passive:          69
% 4.04/1.01  inst_lit_activity:                      0
% 4.04/1.01  inst_lit_activity_moves:                0
% 4.04/1.01  inst_num_tautologies:                   0
% 4.04/1.01  inst_num_prop_implied:                  0
% 4.04/1.01  inst_num_existing_simplified:           0
% 4.04/1.01  inst_num_eq_res_simplified:             0
% 4.04/1.01  inst_num_child_elim:                    0
% 4.04/1.01  inst_num_of_dismatching_blockings:      237
% 4.04/1.01  inst_num_of_non_proper_insts:           837
% 4.04/1.01  inst_num_of_duplicates:                 0
% 4.04/1.01  inst_inst_num_from_inst_to_res:         0
% 4.04/1.01  inst_dismatching_checking_time:         0.
% 4.04/1.01  
% 4.04/1.01  ------ Resolution
% 4.04/1.01  
% 4.04/1.01  res_num_of_clauses:                     0
% 4.04/1.01  res_num_in_passive:                     0
% 4.04/1.01  res_num_in_active:                      0
% 4.04/1.01  res_num_of_loops:                       145
% 4.04/1.01  res_forward_subset_subsumed:            62
% 4.04/1.01  res_backward_subset_subsumed:           0
% 4.04/1.01  res_forward_subsumed:                   0
% 4.04/1.01  res_backward_subsumed:                  0
% 4.04/1.01  res_forward_subsumption_resolution:     0
% 4.04/1.01  res_backward_subsumption_resolution:    0
% 4.04/1.01  res_clause_to_clause_subsumption:       775
% 4.04/1.01  res_orphan_elimination:                 0
% 4.04/1.01  res_tautology_del:                      25
% 4.04/1.01  res_num_eq_res_simplified:              0
% 4.04/1.01  res_num_sel_changes:                    0
% 4.04/1.01  res_moves_from_active_to_pass:          0
% 4.04/1.01  
% 4.04/1.01  ------ Superposition
% 4.04/1.01  
% 4.04/1.01  sup_time_total:                         0.
% 4.04/1.01  sup_time_generating:                    0.
% 4.04/1.01  sup_time_sim_full:                      0.
% 4.04/1.01  sup_time_sim_immed:                     0.
% 4.04/1.01  
% 4.04/1.01  sup_num_of_clauses:                     215
% 4.04/1.01  sup_num_in_active:                      60
% 4.04/1.01  sup_num_in_passive:                     155
% 4.04/1.01  sup_num_of_loops:                       69
% 4.04/1.01  sup_fw_superposition:                   64
% 4.04/1.01  sup_bw_superposition:                   227
% 4.04/1.01  sup_immediate_simplified:               84
% 4.04/1.01  sup_given_eliminated:                   0
% 4.04/1.01  comparisons_done:                       0
% 4.04/1.01  comparisons_avoided:                    35
% 4.04/1.01  
% 4.04/1.01  ------ Simplifications
% 4.04/1.01  
% 4.04/1.01  
% 4.04/1.01  sim_fw_subset_subsumed:                 34
% 4.04/1.01  sim_bw_subset_subsumed:                 2
% 4.04/1.01  sim_fw_subsumed:                        8
% 4.04/1.01  sim_bw_subsumed:                        1
% 4.04/1.01  sim_fw_subsumption_res:                 0
% 4.04/1.01  sim_bw_subsumption_res:                 0
% 4.04/1.01  sim_tautology_del:                      35
% 4.04/1.01  sim_eq_tautology_del:                   15
% 4.04/1.01  sim_eq_res_simp:                        26
% 4.04/1.01  sim_fw_demodulated:                     43
% 4.04/1.01  sim_bw_demodulated:                     9
% 4.04/1.01  sim_light_normalised:                   14
% 4.04/1.01  sim_joinable_taut:                      0
% 4.04/1.01  sim_joinable_simp:                      0
% 4.04/1.01  sim_ac_normalised:                      0
% 4.04/1.01  sim_smt_subsumption:                    0
% 4.04/1.01  
%------------------------------------------------------------------------------
