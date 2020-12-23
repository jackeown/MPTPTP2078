%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:08 EST 2020

% Result     : Theorem 7.61s
% Output     : CNFRefutation 7.61s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 751 expanded)
%              Number of clauses        :   57 ( 163 expanded)
%              Number of leaves         :   19 ( 211 expanded)
%              Depth                    :   17
%              Number of atoms          :  452 (2521 expanded)
%              Number of equality atoms :  207 (1261 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f44,f51])).

fof(f113,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f88])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f87,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f45,f51])).

fof(f112,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f87])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f55,f51])).

fof(f90,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f53,f51,f78])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f46,f51])).

fof(f111,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
        & ( r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) )
   => ( ( ~ r2_hidden(sK4,sK5)
        | k4_xboole_0(k1_tarski(sK4),sK5) != k1_xboole_0 )
      & ( r2_hidden(sK4,sK5)
        | k4_xboole_0(k1_tarski(sK4),sK5) = k1_xboole_0 ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( ~ r2_hidden(sK4,sK5)
      | k4_xboole_0(k1_tarski(sK4),sK5) != k1_xboole_0 )
    & ( r2_hidden(sK4,sK5)
      | k4_xboole_0(k1_tarski(sK4),sK5) = k1_xboole_0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f41])).

fof(f76,plain,
    ( r2_hidden(sK4,sK5)
    | k4_xboole_0(k1_tarski(sK4),sK5) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f66,f79])).

fof(f110,plain,
    ( r2_hidden(sK4,sK5)
    | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f76,f51,f80])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f101,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f60,f79])).

fof(f121,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f101])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f100,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f61,f79])).

fof(f119,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f100])).

fof(f120,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f119])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f91,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f54,f51])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f38])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) ) ),
    inference(definition_unfolding,[],[f74,f51,f80])).

fof(f122,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) ),
    inference(equality_resolution,[],[f107])).

fof(f77,plain,
    ( ~ r2_hidden(sK4,sK5)
    | k4_xboole_0(k1_tarski(sK4),sK5) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

fof(f109,plain,
    ( ~ r2_hidden(sK4,sK5)
    | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f77,f51,f80])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f47,f51])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f56,f80])).

fof(f116,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f95])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f48,f51])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_23316,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_23318,plain,
    ( ~ r2_hidden(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))))
    | r2_hidden(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_23316])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_23309,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))
    | ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_23311,plain,
    ( ~ r2_hidden(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))))
    | ~ r2_hidden(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4)))) ),
    inference(instantiation,[status(thm)],[c_23309])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_913,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_10309,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_913])).

cnf(c_10331,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))
    | r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10309])).

cnf(c_10333,plain,
    ( r2_hidden(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))
    | ~ r2_hidden(sK4,sK4)
    | r2_hidden(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10331])).

cnf(c_342,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_338,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2372,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_342,c_338])).

cnf(c_339,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1305,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_339,c_338])).

cnf(c_29,negated_conjecture,
    ( r2_hidden(sK4,sK5)
    | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1301,plain,
    ( r2_hidden(sK4,sK5)
    | X0 != k1_xboole_0
    | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = X0 ),
    inference(resolution,[status(thm)],[c_339,c_29])).

cnf(c_6642,plain,
    ( r2_hidden(sK4,sK5)
    | X0 = k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5))
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1305,c_1301])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_52,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_19,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_55,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1200,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
    | r2_hidden(X0,k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1610,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK4,k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)))
    | r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1200])).

cnf(c_10,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_896,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1662,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_896])).

cnf(c_1664,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1662])).

cnf(c_1666,plain,
    ( ~ r2_hidden(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1664])).

cnf(c_6636,plain,
    ( r2_hidden(sK4,sK5)
    | k1_xboole_0 = k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_1305,c_29])).

cnf(c_6688,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)))
    | r2_hidden(X1,k1_xboole_0)
    | r2_hidden(sK4,sK5)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_6636,c_342])).

cnf(c_6690,plain,
    ( ~ r2_hidden(sK4,k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)))
    | r2_hidden(sK4,sK5)
    | r2_hidden(sK4,k1_xboole_0)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_6688])).

cnf(c_6694,plain,
    ( r2_hidden(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6642,c_52,c_55,c_1610,c_1666,c_6690])).

cnf(c_28,negated_conjecture,
    ( ~ r2_hidden(sK4,sK5)
    | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_7379,plain,
    ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_6694,c_28])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2370,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)))
    | ~ r2_hidden(X1,k1_xboole_0)
    | r2_hidden(sK4,sK5)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_342,c_29])).

cnf(c_2491,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)))
    | ~ r2_hidden(X0,k1_xboole_0)
    | r2_hidden(sK4,sK5) ),
    inference(resolution,[status(thm)],[c_2370,c_338])).

cnf(c_2526,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2491,c_1664])).

cnf(c_3243,plain,
    ( r2_hidden(sK0(X0,X1,k1_xboole_0),X0)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_2526])).

cnf(c_7385,plain,
    ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(resolution,[status(thm)],[c_7379,c_3243])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_7391,plain,
    ( sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0) = sK4 ),
    inference(resolution,[status(thm)],[c_7385,c_14])).

cnf(c_8146,plain,
    ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0),X0)
    | ~ r2_hidden(sK4,X0) ),
    inference(resolution,[status(thm)],[c_2372,c_7391])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_8982,plain,
    ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK4,sK5)
    | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8146,c_3])).

cnf(c_4764,plain,
    ( X0 != X1
    | X0 = sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0)
    | sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0) != X1 ),
    inference(instantiation,[status(thm)],[c_339])).

cnf(c_4765,plain,
    ( sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0) != sK4
    | sK4 = sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4764])).

cnf(c_1002,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4)))
    | X2 != X0
    | k5_xboole_0(X3,k3_xboole_0(X3,X4)) != X1 ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_1451,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))
    | ~ r2_hidden(X3,k1_xboole_0)
    | X0 != X3
    | k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1002])).

cnf(c_3385,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))
    | ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0),k1_xboole_0)
    | X0 != sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0)
    | k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1451])).

cnf(c_3387,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))))
    | k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))) != k1_xboole_0
    | sK4 != sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3385])).

cnf(c_74,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23318,c_23311,c_10333,c_8982,c_7391,c_6694,c_4765,c_3387,c_1666,c_74,c_55,c_52,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:46:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.61/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.61/1.49  
% 7.61/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.61/1.49  
% 7.61/1.49  ------  iProver source info
% 7.61/1.49  
% 7.61/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.61/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.61/1.49  git: non_committed_changes: false
% 7.61/1.49  git: last_make_outside_of_git: false
% 7.61/1.49  
% 7.61/1.49  ------ 
% 7.61/1.49  ------ Parsing...
% 7.61/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.61/1.49  
% 7.61/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.61/1.49  
% 7.61/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.61/1.49  
% 7.61/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.61/1.49  ------ Proving...
% 7.61/1.49  ------ Problem Properties 
% 7.61/1.49  
% 7.61/1.49  
% 7.61/1.49  clauses                                 30
% 7.61/1.49  conjectures                             2
% 7.61/1.49  EPR                                     0
% 7.61/1.49  Horn                                    18
% 7.61/1.49  unary                                   9
% 7.61/1.49  binary                                  8
% 7.61/1.49  lits                                    66
% 7.61/1.49  lits eq                                 32
% 7.61/1.49  fd_pure                                 0
% 7.61/1.50  fd_pseudo                               0
% 7.61/1.50  fd_cond                                 0
% 7.61/1.50  fd_pseudo_cond                          11
% 7.61/1.50  AC symbols                              0
% 7.61/1.50  
% 7.61/1.50  ------ Input Options Time Limit: Unbounded
% 7.61/1.50  
% 7.61/1.50  
% 7.61/1.50  ------ 
% 7.61/1.50  Current options:
% 7.61/1.50  ------ 
% 7.61/1.50  
% 7.61/1.50  
% 7.61/1.50  
% 7.61/1.50  
% 7.61/1.50  ------ Proving...
% 7.61/1.50  
% 7.61/1.50  
% 7.61/1.50  % SZS status Theorem for theBenchmark.p
% 7.61/1.50  
% 7.61/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.61/1.50  
% 7.61/1.50  fof(f2,axiom,(
% 7.61/1.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.61/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.50  
% 7.61/1.50  fof(f21,plain,(
% 7.61/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.61/1.50    inference(nnf_transformation,[],[f2])).
% 7.61/1.50  
% 7.61/1.50  fof(f22,plain,(
% 7.61/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.61/1.50    inference(flattening,[],[f21])).
% 7.61/1.50  
% 7.61/1.50  fof(f23,plain,(
% 7.61/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.61/1.50    inference(rectify,[],[f22])).
% 7.61/1.50  
% 7.61/1.50  fof(f24,plain,(
% 7.61/1.50    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.61/1.50    introduced(choice_axiom,[])).
% 7.61/1.50  
% 7.61/1.50  fof(f25,plain,(
% 7.61/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.61/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 7.61/1.50  
% 7.61/1.50  fof(f44,plain,(
% 7.61/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.61/1.50    inference(cnf_transformation,[],[f25])).
% 7.61/1.50  
% 7.61/1.50  fof(f4,axiom,(
% 7.61/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.61/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.50  
% 7.61/1.50  fof(f51,plain,(
% 7.61/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.61/1.50    inference(cnf_transformation,[],[f4])).
% 7.61/1.50  
% 7.61/1.50  fof(f88,plain,(
% 7.61/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 7.61/1.50    inference(definition_unfolding,[],[f44,f51])).
% 7.61/1.50  
% 7.61/1.50  fof(f113,plain,(
% 7.61/1.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 7.61/1.50    inference(equality_resolution,[],[f88])).
% 7.61/1.50  
% 7.61/1.50  fof(f45,plain,(
% 7.61/1.50    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.61/1.50    inference(cnf_transformation,[],[f25])).
% 7.61/1.50  
% 7.61/1.50  fof(f87,plain,(
% 7.61/1.50    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 7.61/1.50    inference(definition_unfolding,[],[f45,f51])).
% 7.61/1.50  
% 7.61/1.50  fof(f112,plain,(
% 7.61/1.50    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 7.61/1.50    inference(equality_resolution,[],[f87])).
% 7.61/1.50  
% 7.61/1.50  fof(f6,axiom,(
% 7.61/1.50    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 7.61/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.50  
% 7.61/1.50  fof(f53,plain,(
% 7.61/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 7.61/1.50    inference(cnf_transformation,[],[f6])).
% 7.61/1.50  
% 7.61/1.50  fof(f8,axiom,(
% 7.61/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.61/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.50  
% 7.61/1.50  fof(f55,plain,(
% 7.61/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.61/1.50    inference(cnf_transformation,[],[f8])).
% 7.61/1.50  
% 7.61/1.50  fof(f78,plain,(
% 7.61/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 7.61/1.50    inference(definition_unfolding,[],[f55,f51])).
% 7.61/1.50  
% 7.61/1.50  fof(f90,plain,(
% 7.61/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0) )),
% 7.61/1.50    inference(definition_unfolding,[],[f53,f51,f78])).
% 7.61/1.50  
% 7.61/1.50  fof(f46,plain,(
% 7.61/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 7.61/1.50    inference(cnf_transformation,[],[f25])).
% 7.61/1.50  
% 7.61/1.50  fof(f86,plain,(
% 7.61/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 7.61/1.50    inference(definition_unfolding,[],[f46,f51])).
% 7.61/1.50  
% 7.61/1.50  fof(f111,plain,(
% 7.61/1.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 7.61/1.50    inference(equality_resolution,[],[f86])).
% 7.61/1.50  
% 7.61/1.50  fof(f17,conjecture,(
% 7.61/1.50    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 7.61/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.50  
% 7.61/1.50  fof(f18,negated_conjecture,(
% 7.61/1.50    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 7.61/1.50    inference(negated_conjecture,[],[f17])).
% 7.61/1.50  
% 7.61/1.50  fof(f20,plain,(
% 7.61/1.50    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <~> r2_hidden(X0,X1))),
% 7.61/1.50    inference(ennf_transformation,[],[f18])).
% 7.61/1.50  
% 7.61/1.50  fof(f40,plain,(
% 7.61/1.50    ? [X0,X1] : ((~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0))),
% 7.61/1.50    inference(nnf_transformation,[],[f20])).
% 7.61/1.50  
% 7.61/1.50  fof(f41,plain,(
% 7.61/1.50    ? [X0,X1] : ((~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0)) => ((~r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) != k1_xboole_0) & (r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) = k1_xboole_0))),
% 7.61/1.50    introduced(choice_axiom,[])).
% 7.61/1.50  
% 7.61/1.50  fof(f42,plain,(
% 7.61/1.50    (~r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) != k1_xboole_0) & (r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) = k1_xboole_0)),
% 7.61/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f41])).
% 7.61/1.50  
% 7.61/1.50  fof(f76,plain,(
% 7.61/1.50    r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) = k1_xboole_0),
% 7.61/1.50    inference(cnf_transformation,[],[f42])).
% 7.61/1.50  
% 7.61/1.50  fof(f11,axiom,(
% 7.61/1.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.61/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.50  
% 7.61/1.50  fof(f66,plain,(
% 7.61/1.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.61/1.50    inference(cnf_transformation,[],[f11])).
% 7.61/1.50  
% 7.61/1.50  fof(f12,axiom,(
% 7.61/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.61/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.50  
% 7.61/1.50  fof(f67,plain,(
% 7.61/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.61/1.50    inference(cnf_transformation,[],[f12])).
% 7.61/1.50  
% 7.61/1.50  fof(f13,axiom,(
% 7.61/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.61/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.50  
% 7.61/1.50  fof(f68,plain,(
% 7.61/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.61/1.50    inference(cnf_transformation,[],[f13])).
% 7.61/1.50  
% 7.61/1.50  fof(f79,plain,(
% 7.61/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.61/1.50    inference(definition_unfolding,[],[f67,f68])).
% 7.61/1.50  
% 7.61/1.50  fof(f80,plain,(
% 7.61/1.50    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.61/1.50    inference(definition_unfolding,[],[f66,f79])).
% 7.61/1.50  
% 7.61/1.50  fof(f110,plain,(
% 7.61/1.50    r2_hidden(sK4,sK5) | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k1_xboole_0),
% 7.61/1.50    inference(definition_unfolding,[],[f76,f51,f80])).
% 7.61/1.50  
% 7.61/1.50  fof(f10,axiom,(
% 7.61/1.50    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.61/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.50  
% 7.61/1.50  fof(f30,plain,(
% 7.61/1.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.61/1.50    inference(nnf_transformation,[],[f10])).
% 7.61/1.50  
% 7.61/1.50  fof(f31,plain,(
% 7.61/1.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.61/1.50    inference(flattening,[],[f30])).
% 7.61/1.50  
% 7.61/1.50  fof(f32,plain,(
% 7.61/1.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.61/1.50    inference(rectify,[],[f31])).
% 7.61/1.50  
% 7.61/1.50  fof(f33,plain,(
% 7.61/1.50    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 7.61/1.50    introduced(choice_axiom,[])).
% 7.61/1.50  
% 7.61/1.50  fof(f34,plain,(
% 7.61/1.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.61/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 7.61/1.50  
% 7.61/1.50  fof(f60,plain,(
% 7.61/1.50    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 7.61/1.50    inference(cnf_transformation,[],[f34])).
% 7.61/1.50  
% 7.61/1.50  fof(f101,plain,(
% 7.61/1.50    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.61/1.50    inference(definition_unfolding,[],[f60,f79])).
% 7.61/1.50  
% 7.61/1.50  fof(f121,plain,(
% 7.61/1.50    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 7.61/1.50    inference(equality_resolution,[],[f101])).
% 7.61/1.50  
% 7.61/1.50  fof(f61,plain,(
% 7.61/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.61/1.50    inference(cnf_transformation,[],[f34])).
% 7.61/1.50  
% 7.61/1.50  fof(f100,plain,(
% 7.61/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.61/1.50    inference(definition_unfolding,[],[f61,f79])).
% 7.61/1.50  
% 7.61/1.50  fof(f119,plain,(
% 7.61/1.50    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 7.61/1.50    inference(equality_resolution,[],[f100])).
% 7.61/1.50  
% 7.61/1.50  fof(f120,plain,(
% 7.61/1.50    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 7.61/1.50    inference(equality_resolution,[],[f119])).
% 7.61/1.50  
% 7.61/1.50  fof(f7,axiom,(
% 7.61/1.50    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 7.61/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.50  
% 7.61/1.50  fof(f54,plain,(
% 7.61/1.50    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 7.61/1.50    inference(cnf_transformation,[],[f7])).
% 7.61/1.50  
% 7.61/1.50  fof(f91,plain,(
% 7.61/1.50    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0) )),
% 7.61/1.50    inference(definition_unfolding,[],[f54,f51])).
% 7.61/1.50  
% 7.61/1.50  fof(f16,axiom,(
% 7.61/1.50    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 7.61/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.50  
% 7.61/1.50  fof(f38,plain,(
% 7.61/1.50    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 7.61/1.50    inference(nnf_transformation,[],[f16])).
% 7.61/1.50  
% 7.61/1.50  fof(f39,plain,(
% 7.61/1.50    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 7.61/1.50    inference(flattening,[],[f38])).
% 7.61/1.50  
% 7.61/1.50  fof(f74,plain,(
% 7.61/1.50    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 7.61/1.50    inference(cnf_transformation,[],[f39])).
% 7.61/1.50  
% 7.61/1.50  fof(f107,plain,(
% 7.61/1.50    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))))) )),
% 7.61/1.50    inference(definition_unfolding,[],[f74,f51,f80])).
% 7.61/1.50  
% 7.61/1.50  fof(f122,plain,(
% 7.61/1.50    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))))) )),
% 7.61/1.50    inference(equality_resolution,[],[f107])).
% 7.61/1.50  
% 7.61/1.50  fof(f77,plain,(
% 7.61/1.50    ~r2_hidden(sK4,sK5) | k4_xboole_0(k1_tarski(sK4),sK5) != k1_xboole_0),
% 7.61/1.50    inference(cnf_transformation,[],[f42])).
% 7.61/1.50  
% 7.61/1.50  fof(f109,plain,(
% 7.61/1.50    ~r2_hidden(sK4,sK5) | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_xboole_0),
% 7.61/1.50    inference(definition_unfolding,[],[f77,f51,f80])).
% 7.61/1.50  
% 7.61/1.50  fof(f47,plain,(
% 7.61/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.61/1.50    inference(cnf_transformation,[],[f25])).
% 7.61/1.50  
% 7.61/1.50  fof(f85,plain,(
% 7.61/1.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.61/1.50    inference(definition_unfolding,[],[f47,f51])).
% 7.61/1.50  
% 7.61/1.50  fof(f9,axiom,(
% 7.61/1.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.61/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.61/1.50  
% 7.61/1.50  fof(f26,plain,(
% 7.61/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.61/1.50    inference(nnf_transformation,[],[f9])).
% 7.61/1.50  
% 7.61/1.50  fof(f27,plain,(
% 7.61/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.61/1.50    inference(rectify,[],[f26])).
% 7.61/1.50  
% 7.61/1.50  fof(f28,plain,(
% 7.61/1.50    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 7.61/1.50    introduced(choice_axiom,[])).
% 7.61/1.50  
% 7.61/1.50  fof(f29,plain,(
% 7.61/1.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.61/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 7.61/1.50  
% 7.61/1.50  fof(f56,plain,(
% 7.61/1.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.61/1.50    inference(cnf_transformation,[],[f29])).
% 7.61/1.50  
% 7.61/1.50  fof(f95,plain,(
% 7.61/1.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 7.61/1.50    inference(definition_unfolding,[],[f56,f80])).
% 7.61/1.50  
% 7.61/1.50  fof(f116,plain,(
% 7.61/1.50    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 7.61/1.50    inference(equality_resolution,[],[f95])).
% 7.61/1.50  
% 7.61/1.50  fof(f48,plain,(
% 7.61/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.61/1.50    inference(cnf_transformation,[],[f25])).
% 7.61/1.50  
% 7.61/1.50  fof(f84,plain,(
% 7.61/1.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.61/1.50    inference(definition_unfolding,[],[f48,f51])).
% 7.61/1.50  
% 7.61/1.50  cnf(c_7,plain,
% 7.61/1.50      ( r2_hidden(X0,X1)
% 7.61/1.50      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.61/1.50      inference(cnf_transformation,[],[f113]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_23316,plain,
% 7.61/1.50      ( r2_hidden(X0,X1)
% 7.61/1.50      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))) ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_23318,plain,
% 7.61/1.50      ( ~ r2_hidden(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))))
% 7.61/1.50      | r2_hidden(sK4,sK4) ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_23316]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_6,plain,
% 7.61/1.50      ( ~ r2_hidden(X0,X1)
% 7.61/1.50      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 7.61/1.50      inference(cnf_transformation,[],[f112]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_23309,plain,
% 7.61/1.50      ( ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))
% 7.61/1.50      | ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_23311,plain,
% 7.61/1.50      ( ~ r2_hidden(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))))
% 7.61/1.50      | ~ r2_hidden(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4)))) ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_23309]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_9,plain,
% 7.61/1.50      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
% 7.61/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_5,plain,
% 7.61/1.50      ( ~ r2_hidden(X0,X1)
% 7.61/1.50      | r2_hidden(X0,X2)
% 7.61/1.50      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.61/1.50      inference(cnf_transformation,[],[f111]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_913,plain,
% 7.61/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.61/1.50      | r2_hidden(X0,X2) = iProver_top
% 7.61/1.50      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_10309,plain,
% 7.61/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.61/1.50      | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = iProver_top
% 7.61/1.50      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_9,c_913]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_10331,plain,
% 7.61/1.50      ( ~ r2_hidden(X0,X1)
% 7.61/1.50      | r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))
% 7.61/1.50      | r2_hidden(X0,k1_xboole_0) ),
% 7.61/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_10309]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_10333,plain,
% 7.61/1.50      ( r2_hidden(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))
% 7.61/1.50      | ~ r2_hidden(sK4,sK4)
% 7.61/1.50      | r2_hidden(sK4,k1_xboole_0) ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_10331]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_342,plain,
% 7.61/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.61/1.50      theory(equality) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_338,plain,( X0 = X0 ),theory(equality) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_2372,plain,
% 7.61/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 7.61/1.50      inference(resolution,[status(thm)],[c_342,c_338]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_339,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1305,plain,
% 7.61/1.50      ( X0 != X1 | X1 = X0 ),
% 7.61/1.50      inference(resolution,[status(thm)],[c_339,c_338]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_29,negated_conjecture,
% 7.61/1.50      ( r2_hidden(sK4,sK5)
% 7.61/1.50      | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k1_xboole_0 ),
% 7.61/1.50      inference(cnf_transformation,[],[f110]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1301,plain,
% 7.61/1.50      ( r2_hidden(sK4,sK5)
% 7.61/1.50      | X0 != k1_xboole_0
% 7.61/1.50      | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = X0 ),
% 7.61/1.50      inference(resolution,[status(thm)],[c_339,c_29]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_6642,plain,
% 7.61/1.50      ( r2_hidden(sK4,sK5)
% 7.61/1.50      | X0 = k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5))
% 7.61/1.50      | X0 != k1_xboole_0 ),
% 7.61/1.50      inference(resolution,[status(thm)],[c_1305,c_1301]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_20,plain,
% 7.61/1.50      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 7.61/1.50      inference(cnf_transformation,[],[f121]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_52,plain,
% 7.61/1.50      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) | sK4 = sK4 ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_20]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_19,plain,
% 7.61/1.50      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 7.61/1.50      inference(cnf_transformation,[],[f120]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_55,plain,
% 7.61/1.50      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_19]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1200,plain,
% 7.61/1.50      ( r2_hidden(X0,X1)
% 7.61/1.50      | ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))
% 7.61/1.50      | r2_hidden(X0,k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))) ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1610,plain,
% 7.61/1.50      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
% 7.61/1.50      | r2_hidden(sK4,k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)))
% 7.61/1.50      | r2_hidden(sK4,sK5) ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_1200]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_10,plain,
% 7.61/1.50      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 7.61/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_26,plain,
% 7.61/1.50      ( ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) ),
% 7.61/1.50      inference(cnf_transformation,[],[f122]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_896,plain,
% 7.61/1.50      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) != iProver_top ),
% 7.61/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1662,plain,
% 7.61/1.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.61/1.50      inference(superposition,[status(thm)],[c_10,c_896]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1664,plain,
% 7.61/1.50      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 7.61/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_1662]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1666,plain,
% 7.61/1.50      ( ~ r2_hidden(sK4,k1_xboole_0) ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_1664]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_6636,plain,
% 7.61/1.50      ( r2_hidden(sK4,sK5)
% 7.61/1.50      | k1_xboole_0 = k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) ),
% 7.61/1.50      inference(resolution,[status(thm)],[c_1305,c_29]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_6688,plain,
% 7.61/1.50      ( ~ r2_hidden(X0,k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)))
% 7.61/1.50      | r2_hidden(X1,k1_xboole_0)
% 7.61/1.50      | r2_hidden(sK4,sK5)
% 7.61/1.50      | X1 != X0 ),
% 7.61/1.50      inference(resolution,[status(thm)],[c_6636,c_342]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_6690,plain,
% 7.61/1.50      ( ~ r2_hidden(sK4,k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)))
% 7.61/1.50      | r2_hidden(sK4,sK5)
% 7.61/1.50      | r2_hidden(sK4,k1_xboole_0)
% 7.61/1.50      | sK4 != sK4 ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_6688]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_6694,plain,
% 7.61/1.50      ( r2_hidden(sK4,sK5) ),
% 7.61/1.50      inference(global_propositional_subsumption,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_6642,c_52,c_55,c_1610,c_1666,c_6690]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_28,negated_conjecture,
% 7.61/1.50      ( ~ r2_hidden(sK4,sK5)
% 7.61/1.50      | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_xboole_0 ),
% 7.61/1.50      inference(cnf_transformation,[],[f109]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_7379,plain,
% 7.61/1.50      ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_xboole_0 ),
% 7.61/1.50      inference(backward_subsumption_resolution,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_6694,c_28]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_4,plain,
% 7.61/1.50      ( r2_hidden(sK0(X0,X1,X2),X0)
% 7.61/1.50      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.61/1.50      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 7.61/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_2370,plain,
% 7.61/1.50      ( r2_hidden(X0,k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)))
% 7.61/1.50      | ~ r2_hidden(X1,k1_xboole_0)
% 7.61/1.50      | r2_hidden(sK4,sK5)
% 7.61/1.50      | X0 != X1 ),
% 7.61/1.50      inference(resolution,[status(thm)],[c_342,c_29]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_2491,plain,
% 7.61/1.50      ( r2_hidden(X0,k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)))
% 7.61/1.50      | ~ r2_hidden(X0,k1_xboole_0)
% 7.61/1.50      | r2_hidden(sK4,sK5) ),
% 7.61/1.50      inference(resolution,[status(thm)],[c_2370,c_338]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_2526,plain,
% 7.61/1.50      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 7.61/1.50      inference(global_propositional_subsumption,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_2491,c_1664]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_3243,plain,
% 7.61/1.50      ( r2_hidden(sK0(X0,X1,k1_xboole_0),X0)
% 7.61/1.50      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.61/1.50      inference(resolution,[status(thm)],[c_4,c_2526]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_7385,plain,
% 7.61/1.50      ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0),k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 7.61/1.50      inference(resolution,[status(thm)],[c_7379,c_3243]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_14,plain,
% 7.61/1.50      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 7.61/1.50      inference(cnf_transformation,[],[f116]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_7391,plain,
% 7.61/1.50      ( sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0) = sK4 ),
% 7.61/1.50      inference(resolution,[status(thm)],[c_7385,c_14]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_8146,plain,
% 7.61/1.50      ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0),X0)
% 7.61/1.50      | ~ r2_hidden(sK4,X0) ),
% 7.61/1.50      inference(resolution,[status(thm)],[c_2372,c_7391]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_3,plain,
% 7.61/1.50      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 7.61/1.50      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.61/1.50      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 7.61/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_8982,plain,
% 7.61/1.50      ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0),k1_xboole_0)
% 7.61/1.50      | ~ r2_hidden(sK4,sK5)
% 7.61/1.50      | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k1_xboole_0 ),
% 7.61/1.50      inference(resolution,[status(thm)],[c_8146,c_3]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_4764,plain,
% 7.61/1.50      ( X0 != X1
% 7.61/1.50      | X0 = sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0)
% 7.61/1.50      | sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0) != X1 ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_339]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_4765,plain,
% 7.61/1.50      ( sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0) != sK4
% 7.61/1.50      | sK4 = sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0)
% 7.61/1.50      | sK4 != sK4 ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_4764]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1002,plain,
% 7.61/1.50      ( ~ r2_hidden(X0,X1)
% 7.61/1.50      | r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4)))
% 7.61/1.50      | X2 != X0
% 7.61/1.50      | k5_xboole_0(X3,k3_xboole_0(X3,X4)) != X1 ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_342]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_1451,plain,
% 7.61/1.50      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))
% 7.61/1.50      | ~ r2_hidden(X3,k1_xboole_0)
% 7.61/1.50      | X0 != X3
% 7.61/1.50      | k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) != k1_xboole_0 ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_1002]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_3385,plain,
% 7.61/1.50      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))
% 7.61/1.50      | ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0),k1_xboole_0)
% 7.61/1.50      | X0 != sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0)
% 7.61/1.50      | k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) != k1_xboole_0 ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_1451]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_3387,plain,
% 7.61/1.50      ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0),k1_xboole_0)
% 7.61/1.50      | r2_hidden(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))))
% 7.61/1.50      | k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))) != k1_xboole_0
% 7.61/1.50      | sK4 != sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k1_xboole_0) ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_3385]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(c_74,plain,
% 7.61/1.50      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(sK4,k3_xboole_0(sK4,sK4))))) = k1_xboole_0 ),
% 7.61/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.61/1.50  
% 7.61/1.50  cnf(contradiction,plain,
% 7.61/1.50      ( $false ),
% 7.61/1.50      inference(minisat,
% 7.61/1.50                [status(thm)],
% 7.61/1.50                [c_23318,c_23311,c_10333,c_8982,c_7391,c_6694,c_4765,
% 7.61/1.50                 c_3387,c_1666,c_74,c_55,c_52,c_28]) ).
% 7.61/1.50  
% 7.61/1.50  
% 7.61/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.61/1.50  
% 7.61/1.50  ------                               Statistics
% 7.61/1.50  
% 7.61/1.50  ------ Selected
% 7.61/1.50  
% 7.61/1.50  total_time:                             0.665
% 7.61/1.50  
%------------------------------------------------------------------------------
