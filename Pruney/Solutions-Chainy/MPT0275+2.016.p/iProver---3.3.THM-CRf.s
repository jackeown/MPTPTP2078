%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:26 EST 2020

% Result     : Theorem 19.56s
% Output     : CNFRefutation 19.56s
% Verified   : 
% Statistics : Number of formulae       :  154 (2206 expanded)
%              Number of clauses        :   89 ( 548 expanded)
%              Number of leaves         :   13 ( 535 expanded)
%              Depth                    :   23
%              Number of atoms          :  503 (10990 expanded)
%              Number of equality atoms :  259 (3275 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f18])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f36,f40])).

fof(f69,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f57])).

fof(f70,plain,(
    ! [X4,X0] : r2_hidden(X4,k1_enumset1(X0,X0,X4)) ),
    inference(equality_resolution,[],[f69])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ) )
   => ( ( ~ r2_hidden(sK3,sK4)
        | ~ r2_hidden(sK2,sK4)
        | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k1_xboole_0 )
      & ( ( r2_hidden(sK3,sK4)
          & r2_hidden(sK2,sK4) )
        | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0 ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ( ~ r2_hidden(sK3,sK4)
      | ~ r2_hidden(sK2,sK4)
      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k1_xboole_0 )
    & ( ( r2_hidden(sK3,sK4)
        & r2_hidden(sK2,sK4) )
      | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f24])).

fof(f44,plain,
    ( r2_hidden(sK2,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f65,plain,
    ( r2_hidden(sK2,sK4)
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f44,f32,f40])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f20])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k3_xboole_0(k1_enumset1(X0,X0,X1),X2)) = k1_enumset1(X0,X0,X1)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f43,f32,f40,f40])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f13,plain,(
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

fof(f14,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f27,f32])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f45,plain,
    ( r2_hidden(sK3,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,
    ( r2_hidden(sK3,sK4)
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f45,f32,f40])).

fof(f46,plain,
    ( ~ r2_hidden(sK3,sK4)
    | ~ r2_hidden(sK2,sK4)
    | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,
    ( ~ r2_hidden(sK3,sK4)
    | ~ r2_hidden(sK2,sK4)
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f46,f32,f40])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f34,f40])).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k1_enumset1(X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f35,f40])).

fof(f71,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f58])).

fof(f72,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f71])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f29,f32])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f30,f32])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f26,f32])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f52])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k5_xboole_0(k1_enumset1(X0,X0,X1),k3_xboole_0(k1_enumset1(X0,X0,X1),X2)) != k1_enumset1(X0,X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f32,f40,f40])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f28,f32])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f50])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_512,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK2,sK4)
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_504,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | k5_xboole_0(k1_enumset1(X0,X0,X2),k3_xboole_0(k1_enumset1(X0,X0,X2),X1)) = k1_enumset1(X0,X0,X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_509,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k3_xboole_0(k1_enumset1(X0,X0,X1),X2)) = k1_enumset1(X0,X0,X1)
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_517,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2451,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k3_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3)))) = k1_enumset1(X0,X0,X1)
    | r2_hidden(X1,X3) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_509,c_517])).

cnf(c_40495,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,sK2),k3_xboole_0(k1_enumset1(X0,X0,sK2),k5_xboole_0(X1,k3_xboole_0(X1,sK4)))) = k1_enumset1(X0,X0,sK2)
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_504,c_2451])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK3,sK4)
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_505,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_40494,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,sK3),k3_xboole_0(k1_enumset1(X0,X0,sK3),k5_xboole_0(X1,k3_xboole_0(X1,sK4)))) = k1_enumset1(X0,X0,sK3)
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_505,c_2451])).

cnf(c_45804,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,sK3),k3_xboole_0(k1_enumset1(X0,X0,sK3),k5_xboole_0(X1,k3_xboole_0(X1,sK4)))) = k1_enumset1(X0,X0,sK3)
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_40494,c_517])).

cnf(c_49085,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0
    | k5_xboole_0(k1_enumset1(sK3,sK3,sK3),k3_xboole_0(k1_enumset1(sK3,sK3,sK3),k5_xboole_0(X0,k3_xboole_0(X0,sK4)))) = k1_enumset1(sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_505,c_45804])).

cnf(c_49733,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0
    | r2_hidden(X0,k1_enumset1(sK3,sK3,sK3)) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_49085,c_517])).

cnf(c_56631,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,sK2),k3_xboole_0(k1_enumset1(X0,X0,sK2),k5_xboole_0(X1,k3_xboole_0(X1,sK4)))) = k1_enumset1(X0,X0,sK2)
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0
    | r2_hidden(X0,k1_enumset1(sK3,sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_40495,c_49733])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK3,sK4)
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_30,plain,
    ( ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_33,plain,
    ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_8207,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_8209,plain,
    ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_8207])).

cnf(c_2800,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,sK3))
    | X0 = X1
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_27660,plain,
    ( ~ r2_hidden(X0,k1_enumset1(sK3,sK3,sK3))
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_2800])).

cnf(c_27661,plain,
    ( X0 = sK3
    | r2_hidden(X0,k1_enumset1(sK3,sK3,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27660])).

cnf(c_49086,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(X0,k3_xboole_0(X0,sK4)))) = k1_enumset1(sK2,sK2,sK3)
    | k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_504,c_45804])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_519,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1828,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r2_hidden(sK0(X0,X1,X0),X0) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_519])).

cnf(c_1830,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r2_hidden(sK0(X0,X1,X0),X0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1828])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_521,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3383,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r2_hidden(sK0(X0,X1,X0),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1830,c_521])).

cnf(c_3406,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r2_hidden(sK0(X0,X1,X0),X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3383,c_1830])).

cnf(c_6169,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = X0
    | r2_hidden(sK0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)),X0),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3406,c_517])).

cnf(c_6564,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_1830,c_6169])).

cnf(c_50343,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0
    | k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK4)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK4)),k1_enumset1(sK2,sK2,sK3))) = k5_xboole_0(X0,k3_xboole_0(X0,sK4)) ),
    inference(superposition,[status(thm)],[c_49086,c_6564])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_520,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2607,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1
    | r2_hidden(sK0(X0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_519,c_520])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_516,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3640,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(sK0(X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2607,c_516])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(k1_enumset1(X0,X0,X2),k3_xboole_0(k1_enumset1(X0,X0,X2),X1)) != k1_enumset1(X0,X0,X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_507,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X1),k3_xboole_0(k1_enumset1(X0,X0,X1),X2)) != k1_enumset1(X0,X0,X1)
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_975,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_507])).

cnf(c_1823,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_519,c_975])).

cnf(c_2144,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) = k1_xboole_0
    | r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2,k1_xboole_0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1823,c_517])).

cnf(c_3644,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2607,c_2144])).

cnf(c_3646,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3644,c_6])).

cnf(c_3891,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r2_hidden(sK0(X2,X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3640,c_3646])).

cnf(c_6168,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = X0
    | r2_hidden(sK0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)),X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3406,c_516])).

cnf(c_3386,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1830,c_517])).

cnf(c_8930,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6168,c_3386])).

cnf(c_1827,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = X1
    | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_519,c_975])).

cnf(c_2146,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1823,c_975])).

cnf(c_2959,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1827,c_2146])).

cnf(c_2968,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2959,c_517])).

cnf(c_11951,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8930,c_2968])).

cnf(c_12011,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X1,k3_xboole_0(X1,X3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11951,c_8930])).

cnf(c_14895,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3891,c_12011])).

cnf(c_68653,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_50343,c_14895])).

cnf(c_197,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_985,plain,
    ( X0 != X1
    | k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X0 ),
    inference(resolution,[status(thm)],[c_197,c_6])).

cnf(c_200,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_6209,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)))
    | X2 != X0
    | X1 != X3 ),
    inference(resolution,[status(thm)],[c_985,c_200])).

cnf(c_65901,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)))
    | r2_hidden(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)))
    | r2_hidden(sK2,sK4)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_6209,c_18])).

cnf(c_196,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_994,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_197,c_196])).

cnf(c_4029,plain,
    ( r2_hidden(sK3,sK4)
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) ),
    inference(resolution,[status(thm)],[c_994,c_17])).

cnf(c_4463,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)))
    | r2_hidden(X1,k1_xboole_0)
    | r2_hidden(sK3,sK4)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_4029,c_200])).

cnf(c_1206,plain,
    ( r2_hidden(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)))
    | ~ r2_hidden(X1,k1_xboole_0)
    | r2_hidden(sK3,sK4)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_200,c_17])).

cnf(c_1504,plain,
    ( r2_hidden(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)))
    | ~ r2_hidden(X0,k1_xboole_0)
    | r2_hidden(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_1206,c_196])).

cnf(c_976,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_975])).

cnf(c_1901,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1504,c_976])).

cnf(c_5595,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)))
    | r2_hidden(sK3,sK4)
    | X1 != X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4463,c_1901])).

cnf(c_4030,plain,
    ( r2_hidden(sK2,sK4)
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) ),
    inference(resolution,[status(thm)],[c_994,c_18])).

cnf(c_4478,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)))
    | r2_hidden(X1,k1_xboole_0)
    | r2_hidden(sK2,sK4)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_4030,c_200])).

cnf(c_5608,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)))
    | r2_hidden(sK2,sK4)
    | X1 != X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4478,c_1901])).

cnf(c_69656,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)))
    | X1 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_65901,c_16,c_5595,c_5608,c_68653])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_69702,plain,
    ( ~ r2_hidden(X0,k1_enumset1(sK2,sK2,sK3))
    | r2_hidden(X0,sK4)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_69656,c_3])).

cnf(c_69704,plain,
    ( ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3))
    | r2_hidden(sK2,sK4)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_69702])).

cnf(c_69879,plain,
    ( r2_hidden(sK3,sK4)
    | X0 != sK3 ),
    inference(resolution,[status(thm)],[c_69702,c_10])).

cnf(c_74490,plain,
    ( r2_hidden(X0,k1_enumset1(sK3,sK3,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_56631,c_16,c_30,c_33,c_8209,c_27661,c_68653,c_69704,c_69879])).

cnf(c_74505,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_512,c_74490])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:16 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 19.56/2.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.56/2.99  
% 19.56/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.56/2.99  
% 19.56/2.99  ------  iProver source info
% 19.56/2.99  
% 19.56/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.56/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.56/2.99  git: non_committed_changes: false
% 19.56/2.99  git: last_make_outside_of_git: false
% 19.56/2.99  
% 19.56/2.99  ------ 
% 19.56/2.99  ------ Parsing...
% 19.56/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.56/2.99  
% 19.56/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.56/2.99  
% 19.56/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.56/2.99  
% 19.56/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.56/2.99  ------ Proving...
% 19.56/2.99  ------ Problem Properties 
% 19.56/2.99  
% 19.56/2.99  
% 19.56/2.99  clauses                                 19
% 19.56/2.99  conjectures                             3
% 19.56/2.99  EPR                                     0
% 19.56/2.99  Horn                                    10
% 19.56/2.99  unary                                   3
% 19.56/2.99  binary                                  6
% 19.56/2.99  lits                                    47
% 19.56/2.99  lits eq                                 19
% 19.56/2.99  fd_pure                                 0
% 19.56/2.99  fd_pseudo                               0
% 19.56/2.99  fd_cond                                 0
% 19.56/2.99  fd_pseudo_cond                          6
% 19.56/2.99  AC symbols                              0
% 19.56/2.99  
% 19.56/2.99  ------ Input Options Time Limit: Unbounded
% 19.56/2.99  
% 19.56/2.99  
% 19.56/2.99  ------ 
% 19.56/2.99  Current options:
% 19.56/2.99  ------ 
% 19.56/2.99  
% 19.56/2.99  
% 19.56/2.99  
% 19.56/2.99  
% 19.56/2.99  ------ Proving...
% 19.56/2.99  
% 19.56/2.99  
% 19.56/2.99  % SZS status Theorem for theBenchmark.p
% 19.56/2.99  
% 19.56/2.99   Resolution empty clause
% 19.56/2.99  
% 19.56/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.56/2.99  
% 19.56/2.99  fof(f4,axiom,(
% 19.56/2.99    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 19.56/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.99  
% 19.56/2.99  fof(f15,plain,(
% 19.56/2.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 19.56/2.99    inference(nnf_transformation,[],[f4])).
% 19.56/2.99  
% 19.56/2.99  fof(f16,plain,(
% 19.56/2.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 19.56/2.99    inference(flattening,[],[f15])).
% 19.56/2.99  
% 19.56/2.99  fof(f17,plain,(
% 19.56/2.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 19.56/2.99    inference(rectify,[],[f16])).
% 19.56/2.99  
% 19.56/2.99  fof(f18,plain,(
% 19.56/2.99    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 19.56/2.99    introduced(choice_axiom,[])).
% 19.56/2.99  
% 19.56/2.99  fof(f19,plain,(
% 19.56/2.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 19.56/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f18])).
% 19.56/2.99  
% 19.56/2.99  fof(f36,plain,(
% 19.56/2.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 19.56/2.99    inference(cnf_transformation,[],[f19])).
% 19.56/2.99  
% 19.56/2.99  fof(f5,axiom,(
% 19.56/2.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 19.56/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.99  
% 19.56/2.99  fof(f40,plain,(
% 19.56/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 19.56/2.99    inference(cnf_transformation,[],[f5])).
% 19.56/2.99  
% 19.56/2.99  fof(f57,plain,(
% 19.56/2.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 19.56/2.99    inference(definition_unfolding,[],[f36,f40])).
% 19.56/2.99  
% 19.56/2.99  fof(f69,plain,(
% 19.56/2.99    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k1_enumset1(X0,X0,X4) != X2) )),
% 19.56/2.99    inference(equality_resolution,[],[f57])).
% 19.56/2.99  
% 19.56/2.99  fof(f70,plain,(
% 19.56/2.99    ( ! [X4,X0] : (r2_hidden(X4,k1_enumset1(X0,X0,X4))) )),
% 19.56/2.99    inference(equality_resolution,[],[f69])).
% 19.56/2.99  
% 19.56/2.99  fof(f7,conjecture,(
% 19.56/2.99    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 19.56/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.99  
% 19.56/2.99  fof(f8,negated_conjecture,(
% 19.56/2.99    ~! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 19.56/2.99    inference(negated_conjecture,[],[f7])).
% 19.56/2.99  
% 19.56/2.99  fof(f9,plain,(
% 19.56/2.99    ? [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 19.56/2.99    inference(ennf_transformation,[],[f8])).
% 19.56/2.99  
% 19.56/2.99  fof(f22,plain,(
% 19.56/2.99    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0))),
% 19.56/2.99    inference(nnf_transformation,[],[f9])).
% 19.56/2.99  
% 19.56/2.99  fof(f23,plain,(
% 19.56/2.99    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0))),
% 19.56/2.99    inference(flattening,[],[f22])).
% 19.56/2.99  
% 19.56/2.99  fof(f24,plain,(
% 19.56/2.99    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0)) => ((~r2_hidden(sK3,sK4) | ~r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k1_xboole_0) & ((r2_hidden(sK3,sK4) & r2_hidden(sK2,sK4)) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0))),
% 19.56/2.99    introduced(choice_axiom,[])).
% 19.56/2.99  
% 19.56/2.99  fof(f25,plain,(
% 19.56/2.99    (~r2_hidden(sK3,sK4) | ~r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k1_xboole_0) & ((r2_hidden(sK3,sK4) & r2_hidden(sK2,sK4)) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0)),
% 19.56/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f24])).
% 19.56/2.99  
% 19.56/2.99  fof(f44,plain,(
% 19.56/2.99    r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0),
% 19.56/2.99    inference(cnf_transformation,[],[f25])).
% 19.56/2.99  
% 19.56/2.99  fof(f2,axiom,(
% 19.56/2.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 19.56/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.99  
% 19.56/2.99  fof(f32,plain,(
% 19.56/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 19.56/2.99    inference(cnf_transformation,[],[f2])).
% 19.56/2.99  
% 19.56/2.99  fof(f65,plain,(
% 19.56/2.99    r2_hidden(sK2,sK4) | k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0),
% 19.56/2.99    inference(definition_unfolding,[],[f44,f32,f40])).
% 19.56/2.99  
% 19.56/2.99  fof(f6,axiom,(
% 19.56/2.99    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 19.56/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.99  
% 19.56/2.99  fof(f20,plain,(
% 19.56/2.99    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 19.56/2.99    inference(nnf_transformation,[],[f6])).
% 19.56/2.99  
% 19.56/2.99  fof(f21,plain,(
% 19.56/2.99    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 19.56/2.99    inference(flattening,[],[f20])).
% 19.56/2.99  
% 19.56/2.99  fof(f43,plain,(
% 19.56/2.99    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 19.56/2.99    inference(cnf_transformation,[],[f21])).
% 19.56/2.99  
% 19.56/2.99  fof(f60,plain,(
% 19.56/2.99    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k3_xboole_0(k1_enumset1(X0,X0,X1),X2)) = k1_enumset1(X0,X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 19.56/2.99    inference(definition_unfolding,[],[f43,f32,f40,f40])).
% 19.56/2.99  
% 19.56/2.99  fof(f1,axiom,(
% 19.56/2.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 19.56/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.99  
% 19.56/2.99  fof(f10,plain,(
% 19.56/2.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.56/2.99    inference(nnf_transformation,[],[f1])).
% 19.56/2.99  
% 19.56/2.99  fof(f11,plain,(
% 19.56/2.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.56/2.99    inference(flattening,[],[f10])).
% 19.56/2.99  
% 19.56/2.99  fof(f12,plain,(
% 19.56/2.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.56/2.99    inference(rectify,[],[f11])).
% 19.56/2.99  
% 19.56/2.99  fof(f13,plain,(
% 19.56/2.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 19.56/2.99    introduced(choice_axiom,[])).
% 19.56/2.99  
% 19.56/2.99  fof(f14,plain,(
% 19.56/2.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 19.56/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).
% 19.56/2.99  
% 19.56/2.99  fof(f27,plain,(
% 19.56/2.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 19.56/2.99    inference(cnf_transformation,[],[f14])).
% 19.56/2.99  
% 19.56/2.99  fof(f51,plain,(
% 19.56/2.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 19.56/2.99    inference(definition_unfolding,[],[f27,f32])).
% 19.56/2.99  
% 19.56/2.99  fof(f67,plain,(
% 19.56/2.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 19.56/2.99    inference(equality_resolution,[],[f51])).
% 19.56/2.99  
% 19.56/2.99  fof(f45,plain,(
% 19.56/2.99    r2_hidden(sK3,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) = k1_xboole_0),
% 19.56/2.99    inference(cnf_transformation,[],[f25])).
% 19.56/2.99  
% 19.56/2.99  fof(f64,plain,(
% 19.56/2.99    r2_hidden(sK3,sK4) | k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0),
% 19.56/2.99    inference(definition_unfolding,[],[f45,f32,f40])).
% 19.56/2.99  
% 19.56/2.99  fof(f46,plain,(
% 19.56/2.99    ~r2_hidden(sK3,sK4) | ~r2_hidden(sK2,sK4) | k4_xboole_0(k2_tarski(sK2,sK3),sK4) != k1_xboole_0),
% 19.56/2.99    inference(cnf_transformation,[],[f25])).
% 19.56/2.99  
% 19.56/2.99  fof(f63,plain,(
% 19.56/2.99    ~r2_hidden(sK3,sK4) | ~r2_hidden(sK2,sK4) | k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) != k1_xboole_0),
% 19.56/2.99    inference(definition_unfolding,[],[f46,f32,f40])).
% 19.56/2.99  
% 19.56/2.99  fof(f34,plain,(
% 19.56/2.99    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 19.56/2.99    inference(cnf_transformation,[],[f19])).
% 19.56/2.99  
% 19.56/2.99  fof(f59,plain,(
% 19.56/2.99    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 19.56/2.99    inference(definition_unfolding,[],[f34,f40])).
% 19.56/2.99  
% 19.56/2.99  fof(f73,plain,(
% 19.56/2.99    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k1_enumset1(X0,X0,X1))) )),
% 19.56/2.99    inference(equality_resolution,[],[f59])).
% 19.56/2.99  
% 19.56/2.99  fof(f35,plain,(
% 19.56/2.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 19.56/2.99    inference(cnf_transformation,[],[f19])).
% 19.56/2.99  
% 19.56/2.99  fof(f58,plain,(
% 19.56/2.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 19.56/2.99    inference(definition_unfolding,[],[f35,f40])).
% 19.56/2.99  
% 19.56/2.99  fof(f71,plain,(
% 19.56/2.99    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 19.56/2.99    inference(equality_resolution,[],[f58])).
% 19.56/2.99  
% 19.56/2.99  fof(f72,plain,(
% 19.56/2.99    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 19.56/2.99    inference(equality_resolution,[],[f71])).
% 19.56/2.99  
% 19.56/2.99  fof(f29,plain,(
% 19.56/2.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.56/2.99    inference(cnf_transformation,[],[f14])).
% 19.56/2.99  
% 19.56/2.99  fof(f49,plain,(
% 19.56/2.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.56/2.99    inference(definition_unfolding,[],[f29,f32])).
% 19.56/2.99  
% 19.56/2.99  fof(f31,plain,(
% 19.56/2.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.56/2.99    inference(cnf_transformation,[],[f14])).
% 19.56/2.99  
% 19.56/2.99  fof(f47,plain,(
% 19.56/2.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.56/2.99    inference(definition_unfolding,[],[f31,f32])).
% 19.56/2.99  
% 19.56/2.99  fof(f30,plain,(
% 19.56/2.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.56/2.99    inference(cnf_transformation,[],[f14])).
% 19.56/2.99  
% 19.56/2.99  fof(f48,plain,(
% 19.56/2.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 19.56/2.99    inference(definition_unfolding,[],[f30,f32])).
% 19.56/2.99  
% 19.56/2.99  fof(f26,plain,(
% 19.56/2.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 19.56/2.99    inference(cnf_transformation,[],[f14])).
% 19.56/2.99  
% 19.56/2.99  fof(f52,plain,(
% 19.56/2.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 19.56/2.99    inference(definition_unfolding,[],[f26,f32])).
% 19.56/2.99  
% 19.56/2.99  fof(f68,plain,(
% 19.56/2.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 19.56/2.99    inference(equality_resolution,[],[f52])).
% 19.56/2.99  
% 19.56/2.99  fof(f3,axiom,(
% 19.56/2.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 19.56/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.56/2.99  
% 19.56/2.99  fof(f33,plain,(
% 19.56/2.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.56/2.99    inference(cnf_transformation,[],[f3])).
% 19.56/2.99  
% 19.56/2.99  fof(f53,plain,(
% 19.56/2.99    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 19.56/2.99    inference(definition_unfolding,[],[f33,f32])).
% 19.56/2.99  
% 19.56/2.99  fof(f41,plain,(
% 19.56/2.99    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) )),
% 19.56/2.99    inference(cnf_transformation,[],[f21])).
% 19.56/2.99  
% 19.56/2.99  fof(f62,plain,(
% 19.56/2.99    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k5_xboole_0(k1_enumset1(X0,X0,X1),k3_xboole_0(k1_enumset1(X0,X0,X1),X2)) != k1_enumset1(X0,X0,X1)) )),
% 19.56/2.99    inference(definition_unfolding,[],[f41,f32,f40,f40])).
% 19.56/2.99  
% 19.56/2.99  fof(f28,plain,(
% 19.56/2.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 19.56/2.99    inference(cnf_transformation,[],[f14])).
% 19.56/2.99  
% 19.56/2.99  fof(f50,plain,(
% 19.56/2.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 19.56/2.99    inference(definition_unfolding,[],[f28,f32])).
% 19.56/2.99  
% 19.56/2.99  fof(f66,plain,(
% 19.56/2.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 19.56/2.99    inference(equality_resolution,[],[f50])).
% 19.56/2.99  
% 19.56/2.99  cnf(c_10,plain,
% 19.56/2.99      ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
% 19.56/2.99      inference(cnf_transformation,[],[f70]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_512,plain,
% 19.56/2.99      ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) = iProver_top ),
% 19.56/2.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_18,negated_conjecture,
% 19.56/2.99      ( r2_hidden(sK2,sK4)
% 19.56/2.99      | k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0 ),
% 19.56/2.99      inference(cnf_transformation,[],[f65]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_504,plain,
% 19.56/2.99      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0
% 19.56/2.99      | r2_hidden(sK2,sK4) = iProver_top ),
% 19.56/2.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_13,plain,
% 19.56/2.99      ( r2_hidden(X0,X1)
% 19.56/2.99      | r2_hidden(X2,X1)
% 19.56/2.99      | k5_xboole_0(k1_enumset1(X0,X0,X2),k3_xboole_0(k1_enumset1(X0,X0,X2),X1)) = k1_enumset1(X0,X0,X2) ),
% 19.56/2.99      inference(cnf_transformation,[],[f60]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_509,plain,
% 19.56/2.99      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k3_xboole_0(k1_enumset1(X0,X0,X1),X2)) = k1_enumset1(X0,X0,X1)
% 19.56/2.99      | r2_hidden(X0,X2) = iProver_top
% 19.56/2.99      | r2_hidden(X1,X2) = iProver_top ),
% 19.56/2.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_4,plain,
% 19.56/2.99      ( ~ r2_hidden(X0,X1)
% 19.56/2.99      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 19.56/2.99      inference(cnf_transformation,[],[f67]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_517,plain,
% 19.56/2.99      ( r2_hidden(X0,X1) != iProver_top
% 19.56/2.99      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 19.56/2.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_2451,plain,
% 19.56/2.99      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k3_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3)))) = k1_enumset1(X0,X0,X1)
% 19.56/2.99      | r2_hidden(X1,X3) != iProver_top
% 19.56/2.99      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = iProver_top ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_509,c_517]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_40495,plain,
% 19.56/2.99      ( k5_xboole_0(k1_enumset1(X0,X0,sK2),k3_xboole_0(k1_enumset1(X0,X0,sK2),k5_xboole_0(X1,k3_xboole_0(X1,sK4)))) = k1_enumset1(X0,X0,sK2)
% 19.56/2.99      | k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0
% 19.56/2.99      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,sK4))) = iProver_top ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_504,c_2451]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_17,negated_conjecture,
% 19.56/2.99      ( r2_hidden(sK3,sK4)
% 19.56/2.99      | k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0 ),
% 19.56/2.99      inference(cnf_transformation,[],[f64]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_505,plain,
% 19.56/2.99      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0
% 19.56/2.99      | r2_hidden(sK3,sK4) = iProver_top ),
% 19.56/2.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_40494,plain,
% 19.56/2.99      ( k5_xboole_0(k1_enumset1(X0,X0,sK3),k3_xboole_0(k1_enumset1(X0,X0,sK3),k5_xboole_0(X1,k3_xboole_0(X1,sK4)))) = k1_enumset1(X0,X0,sK3)
% 19.56/2.99      | k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0
% 19.56/2.99      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,sK4))) = iProver_top ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_505,c_2451]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_45804,plain,
% 19.56/2.99      ( k5_xboole_0(k1_enumset1(X0,X0,sK3),k3_xboole_0(k1_enumset1(X0,X0,sK3),k5_xboole_0(X1,k3_xboole_0(X1,sK4)))) = k1_enumset1(X0,X0,sK3)
% 19.56/2.99      | k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0
% 19.56/2.99      | r2_hidden(X0,sK4) != iProver_top ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_40494,c_517]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_49085,plain,
% 19.56/2.99      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0
% 19.56/2.99      | k5_xboole_0(k1_enumset1(sK3,sK3,sK3),k3_xboole_0(k1_enumset1(sK3,sK3,sK3),k5_xboole_0(X0,k3_xboole_0(X0,sK4)))) = k1_enumset1(sK3,sK3,sK3) ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_505,c_45804]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_49733,plain,
% 19.56/2.99      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0
% 19.56/2.99      | r2_hidden(X0,k1_enumset1(sK3,sK3,sK3)) != iProver_top
% 19.56/2.99      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,sK4))) != iProver_top ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_49085,c_517]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_56631,plain,
% 19.56/2.99      ( k5_xboole_0(k1_enumset1(X0,X0,sK2),k3_xboole_0(k1_enumset1(X0,X0,sK2),k5_xboole_0(X1,k3_xboole_0(X1,sK4)))) = k1_enumset1(X0,X0,sK2)
% 19.56/2.99      | k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0
% 19.56/2.99      | r2_hidden(X0,k1_enumset1(sK3,sK3,sK3)) != iProver_top ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_40495,c_49733]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_16,negated_conjecture,
% 19.56/2.99      ( ~ r2_hidden(sK2,sK4)
% 19.56/2.99      | ~ r2_hidden(sK3,sK4)
% 19.56/2.99      | k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) != k1_xboole_0 ),
% 19.56/2.99      inference(cnf_transformation,[],[f63]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_12,plain,
% 19.56/2.99      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 19.56/2.99      inference(cnf_transformation,[],[f73]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_30,plain,
% 19.56/2.99      ( ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) | sK2 = sK2 ),
% 19.56/2.99      inference(instantiation,[status(thm)],[c_12]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_11,plain,
% 19.56/2.99      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
% 19.56/2.99      inference(cnf_transformation,[],[f72]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_33,plain,
% 19.56/2.99      ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) ),
% 19.56/2.99      inference(instantiation,[status(thm)],[c_11]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_8207,plain,
% 19.56/2.99      ( r2_hidden(X0,k1_enumset1(X0,X0,sK3)) ),
% 19.56/2.99      inference(instantiation,[status(thm)],[c_11]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_8209,plain,
% 19.56/2.99      ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) ),
% 19.56/2.99      inference(instantiation,[status(thm)],[c_8207]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_2800,plain,
% 19.56/2.99      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,sK3)) | X0 = X1 | X0 = sK3 ),
% 19.56/2.99      inference(instantiation,[status(thm)],[c_12]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_27660,plain,
% 19.56/2.99      ( ~ r2_hidden(X0,k1_enumset1(sK3,sK3,sK3)) | X0 = sK3 ),
% 19.56/2.99      inference(instantiation,[status(thm)],[c_2800]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_27661,plain,
% 19.56/2.99      ( X0 = sK3 | r2_hidden(X0,k1_enumset1(sK3,sK3,sK3)) != iProver_top ),
% 19.56/2.99      inference(predicate_to_equality,[status(thm)],[c_27660]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_49086,plain,
% 19.56/2.99      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(X0,k3_xboole_0(X0,sK4)))) = k1_enumset1(sK2,sK2,sK3)
% 19.56/2.99      | k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0 ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_504,c_45804]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_2,plain,
% 19.56/2.99      ( r2_hidden(sK0(X0,X1,X2),X0)
% 19.56/2.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 19.56/2.99      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 19.56/2.99      inference(cnf_transformation,[],[f49]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_519,plain,
% 19.56/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 19.56/2.99      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 19.56/2.99      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 19.56/2.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_1828,plain,
% 19.56/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 19.56/2.99      | r2_hidden(sK0(X0,X1,X0),X0) = iProver_top
% 19.56/2.99      | iProver_top != iProver_top ),
% 19.56/2.99      inference(equality_factoring,[status(thm)],[c_519]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_1830,plain,
% 19.56/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 19.56/2.99      | r2_hidden(sK0(X0,X1,X0),X0) = iProver_top ),
% 19.56/2.99      inference(equality_resolution_simp,[status(thm)],[c_1828]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_0,plain,
% 19.56/2.99      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 19.56/2.99      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 19.56/2.99      | r2_hidden(sK0(X0,X1,X2),X1)
% 19.56/2.99      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 19.56/2.99      inference(cnf_transformation,[],[f47]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_521,plain,
% 19.56/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 19.56/2.99      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 19.56/2.99      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 19.56/2.99      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 19.56/2.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_3383,plain,
% 19.56/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 19.56/2.99      | r2_hidden(sK0(X0,X1,X0),X0) != iProver_top
% 19.56/2.99      | r2_hidden(sK0(X0,X1,X0),X1) = iProver_top ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_1830,c_521]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_3406,plain,
% 19.56/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 19.56/2.99      | r2_hidden(sK0(X0,X1,X0),X1) = iProver_top ),
% 19.56/2.99      inference(forward_subsumption_resolution,[status(thm)],[c_3383,c_1830]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_6169,plain,
% 19.56/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = X0
% 19.56/2.99      | r2_hidden(sK0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)),X0),X2) != iProver_top ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_3406,c_517]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_6564,plain,
% 19.56/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_1830,c_6169]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_50343,plain,
% 19.56/2.99      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0
% 19.56/2.99      | k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK4)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK4)),k1_enumset1(sK2,sK2,sK3))) = k5_xboole_0(X0,k3_xboole_0(X0,sK4)) ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_49086,c_6564]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_1,plain,
% 19.56/2.99      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 19.56/2.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 19.56/2.99      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 19.56/2.99      inference(cnf_transformation,[],[f48]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_520,plain,
% 19.56/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 19.56/2.99      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 19.56/2.99      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 19.56/2.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_2607,plain,
% 19.56/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1
% 19.56/2.99      | r2_hidden(sK0(X0,X0,X1),X1) = iProver_top ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_519,c_520]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_5,plain,
% 19.56/2.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 19.56/2.99      inference(cnf_transformation,[],[f68]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_516,plain,
% 19.56/2.99      ( r2_hidden(X0,X1) = iProver_top
% 19.56/2.99      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 19.56/2.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_3640,plain,
% 19.56/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
% 19.56/2.99      | r2_hidden(sK0(X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X1) = iProver_top ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_2607,c_516]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_6,plain,
% 19.56/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 19.56/2.99      inference(cnf_transformation,[],[f53]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_15,plain,
% 19.56/2.99      ( ~ r2_hidden(X0,X1)
% 19.56/2.99      | k5_xboole_0(k1_enumset1(X0,X0,X2),k3_xboole_0(k1_enumset1(X0,X0,X2),X1)) != k1_enumset1(X0,X0,X2) ),
% 19.56/2.99      inference(cnf_transformation,[],[f62]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_507,plain,
% 19.56/2.99      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k3_xboole_0(k1_enumset1(X0,X0,X1),X2)) != k1_enumset1(X0,X0,X1)
% 19.56/2.99      | r2_hidden(X0,X2) != iProver_top ),
% 19.56/2.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_975,plain,
% 19.56/2.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_6,c_507]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_1823,plain,
% 19.56/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 19.56/2.99      | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_519,c_975]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_2144,plain,
% 19.56/2.99      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) = k1_xboole_0
% 19.56/2.99      | r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2,k1_xboole_0),X1) != iProver_top ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_1823,c_517]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_3644,plain,
% 19.56/2.99      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) = k1_xboole_0 ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_2607,c_2144]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_3646,plain,
% 19.56/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 19.56/2.99      inference(light_normalisation,[status(thm)],[c_3644,c_6]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_3891,plain,
% 19.56/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 19.56/2.99      | r2_hidden(sK0(X2,X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))),X0) = iProver_top ),
% 19.56/2.99      inference(light_normalisation,[status(thm)],[c_3640,c_3646]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_6168,plain,
% 19.56/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = X0
% 19.56/2.99      | r2_hidden(sK0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)),X0),X1) = iProver_top ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_3406,c_516]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_3386,plain,
% 19.56/2.99      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
% 19.56/2.99      | r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))),X1) != iProver_top ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_1830,c_517]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_8930,plain,
% 19.56/2.99      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_6168,c_3386]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_1827,plain,
% 19.56/2.99      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = X1
% 19.56/2.99      | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_519,c_975]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_2146,plain,
% 19.56/2.99      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_1823,c_975]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_2959,plain,
% 19.56/2.99      ( k1_xboole_0 = X0 | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 19.56/2.99      inference(demodulation,[status(thm)],[c_1827,c_2146]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_2968,plain,
% 19.56/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 19.56/2.99      | r2_hidden(sK0(k1_xboole_0,X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))),X1) != iProver_top ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_2959,c_517]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_11951,plain,
% 19.56/2.99      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k1_xboole_0
% 19.56/2.99      | r2_hidden(sK0(k1_xboole_0,X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_8930,c_2968]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_12011,plain,
% 19.56/2.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 19.56/2.99      | r2_hidden(sK0(k1_xboole_0,X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X1,k3_xboole_0(X1,X3))) != iProver_top ),
% 19.56/2.99      inference(demodulation,[status(thm)],[c_11951,c_8930]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_14895,plain,
% 19.56/2.99      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) = k1_xboole_0 ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_3891,c_12011]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_68653,plain,
% 19.56/2.99      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = k1_xboole_0 ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_50343,c_14895]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_197,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_985,plain,
% 19.56/2.99      ( X0 != X1 | k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X0 ),
% 19.56/2.99      inference(resolution,[status(thm)],[c_197,c_6]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_200,plain,
% 19.56/2.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.56/2.99      theory(equality) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_6209,plain,
% 19.56/2.99      ( ~ r2_hidden(X0,X1)
% 19.56/2.99      | r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)))
% 19.56/2.99      | X2 != X0
% 19.56/2.99      | X1 != X3 ),
% 19.56/2.99      inference(resolution,[status(thm)],[c_985,c_200]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_65901,plain,
% 19.56/2.99      ( ~ r2_hidden(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)))
% 19.56/2.99      | r2_hidden(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)))
% 19.56/2.99      | r2_hidden(sK2,sK4)
% 19.56/2.99      | X1 != X0 ),
% 19.56/2.99      inference(resolution,[status(thm)],[c_6209,c_18]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_196,plain,( X0 = X0 ),theory(equality) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_994,plain,
% 19.56/2.99      ( X0 != X1 | X1 = X0 ),
% 19.56/2.99      inference(resolution,[status(thm)],[c_197,c_196]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_4029,plain,
% 19.56/2.99      ( r2_hidden(sK3,sK4)
% 19.56/2.99      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) ),
% 19.56/2.99      inference(resolution,[status(thm)],[c_994,c_17]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_4463,plain,
% 19.56/2.99      ( ~ r2_hidden(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)))
% 19.56/2.99      | r2_hidden(X1,k1_xboole_0)
% 19.56/2.99      | r2_hidden(sK3,sK4)
% 19.56/2.99      | X1 != X0 ),
% 19.56/2.99      inference(resolution,[status(thm)],[c_4029,c_200]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_1206,plain,
% 19.56/2.99      ( r2_hidden(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)))
% 19.56/2.99      | ~ r2_hidden(X1,k1_xboole_0)
% 19.56/2.99      | r2_hidden(sK3,sK4)
% 19.56/2.99      | X0 != X1 ),
% 19.56/2.99      inference(resolution,[status(thm)],[c_200,c_17]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_1504,plain,
% 19.56/2.99      ( r2_hidden(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)))
% 19.56/2.99      | ~ r2_hidden(X0,k1_xboole_0)
% 19.56/2.99      | r2_hidden(sK3,sK4) ),
% 19.56/2.99      inference(resolution,[status(thm)],[c_1206,c_196]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_976,plain,
% 19.56/2.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 19.56/2.99      inference(predicate_to_equality_rev,[status(thm)],[c_975]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_1901,plain,
% 19.56/2.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 19.56/2.99      inference(global_propositional_subsumption,[status(thm)],[c_1504,c_976]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_5595,plain,
% 19.56/2.99      ( ~ r2_hidden(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)))
% 19.56/2.99      | r2_hidden(sK3,sK4)
% 19.56/2.99      | X1 != X0 ),
% 19.56/2.99      inference(forward_subsumption_resolution,[status(thm)],[c_4463,c_1901]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_4030,plain,
% 19.56/2.99      ( r2_hidden(sK2,sK4)
% 19.56/2.99      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) ),
% 19.56/2.99      inference(resolution,[status(thm)],[c_994,c_18]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_4478,plain,
% 19.56/2.99      ( ~ r2_hidden(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)))
% 19.56/2.99      | r2_hidden(X1,k1_xboole_0)
% 19.56/2.99      | r2_hidden(sK2,sK4)
% 19.56/2.99      | X1 != X0 ),
% 19.56/2.99      inference(resolution,[status(thm)],[c_4030,c_200]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_5608,plain,
% 19.56/2.99      ( ~ r2_hidden(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)))
% 19.56/2.99      | r2_hidden(sK2,sK4)
% 19.56/2.99      | X1 != X0 ),
% 19.56/2.99      inference(forward_subsumption_resolution,[status(thm)],[c_4478,c_1901]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_69656,plain,
% 19.56/2.99      ( ~ r2_hidden(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)))
% 19.56/2.99      | X1 != X0 ),
% 19.56/2.99      inference(global_propositional_subsumption,
% 19.56/2.99                [status(thm)],
% 19.56/2.99                [c_65901,c_16,c_5595,c_5608,c_68653]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_3,plain,
% 19.56/2.99      ( ~ r2_hidden(X0,X1)
% 19.56/2.99      | r2_hidden(X0,X2)
% 19.56/2.99      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 19.56/2.99      inference(cnf_transformation,[],[f66]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_69702,plain,
% 19.56/2.99      ( ~ r2_hidden(X0,k1_enumset1(sK2,sK2,sK3))
% 19.56/2.99      | r2_hidden(X0,sK4)
% 19.56/2.99      | X1 != X0 ),
% 19.56/2.99      inference(resolution,[status(thm)],[c_69656,c_3]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_69704,plain,
% 19.56/2.99      ( ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3))
% 19.56/2.99      | r2_hidden(sK2,sK4)
% 19.56/2.99      | sK2 != sK2 ),
% 19.56/2.99      inference(instantiation,[status(thm)],[c_69702]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_69879,plain,
% 19.56/2.99      ( r2_hidden(sK3,sK4) | X0 != sK3 ),
% 19.56/2.99      inference(resolution,[status(thm)],[c_69702,c_10]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_74490,plain,
% 19.56/2.99      ( r2_hidden(X0,k1_enumset1(sK3,sK3,sK3)) != iProver_top ),
% 19.56/2.99      inference(global_propositional_subsumption,
% 19.56/2.99                [status(thm)],
% 19.56/2.99                [c_56631,c_16,c_30,c_33,c_8209,c_27661,c_68653,c_69704,c_69879]) ).
% 19.56/2.99  
% 19.56/2.99  cnf(c_74505,plain,
% 19.56/2.99      ( $false ),
% 19.56/2.99      inference(superposition,[status(thm)],[c_512,c_74490]) ).
% 19.56/2.99  
% 19.56/2.99  
% 19.56/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.56/2.99  
% 19.56/2.99  ------                               Statistics
% 19.56/2.99  
% 19.56/2.99  ------ Selected
% 19.56/2.99  
% 19.56/2.99  total_time:                             2.308
% 19.56/2.99  
%------------------------------------------------------------------------------
