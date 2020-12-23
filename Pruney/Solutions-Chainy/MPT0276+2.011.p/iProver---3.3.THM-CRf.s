%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:28 EST 2020

% Result     : Theorem 23.66s
% Output     : CNFRefutation 23.66s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 504 expanded)
%              Number of clauses        :   45 ( 121 expanded)
%              Number of leaves         :   15 ( 162 expanded)
%              Depth                    :   16
%              Number of atoms          :  361 (1634 expanded)
%              Number of equality atoms :  207 (1097 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f22])).

fof(f44,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f65,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_enumset1(X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f44,f52])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
   => ( k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4)
      & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK4)
      & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK3)
      & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0 ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4)
    & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK4)
    & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK3)
    & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f11,f26])).

fof(f50,plain,(
    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f71,plain,(
    k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f50,f34,f42,f52])).

fof(f48,plain,(
    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f48,f34,f42])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_enumset1(X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f43,f52])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f15,plain,(
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

fof(f16,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f28,f34])).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f35,f42])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k1_enumset1(X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f29,f34])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f49,plain,(
    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f49,f34,f42,f52])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f24])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k1_enumset1(X0,X0,X1),k3_xboole_0(k1_enumset1(X0,X0,X1),X2)) = k1_enumset1(X0,X0,X1)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f47,f34,f42,f42])).

fof(f51,plain,(
    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK3,sK3,sK4) ),
    inference(definition_unfolding,[],[f51,f34,f42,f42])).

cnf(c_12,plain,
    ( k1_enumset1(X0,X0,X0) = X1
    | sK2(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_151,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_150,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_894,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_151,c_150])).

cnf(c_2219,plain,
    ( X0 = k1_enumset1(X1,X1,X1)
    | sK2(X0,X1) != X1
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_12,c_894])).

cnf(c_18,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_30177,plain,
    ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) != sK4
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_2219,c_18])).

cnf(c_20,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_713,plain,
    ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_150])).

cnf(c_549,plain,
    ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != X0
    | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_151])).

cnf(c_6667,plain,
    ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
    | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_xboole_0
    | k1_xboole_0 != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_549])).

cnf(c_30600,plain,
    ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_30177,c_20,c_713,c_6667])).

cnf(c_13,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | k1_enumset1(X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1182,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | X0 = k1_enumset1(X1,X1,X1)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_894,c_13])).

cnf(c_1307,plain,
    ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4),k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)))
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_1182,c_18])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1339,plain,
    ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4),k1_enumset1(sK3,sK3,sK4))
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_1307,c_5])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1722,plain,
    ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) = sK4
    | sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) = sK3
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_1339,c_11])).

cnf(c_30606,plain,
    ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) = sK3
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_30600,c_1722])).

cnf(c_31170,plain,
    ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_30606,c_20,c_713,c_1722,c_6667,c_30177])).

cnf(c_154,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1176,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_154,c_150])).

cnf(c_37607,plain,
    ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4),X0)
    | ~ r2_hidden(sK3,X0) ),
    inference(resolution,[status(thm)],[c_31170,c_1176])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1155,plain,
    ( ~ r2_hidden(sK2(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X1)
    | k1_enumset1(X2,X2,X2) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_13,c_4])).

cnf(c_79640,plain,
    ( ~ r2_hidden(sK3,sK5)
    | k1_enumset1(sK4,sK4,sK4) = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_37607,c_1155])).

cnf(c_19,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_30178,plain,
    ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3) != sK3
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_2219,c_19])).

cnf(c_31109,plain,
    ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_30178,c_20,c_713,c_6667])).

cnf(c_1309,plain,
    ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)))
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_1182,c_19])).

cnf(c_1464,plain,
    ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),k1_enumset1(sK3,sK3,sK4))
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_1309,c_5])).

cnf(c_1729,plain,
    ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3) = sK4
    | sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3) = sK3
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_1464,c_11])).

cnf(c_1927,plain,
    ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),X0)
    | ~ r2_hidden(sK4,X0)
    | sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3) = sK3
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_1729,c_1176])).

cnf(c_31118,plain,
    ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),X0)
    | ~ r2_hidden(sK4,X0)
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_31109,c_1927])).

cnf(c_39085,plain,
    ( ~ r2_hidden(sK4,X0)
    | r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31118,c_20,c_713,c_6667])).

cnf(c_39086,plain,
    ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),X0)
    | ~ r2_hidden(sK4,X0) ),
    inference(renaming,[status(thm)],[c_39085])).

cnf(c_1462,plain,
    ( ~ r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),sK5)
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_1309,c_4])).

cnf(c_39119,plain,
    ( ~ r2_hidden(sK4,sK5)
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_39086,c_1462])).

cnf(c_545,plain,
    ( k1_enumset1(sK4,sK4,sK4) != X0
    | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != X0
    | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_enumset1(sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_151])).

cnf(c_8351,plain,
    ( k1_enumset1(sK4,sK4,sK4) != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
    | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_enumset1(sK4,sK4,sK4)
    | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | k5_xboole_0(k1_enumset1(X0,X0,X2),k3_xboole_0(k1_enumset1(X0,X0,X2),X1)) = k1_enumset1(X0,X0,X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_629,plain,
    ( r2_hidden(sK4,sK5)
    | r2_hidden(sK3,sK5)
    | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_enumset1(sK3,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_17,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK3,sK3,sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_79640,c_39119,c_8351,c_6667,c_713,c_629,c_17,c_18,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:20:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.66/3.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.66/3.50  
% 23.66/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.66/3.50  
% 23.66/3.50  ------  iProver source info
% 23.66/3.50  
% 23.66/3.50  git: date: 2020-06-30 10:37:57 +0100
% 23.66/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.66/3.50  git: non_committed_changes: false
% 23.66/3.50  git: last_make_outside_of_git: false
% 23.66/3.50  
% 23.66/3.50  ------ 
% 23.66/3.50  ------ Parsing...
% 23.66/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.66/3.50  
% 23.66/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 23.66/3.50  
% 23.66/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.66/3.50  
% 23.66/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.66/3.50  ------ Proving...
% 23.66/3.50  ------ Problem Properties 
% 23.66/3.50  
% 23.66/3.50  
% 23.66/3.50  clauses                                 21
% 23.66/3.50  conjectures                             4
% 23.66/3.50  EPR                                     0
% 23.66/3.50  Horn                                    12
% 23.66/3.50  unary                                   6
% 23.66/3.50  binary                                  4
% 23.66/3.50  lits                                    49
% 23.66/3.50  lits eq                                 24
% 23.66/3.50  fd_pure                                 0
% 23.66/3.50  fd_pseudo                               0
% 23.66/3.50  fd_cond                                 0
% 23.66/3.50  fd_pseudo_cond                          8
% 23.66/3.50  AC symbols                              0
% 23.66/3.50  
% 23.66/3.50  ------ Input Options Time Limit: Unbounded
% 23.66/3.50  
% 23.66/3.50  
% 23.66/3.50  ------ 
% 23.66/3.50  Current options:
% 23.66/3.50  ------ 
% 23.66/3.50  
% 23.66/3.50  
% 23.66/3.50  
% 23.66/3.50  
% 23.66/3.50  ------ Proving...
% 23.66/3.50  
% 23.66/3.50  
% 23.66/3.50  % SZS status Theorem for theBenchmark.p
% 23.66/3.50  
% 23.66/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.66/3.50  
% 23.66/3.50  fof(f6,axiom,(
% 23.66/3.50    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 23.66/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f10,plain,(
% 23.66/3.50    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 23.66/3.50    inference(ennf_transformation,[],[f6])).
% 23.66/3.50  
% 23.66/3.50  fof(f22,plain,(
% 23.66/3.50    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 23.66/3.50    introduced(choice_axiom,[])).
% 23.66/3.50  
% 23.66/3.50  fof(f23,plain,(
% 23.66/3.50    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 23.66/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f22])).
% 23.66/3.50  
% 23.66/3.50  fof(f44,plain,(
% 23.66/3.50    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 23.66/3.50    inference(cnf_transformation,[],[f23])).
% 23.66/3.50  
% 23.66/3.50  fof(f4,axiom,(
% 23.66/3.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 23.66/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f41,plain,(
% 23.66/3.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 23.66/3.50    inference(cnf_transformation,[],[f4])).
% 23.66/3.50  
% 23.66/3.50  fof(f5,axiom,(
% 23.66/3.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 23.66/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f42,plain,(
% 23.66/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 23.66/3.50    inference(cnf_transformation,[],[f5])).
% 23.66/3.50  
% 23.66/3.50  fof(f52,plain,(
% 23.66/3.50    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 23.66/3.50    inference(definition_unfolding,[],[f41,f42])).
% 23.66/3.50  
% 23.66/3.50  fof(f65,plain,(
% 23.66/3.50    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_enumset1(X1,X1,X1) = X0) )),
% 23.66/3.50    inference(definition_unfolding,[],[f44,f52])).
% 23.66/3.50  
% 23.66/3.50  fof(f8,conjecture,(
% 23.66/3.50    ! [X0,X1,X2] : ~(k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0)),
% 23.66/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f9,negated_conjecture,(
% 23.66/3.50    ~! [X0,X1,X2] : ~(k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0)),
% 23.66/3.50    inference(negated_conjecture,[],[f8])).
% 23.66/3.50  
% 23.66/3.50  fof(f11,plain,(
% 23.66/3.50    ? [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0)),
% 23.66/3.50    inference(ennf_transformation,[],[f9])).
% 23.66/3.50  
% 23.66/3.50  fof(f26,plain,(
% 23.66/3.50    ? [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0) => (k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4) & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK4) & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK3) & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0)),
% 23.66/3.50    introduced(choice_axiom,[])).
% 23.66/3.50  
% 23.66/3.50  fof(f27,plain,(
% 23.66/3.50    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4) & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK4) & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK3) & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0),
% 23.66/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f11,f26])).
% 23.66/3.50  
% 23.66/3.50  fof(f50,plain,(
% 23.66/3.50    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK4)),
% 23.66/3.50    inference(cnf_transformation,[],[f27])).
% 23.66/3.50  
% 23.66/3.50  fof(f2,axiom,(
% 23.66/3.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 23.66/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f34,plain,(
% 23.66/3.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 23.66/3.50    inference(cnf_transformation,[],[f2])).
% 23.66/3.50  
% 23.66/3.50  fof(f71,plain,(
% 23.66/3.50    k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK4,sK4,sK4)),
% 23.66/3.50    inference(definition_unfolding,[],[f50,f34,f42,f52])).
% 23.66/3.50  
% 23.66/3.50  fof(f48,plain,(
% 23.66/3.50    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0),
% 23.66/3.50    inference(cnf_transformation,[],[f27])).
% 23.66/3.50  
% 23.66/3.50  fof(f73,plain,(
% 23.66/3.50    k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_xboole_0),
% 23.66/3.50    inference(definition_unfolding,[],[f48,f34,f42])).
% 23.66/3.50  
% 23.66/3.50  fof(f43,plain,(
% 23.66/3.50    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 23.66/3.50    inference(cnf_transformation,[],[f23])).
% 23.66/3.50  
% 23.66/3.50  fof(f66,plain,(
% 23.66/3.50    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_enumset1(X1,X1,X1) = X0) )),
% 23.66/3.50    inference(definition_unfolding,[],[f43,f52])).
% 23.66/3.50  
% 23.66/3.50  fof(f1,axiom,(
% 23.66/3.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 23.66/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f12,plain,(
% 23.66/3.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.66/3.50    inference(nnf_transformation,[],[f1])).
% 23.66/3.50  
% 23.66/3.50  fof(f13,plain,(
% 23.66/3.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.66/3.50    inference(flattening,[],[f12])).
% 23.66/3.50  
% 23.66/3.50  fof(f14,plain,(
% 23.66/3.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.66/3.50    inference(rectify,[],[f13])).
% 23.66/3.50  
% 23.66/3.50  fof(f15,plain,(
% 23.66/3.50    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 23.66/3.50    introduced(choice_axiom,[])).
% 23.66/3.50  
% 23.66/3.50  fof(f16,plain,(
% 23.66/3.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.66/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).
% 23.66/3.50  
% 23.66/3.50  fof(f28,plain,(
% 23.66/3.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 23.66/3.50    inference(cnf_transformation,[],[f16])).
% 23.66/3.50  
% 23.66/3.50  fof(f58,plain,(
% 23.66/3.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 23.66/3.50    inference(definition_unfolding,[],[f28,f34])).
% 23.66/3.50  
% 23.66/3.50  fof(f76,plain,(
% 23.66/3.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 23.66/3.50    inference(equality_resolution,[],[f58])).
% 23.66/3.50  
% 23.66/3.50  fof(f3,axiom,(
% 23.66/3.50    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 23.66/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f17,plain,(
% 23.66/3.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 23.66/3.50    inference(nnf_transformation,[],[f3])).
% 23.66/3.50  
% 23.66/3.50  fof(f18,plain,(
% 23.66/3.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 23.66/3.50    inference(flattening,[],[f17])).
% 23.66/3.50  
% 23.66/3.50  fof(f19,plain,(
% 23.66/3.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 23.66/3.50    inference(rectify,[],[f18])).
% 23.66/3.50  
% 23.66/3.50  fof(f20,plain,(
% 23.66/3.50    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 23.66/3.50    introduced(choice_axiom,[])).
% 23.66/3.50  
% 23.66/3.50  fof(f21,plain,(
% 23.66/3.50    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 23.66/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 23.66/3.50  
% 23.66/3.50  fof(f35,plain,(
% 23.66/3.50    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 23.66/3.50    inference(cnf_transformation,[],[f21])).
% 23.66/3.50  
% 23.66/3.50  fof(f64,plain,(
% 23.66/3.50    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 23.66/3.50    inference(definition_unfolding,[],[f35,f42])).
% 23.66/3.50  
% 23.66/3.50  fof(f81,plain,(
% 23.66/3.50    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k1_enumset1(X0,X0,X1))) )),
% 23.66/3.50    inference(equality_resolution,[],[f64])).
% 23.66/3.50  
% 23.66/3.50  fof(f29,plain,(
% 23.66/3.50    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 23.66/3.50    inference(cnf_transformation,[],[f16])).
% 23.66/3.50  
% 23.66/3.50  fof(f57,plain,(
% 23.66/3.50    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 23.66/3.50    inference(definition_unfolding,[],[f29,f34])).
% 23.66/3.50  
% 23.66/3.50  fof(f75,plain,(
% 23.66/3.50    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 23.66/3.50    inference(equality_resolution,[],[f57])).
% 23.66/3.50  
% 23.66/3.50  fof(f49,plain,(
% 23.66/3.50    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK3)),
% 23.66/3.50    inference(cnf_transformation,[],[f27])).
% 23.66/3.50  
% 23.66/3.50  fof(f72,plain,(
% 23.66/3.50    k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK3,sK3,sK3)),
% 23.66/3.50    inference(definition_unfolding,[],[f49,f34,f42,f52])).
% 23.66/3.50  
% 23.66/3.50  fof(f7,axiom,(
% 23.66/3.50    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 23.66/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.66/3.50  
% 23.66/3.50  fof(f24,plain,(
% 23.66/3.50    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 23.66/3.50    inference(nnf_transformation,[],[f7])).
% 23.66/3.50  
% 23.66/3.50  fof(f25,plain,(
% 23.66/3.50    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 23.66/3.50    inference(flattening,[],[f24])).
% 23.66/3.50  
% 23.66/3.50  fof(f47,plain,(
% 23.66/3.50    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 23.66/3.50    inference(cnf_transformation,[],[f25])).
% 23.66/3.50  
% 23.66/3.50  fof(f67,plain,(
% 23.66/3.50    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k3_xboole_0(k1_enumset1(X0,X0,X1),X2)) = k1_enumset1(X0,X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 23.66/3.50    inference(definition_unfolding,[],[f47,f34,f42,f42])).
% 23.66/3.50  
% 23.66/3.50  fof(f51,plain,(
% 23.66/3.50    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4)),
% 23.66/3.50    inference(cnf_transformation,[],[f27])).
% 23.66/3.50  
% 23.66/3.50  fof(f70,plain,(
% 23.66/3.50    k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK3,sK3,sK4)),
% 23.66/3.50    inference(definition_unfolding,[],[f51,f34,f42,f42])).
% 23.66/3.50  
% 23.66/3.50  cnf(c_12,plain,
% 23.66/3.50      ( k1_enumset1(X0,X0,X0) = X1
% 23.66/3.50      | sK2(X1,X0) != X0
% 23.66/3.50      | k1_xboole_0 = X1 ),
% 23.66/3.50      inference(cnf_transformation,[],[f65]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_151,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_150,plain,( X0 = X0 ),theory(equality) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_894,plain,
% 23.66/3.50      ( X0 != X1 | X1 = X0 ),
% 23.66/3.50      inference(resolution,[status(thm)],[c_151,c_150]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_2219,plain,
% 23.66/3.50      ( X0 = k1_enumset1(X1,X1,X1)
% 23.66/3.50      | sK2(X0,X1) != X1
% 23.66/3.50      | k1_xboole_0 = X0 ),
% 23.66/3.50      inference(resolution,[status(thm)],[c_12,c_894]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_18,negated_conjecture,
% 23.66/3.50      ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK4,sK4,sK4) ),
% 23.66/3.50      inference(cnf_transformation,[],[f71]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_30177,plain,
% 23.66/3.50      ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) != sK4
% 23.66/3.50      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 23.66/3.50      inference(resolution,[status(thm)],[c_2219,c_18]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_20,negated_conjecture,
% 23.66/3.50      ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_xboole_0 ),
% 23.66/3.50      inference(cnf_transformation,[],[f73]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_713,plain,
% 23.66/3.50      ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_150]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_549,plain,
% 23.66/3.50      ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != X0
% 23.66/3.50      | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_xboole_0
% 23.66/3.50      | k1_xboole_0 != X0 ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_151]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_6667,plain,
% 23.66/3.50      ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
% 23.66/3.50      | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_xboole_0
% 23.66/3.50      | k1_xboole_0 != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_549]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_30600,plain,
% 23.66/3.50      ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) != sK4 ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_30177,c_20,c_713,c_6667]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_13,plain,
% 23.66/3.50      ( r2_hidden(sK2(X0,X1),X0)
% 23.66/3.50      | k1_enumset1(X1,X1,X1) = X0
% 23.66/3.50      | k1_xboole_0 = X0 ),
% 23.66/3.50      inference(cnf_transformation,[],[f66]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1182,plain,
% 23.66/3.50      ( r2_hidden(sK2(X0,X1),X0)
% 23.66/3.50      | X0 = k1_enumset1(X1,X1,X1)
% 23.66/3.50      | k1_xboole_0 = X0 ),
% 23.66/3.50      inference(resolution,[status(thm)],[c_894,c_13]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1307,plain,
% 23.66/3.50      ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4),k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)))
% 23.66/3.50      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 23.66/3.50      inference(resolution,[status(thm)],[c_1182,c_18]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_5,plain,
% 23.66/3.50      ( r2_hidden(X0,X1)
% 23.66/3.50      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 23.66/3.50      inference(cnf_transformation,[],[f76]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1339,plain,
% 23.66/3.50      ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4),k1_enumset1(sK3,sK3,sK4))
% 23.66/3.50      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 23.66/3.50      inference(resolution,[status(thm)],[c_1307,c_5]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11,plain,
% 23.66/3.50      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 23.66/3.50      inference(cnf_transformation,[],[f81]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1722,plain,
% 23.66/3.50      ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) = sK4
% 23.66/3.50      | sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) = sK3
% 23.66/3.50      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 23.66/3.50      inference(resolution,[status(thm)],[c_1339,c_11]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_30606,plain,
% 23.66/3.50      ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) = sK3
% 23.66/3.50      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 23.66/3.50      inference(backward_subsumption_resolution,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_30600,c_1722]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_31170,plain,
% 23.66/3.50      ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) = sK3 ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_30606,c_20,c_713,c_1722,c_6667,c_30177]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_154,plain,
% 23.66/3.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.66/3.50      theory(equality) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1176,plain,
% 23.66/3.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 23.66/3.50      inference(resolution,[status(thm)],[c_154,c_150]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_37607,plain,
% 23.66/3.50      ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4),X0)
% 23.66/3.50      | ~ r2_hidden(sK3,X0) ),
% 23.66/3.50      inference(resolution,[status(thm)],[c_31170,c_1176]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_4,plain,
% 23.66/3.50      ( ~ r2_hidden(X0,X1)
% 23.66/3.50      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 23.66/3.50      inference(cnf_transformation,[],[f75]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1155,plain,
% 23.66/3.50      ( ~ r2_hidden(sK2(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X1)
% 23.66/3.50      | k1_enumset1(X2,X2,X2) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
% 23.66/3.50      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 23.66/3.50      inference(resolution,[status(thm)],[c_13,c_4]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_79640,plain,
% 23.66/3.50      ( ~ r2_hidden(sK3,sK5)
% 23.66/3.50      | k1_enumset1(sK4,sK4,sK4) = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
% 23.66/3.50      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 23.66/3.50      inference(resolution,[status(thm)],[c_37607,c_1155]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_19,negated_conjecture,
% 23.66/3.50      ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK3,sK3,sK3) ),
% 23.66/3.50      inference(cnf_transformation,[],[f72]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_30178,plain,
% 23.66/3.50      ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3) != sK3
% 23.66/3.50      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 23.66/3.50      inference(resolution,[status(thm)],[c_2219,c_19]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_31109,plain,
% 23.66/3.50      ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3) != sK3 ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_30178,c_20,c_713,c_6667]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1309,plain,
% 23.66/3.50      ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)))
% 23.66/3.50      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 23.66/3.50      inference(resolution,[status(thm)],[c_1182,c_19]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1464,plain,
% 23.66/3.50      ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),k1_enumset1(sK3,sK3,sK4))
% 23.66/3.50      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 23.66/3.50      inference(resolution,[status(thm)],[c_1309,c_5]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1729,plain,
% 23.66/3.50      ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3) = sK4
% 23.66/3.50      | sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3) = sK3
% 23.66/3.50      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 23.66/3.50      inference(resolution,[status(thm)],[c_1464,c_11]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1927,plain,
% 23.66/3.50      ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),X0)
% 23.66/3.50      | ~ r2_hidden(sK4,X0)
% 23.66/3.50      | sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3) = sK3
% 23.66/3.50      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 23.66/3.50      inference(resolution,[status(thm)],[c_1729,c_1176]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_31118,plain,
% 23.66/3.50      ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),X0)
% 23.66/3.50      | ~ r2_hidden(sK4,X0)
% 23.66/3.50      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 23.66/3.50      inference(backward_subsumption_resolution,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_31109,c_1927]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_39085,plain,
% 23.66/3.50      ( ~ r2_hidden(sK4,X0)
% 23.66/3.50      | r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),X0) ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_31118,c_20,c_713,c_6667]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_39086,plain,
% 23.66/3.50      ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),X0)
% 23.66/3.50      | ~ r2_hidden(sK4,X0) ),
% 23.66/3.50      inference(renaming,[status(thm)],[c_39085]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1462,plain,
% 23.66/3.50      ( ~ r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),sK5)
% 23.66/3.50      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 23.66/3.50      inference(resolution,[status(thm)],[c_1309,c_4]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_39119,plain,
% 23.66/3.50      ( ~ r2_hidden(sK4,sK5)
% 23.66/3.50      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 23.66/3.50      inference(resolution,[status(thm)],[c_39086,c_1462]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_545,plain,
% 23.66/3.50      ( k1_enumset1(sK4,sK4,sK4) != X0
% 23.66/3.50      | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != X0
% 23.66/3.50      | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_enumset1(sK4,sK4,sK4) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_151]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_8351,plain,
% 23.66/3.50      ( k1_enumset1(sK4,sK4,sK4) != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
% 23.66/3.50      | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_enumset1(sK4,sK4,sK4)
% 23.66/3.50      | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_545]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_14,plain,
% 23.66/3.50      ( r2_hidden(X0,X1)
% 23.66/3.50      | r2_hidden(X2,X1)
% 23.66/3.50      | k5_xboole_0(k1_enumset1(X0,X0,X2),k3_xboole_0(k1_enumset1(X0,X0,X2),X1)) = k1_enumset1(X0,X0,X2) ),
% 23.66/3.50      inference(cnf_transformation,[],[f67]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_629,plain,
% 23.66/3.50      ( r2_hidden(sK4,sK5)
% 23.66/3.50      | r2_hidden(sK3,sK5)
% 23.66/3.50      | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_enumset1(sK3,sK3,sK4) ),
% 23.66/3.50      inference(instantiation,[status(thm)],[c_14]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_17,negated_conjecture,
% 23.66/3.50      ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK3,sK3,sK4) ),
% 23.66/3.50      inference(cnf_transformation,[],[f70]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(contradiction,plain,
% 23.66/3.50      ( $false ),
% 23.66/3.50      inference(minisat,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_79640,c_39119,c_8351,c_6667,c_713,c_629,c_17,c_18,
% 23.66/3.50                 c_20]) ).
% 23.66/3.50  
% 23.66/3.50  
% 23.66/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.66/3.50  
% 23.66/3.50  ------                               Statistics
% 23.66/3.50  
% 23.66/3.50  ------ Selected
% 23.66/3.50  
% 23.66/3.50  total_time:                             2.902
% 23.66/3.50  
%------------------------------------------------------------------------------
