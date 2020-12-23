%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:01 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :  115 (1433 expanded)
%              Number of clauses        :   53 ( 152 expanded)
%              Number of leaves         :   19 ( 444 expanded)
%              Depth                    :   21
%              Number of atoms          :  331 (3168 expanded)
%              Number of equality atoms :  252 (2470 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( X1 != X2
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( X1 != X2
        & k1_tarski(X0) = k2_tarski(X1,X2) )
   => ( sK4 != sK5
      & k1_tarski(sK3) = k2_tarski(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( sK4 != sK5
    & k1_tarski(sK3) = k2_tarski(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f16,f28])).

fof(f57,plain,(
    k1_tarski(sK3) = k2_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f64])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f60])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f53,f61])).

fof(f63,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f62])).

fof(f64,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f51,f63])).

fof(f70,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
    inference(definition_unfolding,[],[f57,f65,f64])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X8 != X10
              & X7 != X10
              & X6 != X10
              & X5 != X10
              & X4 != X10
              & X3 != X10
              & X2 != X10
              & X1 != X10
              & X0 != X10 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ( X8 = X10
            | X7 = X10
            | X6 = X10
            | X5 = X10
            | X4 = X10
            | X3 = X10
            | X2 = X10
            | X1 = X10
            | X0 = X10 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f17,plain,(
    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X8 = X10
        | X7 = X10
        | X6 = X10
        | X5 = X10
        | X4 = X10
        | X3 = X10
        | X2 = X10
        | X1 = X10
        | X0 = X10 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(definition_folding,[],[f15,f18,f17])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(definition_unfolding,[],[f48,f59,f65])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != X9 ) ),
    inference(definition_unfolding,[],[f46,f66])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) ),
    inference(equality_resolution,[],[f69])).

fof(f24,plain,(
    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X8 != X10
          & X7 != X10
          & X6 != X10
          & X5 != X10
          & X4 != X10
          & X3 != X10
          & X2 != X10
          & X1 != X10
          & X0 != X10 ) )
      & ( X8 = X10
        | X7 = X10
        | X6 = X10
        | X5 = X10
        | X4 = X10
        | X3 = X10
        | X2 = X10
        | X1 = X10
        | X0 = X10
        | ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X8 != X10
          & X7 != X10
          & X6 != X10
          & X5 != X10
          & X4 != X10
          & X3 != X10
          & X2 != X10
          & X1 != X10
          & X0 != X10 ) )
      & ( X8 = X10
        | X7 = X10
        | X6 = X10
        | X5 = X10
        | X4 = X10
        | X3 = X10
        | X2 = X10
        | X1 = X10
        | X0 = X10
        | ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8
          & X0 != X9 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | X0 = X9
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ) ),
    inference(rectify,[],[f25])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : sP0(X2,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(equality_resolution,[],[f44])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | ? [X10] :
            ( ( ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X9) )
            & ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X10,X9) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X9)
              | ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X9) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | ? [X10] :
            ( ( ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X9) )
            & ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X10,X9) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X9)
              | ~ sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X11,X9) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X10] :
          ( ( ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X10,X9) )
          & ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X10,X9) ) )
     => ( ( ~ sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
        & ( sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | ( ( ~ sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
          & ( sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X9)
              | ~ sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X11,X9) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | ~ sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f5])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f49,f59,f65,f56])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ r2_hidden(X11,X9)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( X0 = X1
      | X0 = X2
      | X0 = X3
      | X0 = X4
      | X0 = X5
      | X0 = X6
      | X0 = X7
      | X0 = X8
      | X0 = X9
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f71,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(equality_resolution,[],[f45])).

cnf(c_791,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1196,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_7630,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_18,negated_conjecture,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_16,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1071,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1360,plain,
    ( sP1(sK3,X0,X1,X2,X3,X4,X5,X6,X7,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_1071])).

cnf(c_6,plain,
    ( sP0(X0,X1,X0,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1081,plain,
    ( sP0(X0,X1,X0,X2,X3,X4,X5,X6,X7,X8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
    | ~ sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10)
    | r2_hidden(X0,X10) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1084,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != iProver_top
    | sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10) != iProver_top
    | r2_hidden(X0,X10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2235,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != iProver_top
    | r2_hidden(X7,X9) = iProver_top ),
    inference(superposition,[status(thm)],[c_1081,c_1084])).

cnf(c_5189,plain,
    ( r2_hidden(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X7),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X7),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1360,c_2235])).

cnf(c_0,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1373,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X0,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_18,c_0])).

cnf(c_1381,plain,
    ( k6_enumset1(X0,sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k6_enumset1(X0,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_1373,c_0])).

cnf(c_1967,plain,
    ( sP1(sK3,X0,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_xboole_0(k6_enumset1(X0,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_xboole_0(k6_enumset1(X0,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1381,c_1360])).

cnf(c_4,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
    | ~ sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10)
    | ~ r2_hidden(X0,X10) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1083,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = iProver_top
    | sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10) != iProver_top
    | r2_hidden(X0,X10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2547,plain,
    ( sP0(X0,sK3,sK3,sK3,sK3,sK3,sK3,sK3,X1,sK3) = iProver_top
    | r2_hidden(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_xboole_0(k6_enumset1(X1,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_xboole_0(k6_enumset1(X1,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1967,c_1083])).

cnf(c_5495,plain,
    ( sP0(sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5189,c_2547])).

cnf(c_14,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
    | X9 = X0
    | X8 = X0
    | X7 = X0
    | X6 = X0
    | X5 = X0
    | X4 = X0
    | X3 = X0
    | X2 = X0
    | X1 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1073,plain,
    ( X0 = X1
    | X2 = X1
    | X3 = X1
    | X4 = X1
    | X5 = X1
    | X6 = X1
    | X7 = X1
    | X8 = X1
    | X9 = X1
    | sP0(X1,X9,X8,X7,X6,X5,X4,X3,X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5640,plain,
    ( sK3 = sK4
    | sK4 = X0 ),
    inference(superposition,[status(thm)],[c_5495,c_1073])).

cnf(c_17,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1197,plain,
    ( sK5 != sK3
    | sK4 != sK3
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_1212,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_1310,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1212])).

cnf(c_1312,plain,
    ( sK3 != sK5
    | sK5 = sK3
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1310])).

cnf(c_790,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1311,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_790])).

cnf(c_1402,plain,
    ( ~ sP0(sK5,X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | X7 = sK5
    | X6 = sK5
    | X5 = sK5
    | X4 = sK5
    | X3 = sK5
    | X2 = sK5
    | X1 = sK5
    | X0 = sK5
    | X8 = sK5 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1403,plain,
    ( X0 = sK5
    | X1 = sK5
    | X2 = sK5
    | X3 = sK5
    | X4 = sK5
    | X5 = sK5
    | X6 = sK5
    | X7 = sK5
    | X8 = sK5
    | sP0(sK5,X7,X6,X5,X4,X3,X2,X1,X0,X8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1402])).

cnf(c_1405,plain,
    ( sK3 = sK5
    | sP0(sK5,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1403])).

cnf(c_1376,plain,
    ( sP1(X0,X1,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1071])).

cnf(c_5,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1082,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7,X8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2234,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != iProver_top
    | r2_hidden(X8,X9) = iProver_top ),
    inference(superposition,[status(thm)],[c_1082,c_1084])).

cnf(c_3708,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1376,c_2234])).

cnf(c_1358,plain,
    ( sP1(X0,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_1071])).

cnf(c_1798,plain,
    ( sP1(X0,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(X0,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1358,c_0])).

cnf(c_2188,plain,
    ( sP0(X0,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,X1) = iProver_top
    | r2_hidden(X0,k6_enumset1(X1,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1798,c_1083])).

cnf(c_4835,plain,
    ( sP0(sK5,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3708,c_2188])).

cnf(c_4849,plain,
    ( sP0(sK5,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4835])).

cnf(c_5652,plain,
    ( sK3 = sK4
    | sK4 = sK3 ),
    inference(instantiation,[status(thm)],[c_5640])).

cnf(c_6831,plain,
    ( sK3 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5640,c_17,c_1197,c_1312,c_1311,c_1405,c_4849,c_5652])).

cnf(c_3707,plain,
    ( r2_hidden(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1360,c_2234])).

cnf(c_5493,plain,
    ( sP0(sK5,sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3707,c_2547])).

cnf(c_5624,plain,
    ( sK3 = sK5
    | sK5 = X0 ),
    inference(superposition,[status(thm)],[c_5493,c_1073])).

cnf(c_6530,plain,
    ( sK3 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5624,c_1405,c_4849])).

cnf(c_6834,plain,
    ( sK5 = sK4 ),
    inference(demodulation,[status(thm)],[c_6831,c_6530])).

cnf(c_3296,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_790])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7630,c_6834,c_3296,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.69/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/0.99  
% 2.69/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.69/0.99  
% 2.69/0.99  ------  iProver source info
% 2.69/0.99  
% 2.69/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.69/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.69/0.99  git: non_committed_changes: false
% 2.69/0.99  git: last_make_outside_of_git: false
% 2.69/0.99  
% 2.69/0.99  ------ 
% 2.69/0.99  
% 2.69/0.99  ------ Input Options
% 2.69/0.99  
% 2.69/0.99  --out_options                           all
% 2.69/0.99  --tptp_safe_out                         true
% 2.69/0.99  --problem_path                          ""
% 2.69/0.99  --include_path                          ""
% 2.69/0.99  --clausifier                            res/vclausify_rel
% 2.69/0.99  --clausifier_options                    --mode clausify
% 2.69/0.99  --stdin                                 false
% 2.69/0.99  --stats_out                             all
% 2.69/0.99  
% 2.69/0.99  ------ General Options
% 2.69/0.99  
% 2.69/0.99  --fof                                   false
% 2.69/0.99  --time_out_real                         305.
% 2.69/0.99  --time_out_virtual                      -1.
% 2.69/0.99  --symbol_type_check                     false
% 2.69/0.99  --clausify_out                          false
% 2.69/0.99  --sig_cnt_out                           false
% 2.69/0.99  --trig_cnt_out                          false
% 2.69/0.99  --trig_cnt_out_tolerance                1.
% 2.69/0.99  --trig_cnt_out_sk_spl                   false
% 2.69/0.99  --abstr_cl_out                          false
% 2.69/0.99  
% 2.69/0.99  ------ Global Options
% 2.69/0.99  
% 2.69/0.99  --schedule                              default
% 2.69/0.99  --add_important_lit                     false
% 2.69/0.99  --prop_solver_per_cl                    1000
% 2.69/0.99  --min_unsat_core                        false
% 2.69/0.99  --soft_assumptions                      false
% 2.69/0.99  --soft_lemma_size                       3
% 2.69/0.99  --prop_impl_unit_size                   0
% 2.69/0.99  --prop_impl_unit                        []
% 2.69/0.99  --share_sel_clauses                     true
% 2.69/0.99  --reset_solvers                         false
% 2.69/0.99  --bc_imp_inh                            [conj_cone]
% 2.69/0.99  --conj_cone_tolerance                   3.
% 2.69/0.99  --extra_neg_conj                        none
% 2.69/0.99  --large_theory_mode                     true
% 2.69/0.99  --prolific_symb_bound                   200
% 2.69/0.99  --lt_threshold                          2000
% 2.69/0.99  --clause_weak_htbl                      true
% 2.69/0.99  --gc_record_bc_elim                     false
% 2.69/0.99  
% 2.69/0.99  ------ Preprocessing Options
% 2.69/0.99  
% 2.69/0.99  --preprocessing_flag                    true
% 2.69/0.99  --time_out_prep_mult                    0.1
% 2.69/0.99  --splitting_mode                        input
% 2.69/0.99  --splitting_grd                         true
% 2.69/0.99  --splitting_cvd                         false
% 2.69/0.99  --splitting_cvd_svl                     false
% 2.69/0.99  --splitting_nvd                         32
% 2.69/0.99  --sub_typing                            true
% 2.69/0.99  --prep_gs_sim                           true
% 2.69/0.99  --prep_unflatten                        true
% 2.69/0.99  --prep_res_sim                          true
% 2.69/0.99  --prep_upred                            true
% 2.69/0.99  --prep_sem_filter                       exhaustive
% 2.69/0.99  --prep_sem_filter_out                   false
% 2.69/0.99  --pred_elim                             true
% 2.69/0.99  --res_sim_input                         true
% 2.69/0.99  --eq_ax_congr_red                       true
% 2.69/0.99  --pure_diseq_elim                       true
% 2.69/0.99  --brand_transform                       false
% 2.69/0.99  --non_eq_to_eq                          false
% 2.69/0.99  --prep_def_merge                        true
% 2.69/0.99  --prep_def_merge_prop_impl              false
% 2.69/0.99  --prep_def_merge_mbd                    true
% 2.69/0.99  --prep_def_merge_tr_red                 false
% 2.69/0.99  --prep_def_merge_tr_cl                  false
% 2.69/0.99  --smt_preprocessing                     true
% 2.69/0.99  --smt_ac_axioms                         fast
% 2.69/0.99  --preprocessed_out                      false
% 2.69/0.99  --preprocessed_stats                    false
% 2.69/0.99  
% 2.69/0.99  ------ Abstraction refinement Options
% 2.69/0.99  
% 2.69/0.99  --abstr_ref                             []
% 2.69/0.99  --abstr_ref_prep                        false
% 2.69/0.99  --abstr_ref_until_sat                   false
% 2.69/0.99  --abstr_ref_sig_restrict                funpre
% 2.69/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/0.99  --abstr_ref_under                       []
% 2.69/0.99  
% 2.69/0.99  ------ SAT Options
% 2.69/0.99  
% 2.69/0.99  --sat_mode                              false
% 2.69/0.99  --sat_fm_restart_options                ""
% 2.69/0.99  --sat_gr_def                            false
% 2.69/0.99  --sat_epr_types                         true
% 2.69/0.99  --sat_non_cyclic_types                  false
% 2.69/0.99  --sat_finite_models                     false
% 2.69/0.99  --sat_fm_lemmas                         false
% 2.69/0.99  --sat_fm_prep                           false
% 2.69/0.99  --sat_fm_uc_incr                        true
% 2.69/0.99  --sat_out_model                         small
% 2.69/0.99  --sat_out_clauses                       false
% 2.69/0.99  
% 2.69/0.99  ------ QBF Options
% 2.69/0.99  
% 2.69/0.99  --qbf_mode                              false
% 2.69/0.99  --qbf_elim_univ                         false
% 2.69/0.99  --qbf_dom_inst                          none
% 2.69/0.99  --qbf_dom_pre_inst                      false
% 2.69/0.99  --qbf_sk_in                             false
% 2.69/0.99  --qbf_pred_elim                         true
% 2.69/0.99  --qbf_split                             512
% 2.69/0.99  
% 2.69/0.99  ------ BMC1 Options
% 2.69/0.99  
% 2.69/0.99  --bmc1_incremental                      false
% 2.69/0.99  --bmc1_axioms                           reachable_all
% 2.69/0.99  --bmc1_min_bound                        0
% 2.69/0.99  --bmc1_max_bound                        -1
% 2.69/0.99  --bmc1_max_bound_default                -1
% 2.69/0.99  --bmc1_symbol_reachability              true
% 2.69/0.99  --bmc1_property_lemmas                  false
% 2.69/0.99  --bmc1_k_induction                      false
% 2.69/0.99  --bmc1_non_equiv_states                 false
% 2.69/0.99  --bmc1_deadlock                         false
% 2.69/0.99  --bmc1_ucm                              false
% 2.69/0.99  --bmc1_add_unsat_core                   none
% 2.69/0.99  --bmc1_unsat_core_children              false
% 2.69/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/0.99  --bmc1_out_stat                         full
% 2.69/0.99  --bmc1_ground_init                      false
% 2.69/0.99  --bmc1_pre_inst_next_state              false
% 2.69/0.99  --bmc1_pre_inst_state                   false
% 2.69/0.99  --bmc1_pre_inst_reach_state             false
% 2.69/0.99  --bmc1_out_unsat_core                   false
% 2.69/0.99  --bmc1_aig_witness_out                  false
% 2.69/0.99  --bmc1_verbose                          false
% 2.69/0.99  --bmc1_dump_clauses_tptp                false
% 2.69/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.69/0.99  --bmc1_dump_file                        -
% 2.69/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.69/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.69/0.99  --bmc1_ucm_extend_mode                  1
% 2.69/0.99  --bmc1_ucm_init_mode                    2
% 2.69/0.99  --bmc1_ucm_cone_mode                    none
% 2.69/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.69/0.99  --bmc1_ucm_relax_model                  4
% 2.69/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.69/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/0.99  --bmc1_ucm_layered_model                none
% 2.69/0.99  --bmc1_ucm_max_lemma_size               10
% 2.69/0.99  
% 2.69/0.99  ------ AIG Options
% 2.69/0.99  
% 2.69/0.99  --aig_mode                              false
% 2.69/0.99  
% 2.69/0.99  ------ Instantiation Options
% 2.69/0.99  
% 2.69/0.99  --instantiation_flag                    true
% 2.69/0.99  --inst_sos_flag                         false
% 2.69/0.99  --inst_sos_phase                        true
% 2.69/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/0.99  --inst_lit_sel_side                     num_symb
% 2.69/0.99  --inst_solver_per_active                1400
% 2.69/0.99  --inst_solver_calls_frac                1.
% 2.69/0.99  --inst_passive_queue_type               priority_queues
% 2.69/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/0.99  --inst_passive_queues_freq              [25;2]
% 2.69/0.99  --inst_dismatching                      true
% 2.69/0.99  --inst_eager_unprocessed_to_passive     true
% 2.69/0.99  --inst_prop_sim_given                   true
% 2.69/0.99  --inst_prop_sim_new                     false
% 2.69/0.99  --inst_subs_new                         false
% 2.69/0.99  --inst_eq_res_simp                      false
% 2.69/0.99  --inst_subs_given                       false
% 2.69/0.99  --inst_orphan_elimination               true
% 2.69/0.99  --inst_learning_loop_flag               true
% 2.69/0.99  --inst_learning_start                   3000
% 2.69/0.99  --inst_learning_factor                  2
% 2.69/0.99  --inst_start_prop_sim_after_learn       3
% 2.69/0.99  --inst_sel_renew                        solver
% 2.69/0.99  --inst_lit_activity_flag                true
% 2.69/0.99  --inst_restr_to_given                   false
% 2.69/0.99  --inst_activity_threshold               500
% 2.69/0.99  --inst_out_proof                        true
% 2.69/0.99  
% 2.69/0.99  ------ Resolution Options
% 2.69/0.99  
% 2.69/0.99  --resolution_flag                       true
% 2.69/0.99  --res_lit_sel                           adaptive
% 2.69/0.99  --res_lit_sel_side                      none
% 2.69/0.99  --res_ordering                          kbo
% 2.69/0.99  --res_to_prop_solver                    active
% 2.69/0.99  --res_prop_simpl_new                    false
% 2.69/0.99  --res_prop_simpl_given                  true
% 2.69/0.99  --res_passive_queue_type                priority_queues
% 2.69/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/0.99  --res_passive_queues_freq               [15;5]
% 2.69/0.99  --res_forward_subs                      full
% 2.69/0.99  --res_backward_subs                     full
% 2.69/0.99  --res_forward_subs_resolution           true
% 2.69/0.99  --res_backward_subs_resolution          true
% 2.69/0.99  --res_orphan_elimination                true
% 2.69/0.99  --res_time_limit                        2.
% 2.69/0.99  --res_out_proof                         true
% 2.69/0.99  
% 2.69/0.99  ------ Superposition Options
% 2.69/0.99  
% 2.69/0.99  --superposition_flag                    true
% 2.69/0.99  --sup_passive_queue_type                priority_queues
% 2.69/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.69/0.99  --demod_completeness_check              fast
% 2.69/0.99  --demod_use_ground                      true
% 2.69/0.99  --sup_to_prop_solver                    passive
% 2.69/0.99  --sup_prop_simpl_new                    true
% 2.69/0.99  --sup_prop_simpl_given                  true
% 2.69/0.99  --sup_fun_splitting                     false
% 2.69/0.99  --sup_smt_interval                      50000
% 2.69/0.99  
% 2.69/0.99  ------ Superposition Simplification Setup
% 2.69/0.99  
% 2.69/0.99  --sup_indices_passive                   []
% 2.69/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.99  --sup_full_bw                           [BwDemod]
% 2.69/0.99  --sup_immed_triv                        [TrivRules]
% 2.69/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.99  --sup_immed_bw_main                     []
% 2.69/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.99  
% 2.69/0.99  ------ Combination Options
% 2.69/0.99  
% 2.69/0.99  --comb_res_mult                         3
% 2.69/0.99  --comb_sup_mult                         2
% 2.69/0.99  --comb_inst_mult                        10
% 2.69/0.99  
% 2.69/0.99  ------ Debug Options
% 2.69/0.99  
% 2.69/0.99  --dbg_backtrace                         false
% 2.69/0.99  --dbg_dump_prop_clauses                 false
% 2.69/0.99  --dbg_dump_prop_clauses_file            -
% 2.69/0.99  --dbg_out_stat                          false
% 2.69/0.99  ------ Parsing...
% 2.69/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.69/0.99  
% 2.69/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.69/0.99  
% 2.69/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.69/0.99  
% 2.69/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.69/0.99  ------ Proving...
% 2.69/0.99  ------ Problem Properties 
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  clauses                                 19
% 2.69/0.99  conjectures                             2
% 2.69/0.99  EPR                                     13
% 2.69/0.99  Horn                                    17
% 2.69/0.99  unary                                   13
% 2.69/0.99  binary                                  1
% 2.69/0.99  lits                                    37
% 2.69/0.99  lits eq                                 13
% 2.69/0.99  fd_pure                                 0
% 2.69/0.99  fd_pseudo                               0
% 2.69/0.99  fd_cond                                 0
% 2.69/0.99  fd_pseudo_cond                          2
% 2.69/0.99  AC symbols                              0
% 2.69/0.99  
% 2.69/0.99  ------ Schedule dynamic 5 is on 
% 2.69/0.99  
% 2.69/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  ------ 
% 2.69/0.99  Current options:
% 2.69/0.99  ------ 
% 2.69/0.99  
% 2.69/0.99  ------ Input Options
% 2.69/0.99  
% 2.69/0.99  --out_options                           all
% 2.69/0.99  --tptp_safe_out                         true
% 2.69/0.99  --problem_path                          ""
% 2.69/0.99  --include_path                          ""
% 2.69/0.99  --clausifier                            res/vclausify_rel
% 2.69/0.99  --clausifier_options                    --mode clausify
% 2.69/0.99  --stdin                                 false
% 2.69/0.99  --stats_out                             all
% 2.69/0.99  
% 2.69/0.99  ------ General Options
% 2.69/0.99  
% 2.69/0.99  --fof                                   false
% 2.69/0.99  --time_out_real                         305.
% 2.69/0.99  --time_out_virtual                      -1.
% 2.69/0.99  --symbol_type_check                     false
% 2.69/0.99  --clausify_out                          false
% 2.69/0.99  --sig_cnt_out                           false
% 2.69/0.99  --trig_cnt_out                          false
% 2.69/0.99  --trig_cnt_out_tolerance                1.
% 2.69/0.99  --trig_cnt_out_sk_spl                   false
% 2.69/0.99  --abstr_cl_out                          false
% 2.69/0.99  
% 2.69/0.99  ------ Global Options
% 2.69/0.99  
% 2.69/0.99  --schedule                              default
% 2.69/0.99  --add_important_lit                     false
% 2.69/0.99  --prop_solver_per_cl                    1000
% 2.69/0.99  --min_unsat_core                        false
% 2.69/0.99  --soft_assumptions                      false
% 2.69/0.99  --soft_lemma_size                       3
% 2.69/0.99  --prop_impl_unit_size                   0
% 2.69/0.99  --prop_impl_unit                        []
% 2.69/0.99  --share_sel_clauses                     true
% 2.69/0.99  --reset_solvers                         false
% 2.69/0.99  --bc_imp_inh                            [conj_cone]
% 2.69/0.99  --conj_cone_tolerance                   3.
% 2.69/0.99  --extra_neg_conj                        none
% 2.69/0.99  --large_theory_mode                     true
% 2.69/0.99  --prolific_symb_bound                   200
% 2.69/0.99  --lt_threshold                          2000
% 2.69/0.99  --clause_weak_htbl                      true
% 2.69/0.99  --gc_record_bc_elim                     false
% 2.69/0.99  
% 2.69/0.99  ------ Preprocessing Options
% 2.69/0.99  
% 2.69/0.99  --preprocessing_flag                    true
% 2.69/0.99  --time_out_prep_mult                    0.1
% 2.69/0.99  --splitting_mode                        input
% 2.69/0.99  --splitting_grd                         true
% 2.69/0.99  --splitting_cvd                         false
% 2.69/0.99  --splitting_cvd_svl                     false
% 2.69/0.99  --splitting_nvd                         32
% 2.69/0.99  --sub_typing                            true
% 2.69/0.99  --prep_gs_sim                           true
% 2.69/0.99  --prep_unflatten                        true
% 2.69/0.99  --prep_res_sim                          true
% 2.69/0.99  --prep_upred                            true
% 2.69/0.99  --prep_sem_filter                       exhaustive
% 2.69/0.99  --prep_sem_filter_out                   false
% 2.69/0.99  --pred_elim                             true
% 2.69/0.99  --res_sim_input                         true
% 2.69/0.99  --eq_ax_congr_red                       true
% 2.69/0.99  --pure_diseq_elim                       true
% 2.69/0.99  --brand_transform                       false
% 2.69/0.99  --non_eq_to_eq                          false
% 2.69/0.99  --prep_def_merge                        true
% 2.69/0.99  --prep_def_merge_prop_impl              false
% 2.69/0.99  --prep_def_merge_mbd                    true
% 2.69/0.99  --prep_def_merge_tr_red                 false
% 2.69/0.99  --prep_def_merge_tr_cl                  false
% 2.69/0.99  --smt_preprocessing                     true
% 2.69/0.99  --smt_ac_axioms                         fast
% 2.69/0.99  --preprocessed_out                      false
% 2.69/0.99  --preprocessed_stats                    false
% 2.69/0.99  
% 2.69/0.99  ------ Abstraction refinement Options
% 2.69/0.99  
% 2.69/0.99  --abstr_ref                             []
% 2.69/0.99  --abstr_ref_prep                        false
% 2.69/0.99  --abstr_ref_until_sat                   false
% 2.69/0.99  --abstr_ref_sig_restrict                funpre
% 2.69/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/0.99  --abstr_ref_under                       []
% 2.69/0.99  
% 2.69/0.99  ------ SAT Options
% 2.69/0.99  
% 2.69/0.99  --sat_mode                              false
% 2.69/0.99  --sat_fm_restart_options                ""
% 2.69/0.99  --sat_gr_def                            false
% 2.69/0.99  --sat_epr_types                         true
% 2.69/0.99  --sat_non_cyclic_types                  false
% 2.69/0.99  --sat_finite_models                     false
% 2.69/0.99  --sat_fm_lemmas                         false
% 2.69/0.99  --sat_fm_prep                           false
% 2.69/0.99  --sat_fm_uc_incr                        true
% 2.69/0.99  --sat_out_model                         small
% 2.69/0.99  --sat_out_clauses                       false
% 2.69/0.99  
% 2.69/0.99  ------ QBF Options
% 2.69/0.99  
% 2.69/0.99  --qbf_mode                              false
% 2.69/0.99  --qbf_elim_univ                         false
% 2.69/0.99  --qbf_dom_inst                          none
% 2.69/0.99  --qbf_dom_pre_inst                      false
% 2.69/0.99  --qbf_sk_in                             false
% 2.69/0.99  --qbf_pred_elim                         true
% 2.69/0.99  --qbf_split                             512
% 2.69/0.99  
% 2.69/0.99  ------ BMC1 Options
% 2.69/0.99  
% 2.69/0.99  --bmc1_incremental                      false
% 2.69/0.99  --bmc1_axioms                           reachable_all
% 2.69/0.99  --bmc1_min_bound                        0
% 2.69/0.99  --bmc1_max_bound                        -1
% 2.69/0.99  --bmc1_max_bound_default                -1
% 2.69/0.99  --bmc1_symbol_reachability              true
% 2.69/0.99  --bmc1_property_lemmas                  false
% 2.69/0.99  --bmc1_k_induction                      false
% 2.69/0.99  --bmc1_non_equiv_states                 false
% 2.69/0.99  --bmc1_deadlock                         false
% 2.69/0.99  --bmc1_ucm                              false
% 2.69/0.99  --bmc1_add_unsat_core                   none
% 2.69/0.99  --bmc1_unsat_core_children              false
% 2.69/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/0.99  --bmc1_out_stat                         full
% 2.69/0.99  --bmc1_ground_init                      false
% 2.69/0.99  --bmc1_pre_inst_next_state              false
% 2.69/0.99  --bmc1_pre_inst_state                   false
% 2.69/0.99  --bmc1_pre_inst_reach_state             false
% 2.69/0.99  --bmc1_out_unsat_core                   false
% 2.69/0.99  --bmc1_aig_witness_out                  false
% 2.69/0.99  --bmc1_verbose                          false
% 2.69/0.99  --bmc1_dump_clauses_tptp                false
% 2.69/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.69/0.99  --bmc1_dump_file                        -
% 2.69/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.69/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.69/0.99  --bmc1_ucm_extend_mode                  1
% 2.69/0.99  --bmc1_ucm_init_mode                    2
% 2.69/0.99  --bmc1_ucm_cone_mode                    none
% 2.69/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.69/0.99  --bmc1_ucm_relax_model                  4
% 2.69/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.69/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/0.99  --bmc1_ucm_layered_model                none
% 2.69/0.99  --bmc1_ucm_max_lemma_size               10
% 2.69/0.99  
% 2.69/0.99  ------ AIG Options
% 2.69/0.99  
% 2.69/0.99  --aig_mode                              false
% 2.69/0.99  
% 2.69/0.99  ------ Instantiation Options
% 2.69/0.99  
% 2.69/0.99  --instantiation_flag                    true
% 2.69/0.99  --inst_sos_flag                         false
% 2.69/0.99  --inst_sos_phase                        true
% 2.69/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/0.99  --inst_lit_sel_side                     none
% 2.69/0.99  --inst_solver_per_active                1400
% 2.69/0.99  --inst_solver_calls_frac                1.
% 2.69/0.99  --inst_passive_queue_type               priority_queues
% 2.69/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/0.99  --inst_passive_queues_freq              [25;2]
% 2.69/0.99  --inst_dismatching                      true
% 2.69/0.99  --inst_eager_unprocessed_to_passive     true
% 2.69/0.99  --inst_prop_sim_given                   true
% 2.69/0.99  --inst_prop_sim_new                     false
% 2.69/0.99  --inst_subs_new                         false
% 2.69/0.99  --inst_eq_res_simp                      false
% 2.69/0.99  --inst_subs_given                       false
% 2.69/0.99  --inst_orphan_elimination               true
% 2.69/0.99  --inst_learning_loop_flag               true
% 2.69/0.99  --inst_learning_start                   3000
% 2.69/0.99  --inst_learning_factor                  2
% 2.69/0.99  --inst_start_prop_sim_after_learn       3
% 2.69/0.99  --inst_sel_renew                        solver
% 2.69/0.99  --inst_lit_activity_flag                true
% 2.69/0.99  --inst_restr_to_given                   false
% 2.69/0.99  --inst_activity_threshold               500
% 2.69/0.99  --inst_out_proof                        true
% 2.69/0.99  
% 2.69/0.99  ------ Resolution Options
% 2.69/0.99  
% 2.69/0.99  --resolution_flag                       false
% 2.69/0.99  --res_lit_sel                           adaptive
% 2.69/0.99  --res_lit_sel_side                      none
% 2.69/0.99  --res_ordering                          kbo
% 2.69/0.99  --res_to_prop_solver                    active
% 2.69/0.99  --res_prop_simpl_new                    false
% 2.69/0.99  --res_prop_simpl_given                  true
% 2.69/0.99  --res_passive_queue_type                priority_queues
% 2.69/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/0.99  --res_passive_queues_freq               [15;5]
% 2.69/0.99  --res_forward_subs                      full
% 2.69/0.99  --res_backward_subs                     full
% 2.69/0.99  --res_forward_subs_resolution           true
% 2.69/0.99  --res_backward_subs_resolution          true
% 2.69/0.99  --res_orphan_elimination                true
% 2.69/0.99  --res_time_limit                        2.
% 2.69/0.99  --res_out_proof                         true
% 2.69/0.99  
% 2.69/0.99  ------ Superposition Options
% 2.69/0.99  
% 2.69/0.99  --superposition_flag                    true
% 2.69/0.99  --sup_passive_queue_type                priority_queues
% 2.69/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.69/0.99  --demod_completeness_check              fast
% 2.69/0.99  --demod_use_ground                      true
% 2.69/0.99  --sup_to_prop_solver                    passive
% 2.69/0.99  --sup_prop_simpl_new                    true
% 2.69/0.99  --sup_prop_simpl_given                  true
% 2.69/0.99  --sup_fun_splitting                     false
% 2.69/0.99  --sup_smt_interval                      50000
% 2.69/0.99  
% 2.69/0.99  ------ Superposition Simplification Setup
% 2.69/0.99  
% 2.69/0.99  --sup_indices_passive                   []
% 2.69/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.99  --sup_full_bw                           [BwDemod]
% 2.69/0.99  --sup_immed_triv                        [TrivRules]
% 2.69/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.99  --sup_immed_bw_main                     []
% 2.69/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.99  
% 2.69/0.99  ------ Combination Options
% 2.69/0.99  
% 2.69/0.99  --comb_res_mult                         3
% 2.69/0.99  --comb_sup_mult                         2
% 2.69/0.99  --comb_inst_mult                        10
% 2.69/0.99  
% 2.69/0.99  ------ Debug Options
% 2.69/0.99  
% 2.69/0.99  --dbg_backtrace                         false
% 2.69/0.99  --dbg_dump_prop_clauses                 false
% 2.69/0.99  --dbg_dump_prop_clauses_file            -
% 2.69/0.99  --dbg_out_stat                          false
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  ------ Proving...
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  % SZS status Theorem for theBenchmark.p
% 2.69/0.99  
% 2.69/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.69/0.99  
% 2.69/0.99  fof(f13,conjecture,(
% 2.69/0.99    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X1 = X2)),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f14,negated_conjecture,(
% 2.69/0.99    ~! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X1 = X2)),
% 2.69/0.99    inference(negated_conjecture,[],[f13])).
% 2.69/0.99  
% 2.69/0.99  fof(f16,plain,(
% 2.69/0.99    ? [X0,X1,X2] : (X1 != X2 & k1_tarski(X0) = k2_tarski(X1,X2))),
% 2.69/0.99    inference(ennf_transformation,[],[f14])).
% 2.69/0.99  
% 2.69/0.99  fof(f28,plain,(
% 2.69/0.99    ? [X0,X1,X2] : (X1 != X2 & k1_tarski(X0) = k2_tarski(X1,X2)) => (sK4 != sK5 & k1_tarski(sK3) = k2_tarski(sK4,sK5))),
% 2.69/0.99    introduced(choice_axiom,[])).
% 2.69/0.99  
% 2.69/0.99  fof(f29,plain,(
% 2.69/0.99    sK4 != sK5 & k1_tarski(sK3) = k2_tarski(sK4,sK5)),
% 2.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f16,f28])).
% 2.69/0.99  
% 2.69/0.99  fof(f57,plain,(
% 2.69/0.99    k1_tarski(sK3) = k2_tarski(sK4,sK5)),
% 2.69/0.99    inference(cnf_transformation,[],[f29])).
% 2.69/0.99  
% 2.69/0.99  fof(f6,axiom,(
% 2.69/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f50,plain,(
% 2.69/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f6])).
% 2.69/0.99  
% 2.69/0.99  fof(f65,plain,(
% 2.69/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.69/0.99    inference(definition_unfolding,[],[f50,f64])).
% 2.69/0.99  
% 2.69/0.99  fof(f7,axiom,(
% 2.69/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f51,plain,(
% 2.69/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f7])).
% 2.69/0.99  
% 2.69/0.99  fof(f8,axiom,(
% 2.69/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f52,plain,(
% 2.69/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f8])).
% 2.69/0.99  
% 2.69/0.99  fof(f9,axiom,(
% 2.69/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f53,plain,(
% 2.69/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f9])).
% 2.69/0.99  
% 2.69/0.99  fof(f10,axiom,(
% 2.69/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f54,plain,(
% 2.69/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f10])).
% 2.69/0.99  
% 2.69/0.99  fof(f11,axiom,(
% 2.69/0.99    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f55,plain,(
% 2.69/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f11])).
% 2.69/0.99  
% 2.69/0.99  fof(f12,axiom,(
% 2.69/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f56,plain,(
% 2.69/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f12])).
% 2.69/0.99  
% 2.69/0.99  fof(f60,plain,(
% 2.69/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.69/0.99    inference(definition_unfolding,[],[f55,f56])).
% 2.69/0.99  
% 2.69/0.99  fof(f61,plain,(
% 2.69/0.99    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.69/0.99    inference(definition_unfolding,[],[f54,f60])).
% 2.69/0.99  
% 2.69/0.99  fof(f62,plain,(
% 2.69/0.99    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.69/0.99    inference(definition_unfolding,[],[f53,f61])).
% 2.69/0.99  
% 2.69/0.99  fof(f63,plain,(
% 2.69/0.99    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.69/0.99    inference(definition_unfolding,[],[f52,f62])).
% 2.69/0.99  
% 2.69/0.99  fof(f64,plain,(
% 2.69/0.99    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.69/0.99    inference(definition_unfolding,[],[f51,f63])).
% 2.69/0.99  
% 2.69/0.99  fof(f70,plain,(
% 2.69/0.99    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)),
% 2.69/0.99    inference(definition_unfolding,[],[f57,f65,f64])).
% 2.69/0.99  
% 2.69/0.99  fof(f3,axiom,(
% 2.69/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> ~(X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)))),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f15,plain,(
% 2.69/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10)))),
% 2.69/0.99    inference(ennf_transformation,[],[f3])).
% 2.69/0.99  
% 2.69/0.99  fof(f18,plain,(
% 2.69/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) <=> ! [X10] : (r2_hidden(X10,X9) <=> sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.69/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.69/0.99  
% 2.69/0.99  fof(f17,plain,(
% 2.69/0.99    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10))),
% 2.69/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.69/0.99  
% 2.69/0.99  fof(f19,plain,(
% 2.69/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9))),
% 2.69/0.99    inference(definition_folding,[],[f15,f18,f17])).
% 2.69/0.99  
% 2.69/0.99  fof(f27,plain,(
% 2.69/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 2.69/0.99    inference(nnf_transformation,[],[f19])).
% 2.69/0.99  
% 2.69/0.99  fof(f46,plain,(
% 2.69/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 2.69/0.99    inference(cnf_transformation,[],[f27])).
% 2.69/0.99  
% 2.69/0.99  fof(f4,axiom,(
% 2.69/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f48,plain,(
% 2.69/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f4])).
% 2.69/0.99  
% 2.69/0.99  fof(f2,axiom,(
% 2.69/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f31,plain,(
% 2.69/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f2])).
% 2.69/0.99  
% 2.69/0.99  fof(f1,axiom,(
% 2.69/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f30,plain,(
% 2.69/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.69/0.99    inference(cnf_transformation,[],[f1])).
% 2.69/0.99  
% 2.69/0.99  fof(f59,plain,(
% 2.69/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 2.69/0.99    inference(definition_unfolding,[],[f31,f30])).
% 2.69/0.99  
% 2.69/0.99  fof(f66,plain,(
% 2.69/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.69/0.99    inference(definition_unfolding,[],[f48,f59,f65])).
% 2.69/0.99  
% 2.69/0.99  fof(f69,plain,(
% 2.69/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != X9) )),
% 2.69/0.99    inference(definition_unfolding,[],[f46,f66])).
% 2.69/0.99  
% 2.69/0.99  fof(f80,plain,(
% 2.69/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))))) )),
% 2.69/0.99    inference(equality_resolution,[],[f69])).
% 2.69/0.99  
% 2.69/0.99  fof(f24,plain,(
% 2.69/0.99    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.69/0.99    inference(nnf_transformation,[],[f17])).
% 2.69/0.99  
% 2.69/0.99  fof(f25,plain,(
% 2.69/0.99    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.69/0.99    inference(flattening,[],[f24])).
% 2.69/0.99  
% 2.69/0.99  fof(f26,plain,(
% 2.69/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8 & X0 != X9)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | X0 = X9 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 2.69/0.99    inference(rectify,[],[f25])).
% 2.69/0.99  
% 2.69/0.99  fof(f44,plain,(
% 2.69/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | X0 != X2) )),
% 2.69/0.99    inference(cnf_transformation,[],[f26])).
% 2.69/0.99  
% 2.69/0.99  fof(f72,plain,(
% 2.69/0.99    ( ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : (sP0(X2,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 2.69/0.99    inference(equality_resolution,[],[f44])).
% 2.69/0.99  
% 2.69/0.99  fof(f20,plain,(
% 2.69/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 2.69/0.99    inference(nnf_transformation,[],[f18])).
% 2.69/0.99  
% 2.69/0.99  fof(f21,plain,(
% 2.69/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9)))) & (! [X11] : ((r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 2.69/0.99    inference(rectify,[],[f20])).
% 2.69/0.99  
% 2.69/0.99  fof(f22,plain,(
% 2.69/0.99    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9))) => ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9))))),
% 2.69/0.99    introduced(choice_axiom,[])).
% 2.69/0.99  
% 2.69/0.99  fof(f23,plain,(
% 2.69/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)))) & (! [X11] : ((r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 2.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 2.69/0.99  
% 2.69/0.99  fof(f33,plain,(
% 2.69/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f23])).
% 2.69/0.99  
% 2.69/0.99  fof(f5,axiom,(
% 2.69/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 2.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f49,plain,(
% 2.69/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f5])).
% 2.69/0.99  
% 2.69/0.99  fof(f67,plain,(
% 2.69/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 2.69/0.99    inference(definition_unfolding,[],[f49,f59,f65,f56])).
% 2.69/0.99  
% 2.69/0.99  fof(f32,plain,(
% 2.69/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X9) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f23])).
% 2.69/0.99  
% 2.69/0.99  fof(f36,plain,(
% 2.69/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | X0 = X9 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f26])).
% 2.69/0.99  
% 2.69/0.99  fof(f58,plain,(
% 2.69/0.99    sK4 != sK5),
% 2.69/0.99    inference(cnf_transformation,[],[f29])).
% 2.69/0.99  
% 2.69/0.99  fof(f45,plain,(
% 2.69/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | X0 != X1) )),
% 2.69/0.99    inference(cnf_transformation,[],[f26])).
% 2.69/0.99  
% 2.69/0.99  fof(f71,plain,(
% 2.69/0.99    ( ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 2.69/0.99    inference(equality_resolution,[],[f45])).
% 2.69/0.99  
% 2.69/0.99  cnf(c_791,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1196,plain,
% 2.69/0.99      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_791]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_7630,plain,
% 2.69/0.99      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_1196]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_18,negated_conjecture,
% 2.69/0.99      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
% 2.69/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_16,plain,
% 2.69/0.99      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) ),
% 2.69/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1071,plain,
% 2.69/0.99      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) = iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1360,plain,
% 2.69/0.99      ( sP1(sK3,X0,X1,X2,X3,X4,X5,X6,X7,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))) = iProver_top ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_18,c_1071]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_6,plain,
% 2.69/0.99      ( sP0(X0,X1,X0,X2,X3,X4,X5,X6,X7,X8) ),
% 2.69/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1081,plain,
% 2.69/0.99      ( sP0(X0,X1,X0,X2,X3,X4,X5,X6,X7,X8) = iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3,plain,
% 2.69/0.99      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
% 2.69/0.99      | ~ sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10)
% 2.69/0.99      | r2_hidden(X0,X10) ),
% 2.69/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1084,plain,
% 2.69/0.99      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != iProver_top
% 2.69/0.99      | sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10) != iProver_top
% 2.69/0.99      | r2_hidden(X0,X10) = iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_2235,plain,
% 2.69/0.99      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != iProver_top
% 2.69/0.99      | r2_hidden(X7,X9) = iProver_top ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_1081,c_1084]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_5189,plain,
% 2.69/0.99      ( r2_hidden(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X7),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X7),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))) = iProver_top ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_1360,c_2235]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_0,plain,
% 2.69/0.99      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 2.69/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1373,plain,
% 2.69/0.99      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X0,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_18,c_0]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1381,plain,
% 2.69/0.99      ( k6_enumset1(X0,sK4,sK4,sK4,sK4,sK4,sK4,sK5) = k6_enumset1(X0,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 2.69/0.99      inference(demodulation,[status(thm)],[c_1373,c_0]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1967,plain,
% 2.69/0.99      ( sP1(sK3,X0,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_xboole_0(k6_enumset1(X0,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_xboole_0(k6_enumset1(X0,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))) = iProver_top ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_1381,c_1360]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_4,plain,
% 2.69/0.99      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
% 2.69/0.99      | ~ sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10)
% 2.69/0.99      | ~ r2_hidden(X0,X10) ),
% 2.69/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1083,plain,
% 2.69/0.99      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = iProver_top
% 2.69/0.99      | sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10) != iProver_top
% 2.69/0.99      | r2_hidden(X0,X10) != iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_2547,plain,
% 2.69/0.99      ( sP0(X0,sK3,sK3,sK3,sK3,sK3,sK3,sK3,X1,sK3) = iProver_top
% 2.69/0.99      | r2_hidden(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_xboole_0(k6_enumset1(X1,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_xboole_0(k6_enumset1(X1,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))) != iProver_top ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_1967,c_1083]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_5495,plain,
% 2.69/0.99      ( sP0(sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0,sK3) = iProver_top ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_5189,c_2547]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_14,plain,
% 2.69/0.99      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
% 2.69/0.99      | X9 = X0
% 2.69/0.99      | X8 = X0
% 2.69/0.99      | X7 = X0
% 2.69/0.99      | X6 = X0
% 2.69/0.99      | X5 = X0
% 2.69/0.99      | X4 = X0
% 2.69/0.99      | X3 = X0
% 2.69/0.99      | X2 = X0
% 2.69/0.99      | X1 = X0 ),
% 2.69/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1073,plain,
% 2.69/0.99      ( X0 = X1
% 2.69/0.99      | X2 = X1
% 2.69/0.99      | X3 = X1
% 2.69/0.99      | X4 = X1
% 2.69/0.99      | X5 = X1
% 2.69/0.99      | X6 = X1
% 2.69/0.99      | X7 = X1
% 2.69/0.99      | X8 = X1
% 2.69/0.99      | X9 = X1
% 2.69/0.99      | sP0(X1,X9,X8,X7,X6,X5,X4,X3,X2,X0) != iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_5640,plain,
% 2.69/0.99      ( sK3 = sK4 | sK4 = X0 ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_5495,c_1073]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_17,negated_conjecture,
% 2.69/0.99      ( sK4 != sK5 ),
% 2.69/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1197,plain,
% 2.69/0.99      ( sK5 != sK3 | sK4 != sK3 | sK4 = sK5 ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_1196]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1212,plain,
% 2.69/0.99      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_791]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1310,plain,
% 2.69/0.99      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_1212]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1312,plain,
% 2.69/0.99      ( sK3 != sK5 | sK5 = sK3 | sK5 != sK5 ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_1310]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_790,plain,( X0 = X0 ),theory(equality) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1311,plain,
% 2.69/0.99      ( sK5 = sK5 ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_790]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1402,plain,
% 2.69/0.99      ( ~ sP0(sK5,X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 2.69/0.99      | X7 = sK5
% 2.69/0.99      | X6 = sK5
% 2.69/0.99      | X5 = sK5
% 2.69/0.99      | X4 = sK5
% 2.69/0.99      | X3 = sK5
% 2.69/0.99      | X2 = sK5
% 2.69/0.99      | X1 = sK5
% 2.69/0.99      | X0 = sK5
% 2.69/0.99      | X8 = sK5 ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1403,plain,
% 2.69/0.99      ( X0 = sK5
% 2.69/0.99      | X1 = sK5
% 2.69/0.99      | X2 = sK5
% 2.69/0.99      | X3 = sK5
% 2.69/0.99      | X4 = sK5
% 2.69/0.99      | X5 = sK5
% 2.69/0.99      | X6 = sK5
% 2.69/0.99      | X7 = sK5
% 2.69/0.99      | X8 = sK5
% 2.69/0.99      | sP0(sK5,X7,X6,X5,X4,X3,X2,X1,X0,X8) != iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_1402]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1405,plain,
% 2.69/0.99      ( sK3 = sK5
% 2.69/0.99      | sP0(sK5,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != iProver_top ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_1403]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1376,plain,
% 2.69/0.99      ( sP1(X0,X1,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_0,c_1071]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_5,plain,
% 2.69/0.99      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
% 2.69/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1082,plain,
% 2.69/0.99      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7,X8) = iProver_top ),
% 2.69/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_2234,plain,
% 2.69/0.99      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != iProver_top
% 2.69/0.99      | r2_hidden(X8,X9) = iProver_top ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_1082,c_1084]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3708,plain,
% 2.69/0.99      ( r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)) = iProver_top ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_1376,c_2234]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1358,plain,
% 2.69/0.99      ( sP1(X0,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) = iProver_top ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_18,c_1071]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1798,plain,
% 2.69/0.99      ( sP1(X0,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k6_enumset1(X0,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = iProver_top ),
% 2.69/0.99      inference(demodulation,[status(thm)],[c_1358,c_0]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_2188,plain,
% 2.69/0.99      ( sP0(X0,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,X1) = iProver_top
% 2.69/0.99      | r2_hidden(X0,k6_enumset1(X1,sK4,sK4,sK4,sK4,sK4,sK4,sK5)) != iProver_top ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_1798,c_1083]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_4835,plain,
% 2.69/0.99      ( sP0(sK5,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0) = iProver_top ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_3708,c_2188]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_4849,plain,
% 2.69/0.99      ( sP0(sK5,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = iProver_top ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_4835]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_5652,plain,
% 2.69/0.99      ( sK3 = sK4 | sK4 = sK3 ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_5640]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_6831,plain,
% 2.69/0.99      ( sK3 = sK4 ),
% 2.69/0.99      inference(global_propositional_subsumption,
% 2.69/0.99                [status(thm)],
% 2.69/0.99                [c_5640,c_17,c_1197,c_1312,c_1311,c_1405,c_4849,c_5652]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3707,plain,
% 2.69/0.99      ( r2_hidden(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5))))) = iProver_top ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_1360,c_2234]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_5493,plain,
% 2.69/0.99      ( sP0(sK5,sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0,sK3) = iProver_top ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_3707,c_2547]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_5624,plain,
% 2.69/0.99      ( sK3 = sK5 | sK5 = X0 ),
% 2.69/0.99      inference(superposition,[status(thm)],[c_5493,c_1073]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_6530,plain,
% 2.69/0.99      ( sK3 = sK5 ),
% 2.69/0.99      inference(global_propositional_subsumption,
% 2.69/0.99                [status(thm)],
% 2.69/0.99                [c_5624,c_1405,c_4849]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_6834,plain,
% 2.69/0.99      ( sK5 = sK4 ),
% 2.69/0.99      inference(demodulation,[status(thm)],[c_6831,c_6530]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3296,plain,
% 2.69/0.99      ( sK4 = sK4 ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_790]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(contradiction,plain,
% 2.69/0.99      ( $false ),
% 2.69/0.99      inference(minisat,[status(thm)],[c_7630,c_6834,c_3296,c_17]) ).
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.69/0.99  
% 2.69/0.99  ------                               Statistics
% 2.69/0.99  
% 2.69/0.99  ------ General
% 2.69/0.99  
% 2.69/0.99  abstr_ref_over_cycles:                  0
% 2.69/0.99  abstr_ref_under_cycles:                 0
% 2.69/0.99  gc_basic_clause_elim:                   0
% 2.69/0.99  forced_gc_time:                         0
% 2.69/0.99  parsing_time:                           0.008
% 2.69/0.99  unif_index_cands_time:                  0.
% 2.69/0.99  unif_index_add_time:                    0.
% 2.69/0.99  orderings_time:                         0.
% 2.69/0.99  out_proof_time:                         0.011
% 2.69/0.99  total_time:                             0.38
% 2.69/0.99  num_of_symbols:                         41
% 2.69/0.99  num_of_terms:                           10546
% 2.69/0.99  
% 2.69/0.99  ------ Preprocessing
% 2.69/0.99  
% 2.69/0.99  num_of_splits:                          0
% 2.69/0.99  num_of_split_atoms:                     0
% 2.69/0.99  num_of_reused_defs:                     0
% 2.69/0.99  num_eq_ax_congr_red:                    58
% 2.69/0.99  num_of_sem_filtered_clauses:            1
% 2.69/0.99  num_of_subtypes:                        0
% 2.69/0.99  monotx_restored_types:                  0
% 2.69/0.99  sat_num_of_epr_types:                   0
% 2.69/0.99  sat_num_of_non_cyclic_types:            0
% 2.69/0.99  sat_guarded_non_collapsed_types:        0
% 2.69/0.99  num_pure_diseq_elim:                    0
% 2.69/0.99  simp_replaced_by:                       0
% 2.69/0.99  res_preprocessed:                       74
% 2.69/0.99  prep_upred:                             0
% 2.69/0.99  prep_unflattend:                        365
% 2.69/0.99  smt_new_axioms:                         0
% 2.69/0.99  pred_elim_cands:                        3
% 2.69/0.99  pred_elim:                              0
% 2.69/0.99  pred_elim_cl:                           0
% 2.69/0.99  pred_elim_cycles:                       3
% 2.69/0.99  merged_defs:                            0
% 2.69/0.99  merged_defs_ncl:                        0
% 2.69/0.99  bin_hyper_res:                          0
% 2.69/0.99  prep_cycles:                            3
% 2.69/0.99  pred_elim_time:                         0.015
% 2.69/0.99  splitting_time:                         0.
% 2.69/0.99  sem_filter_time:                        0.
% 2.69/0.99  monotx_time:                            0.
% 2.69/0.99  subtype_inf_time:                       0.
% 2.69/0.99  
% 2.69/0.99  ------ Problem properties
% 2.69/0.99  
% 2.69/0.99  clauses:                                19
% 2.69/0.99  conjectures:                            2
% 2.69/0.99  epr:                                    13
% 2.69/0.99  horn:                                   17
% 2.69/0.99  ground:                                 2
% 2.69/0.99  unary:                                  13
% 2.69/0.99  binary:                                 1
% 2.69/0.99  lits:                                   37
% 2.69/0.99  lits_eq:                                13
% 2.69/0.99  fd_pure:                                0
% 2.69/0.99  fd_pseudo:                              0
% 2.69/0.99  fd_cond:                                0
% 2.69/0.99  fd_pseudo_cond:                         2
% 2.69/0.99  ac_symbols:                             0
% 2.69/0.99  
% 2.69/0.99  ------ Propositional Solver
% 2.69/0.99  
% 2.69/0.99  prop_solver_calls:                      26
% 2.69/0.99  prop_fast_solver_calls:                 570
% 2.69/0.99  smt_solver_calls:                       0
% 2.69/0.99  smt_fast_solver_calls:                  0
% 2.69/0.99  prop_num_of_clauses:                    2372
% 2.69/0.99  prop_preprocess_simplified:             6298
% 2.69/0.99  prop_fo_subsumed:                       2
% 2.69/0.99  prop_solver_time:                       0.
% 2.69/0.99  smt_solver_time:                        0.
% 2.69/0.99  smt_fast_solver_time:                   0.
% 2.69/0.99  prop_fast_solver_time:                  0.
% 2.69/0.99  prop_unsat_core_time:                   0.
% 2.69/0.99  
% 2.69/0.99  ------ QBF
% 2.69/0.99  
% 2.69/0.99  qbf_q_res:                              0
% 2.69/0.99  qbf_num_tautologies:                    0
% 2.69/0.99  qbf_prep_cycles:                        0
% 2.69/0.99  
% 2.69/0.99  ------ BMC1
% 2.69/0.99  
% 2.69/0.99  bmc1_current_bound:                     -1
% 2.69/0.99  bmc1_last_solved_bound:                 -1
% 2.69/0.99  bmc1_unsat_core_size:                   -1
% 2.69/0.99  bmc1_unsat_core_parents_size:           -1
% 2.69/0.99  bmc1_merge_next_fun:                    0
% 2.69/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.69/0.99  
% 2.69/0.99  ------ Instantiation
% 2.69/0.99  
% 2.69/0.99  inst_num_of_clauses:                    564
% 2.69/0.99  inst_num_in_passive:                    257
% 2.69/0.99  inst_num_in_active:                     250
% 2.69/0.99  inst_num_in_unprocessed:                56
% 2.69/0.99  inst_num_of_loops:                      354
% 2.69/0.99  inst_num_of_learning_restarts:          0
% 2.69/0.99  inst_num_moves_active_passive:          98
% 2.69/0.99  inst_lit_activity:                      0
% 2.69/0.99  inst_lit_activity_moves:                0
% 2.69/0.99  inst_num_tautologies:                   0
% 2.69/0.99  inst_num_prop_implied:                  0
% 2.69/0.99  inst_num_existing_simplified:           0
% 2.69/0.99  inst_num_eq_res_simplified:             0
% 2.69/0.99  inst_num_child_elim:                    0
% 2.69/0.99  inst_num_of_dismatching_blockings:      520
% 2.69/0.99  inst_num_of_non_proper_insts:           863
% 2.69/0.99  inst_num_of_duplicates:                 0
% 2.69/0.99  inst_inst_num_from_inst_to_res:         0
% 2.69/0.99  inst_dismatching_checking_time:         0.
% 2.69/0.99  
% 2.69/0.99  ------ Resolution
% 2.69/0.99  
% 2.69/0.99  res_num_of_clauses:                     0
% 2.69/0.99  res_num_in_passive:                     0
% 2.69/0.99  res_num_in_active:                      0
% 2.69/0.99  res_num_of_loops:                       77
% 2.69/0.99  res_forward_subset_subsumed:            492
% 2.69/0.99  res_backward_subset_subsumed:           0
% 2.69/0.99  res_forward_subsumed:                   0
% 2.69/0.99  res_backward_subsumed:                  0
% 2.69/0.99  res_forward_subsumption_resolution:     0
% 2.69/0.99  res_backward_subsumption_resolution:    0
% 2.69/0.99  res_clause_to_clause_subsumption:       2160
% 2.69/0.99  res_orphan_elimination:                 0
% 2.69/0.99  res_tautology_del:                      37
% 2.69/0.99  res_num_eq_res_simplified:              0
% 2.69/0.99  res_num_sel_changes:                    0
% 2.69/0.99  res_moves_from_active_to_pass:          0
% 2.69/0.99  
% 2.69/0.99  ------ Superposition
% 2.69/0.99  
% 2.69/0.99  sup_time_total:                         0.
% 2.69/0.99  sup_time_generating:                    0.
% 2.69/0.99  sup_time_sim_full:                      0.
% 2.69/0.99  sup_time_sim_immed:                     0.
% 2.69/0.99  
% 2.69/0.99  sup_num_of_clauses:                     102
% 2.69/0.99  sup_num_in_active:                      38
% 2.69/0.99  sup_num_in_passive:                     64
% 2.69/0.99  sup_num_of_loops:                       70
% 2.69/0.99  sup_fw_superposition:                   207
% 2.69/0.99  sup_bw_superposition:                   151
% 2.69/0.99  sup_immediate_simplified:               109
% 2.69/0.99  sup_given_eliminated:                   0
% 2.69/0.99  comparisons_done:                       0
% 2.69/0.99  comparisons_avoided:                    0
% 2.69/0.99  
% 2.69/0.99  ------ Simplifications
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  sim_fw_subset_subsumed:                 4
% 2.69/0.99  sim_bw_subset_subsumed:                 0
% 2.69/0.99  sim_fw_subsumed:                        37
% 2.69/0.99  sim_bw_subsumed:                        10
% 2.69/0.99  sim_fw_subsumption_res:                 0
% 2.69/0.99  sim_bw_subsumption_res:                 0
% 2.69/0.99  sim_tautology_del:                      0
% 2.69/0.99  sim_eq_tautology_del:                   19
% 2.69/0.99  sim_eq_res_simp:                        2
% 2.69/0.99  sim_fw_demodulated:                     22
% 2.69/0.99  sim_bw_demodulated:                     32
% 2.69/0.99  sim_light_normalised:                   56
% 2.69/0.99  sim_joinable_taut:                      0
% 2.69/0.99  sim_joinable_simp:                      0
% 2.69/0.99  sim_ac_normalised:                      0
% 2.69/0.99  sim_smt_subsumption:                    0
% 2.69/0.99  
%------------------------------------------------------------------------------
