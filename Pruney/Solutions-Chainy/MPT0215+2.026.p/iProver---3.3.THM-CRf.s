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
% DateTime   : Thu Dec  3 11:28:58 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 282 expanded)
%              Number of clauses        :   28 (  31 expanded)
%              Number of leaves         :   17 (  86 expanded)
%              Depth                    :   16
%              Number of atoms          :  274 ( 632 expanded)
%              Number of equality atoms :  171 ( 464 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

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

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f64])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f49,f59,f65,f56])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & k1_tarski(X0) = k2_tarski(X1,X2) )
   => ( sK3 != sK4
      & k1_tarski(sK3) = k2_tarski(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( sK3 != sK4
    & k1_tarski(sK3) = k2_tarski(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f16,f28])).

fof(f57,plain,(
    k1_tarski(sK3) = k2_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f29])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f4])).

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

fof(f32,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ r2_hidden(X11,X9)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f38,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | X0 != X8 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(equality_resolution,[],[f38])).

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
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_3,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
    | ~ sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10)
    | r2_hidden(X0,X10) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1364,plain,
    ( ~ sP0(sK4,X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)
    | r2_hidden(sK4,X9) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1490,plain,
    ( ~ sP0(sK4,X0,X1,X2,X3,X4,X5,X6,sK4,X7)
    | ~ sP1(X7,sK4,X6,X5,X4,X3,X2,X1,X0,X8)
    | r2_hidden(sK4,X8) ),
    inference(instantiation,[status(thm)],[c_1364])).

cnf(c_2761,plain,
    ( ~ sP0(sK4,X0,X1,X2,X3,X4,X5,X6,sK4,X7)
    | ~ sP1(X7,sK4,X6,X5,X4,X3,X2,X1,X0,k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k5_xboole_0(k6_enumset1(X9,X10,X11,X12,X13,X14,X15,sK3),k3_xboole_0(k6_enumset1(X9,X10,X11,X12,X13,X14,X15,sK3),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8)))))
    | r2_hidden(sK4,k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k5_xboole_0(k6_enumset1(X9,X10,X11,X12,X13,X14,X15,sK3),k3_xboole_0(k6_enumset1(X9,X10,X11,X12,X13,X14,X15,sK3),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))))) ),
    inference(instantiation,[status(thm)],[c_1490])).

cnf(c_2803,plain,
    ( ~ sP0(sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4,sK3)
    | ~ sP1(sK3,sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))
    | r2_hidden(sK4,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) ),
    inference(instantiation,[status(thm)],[c_2761])).

cnf(c_0,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_18,negated_conjecture,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1179,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X0,sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
    inference(superposition,[status(thm)],[c_18,c_0])).

cnf(c_1824,plain,
    ( k6_enumset1(X0,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(X0,sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
    inference(superposition,[status(thm)],[c_0,c_1179])).

cnf(c_2002,plain,
    ( k6_enumset1(sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_1824,c_18])).

cnf(c_16,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1090,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2007,plain,
    ( sP1(X0,sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2002,c_1090])).

cnf(c_2009,plain,
    ( sP1(X0,sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2007])).

cnf(c_2011,plain,
    ( sP1(sK3,sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) ),
    inference(instantiation,[status(thm)],[c_2009])).

cnf(c_4,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
    | ~ sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10)
    | ~ r2_hidden(X0,X10) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1203,plain,
    ( sP0(sK4,sK3,X0,X1,X2,X3,X4,X5,X6,X7)
    | ~ sP1(X7,X6,X5,X4,X3,X2,X1,X0,sK3,X8)
    | ~ r2_hidden(sK4,X8) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1942,plain,
    ( sP0(sK4,sK3,X0,X1,X2,X3,X4,X5,X6,X7)
    | ~ sP1(X7,X6,X5,X4,X3,X2,X1,X0,sK3,k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k5_xboole_0(k6_enumset1(X6,X5,X4,X3,X2,X1,X0,sK3),k3_xboole_0(k6_enumset1(X6,X5,X4,X3,X2,X1,X0,sK3),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)))))
    | ~ r2_hidden(sK4,k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k5_xboole_0(k6_enumset1(X6,X5,X4,X3,X2,X1,X0,sK3),k3_xboole_0(k6_enumset1(X6,X5,X4,X3,X2,X1,X0,sK3),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7))))) ),
    inference(instantiation,[status(thm)],[c_1203])).

cnf(c_1945,plain,
    ( sP0(sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | ~ sP1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))
    | ~ r2_hidden(sK4,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) ),
    inference(instantiation,[status(thm)],[c_1942])).

cnf(c_12,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0,X8) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1269,plain,
    ( sP0(sK4,sK3,X0,X1,X2,X3,X4,X5,sK4,X6) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1275,plain,
    ( sP0(sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1269])).

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

cnf(c_1149,plain,
    ( ~ sP0(sK4,sK3,X0,X1,X2,X3,X4,X5,X6,X7)
    | X7 = sK4
    | X6 = sK4
    | X5 = sK4
    | X4 = sK4
    | X3 = sK4
    | X2 = sK4
    | X1 = sK4
    | X0 = sK4
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1151,plain,
    ( ~ sP0(sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_20,plain,
    ( sP1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_17,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2803,c_2011,c_1945,c_1275,c_1151,c_20,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:47:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.60/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.04  
% 3.60/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.60/1.04  
% 3.60/1.04  ------  iProver source info
% 3.60/1.04  
% 3.60/1.04  git: date: 2020-06-30 10:37:57 +0100
% 3.60/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.60/1.04  git: non_committed_changes: false
% 3.60/1.04  git: last_make_outside_of_git: false
% 3.60/1.04  
% 3.60/1.04  ------ 
% 3.60/1.04  ------ Parsing...
% 3.60/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.60/1.04  
% 3.60/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.60/1.04  
% 3.60/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.60/1.04  
% 3.60/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.60/1.04  ------ Proving...
% 3.60/1.04  ------ Problem Properties 
% 3.60/1.04  
% 3.60/1.04  
% 3.60/1.04  clauses                                 19
% 3.60/1.04  conjectures                             2
% 3.60/1.04  EPR                                     13
% 3.60/1.04  Horn                                    17
% 3.60/1.04  unary                                   13
% 3.60/1.04  binary                                  1
% 3.60/1.04  lits                                    37
% 3.60/1.04  lits eq                                 13
% 3.60/1.04  fd_pure                                 0
% 3.60/1.04  fd_pseudo                               0
% 3.60/1.04  fd_cond                                 0
% 3.60/1.04  fd_pseudo_cond                          2
% 3.60/1.04  AC symbols                              0
% 3.60/1.04  
% 3.60/1.04  ------ Input Options Time Limit: Unbounded
% 3.60/1.04  
% 3.60/1.04  
% 3.60/1.04  ------ 
% 3.60/1.04  Current options:
% 3.60/1.04  ------ 
% 3.60/1.04  
% 3.60/1.04  
% 3.60/1.04  
% 3.60/1.04  
% 3.60/1.04  ------ Proving...
% 3.60/1.04  
% 3.60/1.04  
% 3.60/1.04  % SZS status Theorem for theBenchmark.p
% 3.60/1.04  
% 3.60/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 3.60/1.04  
% 3.60/1.04  fof(f18,plain,(
% 3.60/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) <=> ! [X10] : (r2_hidden(X10,X9) <=> sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.60/1.04    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.60/1.04  
% 3.60/1.04  fof(f20,plain,(
% 3.60/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 3.60/1.04    inference(nnf_transformation,[],[f18])).
% 3.60/1.04  
% 3.60/1.04  fof(f21,plain,(
% 3.60/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9)))) & (! [X11] : ((r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 3.60/1.04    inference(rectify,[],[f20])).
% 3.60/1.04  
% 3.60/1.04  fof(f22,plain,(
% 3.60/1.04    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9))) => ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9))))),
% 3.60/1.04    introduced(choice_axiom,[])).
% 3.60/1.04  
% 3.60/1.04  fof(f23,plain,(
% 3.60/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)))) & (! [X11] : ((r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 3.60/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 3.60/1.04  
% 3.60/1.04  fof(f33,plain,(
% 3.60/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 3.60/1.04    inference(cnf_transformation,[],[f23])).
% 3.60/1.04  
% 3.60/1.04  fof(f5,axiom,(
% 3.60/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.60/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.04  
% 3.60/1.04  fof(f49,plain,(
% 3.60/1.04    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.60/1.04    inference(cnf_transformation,[],[f5])).
% 3.60/1.04  
% 3.60/1.04  fof(f2,axiom,(
% 3.60/1.04    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.60/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.04  
% 3.60/1.04  fof(f31,plain,(
% 3.60/1.04    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.60/1.04    inference(cnf_transformation,[],[f2])).
% 3.60/1.04  
% 3.60/1.04  fof(f1,axiom,(
% 3.60/1.04    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.60/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.04  
% 3.60/1.04  fof(f30,plain,(
% 3.60/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.60/1.04    inference(cnf_transformation,[],[f1])).
% 3.60/1.04  
% 3.60/1.04  fof(f59,plain,(
% 3.60/1.04    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.60/1.04    inference(definition_unfolding,[],[f31,f30])).
% 3.60/1.04  
% 3.60/1.04  fof(f6,axiom,(
% 3.60/1.04    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.60/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.04  
% 3.60/1.04  fof(f50,plain,(
% 3.60/1.04    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.60/1.04    inference(cnf_transformation,[],[f6])).
% 3.60/1.04  
% 3.60/1.04  fof(f7,axiom,(
% 3.60/1.04    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.60/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.04  
% 3.60/1.04  fof(f51,plain,(
% 3.60/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.60/1.04    inference(cnf_transformation,[],[f7])).
% 3.60/1.04  
% 3.60/1.04  fof(f8,axiom,(
% 3.60/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.60/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.04  
% 3.60/1.04  fof(f52,plain,(
% 3.60/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.60/1.04    inference(cnf_transformation,[],[f8])).
% 3.60/1.04  
% 3.60/1.04  fof(f9,axiom,(
% 3.60/1.04    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.60/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.04  
% 3.60/1.04  fof(f53,plain,(
% 3.60/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.60/1.04    inference(cnf_transformation,[],[f9])).
% 3.60/1.04  
% 3.60/1.04  fof(f10,axiom,(
% 3.60/1.04    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.60/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.04  
% 3.60/1.04  fof(f54,plain,(
% 3.60/1.04    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.60/1.04    inference(cnf_transformation,[],[f10])).
% 3.60/1.04  
% 3.60/1.04  fof(f11,axiom,(
% 3.60/1.04    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.60/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.04  
% 3.60/1.04  fof(f55,plain,(
% 3.60/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.60/1.04    inference(cnf_transformation,[],[f11])).
% 3.60/1.04  
% 3.60/1.04  fof(f60,plain,(
% 3.60/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.60/1.04    inference(definition_unfolding,[],[f55,f56])).
% 3.60/1.04  
% 3.60/1.04  fof(f61,plain,(
% 3.60/1.04    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.60/1.04    inference(definition_unfolding,[],[f54,f60])).
% 3.60/1.04  
% 3.60/1.04  fof(f62,plain,(
% 3.60/1.04    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.60/1.04    inference(definition_unfolding,[],[f53,f61])).
% 3.60/1.04  
% 3.60/1.04  fof(f63,plain,(
% 3.60/1.04    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.60/1.04    inference(definition_unfolding,[],[f52,f62])).
% 3.60/1.04  
% 3.60/1.04  fof(f64,plain,(
% 3.60/1.04    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.60/1.04    inference(definition_unfolding,[],[f51,f63])).
% 3.60/1.04  
% 3.60/1.04  fof(f65,plain,(
% 3.60/1.04    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.60/1.04    inference(definition_unfolding,[],[f50,f64])).
% 3.60/1.04  
% 3.60/1.04  fof(f12,axiom,(
% 3.60/1.04    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.60/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.04  
% 3.60/1.04  fof(f56,plain,(
% 3.60/1.04    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.60/1.04    inference(cnf_transformation,[],[f12])).
% 3.60/1.04  
% 3.60/1.04  fof(f67,plain,(
% 3.60/1.04    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.60/1.04    inference(definition_unfolding,[],[f49,f59,f65,f56])).
% 3.60/1.04  
% 3.60/1.04  fof(f13,conjecture,(
% 3.60/1.04    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 3.60/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.04  
% 3.60/1.04  fof(f14,negated_conjecture,(
% 3.60/1.04    ~! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 3.60/1.04    inference(negated_conjecture,[],[f13])).
% 3.60/1.04  
% 3.60/1.04  fof(f16,plain,(
% 3.60/1.04    ? [X0,X1,X2] : (X0 != X1 & k1_tarski(X0) = k2_tarski(X1,X2))),
% 3.60/1.04    inference(ennf_transformation,[],[f14])).
% 3.60/1.04  
% 3.60/1.04  fof(f28,plain,(
% 3.60/1.04    ? [X0,X1,X2] : (X0 != X1 & k1_tarski(X0) = k2_tarski(X1,X2)) => (sK3 != sK4 & k1_tarski(sK3) = k2_tarski(sK4,sK5))),
% 3.60/1.04    introduced(choice_axiom,[])).
% 3.60/1.04  
% 3.60/1.04  fof(f29,plain,(
% 3.60/1.04    sK3 != sK4 & k1_tarski(sK3) = k2_tarski(sK4,sK5)),
% 3.60/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f16,f28])).
% 3.60/1.04  
% 3.60/1.04  fof(f57,plain,(
% 3.60/1.04    k1_tarski(sK3) = k2_tarski(sK4,sK5)),
% 3.60/1.04    inference(cnf_transformation,[],[f29])).
% 3.60/1.04  
% 3.60/1.04  fof(f70,plain,(
% 3.60/1.04    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5)),
% 3.60/1.04    inference(definition_unfolding,[],[f57,f65,f64])).
% 3.60/1.04  
% 3.60/1.04  fof(f3,axiom,(
% 3.60/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> ~(X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)))),
% 3.60/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.04  
% 3.60/1.04  fof(f15,plain,(
% 3.60/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10)))),
% 3.60/1.04    inference(ennf_transformation,[],[f3])).
% 3.60/1.04  
% 3.60/1.04  fof(f17,plain,(
% 3.60/1.04    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10))),
% 3.60/1.04    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.60/1.04  
% 3.60/1.04  fof(f19,plain,(
% 3.60/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9))),
% 3.60/1.04    inference(definition_folding,[],[f15,f18,f17])).
% 3.60/1.04  
% 3.60/1.04  fof(f27,plain,(
% 3.60/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 3.60/1.04    inference(nnf_transformation,[],[f19])).
% 3.60/1.04  
% 3.60/1.04  fof(f46,plain,(
% 3.60/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 3.60/1.04    inference(cnf_transformation,[],[f27])).
% 3.60/1.04  
% 3.60/1.04  fof(f4,axiom,(
% 3.60/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 3.60/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.04  
% 3.60/1.04  fof(f48,plain,(
% 3.60/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.60/1.04    inference(cnf_transformation,[],[f4])).
% 3.60/1.04  
% 3.60/1.04  fof(f66,plain,(
% 3.60/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.60/1.04    inference(definition_unfolding,[],[f48,f59,f65])).
% 3.60/1.04  
% 3.60/1.04  fof(f69,plain,(
% 3.60/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != X9) )),
% 3.60/1.04    inference(definition_unfolding,[],[f46,f66])).
% 3.60/1.04  
% 3.60/1.04  fof(f80,plain,(
% 3.60/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))))) )),
% 3.60/1.04    inference(equality_resolution,[],[f69])).
% 3.60/1.04  
% 3.60/1.04  fof(f32,plain,(
% 3.60/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X9) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 3.60/1.04    inference(cnf_transformation,[],[f23])).
% 3.60/1.04  
% 3.60/1.04  fof(f24,plain,(
% 3.60/1.04    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.60/1.04    inference(nnf_transformation,[],[f17])).
% 3.60/1.04  
% 3.60/1.04  fof(f25,plain,(
% 3.60/1.04    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.60/1.04    inference(flattening,[],[f24])).
% 3.60/1.04  
% 3.60/1.04  fof(f26,plain,(
% 3.60/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8 & X0 != X9)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | X0 = X9 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 3.60/1.04    inference(rectify,[],[f25])).
% 3.60/1.04  
% 3.60/1.04  fof(f38,plain,(
% 3.60/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | X0 != X8) )),
% 3.60/1.04    inference(cnf_transformation,[],[f26])).
% 3.60/1.04  
% 3.60/1.04  fof(f78,plain,(
% 3.60/1.04    ( ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : (sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 3.60/1.04    inference(equality_resolution,[],[f38])).
% 3.60/1.04  
% 3.60/1.04  fof(f36,plain,(
% 3.60/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | X0 = X9 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 3.60/1.04    inference(cnf_transformation,[],[f26])).
% 3.60/1.04  
% 3.60/1.04  fof(f58,plain,(
% 3.60/1.04    sK3 != sK4),
% 3.60/1.04    inference(cnf_transformation,[],[f29])).
% 3.60/1.04  
% 3.60/1.04  cnf(c_3,plain,
% 3.60/1.04      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
% 3.60/1.04      | ~ sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10)
% 3.60/1.04      | r2_hidden(X0,X10) ),
% 3.60/1.04      inference(cnf_transformation,[],[f33]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_1364,plain,
% 3.60/1.04      ( ~ sP0(sK4,X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 3.60/1.04      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X0,X9)
% 3.60/1.04      | r2_hidden(sK4,X9) ),
% 3.60/1.04      inference(instantiation,[status(thm)],[c_3]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_1490,plain,
% 3.60/1.04      ( ~ sP0(sK4,X0,X1,X2,X3,X4,X5,X6,sK4,X7)
% 3.60/1.04      | ~ sP1(X7,sK4,X6,X5,X4,X3,X2,X1,X0,X8)
% 3.60/1.04      | r2_hidden(sK4,X8) ),
% 3.60/1.04      inference(instantiation,[status(thm)],[c_1364]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_2761,plain,
% 3.60/1.04      ( ~ sP0(sK4,X0,X1,X2,X3,X4,X5,X6,sK4,X7)
% 3.60/1.04      | ~ sP1(X7,sK4,X6,X5,X4,X3,X2,X1,X0,k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k5_xboole_0(k6_enumset1(X9,X10,X11,X12,X13,X14,X15,sK3),k3_xboole_0(k6_enumset1(X9,X10,X11,X12,X13,X14,X15,sK3),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8)))))
% 3.60/1.04      | r2_hidden(sK4,k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k5_xboole_0(k6_enumset1(X9,X10,X11,X12,X13,X14,X15,sK3),k3_xboole_0(k6_enumset1(X9,X10,X11,X12,X13,X14,X15,sK3),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))))) ),
% 3.60/1.04      inference(instantiation,[status(thm)],[c_1490]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_2803,plain,
% 3.60/1.04      ( ~ sP0(sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4,sK3)
% 3.60/1.04      | ~ sP1(sK3,sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))
% 3.60/1.04      | r2_hidden(sK4,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) ),
% 3.60/1.04      inference(instantiation,[status(thm)],[c_2761]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_0,plain,
% 3.60/1.04      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
% 3.60/1.04      inference(cnf_transformation,[],[f67]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_18,negated_conjecture,
% 3.60/1.04      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
% 3.60/1.04      inference(cnf_transformation,[],[f70]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_1179,plain,
% 3.60/1.04      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X0,sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
% 3.60/1.04      inference(superposition,[status(thm)],[c_18,c_0]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_1824,plain,
% 3.60/1.04      ( k6_enumset1(X0,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(X0,sK4,sK4,sK4,sK4,sK4,sK4,sK5) ),
% 3.60/1.04      inference(superposition,[status(thm)],[c_0,c_1179]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_2002,plain,
% 3.60/1.04      ( k6_enumset1(sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 3.60/1.04      inference(superposition,[status(thm)],[c_1824,c_18]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_16,plain,
% 3.60/1.04      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) ),
% 3.60/1.04      inference(cnf_transformation,[],[f80]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_1090,plain,
% 3.60/1.04      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) = iProver_top ),
% 3.60/1.04      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_2007,plain,
% 3.60/1.04      ( sP1(X0,sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) = iProver_top ),
% 3.60/1.04      inference(superposition,[status(thm)],[c_2002,c_1090]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_2009,plain,
% 3.60/1.04      ( sP1(X0,sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) ),
% 3.60/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_2007]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_2011,plain,
% 3.60/1.04      ( sP1(sK3,sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) ),
% 3.60/1.04      inference(instantiation,[status(thm)],[c_2009]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_4,plain,
% 3.60/1.04      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
% 3.60/1.04      | ~ sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10)
% 3.60/1.04      | ~ r2_hidden(X0,X10) ),
% 3.60/1.04      inference(cnf_transformation,[],[f32]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_1203,plain,
% 3.60/1.04      ( sP0(sK4,sK3,X0,X1,X2,X3,X4,X5,X6,X7)
% 3.60/1.04      | ~ sP1(X7,X6,X5,X4,X3,X2,X1,X0,sK3,X8)
% 3.60/1.04      | ~ r2_hidden(sK4,X8) ),
% 3.60/1.04      inference(instantiation,[status(thm)],[c_4]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_1942,plain,
% 3.60/1.04      ( sP0(sK4,sK3,X0,X1,X2,X3,X4,X5,X6,X7)
% 3.60/1.04      | ~ sP1(X7,X6,X5,X4,X3,X2,X1,X0,sK3,k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k5_xboole_0(k6_enumset1(X6,X5,X4,X3,X2,X1,X0,sK3),k3_xboole_0(k6_enumset1(X6,X5,X4,X3,X2,X1,X0,sK3),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)))))
% 3.60/1.04      | ~ r2_hidden(sK4,k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k5_xboole_0(k6_enumset1(X6,X5,X4,X3,X2,X1,X0,sK3),k3_xboole_0(k6_enumset1(X6,X5,X4,X3,X2,X1,X0,sK3),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7))))) ),
% 3.60/1.04      inference(instantiation,[status(thm)],[c_1203]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_1945,plain,
% 3.60/1.04      ( sP0(sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 3.60/1.04      | ~ sP1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))
% 3.60/1.04      | ~ r2_hidden(sK4,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) ),
% 3.60/1.04      inference(instantiation,[status(thm)],[c_1942]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_12,plain,
% 3.60/1.04      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0,X8) ),
% 3.60/1.04      inference(cnf_transformation,[],[f78]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_1269,plain,
% 3.60/1.04      ( sP0(sK4,sK3,X0,X1,X2,X3,X4,X5,sK4,X6) ),
% 3.60/1.04      inference(instantiation,[status(thm)],[c_12]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_1275,plain,
% 3.60/1.04      ( sP0(sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4,sK3) ),
% 3.60/1.04      inference(instantiation,[status(thm)],[c_1269]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_14,plain,
% 3.60/1.04      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
% 3.60/1.04      | X9 = X0
% 3.60/1.04      | X8 = X0
% 3.60/1.04      | X7 = X0
% 3.60/1.04      | X6 = X0
% 3.60/1.04      | X5 = X0
% 3.60/1.04      | X4 = X0
% 3.60/1.04      | X3 = X0
% 3.60/1.04      | X2 = X0
% 3.60/1.04      | X1 = X0 ),
% 3.60/1.04      inference(cnf_transformation,[],[f36]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_1149,plain,
% 3.60/1.04      ( ~ sP0(sK4,sK3,X0,X1,X2,X3,X4,X5,X6,X7)
% 3.60/1.04      | X7 = sK4
% 3.60/1.04      | X6 = sK4
% 3.60/1.04      | X5 = sK4
% 3.60/1.04      | X4 = sK4
% 3.60/1.04      | X3 = sK4
% 3.60/1.04      | X2 = sK4
% 3.60/1.04      | X1 = sK4
% 3.60/1.04      | X0 = sK4
% 3.60/1.04      | sK3 = sK4 ),
% 3.60/1.04      inference(instantiation,[status(thm)],[c_14]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_1151,plain,
% 3.60/1.04      ( ~ sP0(sK4,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) | sK3 = sK4 ),
% 3.60/1.04      inference(instantiation,[status(thm)],[c_1149]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_20,plain,
% 3.60/1.04      ( sP1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) ),
% 3.60/1.04      inference(instantiation,[status(thm)],[c_16]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(c_17,negated_conjecture,
% 3.60/1.04      ( sK3 != sK4 ),
% 3.60/1.04      inference(cnf_transformation,[],[f58]) ).
% 3.60/1.04  
% 3.60/1.04  cnf(contradiction,plain,
% 3.60/1.04      ( $false ),
% 3.60/1.04      inference(minisat,
% 3.60/1.04                [status(thm)],
% 3.60/1.04                [c_2803,c_2011,c_1945,c_1275,c_1151,c_20,c_17]) ).
% 3.60/1.04  
% 3.60/1.04  
% 3.60/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 3.60/1.04  
% 3.60/1.04  ------                               Statistics
% 3.60/1.04  
% 3.60/1.04  ------ Selected
% 3.60/1.04  
% 3.60/1.04  total_time:                             0.166
% 3.60/1.04  
%------------------------------------------------------------------------------
