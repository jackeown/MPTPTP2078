%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:14 EST 2020

% Result     : Theorem 6.63s
% Output     : CNFRefutation 6.63s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 223 expanded)
%              Number of clauses        :   38 (  41 expanded)
%              Number of leaves         :   24 (  63 expanded)
%              Depth                    :   16
%              Number of atoms          :  333 ( 592 expanded)
%              Number of equality atoms :  230 ( 471 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f21,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK4 != sK5
      & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( sK4 != sK5
    & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f21,f37])).

fof(f74,plain,(
    k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f76,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f45,f41])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f71,f77])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f70,f78])).

fof(f80,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f69,f79])).

fof(f81,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f68,f80])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f67,f81])).

fof(f90,plain,(
    k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f74,f76,f82,f82,f82])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f22,plain,(
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

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(definition_folding,[],[f20,f23,f22])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f10])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(definition_unfolding,[],[f66,f76,f82])).

fof(f89,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) != X9 ) ),
    inference(definition_unfolding,[],[f64,f83])).

fof(f103,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) ),
    inference(equality_resolution,[],[f89])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X10] :
          ( ( ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X10,X9) )
          & ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X10,X9) ) )
     => ( ( ~ sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
        & ( sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | ( ( ~ sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
          & ( sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X9)
              | ~ sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X11,X9) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | ~ sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f94,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(equality_resolution,[],[f63])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f46,f82])).

fof(f93,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f87])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | X0 != X9 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f102,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : sP0(X9,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(equality_resolution,[],[f55])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f75,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_26,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1564,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(demodulation,[status(thm)],[c_0,c_26])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1749,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_4])).

cnf(c_1793,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_1749])).

cnf(c_1839,plain,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1564,c_1793])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1862,plain,
    ( k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1839,c_2,c_4])).

cnf(c_24,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1382,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1738,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1382])).

cnf(c_21199,plain,
    ( sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1862,c_1738])).

cnf(c_21206,plain,
    ( sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_21199,c_2])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
    | ~ sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10)
    | r2_hidden(X0,X10) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_5975,plain,
    ( ~ sP0(sK5,X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X0,k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9))
    | r2_hidden(sK5,k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_13727,plain,
    ( ~ sP0(sK5,sK5,X0,sK4,X1,X2,X3,X4,X5,X6)
    | ~ sP1(X6,X5,X4,X3,X2,X1,sK4,X0,sK5,k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7))
    | r2_hidden(sK5,k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)) ),
    inference(instantiation,[status(thm)],[c_5975])).

cnf(c_13728,plain,
    ( sP0(sK5,sK5,X0,sK4,X1,X2,X3,X4,X5,X6) != iProver_top
    | sP1(X6,X5,X4,X3,X2,X1,sK4,X0,sK5,k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)) != iProver_top
    | r2_hidden(sK5,k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13727])).

cnf(c_13730,plain,
    ( sP0(sK5,sK5,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != iProver_top
    | sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_13728])).

cnf(c_13,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1592,plain,
    ( sP0(sK5,sK5,X0,sK4,X1,X2,X3,X4,X5,X6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1597,plain,
    ( sP0(sK5,sK5,X0,sK4,X1,X2,X3,X4,X5,X6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1592])).

cnf(c_1599,plain,
    ( sP0(sK5,sK5,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1597])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1579,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1580,plain,
    ( sK5 = X0
    | r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1579])).

cnf(c_1582,plain,
    ( sK5 = sK4
    | r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1580])).

cnf(c_1046,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1549,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_1550,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1549])).

cnf(c_21,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_37,plain,
    ( sP0(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_22,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
    | X3 = X0
    | X9 = X0
    | X8 = X0
    | X7 = X0
    | X6 = X0
    | X5 = X0
    | X4 = X0
    | X2 = X0
    | X1 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_34,plain,
    ( ~ sP0(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_25,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f75])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21206,c_13730,c_1599,c_1582,c_1550,c_37,c_34,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 6.63/1.53  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.63/1.53  
% 6.63/1.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.63/1.53  
% 6.63/1.53  ------  iProver source info
% 6.63/1.53  
% 6.63/1.53  git: date: 2020-06-30 10:37:57 +0100
% 6.63/1.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.63/1.53  git: non_committed_changes: false
% 6.63/1.53  git: last_make_outside_of_git: false
% 6.63/1.53  
% 6.63/1.53  ------ 
% 6.63/1.53  
% 6.63/1.53  ------ Input Options
% 6.63/1.53  
% 6.63/1.53  --out_options                           all
% 6.63/1.53  --tptp_safe_out                         true
% 6.63/1.53  --problem_path                          ""
% 6.63/1.53  --include_path                          ""
% 6.63/1.53  --clausifier                            res/vclausify_rel
% 6.63/1.53  --clausifier_options                    --mode clausify
% 6.63/1.53  --stdin                                 false
% 6.63/1.53  --stats_out                             all
% 6.63/1.53  
% 6.63/1.53  ------ General Options
% 6.63/1.53  
% 6.63/1.53  --fof                                   false
% 6.63/1.53  --time_out_real                         305.
% 6.63/1.53  --time_out_virtual                      -1.
% 6.63/1.53  --symbol_type_check                     false
% 6.63/1.53  --clausify_out                          false
% 6.63/1.53  --sig_cnt_out                           false
% 6.63/1.53  --trig_cnt_out                          false
% 6.63/1.53  --trig_cnt_out_tolerance                1.
% 6.63/1.53  --trig_cnt_out_sk_spl                   false
% 6.63/1.53  --abstr_cl_out                          false
% 6.63/1.53  
% 6.63/1.53  ------ Global Options
% 6.63/1.53  
% 6.63/1.53  --schedule                              default
% 6.63/1.53  --add_important_lit                     false
% 6.63/1.53  --prop_solver_per_cl                    1000
% 6.63/1.53  --min_unsat_core                        false
% 6.63/1.53  --soft_assumptions                      false
% 6.63/1.53  --soft_lemma_size                       3
% 6.63/1.53  --prop_impl_unit_size                   0
% 6.63/1.53  --prop_impl_unit                        []
% 6.63/1.53  --share_sel_clauses                     true
% 6.63/1.53  --reset_solvers                         false
% 6.63/1.53  --bc_imp_inh                            [conj_cone]
% 6.63/1.53  --conj_cone_tolerance                   3.
% 6.63/1.53  --extra_neg_conj                        none
% 6.63/1.53  --large_theory_mode                     true
% 6.63/1.53  --prolific_symb_bound                   200
% 6.63/1.53  --lt_threshold                          2000
% 6.63/1.53  --clause_weak_htbl                      true
% 6.63/1.53  --gc_record_bc_elim                     false
% 6.63/1.53  
% 6.63/1.53  ------ Preprocessing Options
% 6.63/1.53  
% 6.63/1.53  --preprocessing_flag                    true
% 6.63/1.53  --time_out_prep_mult                    0.1
% 6.63/1.53  --splitting_mode                        input
% 6.63/1.53  --splitting_grd                         true
% 6.63/1.53  --splitting_cvd                         false
% 6.63/1.53  --splitting_cvd_svl                     false
% 6.63/1.53  --splitting_nvd                         32
% 6.63/1.53  --sub_typing                            true
% 6.63/1.53  --prep_gs_sim                           true
% 6.63/1.53  --prep_unflatten                        true
% 6.63/1.53  --prep_res_sim                          true
% 6.63/1.53  --prep_upred                            true
% 6.63/1.53  --prep_sem_filter                       exhaustive
% 6.63/1.53  --prep_sem_filter_out                   false
% 6.63/1.53  --pred_elim                             true
% 6.63/1.53  --res_sim_input                         true
% 6.63/1.53  --eq_ax_congr_red                       true
% 6.63/1.53  --pure_diseq_elim                       true
% 6.63/1.53  --brand_transform                       false
% 6.63/1.53  --non_eq_to_eq                          false
% 6.63/1.53  --prep_def_merge                        true
% 6.63/1.53  --prep_def_merge_prop_impl              false
% 6.63/1.53  --prep_def_merge_mbd                    true
% 6.63/1.53  --prep_def_merge_tr_red                 false
% 6.63/1.53  --prep_def_merge_tr_cl                  false
% 6.63/1.53  --smt_preprocessing                     true
% 6.63/1.53  --smt_ac_axioms                         fast
% 6.63/1.53  --preprocessed_out                      false
% 6.63/1.53  --preprocessed_stats                    false
% 6.63/1.53  
% 6.63/1.53  ------ Abstraction refinement Options
% 6.63/1.53  
% 6.63/1.53  --abstr_ref                             []
% 6.63/1.53  --abstr_ref_prep                        false
% 6.63/1.53  --abstr_ref_until_sat                   false
% 6.63/1.53  --abstr_ref_sig_restrict                funpre
% 6.63/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 6.63/1.53  --abstr_ref_under                       []
% 6.63/1.53  
% 6.63/1.53  ------ SAT Options
% 6.63/1.53  
% 6.63/1.53  --sat_mode                              false
% 6.63/1.53  --sat_fm_restart_options                ""
% 6.63/1.53  --sat_gr_def                            false
% 6.63/1.53  --sat_epr_types                         true
% 6.63/1.53  --sat_non_cyclic_types                  false
% 6.63/1.53  --sat_finite_models                     false
% 6.63/1.53  --sat_fm_lemmas                         false
% 6.63/1.53  --sat_fm_prep                           false
% 6.63/1.53  --sat_fm_uc_incr                        true
% 6.63/1.53  --sat_out_model                         small
% 6.63/1.53  --sat_out_clauses                       false
% 6.63/1.53  
% 6.63/1.53  ------ QBF Options
% 6.63/1.53  
% 6.63/1.53  --qbf_mode                              false
% 6.63/1.53  --qbf_elim_univ                         false
% 6.63/1.53  --qbf_dom_inst                          none
% 6.63/1.53  --qbf_dom_pre_inst                      false
% 6.63/1.53  --qbf_sk_in                             false
% 6.63/1.53  --qbf_pred_elim                         true
% 6.63/1.53  --qbf_split                             512
% 6.63/1.53  
% 6.63/1.53  ------ BMC1 Options
% 6.63/1.53  
% 6.63/1.53  --bmc1_incremental                      false
% 6.63/1.53  --bmc1_axioms                           reachable_all
% 6.63/1.53  --bmc1_min_bound                        0
% 6.63/1.53  --bmc1_max_bound                        -1
% 6.63/1.53  --bmc1_max_bound_default                -1
% 6.63/1.53  --bmc1_symbol_reachability              true
% 6.63/1.53  --bmc1_property_lemmas                  false
% 6.63/1.53  --bmc1_k_induction                      false
% 6.63/1.53  --bmc1_non_equiv_states                 false
% 6.63/1.53  --bmc1_deadlock                         false
% 6.63/1.53  --bmc1_ucm                              false
% 6.63/1.53  --bmc1_add_unsat_core                   none
% 6.63/1.53  --bmc1_unsat_core_children              false
% 6.63/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 6.63/1.53  --bmc1_out_stat                         full
% 6.63/1.53  --bmc1_ground_init                      false
% 6.63/1.53  --bmc1_pre_inst_next_state              false
% 6.63/1.53  --bmc1_pre_inst_state                   false
% 6.63/1.53  --bmc1_pre_inst_reach_state             false
% 6.63/1.53  --bmc1_out_unsat_core                   false
% 6.63/1.53  --bmc1_aig_witness_out                  false
% 6.63/1.53  --bmc1_verbose                          false
% 6.63/1.53  --bmc1_dump_clauses_tptp                false
% 6.63/1.53  --bmc1_dump_unsat_core_tptp             false
% 6.63/1.53  --bmc1_dump_file                        -
% 6.63/1.53  --bmc1_ucm_expand_uc_limit              128
% 6.63/1.53  --bmc1_ucm_n_expand_iterations          6
% 6.63/1.53  --bmc1_ucm_extend_mode                  1
% 6.63/1.53  --bmc1_ucm_init_mode                    2
% 6.63/1.53  --bmc1_ucm_cone_mode                    none
% 6.63/1.53  --bmc1_ucm_reduced_relation_type        0
% 6.63/1.53  --bmc1_ucm_relax_model                  4
% 6.63/1.53  --bmc1_ucm_full_tr_after_sat            true
% 6.63/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 6.63/1.53  --bmc1_ucm_layered_model                none
% 6.63/1.53  --bmc1_ucm_max_lemma_size               10
% 6.63/1.53  
% 6.63/1.53  ------ AIG Options
% 6.63/1.53  
% 6.63/1.53  --aig_mode                              false
% 6.63/1.53  
% 6.63/1.53  ------ Instantiation Options
% 6.63/1.53  
% 6.63/1.53  --instantiation_flag                    true
% 6.63/1.53  --inst_sos_flag                         false
% 6.63/1.53  --inst_sos_phase                        true
% 6.63/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.63/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.63/1.53  --inst_lit_sel_side                     num_symb
% 6.63/1.53  --inst_solver_per_active                1400
% 6.63/1.53  --inst_solver_calls_frac                1.
% 6.63/1.53  --inst_passive_queue_type               priority_queues
% 6.63/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.63/1.53  --inst_passive_queues_freq              [25;2]
% 6.63/1.53  --inst_dismatching                      true
% 6.63/1.53  --inst_eager_unprocessed_to_passive     true
% 6.63/1.53  --inst_prop_sim_given                   true
% 6.63/1.53  --inst_prop_sim_new                     false
% 6.63/1.53  --inst_subs_new                         false
% 6.63/1.53  --inst_eq_res_simp                      false
% 6.63/1.53  --inst_subs_given                       false
% 6.63/1.53  --inst_orphan_elimination               true
% 6.63/1.53  --inst_learning_loop_flag               true
% 6.63/1.53  --inst_learning_start                   3000
% 6.63/1.53  --inst_learning_factor                  2
% 6.63/1.53  --inst_start_prop_sim_after_learn       3
% 6.63/1.53  --inst_sel_renew                        solver
% 6.63/1.53  --inst_lit_activity_flag                true
% 6.63/1.53  --inst_restr_to_given                   false
% 6.63/1.53  --inst_activity_threshold               500
% 6.63/1.53  --inst_out_proof                        true
% 6.63/1.53  
% 6.63/1.53  ------ Resolution Options
% 6.63/1.53  
% 6.63/1.53  --resolution_flag                       true
% 6.63/1.53  --res_lit_sel                           adaptive
% 6.63/1.53  --res_lit_sel_side                      none
% 6.63/1.53  --res_ordering                          kbo
% 6.63/1.53  --res_to_prop_solver                    active
% 6.63/1.53  --res_prop_simpl_new                    false
% 6.63/1.53  --res_prop_simpl_given                  true
% 6.63/1.53  --res_passive_queue_type                priority_queues
% 6.63/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.63/1.53  --res_passive_queues_freq               [15;5]
% 6.63/1.53  --res_forward_subs                      full
% 6.63/1.53  --res_backward_subs                     full
% 6.63/1.53  --res_forward_subs_resolution           true
% 6.63/1.53  --res_backward_subs_resolution          true
% 6.63/1.53  --res_orphan_elimination                true
% 6.63/1.53  --res_time_limit                        2.
% 6.63/1.53  --res_out_proof                         true
% 6.63/1.53  
% 6.63/1.53  ------ Superposition Options
% 6.63/1.53  
% 6.63/1.53  --superposition_flag                    true
% 6.63/1.53  --sup_passive_queue_type                priority_queues
% 6.63/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.63/1.53  --sup_passive_queues_freq               [8;1;4]
% 6.63/1.53  --demod_completeness_check              fast
% 6.63/1.53  --demod_use_ground                      true
% 6.63/1.53  --sup_to_prop_solver                    passive
% 6.63/1.53  --sup_prop_simpl_new                    true
% 6.63/1.53  --sup_prop_simpl_given                  true
% 6.63/1.53  --sup_fun_splitting                     false
% 6.63/1.53  --sup_smt_interval                      50000
% 6.63/1.53  
% 6.63/1.53  ------ Superposition Simplification Setup
% 6.63/1.53  
% 6.63/1.53  --sup_indices_passive                   []
% 6.63/1.53  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.63/1.53  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.63/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.63/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 6.63/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.63/1.53  --sup_full_bw                           [BwDemod]
% 6.63/1.53  --sup_immed_triv                        [TrivRules]
% 6.63/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.63/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.63/1.53  --sup_immed_bw_main                     []
% 6.63/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.63/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 6.63/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.63/1.53  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.63/1.53  
% 6.63/1.53  ------ Combination Options
% 6.63/1.53  
% 6.63/1.53  --comb_res_mult                         3
% 6.63/1.53  --comb_sup_mult                         2
% 6.63/1.53  --comb_inst_mult                        10
% 6.63/1.53  
% 6.63/1.53  ------ Debug Options
% 6.63/1.53  
% 6.63/1.53  --dbg_backtrace                         false
% 6.63/1.53  --dbg_dump_prop_clauses                 false
% 6.63/1.53  --dbg_dump_prop_clauses_file            -
% 6.63/1.53  --dbg_out_stat                          false
% 6.63/1.53  ------ Parsing...
% 6.63/1.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.63/1.53  
% 6.63/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.63/1.53  
% 6.63/1.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.63/1.53  
% 6.63/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.63/1.53  ------ Proving...
% 6.63/1.53  ------ Problem Properties 
% 6.63/1.53  
% 6.63/1.53  
% 6.63/1.53  clauses                                 27
% 6.63/1.53  conjectures                             2
% 6.63/1.53  EPR                                     13
% 6.63/1.53  Horn                                    24
% 6.63/1.53  unary                                   18
% 6.63/1.53  binary                                  2
% 6.63/1.53  lits                                    50
% 6.63/1.53  lits eq                                 22
% 6.63/1.53  fd_pure                                 0
% 6.63/1.53  fd_pseudo                               0
% 6.63/1.53  fd_cond                                 0
% 6.63/1.53  fd_pseudo_cond                          4
% 6.63/1.53  AC symbols                              1
% 6.63/1.53  
% 6.63/1.53  ------ Schedule dynamic 5 is on 
% 6.63/1.53  
% 6.63/1.53  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.63/1.53  
% 6.63/1.53  
% 6.63/1.53  ------ 
% 6.63/1.53  Current options:
% 6.63/1.53  ------ 
% 6.63/1.53  
% 6.63/1.53  ------ Input Options
% 6.63/1.53  
% 6.63/1.53  --out_options                           all
% 6.63/1.53  --tptp_safe_out                         true
% 6.63/1.53  --problem_path                          ""
% 6.63/1.53  --include_path                          ""
% 6.63/1.53  --clausifier                            res/vclausify_rel
% 6.63/1.53  --clausifier_options                    --mode clausify
% 6.63/1.53  --stdin                                 false
% 6.63/1.53  --stats_out                             all
% 6.63/1.53  
% 6.63/1.53  ------ General Options
% 6.63/1.53  
% 6.63/1.53  --fof                                   false
% 6.63/1.53  --time_out_real                         305.
% 6.63/1.53  --time_out_virtual                      -1.
% 6.63/1.53  --symbol_type_check                     false
% 6.63/1.53  --clausify_out                          false
% 6.63/1.53  --sig_cnt_out                           false
% 6.63/1.53  --trig_cnt_out                          false
% 6.63/1.53  --trig_cnt_out_tolerance                1.
% 6.63/1.53  --trig_cnt_out_sk_spl                   false
% 6.63/1.53  --abstr_cl_out                          false
% 6.63/1.53  
% 6.63/1.53  ------ Global Options
% 6.63/1.53  
% 6.63/1.53  --schedule                              default
% 6.63/1.53  --add_important_lit                     false
% 6.63/1.53  --prop_solver_per_cl                    1000
% 6.63/1.53  --min_unsat_core                        false
% 6.63/1.53  --soft_assumptions                      false
% 6.63/1.53  --soft_lemma_size                       3
% 6.63/1.53  --prop_impl_unit_size                   0
% 6.63/1.53  --prop_impl_unit                        []
% 6.63/1.53  --share_sel_clauses                     true
% 6.63/1.53  --reset_solvers                         false
% 6.63/1.53  --bc_imp_inh                            [conj_cone]
% 6.63/1.53  --conj_cone_tolerance                   3.
% 6.63/1.53  --extra_neg_conj                        none
% 6.63/1.53  --large_theory_mode                     true
% 6.63/1.53  --prolific_symb_bound                   200
% 6.63/1.53  --lt_threshold                          2000
% 6.63/1.53  --clause_weak_htbl                      true
% 6.63/1.53  --gc_record_bc_elim                     false
% 6.63/1.53  
% 6.63/1.53  ------ Preprocessing Options
% 6.63/1.53  
% 6.63/1.53  --preprocessing_flag                    true
% 6.63/1.53  --time_out_prep_mult                    0.1
% 6.63/1.53  --splitting_mode                        input
% 6.63/1.53  --splitting_grd                         true
% 6.63/1.53  --splitting_cvd                         false
% 6.63/1.53  --splitting_cvd_svl                     false
% 6.63/1.53  --splitting_nvd                         32
% 6.63/1.53  --sub_typing                            true
% 6.63/1.53  --prep_gs_sim                           true
% 6.63/1.53  --prep_unflatten                        true
% 6.63/1.53  --prep_res_sim                          true
% 6.63/1.53  --prep_upred                            true
% 6.63/1.53  --prep_sem_filter                       exhaustive
% 6.63/1.53  --prep_sem_filter_out                   false
% 6.63/1.53  --pred_elim                             true
% 6.63/1.53  --res_sim_input                         true
% 6.63/1.53  --eq_ax_congr_red                       true
% 6.63/1.53  --pure_diseq_elim                       true
% 6.63/1.53  --brand_transform                       false
% 6.63/1.53  --non_eq_to_eq                          false
% 6.63/1.53  --prep_def_merge                        true
% 6.63/1.53  --prep_def_merge_prop_impl              false
% 6.63/1.53  --prep_def_merge_mbd                    true
% 6.63/1.53  --prep_def_merge_tr_red                 false
% 6.63/1.53  --prep_def_merge_tr_cl                  false
% 6.63/1.53  --smt_preprocessing                     true
% 6.63/1.53  --smt_ac_axioms                         fast
% 6.63/1.53  --preprocessed_out                      false
% 6.63/1.53  --preprocessed_stats                    false
% 6.63/1.53  
% 6.63/1.53  ------ Abstraction refinement Options
% 6.63/1.53  
% 6.63/1.53  --abstr_ref                             []
% 6.63/1.53  --abstr_ref_prep                        false
% 6.63/1.53  --abstr_ref_until_sat                   false
% 6.63/1.53  --abstr_ref_sig_restrict                funpre
% 6.63/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 6.63/1.53  --abstr_ref_under                       []
% 6.63/1.53  
% 6.63/1.53  ------ SAT Options
% 6.63/1.53  
% 6.63/1.53  --sat_mode                              false
% 6.63/1.53  --sat_fm_restart_options                ""
% 6.63/1.53  --sat_gr_def                            false
% 6.63/1.53  --sat_epr_types                         true
% 6.63/1.53  --sat_non_cyclic_types                  false
% 6.63/1.53  --sat_finite_models                     false
% 6.63/1.53  --sat_fm_lemmas                         false
% 6.63/1.53  --sat_fm_prep                           false
% 6.63/1.53  --sat_fm_uc_incr                        true
% 6.63/1.53  --sat_out_model                         small
% 6.63/1.53  --sat_out_clauses                       false
% 6.63/1.53  
% 6.63/1.53  ------ QBF Options
% 6.63/1.53  
% 6.63/1.53  --qbf_mode                              false
% 6.63/1.53  --qbf_elim_univ                         false
% 6.63/1.53  --qbf_dom_inst                          none
% 6.63/1.53  --qbf_dom_pre_inst                      false
% 6.63/1.53  --qbf_sk_in                             false
% 6.63/1.53  --qbf_pred_elim                         true
% 6.63/1.53  --qbf_split                             512
% 6.63/1.53  
% 6.63/1.53  ------ BMC1 Options
% 6.63/1.53  
% 6.63/1.53  --bmc1_incremental                      false
% 6.63/1.53  --bmc1_axioms                           reachable_all
% 6.63/1.53  --bmc1_min_bound                        0
% 6.63/1.53  --bmc1_max_bound                        -1
% 6.63/1.53  --bmc1_max_bound_default                -1
% 6.63/1.53  --bmc1_symbol_reachability              true
% 6.63/1.53  --bmc1_property_lemmas                  false
% 6.63/1.53  --bmc1_k_induction                      false
% 6.63/1.53  --bmc1_non_equiv_states                 false
% 6.63/1.53  --bmc1_deadlock                         false
% 6.63/1.53  --bmc1_ucm                              false
% 6.63/1.53  --bmc1_add_unsat_core                   none
% 6.63/1.53  --bmc1_unsat_core_children              false
% 6.63/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 6.63/1.53  --bmc1_out_stat                         full
% 6.63/1.53  --bmc1_ground_init                      false
% 6.63/1.53  --bmc1_pre_inst_next_state              false
% 6.63/1.53  --bmc1_pre_inst_state                   false
% 6.63/1.53  --bmc1_pre_inst_reach_state             false
% 6.63/1.53  --bmc1_out_unsat_core                   false
% 6.63/1.53  --bmc1_aig_witness_out                  false
% 6.63/1.53  --bmc1_verbose                          false
% 6.63/1.53  --bmc1_dump_clauses_tptp                false
% 6.63/1.53  --bmc1_dump_unsat_core_tptp             false
% 6.63/1.53  --bmc1_dump_file                        -
% 6.63/1.53  --bmc1_ucm_expand_uc_limit              128
% 6.63/1.53  --bmc1_ucm_n_expand_iterations          6
% 6.63/1.53  --bmc1_ucm_extend_mode                  1
% 6.63/1.53  --bmc1_ucm_init_mode                    2
% 6.63/1.53  --bmc1_ucm_cone_mode                    none
% 6.63/1.53  --bmc1_ucm_reduced_relation_type        0
% 6.63/1.53  --bmc1_ucm_relax_model                  4
% 6.63/1.53  --bmc1_ucm_full_tr_after_sat            true
% 6.63/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 6.63/1.53  --bmc1_ucm_layered_model                none
% 6.63/1.53  --bmc1_ucm_max_lemma_size               10
% 6.63/1.53  
% 6.63/1.53  ------ AIG Options
% 6.63/1.53  
% 6.63/1.53  --aig_mode                              false
% 6.63/1.53  
% 6.63/1.53  ------ Instantiation Options
% 6.63/1.53  
% 6.63/1.53  --instantiation_flag                    true
% 6.63/1.53  --inst_sos_flag                         false
% 6.63/1.53  --inst_sos_phase                        true
% 6.63/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.63/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.63/1.53  --inst_lit_sel_side                     none
% 6.63/1.53  --inst_solver_per_active                1400
% 6.63/1.53  --inst_solver_calls_frac                1.
% 6.63/1.53  --inst_passive_queue_type               priority_queues
% 6.63/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.63/1.53  --inst_passive_queues_freq              [25;2]
% 6.63/1.53  --inst_dismatching                      true
% 6.63/1.53  --inst_eager_unprocessed_to_passive     true
% 6.63/1.53  --inst_prop_sim_given                   true
% 6.63/1.53  --inst_prop_sim_new                     false
% 6.63/1.53  --inst_subs_new                         false
% 6.63/1.53  --inst_eq_res_simp                      false
% 6.63/1.53  --inst_subs_given                       false
% 6.63/1.53  --inst_orphan_elimination               true
% 6.63/1.53  --inst_learning_loop_flag               true
% 6.63/1.53  --inst_learning_start                   3000
% 6.63/1.53  --inst_learning_factor                  2
% 6.63/1.53  --inst_start_prop_sim_after_learn       3
% 6.63/1.53  --inst_sel_renew                        solver
% 6.63/1.53  --inst_lit_activity_flag                true
% 6.63/1.53  --inst_restr_to_given                   false
% 6.63/1.53  --inst_activity_threshold               500
% 6.63/1.53  --inst_out_proof                        true
% 6.63/1.53  
% 6.63/1.53  ------ Resolution Options
% 6.63/1.53  
% 6.63/1.53  --resolution_flag                       false
% 6.63/1.53  --res_lit_sel                           adaptive
% 6.63/1.53  --res_lit_sel_side                      none
% 6.63/1.53  --res_ordering                          kbo
% 6.63/1.53  --res_to_prop_solver                    active
% 6.63/1.53  --res_prop_simpl_new                    false
% 6.63/1.53  --res_prop_simpl_given                  true
% 6.63/1.53  --res_passive_queue_type                priority_queues
% 6.63/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.63/1.53  --res_passive_queues_freq               [15;5]
% 6.63/1.53  --res_forward_subs                      full
% 6.63/1.53  --res_backward_subs                     full
% 6.63/1.53  --res_forward_subs_resolution           true
% 6.63/1.53  --res_backward_subs_resolution          true
% 6.63/1.53  --res_orphan_elimination                true
% 6.63/1.53  --res_time_limit                        2.
% 6.63/1.53  --res_out_proof                         true
% 6.63/1.53  
% 6.63/1.53  ------ Superposition Options
% 6.63/1.53  
% 6.63/1.53  --superposition_flag                    true
% 6.63/1.53  --sup_passive_queue_type                priority_queues
% 6.63/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.63/1.53  --sup_passive_queues_freq               [8;1;4]
% 6.63/1.53  --demod_completeness_check              fast
% 6.63/1.53  --demod_use_ground                      true
% 6.63/1.53  --sup_to_prop_solver                    passive
% 6.63/1.53  --sup_prop_simpl_new                    true
% 6.63/1.53  --sup_prop_simpl_given                  true
% 6.63/1.53  --sup_fun_splitting                     false
% 6.63/1.53  --sup_smt_interval                      50000
% 6.63/1.53  
% 6.63/1.53  ------ Superposition Simplification Setup
% 6.63/1.53  
% 6.63/1.53  --sup_indices_passive                   []
% 6.63/1.53  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.63/1.53  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.63/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.63/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 6.63/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.63/1.53  --sup_full_bw                           [BwDemod]
% 6.63/1.53  --sup_immed_triv                        [TrivRules]
% 6.63/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.63/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.63/1.53  --sup_immed_bw_main                     []
% 6.63/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.63/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 6.63/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.63/1.53  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.63/1.53  
% 6.63/1.53  ------ Combination Options
% 6.63/1.53  
% 6.63/1.53  --comb_res_mult                         3
% 6.63/1.53  --comb_sup_mult                         2
% 6.63/1.53  --comb_inst_mult                        10
% 6.63/1.53  
% 6.63/1.53  ------ Debug Options
% 6.63/1.53  
% 6.63/1.53  --dbg_backtrace                         false
% 6.63/1.53  --dbg_dump_prop_clauses                 false
% 6.63/1.53  --dbg_dump_prop_clauses_file            -
% 6.63/1.53  --dbg_out_stat                          false
% 6.63/1.53  
% 6.63/1.53  
% 6.63/1.53  
% 6.63/1.53  
% 6.63/1.53  ------ Proving...
% 6.63/1.53  
% 6.63/1.53  
% 6.63/1.53  % SZS status Theorem for theBenchmark.p
% 6.63/1.53  
% 6.63/1.53  % SZS output start CNFRefutation for theBenchmark.p
% 6.63/1.53  
% 6.63/1.53  fof(f1,axiom,(
% 6.63/1.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.63/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.63/1.53  
% 6.63/1.53  fof(f39,plain,(
% 6.63/1.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.63/1.53    inference(cnf_transformation,[],[f1])).
% 6.63/1.53  
% 6.63/1.53  fof(f18,conjecture,(
% 6.63/1.53    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 6.63/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.63/1.53  
% 6.63/1.53  fof(f19,negated_conjecture,(
% 6.63/1.53    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 6.63/1.53    inference(negated_conjecture,[],[f18])).
% 6.63/1.53  
% 6.63/1.53  fof(f21,plain,(
% 6.63/1.53    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 6.63/1.53    inference(ennf_transformation,[],[f19])).
% 6.63/1.53  
% 6.63/1.53  fof(f37,plain,(
% 6.63/1.53    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK4 != sK5 & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4))),
% 6.63/1.53    introduced(choice_axiom,[])).
% 6.63/1.53  
% 6.63/1.53  fof(f38,plain,(
% 6.63/1.53    sK4 != sK5 & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4)),
% 6.63/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f21,f37])).
% 6.63/1.53  
% 6.63/1.53  fof(f74,plain,(
% 6.63/1.53    k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4)),
% 6.63/1.53    inference(cnf_transformation,[],[f38])).
% 6.63/1.53  
% 6.63/1.53  fof(f7,axiom,(
% 6.63/1.53    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 6.63/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.63/1.53  
% 6.63/1.53  fof(f45,plain,(
% 6.63/1.53    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 6.63/1.53    inference(cnf_transformation,[],[f7])).
% 6.63/1.53  
% 6.63/1.53  fof(f3,axiom,(
% 6.63/1.53    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 6.63/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.63/1.53  
% 6.63/1.53  fof(f41,plain,(
% 6.63/1.53    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 6.63/1.53    inference(cnf_transformation,[],[f3])).
% 6.63/1.53  
% 6.63/1.53  fof(f76,plain,(
% 6.63/1.53    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 6.63/1.53    inference(definition_unfolding,[],[f45,f41])).
% 6.63/1.53  
% 6.63/1.53  fof(f11,axiom,(
% 6.63/1.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 6.63/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.63/1.53  
% 6.63/1.53  fof(f67,plain,(
% 6.63/1.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 6.63/1.53    inference(cnf_transformation,[],[f11])).
% 6.63/1.53  
% 6.63/1.53  fof(f12,axiom,(
% 6.63/1.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.63/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.63/1.53  
% 6.63/1.53  fof(f68,plain,(
% 6.63/1.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.63/1.53    inference(cnf_transformation,[],[f12])).
% 6.63/1.53  
% 6.63/1.53  fof(f13,axiom,(
% 6.63/1.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.63/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.63/1.53  
% 6.63/1.53  fof(f69,plain,(
% 6.63/1.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.63/1.53    inference(cnf_transformation,[],[f13])).
% 6.63/1.53  
% 6.63/1.53  fof(f14,axiom,(
% 6.63/1.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 6.63/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.63/1.53  
% 6.63/1.53  fof(f70,plain,(
% 6.63/1.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 6.63/1.53    inference(cnf_transformation,[],[f14])).
% 6.63/1.53  
% 6.63/1.53  fof(f15,axiom,(
% 6.63/1.53    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 6.63/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.63/1.53  
% 6.63/1.53  fof(f71,plain,(
% 6.63/1.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 6.63/1.53    inference(cnf_transformation,[],[f15])).
% 6.63/1.53  
% 6.63/1.53  fof(f16,axiom,(
% 6.63/1.53    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 6.63/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.63/1.53  
% 6.63/1.53  fof(f72,plain,(
% 6.63/1.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 6.63/1.53    inference(cnf_transformation,[],[f16])).
% 6.63/1.53  
% 6.63/1.53  fof(f17,axiom,(
% 6.63/1.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 6.63/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.63/1.53  
% 6.63/1.53  fof(f73,plain,(
% 6.63/1.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 6.63/1.53    inference(cnf_transformation,[],[f17])).
% 6.63/1.53  
% 6.63/1.53  fof(f77,plain,(
% 6.63/1.53    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 6.63/1.53    inference(definition_unfolding,[],[f72,f73])).
% 6.63/1.53  
% 6.63/1.53  fof(f78,plain,(
% 6.63/1.53    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 6.63/1.53    inference(definition_unfolding,[],[f71,f77])).
% 6.63/1.53  
% 6.63/1.53  fof(f79,plain,(
% 6.63/1.53    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 6.63/1.53    inference(definition_unfolding,[],[f70,f78])).
% 6.63/1.53  
% 6.63/1.53  fof(f80,plain,(
% 6.63/1.53    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 6.63/1.53    inference(definition_unfolding,[],[f69,f79])).
% 6.63/1.53  
% 6.63/1.53  fof(f81,plain,(
% 6.63/1.53    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 6.63/1.53    inference(definition_unfolding,[],[f68,f80])).
% 6.63/1.53  
% 6.63/1.53  fof(f82,plain,(
% 6.63/1.53    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 6.63/1.53    inference(definition_unfolding,[],[f67,f81])).
% 6.63/1.53  
% 6.63/1.53  fof(f90,plain,(
% 6.63/1.53    k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 6.63/1.53    inference(definition_unfolding,[],[f74,f76,f82,f82,f82])).
% 6.63/1.53  
% 6.63/1.53  fof(f2,axiom,(
% 6.63/1.53    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 6.63/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.63/1.53  
% 6.63/1.53  fof(f40,plain,(
% 6.63/1.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 6.63/1.53    inference(cnf_transformation,[],[f2])).
% 6.63/1.53  
% 6.63/1.53  fof(f5,axiom,(
% 6.63/1.53    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 6.63/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.63/1.53  
% 6.63/1.53  fof(f43,plain,(
% 6.63/1.53    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 6.63/1.53    inference(cnf_transformation,[],[f5])).
% 6.63/1.53  
% 6.63/1.53  fof(f6,axiom,(
% 6.63/1.53    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 6.63/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.63/1.53  
% 6.63/1.53  fof(f44,plain,(
% 6.63/1.53    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 6.63/1.53    inference(cnf_transformation,[],[f6])).
% 6.63/1.53  
% 6.63/1.53  fof(f4,axiom,(
% 6.63/1.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 6.63/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.63/1.53  
% 6.63/1.53  fof(f42,plain,(
% 6.63/1.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.63/1.53    inference(cnf_transformation,[],[f4])).
% 6.63/1.53  
% 6.63/1.53  fof(f9,axiom,(
% 6.63/1.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> ~(X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)))),
% 6.63/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.63/1.53  
% 6.63/1.53  fof(f20,plain,(
% 6.63/1.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10)))),
% 6.63/1.53    inference(ennf_transformation,[],[f9])).
% 6.63/1.53  
% 6.63/1.53  fof(f23,plain,(
% 6.63/1.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) <=> ! [X10] : (r2_hidden(X10,X9) <=> sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 6.63/1.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 6.63/1.53  
% 6.63/1.53  fof(f22,plain,(
% 6.63/1.53    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10))),
% 6.63/1.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 6.63/1.53  
% 6.63/1.53  fof(f24,plain,(
% 6.63/1.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9))),
% 6.63/1.53    inference(definition_folding,[],[f20,f23,f22])).
% 6.63/1.53  
% 6.63/1.53  fof(f36,plain,(
% 6.63/1.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 6.63/1.53    inference(nnf_transformation,[],[f24])).
% 6.63/1.53  
% 6.63/1.53  fof(f64,plain,(
% 6.63/1.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 6.63/1.53    inference(cnf_transformation,[],[f36])).
% 6.63/1.53  
% 6.63/1.53  fof(f10,axiom,(
% 6.63/1.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 6.63/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.63/1.53  
% 6.63/1.53  fof(f66,plain,(
% 6.63/1.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 6.63/1.53    inference(cnf_transformation,[],[f10])).
% 6.63/1.53  
% 6.63/1.53  fof(f83,plain,(
% 6.63/1.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 6.63/1.53    inference(definition_unfolding,[],[f66,f76,f82])).
% 6.63/1.53  
% 6.63/1.53  fof(f89,plain,(
% 6.63/1.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) != X9) )),
% 6.63/1.53    inference(definition_unfolding,[],[f64,f83])).
% 6.63/1.53  
% 6.63/1.53  fof(f103,plain,(
% 6.63/1.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))))) )),
% 6.63/1.53    inference(equality_resolution,[],[f89])).
% 6.63/1.53  
% 6.63/1.53  fof(f29,plain,(
% 6.63/1.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 6.63/1.53    inference(nnf_transformation,[],[f23])).
% 6.63/1.53  
% 6.63/1.53  fof(f30,plain,(
% 6.63/1.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9)))) & (! [X11] : ((r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 6.63/1.53    inference(rectify,[],[f29])).
% 6.63/1.53  
% 6.63/1.53  fof(f31,plain,(
% 6.63/1.53    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9))) => ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9))))),
% 6.63/1.53    introduced(choice_axiom,[])).
% 6.63/1.53  
% 6.63/1.53  fof(f32,plain,(
% 6.63/1.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)))) & (! [X11] : ((r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 6.63/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 6.63/1.53  
% 6.63/1.53  fof(f51,plain,(
% 6.63/1.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 6.63/1.53    inference(cnf_transformation,[],[f32])).
% 6.63/1.53  
% 6.63/1.53  fof(f33,plain,(
% 6.63/1.53    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 6.63/1.53    inference(nnf_transformation,[],[f22])).
% 6.63/1.53  
% 6.63/1.53  fof(f34,plain,(
% 6.63/1.53    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 6.63/1.53    inference(flattening,[],[f33])).
% 6.63/1.53  
% 6.63/1.53  fof(f35,plain,(
% 6.63/1.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8 & X0 != X9)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | X0 = X9 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 6.63/1.53    inference(rectify,[],[f34])).
% 6.63/1.53  
% 6.63/1.53  fof(f63,plain,(
% 6.63/1.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | X0 != X1) )),
% 6.63/1.53    inference(cnf_transformation,[],[f35])).
% 6.63/1.53  
% 6.63/1.53  fof(f94,plain,(
% 6.63/1.53    ( ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 6.63/1.53    inference(equality_resolution,[],[f63])).
% 6.63/1.53  
% 6.63/1.53  fof(f8,axiom,(
% 6.63/1.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 6.63/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.63/1.53  
% 6.63/1.53  fof(f25,plain,(
% 6.63/1.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 6.63/1.53    inference(nnf_transformation,[],[f8])).
% 6.63/1.53  
% 6.63/1.53  fof(f26,plain,(
% 6.63/1.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 6.63/1.53    inference(rectify,[],[f25])).
% 6.63/1.53  
% 6.63/1.53  fof(f27,plain,(
% 6.63/1.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 6.63/1.53    introduced(choice_axiom,[])).
% 6.63/1.53  
% 6.63/1.53  fof(f28,plain,(
% 6.63/1.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 6.63/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 6.63/1.53  
% 6.63/1.53  fof(f46,plain,(
% 6.63/1.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 6.63/1.53    inference(cnf_transformation,[],[f28])).
% 6.63/1.53  
% 6.63/1.53  fof(f87,plain,(
% 6.63/1.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 6.63/1.53    inference(definition_unfolding,[],[f46,f82])).
% 6.63/1.53  
% 6.63/1.53  fof(f93,plain,(
% 6.63/1.53    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 6.63/1.53    inference(equality_resolution,[],[f87])).
% 6.63/1.53  
% 6.63/1.53  fof(f55,plain,(
% 6.63/1.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | X0 != X9) )),
% 6.63/1.53    inference(cnf_transformation,[],[f35])).
% 6.63/1.53  
% 6.63/1.53  fof(f102,plain,(
% 6.63/1.53    ( ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : (sP0(X9,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 6.63/1.53    inference(equality_resolution,[],[f55])).
% 6.63/1.53  
% 6.63/1.53  fof(f54,plain,(
% 6.63/1.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | X0 = X9 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 6.63/1.53    inference(cnf_transformation,[],[f35])).
% 6.63/1.53  
% 6.63/1.53  fof(f75,plain,(
% 6.63/1.53    sK4 != sK5),
% 6.63/1.53    inference(cnf_transformation,[],[f38])).
% 6.63/1.53  
% 6.63/1.53  cnf(c_0,plain,
% 6.63/1.53      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 6.63/1.53      inference(cnf_transformation,[],[f39]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_26,negated_conjecture,
% 6.63/1.53      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 6.63/1.53      inference(cnf_transformation,[],[f90]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_1564,plain,
% 6.63/1.53      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 6.63/1.53      inference(demodulation,[status(thm)],[c_0,c_26]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_1,plain,
% 6.63/1.53      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 6.63/1.53      inference(cnf_transformation,[],[f40]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_3,plain,
% 6.63/1.53      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 6.63/1.53      inference(cnf_transformation,[],[f43]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_4,plain,
% 6.63/1.53      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 6.63/1.53      inference(cnf_transformation,[],[f44]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_1749,plain,
% 6.63/1.53      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 6.63/1.53      inference(superposition,[status(thm)],[c_3,c_4]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_1793,plain,
% 6.63/1.53      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,X0))) = k1_xboole_0 ),
% 6.63/1.53      inference(superposition,[status(thm)],[c_1,c_1749]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_1839,plain,
% 6.63/1.53      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = k1_xboole_0 ),
% 6.63/1.53      inference(superposition,[status(thm)],[c_1564,c_1793]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_2,plain,
% 6.63/1.53      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 6.63/1.53      inference(cnf_transformation,[],[f42]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_1862,plain,
% 6.63/1.53      ( k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = k1_xboole_0 ),
% 6.63/1.53      inference(demodulation,[status(thm)],[c_1839,c_2,c_4]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_24,plain,
% 6.63/1.53      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) ),
% 6.63/1.53      inference(cnf_transformation,[],[f103]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_1382,plain,
% 6.63/1.53      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) = iProver_top ),
% 6.63/1.53      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_1738,plain,
% 6.63/1.53      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))))) = iProver_top ),
% 6.63/1.53      inference(superposition,[status(thm)],[c_0,c_1382]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_21199,plain,
% 6.63/1.53      ( sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_xboole_0)) = iProver_top ),
% 6.63/1.53      inference(superposition,[status(thm)],[c_1862,c_1738]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_21206,plain,
% 6.63/1.53      ( sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 6.63/1.53      inference(demodulation,[status(thm)],[c_21199,c_2]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_11,plain,
% 6.63/1.53      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
% 6.63/1.53      | ~ sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10)
% 6.63/1.53      | r2_hidden(X0,X10) ),
% 6.63/1.53      inference(cnf_transformation,[],[f51]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_5975,plain,
% 6.63/1.53      ( ~ sP0(sK5,X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 6.63/1.53      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X0,k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9))
% 6.63/1.53      | r2_hidden(sK5,k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9)) ),
% 6.63/1.53      inference(instantiation,[status(thm)],[c_11]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_13727,plain,
% 6.63/1.53      ( ~ sP0(sK5,sK5,X0,sK4,X1,X2,X3,X4,X5,X6)
% 6.63/1.53      | ~ sP1(X6,X5,X4,X3,X2,X1,sK4,X0,sK5,k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7))
% 6.63/1.53      | r2_hidden(sK5,k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)) ),
% 6.63/1.53      inference(instantiation,[status(thm)],[c_5975]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_13728,plain,
% 6.63/1.53      ( sP0(sK5,sK5,X0,sK4,X1,X2,X3,X4,X5,X6) != iProver_top
% 6.63/1.53      | sP1(X6,X5,X4,X3,X2,X1,sK4,X0,sK5,k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)) != iProver_top
% 6.63/1.53      | r2_hidden(sK5,k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)) = iProver_top ),
% 6.63/1.53      inference(predicate_to_equality,[status(thm)],[c_13727]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_13730,plain,
% 6.63/1.53      ( sP0(sK5,sK5,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != iProver_top
% 6.63/1.53      | sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
% 6.63/1.53      | r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 6.63/1.53      inference(instantiation,[status(thm)],[c_13728]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_13,plain,
% 6.63/1.53      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
% 6.63/1.53      inference(cnf_transformation,[],[f94]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_1592,plain,
% 6.63/1.53      ( sP0(sK5,sK5,X0,sK4,X1,X2,X3,X4,X5,X6) ),
% 6.63/1.53      inference(instantiation,[status(thm)],[c_13]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_1597,plain,
% 6.63/1.53      ( sP0(sK5,sK5,X0,sK4,X1,X2,X3,X4,X5,X6) = iProver_top ),
% 6.63/1.53      inference(predicate_to_equality,[status(thm)],[c_1592]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_1599,plain,
% 6.63/1.53      ( sP0(sK5,sK5,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = iProver_top ),
% 6.63/1.53      inference(instantiation,[status(thm)],[c_1597]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_8,plain,
% 6.63/1.53      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 6.63/1.53      inference(cnf_transformation,[],[f93]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_1579,plain,
% 6.63/1.53      ( ~ r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 6.63/1.53      | sK5 = X0 ),
% 6.63/1.53      inference(instantiation,[status(thm)],[c_8]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_1580,plain,
% 6.63/1.53      ( sK5 = X0
% 6.63/1.53      | r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 6.63/1.53      inference(predicate_to_equality,[status(thm)],[c_1579]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_1582,plain,
% 6.63/1.53      ( sK5 = sK4
% 6.63/1.53      | r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
% 6.63/1.53      inference(instantiation,[status(thm)],[c_1580]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_1046,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_1549,plain,
% 6.63/1.53      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 6.63/1.53      inference(instantiation,[status(thm)],[c_1046]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_1550,plain,
% 6.63/1.53      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 6.63/1.53      inference(instantiation,[status(thm)],[c_1549]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_21,plain,
% 6.63/1.53      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X0) ),
% 6.63/1.53      inference(cnf_transformation,[],[f102]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_37,plain,
% 6.63/1.53      ( sP0(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 6.63/1.53      inference(instantiation,[status(thm)],[c_21]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_22,plain,
% 6.63/1.53      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
% 6.63/1.53      | X3 = X0
% 6.63/1.53      | X9 = X0
% 6.63/1.53      | X8 = X0
% 6.63/1.53      | X7 = X0
% 6.63/1.53      | X6 = X0
% 6.63/1.53      | X5 = X0
% 6.63/1.53      | X4 = X0
% 6.63/1.53      | X2 = X0
% 6.63/1.53      | X1 = X0 ),
% 6.63/1.53      inference(cnf_transformation,[],[f54]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_34,plain,
% 6.63/1.53      ( ~ sP0(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | sK4 = sK4 ),
% 6.63/1.53      inference(instantiation,[status(thm)],[c_22]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(c_25,negated_conjecture,
% 6.63/1.53      ( sK4 != sK5 ),
% 6.63/1.53      inference(cnf_transformation,[],[f75]) ).
% 6.63/1.53  
% 6.63/1.53  cnf(contradiction,plain,
% 6.63/1.53      ( $false ),
% 6.63/1.53      inference(minisat,
% 6.63/1.53                [status(thm)],
% 6.63/1.53                [c_21206,c_13730,c_1599,c_1582,c_1550,c_37,c_34,c_25]) ).
% 6.63/1.53  
% 6.63/1.53  
% 6.63/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 6.63/1.53  
% 6.63/1.53  ------                               Statistics
% 6.63/1.53  
% 6.63/1.53  ------ General
% 6.63/1.53  
% 6.63/1.53  abstr_ref_over_cycles:                  0
% 6.63/1.53  abstr_ref_under_cycles:                 0
% 6.63/1.53  gc_basic_clause_elim:                   0
% 6.63/1.53  forced_gc_time:                         0
% 6.63/1.53  parsing_time:                           0.014
% 6.63/1.53  unif_index_cands_time:                  0.
% 6.63/1.53  unif_index_add_time:                    0.
% 6.63/1.53  orderings_time:                         0.
% 6.63/1.53  out_proof_time:                         0.011
% 6.63/1.53  total_time:                             1.037
% 6.63/1.53  num_of_symbols:                         42
% 6.63/1.53  num_of_terms:                           30991
% 6.63/1.53  
% 6.63/1.53  ------ Preprocessing
% 6.63/1.53  
% 6.63/1.53  num_of_splits:                          0
% 6.63/1.53  num_of_split_atoms:                     0
% 6.63/1.53  num_of_reused_defs:                     0
% 6.63/1.53  num_eq_ax_congr_red:                    60
% 6.63/1.53  num_of_sem_filtered_clauses:            1
% 6.63/1.53  num_of_subtypes:                        0
% 6.63/1.53  monotx_restored_types:                  0
% 6.63/1.53  sat_num_of_epr_types:                   0
% 6.63/1.53  sat_num_of_non_cyclic_types:            0
% 6.63/1.53  sat_guarded_non_collapsed_types:        0
% 6.63/1.53  num_pure_diseq_elim:                    0
% 6.63/1.53  simp_replaced_by:                       0
% 6.63/1.53  res_preprocessed:                       98
% 6.63/1.53  prep_upred:                             0
% 6.63/1.53  prep_unflattend:                        382
% 6.63/1.53  smt_new_axioms:                         0
% 6.63/1.53  pred_elim_cands:                        3
% 6.63/1.53  pred_elim:                              0
% 6.63/1.53  pred_elim_cl:                           0
% 6.63/1.53  pred_elim_cycles:                       3
% 6.63/1.53  merged_defs:                            0
% 6.63/1.53  merged_defs_ncl:                        0
% 6.63/1.53  bin_hyper_res:                          0
% 6.63/1.53  prep_cycles:                            3
% 6.63/1.53  pred_elim_time:                         0.047
% 6.63/1.53  splitting_time:                         0.
% 6.63/1.53  sem_filter_time:                        0.
% 6.63/1.53  monotx_time:                            0.001
% 6.63/1.53  subtype_inf_time:                       0.
% 6.63/1.53  
% 6.63/1.53  ------ Problem properties
% 6.63/1.53  
% 6.63/1.53  clauses:                                27
% 6.63/1.53  conjectures:                            2
% 6.63/1.53  epr:                                    13
% 6.63/1.53  horn:                                   24
% 6.63/1.53  ground:                                 2
% 6.63/1.53  unary:                                  18
% 6.63/1.53  binary:                                 2
% 6.63/1.53  lits:                                   50
% 6.63/1.53  lits_eq:                                22
% 6.63/1.53  fd_pure:                                0
% 6.63/1.53  fd_pseudo:                              0
% 6.63/1.53  fd_cond:                                0
% 6.63/1.53  fd_pseudo_cond:                         4
% 6.63/1.53  ac_symbols:                             1
% 6.63/1.53  
% 6.63/1.53  ------ Propositional Solver
% 6.63/1.53  
% 6.63/1.53  prop_solver_calls:                      27
% 6.63/1.53  prop_fast_solver_calls:                 668
% 6.63/1.53  smt_solver_calls:                       0
% 6.63/1.53  smt_fast_solver_calls:                  0
% 6.63/1.53  prop_num_of_clauses:                    6716
% 6.63/1.53  prop_preprocess_simplified:             14851
% 6.63/1.53  prop_fo_subsumed:                       0
% 6.63/1.53  prop_solver_time:                       0.
% 6.63/1.53  smt_solver_time:                        0.
% 6.63/1.53  smt_fast_solver_time:                   0.
% 6.63/1.53  prop_fast_solver_time:                  0.
% 6.63/1.53  prop_unsat_core_time:                   0.
% 6.63/1.53  
% 6.63/1.53  ------ QBF
% 6.63/1.53  
% 6.63/1.53  qbf_q_res:                              0
% 6.63/1.53  qbf_num_tautologies:                    0
% 6.63/1.53  qbf_prep_cycles:                        0
% 6.63/1.53  
% 6.63/1.53  ------ BMC1
% 6.63/1.53  
% 6.63/1.53  bmc1_current_bound:                     -1
% 6.63/1.53  bmc1_last_solved_bound:                 -1
% 6.63/1.53  bmc1_unsat_core_size:                   -1
% 6.63/1.53  bmc1_unsat_core_parents_size:           -1
% 6.63/1.53  bmc1_merge_next_fun:                    0
% 6.63/1.53  bmc1_unsat_core_clauses_time:           0.
% 6.63/1.53  
% 6.63/1.53  ------ Instantiation
% 6.63/1.53  
% 6.63/1.53  inst_num_of_clauses:                    1747
% 6.63/1.53  inst_num_in_passive:                    902
% 6.63/1.53  inst_num_in_active:                     319
% 6.63/1.53  inst_num_in_unprocessed:                526
% 6.63/1.53  inst_num_of_loops:                      360
% 6.63/1.53  inst_num_of_learning_restarts:          0
% 6.63/1.53  inst_num_moves_active_passive:          38
% 6.63/1.53  inst_lit_activity:                      0
% 6.63/1.53  inst_lit_activity_moves:                0
% 6.63/1.53  inst_num_tautologies:                   0
% 6.63/1.53  inst_num_prop_implied:                  0
% 6.63/1.53  inst_num_existing_simplified:           0
% 6.63/1.53  inst_num_eq_res_simplified:             0
% 6.63/1.53  inst_num_child_elim:                    0
% 6.63/1.53  inst_num_of_dismatching_blockings:      688
% 6.63/1.53  inst_num_of_non_proper_insts:           1571
% 6.63/1.53  inst_num_of_duplicates:                 0
% 6.63/1.53  inst_inst_num_from_inst_to_res:         0
% 6.63/1.53  inst_dismatching_checking_time:         0.
% 6.63/1.53  
% 6.63/1.53  ------ Resolution
% 6.63/1.53  
% 6.63/1.53  res_num_of_clauses:                     0
% 6.63/1.53  res_num_in_passive:                     0
% 6.63/1.53  res_num_in_active:                      0
% 6.63/1.53  res_num_of_loops:                       101
% 6.63/1.53  res_forward_subset_subsumed:            450
% 6.63/1.53  res_backward_subset_subsumed:           0
% 6.63/1.53  res_forward_subsumed:                   0
% 6.63/1.53  res_backward_subsumed:                  0
% 6.63/1.53  res_forward_subsumption_resolution:     0
% 6.63/1.53  res_backward_subsumption_resolution:    0
% 6.63/1.53  res_clause_to_clause_subsumption:       19607
% 6.63/1.53  res_orphan_elimination:                 0
% 6.63/1.53  res_tautology_del:                      34
% 6.63/1.53  res_num_eq_res_simplified:              0
% 6.63/1.53  res_num_sel_changes:                    0
% 6.63/1.53  res_moves_from_active_to_pass:          0
% 6.63/1.53  
% 6.63/1.53  ------ Superposition
% 6.63/1.53  
% 6.63/1.53  sup_time_total:                         0.
% 6.63/1.53  sup_time_generating:                    0.
% 6.63/1.53  sup_time_sim_full:                      0.
% 6.63/1.53  sup_time_sim_immed:                     0.
% 6.63/1.53  
% 6.63/1.53  sup_num_of_clauses:                     1034
% 6.63/1.53  sup_num_in_active:                      48
% 6.63/1.53  sup_num_in_passive:                     986
% 6.63/1.53  sup_num_of_loops:                       71
% 6.63/1.53  sup_fw_superposition:                   1941
% 6.63/1.53  sup_bw_superposition:                   1437
% 6.63/1.53  sup_immediate_simplified:               1258
% 6.63/1.53  sup_given_eliminated:                   13
% 6.63/1.53  comparisons_done:                       0
% 6.63/1.53  comparisons_avoided:                    2
% 6.63/1.53  
% 6.63/1.53  ------ Simplifications
% 6.63/1.53  
% 6.63/1.53  
% 6.63/1.53  sim_fw_subset_subsumed:                 0
% 6.63/1.53  sim_bw_subset_subsumed:                 0
% 6.63/1.53  sim_fw_subsumed:                        192
% 6.63/1.53  sim_bw_subsumed:                        30
% 6.63/1.53  sim_fw_subsumption_res:                 0
% 6.63/1.53  sim_bw_subsumption_res:                 0
% 6.63/1.53  sim_tautology_del:                      0
% 6.63/1.53  sim_eq_tautology_del:                   172
% 6.63/1.53  sim_eq_res_simp:                        0
% 6.63/1.53  sim_fw_demodulated:                     828
% 6.63/1.53  sim_bw_demodulated:                     223
% 6.63/1.53  sim_light_normalised:                   436
% 6.63/1.53  sim_joinable_taut:                      73
% 6.63/1.53  sim_joinable_simp:                      0
% 6.63/1.53  sim_ac_normalised:                      0
% 6.63/1.53  sim_smt_subsumption:                    0
% 6.63/1.53  
%------------------------------------------------------------------------------
