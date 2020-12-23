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
% DateTime   : Thu Dec  3 11:29:21 EST 2020

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :  140 (7817 expanded)
%              Number of clauses        :   62 (1143 expanded)
%              Number of leaves         :   24 (2500 expanded)
%              Depth                    :   26
%              Number of atoms          :  359 (8515 expanded)
%              Number of equality atoms :  256 (8394 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f76,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f45,f40])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f92,plain,(
    k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f74,f76,f82,f82,f82])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f85,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f42,f40,f76])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f41,f76])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f10])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(definition_unfolding,[],[f66,f76,f82])).

fof(f91,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) != X9 ) ),
    inference(definition_unfolding,[],[f64,f83])).

fof(f105,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) ),
    inference(equality_resolution,[],[f91])).

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

fof(f96,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(equality_resolution,[],[f63])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f46,f82])).

fof(f95,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | X0 != X9 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f104,plain,(
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
    inference(cnf_transformation,[],[f92])).

cnf(c_1756,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(demodulation,[status(thm)],[c_0,c_26])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1380,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2,c_1])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1800,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_1380,c_4])).

cnf(c_2046,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_1756,c_1800])).

cnf(c_2045,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1380,c_1800])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2061,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2045,c_3])).

cnf(c_2079,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2046,c_1380,c_2061])).

cnf(c_2432,plain,
    ( k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2079,c_2061])).

cnf(c_1801,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))),X0)) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0) ),
    inference(superposition,[status(thm)],[c_1756,c_4])).

cnf(c_2417,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))),X0),X1)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0),X1) ),
    inference(superposition,[status(thm)],[c_1801,c_4])).

cnf(c_2900,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_2417,c_2061,c_2417,c_2432])).

cnf(c_1805,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_1380])).

cnf(c_2916,plain,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0),k5_xboole_0(X1,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2900,c_1805])).

cnf(c_3369,plain,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(X0,X1))),X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_2916,c_4])).

cnf(c_3374,plain,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(X0,X1))),X2)) = X2 ),
    inference(demodulation,[status(thm)],[c_3369,c_2061,c_2900])).

cnf(c_5714,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1380,c_3374])).

cnf(c_5809,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(X1,X0))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X1) ),
    inference(demodulation,[status(thm)],[c_5714,c_3,c_2900])).

cnf(c_5818,plain,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0),X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_5809,c_3374])).

cnf(c_5824,plain,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(X0,X1))) = X1 ),
    inference(light_normalisation,[status(thm)],[c_5818,c_2900])).

cnf(c_6712,plain,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_xboole_0)) = k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(superposition,[status(thm)],[c_2432,c_5824])).

cnf(c_2412,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),X0))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0) ),
    inference(superposition,[status(thm)],[c_4,c_1801])).

cnf(c_6209,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),X0),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0)) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(superposition,[status(thm)],[c_2412,c_5809])).

cnf(c_3356,plain,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),X0),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2412,c_2916])).

cnf(c_6222,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),X0),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0)),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_xboole_0)) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
    inference(superposition,[status(thm)],[c_3356,c_5809])).

cnf(c_2906,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1380,c_2900])).

cnf(c_2926,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2906,c_2061])).

cnf(c_6260,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),X0),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(demodulation,[status(thm)],[c_6222,c_3,c_2926])).

cnf(c_6275,plain,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(demodulation,[status(thm)],[c_6209,c_6260])).

cnf(c_6751,plain,
    ( k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(demodulation,[status(thm)],[c_6712,c_3,c_2900,c_6275])).

cnf(c_24,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1360,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1943,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1360])).

cnf(c_16567,plain,
    ( sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6751,c_1943])).

cnf(c_16569,plain,
    ( sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16567,c_3,c_1380])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
    | ~ sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10)
    | r2_hidden(X0,X10) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1530,plain,
    ( ~ sP0(sK5,X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X0,k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9))
    | r2_hidden(sK5,k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1885,plain,
    ( ~ sP0(sK5,sK5,X0,sK4,X1,X2,X3,X4,X5,X6)
    | ~ sP1(X6,X5,X4,X3,X2,X1,sK4,X0,sK5,k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7))
    | r2_hidden(sK5,k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)) ),
    inference(instantiation,[status(thm)],[c_1530])).

cnf(c_1886,plain,
    ( sP0(sK5,sK5,X0,sK4,X1,X2,X3,X4,X5,X6) != iProver_top
    | sP1(X6,X5,X4,X3,X2,X1,sK4,X0,sK5,k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)) != iProver_top
    | r2_hidden(sK5,k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1885])).

cnf(c_1888,plain,
    ( sP0(sK5,sK5,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != iProver_top
    | sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1886])).

cnf(c_13,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1541,plain,
    ( sP0(sK5,sK5,X0,sK4,X1,X2,X3,X4,X5,X6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1542,plain,
    ( sP0(sK5,sK5,X0,sK4,X1,X2,X3,X4,X5,X6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1541])).

cnf(c_1544,plain,
    ( sP0(sK5,sK5,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1542])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1427,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1428,plain,
    ( sK5 = X0
    | r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1427])).

cnf(c_1430,plain,
    ( sK5 = sK4
    | r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1428])).

cnf(c_1046,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1410,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_1411,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1410])).

cnf(c_21,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X0) ),
    inference(cnf_transformation,[],[f104])).

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
    inference(minisat,[status(thm)],[c_16569,c_1888,c_1544,c_1430,c_1411,c_37,c_34,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.67/1.54  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.67/1.54  
% 7.67/1.54  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.67/1.54  
% 7.67/1.54  ------  iProver source info
% 7.67/1.54  
% 7.67/1.54  git: date: 2020-06-30 10:37:57 +0100
% 7.67/1.54  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.67/1.54  git: non_committed_changes: false
% 7.67/1.54  git: last_make_outside_of_git: false
% 7.67/1.54  
% 7.67/1.54  ------ 
% 7.67/1.54  
% 7.67/1.54  ------ Input Options
% 7.67/1.54  
% 7.67/1.54  --out_options                           all
% 7.67/1.54  --tptp_safe_out                         true
% 7.67/1.54  --problem_path                          ""
% 7.67/1.54  --include_path                          ""
% 7.67/1.54  --clausifier                            res/vclausify_rel
% 7.67/1.54  --clausifier_options                    ""
% 7.67/1.54  --stdin                                 false
% 7.67/1.54  --stats_out                             all
% 7.67/1.54  
% 7.67/1.54  ------ General Options
% 7.67/1.54  
% 7.67/1.54  --fof                                   false
% 7.67/1.54  --time_out_real                         305.
% 7.67/1.54  --time_out_virtual                      -1.
% 7.67/1.54  --symbol_type_check                     false
% 7.67/1.54  --clausify_out                          false
% 7.67/1.54  --sig_cnt_out                           false
% 7.67/1.54  --trig_cnt_out                          false
% 7.67/1.54  --trig_cnt_out_tolerance                1.
% 7.67/1.54  --trig_cnt_out_sk_spl                   false
% 7.67/1.54  --abstr_cl_out                          false
% 7.67/1.54  
% 7.67/1.54  ------ Global Options
% 7.67/1.54  
% 7.67/1.54  --schedule                              default
% 7.67/1.54  --add_important_lit                     false
% 7.67/1.54  --prop_solver_per_cl                    1000
% 7.67/1.54  --min_unsat_core                        false
% 7.67/1.54  --soft_assumptions                      false
% 7.67/1.54  --soft_lemma_size                       3
% 7.67/1.54  --prop_impl_unit_size                   0
% 7.67/1.54  --prop_impl_unit                        []
% 7.67/1.54  --share_sel_clauses                     true
% 7.67/1.54  --reset_solvers                         false
% 7.67/1.54  --bc_imp_inh                            [conj_cone]
% 7.67/1.54  --conj_cone_tolerance                   3.
% 7.67/1.54  --extra_neg_conj                        none
% 7.67/1.54  --large_theory_mode                     true
% 7.67/1.54  --prolific_symb_bound                   200
% 7.67/1.54  --lt_threshold                          2000
% 7.67/1.54  --clause_weak_htbl                      true
% 7.67/1.54  --gc_record_bc_elim                     false
% 7.67/1.54  
% 7.67/1.54  ------ Preprocessing Options
% 7.67/1.54  
% 7.67/1.54  --preprocessing_flag                    true
% 7.67/1.54  --time_out_prep_mult                    0.1
% 7.67/1.54  --splitting_mode                        input
% 7.67/1.54  --splitting_grd                         true
% 7.67/1.54  --splitting_cvd                         false
% 7.67/1.54  --splitting_cvd_svl                     false
% 7.67/1.54  --splitting_nvd                         32
% 7.67/1.54  --sub_typing                            true
% 7.67/1.54  --prep_gs_sim                           true
% 7.67/1.54  --prep_unflatten                        true
% 7.67/1.54  --prep_res_sim                          true
% 7.67/1.54  --prep_upred                            true
% 7.67/1.54  --prep_sem_filter                       exhaustive
% 7.67/1.54  --prep_sem_filter_out                   false
% 7.67/1.54  --pred_elim                             true
% 7.67/1.54  --res_sim_input                         true
% 7.67/1.54  --eq_ax_congr_red                       true
% 7.67/1.54  --pure_diseq_elim                       true
% 7.67/1.54  --brand_transform                       false
% 7.67/1.54  --non_eq_to_eq                          false
% 7.67/1.54  --prep_def_merge                        true
% 7.67/1.54  --prep_def_merge_prop_impl              false
% 7.67/1.54  --prep_def_merge_mbd                    true
% 7.67/1.54  --prep_def_merge_tr_red                 false
% 7.67/1.54  --prep_def_merge_tr_cl                  false
% 7.67/1.54  --smt_preprocessing                     true
% 7.67/1.54  --smt_ac_axioms                         fast
% 7.67/1.54  --preprocessed_out                      false
% 7.67/1.54  --preprocessed_stats                    false
% 7.67/1.54  
% 7.67/1.54  ------ Abstraction refinement Options
% 7.67/1.54  
% 7.67/1.54  --abstr_ref                             []
% 7.67/1.54  --abstr_ref_prep                        false
% 7.67/1.54  --abstr_ref_until_sat                   false
% 7.67/1.54  --abstr_ref_sig_restrict                funpre
% 7.67/1.54  --abstr_ref_af_restrict_to_split_sk     false
% 7.67/1.54  --abstr_ref_under                       []
% 7.67/1.54  
% 7.67/1.54  ------ SAT Options
% 7.67/1.54  
% 7.67/1.54  --sat_mode                              false
% 7.67/1.54  --sat_fm_restart_options                ""
% 7.67/1.54  --sat_gr_def                            false
% 7.67/1.54  --sat_epr_types                         true
% 7.67/1.54  --sat_non_cyclic_types                  false
% 7.67/1.54  --sat_finite_models                     false
% 7.67/1.54  --sat_fm_lemmas                         false
% 7.67/1.54  --sat_fm_prep                           false
% 7.67/1.54  --sat_fm_uc_incr                        true
% 7.67/1.54  --sat_out_model                         small
% 7.67/1.54  --sat_out_clauses                       false
% 7.67/1.54  
% 7.67/1.54  ------ QBF Options
% 7.67/1.54  
% 7.67/1.54  --qbf_mode                              false
% 7.67/1.54  --qbf_elim_univ                         false
% 7.67/1.54  --qbf_dom_inst                          none
% 7.67/1.54  --qbf_dom_pre_inst                      false
% 7.67/1.54  --qbf_sk_in                             false
% 7.67/1.54  --qbf_pred_elim                         true
% 7.67/1.54  --qbf_split                             512
% 7.67/1.54  
% 7.67/1.54  ------ BMC1 Options
% 7.67/1.54  
% 7.67/1.54  --bmc1_incremental                      false
% 7.67/1.54  --bmc1_axioms                           reachable_all
% 7.67/1.54  --bmc1_min_bound                        0
% 7.67/1.54  --bmc1_max_bound                        -1
% 7.67/1.54  --bmc1_max_bound_default                -1
% 7.67/1.54  --bmc1_symbol_reachability              true
% 7.67/1.54  --bmc1_property_lemmas                  false
% 7.67/1.54  --bmc1_k_induction                      false
% 7.67/1.54  --bmc1_non_equiv_states                 false
% 7.67/1.54  --bmc1_deadlock                         false
% 7.67/1.54  --bmc1_ucm                              false
% 7.67/1.54  --bmc1_add_unsat_core                   none
% 7.67/1.54  --bmc1_unsat_core_children              false
% 7.67/1.54  --bmc1_unsat_core_extrapolate_axioms    false
% 7.67/1.54  --bmc1_out_stat                         full
% 7.67/1.54  --bmc1_ground_init                      false
% 7.67/1.54  --bmc1_pre_inst_next_state              false
% 7.67/1.54  --bmc1_pre_inst_state                   false
% 7.67/1.54  --bmc1_pre_inst_reach_state             false
% 7.67/1.54  --bmc1_out_unsat_core                   false
% 7.67/1.54  --bmc1_aig_witness_out                  false
% 7.67/1.54  --bmc1_verbose                          false
% 7.67/1.54  --bmc1_dump_clauses_tptp                false
% 7.67/1.54  --bmc1_dump_unsat_core_tptp             false
% 7.67/1.54  --bmc1_dump_file                        -
% 7.67/1.54  --bmc1_ucm_expand_uc_limit              128
% 7.67/1.54  --bmc1_ucm_n_expand_iterations          6
% 7.67/1.54  --bmc1_ucm_extend_mode                  1
% 7.67/1.54  --bmc1_ucm_init_mode                    2
% 7.67/1.54  --bmc1_ucm_cone_mode                    none
% 7.67/1.54  --bmc1_ucm_reduced_relation_type        0
% 7.67/1.54  --bmc1_ucm_relax_model                  4
% 7.67/1.54  --bmc1_ucm_full_tr_after_sat            true
% 7.67/1.54  --bmc1_ucm_expand_neg_assumptions       false
% 7.67/1.54  --bmc1_ucm_layered_model                none
% 7.67/1.54  --bmc1_ucm_max_lemma_size               10
% 7.67/1.54  
% 7.67/1.54  ------ AIG Options
% 7.67/1.54  
% 7.67/1.54  --aig_mode                              false
% 7.67/1.54  
% 7.67/1.54  ------ Instantiation Options
% 7.67/1.54  
% 7.67/1.54  --instantiation_flag                    true
% 7.67/1.54  --inst_sos_flag                         true
% 7.67/1.54  --inst_sos_phase                        true
% 7.67/1.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.67/1.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.67/1.54  --inst_lit_sel_side                     num_symb
% 7.67/1.54  --inst_solver_per_active                1400
% 7.67/1.54  --inst_solver_calls_frac                1.
% 7.67/1.54  --inst_passive_queue_type               priority_queues
% 7.67/1.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.67/1.54  --inst_passive_queues_freq              [25;2]
% 7.67/1.54  --inst_dismatching                      true
% 7.67/1.54  --inst_eager_unprocessed_to_passive     true
% 7.67/1.54  --inst_prop_sim_given                   true
% 7.67/1.54  --inst_prop_sim_new                     false
% 7.67/1.54  --inst_subs_new                         false
% 7.67/1.54  --inst_eq_res_simp                      false
% 7.67/1.54  --inst_subs_given                       false
% 7.67/1.54  --inst_orphan_elimination               true
% 7.67/1.54  --inst_learning_loop_flag               true
% 7.67/1.54  --inst_learning_start                   3000
% 7.67/1.54  --inst_learning_factor                  2
% 7.67/1.54  --inst_start_prop_sim_after_learn       3
% 7.67/1.54  --inst_sel_renew                        solver
% 7.67/1.54  --inst_lit_activity_flag                true
% 7.67/1.54  --inst_restr_to_given                   false
% 7.67/1.54  --inst_activity_threshold               500
% 7.67/1.54  --inst_out_proof                        true
% 7.67/1.54  
% 7.67/1.54  ------ Resolution Options
% 7.67/1.54  
% 7.67/1.54  --resolution_flag                       true
% 7.67/1.54  --res_lit_sel                           adaptive
% 7.67/1.54  --res_lit_sel_side                      none
% 7.67/1.54  --res_ordering                          kbo
% 7.67/1.54  --res_to_prop_solver                    active
% 7.67/1.54  --res_prop_simpl_new                    false
% 7.67/1.54  --res_prop_simpl_given                  true
% 7.67/1.54  --res_passive_queue_type                priority_queues
% 7.67/1.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.67/1.54  --res_passive_queues_freq               [15;5]
% 7.67/1.54  --res_forward_subs                      full
% 7.67/1.54  --res_backward_subs                     full
% 7.67/1.54  --res_forward_subs_resolution           true
% 7.67/1.54  --res_backward_subs_resolution          true
% 7.67/1.54  --res_orphan_elimination                true
% 7.67/1.54  --res_time_limit                        2.
% 7.67/1.54  --res_out_proof                         true
% 7.67/1.54  
% 7.67/1.54  ------ Superposition Options
% 7.67/1.54  
% 7.67/1.54  --superposition_flag                    true
% 7.67/1.54  --sup_passive_queue_type                priority_queues
% 7.67/1.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.67/1.54  --sup_passive_queues_freq               [8;1;4]
% 7.67/1.54  --demod_completeness_check              fast
% 7.67/1.54  --demod_use_ground                      true
% 7.67/1.54  --sup_to_prop_solver                    passive
% 7.67/1.54  --sup_prop_simpl_new                    true
% 7.67/1.54  --sup_prop_simpl_given                  true
% 7.67/1.54  --sup_fun_splitting                     true
% 7.67/1.54  --sup_smt_interval                      50000
% 7.67/1.54  
% 7.67/1.54  ------ Superposition Simplification Setup
% 7.67/1.54  
% 7.67/1.54  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.67/1.54  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.67/1.54  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.67/1.54  --sup_full_triv                         [TrivRules;PropSubs]
% 7.67/1.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.67/1.54  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.67/1.54  --sup_immed_triv                        [TrivRules]
% 7.67/1.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.54  --sup_immed_bw_main                     []
% 7.67/1.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.67/1.54  --sup_input_triv                        [Unflattening;TrivRules]
% 7.67/1.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.54  --sup_input_bw                          []
% 7.67/1.54  
% 7.67/1.54  ------ Combination Options
% 7.67/1.54  
% 7.67/1.54  --comb_res_mult                         3
% 7.67/1.54  --comb_sup_mult                         2
% 7.67/1.54  --comb_inst_mult                        10
% 7.67/1.54  
% 7.67/1.54  ------ Debug Options
% 7.67/1.54  
% 7.67/1.54  --dbg_backtrace                         false
% 7.67/1.54  --dbg_dump_prop_clauses                 false
% 7.67/1.54  --dbg_dump_prop_clauses_file            -
% 7.67/1.54  --dbg_out_stat                          false
% 7.67/1.54  ------ Parsing...
% 7.67/1.54  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.67/1.54  
% 7.67/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.67/1.54  
% 7.67/1.54  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.67/1.54  
% 7.67/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.54  ------ Proving...
% 7.67/1.54  ------ Problem Properties 
% 7.67/1.54  
% 7.67/1.54  
% 7.67/1.54  clauses                                 27
% 7.67/1.54  conjectures                             2
% 7.67/1.54  EPR                                     13
% 7.67/1.54  Horn                                    24
% 7.67/1.54  unary                                   18
% 7.67/1.54  binary                                  2
% 7.67/1.54  lits                                    50
% 7.67/1.54  lits eq                                 22
% 7.67/1.54  fd_pure                                 0
% 7.67/1.54  fd_pseudo                               0
% 7.67/1.54  fd_cond                                 0
% 7.67/1.54  fd_pseudo_cond                          4
% 7.67/1.54  AC symbols                              0
% 7.67/1.54  
% 7.67/1.54  ------ Schedule dynamic 5 is on 
% 7.67/1.54  
% 7.67/1.54  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.67/1.54  
% 7.67/1.54  
% 7.67/1.54  ------ 
% 7.67/1.54  Current options:
% 7.67/1.54  ------ 
% 7.67/1.54  
% 7.67/1.54  ------ Input Options
% 7.67/1.54  
% 7.67/1.54  --out_options                           all
% 7.67/1.54  --tptp_safe_out                         true
% 7.67/1.54  --problem_path                          ""
% 7.67/1.54  --include_path                          ""
% 7.67/1.54  --clausifier                            res/vclausify_rel
% 7.67/1.54  --clausifier_options                    ""
% 7.67/1.54  --stdin                                 false
% 7.67/1.54  --stats_out                             all
% 7.67/1.54  
% 7.67/1.54  ------ General Options
% 7.67/1.54  
% 7.67/1.54  --fof                                   false
% 7.67/1.54  --time_out_real                         305.
% 7.67/1.54  --time_out_virtual                      -1.
% 7.67/1.54  --symbol_type_check                     false
% 7.67/1.54  --clausify_out                          false
% 7.67/1.54  --sig_cnt_out                           false
% 7.67/1.54  --trig_cnt_out                          false
% 7.67/1.54  --trig_cnt_out_tolerance                1.
% 7.67/1.54  --trig_cnt_out_sk_spl                   false
% 7.67/1.54  --abstr_cl_out                          false
% 7.67/1.54  
% 7.67/1.54  ------ Global Options
% 7.67/1.54  
% 7.67/1.54  --schedule                              default
% 7.67/1.54  --add_important_lit                     false
% 7.67/1.54  --prop_solver_per_cl                    1000
% 7.67/1.54  --min_unsat_core                        false
% 7.67/1.54  --soft_assumptions                      false
% 7.67/1.54  --soft_lemma_size                       3
% 7.67/1.54  --prop_impl_unit_size                   0
% 7.67/1.54  --prop_impl_unit                        []
% 7.67/1.54  --share_sel_clauses                     true
% 7.67/1.54  --reset_solvers                         false
% 7.67/1.54  --bc_imp_inh                            [conj_cone]
% 7.67/1.54  --conj_cone_tolerance                   3.
% 7.67/1.54  --extra_neg_conj                        none
% 7.67/1.54  --large_theory_mode                     true
% 7.67/1.54  --prolific_symb_bound                   200
% 7.67/1.54  --lt_threshold                          2000
% 7.67/1.54  --clause_weak_htbl                      true
% 7.67/1.54  --gc_record_bc_elim                     false
% 7.67/1.54  
% 7.67/1.54  ------ Preprocessing Options
% 7.67/1.54  
% 7.67/1.54  --preprocessing_flag                    true
% 7.67/1.54  --time_out_prep_mult                    0.1
% 7.67/1.54  --splitting_mode                        input
% 7.67/1.54  --splitting_grd                         true
% 7.67/1.54  --splitting_cvd                         false
% 7.67/1.54  --splitting_cvd_svl                     false
% 7.67/1.54  --splitting_nvd                         32
% 7.67/1.54  --sub_typing                            true
% 7.67/1.54  --prep_gs_sim                           true
% 7.67/1.54  --prep_unflatten                        true
% 7.67/1.54  --prep_res_sim                          true
% 7.67/1.54  --prep_upred                            true
% 7.67/1.54  --prep_sem_filter                       exhaustive
% 7.67/1.54  --prep_sem_filter_out                   false
% 7.67/1.54  --pred_elim                             true
% 7.67/1.54  --res_sim_input                         true
% 7.67/1.54  --eq_ax_congr_red                       true
% 7.67/1.54  --pure_diseq_elim                       true
% 7.67/1.54  --brand_transform                       false
% 7.67/1.54  --non_eq_to_eq                          false
% 7.67/1.54  --prep_def_merge                        true
% 7.67/1.54  --prep_def_merge_prop_impl              false
% 7.67/1.54  --prep_def_merge_mbd                    true
% 7.67/1.54  --prep_def_merge_tr_red                 false
% 7.67/1.54  --prep_def_merge_tr_cl                  false
% 7.67/1.54  --smt_preprocessing                     true
% 7.67/1.54  --smt_ac_axioms                         fast
% 7.67/1.54  --preprocessed_out                      false
% 7.67/1.54  --preprocessed_stats                    false
% 7.67/1.54  
% 7.67/1.54  ------ Abstraction refinement Options
% 7.67/1.54  
% 7.67/1.54  --abstr_ref                             []
% 7.67/1.54  --abstr_ref_prep                        false
% 7.67/1.54  --abstr_ref_until_sat                   false
% 7.67/1.54  --abstr_ref_sig_restrict                funpre
% 7.67/1.54  --abstr_ref_af_restrict_to_split_sk     false
% 7.67/1.54  --abstr_ref_under                       []
% 7.67/1.54  
% 7.67/1.54  ------ SAT Options
% 7.67/1.54  
% 7.67/1.54  --sat_mode                              false
% 7.67/1.54  --sat_fm_restart_options                ""
% 7.67/1.54  --sat_gr_def                            false
% 7.67/1.54  --sat_epr_types                         true
% 7.67/1.54  --sat_non_cyclic_types                  false
% 7.67/1.54  --sat_finite_models                     false
% 7.67/1.54  --sat_fm_lemmas                         false
% 7.67/1.54  --sat_fm_prep                           false
% 7.67/1.54  --sat_fm_uc_incr                        true
% 7.67/1.54  --sat_out_model                         small
% 7.67/1.54  --sat_out_clauses                       false
% 7.67/1.54  
% 7.67/1.54  ------ QBF Options
% 7.67/1.54  
% 7.67/1.54  --qbf_mode                              false
% 7.67/1.54  --qbf_elim_univ                         false
% 7.67/1.54  --qbf_dom_inst                          none
% 7.67/1.54  --qbf_dom_pre_inst                      false
% 7.67/1.54  --qbf_sk_in                             false
% 7.67/1.54  --qbf_pred_elim                         true
% 7.67/1.54  --qbf_split                             512
% 7.67/1.54  
% 7.67/1.54  ------ BMC1 Options
% 7.67/1.54  
% 7.67/1.54  --bmc1_incremental                      false
% 7.67/1.54  --bmc1_axioms                           reachable_all
% 7.67/1.54  --bmc1_min_bound                        0
% 7.67/1.54  --bmc1_max_bound                        -1
% 7.67/1.54  --bmc1_max_bound_default                -1
% 7.67/1.54  --bmc1_symbol_reachability              true
% 7.67/1.54  --bmc1_property_lemmas                  false
% 7.67/1.54  --bmc1_k_induction                      false
% 7.67/1.54  --bmc1_non_equiv_states                 false
% 7.67/1.54  --bmc1_deadlock                         false
% 7.67/1.54  --bmc1_ucm                              false
% 7.67/1.54  --bmc1_add_unsat_core                   none
% 7.67/1.54  --bmc1_unsat_core_children              false
% 7.67/1.54  --bmc1_unsat_core_extrapolate_axioms    false
% 7.67/1.54  --bmc1_out_stat                         full
% 7.67/1.54  --bmc1_ground_init                      false
% 7.67/1.54  --bmc1_pre_inst_next_state              false
% 7.67/1.54  --bmc1_pre_inst_state                   false
% 7.67/1.54  --bmc1_pre_inst_reach_state             false
% 7.67/1.54  --bmc1_out_unsat_core                   false
% 7.67/1.54  --bmc1_aig_witness_out                  false
% 7.67/1.54  --bmc1_verbose                          false
% 7.67/1.54  --bmc1_dump_clauses_tptp                false
% 7.67/1.54  --bmc1_dump_unsat_core_tptp             false
% 7.67/1.54  --bmc1_dump_file                        -
% 7.67/1.54  --bmc1_ucm_expand_uc_limit              128
% 7.67/1.54  --bmc1_ucm_n_expand_iterations          6
% 7.67/1.54  --bmc1_ucm_extend_mode                  1
% 7.67/1.54  --bmc1_ucm_init_mode                    2
% 7.67/1.54  --bmc1_ucm_cone_mode                    none
% 7.67/1.54  --bmc1_ucm_reduced_relation_type        0
% 7.67/1.54  --bmc1_ucm_relax_model                  4
% 7.67/1.54  --bmc1_ucm_full_tr_after_sat            true
% 7.67/1.54  --bmc1_ucm_expand_neg_assumptions       false
% 7.67/1.54  --bmc1_ucm_layered_model                none
% 7.67/1.54  --bmc1_ucm_max_lemma_size               10
% 7.67/1.54  
% 7.67/1.54  ------ AIG Options
% 7.67/1.54  
% 7.67/1.54  --aig_mode                              false
% 7.67/1.54  
% 7.67/1.54  ------ Instantiation Options
% 7.67/1.54  
% 7.67/1.54  --instantiation_flag                    true
% 7.67/1.54  --inst_sos_flag                         true
% 7.67/1.54  --inst_sos_phase                        true
% 7.67/1.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.67/1.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.67/1.54  --inst_lit_sel_side                     none
% 7.67/1.54  --inst_solver_per_active                1400
% 7.67/1.54  --inst_solver_calls_frac                1.
% 7.67/1.54  --inst_passive_queue_type               priority_queues
% 7.67/1.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.67/1.54  --inst_passive_queues_freq              [25;2]
% 7.67/1.54  --inst_dismatching                      true
% 7.67/1.54  --inst_eager_unprocessed_to_passive     true
% 7.67/1.54  --inst_prop_sim_given                   true
% 7.67/1.54  --inst_prop_sim_new                     false
% 7.67/1.54  --inst_subs_new                         false
% 7.67/1.54  --inst_eq_res_simp                      false
% 7.67/1.54  --inst_subs_given                       false
% 7.67/1.54  --inst_orphan_elimination               true
% 7.67/1.54  --inst_learning_loop_flag               true
% 7.67/1.54  --inst_learning_start                   3000
% 7.67/1.54  --inst_learning_factor                  2
% 7.67/1.54  --inst_start_prop_sim_after_learn       3
% 7.67/1.54  --inst_sel_renew                        solver
% 7.67/1.54  --inst_lit_activity_flag                true
% 7.67/1.54  --inst_restr_to_given                   false
% 7.67/1.54  --inst_activity_threshold               500
% 7.67/1.54  --inst_out_proof                        true
% 7.67/1.54  
% 7.67/1.54  ------ Resolution Options
% 7.67/1.54  
% 7.67/1.54  --resolution_flag                       false
% 7.67/1.54  --res_lit_sel                           adaptive
% 7.67/1.54  --res_lit_sel_side                      none
% 7.67/1.54  --res_ordering                          kbo
% 7.67/1.54  --res_to_prop_solver                    active
% 7.67/1.54  --res_prop_simpl_new                    false
% 7.67/1.54  --res_prop_simpl_given                  true
% 7.67/1.54  --res_passive_queue_type                priority_queues
% 7.67/1.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.67/1.54  --res_passive_queues_freq               [15;5]
% 7.67/1.54  --res_forward_subs                      full
% 7.67/1.54  --res_backward_subs                     full
% 7.67/1.54  --res_forward_subs_resolution           true
% 7.67/1.54  --res_backward_subs_resolution          true
% 7.67/1.54  --res_orphan_elimination                true
% 7.67/1.54  --res_time_limit                        2.
% 7.67/1.54  --res_out_proof                         true
% 7.67/1.54  
% 7.67/1.54  ------ Superposition Options
% 7.67/1.54  
% 7.67/1.54  --superposition_flag                    true
% 7.67/1.54  --sup_passive_queue_type                priority_queues
% 7.67/1.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.67/1.54  --sup_passive_queues_freq               [8;1;4]
% 7.67/1.54  --demod_completeness_check              fast
% 7.67/1.54  --demod_use_ground                      true
% 7.67/1.54  --sup_to_prop_solver                    passive
% 7.67/1.54  --sup_prop_simpl_new                    true
% 7.67/1.54  --sup_prop_simpl_given                  true
% 7.67/1.54  --sup_fun_splitting                     true
% 7.67/1.54  --sup_smt_interval                      50000
% 7.67/1.54  
% 7.67/1.54  ------ Superposition Simplification Setup
% 7.67/1.54  
% 7.67/1.54  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.67/1.54  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.67/1.54  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.67/1.54  --sup_full_triv                         [TrivRules;PropSubs]
% 7.67/1.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.67/1.54  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.67/1.54  --sup_immed_triv                        [TrivRules]
% 7.67/1.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.54  --sup_immed_bw_main                     []
% 7.67/1.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.67/1.54  --sup_input_triv                        [Unflattening;TrivRules]
% 7.67/1.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.54  --sup_input_bw                          []
% 7.67/1.54  
% 7.67/1.54  ------ Combination Options
% 7.67/1.54  
% 7.67/1.54  --comb_res_mult                         3
% 7.67/1.54  --comb_sup_mult                         2
% 7.67/1.54  --comb_inst_mult                        10
% 7.67/1.54  
% 7.67/1.54  ------ Debug Options
% 7.67/1.54  
% 7.67/1.54  --dbg_backtrace                         false
% 7.67/1.54  --dbg_dump_prop_clauses                 false
% 7.67/1.54  --dbg_dump_prop_clauses_file            -
% 7.67/1.54  --dbg_out_stat                          false
% 7.67/1.54  
% 7.67/1.54  
% 7.67/1.54  
% 7.67/1.54  
% 7.67/1.54  ------ Proving...
% 7.67/1.54  
% 7.67/1.54  
% 7.67/1.54  % SZS status Theorem for theBenchmark.p
% 7.67/1.54  
% 7.67/1.54  % SZS output start CNFRefutation for theBenchmark.p
% 7.67/1.54  
% 7.67/1.54  fof(f1,axiom,(
% 7.67/1.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.67/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.54  
% 7.67/1.54  fof(f39,plain,(
% 7.67/1.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.67/1.54    inference(cnf_transformation,[],[f1])).
% 7.67/1.54  
% 7.67/1.54  fof(f18,conjecture,(
% 7.67/1.54    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 7.67/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.54  
% 7.67/1.54  fof(f19,negated_conjecture,(
% 7.67/1.54    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 7.67/1.54    inference(negated_conjecture,[],[f18])).
% 7.67/1.54  
% 7.67/1.54  fof(f21,plain,(
% 7.67/1.54    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 7.67/1.54    inference(ennf_transformation,[],[f19])).
% 7.67/1.54  
% 7.67/1.54  fof(f37,plain,(
% 7.67/1.54    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK4 != sK5 & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4))),
% 7.67/1.54    introduced(choice_axiom,[])).
% 7.67/1.54  
% 7.67/1.54  fof(f38,plain,(
% 7.67/1.54    sK4 != sK5 & k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4)),
% 7.67/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f21,f37])).
% 7.67/1.54  
% 7.67/1.54  fof(f74,plain,(
% 7.67/1.54    k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4)),
% 7.67/1.54    inference(cnf_transformation,[],[f38])).
% 7.67/1.54  
% 7.67/1.54  fof(f7,axiom,(
% 7.67/1.54    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.67/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.54  
% 7.67/1.54  fof(f45,plain,(
% 7.67/1.54    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.67/1.54    inference(cnf_transformation,[],[f7])).
% 7.67/1.54  
% 7.67/1.54  fof(f2,axiom,(
% 7.67/1.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.67/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.54  
% 7.67/1.54  fof(f40,plain,(
% 7.67/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.67/1.54    inference(cnf_transformation,[],[f2])).
% 7.67/1.54  
% 7.67/1.54  fof(f76,plain,(
% 7.67/1.54    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 7.67/1.54    inference(definition_unfolding,[],[f45,f40])).
% 7.67/1.54  
% 7.67/1.54  fof(f11,axiom,(
% 7.67/1.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.67/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.54  
% 7.67/1.54  fof(f67,plain,(
% 7.67/1.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.67/1.54    inference(cnf_transformation,[],[f11])).
% 7.67/1.54  
% 7.67/1.54  fof(f12,axiom,(
% 7.67/1.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.67/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.54  
% 7.67/1.54  fof(f68,plain,(
% 7.67/1.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.67/1.54    inference(cnf_transformation,[],[f12])).
% 7.67/1.54  
% 7.67/1.54  fof(f13,axiom,(
% 7.67/1.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.67/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.54  
% 7.67/1.54  fof(f69,plain,(
% 7.67/1.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.67/1.54    inference(cnf_transformation,[],[f13])).
% 7.67/1.54  
% 7.67/1.54  fof(f14,axiom,(
% 7.67/1.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.67/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.54  
% 7.67/1.54  fof(f70,plain,(
% 7.67/1.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.67/1.54    inference(cnf_transformation,[],[f14])).
% 7.67/1.54  
% 7.67/1.54  fof(f15,axiom,(
% 7.67/1.54    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.67/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.54  
% 7.67/1.54  fof(f71,plain,(
% 7.67/1.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.67/1.54    inference(cnf_transformation,[],[f15])).
% 7.67/1.54  
% 7.67/1.54  fof(f16,axiom,(
% 7.67/1.54    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.67/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.54  
% 7.67/1.54  fof(f72,plain,(
% 7.67/1.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.67/1.54    inference(cnf_transformation,[],[f16])).
% 7.67/1.54  
% 7.67/1.54  fof(f17,axiom,(
% 7.67/1.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 7.67/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.54  
% 7.67/1.54  fof(f73,plain,(
% 7.67/1.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.67/1.54    inference(cnf_transformation,[],[f17])).
% 7.67/1.54  
% 7.67/1.54  fof(f77,plain,(
% 7.67/1.54    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.67/1.54    inference(definition_unfolding,[],[f72,f73])).
% 7.67/1.54  
% 7.67/1.54  fof(f78,plain,(
% 7.67/1.54    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.67/1.54    inference(definition_unfolding,[],[f71,f77])).
% 7.67/1.54  
% 7.67/1.54  fof(f79,plain,(
% 7.67/1.54    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.67/1.54    inference(definition_unfolding,[],[f70,f78])).
% 7.67/1.54  
% 7.67/1.54  fof(f80,plain,(
% 7.67/1.54    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.67/1.54    inference(definition_unfolding,[],[f69,f79])).
% 7.67/1.54  
% 7.67/1.54  fof(f81,plain,(
% 7.67/1.54    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.67/1.54    inference(definition_unfolding,[],[f68,f80])).
% 7.67/1.54  
% 7.67/1.54  fof(f82,plain,(
% 7.67/1.54    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.67/1.54    inference(definition_unfolding,[],[f67,f81])).
% 7.67/1.54  
% 7.67/1.54  fof(f92,plain,(
% 7.67/1.54    k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 7.67/1.54    inference(definition_unfolding,[],[f74,f76,f82,f82,f82])).
% 7.67/1.54  
% 7.67/1.54  fof(f4,axiom,(
% 7.67/1.54    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 7.67/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.54  
% 7.67/1.54  fof(f42,plain,(
% 7.67/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 7.67/1.54    inference(cnf_transformation,[],[f4])).
% 7.67/1.54  
% 7.67/1.54  fof(f85,plain,(
% 7.67/1.54    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0) )),
% 7.67/1.54    inference(definition_unfolding,[],[f42,f40,f76])).
% 7.67/1.54  
% 7.67/1.54  fof(f3,axiom,(
% 7.67/1.54    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 7.67/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.54  
% 7.67/1.54  fof(f41,plain,(
% 7.67/1.54    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 7.67/1.54    inference(cnf_transformation,[],[f3])).
% 7.67/1.54  
% 7.67/1.54  fof(f84,plain,(
% 7.67/1.54    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 7.67/1.54    inference(definition_unfolding,[],[f41,f76])).
% 7.67/1.54  
% 7.67/1.54  fof(f6,axiom,(
% 7.67/1.54    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.67/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.54  
% 7.67/1.54  fof(f44,plain,(
% 7.67/1.54    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.67/1.54    inference(cnf_transformation,[],[f6])).
% 7.67/1.54  
% 7.67/1.54  fof(f5,axiom,(
% 7.67/1.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.67/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.54  
% 7.67/1.54  fof(f43,plain,(
% 7.67/1.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.67/1.54    inference(cnf_transformation,[],[f5])).
% 7.67/1.54  
% 7.67/1.54  fof(f9,axiom,(
% 7.67/1.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> ~(X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)))),
% 7.67/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.54  
% 7.67/1.54  fof(f20,plain,(
% 7.67/1.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10)))),
% 7.67/1.54    inference(ennf_transformation,[],[f9])).
% 7.67/1.54  
% 7.67/1.54  fof(f23,plain,(
% 7.67/1.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) <=> ! [X10] : (r2_hidden(X10,X9) <=> sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 7.67/1.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 7.67/1.54  
% 7.67/1.54  fof(f22,plain,(
% 7.67/1.54    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10))),
% 7.67/1.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.67/1.54  
% 7.67/1.54  fof(f24,plain,(
% 7.67/1.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9))),
% 7.67/1.54    inference(definition_folding,[],[f20,f23,f22])).
% 7.67/1.54  
% 7.67/1.54  fof(f36,plain,(
% 7.67/1.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 7.67/1.54    inference(nnf_transformation,[],[f24])).
% 7.67/1.54  
% 7.67/1.54  fof(f64,plain,(
% 7.67/1.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 7.67/1.54    inference(cnf_transformation,[],[f36])).
% 7.67/1.54  
% 7.67/1.54  fof(f10,axiom,(
% 7.67/1.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 7.67/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.54  
% 7.67/1.54  fof(f66,plain,(
% 7.67/1.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 7.67/1.54    inference(cnf_transformation,[],[f10])).
% 7.67/1.54  
% 7.67/1.54  fof(f83,plain,(
% 7.67/1.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 7.67/1.54    inference(definition_unfolding,[],[f66,f76,f82])).
% 7.67/1.54  
% 7.67/1.54  fof(f91,plain,(
% 7.67/1.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) != X9) )),
% 7.67/1.54    inference(definition_unfolding,[],[f64,f83])).
% 7.67/1.54  
% 7.67/1.54  fof(f105,plain,(
% 7.67/1.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))))) )),
% 7.67/1.54    inference(equality_resolution,[],[f91])).
% 7.67/1.54  
% 7.67/1.54  fof(f29,plain,(
% 7.67/1.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 7.67/1.54    inference(nnf_transformation,[],[f23])).
% 7.67/1.54  
% 7.67/1.54  fof(f30,plain,(
% 7.67/1.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9)))) & (! [X11] : ((r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 7.67/1.54    inference(rectify,[],[f29])).
% 7.67/1.54  
% 7.67/1.54  fof(f31,plain,(
% 7.67/1.54    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9))) => ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9))))),
% 7.67/1.54    introduced(choice_axiom,[])).
% 7.67/1.54  
% 7.67/1.54  fof(f32,plain,(
% 7.67/1.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)))) & (! [X11] : ((r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 7.67/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 7.67/1.54  
% 7.67/1.54  fof(f51,plain,(
% 7.67/1.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 7.67/1.54    inference(cnf_transformation,[],[f32])).
% 7.67/1.54  
% 7.67/1.54  fof(f33,plain,(
% 7.67/1.54    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 7.67/1.54    inference(nnf_transformation,[],[f22])).
% 7.67/1.54  
% 7.67/1.54  fof(f34,plain,(
% 7.67/1.54    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 7.67/1.54    inference(flattening,[],[f33])).
% 7.67/1.54  
% 7.67/1.54  fof(f35,plain,(
% 7.67/1.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8 & X0 != X9)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | X0 = X9 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 7.67/1.54    inference(rectify,[],[f34])).
% 7.67/1.54  
% 7.67/1.54  fof(f63,plain,(
% 7.67/1.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | X0 != X1) )),
% 7.67/1.54    inference(cnf_transformation,[],[f35])).
% 7.67/1.54  
% 7.67/1.54  fof(f96,plain,(
% 7.67/1.54    ( ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 7.67/1.54    inference(equality_resolution,[],[f63])).
% 7.67/1.54  
% 7.67/1.54  fof(f8,axiom,(
% 7.67/1.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.67/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.54  
% 7.67/1.54  fof(f25,plain,(
% 7.67/1.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.67/1.54    inference(nnf_transformation,[],[f8])).
% 7.67/1.54  
% 7.67/1.54  fof(f26,plain,(
% 7.67/1.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.67/1.54    inference(rectify,[],[f25])).
% 7.67/1.54  
% 7.67/1.54  fof(f27,plain,(
% 7.67/1.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 7.67/1.54    introduced(choice_axiom,[])).
% 7.67/1.54  
% 7.67/1.54  fof(f28,plain,(
% 7.67/1.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.67/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 7.67/1.54  
% 7.67/1.54  fof(f46,plain,(
% 7.67/1.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.67/1.54    inference(cnf_transformation,[],[f28])).
% 7.67/1.54  
% 7.67/1.54  fof(f89,plain,(
% 7.67/1.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 7.67/1.54    inference(definition_unfolding,[],[f46,f82])).
% 7.67/1.54  
% 7.67/1.54  fof(f95,plain,(
% 7.67/1.54    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 7.67/1.54    inference(equality_resolution,[],[f89])).
% 7.67/1.54  
% 7.67/1.54  fof(f55,plain,(
% 7.67/1.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | X0 != X9) )),
% 7.67/1.54    inference(cnf_transformation,[],[f35])).
% 7.67/1.54  
% 7.67/1.54  fof(f104,plain,(
% 7.67/1.54    ( ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : (sP0(X9,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 7.67/1.54    inference(equality_resolution,[],[f55])).
% 7.67/1.54  
% 7.67/1.54  fof(f54,plain,(
% 7.67/1.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | X0 = X9 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 7.67/1.54    inference(cnf_transformation,[],[f35])).
% 7.67/1.54  
% 7.67/1.54  fof(f75,plain,(
% 7.67/1.54    sK4 != sK5),
% 7.67/1.54    inference(cnf_transformation,[],[f38])).
% 7.67/1.54  
% 7.67/1.54  cnf(c_0,plain,
% 7.67/1.54      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.67/1.54      inference(cnf_transformation,[],[f39]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_26,negated_conjecture,
% 7.67/1.54      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 7.67/1.54      inference(cnf_transformation,[],[f92]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1756,plain,
% 7.67/1.54      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 7.67/1.54      inference(demodulation,[status(thm)],[c_0,c_26]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_2,plain,
% 7.67/1.54      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
% 7.67/1.54      inference(cnf_transformation,[],[f85]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1,plain,
% 7.67/1.54      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 7.67/1.54      inference(cnf_transformation,[],[f84]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1380,plain,
% 7.67/1.54      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.67/1.54      inference(light_normalisation,[status(thm)],[c_2,c_1]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_4,plain,
% 7.67/1.54      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.67/1.54      inference(cnf_transformation,[],[f44]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1800,plain,
% 7.67/1.54      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_1380,c_4]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_2046,plain,
% 7.67/1.54      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_1756,c_1800]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_2045,plain,
% 7.67/1.54      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_1380,c_1800]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_3,plain,
% 7.67/1.54      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.67/1.54      inference(cnf_transformation,[],[f43]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_2061,plain,
% 7.67/1.54      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.67/1.54      inference(light_normalisation,[status(thm)],[c_2045,c_3]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_2079,plain,
% 7.67/1.54      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = k1_xboole_0 ),
% 7.67/1.54      inference(demodulation,[status(thm)],[c_2046,c_1380,c_2061]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_2432,plain,
% 7.67/1.54      ( k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = k1_xboole_0 ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_2079,c_2061]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1801,plain,
% 7.67/1.54      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))),X0)) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0) ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_1756,c_4]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_2417,plain,
% 7.67/1.54      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))),X0),X1)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0),X1) ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_1801,c_4]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_2900,plain,
% 7.67/1.54      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0),X1) ),
% 7.67/1.54      inference(light_normalisation,
% 7.67/1.54                [status(thm)],
% 7.67/1.54                [c_2417,c_2061,c_2417,c_2432]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1805,plain,
% 7.67/1.54      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_4,c_1380]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_2916,plain,
% 7.67/1.54      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0),k5_xboole_0(X1,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_2900,c_1805]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_3369,plain,
% 7.67/1.54      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(X0,X1))),X2)) = k5_xboole_0(k1_xboole_0,X2) ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_2916,c_4]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_3374,plain,
% 7.67/1.54      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(X0,X1))),X2)) = X2 ),
% 7.67/1.54      inference(demodulation,[status(thm)],[c_3369,c_2061,c_2900]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_5714,plain,
% 7.67/1.54      ( k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X1),k1_xboole_0) ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_1380,c_3374]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_5809,plain,
% 7.67/1.54      ( k5_xboole_0(X0,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(X1,X0))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X1) ),
% 7.67/1.54      inference(demodulation,[status(thm)],[c_5714,c_3,c_2900]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_5818,plain,
% 7.67/1.54      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0),X1)) = X1 ),
% 7.67/1.54      inference(demodulation,[status(thm)],[c_5809,c_3374]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_5824,plain,
% 7.67/1.54      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(X0,X1))) = X1 ),
% 7.67/1.54      inference(light_normalisation,[status(thm)],[c_5818,c_2900]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_6712,plain,
% 7.67/1.54      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_xboole_0)) = k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_2432,c_5824]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_2412,plain,
% 7.67/1.54      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),X0))) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0) ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_4,c_1801]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_6209,plain,
% 7.67/1.54      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),X0),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0)) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_2412,c_5809]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_3356,plain,
% 7.67/1.54      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),X0),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0))) = k1_xboole_0 ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_2412,c_2916]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_6222,plain,
% 7.67/1.54      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),X0),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0)),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_xboole_0)) = k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_3356,c_5809]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_2906,plain,
% 7.67/1.54      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_1380,c_2900]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_2926,plain,
% 7.67/1.54      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0)) = X0 ),
% 7.67/1.54      inference(light_normalisation,[status(thm)],[c_2906,c_2061]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_6260,plain,
% 7.67/1.54      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),X0),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 7.67/1.54      inference(demodulation,[status(thm)],[c_6222,c_3,c_2926]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_6275,plain,
% 7.67/1.54      ( k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 7.67/1.54      inference(demodulation,[status(thm)],[c_6209,c_6260]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_6751,plain,
% 7.67/1.54      ( k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 7.67/1.54      inference(demodulation,[status(thm)],[c_6712,c_3,c_2900,c_6275]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_24,plain,
% 7.67/1.54      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) ),
% 7.67/1.54      inference(cnf_transformation,[],[f105]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1360,plain,
% 7.67/1.54      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) = iProver_top ),
% 7.67/1.54      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1943,plain,
% 7.67/1.54      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))))) = iProver_top ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_0,c_1360]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_16567,plain,
% 7.67/1.54      ( sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5,k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = iProver_top ),
% 7.67/1.54      inference(superposition,[status(thm)],[c_6751,c_1943]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_16569,plain,
% 7.67/1.54      ( sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 7.67/1.54      inference(demodulation,[status(thm)],[c_16567,c_3,c_1380]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_11,plain,
% 7.67/1.54      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
% 7.67/1.54      | ~ sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10)
% 7.67/1.54      | r2_hidden(X0,X10) ),
% 7.67/1.54      inference(cnf_transformation,[],[f51]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1530,plain,
% 7.67/1.54      ( ~ sP0(sK5,X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 7.67/1.54      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X0,k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9))
% 7.67/1.54      | r2_hidden(sK5,k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9)) ),
% 7.67/1.54      inference(instantiation,[status(thm)],[c_11]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1885,plain,
% 7.67/1.54      ( ~ sP0(sK5,sK5,X0,sK4,X1,X2,X3,X4,X5,X6)
% 7.67/1.54      | ~ sP1(X6,X5,X4,X3,X2,X1,sK4,X0,sK5,k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7))
% 7.67/1.54      | r2_hidden(sK5,k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)) ),
% 7.67/1.54      inference(instantiation,[status(thm)],[c_1530]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1886,plain,
% 7.67/1.54      ( sP0(sK5,sK5,X0,sK4,X1,X2,X3,X4,X5,X6) != iProver_top
% 7.67/1.54      | sP1(X6,X5,X4,X3,X2,X1,sK4,X0,sK5,k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)) != iProver_top
% 7.67/1.54      | r2_hidden(sK5,k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)) = iProver_top ),
% 7.67/1.54      inference(predicate_to_equality,[status(thm)],[c_1885]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1888,plain,
% 7.67/1.54      ( sP0(sK5,sK5,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != iProver_top
% 7.67/1.54      | sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
% 7.67/1.54      | r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 7.67/1.54      inference(instantiation,[status(thm)],[c_1886]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_13,plain,
% 7.67/1.54      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
% 7.67/1.54      inference(cnf_transformation,[],[f96]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1541,plain,
% 7.67/1.54      ( sP0(sK5,sK5,X0,sK4,X1,X2,X3,X4,X5,X6) ),
% 7.67/1.54      inference(instantiation,[status(thm)],[c_13]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1542,plain,
% 7.67/1.54      ( sP0(sK5,sK5,X0,sK4,X1,X2,X3,X4,X5,X6) = iProver_top ),
% 7.67/1.54      inference(predicate_to_equality,[status(thm)],[c_1541]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1544,plain,
% 7.67/1.54      ( sP0(sK5,sK5,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = iProver_top ),
% 7.67/1.54      inference(instantiation,[status(thm)],[c_1542]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_8,plain,
% 7.67/1.54      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 7.67/1.54      inference(cnf_transformation,[],[f95]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1427,plain,
% 7.67/1.54      ( ~ r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 7.67/1.54      | sK5 = X0 ),
% 7.67/1.54      inference(instantiation,[status(thm)],[c_8]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1428,plain,
% 7.67/1.54      ( sK5 = X0
% 7.67/1.54      | r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 7.67/1.54      inference(predicate_to_equality,[status(thm)],[c_1427]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1430,plain,
% 7.67/1.54      ( sK5 = sK4
% 7.67/1.54      | r2_hidden(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
% 7.67/1.54      inference(instantiation,[status(thm)],[c_1428]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1046,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1410,plain,
% 7.67/1.54      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 7.67/1.54      inference(instantiation,[status(thm)],[c_1046]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_1411,plain,
% 7.67/1.54      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 7.67/1.54      inference(instantiation,[status(thm)],[c_1410]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_21,plain,
% 7.67/1.54      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X0) ),
% 7.67/1.54      inference(cnf_transformation,[],[f104]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_37,plain,
% 7.67/1.54      ( sP0(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 7.67/1.54      inference(instantiation,[status(thm)],[c_21]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_22,plain,
% 7.67/1.54      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
% 7.67/1.54      | X3 = X0
% 7.67/1.54      | X9 = X0
% 7.67/1.54      | X8 = X0
% 7.67/1.54      | X7 = X0
% 7.67/1.54      | X6 = X0
% 7.67/1.54      | X5 = X0
% 7.67/1.54      | X4 = X0
% 7.67/1.54      | X2 = X0
% 7.67/1.54      | X1 = X0 ),
% 7.67/1.54      inference(cnf_transformation,[],[f54]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_34,plain,
% 7.67/1.54      ( ~ sP0(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | sK4 = sK4 ),
% 7.67/1.54      inference(instantiation,[status(thm)],[c_22]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(c_25,negated_conjecture,
% 7.67/1.54      ( sK4 != sK5 ),
% 7.67/1.54      inference(cnf_transformation,[],[f75]) ).
% 7.67/1.54  
% 7.67/1.54  cnf(contradiction,plain,
% 7.67/1.54      ( $false ),
% 7.67/1.54      inference(minisat,
% 7.67/1.54                [status(thm)],
% 7.67/1.54                [c_16569,c_1888,c_1544,c_1430,c_1411,c_37,c_34,c_25]) ).
% 7.67/1.54  
% 7.67/1.54  
% 7.67/1.54  % SZS output end CNFRefutation for theBenchmark.p
% 7.67/1.54  
% 7.67/1.54  ------                               Statistics
% 7.67/1.54  
% 7.67/1.54  ------ General
% 7.67/1.54  
% 7.67/1.54  abstr_ref_over_cycles:                  0
% 7.67/1.54  abstr_ref_under_cycles:                 0
% 7.67/1.54  gc_basic_clause_elim:                   0
% 7.67/1.54  forced_gc_time:                         0
% 7.67/1.54  parsing_time:                           0.008
% 7.67/1.54  unif_index_cands_time:                  0.
% 7.67/1.54  unif_index_add_time:                    0.
% 7.67/1.54  orderings_time:                         0.
% 7.67/1.54  out_proof_time:                         0.011
% 7.67/1.54  total_time:                             0.724
% 7.67/1.54  num_of_symbols:                         42
% 7.67/1.54  num_of_terms:                           31844
% 7.67/1.54  
% 7.67/1.54  ------ Preprocessing
% 7.67/1.54  
% 7.67/1.54  num_of_splits:                          0
% 7.67/1.54  num_of_split_atoms:                     0
% 7.67/1.54  num_of_reused_defs:                     0
% 7.67/1.54  num_eq_ax_congr_red:                    60
% 7.67/1.54  num_of_sem_filtered_clauses:            1
% 7.67/1.54  num_of_subtypes:                        0
% 7.67/1.54  monotx_restored_types:                  0
% 7.67/1.54  sat_num_of_epr_types:                   0
% 7.67/1.54  sat_num_of_non_cyclic_types:            0
% 7.67/1.54  sat_guarded_non_collapsed_types:        0
% 7.67/1.54  num_pure_diseq_elim:                    0
% 7.67/1.54  simp_replaced_by:                       0
% 7.67/1.54  res_preprocessed:                       98
% 7.67/1.54  prep_upred:                             0
% 7.67/1.54  prep_unflattend:                        382
% 7.67/1.54  smt_new_axioms:                         0
% 7.67/1.54  pred_elim_cands:                        3
% 7.67/1.54  pred_elim:                              0
% 7.67/1.54  pred_elim_cl:                           0
% 7.67/1.54  pred_elim_cycles:                       3
% 7.67/1.54  merged_defs:                            0
% 7.67/1.54  merged_defs_ncl:                        0
% 7.67/1.54  bin_hyper_res:                          0
% 7.67/1.54  prep_cycles:                            3
% 7.67/1.54  pred_elim_time:                         0.021
% 7.67/1.54  splitting_time:                         0.
% 7.67/1.54  sem_filter_time:                        0.
% 7.67/1.54  monotx_time:                            0.003
% 7.67/1.54  subtype_inf_time:                       0.
% 7.67/1.54  
% 7.67/1.54  ------ Problem properties
% 7.67/1.54  
% 7.67/1.54  clauses:                                27
% 7.67/1.54  conjectures:                            2
% 7.67/1.54  epr:                                    13
% 7.67/1.54  horn:                                   24
% 7.67/1.54  ground:                                 2
% 7.67/1.54  unary:                                  18
% 7.67/1.54  binary:                                 2
% 7.67/1.54  lits:                                   50
% 7.67/1.54  lits_eq:                                22
% 7.67/1.54  fd_pure:                                0
% 7.67/1.54  fd_pseudo:                              0
% 7.67/1.54  fd_cond:                                0
% 7.67/1.54  fd_pseudo_cond:                         4
% 7.67/1.54  ac_symbols:                             1
% 7.67/1.54  
% 7.67/1.54  ------ Propositional Solver
% 7.67/1.54  
% 7.67/1.54  prop_solver_calls:                      27
% 7.67/1.54  prop_fast_solver_calls:                 692
% 7.67/1.54  smt_solver_calls:                       0
% 7.67/1.54  smt_fast_solver_calls:                  0
% 7.67/1.54  prop_num_of_clauses:                    5952
% 7.67/1.54  prop_preprocess_simplified:             12567
% 7.67/1.54  prop_fo_subsumed:                       0
% 7.67/1.54  prop_solver_time:                       0.
% 7.67/1.54  smt_solver_time:                        0.
% 7.67/1.54  smt_fast_solver_time:                   0.
% 7.67/1.54  prop_fast_solver_time:                  0.
% 7.67/1.54  prop_unsat_core_time:                   0.
% 7.67/1.54  
% 7.67/1.54  ------ QBF
% 7.67/1.54  
% 7.67/1.54  qbf_q_res:                              0
% 7.67/1.54  qbf_num_tautologies:                    0
% 7.67/1.54  qbf_prep_cycles:                        0
% 7.67/1.54  
% 7.67/1.54  ------ BMC1
% 7.67/1.54  
% 7.67/1.54  bmc1_current_bound:                     -1
% 7.67/1.54  bmc1_last_solved_bound:                 -1
% 7.67/1.54  bmc1_unsat_core_size:                   -1
% 7.67/1.54  bmc1_unsat_core_parents_size:           -1
% 7.67/1.54  bmc1_merge_next_fun:                    0
% 7.67/1.54  bmc1_unsat_core_clauses_time:           0.
% 7.67/1.54  
% 7.67/1.54  ------ Instantiation
% 7.67/1.54  
% 7.67/1.54  inst_num_of_clauses:                    1564
% 7.67/1.54  inst_num_in_passive:                    437
% 7.67/1.54  inst_num_in_active:                     369
% 7.67/1.54  inst_num_in_unprocessed:                758
% 7.67/1.54  inst_num_of_loops:                      410
% 7.67/1.54  inst_num_of_learning_restarts:          0
% 7.67/1.54  inst_num_moves_active_passive:          39
% 7.67/1.54  inst_lit_activity:                      0
% 7.67/1.54  inst_lit_activity_moves:                0
% 7.67/1.54  inst_num_tautologies:                   0
% 7.67/1.54  inst_num_prop_implied:                  0
% 7.67/1.54  inst_num_existing_simplified:           0
% 7.67/1.54  inst_num_eq_res_simplified:             0
% 7.67/1.54  inst_num_child_elim:                    0
% 7.67/1.54  inst_num_of_dismatching_blockings:      1212
% 7.67/1.54  inst_num_of_non_proper_insts:           1660
% 7.67/1.54  inst_num_of_duplicates:                 0
% 7.67/1.54  inst_inst_num_from_inst_to_res:         0
% 7.67/1.54  inst_dismatching_checking_time:         0.
% 7.67/1.54  
% 7.67/1.54  ------ Resolution
% 7.67/1.54  
% 7.67/1.54  res_num_of_clauses:                     0
% 7.67/1.54  res_num_in_passive:                     0
% 7.67/1.54  res_num_in_active:                      0
% 7.67/1.54  res_num_of_loops:                       101
% 7.67/1.54  res_forward_subset_subsumed:            236
% 7.67/1.54  res_backward_subset_subsumed:           0
% 7.67/1.54  res_forward_subsumed:                   0
% 7.67/1.54  res_backward_subsumed:                  0
% 7.67/1.54  res_forward_subsumption_resolution:     0
% 7.67/1.54  res_backward_subsumption_resolution:    0
% 7.67/1.54  res_clause_to_clause_subsumption:       6031
% 7.67/1.54  res_orphan_elimination:                 0
% 7.67/1.54  res_tautology_del:                      184
% 7.67/1.54  res_num_eq_res_simplified:              0
% 7.67/1.54  res_num_sel_changes:                    0
% 7.67/1.54  res_moves_from_active_to_pass:          0
% 7.67/1.54  
% 7.67/1.54  ------ Superposition
% 7.67/1.54  
% 7.67/1.54  sup_time_total:                         0.
% 7.67/1.54  sup_time_generating:                    0.
% 7.67/1.54  sup_time_sim_full:                      0.
% 7.67/1.54  sup_time_sim_immed:                     0.
% 7.67/1.54  
% 7.67/1.54  sup_num_of_clauses:                     586
% 7.67/1.54  sup_num_in_active:                      57
% 7.67/1.54  sup_num_in_passive:                     529
% 7.67/1.54  sup_num_of_loops:                       81
% 7.67/1.54  sup_fw_superposition:                   1378
% 7.67/1.54  sup_bw_superposition:                   794
% 7.67/1.54  sup_immediate_simplified:               1382
% 7.67/1.54  sup_given_eliminated:                   8
% 7.67/1.54  comparisons_done:                       0
% 7.67/1.54  comparisons_avoided:                    2
% 7.67/1.54  
% 7.67/1.54  ------ Simplifications
% 7.67/1.54  
% 7.67/1.54  
% 7.67/1.54  sim_fw_subset_subsumed:                 0
% 7.67/1.54  sim_bw_subset_subsumed:                 0
% 7.67/1.54  sim_fw_subsumed:                        128
% 7.67/1.54  sim_bw_subsumed:                        38
% 7.67/1.54  sim_fw_subsumption_res:                 0
% 7.67/1.54  sim_bw_subsumption_res:                 0
% 7.67/1.54  sim_tautology_del:                      0
% 7.67/1.54  sim_eq_tautology_del:                   451
% 7.67/1.54  sim_eq_res_simp:                        0
% 7.67/1.54  sim_fw_demodulated:                     1409
% 7.67/1.54  sim_bw_demodulated:                     77
% 7.67/1.54  sim_light_normalised:                   476
% 7.67/1.54  sim_joinable_taut:                      18
% 7.67/1.54  sim_joinable_simp:                      0
% 7.67/1.54  sim_ac_normalised:                      0
% 7.67/1.54  sim_smt_subsumption:                    0
% 7.67/1.54  
%------------------------------------------------------------------------------
