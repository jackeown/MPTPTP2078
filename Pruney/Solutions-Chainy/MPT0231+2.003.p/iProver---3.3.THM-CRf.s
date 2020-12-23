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
% DateTime   : Thu Dec  3 11:31:03 EST 2020

% Result     : Theorem 55.09s
% Output     : CNFRefutation 55.09s
% Verified   : 
% Statistics : Number of formulae       :  164 (8060 expanded)
%              Number of clauses        :   87 (1394 expanded)
%              Number of leaves         :   23 (2413 expanded)
%              Depth                    :   26
%              Number of atoms          :  379 (9616 expanded)
%              Number of equality atoms :  251 (7994 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal clause size      :   22 (   1 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( sK4 != sK6
      & r1_tarski(k2_tarski(sK4,sK5),k1_tarski(sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( sK4 != sK6
    & r1_tarski(k2_tarski(sK4,sK5),k1_tarski(sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f23,f39])).

fof(f77,plain,(
    r1_tarski(k2_tarski(sK4,sK5),k1_tarski(sK6)) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f73,f74])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f72,f79])).

fof(f81,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f75,f80])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f71,f81])).

fof(f95,plain,(
    r1_tarski(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(definition_unfolding,[],[f77,f81,f82])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f7])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f11])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f70,f82])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(definition_unfolding,[],[f66,f82,f83])).

fof(f92,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) ),
    inference(definition_unfolding,[],[f67,f81,f84])).

fof(f17,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f94,plain,(
    ! [X0,X1] : r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f76,f82,f81])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10
    <=> ! [X11] :
          ( r2_hidden(X11,X10)
        <=> ~ ( X9 != X11
              & X8 != X11
              & X7 != X11
              & X6 != X11
              & X5 != X11
              & X4 != X11
              & X3 != X11
              & X2 != X11
              & X1 != X11
              & X0 != X11 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10
    <=> ! [X11] :
          ( r2_hidden(X11,X10)
        <=> ( X9 = X11
            | X8 = X11
            | X7 = X11
            | X6 = X11
            | X5 = X11
            | X4 = X11
            | X3 = X11
            | X2 = X11
            | X1 = X11
            | X0 = X11 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
    <=> ! [X11] :
          ( r2_hidden(X11,X10)
        <=> sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f24,plain,(
    ! [X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X9 = X11
        | X8 = X11
        | X7 = X11
        | X6 = X11
        | X5 = X11
        | X4 = X11
        | X3 = X11
        | X2 = X11
        | X1 = X11
        | X0 = X11 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) ) ),
    inference(definition_folding,[],[f22,f25,f24])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( ( k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
        | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
      | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : k2_xboole_0(k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) = k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : k2_xboole_0(k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) = k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(cnf_transformation,[],[f10])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),k5_enumset1(X9,X9,X9,X9,X9,X9,X9)) = k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(definition_unfolding,[],[f69,f84,f82])).

fof(f91,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
      | k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),k5_enumset1(X9,X9,X9,X9,X9,X9,X9)) != X10 ) ),
    inference(definition_unfolding,[],[f64,f85])).

fof(f109,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),k5_enumset1(X9,X9,X9,X9,X9,X9,X9))) ),
    inference(equality_resolution,[],[f91])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f9])).

fof(f93,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)),k5_enumset1(X8,X8,X8,X8,X8,X8,X8)) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) ),
    inference(definition_unfolding,[],[f68,f83,f82,f84])).

fof(f35,plain,(
    ! [X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X9 != X11
          & X8 != X11
          & X7 != X11
          & X6 != X11
          & X5 != X11
          & X4 != X11
          & X3 != X11
          & X2 != X11
          & X1 != X11
          & X0 != X11 ) )
      & ( X9 = X11
        | X8 = X11
        | X7 = X11
        | X6 = X11
        | X5 = X11
        | X4 = X11
        | X3 = X11
        | X2 = X11
        | X1 = X11
        | X0 = X11
        | ~ sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f36,plain,(
    ! [X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X9 != X11
          & X8 != X11
          & X7 != X11
          & X6 != X11
          & X5 != X11
          & X4 != X11
          & X3 != X11
          & X2 != X11
          & X1 != X11
          & X0 != X11 ) )
      & ( X9 = X11
        | X8 = X11
        | X7 = X11
        | X6 = X11
        | X5 = X11
        | X4 = X11
        | X3 = X11
        | X2 = X11
        | X1 = X11
        | X0 = X11
        | ~ sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8
          & X0 != X9
          & X0 != X10 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | X0 = X9
        | X0 = X10
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) ) ) ),
    inference(rectify,[],[f36])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f99,plain,(
    ! [X6,X4,X2,X10,X8,X7,X5,X3,X1,X9] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) ),
    inference(equality_resolution,[],[f63])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
        | ? [X11] :
            ( ( ~ sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X11,X10) )
            & ( sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X11,X10) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X10)
              | ~ sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X11,X10) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
        | ? [X11] :
            ( ( ~ sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X11,X10) )
            & ( sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X11,X10) ) ) )
      & ( ! [X12] :
            ( ( r2_hidden(X12,X10)
              | ~ sP0(X12,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X12,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X12,X10) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X10,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X11] :
          ( ( ~ sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X11,X10) )
          & ( sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X11,X10) ) )
     => ( ( ~ sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10) )
        & ( sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
        | ( ( ~ sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10) )
          & ( sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10) ) ) )
      & ( ! [X12] :
            ( ( r2_hidden(X12,X10)
              | ~ sP0(X12,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X12,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X12,X10) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X12,X10,X8,X7,X5,X3,X1,X9] :
      ( r2_hidden(X12,X10)
      | ~ sP0(X12,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f45,f82])).

fof(f98,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f78,plain,(
    sK4 != sK6 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_29,negated_conjecture,
    ( r1_tarski(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1538,plain,
    ( r1_tarski(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1561,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2495,plain,
    ( k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
    inference(superposition,[status(thm)],[c_1538,c_1561])).

cnf(c_3,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2649,plain,
    ( k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X0)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X0) ),
    inference(superposition,[status(thm)],[c_2495,c_3])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1593,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_3313,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5))) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X0) ),
    inference(superposition,[status(thm)],[c_2649,c_1593])).

cnf(c_1594,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_2651,plain,
    ( k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X0)) = k2_xboole_0(X0,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(superposition,[status(thm)],[c_2495,c_1594])).

cnf(c_4657,plain,
    ( k2_xboole_0(k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6))) ),
    inference(superposition,[status(thm)],[c_3313,c_2651])).

cnf(c_2652,plain,
    ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),X0)) = k2_xboole_0(X0,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(superposition,[status(thm)],[c_2495,c_1593])).

cnf(c_4660,plain,
    ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5))) = k2_xboole_0(k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(superposition,[status(thm)],[c_3313,c_2652])).

cnf(c_4661,plain,
    ( k2_xboole_0(k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(demodulation,[status(thm)],[c_4660,c_3313])).

cnf(c_25,plain,
    ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1131,plain,
    ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) = k2_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(theory_normalisation,[status(thm)],[c_25,c_3,c_0])).

cnf(c_2476,plain,
    ( k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)),k5_enumset1(X8,X8,X8,X8,X8,X8,X8)) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X8,X8,X8,X8,X8,X8,X0)) ),
    inference(superposition,[status(thm)],[c_1131,c_0])).

cnf(c_4662,plain,
    ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
    inference(demodulation,[status(thm)],[c_4661,c_2476,c_2495])).

cnf(c_4664,plain,
    ( k2_xboole_0(k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(demodulation,[status(thm)],[c_4657,c_4662])).

cnf(c_4665,plain,
    ( k2_xboole_0(k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
    inference(light_normalisation,[status(thm)],[c_4664,c_2495])).

cnf(c_5720,plain,
    ( k2_xboole_0(k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X0)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X0) ),
    inference(superposition,[status(thm)],[c_4665,c_3])).

cnf(c_5724,plain,
    ( k2_xboole_0(k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X0)) = k2_xboole_0(X0,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(superposition,[status(thm)],[c_4665,c_1594])).

cnf(c_5698,plain,
    ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X0)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X0) ),
    inference(superposition,[status(thm)],[c_4662,c_3])).

cnf(c_3297,plain,
    ( k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k2_xboole_0(X0,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6))) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X0) ),
    inference(superposition,[status(thm)],[c_0,c_2649])).

cnf(c_5730,plain,
    ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5))) = k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(superposition,[status(thm)],[c_4665,c_3297])).

cnf(c_5732,plain,
    ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5))) = k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
    inference(light_normalisation,[status(thm)],[c_5730,c_2495])).

cnf(c_6172,plain,
    ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
    inference(superposition,[status(thm)],[c_5698,c_5732])).

cnf(c_27,plain,
    ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1539,plain,
    ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1134,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X1,X2)) ),
    inference(theory_normalisation,[status(thm)],[c_1,c_3,c_0])).

cnf(c_1562,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1134])).

cnf(c_7585,plain,
    ( r1_tarski(X0,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top
    | r1_tarski(X0,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2495,c_1562])).

cnf(c_8189,plain,
    ( r1_tarski(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1539,c_7585])).

cnf(c_8245,plain,
    ( k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
    inference(superposition,[status(thm)],[c_8189,c_1561])).

cnf(c_1592,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_5704,plain,
    ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k2_xboole_0(X0,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6))) = k2_xboole_0(X0,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(superposition,[status(thm)],[c_4662,c_1592])).

cnf(c_6358,plain,
    ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0)) ),
    inference(superposition,[status(thm)],[c_5704,c_1131])).

cnf(c_4675,plain,
    ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_1539,c_1561])).

cnf(c_6369,plain,
    ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0) ),
    inference(demodulation,[status(thm)],[c_6358,c_4675])).

cnf(c_8246,plain,
    ( k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4) = k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
    inference(demodulation,[status(thm)],[c_8245,c_6369])).

cnf(c_19180,plain,
    ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4),X0)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4),X0) ),
    inference(light_normalisation,[status(thm)],[c_5720,c_5724,c_6172,c_8246])).

cnf(c_2477,plain,
    ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)),X9)) = k2_xboole_0(X9,k2_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_1131,c_1594])).

cnf(c_17172,plain,
    ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X1)) = k2_xboole_0(X1,k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(X0,X0,X0,X0,X0,X0,sK6))) ),
    inference(superposition,[status(thm)],[c_6172,c_2477])).

cnf(c_5703,plain,
    ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(X0,X0,X0,X0,X0,X0,sK6)) ),
    inference(superposition,[status(thm)],[c_4662,c_1131])).

cnf(c_14688,plain,
    ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(X0,X0,X0,X0,X0,X0,sK6)) ),
    inference(superposition,[status(thm)],[c_4662,c_2476])).

cnf(c_4651,plain,
    ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(X0,X0,X0,X0,X0,X0,sK6)) ),
    inference(superposition,[status(thm)],[c_3313,c_1131])).

cnf(c_14747,plain,
    ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4),k5_enumset1(X0,X0,X0,X0,X0,X0,sK6)) = k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(X0,X0,X0,X0,X0,X0,sK6)) ),
    inference(light_normalisation,[status(thm)],[c_14688,c_4651,c_8246])).

cnf(c_17044,plain,
    ( k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(X0,X0,X0,X0,X0,X0,sK6)) = k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0) ),
    inference(light_normalisation,[status(thm)],[c_5703,c_6369,c_8246,c_14747])).

cnf(c_17304,plain,
    ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4),X1)) = k2_xboole_0(X1,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0)) ),
    inference(light_normalisation,[status(thm)],[c_17172,c_8246,c_17044])).

cnf(c_19181,plain,
    ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4),X0)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4),X0) ),
    inference(demodulation,[status(thm)],[c_19180,c_8246,c_17304])).

cnf(c_24,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),k5_enumset1(X9,X9,X9,X9,X9,X9,X9))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1132,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k2_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k5_enumset1(X9,X9,X9,X9,X9,X9,X9))))) ),
    inference(theory_normalisation,[status(thm)],[c_24,c_3,c_0])).

cnf(c_1540,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k2_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k5_enumset1(X9,X9,X9,X9,X9,X9,X9))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1132])).

cnf(c_2471,plain,
    ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X8,X8,X8,X8,X8,X8,X8))) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X0,X0,X8)) ),
    inference(superposition,[status(thm)],[c_0,c_1131])).

cnf(c_6427,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X1,X1,X9)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1540,c_2471])).

cnf(c_6433,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,k2_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X9),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1594,c_6427])).

cnf(c_117869,plain,
    ( sP1(X0,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK4,sK4,k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_19181,c_6433])).

cnf(c_26,plain,
    ( k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)),k5_enumset1(X8,X8,X8,X8,X8,X8,X8)) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1130,plain,
    ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X8,X8,X8,X8,X8,X8,X8))) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) ),
    inference(theory_normalisation,[status(thm)],[c_26,c_3,c_0])).

cnf(c_1563,plain,
    ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X8,X8,X8,X8,X8,X8,X8))) = k2_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_1130,c_1131])).

cnf(c_5699,plain,
    ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X0)) = k2_xboole_0(X0,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(superposition,[status(thm)],[c_4662,c_1593])).

cnf(c_8646,plain,
    ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(superposition,[status(thm)],[c_1563,c_5699])).

cnf(c_8654,plain,
    ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4)) = k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0) ),
    inference(light_normalisation,[status(thm)],[c_8646,c_6369,c_8246])).

cnf(c_8647,plain,
    ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(superposition,[status(thm)],[c_1563,c_5698])).

cnf(c_8653,plain,
    ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_8647,c_4651,c_8246])).

cnf(c_8655,plain,
    ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0) ),
    inference(demodulation,[status(thm)],[c_8654,c_8653])).

cnf(c_117877,plain,
    ( sP1(X0,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK4,sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_117869,c_8655])).

cnf(c_117891,plain,
    ( sP1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK4,sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_117877])).

cnf(c_12,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1756,plain,
    ( sP0(sK4,sK4,X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2661,plain,
    ( sP0(sK4,sK4,sK4,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(instantiation,[status(thm)],[c_1756])).

cnf(c_2662,plain,
    ( sP0(sK4,sK4,sK4,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2661])).

cnf(c_2664,plain,
    ( sP0(sK4,sK4,sK4,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2662])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
    | ~ sP1(X10,X9,X8,X7,X6,X5,X4,X3,X2,X1,X11)
    | r2_hidden(X0,X11) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1604,plain,
    ( ~ sP0(sK4,X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
    | ~ sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X0,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | r2_hidden(sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1640,plain,
    ( ~ sP0(sK4,sK4,X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X0,sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | r2_hidden(sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_1604])).

cnf(c_1761,plain,
    ( ~ sP0(sK4,sK4,sK4,X0,X1,X2,X3,X4,X5,X6,X7)
    | ~ sP1(X7,X6,X5,X4,X3,X2,X1,X0,sK4,sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | r2_hidden(sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_1640])).

cnf(c_1762,plain,
    ( sP0(sK4,sK4,sK4,X0,X1,X2,X3,X4,X5,X6,X7) != iProver_top
    | sP1(X7,X6,X5,X4,X3,X2,X1,X0,sK4,sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
    | r2_hidden(sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1761])).

cnf(c_1764,plain,
    ( sP0(sK4,sK4,sK4,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != iProver_top
    | sP1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK4,sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
    | r2_hidden(sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1762])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1600,plain,
    ( ~ r2_hidden(sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | sK4 = sK6 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1601,plain,
    ( sK4 = sK6
    | r2_hidden(sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1600])).

cnf(c_28,negated_conjecture,
    ( sK4 != sK6 ),
    inference(cnf_transformation,[],[f78])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_117891,c_2664,c_1764,c_1601,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:14:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 55.09/7.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 55.09/7.51  
% 55.09/7.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.09/7.51  
% 55.09/7.51  ------  iProver source info
% 55.09/7.51  
% 55.09/7.51  git: date: 2020-06-30 10:37:57 +0100
% 55.09/7.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.09/7.51  git: non_committed_changes: false
% 55.09/7.51  git: last_make_outside_of_git: false
% 55.09/7.51  
% 55.09/7.51  ------ 
% 55.09/7.51  
% 55.09/7.51  ------ Input Options
% 55.09/7.51  
% 55.09/7.51  --out_options                           all
% 55.09/7.51  --tptp_safe_out                         true
% 55.09/7.51  --problem_path                          ""
% 55.09/7.51  --include_path                          ""
% 55.09/7.51  --clausifier                            res/vclausify_rel
% 55.09/7.51  --clausifier_options                    ""
% 55.09/7.51  --stdin                                 false
% 55.09/7.51  --stats_out                             all
% 55.09/7.51  
% 55.09/7.51  ------ General Options
% 55.09/7.51  
% 55.09/7.51  --fof                                   false
% 55.09/7.51  --time_out_real                         305.
% 55.09/7.51  --time_out_virtual                      -1.
% 55.09/7.51  --symbol_type_check                     false
% 55.09/7.51  --clausify_out                          false
% 55.09/7.51  --sig_cnt_out                           false
% 55.09/7.51  --trig_cnt_out                          false
% 55.09/7.51  --trig_cnt_out_tolerance                1.
% 55.09/7.51  --trig_cnt_out_sk_spl                   false
% 55.09/7.51  --abstr_cl_out                          false
% 55.09/7.51  
% 55.09/7.51  ------ Global Options
% 55.09/7.51  
% 55.09/7.51  --schedule                              default
% 55.09/7.51  --add_important_lit                     false
% 55.09/7.51  --prop_solver_per_cl                    1000
% 55.09/7.51  --min_unsat_core                        false
% 55.09/7.51  --soft_assumptions                      false
% 55.09/7.51  --soft_lemma_size                       3
% 55.09/7.51  --prop_impl_unit_size                   0
% 55.09/7.51  --prop_impl_unit                        []
% 55.09/7.51  --share_sel_clauses                     true
% 55.09/7.51  --reset_solvers                         false
% 55.09/7.51  --bc_imp_inh                            [conj_cone]
% 55.09/7.51  --conj_cone_tolerance                   3.
% 55.09/7.51  --extra_neg_conj                        none
% 55.09/7.51  --large_theory_mode                     true
% 55.09/7.51  --prolific_symb_bound                   200
% 55.09/7.51  --lt_threshold                          2000
% 55.09/7.51  --clause_weak_htbl                      true
% 55.09/7.51  --gc_record_bc_elim                     false
% 55.09/7.51  
% 55.09/7.51  ------ Preprocessing Options
% 55.09/7.51  
% 55.09/7.51  --preprocessing_flag                    true
% 55.09/7.51  --time_out_prep_mult                    0.1
% 55.09/7.51  --splitting_mode                        input
% 55.09/7.51  --splitting_grd                         true
% 55.09/7.51  --splitting_cvd                         false
% 55.09/7.51  --splitting_cvd_svl                     false
% 55.09/7.51  --splitting_nvd                         32
% 55.09/7.51  --sub_typing                            true
% 55.09/7.51  --prep_gs_sim                           true
% 55.09/7.51  --prep_unflatten                        true
% 55.09/7.51  --prep_res_sim                          true
% 55.09/7.51  --prep_upred                            true
% 55.09/7.51  --prep_sem_filter                       exhaustive
% 55.09/7.51  --prep_sem_filter_out                   false
% 55.09/7.51  --pred_elim                             true
% 55.09/7.51  --res_sim_input                         true
% 55.09/7.51  --eq_ax_congr_red                       true
% 55.09/7.51  --pure_diseq_elim                       true
% 55.09/7.51  --brand_transform                       false
% 55.09/7.51  --non_eq_to_eq                          false
% 55.09/7.51  --prep_def_merge                        true
% 55.09/7.51  --prep_def_merge_prop_impl              false
% 55.09/7.51  --prep_def_merge_mbd                    true
% 55.09/7.51  --prep_def_merge_tr_red                 false
% 55.09/7.51  --prep_def_merge_tr_cl                  false
% 55.09/7.51  --smt_preprocessing                     true
% 55.09/7.51  --smt_ac_axioms                         fast
% 55.09/7.51  --preprocessed_out                      false
% 55.09/7.51  --preprocessed_stats                    false
% 55.09/7.51  
% 55.09/7.51  ------ Abstraction refinement Options
% 55.09/7.51  
% 55.09/7.51  --abstr_ref                             []
% 55.09/7.51  --abstr_ref_prep                        false
% 55.09/7.51  --abstr_ref_until_sat                   false
% 55.09/7.51  --abstr_ref_sig_restrict                funpre
% 55.09/7.51  --abstr_ref_af_restrict_to_split_sk     false
% 55.09/7.51  --abstr_ref_under                       []
% 55.09/7.51  
% 55.09/7.51  ------ SAT Options
% 55.09/7.51  
% 55.09/7.51  --sat_mode                              false
% 55.09/7.51  --sat_fm_restart_options                ""
% 55.09/7.51  --sat_gr_def                            false
% 55.09/7.51  --sat_epr_types                         true
% 55.09/7.51  --sat_non_cyclic_types                  false
% 55.09/7.51  --sat_finite_models                     false
% 55.09/7.51  --sat_fm_lemmas                         false
% 55.09/7.51  --sat_fm_prep                           false
% 55.09/7.51  --sat_fm_uc_incr                        true
% 55.09/7.51  --sat_out_model                         small
% 55.09/7.51  --sat_out_clauses                       false
% 55.09/7.51  
% 55.09/7.51  ------ QBF Options
% 55.09/7.51  
% 55.09/7.51  --qbf_mode                              false
% 55.09/7.51  --qbf_elim_univ                         false
% 55.09/7.51  --qbf_dom_inst                          none
% 55.09/7.51  --qbf_dom_pre_inst                      false
% 55.09/7.51  --qbf_sk_in                             false
% 55.09/7.51  --qbf_pred_elim                         true
% 55.09/7.51  --qbf_split                             512
% 55.09/7.51  
% 55.09/7.51  ------ BMC1 Options
% 55.09/7.51  
% 55.09/7.51  --bmc1_incremental                      false
% 55.09/7.51  --bmc1_axioms                           reachable_all
% 55.09/7.51  --bmc1_min_bound                        0
% 55.09/7.51  --bmc1_max_bound                        -1
% 55.09/7.51  --bmc1_max_bound_default                -1
% 55.09/7.51  --bmc1_symbol_reachability              true
% 55.09/7.51  --bmc1_property_lemmas                  false
% 55.09/7.51  --bmc1_k_induction                      false
% 55.09/7.51  --bmc1_non_equiv_states                 false
% 55.09/7.51  --bmc1_deadlock                         false
% 55.09/7.51  --bmc1_ucm                              false
% 55.09/7.51  --bmc1_add_unsat_core                   none
% 55.09/7.51  --bmc1_unsat_core_children              false
% 55.09/7.51  --bmc1_unsat_core_extrapolate_axioms    false
% 55.09/7.51  --bmc1_out_stat                         full
% 55.09/7.51  --bmc1_ground_init                      false
% 55.09/7.51  --bmc1_pre_inst_next_state              false
% 55.09/7.51  --bmc1_pre_inst_state                   false
% 55.09/7.51  --bmc1_pre_inst_reach_state             false
% 55.09/7.51  --bmc1_out_unsat_core                   false
% 55.09/7.51  --bmc1_aig_witness_out                  false
% 55.09/7.51  --bmc1_verbose                          false
% 55.09/7.51  --bmc1_dump_clauses_tptp                false
% 55.09/7.51  --bmc1_dump_unsat_core_tptp             false
% 55.09/7.51  --bmc1_dump_file                        -
% 55.09/7.51  --bmc1_ucm_expand_uc_limit              128
% 55.09/7.51  --bmc1_ucm_n_expand_iterations          6
% 55.09/7.51  --bmc1_ucm_extend_mode                  1
% 55.09/7.51  --bmc1_ucm_init_mode                    2
% 55.09/7.51  --bmc1_ucm_cone_mode                    none
% 55.09/7.51  --bmc1_ucm_reduced_relation_type        0
% 55.09/7.51  --bmc1_ucm_relax_model                  4
% 55.09/7.51  --bmc1_ucm_full_tr_after_sat            true
% 55.09/7.51  --bmc1_ucm_expand_neg_assumptions       false
% 55.09/7.51  --bmc1_ucm_layered_model                none
% 55.09/7.51  --bmc1_ucm_max_lemma_size               10
% 55.09/7.51  
% 55.09/7.51  ------ AIG Options
% 55.09/7.51  
% 55.09/7.51  --aig_mode                              false
% 55.09/7.51  
% 55.09/7.51  ------ Instantiation Options
% 55.09/7.51  
% 55.09/7.51  --instantiation_flag                    true
% 55.09/7.51  --inst_sos_flag                         true
% 55.09/7.51  --inst_sos_phase                        true
% 55.09/7.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.09/7.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.09/7.51  --inst_lit_sel_side                     num_symb
% 55.09/7.51  --inst_solver_per_active                1400
% 55.09/7.51  --inst_solver_calls_frac                1.
% 55.09/7.51  --inst_passive_queue_type               priority_queues
% 55.09/7.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.09/7.51  --inst_passive_queues_freq              [25;2]
% 55.09/7.51  --inst_dismatching                      true
% 55.09/7.51  --inst_eager_unprocessed_to_passive     true
% 55.09/7.51  --inst_prop_sim_given                   true
% 55.09/7.51  --inst_prop_sim_new                     false
% 55.09/7.51  --inst_subs_new                         false
% 55.09/7.51  --inst_eq_res_simp                      false
% 55.09/7.51  --inst_subs_given                       false
% 55.09/7.51  --inst_orphan_elimination               true
% 55.09/7.51  --inst_learning_loop_flag               true
% 55.09/7.51  --inst_learning_start                   3000
% 55.09/7.51  --inst_learning_factor                  2
% 55.09/7.51  --inst_start_prop_sim_after_learn       3
% 55.09/7.51  --inst_sel_renew                        solver
% 55.09/7.51  --inst_lit_activity_flag                true
% 55.09/7.51  --inst_restr_to_given                   false
% 55.09/7.51  --inst_activity_threshold               500
% 55.09/7.51  --inst_out_proof                        true
% 55.09/7.51  
% 55.09/7.51  ------ Resolution Options
% 55.09/7.51  
% 55.09/7.51  --resolution_flag                       true
% 55.09/7.51  --res_lit_sel                           adaptive
% 55.09/7.51  --res_lit_sel_side                      none
% 55.09/7.51  --res_ordering                          kbo
% 55.09/7.51  --res_to_prop_solver                    active
% 55.09/7.51  --res_prop_simpl_new                    false
% 55.09/7.51  --res_prop_simpl_given                  true
% 55.09/7.51  --res_passive_queue_type                priority_queues
% 55.09/7.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.09/7.51  --res_passive_queues_freq               [15;5]
% 55.09/7.51  --res_forward_subs                      full
% 55.09/7.51  --res_backward_subs                     full
% 55.09/7.51  --res_forward_subs_resolution           true
% 55.09/7.51  --res_backward_subs_resolution          true
% 55.09/7.51  --res_orphan_elimination                true
% 55.09/7.51  --res_time_limit                        2.
% 55.09/7.51  --res_out_proof                         true
% 55.09/7.51  
% 55.09/7.51  ------ Superposition Options
% 55.09/7.51  
% 55.09/7.51  --superposition_flag                    true
% 55.09/7.51  --sup_passive_queue_type                priority_queues
% 55.09/7.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.09/7.51  --sup_passive_queues_freq               [8;1;4]
% 55.09/7.51  --demod_completeness_check              fast
% 55.09/7.51  --demod_use_ground                      true
% 55.09/7.51  --sup_to_prop_solver                    passive
% 55.09/7.51  --sup_prop_simpl_new                    true
% 55.09/7.51  --sup_prop_simpl_given                  true
% 55.09/7.51  --sup_fun_splitting                     true
% 55.09/7.51  --sup_smt_interval                      50000
% 55.09/7.51  
% 55.09/7.51  ------ Superposition Simplification Setup
% 55.09/7.51  
% 55.09/7.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.09/7.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.09/7.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.09/7.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.09/7.51  --sup_full_triv                         [TrivRules;PropSubs]
% 55.09/7.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.09/7.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.09/7.51  --sup_immed_triv                        [TrivRules]
% 55.09/7.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.09/7.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.09/7.51  --sup_immed_bw_main                     []
% 55.09/7.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.09/7.51  --sup_input_triv                        [Unflattening;TrivRules]
% 55.09/7.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.09/7.51  --sup_input_bw                          []
% 55.09/7.51  
% 55.09/7.51  ------ Combination Options
% 55.09/7.51  
% 55.09/7.51  --comb_res_mult                         3
% 55.09/7.51  --comb_sup_mult                         2
% 55.09/7.51  --comb_inst_mult                        10
% 55.09/7.51  
% 55.09/7.51  ------ Debug Options
% 55.09/7.51  
% 55.09/7.51  --dbg_backtrace                         false
% 55.09/7.51  --dbg_dump_prop_clauses                 false
% 55.09/7.51  --dbg_dump_prop_clauses_file            -
% 55.09/7.51  --dbg_out_stat                          false
% 55.09/7.51  ------ Parsing...
% 55.09/7.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.09/7.51  
% 55.09/7.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 55.09/7.51  
% 55.09/7.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.09/7.51  
% 55.09/7.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.09/7.51  ------ Proving...
% 55.09/7.51  ------ Problem Properties 
% 55.09/7.51  
% 55.09/7.51  
% 55.09/7.51  clauses                                 30
% 55.09/7.51  conjectures                             2
% 55.09/7.51  EPR                                     14
% 55.09/7.51  Horn                                    27
% 55.09/7.51  unary                                   19
% 55.09/7.51  binary                                  4
% 55.09/7.51  lits                                    56
% 55.09/7.51  lits eq                                 22
% 55.09/7.51  fd_pure                                 0
% 55.09/7.51  fd_pseudo                               0
% 55.09/7.51  fd_cond                                 0
% 55.09/7.51  fd_pseudo_cond                          4
% 55.09/7.51  AC symbols                              1
% 55.09/7.51  
% 55.09/7.51  ------ Schedule dynamic 5 is on 
% 55.09/7.51  
% 55.09/7.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 55.09/7.51  
% 55.09/7.51  
% 55.09/7.51  ------ 
% 55.09/7.51  Current options:
% 55.09/7.51  ------ 
% 55.09/7.51  
% 55.09/7.51  ------ Input Options
% 55.09/7.51  
% 55.09/7.51  --out_options                           all
% 55.09/7.51  --tptp_safe_out                         true
% 55.09/7.51  --problem_path                          ""
% 55.09/7.51  --include_path                          ""
% 55.09/7.51  --clausifier                            res/vclausify_rel
% 55.09/7.51  --clausifier_options                    ""
% 55.09/7.51  --stdin                                 false
% 55.09/7.51  --stats_out                             all
% 55.09/7.51  
% 55.09/7.51  ------ General Options
% 55.09/7.51  
% 55.09/7.51  --fof                                   false
% 55.09/7.51  --time_out_real                         305.
% 55.09/7.51  --time_out_virtual                      -1.
% 55.09/7.51  --symbol_type_check                     false
% 55.09/7.51  --clausify_out                          false
% 55.09/7.51  --sig_cnt_out                           false
% 55.09/7.51  --trig_cnt_out                          false
% 55.09/7.51  --trig_cnt_out_tolerance                1.
% 55.09/7.51  --trig_cnt_out_sk_spl                   false
% 55.09/7.51  --abstr_cl_out                          false
% 55.09/7.51  
% 55.09/7.51  ------ Global Options
% 55.09/7.51  
% 55.09/7.51  --schedule                              default
% 55.09/7.51  --add_important_lit                     false
% 55.09/7.51  --prop_solver_per_cl                    1000
% 55.09/7.51  --min_unsat_core                        false
% 55.09/7.51  --soft_assumptions                      false
% 55.09/7.51  --soft_lemma_size                       3
% 55.09/7.51  --prop_impl_unit_size                   0
% 55.09/7.51  --prop_impl_unit                        []
% 55.09/7.51  --share_sel_clauses                     true
% 55.09/7.51  --reset_solvers                         false
% 55.09/7.51  --bc_imp_inh                            [conj_cone]
% 55.09/7.51  --conj_cone_tolerance                   3.
% 55.09/7.51  --extra_neg_conj                        none
% 55.09/7.51  --large_theory_mode                     true
% 55.09/7.51  --prolific_symb_bound                   200
% 55.09/7.51  --lt_threshold                          2000
% 55.09/7.51  --clause_weak_htbl                      true
% 55.09/7.51  --gc_record_bc_elim                     false
% 55.09/7.51  
% 55.09/7.51  ------ Preprocessing Options
% 55.09/7.51  
% 55.09/7.51  --preprocessing_flag                    true
% 55.09/7.51  --time_out_prep_mult                    0.1
% 55.09/7.51  --splitting_mode                        input
% 55.09/7.51  --splitting_grd                         true
% 55.09/7.51  --splitting_cvd                         false
% 55.09/7.51  --splitting_cvd_svl                     false
% 55.09/7.51  --splitting_nvd                         32
% 55.09/7.51  --sub_typing                            true
% 55.09/7.51  --prep_gs_sim                           true
% 55.09/7.51  --prep_unflatten                        true
% 55.09/7.51  --prep_res_sim                          true
% 55.09/7.51  --prep_upred                            true
% 55.09/7.51  --prep_sem_filter                       exhaustive
% 55.09/7.51  --prep_sem_filter_out                   false
% 55.09/7.51  --pred_elim                             true
% 55.09/7.51  --res_sim_input                         true
% 55.09/7.51  --eq_ax_congr_red                       true
% 55.09/7.51  --pure_diseq_elim                       true
% 55.09/7.51  --brand_transform                       false
% 55.09/7.51  --non_eq_to_eq                          false
% 55.09/7.51  --prep_def_merge                        true
% 55.09/7.51  --prep_def_merge_prop_impl              false
% 55.09/7.51  --prep_def_merge_mbd                    true
% 55.09/7.51  --prep_def_merge_tr_red                 false
% 55.09/7.51  --prep_def_merge_tr_cl                  false
% 55.09/7.51  --smt_preprocessing                     true
% 55.09/7.51  --smt_ac_axioms                         fast
% 55.09/7.51  --preprocessed_out                      false
% 55.09/7.51  --preprocessed_stats                    false
% 55.09/7.51  
% 55.09/7.51  ------ Abstraction refinement Options
% 55.09/7.51  
% 55.09/7.51  --abstr_ref                             []
% 55.09/7.51  --abstr_ref_prep                        false
% 55.09/7.51  --abstr_ref_until_sat                   false
% 55.09/7.51  --abstr_ref_sig_restrict                funpre
% 55.09/7.51  --abstr_ref_af_restrict_to_split_sk     false
% 55.09/7.51  --abstr_ref_under                       []
% 55.09/7.51  
% 55.09/7.51  ------ SAT Options
% 55.09/7.51  
% 55.09/7.51  --sat_mode                              false
% 55.09/7.51  --sat_fm_restart_options                ""
% 55.09/7.51  --sat_gr_def                            false
% 55.09/7.51  --sat_epr_types                         true
% 55.09/7.51  --sat_non_cyclic_types                  false
% 55.09/7.51  --sat_finite_models                     false
% 55.09/7.51  --sat_fm_lemmas                         false
% 55.09/7.51  --sat_fm_prep                           false
% 55.09/7.51  --sat_fm_uc_incr                        true
% 55.09/7.51  --sat_out_model                         small
% 55.09/7.51  --sat_out_clauses                       false
% 55.09/7.51  
% 55.09/7.51  ------ QBF Options
% 55.09/7.51  
% 55.09/7.51  --qbf_mode                              false
% 55.09/7.51  --qbf_elim_univ                         false
% 55.09/7.51  --qbf_dom_inst                          none
% 55.09/7.51  --qbf_dom_pre_inst                      false
% 55.09/7.51  --qbf_sk_in                             false
% 55.09/7.51  --qbf_pred_elim                         true
% 55.09/7.51  --qbf_split                             512
% 55.09/7.51  
% 55.09/7.51  ------ BMC1 Options
% 55.09/7.51  
% 55.09/7.51  --bmc1_incremental                      false
% 55.09/7.51  --bmc1_axioms                           reachable_all
% 55.09/7.51  --bmc1_min_bound                        0
% 55.09/7.51  --bmc1_max_bound                        -1
% 55.09/7.51  --bmc1_max_bound_default                -1
% 55.09/7.51  --bmc1_symbol_reachability              true
% 55.09/7.51  --bmc1_property_lemmas                  false
% 55.09/7.51  --bmc1_k_induction                      false
% 55.09/7.51  --bmc1_non_equiv_states                 false
% 55.09/7.51  --bmc1_deadlock                         false
% 55.09/7.51  --bmc1_ucm                              false
% 55.09/7.51  --bmc1_add_unsat_core                   none
% 55.09/7.51  --bmc1_unsat_core_children              false
% 55.09/7.51  --bmc1_unsat_core_extrapolate_axioms    false
% 55.09/7.51  --bmc1_out_stat                         full
% 55.09/7.51  --bmc1_ground_init                      false
% 55.09/7.51  --bmc1_pre_inst_next_state              false
% 55.09/7.51  --bmc1_pre_inst_state                   false
% 55.09/7.51  --bmc1_pre_inst_reach_state             false
% 55.09/7.51  --bmc1_out_unsat_core                   false
% 55.09/7.51  --bmc1_aig_witness_out                  false
% 55.09/7.51  --bmc1_verbose                          false
% 55.09/7.51  --bmc1_dump_clauses_tptp                false
% 55.09/7.51  --bmc1_dump_unsat_core_tptp             false
% 55.09/7.51  --bmc1_dump_file                        -
% 55.09/7.51  --bmc1_ucm_expand_uc_limit              128
% 55.09/7.51  --bmc1_ucm_n_expand_iterations          6
% 55.09/7.51  --bmc1_ucm_extend_mode                  1
% 55.09/7.51  --bmc1_ucm_init_mode                    2
% 55.09/7.51  --bmc1_ucm_cone_mode                    none
% 55.09/7.51  --bmc1_ucm_reduced_relation_type        0
% 55.09/7.51  --bmc1_ucm_relax_model                  4
% 55.09/7.51  --bmc1_ucm_full_tr_after_sat            true
% 55.09/7.51  --bmc1_ucm_expand_neg_assumptions       false
% 55.09/7.51  --bmc1_ucm_layered_model                none
% 55.09/7.51  --bmc1_ucm_max_lemma_size               10
% 55.09/7.51  
% 55.09/7.51  ------ AIG Options
% 55.09/7.51  
% 55.09/7.51  --aig_mode                              false
% 55.09/7.51  
% 55.09/7.51  ------ Instantiation Options
% 55.09/7.51  
% 55.09/7.51  --instantiation_flag                    true
% 55.09/7.51  --inst_sos_flag                         true
% 55.09/7.51  --inst_sos_phase                        true
% 55.09/7.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.09/7.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.09/7.51  --inst_lit_sel_side                     none
% 55.09/7.51  --inst_solver_per_active                1400
% 55.09/7.51  --inst_solver_calls_frac                1.
% 55.09/7.51  --inst_passive_queue_type               priority_queues
% 55.09/7.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.09/7.51  --inst_passive_queues_freq              [25;2]
% 55.09/7.51  --inst_dismatching                      true
% 55.09/7.51  --inst_eager_unprocessed_to_passive     true
% 55.09/7.51  --inst_prop_sim_given                   true
% 55.09/7.51  --inst_prop_sim_new                     false
% 55.09/7.51  --inst_subs_new                         false
% 55.09/7.51  --inst_eq_res_simp                      false
% 55.09/7.51  --inst_subs_given                       false
% 55.09/7.51  --inst_orphan_elimination               true
% 55.09/7.51  --inst_learning_loop_flag               true
% 55.09/7.51  --inst_learning_start                   3000
% 55.09/7.51  --inst_learning_factor                  2
% 55.09/7.51  --inst_start_prop_sim_after_learn       3
% 55.09/7.51  --inst_sel_renew                        solver
% 55.09/7.51  --inst_lit_activity_flag                true
% 55.09/7.51  --inst_restr_to_given                   false
% 55.09/7.51  --inst_activity_threshold               500
% 55.09/7.51  --inst_out_proof                        true
% 55.09/7.51  
% 55.09/7.51  ------ Resolution Options
% 55.09/7.51  
% 55.09/7.51  --resolution_flag                       false
% 55.09/7.51  --res_lit_sel                           adaptive
% 55.09/7.51  --res_lit_sel_side                      none
% 55.09/7.51  --res_ordering                          kbo
% 55.09/7.51  --res_to_prop_solver                    active
% 55.09/7.51  --res_prop_simpl_new                    false
% 55.09/7.51  --res_prop_simpl_given                  true
% 55.09/7.51  --res_passive_queue_type                priority_queues
% 55.09/7.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.09/7.51  --res_passive_queues_freq               [15;5]
% 55.09/7.51  --res_forward_subs                      full
% 55.09/7.51  --res_backward_subs                     full
% 55.09/7.51  --res_forward_subs_resolution           true
% 55.09/7.51  --res_backward_subs_resolution          true
% 55.09/7.51  --res_orphan_elimination                true
% 55.09/7.51  --res_time_limit                        2.
% 55.09/7.51  --res_out_proof                         true
% 55.09/7.51  
% 55.09/7.51  ------ Superposition Options
% 55.09/7.51  
% 55.09/7.51  --superposition_flag                    true
% 55.09/7.51  --sup_passive_queue_type                priority_queues
% 55.09/7.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.09/7.51  --sup_passive_queues_freq               [8;1;4]
% 55.09/7.51  --demod_completeness_check              fast
% 55.09/7.51  --demod_use_ground                      true
% 55.09/7.51  --sup_to_prop_solver                    passive
% 55.09/7.51  --sup_prop_simpl_new                    true
% 55.09/7.51  --sup_prop_simpl_given                  true
% 55.09/7.51  --sup_fun_splitting                     true
% 55.09/7.51  --sup_smt_interval                      50000
% 55.09/7.51  
% 55.09/7.51  ------ Superposition Simplification Setup
% 55.09/7.51  
% 55.09/7.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.09/7.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.09/7.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.09/7.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.09/7.51  --sup_full_triv                         [TrivRules;PropSubs]
% 55.09/7.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.09/7.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.09/7.51  --sup_immed_triv                        [TrivRules]
% 55.09/7.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.09/7.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.09/7.51  --sup_immed_bw_main                     []
% 55.09/7.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.09/7.51  --sup_input_triv                        [Unflattening;TrivRules]
% 55.09/7.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.09/7.51  --sup_input_bw                          []
% 55.09/7.51  
% 55.09/7.51  ------ Combination Options
% 55.09/7.51  
% 55.09/7.51  --comb_res_mult                         3
% 55.09/7.51  --comb_sup_mult                         2
% 55.09/7.51  --comb_inst_mult                        10
% 55.09/7.51  
% 55.09/7.51  ------ Debug Options
% 55.09/7.51  
% 55.09/7.51  --dbg_backtrace                         false
% 55.09/7.51  --dbg_dump_prop_clauses                 false
% 55.09/7.51  --dbg_dump_prop_clauses_file            -
% 55.09/7.51  --dbg_out_stat                          false
% 55.09/7.51  
% 55.09/7.51  
% 55.09/7.51  
% 55.09/7.51  
% 55.09/7.51  ------ Proving...
% 55.09/7.51  
% 55.09/7.51  
% 55.09/7.51  % SZS status Theorem for theBenchmark.p
% 55.09/7.51  
% 55.09/7.51  % SZS output start CNFRefutation for theBenchmark.p
% 55.09/7.51  
% 55.09/7.51  fof(f18,conjecture,(
% 55.09/7.51    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 55.09/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.09/7.51  
% 55.09/7.51  fof(f19,negated_conjecture,(
% 55.09/7.51    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 55.09/7.51    inference(negated_conjecture,[],[f18])).
% 55.09/7.51  
% 55.09/7.51  fof(f23,plain,(
% 55.09/7.51    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 55.09/7.51    inference(ennf_transformation,[],[f19])).
% 55.09/7.51  
% 55.09/7.51  fof(f39,plain,(
% 55.09/7.51    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (sK4 != sK6 & r1_tarski(k2_tarski(sK4,sK5),k1_tarski(sK6)))),
% 55.09/7.51    introduced(choice_axiom,[])).
% 55.09/7.51  
% 55.09/7.51  fof(f40,plain,(
% 55.09/7.51    sK4 != sK6 & r1_tarski(k2_tarski(sK4,sK5),k1_tarski(sK6))),
% 55.09/7.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f23,f39])).
% 55.09/7.51  
% 55.09/7.51  fof(f77,plain,(
% 55.09/7.51    r1_tarski(k2_tarski(sK4,sK5),k1_tarski(sK6))),
% 55.09/7.51    inference(cnf_transformation,[],[f40])).
% 55.09/7.51  
% 55.09/7.51  fof(f12,axiom,(
% 55.09/7.51    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 55.09/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.09/7.51  
% 55.09/7.51  fof(f71,plain,(
% 55.09/7.51    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 55.09/7.51    inference(cnf_transformation,[],[f12])).
% 55.09/7.51  
% 55.09/7.51  fof(f16,axiom,(
% 55.09/7.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 55.09/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.09/7.51  
% 55.09/7.51  fof(f75,plain,(
% 55.09/7.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 55.09/7.51    inference(cnf_transformation,[],[f16])).
% 55.09/7.51  
% 55.09/7.51  fof(f13,axiom,(
% 55.09/7.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 55.09/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.09/7.51  
% 55.09/7.51  fof(f72,plain,(
% 55.09/7.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 55.09/7.51    inference(cnf_transformation,[],[f13])).
% 55.09/7.51  
% 55.09/7.51  fof(f14,axiom,(
% 55.09/7.51    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 55.09/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.09/7.51  
% 55.09/7.51  fof(f73,plain,(
% 55.09/7.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 55.09/7.51    inference(cnf_transformation,[],[f14])).
% 55.09/7.51  
% 55.09/7.51  fof(f15,axiom,(
% 55.09/7.51    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 55.09/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.09/7.51  
% 55.09/7.51  fof(f74,plain,(
% 55.09/7.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 55.09/7.51    inference(cnf_transformation,[],[f15])).
% 55.09/7.51  
% 55.09/7.51  fof(f79,plain,(
% 55.09/7.51    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 55.09/7.51    inference(definition_unfolding,[],[f73,f74])).
% 55.09/7.51  
% 55.09/7.51  fof(f80,plain,(
% 55.09/7.51    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 55.09/7.51    inference(definition_unfolding,[],[f72,f79])).
% 55.09/7.51  
% 55.09/7.51  fof(f81,plain,(
% 55.09/7.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 55.09/7.51    inference(definition_unfolding,[],[f75,f80])).
% 55.09/7.51  
% 55.09/7.51  fof(f82,plain,(
% 55.09/7.51    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 55.09/7.51    inference(definition_unfolding,[],[f71,f81])).
% 55.09/7.51  
% 55.09/7.51  fof(f95,plain,(
% 55.09/7.51    r1_tarski(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6))),
% 55.09/7.51    inference(definition_unfolding,[],[f77,f81,f82])).
% 55.09/7.51  
% 55.09/7.51  fof(f3,axiom,(
% 55.09/7.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 55.09/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.09/7.51  
% 55.09/7.51  fof(f21,plain,(
% 55.09/7.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 55.09/7.51    inference(ennf_transformation,[],[f3])).
% 55.09/7.51  
% 55.09/7.51  fof(f43,plain,(
% 55.09/7.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 55.09/7.51    inference(cnf_transformation,[],[f21])).
% 55.09/7.51  
% 55.09/7.51  fof(f4,axiom,(
% 55.09/7.51    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 55.09/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.09/7.51  
% 55.09/7.51  fof(f44,plain,(
% 55.09/7.51    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 55.09/7.51    inference(cnf_transformation,[],[f4])).
% 55.09/7.51  
% 55.09/7.51  fof(f1,axiom,(
% 55.09/7.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 55.09/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.09/7.51  
% 55.09/7.51  fof(f41,plain,(
% 55.09/7.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 55.09/7.51    inference(cnf_transformation,[],[f1])).
% 55.09/7.51  
% 55.09/7.51  fof(f8,axiom,(
% 55.09/7.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 55.09/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.09/7.51  
% 55.09/7.51  fof(f67,plain,(
% 55.09/7.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 55.09/7.51    inference(cnf_transformation,[],[f8])).
% 55.09/7.51  
% 55.09/7.51  fof(f7,axiom,(
% 55.09/7.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 55.09/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.09/7.51  
% 55.09/7.51  fof(f66,plain,(
% 55.09/7.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 55.09/7.51    inference(cnf_transformation,[],[f7])).
% 55.09/7.51  
% 55.09/7.51  fof(f11,axiom,(
% 55.09/7.51    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 55.09/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.09/7.51  
% 55.09/7.51  fof(f70,plain,(
% 55.09/7.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 55.09/7.51    inference(cnf_transformation,[],[f11])).
% 55.09/7.51  
% 55.09/7.51  fof(f83,plain,(
% 55.09/7.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 55.09/7.51    inference(definition_unfolding,[],[f70,f82])).
% 55.09/7.51  
% 55.09/7.51  fof(f84,plain,(
% 55.09/7.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 55.09/7.51    inference(definition_unfolding,[],[f66,f82,f83])).
% 55.09/7.51  
% 55.09/7.51  fof(f92,plain,(
% 55.09/7.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)))) )),
% 55.09/7.51    inference(definition_unfolding,[],[f67,f81,f84])).
% 55.09/7.51  
% 55.09/7.51  fof(f17,axiom,(
% 55.09/7.51    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 55.09/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.09/7.51  
% 55.09/7.51  fof(f76,plain,(
% 55.09/7.51    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 55.09/7.51    inference(cnf_transformation,[],[f17])).
% 55.09/7.51  
% 55.09/7.51  fof(f94,plain,(
% 55.09/7.51    ( ! [X0,X1] : (r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 55.09/7.51    inference(definition_unfolding,[],[f76,f82,f81])).
% 55.09/7.51  
% 55.09/7.51  fof(f2,axiom,(
% 55.09/7.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 55.09/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.09/7.51  
% 55.09/7.51  fof(f20,plain,(
% 55.09/7.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 55.09/7.51    inference(ennf_transformation,[],[f2])).
% 55.09/7.51  
% 55.09/7.51  fof(f42,plain,(
% 55.09/7.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 55.09/7.51    inference(cnf_transformation,[],[f20])).
% 55.09/7.51  
% 55.09/7.51  fof(f6,axiom,(
% 55.09/7.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : (k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10 <=> ! [X11] : (r2_hidden(X11,X10) <=> ~(X9 != X11 & X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11)))),
% 55.09/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.09/7.51  
% 55.09/7.51  fof(f22,plain,(
% 55.09/7.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : (k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10 <=> ! [X11] : (r2_hidden(X11,X10) <=> (X9 = X11 | X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11)))),
% 55.09/7.51    inference(ennf_transformation,[],[f6])).
% 55.09/7.51  
% 55.09/7.51  fof(f25,plain,(
% 55.09/7.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) <=> ! [X11] : (r2_hidden(X11,X10) <=> sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 55.09/7.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 55.09/7.51  
% 55.09/7.51  fof(f24,plain,(
% 55.09/7.51    ! [X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X9 = X11 | X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11))),
% 55.09/7.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 55.09/7.51  
% 55.09/7.51  fof(f26,plain,(
% 55.09/7.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : (k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10))),
% 55.09/7.51    inference(definition_folding,[],[f22,f25,f24])).
% 55.09/7.51  
% 55.09/7.51  fof(f38,plain,(
% 55.09/7.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : ((k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10))),
% 55.09/7.51    inference(nnf_transformation,[],[f26])).
% 55.09/7.51  
% 55.09/7.51  fof(f64,plain,(
% 55.09/7.51    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10) )),
% 55.09/7.51    inference(cnf_transformation,[],[f38])).
% 55.09/7.51  
% 55.09/7.51  fof(f10,axiom,(
% 55.09/7.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : k2_xboole_0(k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) = k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)),
% 55.09/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.09/7.51  
% 55.09/7.51  fof(f69,plain,(
% 55.09/7.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (k2_xboole_0(k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) = k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 55.09/7.51    inference(cnf_transformation,[],[f10])).
% 55.09/7.51  
% 55.09/7.51  fof(f85,plain,(
% 55.09/7.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),k5_enumset1(X9,X9,X9,X9,X9,X9,X9)) = k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 55.09/7.51    inference(definition_unfolding,[],[f69,f84,f82])).
% 55.09/7.51  
% 55.09/7.51  fof(f91,plain,(
% 55.09/7.51    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) | k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),k5_enumset1(X9,X9,X9,X9,X9,X9,X9)) != X10) )),
% 55.09/7.51    inference(definition_unfolding,[],[f64,f85])).
% 55.09/7.51  
% 55.09/7.51  fof(f109,plain,(
% 55.09/7.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),k5_enumset1(X9,X9,X9,X9,X9,X9,X9)))) )),
% 55.09/7.51    inference(equality_resolution,[],[f91])).
% 55.09/7.51  
% 55.09/7.51  fof(f9,axiom,(
% 55.09/7.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 55.09/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.09/7.51  
% 55.09/7.51  fof(f68,plain,(
% 55.09/7.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 55.09/7.51    inference(cnf_transformation,[],[f9])).
% 55.09/7.51  
% 55.09/7.51  fof(f93,plain,(
% 55.09/7.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)),k5_enumset1(X8,X8,X8,X8,X8,X8,X8)) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)))) )),
% 55.09/7.51    inference(definition_unfolding,[],[f68,f83,f82,f84])).
% 55.09/7.51  
% 55.09/7.51  fof(f35,plain,(
% 55.09/7.51    ! [X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X9 != X11 & X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11)) & ((X9 = X11 | X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11) | ~sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 55.09/7.51    inference(nnf_transformation,[],[f24])).
% 55.09/7.51  
% 55.09/7.51  fof(f36,plain,(
% 55.09/7.51    ! [X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X9 != X11 & X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11)) & (X9 = X11 | X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | ~sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 55.09/7.51    inference(flattening,[],[f35])).
% 55.09/7.51  
% 55.09/7.51  fof(f37,plain,(
% 55.09/7.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8 & X0 != X9 & X0 != X10)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | X0 = X9 | X0 = X10 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)))),
% 55.09/7.51    inference(rectify,[],[f36])).
% 55.09/7.51  
% 55.09/7.51  fof(f63,plain,(
% 55.09/7.51    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) | X0 != X1) )),
% 55.09/7.51    inference(cnf_transformation,[],[f37])).
% 55.09/7.51  
% 55.09/7.51  fof(f99,plain,(
% 55.09/7.51    ( ! [X6,X4,X2,X10,X8,X7,X5,X3,X1,X9] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)) )),
% 55.09/7.51    inference(equality_resolution,[],[f63])).
% 55.09/7.51  
% 55.09/7.51  fof(f31,plain,(
% 55.09/7.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) | ? [X11] : ((~sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X10)) & (sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X11,X10)))) & (! [X11] : ((r2_hidden(X11,X10) | ~sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X10))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)))),
% 55.09/7.51    inference(nnf_transformation,[],[f25])).
% 55.09/7.51  
% 55.09/7.51  fof(f32,plain,(
% 55.09/7.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) | ? [X11] : ((~sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X10)) & (sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X11,X10)))) & (! [X12] : ((r2_hidden(X12,X10) | ~sP0(X12,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X12,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X12,X10))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)))),
% 55.09/7.51    inference(rectify,[],[f31])).
% 55.09/7.51  
% 55.09/7.51  fof(f33,plain,(
% 55.09/7.51    ! [X10,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X11] : ((~sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X10)) & (sP0(X11,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X11,X10))) => ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10))))),
% 55.09/7.51    introduced(choice_axiom,[])).
% 55.09/7.51  
% 55.09/7.51  fof(f34,plain,(
% 55.09/7.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) | ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10)))) & (! [X12] : ((r2_hidden(X12,X10) | ~sP0(X12,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X12,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X12,X10))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)))),
% 55.09/7.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 55.09/7.51  
% 55.09/7.51  fof(f50,plain,(
% 55.09/7.51    ( ! [X6,X4,X2,X0,X12,X10,X8,X7,X5,X3,X1,X9] : (r2_hidden(X12,X10) | ~sP0(X12,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)) )),
% 55.09/7.51    inference(cnf_transformation,[],[f34])).
% 55.09/7.51  
% 55.09/7.51  fof(f5,axiom,(
% 55.09/7.51    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 55.09/7.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.09/7.51  
% 55.09/7.51  fof(f27,plain,(
% 55.09/7.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 55.09/7.51    inference(nnf_transformation,[],[f5])).
% 55.09/7.51  
% 55.09/7.51  fof(f28,plain,(
% 55.09/7.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 55.09/7.51    inference(rectify,[],[f27])).
% 55.09/7.51  
% 55.09/7.51  fof(f29,plain,(
% 55.09/7.51    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 55.09/7.51    introduced(choice_axiom,[])).
% 55.09/7.51  
% 55.09/7.51  fof(f30,plain,(
% 55.09/7.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 55.09/7.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).
% 55.09/7.51  
% 55.09/7.51  fof(f45,plain,(
% 55.09/7.51    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 55.09/7.51    inference(cnf_transformation,[],[f30])).
% 55.09/7.51  
% 55.09/7.51  fof(f89,plain,(
% 55.09/7.51    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 55.09/7.51    inference(definition_unfolding,[],[f45,f82])).
% 55.09/7.51  
% 55.09/7.51  fof(f98,plain,(
% 55.09/7.51    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) )),
% 55.09/7.51    inference(equality_resolution,[],[f89])).
% 55.09/7.51  
% 55.09/7.51  fof(f78,plain,(
% 55.09/7.51    sK4 != sK6),
% 55.09/7.51    inference(cnf_transformation,[],[f40])).
% 55.09/7.51  
% 55.09/7.51  cnf(c_29,negated_conjecture,
% 55.09/7.51      ( r1_tarski(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 55.09/7.51      inference(cnf_transformation,[],[f95]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_1538,plain,
% 55.09/7.51      ( r1_tarski(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 55.09/7.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_2,plain,
% 55.09/7.51      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 55.09/7.51      inference(cnf_transformation,[],[f43]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_1561,plain,
% 55.09/7.51      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 55.09/7.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_2495,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_1538,c_1561]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_3,plain,
% 55.09/7.51      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 55.09/7.51      inference(cnf_transformation,[],[f44]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_2649,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X0)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X0) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_2495,c_3]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_0,plain,
% 55.09/7.51      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 55.09/7.51      inference(cnf_transformation,[],[f41]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_1593,plain,
% 55.09/7.51      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_3313,plain,
% 55.09/7.51      ( k2_xboole_0(X0,k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5))) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X0) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_2649,c_1593]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_1594,plain,
% 55.09/7.51      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_2651,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X0)) = k2_xboole_0(X0,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_2495,c_1594]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_4657,plain,
% 55.09/7.51      ( k2_xboole_0(k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6))) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_3313,c_2651]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_2652,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),X0)) = k2_xboole_0(X0,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_2495,c_1593]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_4660,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5))) = k2_xboole_0(k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_3313,c_2652]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_4661,plain,
% 55.09/7.51      ( k2_xboole_0(k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 55.09/7.51      inference(demodulation,[status(thm)],[c_4660,c_3313]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_25,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
% 55.09/7.51      inference(cnf_transformation,[],[f92]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_1131,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) = k2_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
% 55.09/7.51      inference(theory_normalisation,[status(thm)],[c_25,c_3,c_0]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_2476,plain,
% 55.09/7.51      ( k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)),k5_enumset1(X8,X8,X8,X8,X8,X8,X8)) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X8,X8,X8,X8,X8,X8,X0)) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_1131,c_0]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_4662,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
% 55.09/7.51      inference(demodulation,[status(thm)],[c_4661,c_2476,c_2495]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_4664,plain,
% 55.09/7.51      ( k2_xboole_0(k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 55.09/7.51      inference(demodulation,[status(thm)],[c_4657,c_4662]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_4665,plain,
% 55.09/7.51      ( k2_xboole_0(k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
% 55.09/7.51      inference(light_normalisation,[status(thm)],[c_4664,c_2495]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_5720,plain,
% 55.09/7.51      ( k2_xboole_0(k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X0)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X0) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_4665,c_3]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_5724,plain,
% 55.09/7.51      ( k2_xboole_0(k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X0)) = k2_xboole_0(X0,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_4665,c_1594]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_5698,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X0)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X0) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_4662,c_3]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_3297,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k2_xboole_0(X0,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6))) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X0) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_0,c_2649]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_5730,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5))) = k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_4665,c_3297]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_5732,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5))) = k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
% 55.09/7.51      inference(light_normalisation,[status(thm)],[c_5730,c_2495]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_6172,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)) = k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_5698,c_5732]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_27,plain,
% 55.09/7.51      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
% 55.09/7.51      inference(cnf_transformation,[],[f94]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_1539,plain,
% 55.09/7.51      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = iProver_top ),
% 55.09/7.51      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_1,plain,
% 55.09/7.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 55.09/7.51      inference(cnf_transformation,[],[f42]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_1134,plain,
% 55.09/7.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X1,X2)) ),
% 55.09/7.51      inference(theory_normalisation,[status(thm)],[c_1,c_3,c_0]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_1562,plain,
% 55.09/7.51      ( r1_tarski(X0,X1) != iProver_top
% 55.09/7.51      | r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 55.09/7.51      inference(predicate_to_equality,[status(thm)],[c_1134]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_7585,plain,
% 55.09/7.51      ( r1_tarski(X0,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top
% 55.09/7.51      | r1_tarski(X0,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5)) != iProver_top ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_2495,c_1562]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_8189,plain,
% 55.09/7.51      ( r1_tarski(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_1539,c_7585]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_8245,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_8189,c_1561]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_1592,plain,
% 55.09/7.51      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_5704,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k2_xboole_0(X0,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6))) = k2_xboole_0(X0,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_4662,c_1592]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_6358,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0)) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_5704,c_1131]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_4675,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_1539,c_1561]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_6369,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0) ),
% 55.09/7.51      inference(demodulation,[status(thm)],[c_6358,c_4675]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_8246,plain,
% 55.09/7.51      ( k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4) = k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) ),
% 55.09/7.51      inference(demodulation,[status(thm)],[c_8245,c_6369]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_19180,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4),X0)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4),X0) ),
% 55.09/7.51      inference(light_normalisation,
% 55.09/7.51                [status(thm)],
% 55.09/7.51                [c_5720,c_5724,c_6172,c_8246]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_2477,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)),X9)) = k2_xboole_0(X9,k2_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_1131,c_1594]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_17172,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X1)) = k2_xboole_0(X1,k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(X0,X0,X0,X0,X0,X0,sK6))) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_6172,c_2477]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_5703,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(X0,X0,X0,X0,X0,X0,sK6)) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_4662,c_1131]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_14688,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(X0,X0,X0,X0,X0,X0,sK6)) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_4662,c_2476]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_4651,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(X0,X0,X0,X0,X0,X0,sK6)) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_3313,c_1131]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_14747,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4),k5_enumset1(X0,X0,X0,X0,X0,X0,sK6)) = k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(X0,X0,X0,X0,X0,X0,sK6)) ),
% 55.09/7.51      inference(light_normalisation,
% 55.09/7.51                [status(thm)],
% 55.09/7.51                [c_14688,c_4651,c_8246]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_17044,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK5),k5_enumset1(X0,X0,X0,X0,X0,X0,sK6)) = k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0) ),
% 55.09/7.51      inference(light_normalisation,
% 55.09/7.51                [status(thm)],
% 55.09/7.51                [c_5703,c_6369,c_8246,c_14747]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_17304,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4),X1)) = k2_xboole_0(X1,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0)) ),
% 55.09/7.51      inference(light_normalisation,
% 55.09/7.51                [status(thm)],
% 55.09/7.51                [c_17172,c_8246,c_17044]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_19181,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4),X0)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4),X0) ),
% 55.09/7.51      inference(demodulation,[status(thm)],[c_19180,c_8246,c_17304]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_24,plain,
% 55.09/7.51      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),k5_enumset1(X9,X9,X9,X9,X9,X9,X9))) ),
% 55.09/7.51      inference(cnf_transformation,[],[f109]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_1132,plain,
% 55.09/7.51      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k2_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k5_enumset1(X9,X9,X9,X9,X9,X9,X9))))) ),
% 55.09/7.51      inference(theory_normalisation,[status(thm)],[c_24,c_3,c_0]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_1540,plain,
% 55.09/7.51      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k2_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k5_enumset1(X9,X9,X9,X9,X9,X9,X9))))) = iProver_top ),
% 55.09/7.51      inference(predicate_to_equality,[status(thm)],[c_1132]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_2471,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X8,X8,X8,X8,X8,X8,X8))) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X0,X0,X8)) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_0,c_1131]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_6427,plain,
% 55.09/7.51      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k5_enumset1(X1,X1,X1,X1,X1,X1,X9)))) = iProver_top ),
% 55.09/7.51      inference(demodulation,[status(thm)],[c_1540,c_2471]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_6433,plain,
% 55.09/7.51      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,k2_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X9),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) = iProver_top ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_1594,c_6427]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_117869,plain,
% 55.09/7.51      ( sP1(X0,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK4,sK4,k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = iProver_top ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_19181,c_6433]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_26,plain,
% 55.09/7.51      ( k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)),k5_enumset1(X8,X8,X8,X8,X8,X8,X8)) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) ),
% 55.09/7.51      inference(cnf_transformation,[],[f93]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_1130,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X8,X8,X8,X8,X8,X8,X8))) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) ),
% 55.09/7.51      inference(theory_normalisation,[status(thm)],[c_26,c_3,c_0]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_1563,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X8,X8,X8,X8,X8,X8,X8))) = k2_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
% 55.09/7.51      inference(light_normalisation,[status(thm)],[c_1130,c_1131]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_5699,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),X0)) = k2_xboole_0(X0,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_4662,c_1593]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_8646,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_1563,c_5699]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_8654,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4)) = k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0) ),
% 55.09/7.51      inference(light_normalisation,[status(thm)],[c_8646,c_6369,c_8246]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_8647,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 55.09/7.51      inference(superposition,[status(thm)],[c_1563,c_5698]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_8653,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0),k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4)) ),
% 55.09/7.51      inference(light_normalisation,[status(thm)],[c_8647,c_4651,c_8246]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_8655,plain,
% 55.09/7.51      ( k2_xboole_0(k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK4),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0) ),
% 55.09/7.51      inference(demodulation,[status(thm)],[c_8654,c_8653]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_117877,plain,
% 55.09/7.51      ( sP1(X0,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK4,sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0)) = iProver_top ),
% 55.09/7.51      inference(light_normalisation,[status(thm)],[c_117869,c_8655]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_117891,plain,
% 55.09/7.51      ( sP1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK4,sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 55.09/7.51      inference(instantiation,[status(thm)],[c_117877]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_12,plain,
% 55.09/7.51      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
% 55.09/7.51      inference(cnf_transformation,[],[f99]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_1756,plain,
% 55.09/7.51      ( sP0(sK4,sK4,X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
% 55.09/7.51      inference(instantiation,[status(thm)],[c_12]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_2661,plain,
% 55.09/7.51      ( sP0(sK4,sK4,sK4,X0,X1,X2,X3,X4,X5,X6,X7) ),
% 55.09/7.51      inference(instantiation,[status(thm)],[c_1756]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_2662,plain,
% 55.09/7.51      ( sP0(sK4,sK4,sK4,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
% 55.09/7.51      inference(predicate_to_equality,[status(thm)],[c_2661]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_2664,plain,
% 55.09/7.51      ( sP0(sK4,sK4,sK4,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = iProver_top ),
% 55.09/7.51      inference(instantiation,[status(thm)],[c_2662]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_10,plain,
% 55.09/7.51      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10)
% 55.09/7.51      | ~ sP1(X10,X9,X8,X7,X6,X5,X4,X3,X2,X1,X11)
% 55.09/7.51      | r2_hidden(X0,X11) ),
% 55.09/7.51      inference(cnf_transformation,[],[f50]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_1604,plain,
% 55.09/7.51      ( ~ sP0(sK4,X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
% 55.09/7.51      | ~ sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X0,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 55.09/7.51      | r2_hidden(sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 55.09/7.51      inference(instantiation,[status(thm)],[c_10]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_1640,plain,
% 55.09/7.51      ( ~ sP0(sK4,sK4,X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 55.09/7.51      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X0,sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 55.09/7.51      | r2_hidden(sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 55.09/7.51      inference(instantiation,[status(thm)],[c_1604]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_1761,plain,
% 55.09/7.51      ( ~ sP0(sK4,sK4,sK4,X0,X1,X2,X3,X4,X5,X6,X7)
% 55.09/7.51      | ~ sP1(X7,X6,X5,X4,X3,X2,X1,X0,sK4,sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 55.09/7.51      | r2_hidden(sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 55.09/7.51      inference(instantiation,[status(thm)],[c_1640]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_1762,plain,
% 55.09/7.51      ( sP0(sK4,sK4,sK4,X0,X1,X2,X3,X4,X5,X6,X7) != iProver_top
% 55.09/7.51      | sP1(X7,X6,X5,X4,X3,X2,X1,X0,sK4,sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
% 55.09/7.51      | r2_hidden(sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 55.09/7.51      inference(predicate_to_equality,[status(thm)],[c_1761]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_1764,plain,
% 55.09/7.51      ( sP0(sK4,sK4,sK4,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != iProver_top
% 55.09/7.51      | sP1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK4,sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
% 55.09/7.51      | r2_hidden(sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 55.09/7.51      inference(instantiation,[status(thm)],[c_1762]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_7,plain,
% 55.09/7.51      ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 55.09/7.51      inference(cnf_transformation,[],[f98]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_1600,plain,
% 55.09/7.51      ( ~ r2_hidden(sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 55.09/7.51      | sK4 = sK6 ),
% 55.09/7.51      inference(instantiation,[status(thm)],[c_7]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_1601,plain,
% 55.09/7.51      ( sK4 = sK6
% 55.09/7.51      | r2_hidden(sK4,k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top ),
% 55.09/7.51      inference(predicate_to_equality,[status(thm)],[c_1600]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(c_28,negated_conjecture,
% 55.09/7.51      ( sK4 != sK6 ),
% 55.09/7.51      inference(cnf_transformation,[],[f78]) ).
% 55.09/7.51  
% 55.09/7.51  cnf(contradiction,plain,
% 55.09/7.51      ( $false ),
% 55.09/7.51      inference(minisat,
% 55.09/7.51                [status(thm)],
% 55.09/7.51                [c_117891,c_2664,c_1764,c_1601,c_28]) ).
% 55.09/7.51  
% 55.09/7.51  
% 55.09/7.51  % SZS output end CNFRefutation for theBenchmark.p
% 55.09/7.51  
% 55.09/7.51  ------                               Statistics
% 55.09/7.51  
% 55.09/7.51  ------ General
% 55.09/7.51  
% 55.09/7.51  abstr_ref_over_cycles:                  0
% 55.09/7.51  abstr_ref_under_cycles:                 0
% 55.09/7.51  gc_basic_clause_elim:                   0
% 55.09/7.51  forced_gc_time:                         0
% 55.09/7.51  parsing_time:                           0.024
% 55.09/7.51  unif_index_cands_time:                  0.
% 55.09/7.51  unif_index_add_time:                    0.
% 55.09/7.51  orderings_time:                         0.
% 55.09/7.51  out_proof_time:                         0.016
% 55.09/7.51  total_time:                             6.516
% 55.09/7.51  num_of_symbols:                         42
% 55.09/7.51  num_of_terms:                           137483
% 55.09/7.51  
% 55.09/7.51  ------ Preprocessing
% 55.09/7.51  
% 55.09/7.51  num_of_splits:                          0
% 55.09/7.51  num_of_split_atoms:                     0
% 55.09/7.51  num_of_reused_defs:                     0
% 55.09/7.51  num_eq_ax_congr_red:                    66
% 55.09/7.51  num_of_sem_filtered_clauses:            1
% 55.09/7.51  num_of_subtypes:                        0
% 55.09/7.51  monotx_restored_types:                  0
% 55.09/7.51  sat_num_of_epr_types:                   0
% 55.09/7.51  sat_num_of_non_cyclic_types:            0
% 55.09/7.51  sat_guarded_non_collapsed_types:        0
% 55.09/7.51  num_pure_diseq_elim:                    0
% 55.09/7.51  simp_replaced_by:                       0
% 55.09/7.51  res_preprocessed:                       107
% 55.09/7.51  prep_upred:                             0
% 55.09/7.51  prep_unflattend:                        451
% 55.09/7.51  smt_new_axioms:                         0
% 55.09/7.51  pred_elim_cands:                        4
% 55.09/7.51  pred_elim:                              0
% 55.09/7.51  pred_elim_cl:                           0
% 55.09/7.51  pred_elim_cycles:                       3
% 55.09/7.51  merged_defs:                            0
% 55.09/7.51  merged_defs_ncl:                        0
% 55.09/7.51  bin_hyper_res:                          0
% 55.09/7.51  prep_cycles:                            3
% 55.09/7.51  pred_elim_time:                         0.024
% 55.09/7.51  splitting_time:                         0.
% 55.09/7.51  sem_filter_time:                        0.
% 55.09/7.51  monotx_time:                            0.001
% 55.09/7.51  subtype_inf_time:                       0.
% 55.09/7.51  
% 55.09/7.51  ------ Problem properties
% 55.09/7.51  
% 55.09/7.51  clauses:                                30
% 55.09/7.51  conjectures:                            2
% 55.09/7.51  epr:                                    14
% 55.09/7.51  horn:                                   27
% 55.09/7.51  ground:                                 2
% 55.09/7.51  unary:                                  19
% 55.09/7.51  binary:                                 4
% 55.09/7.51  lits:                                   56
% 55.09/7.51  lits_eq:                                22
% 55.09/7.51  fd_pure:                                0
% 55.09/7.51  fd_pseudo:                              0
% 55.09/7.51  fd_cond:                                0
% 55.09/7.51  fd_pseudo_cond:                         4
% 55.09/7.51  ac_symbols:                             1
% 55.09/7.51  
% 55.09/7.51  ------ Propositional Solver
% 55.09/7.51  
% 55.09/7.51  prop_solver_calls:                      49
% 55.09/7.51  prop_fast_solver_calls:                 1259
% 55.09/7.51  smt_solver_calls:                       0
% 55.09/7.51  smt_fast_solver_calls:                  0
% 55.09/7.51  prop_num_of_clauses:                    48134
% 55.09/7.51  prop_preprocess_simplified:             60674
% 55.09/7.51  prop_fo_subsumed:                       0
% 55.09/7.51  prop_solver_time:                       0.
% 55.09/7.51  smt_solver_time:                        0.
% 55.09/7.51  smt_fast_solver_time:                   0.
% 55.09/7.51  prop_fast_solver_time:                  0.
% 55.09/7.51  prop_unsat_core_time:                   0.003
% 55.09/7.51  
% 55.09/7.51  ------ QBF
% 55.09/7.51  
% 55.09/7.51  qbf_q_res:                              0
% 55.09/7.51  qbf_num_tautologies:                    0
% 55.09/7.51  qbf_prep_cycles:                        0
% 55.09/7.51  
% 55.09/7.51  ------ BMC1
% 55.09/7.51  
% 55.09/7.51  bmc1_current_bound:                     -1
% 55.09/7.51  bmc1_last_solved_bound:                 -1
% 55.09/7.51  bmc1_unsat_core_size:                   -1
% 55.09/7.51  bmc1_unsat_core_parents_size:           -1
% 55.09/7.51  bmc1_merge_next_fun:                    0
% 55.09/7.51  bmc1_unsat_core_clauses_time:           0.
% 55.09/7.51  
% 55.09/7.51  ------ Instantiation
% 55.09/7.51  
% 55.09/7.51  inst_num_of_clauses:                    6003
% 55.09/7.51  inst_num_in_passive:                    2654
% 55.09/7.51  inst_num_in_active:                     1254
% 55.09/7.51  inst_num_in_unprocessed:                2095
% 55.09/7.51  inst_num_of_loops:                      1450
% 55.09/7.51  inst_num_of_learning_restarts:          0
% 55.09/7.51  inst_num_moves_active_passive:          194
% 55.09/7.51  inst_lit_activity:                      0
% 55.09/7.51  inst_lit_activity_moves:                0
% 55.09/7.51  inst_num_tautologies:                   0
% 55.09/7.51  inst_num_prop_implied:                  0
% 55.09/7.51  inst_num_existing_simplified:           0
% 55.09/7.51  inst_num_eq_res_simplified:             0
% 55.09/7.51  inst_num_child_elim:                    0
% 55.09/7.51  inst_num_of_dismatching_blockings:      6991
% 55.09/7.51  inst_num_of_non_proper_insts:           6184
% 55.09/7.51  inst_num_of_duplicates:                 0
% 55.09/7.51  inst_inst_num_from_inst_to_res:         0
% 55.09/7.51  inst_dismatching_checking_time:         0.
% 55.09/7.51  
% 55.09/7.51  ------ Resolution
% 55.09/7.51  
% 55.09/7.51  res_num_of_clauses:                     0
% 55.09/7.51  res_num_in_passive:                     0
% 55.09/7.51  res_num_in_active:                      0
% 55.09/7.51  res_num_of_loops:                       110
% 55.09/7.51  res_forward_subset_subsumed:            1849
% 55.09/7.51  res_backward_subset_subsumed:           12
% 55.09/7.51  res_forward_subsumed:                   0
% 55.09/7.51  res_backward_subsumed:                  0
% 55.09/7.51  res_forward_subsumption_resolution:     0
% 55.09/7.51  res_backward_subsumption_resolution:    0
% 55.09/7.51  res_clause_to_clause_subsumption:       575301
% 55.09/7.51  res_orphan_elimination:                 0
% 55.09/7.51  res_tautology_del:                      139
% 55.09/7.51  res_num_eq_res_simplified:              0
% 55.09/7.51  res_num_sel_changes:                    0
% 55.09/7.51  res_moves_from_active_to_pass:          0
% 55.09/7.51  
% 55.09/7.51  ------ Superposition
% 55.09/7.51  
% 55.09/7.51  sup_time_total:                         0.
% 55.09/7.51  sup_time_generating:                    0.
% 55.09/7.51  sup_time_sim_full:                      0.
% 55.09/7.51  sup_time_sim_immed:                     0.
% 55.09/7.51  
% 55.09/7.51  sup_num_of_clauses:                     11094
% 55.09/7.51  sup_num_in_active:                      280
% 55.09/7.51  sup_num_in_passive:                     10814
% 55.09/7.51  sup_num_of_loops:                       288
% 55.09/7.51  sup_fw_superposition:                   21659
% 55.09/7.51  sup_bw_superposition:                   6169
% 55.09/7.51  sup_immediate_simplified:               11707
% 55.09/7.51  sup_given_eliminated:                   1
% 55.09/7.51  comparisons_done:                       0
% 55.09/7.51  comparisons_avoided:                    2
% 55.09/7.51  
% 55.09/7.51  ------ Simplifications
% 55.09/7.51  
% 55.09/7.51  
% 55.09/7.51  sim_fw_subset_subsumed:                 0
% 55.09/7.51  sim_bw_subset_subsumed:                 0
% 55.09/7.51  sim_fw_subsumed:                        2071
% 55.09/7.51  sim_bw_subsumed:                        360
% 55.09/7.51  sim_fw_subsumption_res:                 0
% 55.09/7.51  sim_bw_subsumption_res:                 0
% 55.09/7.51  sim_tautology_del:                      242
% 55.09/7.51  sim_eq_tautology_del:                   115
% 55.09/7.51  sim_eq_res_simp:                        0
% 55.09/7.51  sim_fw_demodulated:                     8475
% 55.09/7.51  sim_bw_demodulated:                     302
% 55.09/7.51  sim_light_normalised:                   4771
% 55.09/7.51  sim_joinable_taut:                      253
% 55.09/7.51  sim_joinable_simp:                      0
% 55.09/7.51  sim_ac_normalised:                      0
% 55.09/7.51  sim_smt_subsumption:                    0
% 55.09/7.51  
%------------------------------------------------------------------------------
