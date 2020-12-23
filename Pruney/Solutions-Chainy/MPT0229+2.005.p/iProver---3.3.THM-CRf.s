%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:36 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 160 expanded)
%              Number of clauses        :   23 (  23 expanded)
%              Number of leaves         :   21 (  46 expanded)
%              Depth                    :   17
%              Number of atoms          :  285 ( 370 expanded)
%              Number of equality atoms :  183 ( 258 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f24,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK4 != sK5
      & r1_tarski(k1_tarski(sK4),k1_tarski(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( sK4 != sK5
    & r1_tarski(k1_tarski(sK4),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f24,f40])).

fof(f78,plain,(
    r1_tarski(k1_tarski(sK4),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f75,f76])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f74,f81])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f73,f82])).

fof(f84,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f72,f83])).

fof(f85,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f71,f84])).

fof(f86,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f70,f85])).

fof(f95,plain,(
    r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f78,f86,f86])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f23,plain,(
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

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
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

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(definition_folding,[],[f23,f26,f25])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f80,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f48,f43])).

fof(f87,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(definition_unfolding,[],[f69,f80,f86])).

fof(f93,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) != X9 ) ),
    inference(definition_unfolding,[],[f67,f87])).

fof(f108,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) ),
    inference(equality_resolution,[],[f93])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f99,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(equality_resolution,[],[f66])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | ~ sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f49,f86])).

fof(f98,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f91])).

fof(f79,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_27,negated_conjecture,
    ( r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1526,plain,
    ( r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1548,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1714,plain,
    ( k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(superposition,[status(thm)],[c_1526,c_1548])).

cnf(c_24,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1528,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3943,plain,
    ( sP1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1714,c_1528])).

cnf(c_9737,plain,
    ( sP1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_3943])).

cnf(c_9937,plain,
    ( sP1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_9737])).

cnf(c_13,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1539,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7,X8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
    | ~ sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10)
    | r2_hidden(X0,X10) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1541,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != iProver_top
    | sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10) != iProver_top
    | r2_hidden(X0,X10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3305,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != iProver_top
    | r2_hidden(X8,X9) = iProver_top ),
    inference(superposition,[status(thm)],[c_1539,c_1541])).

cnf(c_9974,plain,
    ( r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9937,c_3305])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1632,plain,
    ( ~ r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1633,plain,
    ( sK4 = sK5
    | r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1632])).

cnf(c_26,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f79])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9974,c_1633,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:29:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.79/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.01  
% 3.79/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.79/1.01  
% 3.79/1.01  ------  iProver source info
% 3.79/1.01  
% 3.79/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.79/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.79/1.01  git: non_committed_changes: false
% 3.79/1.01  git: last_make_outside_of_git: false
% 3.79/1.01  
% 3.79/1.01  ------ 
% 3.79/1.01  ------ Parsing...
% 3.79/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.79/1.01  
% 3.79/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.79/1.01  
% 3.79/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.79/1.01  
% 3.79/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.79/1.01  ------ Proving...
% 3.79/1.01  ------ Problem Properties 
% 3.79/1.01  
% 3.79/1.01  
% 3.79/1.01  clauses                                 28
% 3.79/1.01  conjectures                             2
% 3.79/1.01  EPR                                     13
% 3.79/1.01  Horn                                    25
% 3.79/1.01  unary                                   17
% 3.79/1.01  binary                                  4
% 3.79/1.01  lits                                    53
% 3.79/1.01  lits eq                                 20
% 3.79/1.01  fd_pure                                 0
% 3.79/1.01  fd_pseudo                               0
% 3.79/1.01  fd_cond                                 0
% 3.79/1.01  fd_pseudo_cond                          4
% 3.79/1.01  AC symbols                              0
% 3.79/1.01  
% 3.79/1.01  ------ Input Options Time Limit: Unbounded
% 3.79/1.01  
% 3.79/1.01  
% 3.79/1.01  ------ 
% 3.79/1.01  Current options:
% 3.79/1.01  ------ 
% 3.79/1.01  
% 3.79/1.01  
% 3.79/1.01  
% 3.79/1.01  
% 3.79/1.01  ------ Proving...
% 3.79/1.01  
% 3.79/1.01  
% 3.79/1.01  % SZS status Theorem for theBenchmark.p
% 3.79/1.01  
% 3.79/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.79/1.01  
% 3.79/1.01  fof(f5,axiom,(
% 3.79/1.01    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.79/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.01  
% 3.79/1.01  fof(f46,plain,(
% 3.79/1.01    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.79/1.01    inference(cnf_transformation,[],[f5])).
% 3.79/1.01  
% 3.79/1.01  fof(f6,axiom,(
% 3.79/1.01    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.79/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.01  
% 3.79/1.01  fof(f47,plain,(
% 3.79/1.01    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.79/1.01    inference(cnf_transformation,[],[f6])).
% 3.79/1.01  
% 3.79/1.01  fof(f19,conjecture,(
% 3.79/1.01    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 3.79/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.01  
% 3.79/1.01  fof(f20,negated_conjecture,(
% 3.79/1.01    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 3.79/1.01    inference(negated_conjecture,[],[f19])).
% 3.79/1.01  
% 3.79/1.01  fof(f24,plain,(
% 3.79/1.01    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 3.79/1.01    inference(ennf_transformation,[],[f20])).
% 3.79/1.01  
% 3.79/1.01  fof(f40,plain,(
% 3.79/1.01    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK4 != sK5 & r1_tarski(k1_tarski(sK4),k1_tarski(sK5)))),
% 3.79/1.01    introduced(choice_axiom,[])).
% 3.79/1.01  
% 3.79/1.01  fof(f41,plain,(
% 3.79/1.01    sK4 != sK5 & r1_tarski(k1_tarski(sK4),k1_tarski(sK5))),
% 3.79/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f24,f40])).
% 3.79/1.01  
% 3.79/1.01  fof(f78,plain,(
% 3.79/1.01    r1_tarski(k1_tarski(sK4),k1_tarski(sK5))),
% 3.79/1.01    inference(cnf_transformation,[],[f41])).
% 3.79/1.01  
% 3.79/1.01  fof(f11,axiom,(
% 3.79/1.01    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.79/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.01  
% 3.79/1.01  fof(f70,plain,(
% 3.79/1.01    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.79/1.01    inference(cnf_transformation,[],[f11])).
% 3.79/1.01  
% 3.79/1.01  fof(f12,axiom,(
% 3.79/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.79/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.01  
% 3.79/1.01  fof(f71,plain,(
% 3.79/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.79/1.01    inference(cnf_transformation,[],[f12])).
% 3.79/1.01  
% 3.79/1.01  fof(f13,axiom,(
% 3.79/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.79/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.01  
% 3.79/1.01  fof(f72,plain,(
% 3.79/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.79/1.01    inference(cnf_transformation,[],[f13])).
% 3.79/1.01  
% 3.79/1.01  fof(f14,axiom,(
% 3.79/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.79/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.01  
% 3.79/1.01  fof(f73,plain,(
% 3.79/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.79/1.01    inference(cnf_transformation,[],[f14])).
% 3.79/1.01  
% 3.79/1.01  fof(f15,axiom,(
% 3.79/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.79/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.01  
% 3.79/1.01  fof(f74,plain,(
% 3.79/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.79/1.01    inference(cnf_transformation,[],[f15])).
% 3.79/1.01  
% 3.79/1.01  fof(f16,axiom,(
% 3.79/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.79/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.01  
% 3.79/1.01  fof(f75,plain,(
% 3.79/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.79/1.01    inference(cnf_transformation,[],[f16])).
% 3.79/1.01  
% 3.79/1.01  fof(f17,axiom,(
% 3.79/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.79/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.01  
% 3.79/1.01  fof(f76,plain,(
% 3.79/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.79/1.01    inference(cnf_transformation,[],[f17])).
% 3.79/1.01  
% 3.79/1.01  fof(f81,plain,(
% 3.79/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.79/1.01    inference(definition_unfolding,[],[f75,f76])).
% 3.79/1.01  
% 3.79/1.01  fof(f82,plain,(
% 3.79/1.01    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.79/1.01    inference(definition_unfolding,[],[f74,f81])).
% 3.79/1.01  
% 3.79/1.01  fof(f83,plain,(
% 3.79/1.01    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.79/1.01    inference(definition_unfolding,[],[f73,f82])).
% 3.79/1.01  
% 3.79/1.01  fof(f84,plain,(
% 3.79/1.01    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.79/1.01    inference(definition_unfolding,[],[f72,f83])).
% 3.79/1.01  
% 3.79/1.01  fof(f85,plain,(
% 3.79/1.01    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.79/1.01    inference(definition_unfolding,[],[f71,f84])).
% 3.79/1.01  
% 3.79/1.01  fof(f86,plain,(
% 3.79/1.01    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.79/1.01    inference(definition_unfolding,[],[f70,f85])).
% 3.79/1.01  
% 3.79/1.01  fof(f95,plain,(
% 3.79/1.01    r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))),
% 3.79/1.01    inference(definition_unfolding,[],[f78,f86,f86])).
% 3.79/1.01  
% 3.79/1.01  fof(f4,axiom,(
% 3.79/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.79/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.01  
% 3.79/1.01  fof(f22,plain,(
% 3.79/1.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.79/1.01    inference(ennf_transformation,[],[f4])).
% 3.79/1.01  
% 3.79/1.01  fof(f45,plain,(
% 3.79/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.79/1.01    inference(cnf_transformation,[],[f22])).
% 3.79/1.01  
% 3.79/1.01  fof(f9,axiom,(
% 3.79/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> ~(X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)))),
% 3.79/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.01  
% 3.79/1.01  fof(f23,plain,(
% 3.79/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10)))),
% 3.79/1.01    inference(ennf_transformation,[],[f9])).
% 3.79/1.01  
% 3.79/1.01  fof(f26,plain,(
% 3.79/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) <=> ! [X10] : (r2_hidden(X10,X9) <=> sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.79/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.79/1.01  
% 3.79/1.01  fof(f25,plain,(
% 3.79/1.01    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10))),
% 3.79/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.79/1.01  
% 3.79/1.01  fof(f27,plain,(
% 3.79/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9))),
% 3.79/1.01    inference(definition_folding,[],[f23,f26,f25])).
% 3.79/1.01  
% 3.79/1.01  fof(f39,plain,(
% 3.79/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 3.79/1.01    inference(nnf_transformation,[],[f27])).
% 3.79/1.01  
% 3.79/1.01  fof(f67,plain,(
% 3.79/1.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 3.79/1.01    inference(cnf_transformation,[],[f39])).
% 3.79/1.01  
% 3.79/1.01  fof(f10,axiom,(
% 3.79/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 3.79/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.01  
% 3.79/1.01  fof(f69,plain,(
% 3.79/1.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.79/1.01    inference(cnf_transformation,[],[f10])).
% 3.79/1.01  
% 3.79/1.01  fof(f7,axiom,(
% 3.79/1.01    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.79/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.01  
% 3.79/1.01  fof(f48,plain,(
% 3.79/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.79/1.01    inference(cnf_transformation,[],[f7])).
% 3.79/1.01  
% 3.79/1.01  fof(f2,axiom,(
% 3.79/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.79/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.01  
% 3.79/1.01  fof(f43,plain,(
% 3.79/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.79/1.01    inference(cnf_transformation,[],[f2])).
% 3.79/1.01  
% 3.79/1.01  fof(f80,plain,(
% 3.79/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.79/1.01    inference(definition_unfolding,[],[f48,f43])).
% 3.79/1.01  
% 3.79/1.01  fof(f87,plain,(
% 3.79/1.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.79/1.01    inference(definition_unfolding,[],[f69,f80,f86])).
% 3.79/1.01  
% 3.79/1.01  fof(f93,plain,(
% 3.79/1.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))) != X9) )),
% 3.79/1.01    inference(definition_unfolding,[],[f67,f87])).
% 3.79/1.01  
% 3.79/1.01  fof(f108,plain,(
% 3.79/1.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)))))) )),
% 3.79/1.01    inference(equality_resolution,[],[f93])).
% 3.79/1.01  
% 3.79/1.01  fof(f36,plain,(
% 3.79/1.01    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.79/1.01    inference(nnf_transformation,[],[f25])).
% 3.79/1.01  
% 3.79/1.01  fof(f37,plain,(
% 3.79/1.01    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.79/1.01    inference(flattening,[],[f36])).
% 3.79/1.01  
% 3.79/1.01  fof(f38,plain,(
% 3.79/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8 & X0 != X9)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | X0 = X9 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 3.79/1.01    inference(rectify,[],[f37])).
% 3.79/1.01  
% 3.79/1.01  fof(f66,plain,(
% 3.79/1.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | X0 != X1) )),
% 3.79/1.01    inference(cnf_transformation,[],[f38])).
% 3.79/1.01  
% 3.79/1.01  fof(f99,plain,(
% 3.79/1.01    ( ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 3.79/1.01    inference(equality_resolution,[],[f66])).
% 3.79/1.01  
% 3.79/1.01  fof(f32,plain,(
% 3.79/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 3.79/1.01    inference(nnf_transformation,[],[f26])).
% 3.79/1.01  
% 3.79/1.01  fof(f33,plain,(
% 3.79/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9)))) & (! [X11] : ((r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 3.79/1.01    inference(rectify,[],[f32])).
% 3.79/1.01  
% 3.79/1.01  fof(f34,plain,(
% 3.79/1.01    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9))) => ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9))))),
% 3.79/1.01    introduced(choice_axiom,[])).
% 3.79/1.01  
% 3.79/1.01  fof(f35,plain,(
% 3.79/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)))) & (! [X11] : ((r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 3.79/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).
% 3.79/1.01  
% 3.79/1.01  fof(f54,plain,(
% 3.79/1.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 3.79/1.01    inference(cnf_transformation,[],[f35])).
% 3.79/1.01  
% 3.79/1.01  fof(f8,axiom,(
% 3.79/1.01    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.79/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/1.01  
% 3.79/1.01  fof(f28,plain,(
% 3.79/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.79/1.01    inference(nnf_transformation,[],[f8])).
% 3.79/1.01  
% 3.79/1.01  fof(f29,plain,(
% 3.79/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.79/1.01    inference(rectify,[],[f28])).
% 3.79/1.01  
% 3.79/1.01  fof(f30,plain,(
% 3.79/1.01    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 3.79/1.01    introduced(choice_axiom,[])).
% 3.79/1.01  
% 3.79/1.01  fof(f31,plain,(
% 3.79/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.79/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 3.79/1.01  
% 3.79/1.01  fof(f49,plain,(
% 3.79/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.79/1.01    inference(cnf_transformation,[],[f31])).
% 3.79/1.01  
% 3.79/1.01  fof(f91,plain,(
% 3.79/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 3.79/1.01    inference(definition_unfolding,[],[f49,f86])).
% 3.79/1.01  
% 3.79/1.01  fof(f98,plain,(
% 3.79/1.01    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 3.79/1.01    inference(equality_resolution,[],[f91])).
% 3.79/1.01  
% 3.79/1.01  fof(f79,plain,(
% 3.79/1.01    sK4 != sK5),
% 3.79/1.01    inference(cnf_transformation,[],[f41])).
% 3.79/1.01  
% 3.79/1.01  cnf(c_3,plain,
% 3.79/1.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.79/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.79/1.01  
% 3.79/1.01  cnf(c_4,plain,
% 3.79/1.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.79/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.79/1.01  
% 3.79/1.01  cnf(c_27,negated_conjecture,
% 3.79/1.01      ( r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
% 3.79/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.79/1.01  
% 3.79/1.01  cnf(c_1526,plain,
% 3.79/1.01      ( r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
% 3.79/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.79/1.01  
% 3.79/1.01  cnf(c_2,plain,
% 3.79/1.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.79/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.79/1.01  
% 3.79/1.01  cnf(c_1548,plain,
% 3.79/1.01      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.79/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.79/1.01  
% 3.79/1.01  cnf(c_1714,plain,
% 3.79/1.01      ( k3_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 3.79/1.01      inference(superposition,[status(thm)],[c_1526,c_1548]) ).
% 3.79/1.01  
% 3.79/1.01  cnf(c_24,plain,
% 3.79/1.01      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) ),
% 3.79/1.01      inference(cnf_transformation,[],[f108]) ).
% 3.79/1.01  
% 3.79/1.01  cnf(c_1528,plain,
% 3.79/1.01      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))))) = iProver_top ),
% 3.79/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.79/1.01  
% 3.79/1.01  cnf(c_3943,plain,
% 3.79/1.01      ( sP1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) = iProver_top ),
% 3.79/1.01      inference(superposition,[status(thm)],[c_1714,c_1528]) ).
% 3.79/1.01  
% 3.79/1.01  cnf(c_9737,plain,
% 3.79/1.01      ( sP1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_xboole_0)) = iProver_top ),
% 3.79/1.01      inference(superposition,[status(thm)],[c_4,c_3943]) ).
% 3.79/1.01  
% 3.79/1.01  cnf(c_9937,plain,
% 3.79/1.01      ( sP1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
% 3.79/1.01      inference(superposition,[status(thm)],[c_3,c_9737]) ).
% 3.79/1.01  
% 3.79/1.01  cnf(c_13,plain,
% 3.79/1.01      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
% 3.79/1.01      inference(cnf_transformation,[],[f99]) ).
% 3.79/1.01  
% 3.79/1.01  cnf(c_1539,plain,
% 3.79/1.01      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7,X8) = iProver_top ),
% 3.79/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.79/1.01  
% 3.79/1.01  cnf(c_11,plain,
% 3.79/1.01      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
% 3.79/1.01      | ~ sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10)
% 3.79/1.01      | r2_hidden(X0,X10) ),
% 3.79/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.79/1.01  
% 3.79/1.01  cnf(c_1541,plain,
% 3.79/1.01      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != iProver_top
% 3.79/1.01      | sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,X10) != iProver_top
% 3.79/1.01      | r2_hidden(X0,X10) = iProver_top ),
% 3.79/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.79/1.01  
% 3.79/1.01  cnf(c_3305,plain,
% 3.79/1.01      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != iProver_top
% 3.79/1.01      | r2_hidden(X8,X9) = iProver_top ),
% 3.79/1.01      inference(superposition,[status(thm)],[c_1539,c_1541]) ).
% 3.79/1.01  
% 3.79/1.01  cnf(c_9974,plain,
% 3.79/1.01      ( r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
% 3.79/1.01      inference(superposition,[status(thm)],[c_9937,c_3305]) ).
% 3.79/1.01  
% 3.79/1.01  cnf(c_8,plain,
% 3.79/1.01      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 3.79/1.01      inference(cnf_transformation,[],[f98]) ).
% 3.79/1.01  
% 3.79/1.01  cnf(c_1632,plain,
% 3.79/1.01      ( ~ r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 3.79/1.01      | sK4 = sK5 ),
% 3.79/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 3.79/1.01  
% 3.79/1.01  cnf(c_1633,plain,
% 3.79/1.01      ( sK4 = sK5
% 3.79/1.01      | r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top ),
% 3.79/1.01      inference(predicate_to_equality,[status(thm)],[c_1632]) ).
% 3.79/1.01  
% 3.79/1.01  cnf(c_26,negated_conjecture,
% 3.79/1.01      ( sK4 != sK5 ),
% 3.79/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.79/1.01  
% 3.79/1.01  cnf(contradiction,plain,
% 3.79/1.01      ( $false ),
% 3.79/1.01      inference(minisat,[status(thm)],[c_9974,c_1633,c_26]) ).
% 3.79/1.01  
% 3.79/1.01  
% 3.79/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.79/1.01  
% 3.79/1.01  ------                               Statistics
% 3.79/1.01  
% 3.79/1.01  ------ Selected
% 3.79/1.01  
% 3.79/1.01  total_time:                             0.423
% 3.79/1.01  
%------------------------------------------------------------------------------
