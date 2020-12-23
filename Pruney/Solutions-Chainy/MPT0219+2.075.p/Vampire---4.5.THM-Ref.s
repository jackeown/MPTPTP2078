%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:31 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 166 expanded)
%              Number of leaves         :   19 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  255 ( 366 expanded)
%              Number of equality atoms :  168 ( 275 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f857,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f856])).

fof(f856,plain,(
    sK2 != sK2 ),
    inference(superposition,[],[f40,f837])).

fof(f837,plain,(
    sK2 = sK3 ),
    inference(resolution,[],[f827,f96])).

fof(f96,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8,X9) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f827,plain,(
    ! [X0] :
      ( ~ sP0(X0,sK3,sK3,sK3,sK2,sK2,sK2,sK2,sK2,sK2)
      | sK2 = X0 ) ),
    inference(resolution,[],[f802,f327])).

fof(f327,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | ~ sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X10))
      | X0 = X10 ) ),
    inference(resolution,[],[f55,f95])).

fof(f95,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f45,f82])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f81])).

fof(f81,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f74,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f53,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f52,f75])).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | ~ sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | ( ( ~ sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
          & ( sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X9)
              | ~ sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X11,X9) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).

fof(f33,plain,(
    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X10] :
          ( ( ~ sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X10,X9) )
          & ( sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X10,X9) ) )
     => ( ( ~ sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
        & ( sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f802,plain,(
    sP1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK3,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(superposition,[],[f416,f186])).

fof(f186,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) ),
    inference(forward_demodulation,[],[f84,f73])).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f84,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f39,f82,f76,f82,f82])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f42,f71])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f39,plain,(
    k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( sK2 != sK3
    & k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK2 != sK3
      & k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f416,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : sP1(X3,X4,X5,X6,X7,X8,X0,X1,X2,k5_xboole_0(k6_enumset1(X3,X3,X3,X4,X5,X6,X7,X8),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k6_enumset1(X3,X3,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))))) ),
    inference(superposition,[],[f105,f73])).

fof(f105,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))))) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) != X9 ) ),
    inference(definition_unfolding,[],[f68,f83])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) ),
    inference(definition_unfolding,[],[f41,f76,f77,f80])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) ) ),
    inference(definition_folding,[],[f21,f23,f22])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_enumset1)).

fof(f40,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:07:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (5719)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (5721)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.19/0.52  % (5716)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.19/0.52  % (5717)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.19/0.52  % (5714)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.19/0.52  % (5715)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.19/0.52  % (5723)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.19/0.52  % (5724)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.19/0.53  % (5722)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.19/0.53  % (5741)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.19/0.54  % (5734)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.19/0.54  % (5732)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.19/0.54  % (5726)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.19/0.54  % (5724)Refutation not found, incomplete strategy% (5724)------------------------------
% 1.19/0.54  % (5724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.54  % (5724)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.54  
% 1.19/0.54  % (5724)Memory used [KB]: 10618
% 1.19/0.54  % (5724)Time elapsed: 0.131 s
% 1.19/0.54  % (5724)------------------------------
% 1.19/0.54  % (5724)------------------------------
% 1.19/0.54  % (5738)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.19/0.54  % (5713)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.19/0.54  % (5740)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.19/0.54  % (5712)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.19/0.54  % (5713)Refutation not found, incomplete strategy% (5713)------------------------------
% 1.19/0.54  % (5713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.54  % (5713)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.54  
% 1.19/0.54  % (5713)Memory used [KB]: 1663
% 1.19/0.54  % (5713)Time elapsed: 0.124 s
% 1.19/0.54  % (5713)------------------------------
% 1.19/0.54  % (5713)------------------------------
% 1.19/0.54  % (5729)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.39/0.54  % (5720)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.39/0.54  % (5739)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.39/0.54  % (5733)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.39/0.55  % (5718)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.55  % (5731)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.39/0.55  % (5741)Refutation not found, incomplete strategy% (5741)------------------------------
% 1.39/0.55  % (5741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (5741)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (5741)Memory used [KB]: 1663
% 1.39/0.55  % (5741)Time elapsed: 0.003 s
% 1.39/0.55  % (5741)------------------------------
% 1.39/0.55  % (5741)------------------------------
% 1.39/0.55  % (5725)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.39/0.55  % (5736)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.39/0.55  % (5737)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.39/0.56  % (5730)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.39/0.56  % (5735)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.39/0.56  % (5727)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.39/0.57  % (5728)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.39/0.57  % (5728)Refutation not found, incomplete strategy% (5728)------------------------------
% 1.39/0.57  % (5728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.57  % (5728)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.57  
% 1.39/0.57  % (5728)Memory used [KB]: 10746
% 1.39/0.57  % (5728)Time elapsed: 0.160 s
% 1.39/0.57  % (5728)------------------------------
% 1.39/0.57  % (5728)------------------------------
% 1.39/0.63  % (5717)Refutation found. Thanks to Tanya!
% 1.39/0.63  % SZS status Theorem for theBenchmark
% 2.02/0.65  % SZS output start Proof for theBenchmark
% 2.02/0.65  fof(f857,plain,(
% 2.02/0.65    $false),
% 2.02/0.65    inference(trivial_inequality_removal,[],[f856])).
% 2.02/0.65  fof(f856,plain,(
% 2.02/0.65    sK2 != sK2),
% 2.02/0.65    inference(superposition,[],[f40,f837])).
% 2.02/0.65  fof(f837,plain,(
% 2.02/0.65    sK2 = sK3),
% 2.02/0.65    inference(resolution,[],[f827,f96])).
% 2.02/0.65  fof(f96,plain,(
% 2.02/0.65    ( ! [X6,X4,X2,X8,X7,X5,X3,X1,X9] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 2.02/0.65    inference(equality_resolution,[],[f67])).
% 2.02/0.65  fof(f67,plain,(
% 2.02/0.65    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | X0 != X1) )),
% 2.02/0.65    inference(cnf_transformation,[],[f37])).
% 2.02/0.65  fof(f37,plain,(
% 2.02/0.65    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8 & X0 != X9)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | X0 = X9 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 2.02/0.65    inference(rectify,[],[f36])).
% 2.02/0.65  fof(f36,plain,(
% 2.02/0.65    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.02/0.65    inference(flattening,[],[f35])).
% 2.02/0.65  fof(f35,plain,(
% 2.02/0.65    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.02/0.65    inference(nnf_transformation,[],[f22])).
% 2.02/0.65  fof(f22,plain,(
% 2.02/0.65    ! [X10,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10))),
% 2.02/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.02/0.65  fof(f827,plain,(
% 2.02/0.65    ( ! [X0] : (~sP0(X0,sK3,sK3,sK3,sK2,sK2,sK2,sK2,sK2,sK2) | sK2 = X0) )),
% 2.02/0.65    inference(resolution,[],[f802,f327])).
% 2.02/0.65  fof(f327,plain,(
% 2.02/0.65    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : (~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ~sP1(X9,X8,X7,X6,X5,X4,X3,X2,X1,k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X10)) | X0 = X10) )),
% 2.02/0.65    inference(resolution,[],[f55,f95])).
% 2.02/0.65  fof(f95,plain,(
% 2.02/0.65    ( ! [X0,X3] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X3) )),
% 2.02/0.65    inference(equality_resolution,[],[f90])).
% 2.02/0.65  fof(f90,plain,(
% 2.02/0.65    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 2.02/0.65    inference(definition_unfolding,[],[f45,f82])).
% 2.02/0.65  fof(f82,plain,(
% 2.02/0.65    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.02/0.65    inference(definition_unfolding,[],[f49,f81])).
% 2.02/0.65  fof(f81,plain,(
% 2.02/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.02/0.65    inference(definition_unfolding,[],[f51,f80])).
% 2.02/0.65  fof(f80,plain,(
% 2.02/0.65    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.02/0.65    inference(definition_unfolding,[],[f50,f79])).
% 2.02/0.65  fof(f79,plain,(
% 2.02/0.65    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.02/0.65    inference(definition_unfolding,[],[f74,f78])).
% 2.02/0.65  fof(f78,plain,(
% 2.02/0.65    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.02/0.65    inference(definition_unfolding,[],[f53,f77])).
% 2.02/0.65  fof(f77,plain,(
% 2.02/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.02/0.65    inference(definition_unfolding,[],[f52,f75])).
% 2.02/0.65  fof(f75,plain,(
% 2.02/0.65    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f17])).
% 2.02/0.65  fof(f17,axiom,(
% 2.02/0.65    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.02/0.65  fof(f52,plain,(
% 2.02/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f16])).
% 2.02/0.65  fof(f16,axiom,(
% 2.02/0.65    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.02/0.65  fof(f53,plain,(
% 2.02/0.65    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f15])).
% 2.02/0.65  fof(f15,axiom,(
% 2.02/0.65    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.02/0.65  fof(f74,plain,(
% 2.02/0.65    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f14])).
% 2.02/0.65  fof(f14,axiom,(
% 2.02/0.65    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.02/0.65  fof(f50,plain,(
% 2.02/0.65    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f13])).
% 2.02/0.65  fof(f13,axiom,(
% 2.02/0.65    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.02/0.65  fof(f51,plain,(
% 2.02/0.65    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f12])).
% 2.02/0.65  fof(f12,axiom,(
% 2.02/0.65    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.02/0.65  fof(f49,plain,(
% 2.02/0.65    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f11])).
% 2.02/0.65  fof(f11,axiom,(
% 2.02/0.65    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.02/0.65  fof(f45,plain,(
% 2.02/0.65    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.02/0.65    inference(cnf_transformation,[],[f30])).
% 2.02/0.65  fof(f30,plain,(
% 2.02/0.65    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.02/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 2.02/0.65  fof(f29,plain,(
% 2.02/0.65    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 2.02/0.65    introduced(choice_axiom,[])).
% 2.02/0.65  fof(f28,plain,(
% 2.02/0.65    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.02/0.65    inference(rectify,[],[f27])).
% 2.02/0.65  fof(f27,plain,(
% 2.02/0.65    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.02/0.65    inference(nnf_transformation,[],[f8])).
% 2.02/0.65  fof(f8,axiom,(
% 2.02/0.65    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.02/0.65  fof(f55,plain,(
% 2.02/0.65    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f34])).
% 2.02/0.65  fof(f34,plain,(
% 2.02/0.65    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ((~sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)))) & (! [X11] : ((r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 2.02/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).
% 2.02/0.65  fof(f33,plain,(
% 2.02/0.65    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9))) => ((~sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sP0(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9))))),
% 2.02/0.65    introduced(choice_axiom,[])).
% 2.02/0.65  fof(f32,plain,(
% 2.02/0.65    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9)))) & (! [X11] : ((r2_hidden(X11,X9) | ~sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X11,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X11,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 2.02/0.65    inference(rectify,[],[f31])).
% 2.02/0.65  fof(f31,plain,(
% 2.02/0.65    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | ? [X10] : ((~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | ~sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X9))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)))),
% 2.02/0.65    inference(nnf_transformation,[],[f23])).
% 2.02/0.66  fof(f23,plain,(
% 2.02/0.66    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) <=> ! [X10] : (r2_hidden(X10,X9) <=> sP0(X10,X8,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.02/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.02/0.66  fof(f802,plain,(
% 2.02/0.66    sP1(sK2,sK2,sK2,sK2,sK2,sK2,sK3,sK3,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 2.02/0.66    inference(superposition,[],[f416,f186])).
% 2.02/0.66  fof(f186,plain,(
% 2.02/0.66    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))),
% 2.02/0.66    inference(forward_demodulation,[],[f84,f73])).
% 2.02/0.66  fof(f73,plain,(
% 2.02/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.02/0.66    inference(cnf_transformation,[],[f1])).
% 2.02/0.66  fof(f1,axiom,(
% 2.02/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.02/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.02/0.66  fof(f84,plain,(
% 2.02/0.66    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 2.02/0.66    inference(definition_unfolding,[],[f39,f82,f76,f82,f82])).
% 2.02/0.66  fof(f76,plain,(
% 2.02/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.02/0.66    inference(definition_unfolding,[],[f42,f71])).
% 2.02/0.66  fof(f71,plain,(
% 2.02/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.02/0.66    inference(cnf_transformation,[],[f2])).
% 2.02/0.66  fof(f2,axiom,(
% 2.02/0.66    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.02/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.02/0.66  fof(f42,plain,(
% 2.02/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.02/0.66    inference(cnf_transformation,[],[f7])).
% 2.02/0.66  fof(f7,axiom,(
% 2.02/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.02/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.02/0.66  fof(f39,plain,(
% 2.02/0.66    k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),
% 2.02/0.66    inference(cnf_transformation,[],[f26])).
% 2.02/0.66  fof(f26,plain,(
% 2.02/0.66    sK2 != sK3 & k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),
% 2.02/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f25])).
% 2.02/0.66  fof(f25,plain,(
% 2.02/0.66    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK2 != sK3 & k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),
% 2.02/0.66    introduced(choice_axiom,[])).
% 2.02/0.66  fof(f20,plain,(
% 2.02/0.66    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 2.02/0.66    inference(ennf_transformation,[],[f19])).
% 2.02/0.66  fof(f19,negated_conjecture,(
% 2.02/0.66    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.02/0.66    inference(negated_conjecture,[],[f18])).
% 2.02/0.66  fof(f18,conjecture,(
% 2.02/0.66    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.02/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 2.02/0.66  fof(f416,plain,(
% 2.02/0.66    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X3,X4,X5,X6,X7,X8,X0,X1,X2,k5_xboole_0(k6_enumset1(X3,X3,X3,X4,X5,X6,X7,X8),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k3_xboole_0(k6_enumset1(X3,X3,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)))))) )),
% 2.02/0.66    inference(superposition,[],[f105,f73])).
% 2.02/0.66  fof(f105,plain,(
% 2.02/0.66    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))))) )),
% 2.02/0.66    inference(equality_resolution,[],[f92])).
% 2.02/0.66  fof(f92,plain,(
% 2.02/0.66    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) != X9) )),
% 2.02/0.66    inference(definition_unfolding,[],[f68,f83])).
% 2.02/0.66  fof(f83,plain,(
% 2.02/0.66    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))))) )),
% 2.02/0.66    inference(definition_unfolding,[],[f41,f76,f77,f80])).
% 2.02/0.66  fof(f41,plain,(
% 2.02/0.66    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))) )),
% 2.02/0.66    inference(cnf_transformation,[],[f10])).
% 2.02/0.66  fof(f10,axiom,(
% 2.02/0.66    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 2.02/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).
% 2.02/0.66  fof(f68,plain,(
% 2.02/0.66    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 2.02/0.66    inference(cnf_transformation,[],[f38])).
% 2.02/0.66  fof(f38,plain,(
% 2.02/0.66    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 2.02/0.66    inference(nnf_transformation,[],[f24])).
% 2.02/0.66  fof(f24,plain,(
% 2.02/0.66    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9))),
% 2.02/0.66    inference(definition_folding,[],[f21,f23,f22])).
% 2.02/0.66  fof(f21,plain,(
% 2.02/0.66    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10)))),
% 2.02/0.66    inference(ennf_transformation,[],[f9])).
% 2.02/0.66  fof(f9,axiom,(
% 2.02/0.66    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> ~(X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)))),
% 2.02/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_enumset1)).
% 2.02/0.66  fof(f40,plain,(
% 2.02/0.66    sK2 != sK3),
% 2.02/0.66    inference(cnf_transformation,[],[f26])).
% 2.02/0.66  % SZS output end Proof for theBenchmark
% 2.02/0.66  % (5717)------------------------------
% 2.02/0.66  % (5717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.66  % (5717)Termination reason: Refutation
% 2.02/0.66  
% 2.02/0.66  % (5717)Memory used [KB]: 2686
% 2.02/0.66  % (5717)Time elapsed: 0.204 s
% 2.02/0.66  % (5717)------------------------------
% 2.02/0.66  % (5717)------------------------------
% 2.02/0.66  % (5711)Success in time 0.292 s
%------------------------------------------------------------------------------
