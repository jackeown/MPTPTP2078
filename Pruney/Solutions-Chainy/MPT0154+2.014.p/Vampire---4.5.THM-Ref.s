%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:33 EST 2020

% Result     : Theorem 3.10s
% Output     : Refutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 170 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :  232 ( 324 expanded)
%              Number of equality atoms :  101 ( 171 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4423,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f85,f4195,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_tarski(X2,X1))
      | ~ sP1(X0,X1,X2) ) ),
    inference(resolution,[],[f65,f86])).

fof(f86,plain,(
    ! [X0,X1] : sP2(X0,X1,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP2(X0,X1,X2) )
      & ( sP2(X0,X1,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP2(X0,X1,X2) ) ),
    inference(definition_folding,[],[f12,f25,f24])).

fof(f24,plain,(
    ! [X3,X1,X0] :
      ( sP1(X3,X1,X0)
    <=> ( X1 = X3
        | X0 = X3 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP1(X3,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ sP1(X4,X1,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ~ sP1(sK7(X0,X1,X2),X1,X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sP1(sK7(X0,X1,X2),X1,X0)
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X4,X1,X0) )
            & ( sP1(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP1(X3,X1,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP1(X3,X1,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP1(sK7(X0,X1,X2),X1,X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sP1(sK7(X0,X1,X2),X1,X0)
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X4,X1,X0) )
            & ( sP1(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP1(X3,X1,X0) )
            & ( sP1(X3,X1,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f4195,plain,(
    ~ r2_hidden(sK3,k2_tarski(sK3,sK4)) ),
    inference(resolution,[],[f4179,f1914])).

fof(f1914,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f1911])).

fof(f1911,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k2_tarski(X0,X0),X1)
      | r1_tarski(k2_tarski(X0,X0),X1) ) ),
    inference(superposition,[],[f55,f117])).

fof(f117,plain,(
    ! [X2,X1] :
      ( sK5(k2_tarski(X1,X1),X2) = X1
      | r1_tarski(k2_tarski(X1,X1),X2) ) ),
    inference(resolution,[],[f95,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_tarski(X1,X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f56,f83])).

fof(f83,plain,(
    ! [X0] : sP0(X0,k2_tarski(X0,X0)) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f60,f46])).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f11,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X3,X1)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4179,plain,(
    ~ r1_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK4)) ),
    inference(trivial_inequality_removal,[],[f4176])).

fof(f4176,plain,
    ( k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4)
    | ~ r1_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK4)) ),
    inference(superposition,[],[f75,f1847])).

fof(f1847,plain,(
    ! [X4,X3] :
      ( k5_xboole_0(X4,k4_xboole_0(X3,X4)) = X3
      | ~ r1_tarski(X4,X3) ) ),
    inference(superposition,[],[f659,f134])).

fof(f134,plain,(
    ! [X6,X5] :
      ( k4_xboole_0(X6,k4_xboole_0(X6,X5)) = X5
      | ~ r1_tarski(X5,X6) ) ),
    inference(superposition,[],[f77,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f48,f52,f52])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f659,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(forward_demodulation,[],[f636,f294])).

fof(f294,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f124,f267])).

fof(f267,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f133,f259])).

fof(f259,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f160,f74])).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f160,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[],[f78,f45])).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f78,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    inference(definition_unfolding,[],[f49,f50,f52])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f133,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f77,f45])).

fof(f124,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f74,f45])).

fof(f636,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[],[f131,f295])).

fof(f295,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f128,f267])).

fof(f128,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f74,f76])).

fof(f76,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f47,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f131,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[],[f63,f74])).

fof(f63,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f75,plain,(
    k2_tarski(sK3,sK4) != k5_xboole_0(k2_tarski(sK3,sK3),k4_xboole_0(k2_tarski(sK3,sK4),k2_tarski(sK3,sK3))) ),
    inference(definition_unfolding,[],[f44,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f62,f50,f46])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f44,plain,(
    k2_tarski(sK3,sK4) != k1_enumset1(sK3,sK3,sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    k2_tarski(sK3,sK4) != k1_enumset1(sK3,sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f19,f27])).

fof(f27,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK3,sK4) != k1_enumset1(sK3,sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f85,plain,(
    ! [X2,X1] : sP1(X2,X1,X2) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( X0 != X1
          & X0 != X2 ) )
      & ( X0 = X1
        | X0 = X2
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X3,X1,X0] :
      ( ( sP1(X3,X1,X0)
        | ( X1 != X3
          & X0 != X3 ) )
      & ( X1 = X3
        | X0 = X3
        | ~ sP1(X3,X1,X0) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X3,X1,X0] :
      ( ( sP1(X3,X1,X0)
        | ( X1 != X3
          & X0 != X3 ) )
      & ( X1 = X3
        | X0 = X3
        | ~ sP1(X3,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:41:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (21484)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (21500)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (21492)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (21480)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (21492)Refutation not found, incomplete strategy% (21492)------------------------------
% 0.21/0.51  % (21492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21492)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21492)Memory used [KB]: 10746
% 0.21/0.51  % (21492)Time elapsed: 0.105 s
% 0.21/0.51  % (21492)------------------------------
% 0.21/0.51  % (21492)------------------------------
% 0.21/0.52  % (21494)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.28/0.52  % (21486)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.28/0.52  % (21494)Refutation not found, incomplete strategy% (21494)------------------------------
% 1.28/0.52  % (21494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.52  % (21494)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.52  
% 1.28/0.52  % (21494)Memory used [KB]: 10618
% 1.28/0.52  % (21494)Time elapsed: 0.074 s
% 1.28/0.52  % (21494)------------------------------
% 1.28/0.52  % (21494)------------------------------
% 1.28/0.52  % (21491)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.28/0.53  % (21476)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.28/0.53  % (21475)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.28/0.53  % (21478)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.28/0.53  % (21473)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.28/0.53  % (21498)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.28/0.53  % (21480)Refutation not found, incomplete strategy% (21480)------------------------------
% 1.28/0.53  % (21480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (21480)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (21480)Memory used [KB]: 10618
% 1.28/0.53  % (21480)Time elapsed: 0.122 s
% 1.28/0.53  % (21480)------------------------------
% 1.28/0.53  % (21480)------------------------------
% 1.28/0.53  % (21472)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.28/0.53  % (21499)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.28/0.53  % (21481)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.28/0.53  % (21477)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.28/0.54  % (21490)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.44/0.54  % (21495)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.44/0.54  % (21483)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.44/0.54  % (21496)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.44/0.54  % (21495)Refutation not found, incomplete strategy% (21495)------------------------------
% 1.44/0.54  % (21495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (21495)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (21495)Memory used [KB]: 1663
% 1.44/0.54  % (21495)Time elapsed: 0.116 s
% 1.44/0.54  % (21495)------------------------------
% 1.44/0.54  % (21495)------------------------------
% 1.44/0.54  % (21474)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.44/0.54  % (21487)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.44/0.54  % (21474)Refutation not found, incomplete strategy% (21474)------------------------------
% 1.44/0.54  % (21474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (21474)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (21474)Memory used [KB]: 10618
% 1.44/0.54  % (21474)Time elapsed: 0.136 s
% 1.44/0.54  % (21474)------------------------------
% 1.44/0.54  % (21474)------------------------------
% 1.44/0.54  % (21482)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.44/0.54  % (21493)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.44/0.54  % (21493)Refutation not found, incomplete strategy% (21493)------------------------------
% 1.44/0.54  % (21493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (21493)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (21482)Refutation not found, incomplete strategy% (21482)------------------------------
% 1.44/0.54  % (21482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (21493)Memory used [KB]: 1663
% 1.44/0.54  % (21482)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (21493)Time elapsed: 0.138 s
% 1.44/0.54  % (21493)------------------------------
% 1.44/0.54  % (21493)------------------------------
% 1.44/0.54  % (21482)Memory used [KB]: 10618
% 1.44/0.54  % (21482)Time elapsed: 0.137 s
% 1.44/0.54  % (21482)------------------------------
% 1.44/0.54  % (21482)------------------------------
% 1.44/0.54  % (21501)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.44/0.55  % (21497)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.44/0.55  % (21479)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.44/0.55  % (21497)Refutation not found, incomplete strategy% (21497)------------------------------
% 1.44/0.55  % (21497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (21497)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (21497)Memory used [KB]: 6268
% 1.44/0.55  % (21497)Time elapsed: 0.139 s
% 1.44/0.55  % (21497)------------------------------
% 1.44/0.55  % (21497)------------------------------
% 1.44/0.55  % (21485)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.44/0.55  % (21489)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.44/0.56  % (21489)Refutation not found, incomplete strategy% (21489)------------------------------
% 1.44/0.56  % (21489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (21489)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (21489)Memory used [KB]: 10618
% 1.44/0.56  % (21489)Time elapsed: 0.149 s
% 1.44/0.56  % (21489)------------------------------
% 1.44/0.56  % (21489)------------------------------
% 1.44/0.56  % (21483)Refutation not found, incomplete strategy% (21483)------------------------------
% 1.44/0.56  % (21483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (21483)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (21483)Memory used [KB]: 10618
% 1.44/0.56  % (21483)Time elapsed: 0.133 s
% 1.44/0.56  % (21483)------------------------------
% 1.44/0.56  % (21483)------------------------------
% 1.44/0.56  % (21488)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.44/0.58  % (21498)Refutation not found, incomplete strategy% (21498)------------------------------
% 1.44/0.58  % (21498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.59  % (21498)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.59  
% 1.44/0.59  % (21498)Memory used [KB]: 10874
% 1.44/0.59  % (21498)Time elapsed: 0.181 s
% 1.44/0.59  % (21498)------------------------------
% 1.44/0.59  % (21498)------------------------------
% 1.96/0.67  % (21534)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.96/0.67  % (21536)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 1.96/0.67  % (21535)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.96/0.67  % (21533)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.96/0.68  % (21541)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.29/0.69  % (21538)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.29/0.69  % (21537)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.29/0.69  % (21539)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.29/0.70  % (21542)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.29/0.70  % (21540)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.29/0.73  % (21543)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.94/0.81  % (21477)Time limit reached!
% 2.94/0.81  % (21477)------------------------------
% 2.94/0.81  % (21477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.94/0.83  % (21477)Termination reason: Time limit
% 2.94/0.83  % (21477)Termination phase: Saturation
% 2.94/0.83  
% 2.94/0.83  % (21477)Memory used [KB]: 9210
% 2.94/0.83  % (21477)Time elapsed: 0.400 s
% 2.94/0.83  % (21477)------------------------------
% 2.94/0.83  % (21477)------------------------------
% 3.10/0.85  % (21501)Refutation found. Thanks to Tanya!
% 3.10/0.85  % SZS status Theorem for theBenchmark
% 3.10/0.85  % SZS output start Proof for theBenchmark
% 3.10/0.85  fof(f4423,plain,(
% 3.10/0.85    $false),
% 3.10/0.85    inference(unit_resulting_resolution,[],[f85,f4195,f120])).
% 3.10/0.85  fof(f120,plain,(
% 3.10/0.85    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_tarski(X2,X1)) | ~sP1(X0,X1,X2)) )),
% 3.10/0.85    inference(resolution,[],[f65,f86])).
% 3.10/0.85  fof(f86,plain,(
% 3.10/0.85    ( ! [X0,X1] : (sP2(X0,X1,k2_tarski(X0,X1))) )),
% 3.10/0.85    inference(equality_resolution,[],[f71])).
% 3.10/0.85  fof(f71,plain,(
% 3.10/0.85    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | k2_tarski(X0,X1) != X2) )),
% 3.10/0.85    inference(cnf_transformation,[],[f43])).
% 3.10/0.85  fof(f43,plain,(
% 3.10/0.85    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP2(X0,X1,X2)) & (sP2(X0,X1,X2) | k2_tarski(X0,X1) != X2))),
% 3.10/0.85    inference(nnf_transformation,[],[f26])).
% 3.10/0.85  fof(f26,plain,(
% 3.10/0.85    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP2(X0,X1,X2))),
% 3.10/0.85    inference(definition_folding,[],[f12,f25,f24])).
% 3.10/0.85  fof(f24,plain,(
% 3.10/0.85    ! [X3,X1,X0] : (sP1(X3,X1,X0) <=> (X1 = X3 | X0 = X3))),
% 3.10/0.85    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.10/0.85  fof(f25,plain,(
% 3.10/0.85    ! [X0,X1,X2] : (sP2(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP1(X3,X1,X0)))),
% 3.10/0.85    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 3.10/0.85  fof(f12,axiom,(
% 3.10/0.85    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.10/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 3.10/0.85  fof(f65,plain,(
% 3.10/0.85    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~sP1(X4,X1,X0) | r2_hidden(X4,X2)) )),
% 3.10/0.85    inference(cnf_transformation,[],[f39])).
% 3.10/0.85  fof(f39,plain,(
% 3.10/0.85    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((~sP1(sK7(X0,X1,X2),X1,X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP1(sK7(X0,X1,X2),X1,X0) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X4,X1,X0)) & (sP1(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 3.10/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f37,f38])).
% 3.10/0.85  fof(f38,plain,(
% 3.10/0.85    ! [X2,X1,X0] : (? [X3] : ((~sP1(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP1(X3,X1,X0) | r2_hidden(X3,X2))) => ((~sP1(sK7(X0,X1,X2),X1,X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP1(sK7(X0,X1,X2),X1,X0) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 3.10/0.85    introduced(choice_axiom,[])).
% 3.10/0.85  fof(f37,plain,(
% 3.10/0.85    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP1(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X4,X1,X0)) & (sP1(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 3.10/0.85    inference(rectify,[],[f36])).
% 3.10/0.85  fof(f36,plain,(
% 3.10/0.85    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP1(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP1(X3,X1,X0)) & (sP1(X3,X1,X0) | ~r2_hidden(X3,X2))) | ~sP2(X0,X1,X2)))),
% 3.10/0.85    inference(nnf_transformation,[],[f25])).
% 3.10/0.85  fof(f4195,plain,(
% 3.10/0.85    ~r2_hidden(sK3,k2_tarski(sK3,sK4))),
% 3.10/0.85    inference(resolution,[],[f4179,f1914])).
% 3.10/0.85  fof(f1914,plain,(
% 3.10/0.85    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.10/0.85    inference(duplicate_literal_removal,[],[f1911])).
% 3.10/0.85  fof(f1911,plain,(
% 3.10/0.85    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k2_tarski(X0,X0),X1) | r1_tarski(k2_tarski(X0,X0),X1)) )),
% 3.10/0.85    inference(superposition,[],[f55,f117])).
% 3.10/0.85  fof(f117,plain,(
% 3.10/0.85    ( ! [X2,X1] : (sK5(k2_tarski(X1,X1),X2) = X1 | r1_tarski(k2_tarski(X1,X1),X2)) )),
% 3.10/0.85    inference(resolution,[],[f95,f54])).
% 3.10/0.85  fof(f54,plain,(
% 3.10/0.85    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 3.10/0.85    inference(cnf_transformation,[],[f30])).
% 3.10/0.85  fof(f30,plain,(
% 3.10/0.85    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 3.10/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f29])).
% 3.10/0.85  fof(f29,plain,(
% 3.10/0.85    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 3.10/0.85    introduced(choice_axiom,[])).
% 3.10/0.85  fof(f21,plain,(
% 3.10/0.85    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 3.10/0.85    inference(ennf_transformation,[],[f18])).
% 3.10/0.85  fof(f18,plain,(
% 3.10/0.85    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 3.10/0.85    inference(unused_predicate_definition_removal,[],[f2])).
% 3.10/0.85  fof(f2,axiom,(
% 3.10/0.85    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.10/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 3.10/0.85  fof(f95,plain,(
% 3.10/0.85    ( ! [X0,X1] : (~r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1) )),
% 3.10/0.85    inference(resolution,[],[f56,f83])).
% 3.10/0.85  fof(f83,plain,(
% 3.10/0.85    ( ! [X0] : (sP0(X0,k2_tarski(X0,X0))) )),
% 3.10/0.85    inference(equality_resolution,[],[f81])).
% 3.10/0.85  fof(f81,plain,(
% 3.10/0.85    ( ! [X0,X1] : (sP0(X0,X1) | k2_tarski(X0,X0) != X1) )),
% 3.10/0.85    inference(definition_unfolding,[],[f60,f46])).
% 3.10/0.85  fof(f46,plain,(
% 3.10/0.85    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.10/0.85    inference(cnf_transformation,[],[f14])).
% 3.10/0.85  fof(f14,axiom,(
% 3.10/0.85    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.10/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 3.10/0.85  fof(f60,plain,(
% 3.10/0.85    ( ! [X0,X1] : (sP0(X0,X1) | k1_tarski(X0) != X1) )),
% 3.10/0.85    inference(cnf_transformation,[],[f35])).
% 3.10/0.85  fof(f35,plain,(
% 3.10/0.85    ! [X0,X1] : ((k1_tarski(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_tarski(X0) != X1))),
% 3.10/0.85    inference(nnf_transformation,[],[f23])).
% 3.10/0.85  fof(f23,plain,(
% 3.10/0.85    ! [X0,X1] : (k1_tarski(X0) = X1 <=> sP0(X0,X1))),
% 3.10/0.85    inference(definition_folding,[],[f11,f22])).
% 3.10/0.85  fof(f22,plain,(
% 3.10/0.85    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.10/0.85    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.10/0.85  fof(f11,axiom,(
% 3.10/0.85    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.10/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 3.10/0.85  fof(f56,plain,(
% 3.10/0.85    ( ! [X0,X3,X1] : (~sP0(X0,X1) | ~r2_hidden(X3,X1) | X0 = X3) )),
% 3.10/0.85    inference(cnf_transformation,[],[f34])).
% 3.10/0.85  fof(f34,plain,(
% 3.10/0.85    ! [X0,X1] : ((sP0(X0,X1) | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 3.10/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f32,f33])).
% 3.10/0.85  fof(f33,plain,(
% 3.10/0.85    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 3.10/0.85    introduced(choice_axiom,[])).
% 3.10/0.85  fof(f32,plain,(
% 3.10/0.85    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 3.10/0.85    inference(rectify,[],[f31])).
% 3.10/0.85  fof(f31,plain,(
% 3.10/0.85    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 3.10/0.85    inference(nnf_transformation,[],[f22])).
% 3.10/0.85  fof(f55,plain,(
% 3.10/0.85    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 3.10/0.85    inference(cnf_transformation,[],[f30])).
% 3.10/0.85  fof(f4179,plain,(
% 3.10/0.85    ~r1_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK4))),
% 3.10/0.85    inference(trivial_inequality_removal,[],[f4176])).
% 3.10/0.85  fof(f4176,plain,(
% 3.10/0.85    k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4) | ~r1_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK4))),
% 3.10/0.85    inference(superposition,[],[f75,f1847])).
% 3.10/0.85  fof(f1847,plain,(
% 3.10/0.85    ( ! [X4,X3] : (k5_xboole_0(X4,k4_xboole_0(X3,X4)) = X3 | ~r1_tarski(X4,X3)) )),
% 3.10/0.85    inference(superposition,[],[f659,f134])).
% 3.10/0.85  fof(f134,plain,(
% 3.10/0.85    ( ! [X6,X5] : (k4_xboole_0(X6,k4_xboole_0(X6,X5)) = X5 | ~r1_tarski(X5,X6)) )),
% 3.10/0.85    inference(superposition,[],[f77,f79])).
% 3.10/0.85  fof(f79,plain,(
% 3.10/0.85    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.10/0.85    inference(definition_unfolding,[],[f53,f52])).
% 3.10/0.85  fof(f52,plain,(
% 3.10/0.85    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.10/0.85    inference(cnf_transformation,[],[f8])).
% 3.10/0.85  fof(f8,axiom,(
% 3.10/0.85    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.10/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.10/0.85  fof(f53,plain,(
% 3.10/0.85    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.10/0.85    inference(cnf_transformation,[],[f20])).
% 3.10/0.85  fof(f20,plain,(
% 3.10/0.85    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.10/0.85    inference(ennf_transformation,[],[f6])).
% 3.10/0.85  fof(f6,axiom,(
% 3.10/0.85    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.10/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.10/0.85  fof(f77,plain,(
% 3.10/0.85    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.10/0.85    inference(definition_unfolding,[],[f48,f52,f52])).
% 3.10/0.85  fof(f48,plain,(
% 3.10/0.85    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.10/0.85    inference(cnf_transformation,[],[f1])).
% 3.10/0.85  fof(f1,axiom,(
% 3.10/0.85    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.10/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.10/0.85  fof(f659,plain,(
% 3.10/0.85    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 3.10/0.85    inference(forward_demodulation,[],[f636,f294])).
% 3.10/0.85  fof(f294,plain,(
% 3.10/0.85    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.10/0.85    inference(backward_demodulation,[],[f124,f267])).
% 3.10/0.85  fof(f267,plain,(
% 3.10/0.85    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 3.10/0.85    inference(backward_demodulation,[],[f133,f259])).
% 3.10/0.85  fof(f259,plain,(
% 3.10/0.85    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 3.10/0.85    inference(superposition,[],[f160,f74])).
% 3.10/0.85  fof(f74,plain,(
% 3.10/0.85    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.10/0.85    inference(definition_unfolding,[],[f51,f52])).
% 3.10/0.85  fof(f51,plain,(
% 3.10/0.85    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.10/0.85    inference(cnf_transformation,[],[f4])).
% 3.10/0.85  fof(f4,axiom,(
% 3.10/0.85    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.10/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.10/0.85  fof(f160,plain,(
% 3.10/0.85    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) )),
% 3.10/0.85    inference(superposition,[],[f78,f45])).
% 3.10/0.85  fof(f45,plain,(
% 3.10/0.85    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.10/0.85    inference(cnf_transformation,[],[f7])).
% 3.10/0.85  fof(f7,axiom,(
% 3.10/0.85    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.10/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 3.10/0.85  fof(f78,plain,(
% 3.10/0.85    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0) )),
% 3.10/0.85    inference(definition_unfolding,[],[f49,f50,f52])).
% 3.10/0.85  fof(f50,plain,(
% 3.10/0.85    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.10/0.85    inference(cnf_transformation,[],[f10])).
% 3.10/0.85  fof(f10,axiom,(
% 3.10/0.85    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.10/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 3.10/0.85  fof(f49,plain,(
% 3.10/0.85    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.10/0.85    inference(cnf_transformation,[],[f5])).
% 3.10/0.85  fof(f5,axiom,(
% 3.10/0.85    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.10/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 3.10/0.85  fof(f133,plain,(
% 3.10/0.85    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 3.10/0.85    inference(superposition,[],[f77,f45])).
% 3.10/0.85  fof(f124,plain,(
% 3.10/0.85    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 3.10/0.85    inference(superposition,[],[f74,f45])).
% 3.10/0.85  fof(f636,plain,(
% 3.10/0.85    ( ! [X0,X1] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.10/0.85    inference(superposition,[],[f131,f295])).
% 3.10/0.85  fof(f295,plain,(
% 3.10/0.85    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.10/0.85    inference(backward_demodulation,[],[f128,f267])).
% 3.10/0.85  fof(f128,plain,(
% 3.10/0.85    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 3.10/0.85    inference(superposition,[],[f74,f76])).
% 3.10/0.85  fof(f76,plain,(
% 3.10/0.85    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 3.10/0.85    inference(definition_unfolding,[],[f47,f52])).
% 3.10/0.85  fof(f47,plain,(
% 3.10/0.85    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.10/0.85    inference(cnf_transformation,[],[f17])).
% 3.10/0.85  fof(f17,plain,(
% 3.10/0.85    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.10/0.85    inference(rectify,[],[f3])).
% 3.10/0.85  fof(f3,axiom,(
% 3.10/0.85    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.10/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 3.10/0.85  fof(f131,plain,(
% 3.10/0.85    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.10/0.85    inference(superposition,[],[f63,f74])).
% 3.10/0.85  fof(f63,plain,(
% 3.10/0.85    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 3.10/0.85    inference(cnf_transformation,[],[f9])).
% 3.10/0.85  fof(f9,axiom,(
% 3.10/0.85    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 3.10/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 3.10/0.85  fof(f75,plain,(
% 3.10/0.85    k2_tarski(sK3,sK4) != k5_xboole_0(k2_tarski(sK3,sK3),k4_xboole_0(k2_tarski(sK3,sK4),k2_tarski(sK3,sK3)))),
% 3.10/0.85    inference(definition_unfolding,[],[f44,f73])).
% 3.10/0.85  fof(f73,plain,(
% 3.10/0.85    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) )),
% 3.10/0.85    inference(definition_unfolding,[],[f62,f50,f46])).
% 3.10/0.85  fof(f62,plain,(
% 3.10/0.85    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 3.10/0.85    inference(cnf_transformation,[],[f13])).
% 3.10/0.85  fof(f13,axiom,(
% 3.10/0.85    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 3.10/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 3.10/0.85  fof(f44,plain,(
% 3.10/0.85    k2_tarski(sK3,sK4) != k1_enumset1(sK3,sK3,sK4)),
% 3.10/0.85    inference(cnf_transformation,[],[f28])).
% 3.10/0.85  fof(f28,plain,(
% 3.10/0.85    k2_tarski(sK3,sK4) != k1_enumset1(sK3,sK3,sK4)),
% 3.10/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f19,f27])).
% 3.10/0.85  fof(f27,plain,(
% 3.10/0.85    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) => k2_tarski(sK3,sK4) != k1_enumset1(sK3,sK3,sK4)),
% 3.10/0.85    introduced(choice_axiom,[])).
% 3.10/0.85  fof(f19,plain,(
% 3.10/0.85    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 3.10/0.85    inference(ennf_transformation,[],[f16])).
% 3.10/0.85  fof(f16,negated_conjecture,(
% 3.10/0.85    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.10/0.85    inference(negated_conjecture,[],[f15])).
% 3.10/0.85  fof(f15,conjecture,(
% 3.10/0.85    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.10/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.10/0.85  fof(f85,plain,(
% 3.10/0.85    ( ! [X2,X1] : (sP1(X2,X1,X2)) )),
% 3.10/0.85    inference(equality_resolution,[],[f69])).
% 3.10/0.85  fof(f69,plain,(
% 3.10/0.85    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | X0 != X2) )),
% 3.10/0.85    inference(cnf_transformation,[],[f42])).
% 3.10/0.85  fof(f42,plain,(
% 3.10/0.85    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (X0 != X1 & X0 != X2)) & (X0 = X1 | X0 = X2 | ~sP1(X0,X1,X2)))),
% 3.10/0.85    inference(rectify,[],[f41])).
% 3.10/0.85  fof(f41,plain,(
% 3.10/0.85    ! [X3,X1,X0] : ((sP1(X3,X1,X0) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~sP1(X3,X1,X0)))),
% 3.10/0.85    inference(flattening,[],[f40])).
% 3.10/0.85  fof(f40,plain,(
% 3.10/0.85    ! [X3,X1,X0] : ((sP1(X3,X1,X0) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~sP1(X3,X1,X0)))),
% 3.10/0.85    inference(nnf_transformation,[],[f24])).
% 3.10/0.85  % SZS output end Proof for theBenchmark
% 3.10/0.85  % (21501)------------------------------
% 3.10/0.85  % (21501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.10/0.85  % (21501)Termination reason: Refutation
% 3.10/0.85  
% 3.10/0.85  % (21501)Memory used [KB]: 4477
% 3.10/0.85  % (21501)Time elapsed: 0.435 s
% 3.10/0.85  % (21501)------------------------------
% 3.10/0.85  % (21501)------------------------------
% 3.10/0.85  % (21471)Success in time 0.492 s
%------------------------------------------------------------------------------
