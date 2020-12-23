%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:32 EST 2020

% Result     : Theorem 2.81s
% Output     : Refutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 157 expanded)
%              Number of leaves         :   22 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  245 ( 335 expanded)
%              Number of equality atoms :  100 ( 156 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4064,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f94,f3899,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_tarski(X2,X1))
      | ~ sP1(X0,X1,X2) ) ),
    inference(resolution,[],[f72,f95])).

fof(f95,plain,(
    ! [X0,X1] : sP2(X0,X1,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP2(X0,X1,X2) )
      & ( sP2(X0,X1,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP2(X0,X1,X2) ) ),
    inference(definition_folding,[],[f13,f24,f23])).

fof(f23,plain,(
    ! [X3,X1,X0] :
      ( sP1(X3,X1,X0)
    <=> ( X1 = X3
        | X0 = X3 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP1(X3,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ sP1(X4,X1,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f40,f41])).

fof(f41,plain,(
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

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f3899,plain,(
    ~ r2_hidden(sK3,k2_tarski(sK3,sK4)) ),
    inference(resolution,[],[f3883,f1857])).

fof(f1857,plain,(
    ! [X4,X3] :
      ( r1_tarski(k2_tarski(X3,X3),X4)
      | ~ r2_hidden(X3,X4) ) ),
    inference(duplicate_literal_removal,[],[f1854])).

fof(f1854,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,X4)
      | r1_tarski(k2_tarski(X3,X3),X4)
      | r1_tarski(k2_tarski(X3,X3),X4) ) ),
    inference(superposition,[],[f62,f109])).

fof(f109,plain,(
    ! [X2,X1] :
      ( sK5(k2_tarski(X1,X1),X2) = X1
      | r1_tarski(k2_tarski(X1,X1),X2) ) ),
    inference(resolution,[],[f107,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_tarski(X1,X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f63,f92])).

fof(f92,plain,(
    ! [X0] : sP0(X0,k2_tarski(X0,X0)) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f67,f50])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f12,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X3,X1)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f36])).

fof(f36,plain,(
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

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3883,plain,(
    ~ r1_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK4)) ),
    inference(trivial_inequality_removal,[],[f3880])).

fof(f3880,plain,
    ( k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4)
    | ~ r1_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK4)) ),
    inference(superposition,[],[f82,f2524])).

fof(f2524,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X1,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X1,X0) ) ),
    inference(forward_demodulation,[],[f2470,f265])).

fof(f265,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f83,f256])).

fof(f256,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f179,f81])).

fof(f81,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f179,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[],[f85,f49])).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f85,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    inference(definition_unfolding,[],[f52,f53,f55])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f83,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f53])).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f2470,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X1,k4_xboole_0(X0,X1))
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f694,f303])).

fof(f303,plain,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3) ),
    inference(forward_demodulation,[],[f298,f49])).

fof(f298,plain,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0)) ),
    inference(superposition,[],[f81,f280])).

fof(f280,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f264,f49])).

fof(f264,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f150,f256])).

fof(f150,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f84,f49])).

fof(f84,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f51,f55,f55])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f694,plain,(
    ! [X6,X7,X5] :
      ( k5_xboole_0(X6,X7) = k5_xboole_0(X5,k5_xboole_0(k4_xboole_0(X5,X6),X7))
      | ~ r1_tarski(X6,X5) ) ),
    inference(superposition,[],[f148,f151])).

fof(f151,plain,(
    ! [X4,X5] :
      ( k4_xboole_0(X5,k4_xboole_0(X5,X4)) = X4
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f84,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f55])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f148,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[],[f70,f81])).

fof(f70,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f82,plain,(
    k2_tarski(sK3,sK4) != k5_xboole_0(k2_tarski(sK3,sK3),k4_xboole_0(k2_tarski(sK3,sK4),k2_tarski(sK3,sK3))) ),
    inference(definition_unfolding,[],[f47,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f69,f53,f50])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f47,plain,(
    k2_tarski(sK3,sK4) != k1_enumset1(sK3,sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    k2_tarski(sK3,sK4) != k1_enumset1(sK3,sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f18,f26])).

fof(f26,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK3,sK4) != k1_enumset1(sK3,sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f94,plain,(
    ! [X2,X1] : sP1(X2,X1,X2) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( X0 != X1
          & X0 != X2 ) )
      & ( X0 = X1
        | X0 = X2
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X3,X1,X0] :
      ( ( sP1(X3,X1,X0)
        | ( X1 != X3
          & X0 != X3 ) )
      & ( X1 = X3
        | X0 = X3
        | ~ sP1(X3,X1,X0) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X3,X1,X0] :
      ( ( sP1(X3,X1,X0)
        | ( X1 != X3
          & X0 != X3 ) )
      & ( X1 = X3
        | X0 = X3
        | ~ sP1(X3,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:24:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (32636)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (32630)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (32652)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (32644)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (32629)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (32638)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (32641)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (32631)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (32634)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (32646)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (32646)Refutation not found, incomplete strategy% (32646)------------------------------
% 0.21/0.53  % (32646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32633)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (32646)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32646)Memory used [KB]: 10618
% 0.21/0.53  % (32646)Time elapsed: 0.119 s
% 0.21/0.53  % (32646)------------------------------
% 0.21/0.53  % (32646)------------------------------
% 0.21/0.53  % (32651)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (32652)Refutation not found, incomplete strategy% (32652)------------------------------
% 0.21/0.54  % (32652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32652)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32652)Memory used [KB]: 1663
% 0.21/0.54  % (32652)Time elapsed: 0.123 s
% 0.21/0.54  % (32652)------------------------------
% 0.21/0.54  % (32652)------------------------------
% 0.21/0.54  % (32651)Refutation not found, incomplete strategy% (32651)------------------------------
% 0.21/0.54  % (32651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32651)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32651)Memory used [KB]: 10746
% 0.21/0.54  % (32651)Time elapsed: 0.092 s
% 0.21/0.54  % (32651)------------------------------
% 0.21/0.54  % (32651)------------------------------
% 0.21/0.54  % (32648)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (32658)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (32632)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (32650)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (32650)Refutation not found, incomplete strategy% (32650)------------------------------
% 0.21/0.54  % (32650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32650)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32650)Memory used [KB]: 1663
% 0.21/0.54  % (32650)Time elapsed: 0.130 s
% 0.21/0.54  % (32650)------------------------------
% 0.21/0.54  % (32650)------------------------------
% 0.21/0.54  % (32656)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (32655)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (32635)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (32647)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (32631)Refutation not found, incomplete strategy% (32631)------------------------------
% 0.21/0.55  % (32631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32631)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32631)Memory used [KB]: 10618
% 0.21/0.55  % (32631)Time elapsed: 0.134 s
% 0.21/0.55  % (32631)------------------------------
% 0.21/0.55  % (32631)------------------------------
% 0.21/0.55  % (32653)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (32657)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (32639)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (32643)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (32639)Refutation not found, incomplete strategy% (32639)------------------------------
% 0.21/0.55  % (32639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32639)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32639)Memory used [KB]: 10618
% 0.21/0.55  % (32639)Time elapsed: 0.140 s
% 0.21/0.55  % (32639)------------------------------
% 0.21/0.55  % (32639)------------------------------
% 0.21/0.55  % (32642)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (32654)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (32649)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (32645)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (32649)Refutation not found, incomplete strategy% (32649)------------------------------
% 0.21/0.56  % (32649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (32649)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (32649)Memory used [KB]: 10746
% 0.21/0.56  % (32649)Time elapsed: 0.148 s
% 0.21/0.56  % (32649)------------------------------
% 0.21/0.56  % (32649)------------------------------
% 0.21/0.56  % (32640)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (32640)Refutation not found, incomplete strategy% (32640)------------------------------
% 0.21/0.56  % (32640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (32640)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (32640)Memory used [KB]: 10618
% 0.21/0.56  % (32640)Time elapsed: 0.151 s
% 0.21/0.56  % (32640)------------------------------
% 0.21/0.56  % (32640)------------------------------
% 0.21/0.56  % (32637)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (32637)Refutation not found, incomplete strategy% (32637)------------------------------
% 0.21/0.56  % (32637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (32637)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (32637)Memory used [KB]: 10618
% 0.21/0.56  % (32637)Time elapsed: 0.152 s
% 0.21/0.56  % (32637)------------------------------
% 0.21/0.56  % (32637)------------------------------
% 2.10/0.65  % (32705)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.10/0.66  % (32715)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.10/0.66  % (32707)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.10/0.67  % (32708)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.10/0.68  % (32720)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.10/0.68  % (32713)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.10/0.70  % (32718)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.10/0.70  % (32722)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.10/0.70  % (32724)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.81/0.77  % (32658)Refutation found. Thanks to Tanya!
% 2.81/0.77  % SZS status Theorem for theBenchmark
% 2.81/0.79  % SZS output start Proof for theBenchmark
% 2.81/0.79  fof(f4064,plain,(
% 2.81/0.79    $false),
% 2.81/0.79    inference(unit_resulting_resolution,[],[f94,f3899,f138])).
% 2.81/0.79  fof(f138,plain,(
% 2.81/0.79    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_tarski(X2,X1)) | ~sP1(X0,X1,X2)) )),
% 2.81/0.79    inference(resolution,[],[f72,f95])).
% 2.81/0.79  fof(f95,plain,(
% 2.81/0.79    ( ! [X0,X1] : (sP2(X0,X1,k2_tarski(X0,X1))) )),
% 2.81/0.79    inference(equality_resolution,[],[f78])).
% 2.81/0.79  fof(f78,plain,(
% 2.81/0.79    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | k2_tarski(X0,X1) != X2) )),
% 2.81/0.79    inference(cnf_transformation,[],[f46])).
% 2.81/0.79  fof(f46,plain,(
% 2.81/0.79    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP2(X0,X1,X2)) & (sP2(X0,X1,X2) | k2_tarski(X0,X1) != X2))),
% 2.81/0.79    inference(nnf_transformation,[],[f25])).
% 2.81/0.79  fof(f25,plain,(
% 2.81/0.79    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP2(X0,X1,X2))),
% 2.81/0.79    inference(definition_folding,[],[f13,f24,f23])).
% 2.81/0.79  fof(f23,plain,(
% 2.81/0.79    ! [X3,X1,X0] : (sP1(X3,X1,X0) <=> (X1 = X3 | X0 = X3))),
% 2.81/0.79    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.81/0.79  fof(f24,plain,(
% 2.81/0.79    ! [X0,X1,X2] : (sP2(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP1(X3,X1,X0)))),
% 2.81/0.79    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.81/0.79  fof(f13,axiom,(
% 2.81/0.79    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.81/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 2.81/0.79  fof(f72,plain,(
% 2.81/0.79    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~sP1(X4,X1,X0) | r2_hidden(X4,X2)) )),
% 2.81/0.79    inference(cnf_transformation,[],[f42])).
% 2.81/0.79  fof(f42,plain,(
% 2.81/0.79    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((~sP1(sK7(X0,X1,X2),X1,X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP1(sK7(X0,X1,X2),X1,X0) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X4,X1,X0)) & (sP1(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 2.81/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f40,f41])).
% 2.81/0.79  fof(f41,plain,(
% 2.81/0.79    ! [X2,X1,X0] : (? [X3] : ((~sP1(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP1(X3,X1,X0) | r2_hidden(X3,X2))) => ((~sP1(sK7(X0,X1,X2),X1,X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP1(sK7(X0,X1,X2),X1,X0) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 2.81/0.79    introduced(choice_axiom,[])).
% 2.81/0.79  fof(f40,plain,(
% 2.81/0.79    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP1(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X4,X1,X0)) & (sP1(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 2.81/0.79    inference(rectify,[],[f39])).
% 2.81/0.79  fof(f39,plain,(
% 2.81/0.79    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP1(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP1(X3,X1,X0)) & (sP1(X3,X1,X0) | ~r2_hidden(X3,X2))) | ~sP2(X0,X1,X2)))),
% 2.81/0.79    inference(nnf_transformation,[],[f24])).
% 2.81/0.79  fof(f3899,plain,(
% 2.81/0.79    ~r2_hidden(sK3,k2_tarski(sK3,sK4))),
% 2.81/0.79    inference(resolution,[],[f3883,f1857])).
% 2.81/0.79  fof(f1857,plain,(
% 2.81/0.79    ( ! [X4,X3] : (r1_tarski(k2_tarski(X3,X3),X4) | ~r2_hidden(X3,X4)) )),
% 2.81/0.79    inference(duplicate_literal_removal,[],[f1854])).
% 2.81/0.79  fof(f1854,plain,(
% 2.81/0.79    ( ! [X4,X3] : (~r2_hidden(X3,X4) | r1_tarski(k2_tarski(X3,X3),X4) | r1_tarski(k2_tarski(X3,X3),X4)) )),
% 2.81/0.79    inference(superposition,[],[f62,f109])).
% 2.81/0.79  fof(f109,plain,(
% 2.81/0.79    ( ! [X2,X1] : (sK5(k2_tarski(X1,X1),X2) = X1 | r1_tarski(k2_tarski(X1,X1),X2)) )),
% 2.81/0.79    inference(resolution,[],[f107,f61])).
% 2.81/0.79  fof(f61,plain,(
% 2.81/0.79    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.81/0.79    inference(cnf_transformation,[],[f33])).
% 2.81/0.79  fof(f33,plain,(
% 2.81/0.79    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.81/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).
% 2.81/0.79  fof(f32,plain,(
% 2.81/0.79    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 2.81/0.79    introduced(choice_axiom,[])).
% 2.81/0.79  fof(f31,plain,(
% 2.81/0.79    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.81/0.79    inference(rectify,[],[f30])).
% 2.81/0.79  fof(f30,plain,(
% 2.81/0.79    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.81/0.79    inference(nnf_transformation,[],[f20])).
% 2.81/0.79  fof(f20,plain,(
% 2.81/0.79    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.81/0.79    inference(ennf_transformation,[],[f2])).
% 2.81/0.79  fof(f2,axiom,(
% 2.81/0.79    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.81/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.81/0.79  fof(f107,plain,(
% 2.81/0.79    ( ! [X0,X1] : (~r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1) )),
% 2.81/0.79    inference(resolution,[],[f63,f92])).
% 2.81/0.79  fof(f92,plain,(
% 2.81/0.79    ( ! [X0] : (sP0(X0,k2_tarski(X0,X0))) )),
% 2.81/0.79    inference(equality_resolution,[],[f88])).
% 2.81/0.79  fof(f88,plain,(
% 2.81/0.79    ( ! [X0,X1] : (sP0(X0,X1) | k2_tarski(X0,X0) != X1) )),
% 2.81/0.79    inference(definition_unfolding,[],[f67,f50])).
% 2.81/0.79  fof(f50,plain,(
% 2.81/0.79    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.81/0.79    inference(cnf_transformation,[],[f15])).
% 2.81/0.79  fof(f15,axiom,(
% 2.81/0.79    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.81/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.81/0.79  fof(f67,plain,(
% 2.81/0.79    ( ! [X0,X1] : (sP0(X0,X1) | k1_tarski(X0) != X1) )),
% 2.81/0.79    inference(cnf_transformation,[],[f38])).
% 2.81/0.79  fof(f38,plain,(
% 2.81/0.79    ! [X0,X1] : ((k1_tarski(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_tarski(X0) != X1))),
% 2.81/0.79    inference(nnf_transformation,[],[f22])).
% 2.81/0.79  fof(f22,plain,(
% 2.81/0.79    ! [X0,X1] : (k1_tarski(X0) = X1 <=> sP0(X0,X1))),
% 2.81/0.79    inference(definition_folding,[],[f12,f21])).
% 2.81/0.79  fof(f21,plain,(
% 2.81/0.79    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.81/0.79    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.81/0.79  fof(f12,axiom,(
% 2.81/0.79    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.81/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.81/0.79  fof(f63,plain,(
% 2.81/0.79    ( ! [X0,X3,X1] : (~sP0(X0,X1) | ~r2_hidden(X3,X1) | X0 = X3) )),
% 2.81/0.79    inference(cnf_transformation,[],[f37])).
% 2.81/0.79  fof(f37,plain,(
% 2.81/0.79    ! [X0,X1] : ((sP0(X0,X1) | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 2.81/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f36])).
% 2.81/0.79  fof(f36,plain,(
% 2.81/0.79    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 2.81/0.79    introduced(choice_axiom,[])).
% 2.81/0.79  fof(f35,plain,(
% 2.81/0.79    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 2.81/0.79    inference(rectify,[],[f34])).
% 2.81/0.79  fof(f34,plain,(
% 2.81/0.79    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 2.81/0.79    inference(nnf_transformation,[],[f21])).
% 2.81/0.79  fof(f62,plain,(
% 2.81/0.79    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.81/0.79    inference(cnf_transformation,[],[f33])).
% 2.81/0.79  fof(f3883,plain,(
% 2.81/0.79    ~r1_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK4))),
% 2.81/0.79    inference(trivial_inequality_removal,[],[f3880])).
% 2.81/0.79  fof(f3880,plain,(
% 2.81/0.79    k2_tarski(sK3,sK4) != k2_tarski(sK3,sK4) | ~r1_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK4))),
% 2.81/0.79    inference(superposition,[],[f82,f2524])).
% 2.81/0.79  fof(f2524,plain,(
% 2.81/0.79    ( ! [X0,X1] : (k5_xboole_0(X1,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X1,X0)) )),
% 2.81/0.79    inference(forward_demodulation,[],[f2470,f265])).
% 2.81/0.79  fof(f265,plain,(
% 2.81/0.79    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.81/0.79    inference(backward_demodulation,[],[f83,f256])).
% 2.81/0.79  fof(f256,plain,(
% 2.81/0.79    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 2.81/0.79    inference(superposition,[],[f179,f81])).
% 2.81/0.79  fof(f81,plain,(
% 2.81/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.81/0.79    inference(definition_unfolding,[],[f54,f55])).
% 2.81/0.79  fof(f55,plain,(
% 2.81/0.79    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.81/0.79    inference(cnf_transformation,[],[f9])).
% 2.81/0.79  fof(f9,axiom,(
% 2.81/0.79    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.81/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.81/0.79  fof(f54,plain,(
% 2.81/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.81/0.79    inference(cnf_transformation,[],[f4])).
% 2.81/0.79  fof(f4,axiom,(
% 2.81/0.79    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.81/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.81/0.79  fof(f179,plain,(
% 2.81/0.79    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) )),
% 2.81/0.79    inference(superposition,[],[f85,f49])).
% 2.81/0.79  fof(f49,plain,(
% 2.81/0.79    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.81/0.79    inference(cnf_transformation,[],[f8])).
% 2.81/0.79  fof(f8,axiom,(
% 2.81/0.79    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.81/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.81/0.79  fof(f85,plain,(
% 2.81/0.79    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0) )),
% 2.81/0.79    inference(definition_unfolding,[],[f52,f53,f55])).
% 2.81/0.79  fof(f53,plain,(
% 2.81/0.79    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.81/0.79    inference(cnf_transformation,[],[f11])).
% 2.81/0.79  fof(f11,axiom,(
% 2.81/0.79    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.81/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.81/0.79  fof(f52,plain,(
% 2.81/0.79    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.81/0.79    inference(cnf_transformation,[],[f6])).
% 2.81/0.79  fof(f6,axiom,(
% 2.81/0.79    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.81/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 2.81/0.79  fof(f83,plain,(
% 2.81/0.79    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 2.81/0.79    inference(definition_unfolding,[],[f48,f53])).
% 2.81/0.79  fof(f48,plain,(
% 2.81/0.79    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.81/0.79    inference(cnf_transformation,[],[f5])).
% 2.81/0.79  fof(f5,axiom,(
% 2.81/0.79    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.81/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.81/0.79  fof(f2470,plain,(
% 2.81/0.79    ( ! [X0,X1] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) | ~r1_tarski(X1,X0)) )),
% 2.81/0.79    inference(superposition,[],[f694,f303])).
% 2.81/0.79  fof(f303,plain,(
% 2.81/0.79    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,X3)) )),
% 2.81/0.79    inference(forward_demodulation,[],[f298,f49])).
% 2.81/0.79  fof(f298,plain,(
% 2.81/0.79    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0))) )),
% 2.81/0.79    inference(superposition,[],[f81,f280])).
% 2.81/0.79  fof(f280,plain,(
% 2.81/0.79    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.81/0.79    inference(forward_demodulation,[],[f264,f49])).
% 2.81/0.79  fof(f264,plain,(
% 2.81/0.79    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 2.81/0.79    inference(backward_demodulation,[],[f150,f256])).
% 2.81/0.79  fof(f150,plain,(
% 2.81/0.79    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 2.81/0.79    inference(superposition,[],[f84,f49])).
% 2.81/0.79  fof(f84,plain,(
% 2.81/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.81/0.79    inference(definition_unfolding,[],[f51,f55,f55])).
% 2.81/0.79  fof(f51,plain,(
% 2.81/0.79    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.81/0.79    inference(cnf_transformation,[],[f1])).
% 2.81/0.79  fof(f1,axiom,(
% 2.81/0.79    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.81/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.81/0.79  fof(f694,plain,(
% 2.81/0.79    ( ! [X6,X7,X5] : (k5_xboole_0(X6,X7) = k5_xboole_0(X5,k5_xboole_0(k4_xboole_0(X5,X6),X7)) | ~r1_tarski(X6,X5)) )),
% 2.81/0.79    inference(superposition,[],[f148,f151])).
% 2.81/0.79  fof(f151,plain,(
% 2.81/0.79    ( ! [X4,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,X4)) = X4 | ~r1_tarski(X4,X5)) )),
% 2.81/0.79    inference(superposition,[],[f84,f86])).
% 2.81/0.79  fof(f86,plain,(
% 2.81/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.81/0.79    inference(definition_unfolding,[],[f56,f55])).
% 2.81/0.79  fof(f56,plain,(
% 2.81/0.79    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.81/0.79    inference(cnf_transformation,[],[f19])).
% 2.81/0.79  fof(f19,plain,(
% 2.81/0.79    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.81/0.79    inference(ennf_transformation,[],[f7])).
% 2.81/0.79  fof(f7,axiom,(
% 2.81/0.79    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.81/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.81/0.79  fof(f148,plain,(
% 2.81/0.79    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 2.81/0.79    inference(superposition,[],[f70,f81])).
% 2.81/0.79  fof(f70,plain,(
% 2.81/0.79    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.81/0.79    inference(cnf_transformation,[],[f10])).
% 2.81/0.79  fof(f10,axiom,(
% 2.81/0.79    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.81/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.81/0.79  fof(f82,plain,(
% 2.81/0.79    k2_tarski(sK3,sK4) != k5_xboole_0(k2_tarski(sK3,sK3),k4_xboole_0(k2_tarski(sK3,sK4),k2_tarski(sK3,sK3)))),
% 2.81/0.79    inference(definition_unfolding,[],[f47,f80])).
% 2.81/0.79  fof(f80,plain,(
% 2.81/0.79    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) )),
% 2.81/0.79    inference(definition_unfolding,[],[f69,f53,f50])).
% 2.81/0.79  fof(f69,plain,(
% 2.81/0.79    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 2.81/0.79    inference(cnf_transformation,[],[f14])).
% 2.81/0.79  fof(f14,axiom,(
% 2.81/0.79    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 2.81/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 2.81/0.79  fof(f47,plain,(
% 2.81/0.79    k2_tarski(sK3,sK4) != k1_enumset1(sK3,sK3,sK4)),
% 2.81/0.79    inference(cnf_transformation,[],[f27])).
% 2.81/0.79  fof(f27,plain,(
% 2.81/0.79    k2_tarski(sK3,sK4) != k1_enumset1(sK3,sK3,sK4)),
% 2.81/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f18,f26])).
% 2.81/0.79  fof(f26,plain,(
% 2.81/0.79    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) => k2_tarski(sK3,sK4) != k1_enumset1(sK3,sK3,sK4)),
% 2.81/0.79    introduced(choice_axiom,[])).
% 2.81/0.79  fof(f18,plain,(
% 2.81/0.79    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 2.81/0.79    inference(ennf_transformation,[],[f17])).
% 2.81/0.79  fof(f17,negated_conjecture,(
% 2.81/0.79    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.81/0.79    inference(negated_conjecture,[],[f16])).
% 2.81/0.79  fof(f16,conjecture,(
% 2.81/0.79    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.81/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.81/0.79  fof(f94,plain,(
% 2.81/0.79    ( ! [X2,X1] : (sP1(X2,X1,X2)) )),
% 2.81/0.79    inference(equality_resolution,[],[f76])).
% 2.81/0.79  fof(f76,plain,(
% 2.81/0.79    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | X0 != X2) )),
% 2.81/0.79    inference(cnf_transformation,[],[f45])).
% 2.81/0.79  fof(f45,plain,(
% 2.81/0.79    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (X0 != X1 & X0 != X2)) & (X0 = X1 | X0 = X2 | ~sP1(X0,X1,X2)))),
% 2.81/0.79    inference(rectify,[],[f44])).
% 2.81/0.79  fof(f44,plain,(
% 2.81/0.79    ! [X3,X1,X0] : ((sP1(X3,X1,X0) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~sP1(X3,X1,X0)))),
% 2.81/0.79    inference(flattening,[],[f43])).
% 2.81/0.79  fof(f43,plain,(
% 2.81/0.79    ! [X3,X1,X0] : ((sP1(X3,X1,X0) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~sP1(X3,X1,X0)))),
% 2.81/0.79    inference(nnf_transformation,[],[f23])).
% 2.81/0.79  % SZS output end Proof for theBenchmark
% 2.81/0.79  % (32658)------------------------------
% 2.81/0.79  % (32658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.79  % (32658)Termination reason: Refutation
% 2.81/0.79  
% 2.81/0.79  % (32658)Memory used [KB]: 3837
% 2.81/0.79  % (32658)Time elapsed: 0.351 s
% 2.81/0.79  % (32658)------------------------------
% 2.81/0.79  % (32658)------------------------------
% 2.81/0.79  % (32628)Success in time 0.416 s
%------------------------------------------------------------------------------
