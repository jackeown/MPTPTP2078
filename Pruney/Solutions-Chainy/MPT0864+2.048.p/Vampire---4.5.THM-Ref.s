%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:37 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 750 expanded)
%              Number of leaves         :   26 ( 262 expanded)
%              Depth                    :   16
%              Number of atoms          :  313 (1373 expanded)
%              Number of equality atoms :  109 ( 887 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f486,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f368,f412,f450,f485])).

fof(f485,plain,
    ( ~ spl10_1
    | ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f484])).

fof(f484,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f483,f451])).

fof(f451,plain,
    ( sP0(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | ~ spl10_1
    | ~ spl10_3 ),
    inference(forward_demodulation,[],[f192,f422])).

fof(f422,plain,
    ( sK3 = sK4
    | ~ spl10_1 ),
    inference(backward_demodulation,[],[f91,f85])).

fof(f85,plain,
    ( sK3 = k1_mcart_1(sK3)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl10_1
  <=> sK3 = k1_mcart_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f91,plain,(
    k1_mcart_1(sK3) = sK4 ),
    inference(superposition,[],[f49,f39])).

fof(f39,plain,(
    sK3 = k4_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( sK3 = k2_mcart_1(sK3)
      | sK3 = k1_mcart_1(sK3) )
    & sK3 = k4_tarski(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f16,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK3 = k2_mcart_1(sK3)
        | sK3 = k1_mcart_1(sK3) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK3 ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK3
   => sK3 = k4_tarski(sK4,sK5) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f49,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f192,plain,
    ( sP0(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl10_3
  <=> sP0(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f483,plain,
    ( ~ sP0(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | ~ spl10_1 ),
    inference(superposition,[],[f481,f423])).

fof(f423,plain,
    ( sK3 = k4_tarski(sK3,sK5)
    | ~ spl10_1 ),
    inference(backward_demodulation,[],[f39,f422])).

fof(f481,plain,
    ( ! [X10] : ~ sP0(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,k4_tarski(X10,sK5))),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X10))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f476,f286])).

fof(f286,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(superposition,[],[f74,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X3,X3,X3,X3,X3,X3,X3))) ),
    inference(definition_unfolding,[],[f65,f69,f73,f70,f72])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f70])).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f69])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f47,f71])).

fof(f47,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f64,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f74,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)) ),
    inference(definition_unfolding,[],[f46,f73,f72])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f476,plain,
    ( ! [X10] :
        ( ~ sP0(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,k4_tarski(X10,sK5))),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X10))
        | k1_xboole_0 = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,k4_tarski(X10,sK5)) )
    | ~ spl10_1 ),
    inference(superposition,[],[f154,f430])).

fof(f430,plain,
    ( ! [X0] : k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,k4_tarski(X0,sK5)) = k2_zfmisc_1(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X0),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | ~ spl10_1 ),
    inference(superposition,[],[f75,f423])).

fof(f75,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) = k5_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f53,f71,f72,f71])).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f154,plain,(
    ! [X6,X7] :
      ( ~ sP0(sK6(k2_zfmisc_1(X6,X7)),X6)
      | k1_xboole_0 = k2_zfmisc_1(X6,X7) ) ),
    inference(resolution,[],[f151,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( sP1(sK6(k2_zfmisc_1(X0,X1)),X1,X0)
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f101,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( sP0(sK6(X0),X0)
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP0(sK6(X0),X0)
        & r2_hidden(sK6(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ! [X2,X3] :
          ( k4_tarski(X2,X3) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

% (8317)Termination reason: Refutation not found, incomplete strategy
fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | sP1(X0,X2,X1) ) ),
    inference(resolution,[],[f54,f81])).

fof(f81,plain,(
    ! [X0,X1] : sP2(X0,X1,k2_zfmisc_1(X0,X1)) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP2(X0,X1,X2) )
      & ( sP2(X0,X1,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP2(X0,X1,X2) ) ),
    inference(definition_folding,[],[f8,f21,f20])).

fof(f20,plain,(
    ! [X3,X1,X0] :
      ( sP1(X3,X1,X0)
    <=> ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X4,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP1(X3,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP1(X4,X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f32])).

fof(f32,plain,(
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

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

% (8317)Memory used [KB]: 10618
% (8317)Time elapsed: 0.122 s
% (8317)------------------------------
% (8317)------------------------------
% (8325)Refutation not found, incomplete strategy% (8325)------------------------------
% (8325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8319)Termination reason: Refutation not found, incomplete strategy

% (8319)Memory used [KB]: 10618
% (8319)Time elapsed: 0.135 s
% (8319)------------------------------
% (8319)------------------------------
% (8325)Termination reason: Refutation not found, incomplete strategy

% (8325)Memory used [KB]: 10618
% (8325)Time elapsed: 0.149 s
% (8325)------------------------------
% (8325)------------------------------
% (8337)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (8323)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (8323)Refutation not found, incomplete strategy% (8323)------------------------------
% (8323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8323)Termination reason: Refutation not found, incomplete strategy

% (8323)Memory used [KB]: 6140
% (8323)Time elapsed: 0.002 s
% (8323)------------------------------
% (8323)------------------------------
fof(f30,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X2,X1)
      | ~ sP0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1)
      | ~ sP1(X0,X2,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(resolution,[],[f113,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3,X4] :
            ( k4_tarski(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ( k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)) = X0
          & r2_hidden(sK9(X0,X1,X2),X1)
          & r2_hidden(sK8(X0,X1,X2),X2) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X5,X6] :
          ( k4_tarski(X5,X6) = X0
          & r2_hidden(X6,X1)
          & r2_hidden(X5,X2) )
     => ( k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)) = X0
        & r2_hidden(sK9(X0,X1,X2),X1)
        & r2_hidden(sK8(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3,X4] :
            ( k4_tarski(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ? [X5,X6] :
            ( k4_tarski(X5,X6) = X0
            & r2_hidden(X6,X1)
            & r2_hidden(X5,X2) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X3,X1,X0] :
      ( ( sP1(X3,X1,X0)
        | ! [X4,X5] :
            ( k4_tarski(X4,X5) != X3
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X0) ) )
      & ( ? [X4,X5] :
            ( k4_tarski(X4,X5) = X3
            & r2_hidden(X5,X1)
            & r2_hidden(X4,X0) )
        | ~ sP1(X3,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f113,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r2_hidden(sK8(X5,X6,X7),X8)
      | ~ sP0(X5,X8)
      | ~ sP1(X5,X6,X7) ) ),
    inference(superposition,[],[f79,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)) = X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f79,plain,(
    ! [X2,X3,X1] :
      ( ~ sP0(k4_tarski(X2,X3),X1)
      | ~ r2_hidden(X2,X1) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X2,X3) != X0
      | ~ r2_hidden(X2,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( k4_tarski(X2,X3) != X0
          | ( ~ r2_hidden(X3,X1)
            & ~ r2_hidden(X2,X1) ) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ! [X2,X3] :
          ( k4_tarski(X2,X3) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP0(X1,X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f450,plain,
    ( ~ spl10_1
    | spl10_3 ),
    inference(avatar_contradiction_clause,[],[f449])).

fof(f449,plain,
    ( $false
    | ~ spl10_1
    | spl10_3 ),
    inference(subsumption_resolution,[],[f448,f286])).

% (8324)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f448,plain,
    ( k1_xboole_0 = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | ~ spl10_1
    | spl10_3 ),
    inference(resolution,[],[f424,f45])).

fof(f45,plain,(
    ! [X0] :
      ( sP0(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f424,plain,
    ( ~ sP0(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | ~ spl10_1
    | spl10_3 ),
    inference(backward_demodulation,[],[f193,f422])).

fof(f193,plain,
    ( ~ sP0(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | spl10_3 ),
    inference(avatar_component_clause,[],[f191])).

fof(f412,plain,(
    ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f411])).

fof(f411,plain,
    ( $false
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f410,f286])).

fof(f410,plain,
    ( k1_xboole_0 = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | ~ spl10_5 ),
    inference(resolution,[],[f408,f45])).

fof(f408,plain,
    ( ~ sP0(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | ~ spl10_5 ),
    inference(resolution,[],[f403,f237])).

fof(f237,plain,
    ( sP1(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl10_5
  <=> sP1(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f403,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f399])).

fof(f399,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1)
      | ~ sP1(X0,X1,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(resolution,[],[f114,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X1)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f114,plain,(
    ! [X12,X10,X11,X9] :
      ( ~ r2_hidden(sK9(X9,X10,X11),X12)
      | ~ sP0(X9,X12)
      | ~ sP1(X9,X10,X11) ) ),
    inference(superposition,[],[f78,f60])).

fof(f78,plain,(
    ! [X2,X3,X1] :
      ( ~ sP0(k4_tarski(X2,X3),X1)
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X2,X3) != X0
      | ~ r2_hidden(X3,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f368,plain,
    ( spl10_5
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f367,f87,f235])).

fof(f87,plain,
    ( spl10_2
  <=> sK3 = k2_mcart_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f367,plain,
    ( sP1(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f362,f286])).

fof(f362,plain,
    ( sP1(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k1_xboole_0 = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | ~ spl10_2 ),
    inference(superposition,[],[f102,f220])).

fof(f220,plain,
    ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k2_zfmisc_1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | ~ spl10_2 ),
    inference(resolution,[],[f187,f81])).

fof(f187,plain,
    ( ! [X0] :
        ( ~ sP2(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0)
        | k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) = X0 )
    | ~ spl10_2 ),
    inference(resolution,[],[f185,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X3)
      | X2 = X3
      | ~ sP2(X0,X1,X2) ) ),
    inference(superposition,[],[f63,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f185,plain,
    ( sP2(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | ~ spl10_2 ),
    inference(superposition,[],[f174,f94])).

fof(f94,plain,
    ( sK3 = k4_tarski(sK4,sK3)
    | ~ spl10_2 ),
    inference(backward_demodulation,[],[f39,f93])).

fof(f93,plain,
    ( sK3 = sK5
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f92,f89])).

fof(f89,plain,
    ( sK3 = k2_mcart_1(sK3)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f92,plain,(
    k2_mcart_1(sK3) = sK5 ),
    inference(superposition,[],[f50,f39])).

fof(f50,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f12])).

fof(f174,plain,
    ( ! [X2] : sP2(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,X2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,k4_tarski(X2,sK3)))
    | ~ spl10_2 ),
    inference(superposition,[],[f81,f167])).

fof(f167,plain,
    ( ! [X0] : k2_zfmisc_1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,X0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,k4_tarski(X0,sK3))
    | ~ spl10_2 ),
    inference(superposition,[],[f75,f94])).

fof(f90,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f40,f87,f83])).

fof(f40,plain,
    ( sK3 = k2_mcart_1(sK3)
    | sK3 = k1_mcart_1(sK3) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 10:35:15 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.48  % (8313)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.50  % (8310)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.52  % (8328)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.23/0.54  % (8336)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.23/0.54  % (8331)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.23/0.54  % (8322)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.55  % (8327)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.23/0.55  % (8311)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.55  % (8312)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.55  % (8311)Refutation not found, incomplete strategy% (8311)------------------------------
% 0.23/0.55  % (8311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (8311)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (8311)Memory used [KB]: 6140
% 0.23/0.55  % (8311)Time elapsed: 0.092 s
% 0.23/0.55  % (8311)------------------------------
% 0.23/0.55  % (8311)------------------------------
% 0.23/0.55  % (8305)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.55  % (8305)Refutation not found, incomplete strategy% (8305)------------------------------
% 0.23/0.55  % (8305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (8305)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (8305)Memory used [KB]: 1663
% 0.23/0.55  % (8305)Time elapsed: 0.124 s
% 0.23/0.55  % (8305)------------------------------
% 0.23/0.55  % (8305)------------------------------
% 0.23/0.55  % (8308)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.55  % (8320)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.56  % (8332)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.56  % (8317)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.23/0.56  % (8317)Refutation not found, incomplete strategy% (8317)------------------------------
% 0.23/0.56  % (8317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (8333)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.23/0.56  % (8335)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.23/0.56  % (8338)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.23/0.57  % (8326)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.23/0.57  % (8319)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.23/0.57  % (8325)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.23/0.57  % (8336)Refutation found. Thanks to Tanya!
% 0.23/0.57  % SZS status Theorem for theBenchmark
% 0.23/0.57  % (8319)Refutation not found, incomplete strategy% (8319)------------------------------
% 0.23/0.57  % (8319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (8328)Refutation not found, incomplete strategy% (8328)------------------------------
% 0.23/0.57  % (8328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (8328)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.57  
% 0.23/0.57  % (8328)Memory used [KB]: 10874
% 0.23/0.57  % (8328)Time elapsed: 0.138 s
% 0.23/0.57  % (8328)------------------------------
% 0.23/0.57  % (8328)------------------------------
% 0.23/0.57  % (8306)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.57  % (8330)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.57  % (8318)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.23/0.57  % (8318)Refutation not found, incomplete strategy% (8318)------------------------------
% 0.23/0.57  % (8318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (8318)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.57  
% 0.23/0.57  % (8318)Memory used [KB]: 10618
% 0.23/0.57  % (8318)Time elapsed: 0.138 s
% 0.23/0.57  % (8318)------------------------------
% 0.23/0.57  % (8318)------------------------------
% 0.23/0.57  % SZS output start Proof for theBenchmark
% 0.23/0.57  fof(f486,plain,(
% 0.23/0.57    $false),
% 0.23/0.57    inference(avatar_sat_refutation,[],[f90,f368,f412,f450,f485])).
% 0.23/0.57  fof(f485,plain,(
% 0.23/0.57    ~spl10_1 | ~spl10_3),
% 0.23/0.57    inference(avatar_contradiction_clause,[],[f484])).
% 0.23/0.57  fof(f484,plain,(
% 0.23/0.57    $false | (~spl10_1 | ~spl10_3)),
% 0.23/0.57    inference(subsumption_resolution,[],[f483,f451])).
% 0.23/0.57  fof(f451,plain,(
% 0.23/0.57    sP0(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | (~spl10_1 | ~spl10_3)),
% 0.23/0.57    inference(forward_demodulation,[],[f192,f422])).
% 0.23/0.57  fof(f422,plain,(
% 0.23/0.57    sK3 = sK4 | ~spl10_1),
% 0.23/0.57    inference(backward_demodulation,[],[f91,f85])).
% 0.23/0.57  fof(f85,plain,(
% 0.23/0.57    sK3 = k1_mcart_1(sK3) | ~spl10_1),
% 0.23/0.57    inference(avatar_component_clause,[],[f83])).
% 0.23/0.57  fof(f83,plain,(
% 0.23/0.57    spl10_1 <=> sK3 = k1_mcart_1(sK3)),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.23/0.57  fof(f91,plain,(
% 0.23/0.57    k1_mcart_1(sK3) = sK4),
% 0.23/0.57    inference(superposition,[],[f49,f39])).
% 0.23/0.57  fof(f39,plain,(
% 0.23/0.57    sK3 = k4_tarski(sK4,sK5)),
% 0.23/0.57    inference(cnf_transformation,[],[f25])).
% 0.23/0.57  fof(f25,plain,(
% 0.23/0.57    (sK3 = k2_mcart_1(sK3) | sK3 = k1_mcart_1(sK3)) & sK3 = k4_tarski(sK4,sK5)),
% 0.23/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f16,f24,f23])).
% 0.23/0.57  fof(f23,plain,(
% 0.23/0.57    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK3 = k2_mcart_1(sK3) | sK3 = k1_mcart_1(sK3)) & ? [X2,X1] : k4_tarski(X1,X2) = sK3)),
% 0.23/0.57    introduced(choice_axiom,[])).
% 0.23/0.57  fof(f24,plain,(
% 0.23/0.57    ? [X2,X1] : k4_tarski(X1,X2) = sK3 => sK3 = k4_tarski(sK4,sK5)),
% 0.23/0.57    introduced(choice_axiom,[])).
% 0.23/0.57  fof(f16,plain,(
% 0.23/0.57    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.23/0.57    inference(ennf_transformation,[],[f15])).
% 0.23/0.57  fof(f15,negated_conjecture,(
% 0.23/0.57    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.23/0.57    inference(negated_conjecture,[],[f14])).
% 0.23/0.57  fof(f14,conjecture,(
% 0.23/0.57    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.23/0.57  fof(f49,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.23/0.57    inference(cnf_transformation,[],[f12])).
% 0.23/0.57  fof(f12,axiom,(
% 0.23/0.57    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.23/0.57  fof(f192,plain,(
% 0.23/0.57    sP0(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) | ~spl10_3),
% 0.23/0.57    inference(avatar_component_clause,[],[f191])).
% 0.23/0.57  fof(f191,plain,(
% 0.23/0.57    spl10_3 <=> sP0(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))),
% 0.23/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.23/0.57  fof(f483,plain,(
% 0.23/0.57    ~sP0(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | ~spl10_1),
% 0.23/0.57    inference(superposition,[],[f481,f423])).
% 0.23/0.57  fof(f423,plain,(
% 0.23/0.57    sK3 = k4_tarski(sK3,sK5) | ~spl10_1),
% 0.23/0.57    inference(backward_demodulation,[],[f39,f422])).
% 0.23/0.57  fof(f481,plain,(
% 0.23/0.57    ( ! [X10] : (~sP0(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,k4_tarski(X10,sK5))),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X10))) ) | ~spl10_1),
% 0.23/0.57    inference(subsumption_resolution,[],[f476,f286])).
% 0.23/0.57  fof(f286,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k1_xboole_0 != k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.23/0.57    inference(superposition,[],[f74,f77])).
% 0.23/0.57  fof(f77,plain,(
% 0.23/0.57    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X3,X3,X3,X3,X3,X3,X3)))) )),
% 0.23/0.57    inference(definition_unfolding,[],[f65,f69,f73,f70,f72])).
% 0.23/0.57  fof(f72,plain,(
% 0.23/0.57    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 0.23/0.57    inference(definition_unfolding,[],[f41,f71])).
% 0.23/0.57  fof(f71,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.23/0.57    inference(definition_unfolding,[],[f48,f70])).
% 0.23/0.57  fof(f48,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f3])).
% 0.23/0.57  fof(f3,axiom,(
% 0.23/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.57  fof(f41,plain,(
% 0.23/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f2])).
% 0.23/0.57  fof(f2,axiom,(
% 0.23/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.23/0.57  fof(f70,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.23/0.57    inference(definition_unfolding,[],[f51,f69])).
% 0.23/0.57  fof(f51,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f4])).
% 0.23/0.57  fof(f4,axiom,(
% 0.23/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.23/0.57  fof(f73,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.23/0.57    inference(definition_unfolding,[],[f47,f71])).
% 0.23/0.57  fof(f47,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f9])).
% 0.23/0.57  fof(f9,axiom,(
% 0.23/0.57    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.23/0.57  fof(f69,plain,(
% 0.23/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.23/0.57    inference(definition_unfolding,[],[f64,f68])).
% 0.23/0.57  fof(f68,plain,(
% 0.23/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.23/0.57    inference(definition_unfolding,[],[f66,f67])).
% 0.23/0.57  fof(f67,plain,(
% 0.23/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f7])).
% 0.23/0.57  fof(f7,axiom,(
% 0.23/0.57    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.23/0.57  fof(f66,plain,(
% 0.23/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f6])).
% 0.23/0.57  fof(f6,axiom,(
% 0.23/0.57    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.23/0.57  fof(f64,plain,(
% 0.23/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f5])).
% 0.23/0.57  fof(f5,axiom,(
% 0.23/0.57    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.23/0.57  fof(f65,plain,(
% 0.23/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.23/0.57    inference(cnf_transformation,[],[f1])).
% 0.23/0.57  fof(f1,axiom,(
% 0.23/0.57    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 0.23/0.57  fof(f74,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1))) )),
% 0.23/0.57    inference(definition_unfolding,[],[f46,f73,f72])).
% 0.23/0.57  fof(f46,plain,(
% 0.23/0.57    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.23/0.57    inference(cnf_transformation,[],[f11])).
% 0.23/0.57  fof(f11,axiom,(
% 0.23/0.57    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.23/0.57  fof(f476,plain,(
% 0.23/0.57    ( ! [X10] : (~sP0(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,k4_tarski(X10,sK5))),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X10)) | k1_xboole_0 = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,k4_tarski(X10,sK5))) ) | ~spl10_1),
% 0.23/0.57    inference(superposition,[],[f154,f430])).
% 0.23/0.57  fof(f430,plain,(
% 0.23/0.57    ( ! [X0] : (k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,k4_tarski(X0,sK5)) = k2_zfmisc_1(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X0),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ) | ~spl10_1),
% 0.23/0.57    inference(superposition,[],[f75,f423])).
% 0.23/0.57  fof(f75,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) = k5_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.23/0.57    inference(definition_unfolding,[],[f53,f71,f72,f71])).
% 0.23/0.57  fof(f53,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.23/0.57    inference(cnf_transformation,[],[f10])).
% 0.23/0.57  fof(f10,axiom,(
% 0.23/0.57    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.23/0.57  fof(f154,plain,(
% 0.23/0.57    ( ! [X6,X7] : (~sP0(sK6(k2_zfmisc_1(X6,X7)),X6) | k1_xboole_0 = k2_zfmisc_1(X6,X7)) )),
% 0.23/0.57    inference(resolution,[],[f151,f102])).
% 0.23/0.57  fof(f102,plain,(
% 0.23/0.57    ( ! [X0,X1] : (sP1(sK6(k2_zfmisc_1(X0,X1)),X1,X0) | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.23/0.57    inference(resolution,[],[f101,f44])).
% 0.23/0.57  fof(f44,plain,(
% 0.23/0.57    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 0.23/0.57    inference(cnf_transformation,[],[f29])).
% 0.23/0.57  fof(f29,plain,(
% 0.23/0.57    ! [X0] : ((sP0(sK6(X0),X0) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 0.23/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f28])).
% 0.23/0.57  fof(f28,plain,(
% 0.23/0.57    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) => (sP0(sK6(X0),X0) & r2_hidden(sK6(X0),X0)))),
% 0.23/0.57    introduced(choice_axiom,[])).
% 0.23/0.57  fof(f19,plain,(
% 0.23/0.57    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.23/0.57    inference(definition_folding,[],[f17,f18])).
% 0.23/0.57  fof(f18,plain,(
% 0.23/0.57    ! [X1,X0] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP0(X1,X0))),
% 0.23/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.23/0.57  % (8317)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.57  fof(f17,plain,(
% 0.23/0.57    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.23/0.57    inference(ennf_transformation,[],[f13])).
% 0.23/0.57  fof(f13,axiom,(
% 0.23/0.57    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.23/0.57  fof(f101,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | sP1(X0,X2,X1)) )),
% 0.23/0.57    inference(resolution,[],[f54,f81])).
% 0.23/0.57  fof(f81,plain,(
% 0.23/0.57    ( ! [X0,X1] : (sP2(X0,X1,k2_zfmisc_1(X0,X1))) )),
% 0.23/0.57    inference(equality_resolution,[],[f62])).
% 0.23/0.57  fof(f62,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.23/0.57    inference(cnf_transformation,[],[f38])).
% 0.23/0.57  fof(f38,plain,(
% 0.23/0.57    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP2(X0,X1,X2)) & (sP2(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 0.23/0.57    inference(nnf_transformation,[],[f22])).
% 0.23/0.57  fof(f22,plain,(
% 0.23/0.57    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP2(X0,X1,X2))),
% 0.23/0.57    inference(definition_folding,[],[f8,f21,f20])).
% 0.23/0.57  fof(f20,plain,(
% 0.23/0.57    ! [X3,X1,X0] : (sP1(X3,X1,X0) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)))),
% 0.23/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.23/0.57  fof(f21,plain,(
% 0.23/0.57    ! [X0,X1,X2] : (sP2(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP1(X3,X1,X0)))),
% 0.23/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.23/0.57  fof(f8,axiom,(
% 0.23/0.57    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.23/0.57  fof(f54,plain,(
% 0.23/0.57    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_hidden(X4,X2) | sP1(X4,X1,X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f33])).
% 0.23/0.57  fof(f33,plain,(
% 0.23/0.57    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((~sP1(sK7(X0,X1,X2),X1,X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP1(sK7(X0,X1,X2),X1,X0) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X4,X1,X0)) & (sP1(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.23/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f32])).
% 0.23/0.57  
% 0.23/0.57  fof(f32,plain,(
% 0.23/0.57    ! [X2,X1,X0] : (? [X3] : ((~sP1(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP1(X3,X1,X0) | r2_hidden(X3,X2))) => ((~sP1(sK7(X0,X1,X2),X1,X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP1(sK7(X0,X1,X2),X1,X0) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 0.23/0.57    introduced(choice_axiom,[])).
% 0.23/0.57  fof(f31,plain,(
% 0.23/0.57    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP1(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X4,X1,X0)) & (sP1(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.23/0.57    inference(rectify,[],[f30])).
% 0.23/0.57  % (8317)Memory used [KB]: 10618
% 0.23/0.57  % (8317)Time elapsed: 0.122 s
% 0.23/0.57  % (8317)------------------------------
% 0.23/0.57  % (8317)------------------------------
% 0.23/0.57  % (8325)Refutation not found, incomplete strategy% (8325)------------------------------
% 0.23/0.57  % (8325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (8319)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (8319)Memory used [KB]: 10618
% 1.56/0.57  % (8319)Time elapsed: 0.135 s
% 1.56/0.57  % (8319)------------------------------
% 1.56/0.57  % (8319)------------------------------
% 1.56/0.57  % (8325)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (8325)Memory used [KB]: 10618
% 1.56/0.57  % (8325)Time elapsed: 0.149 s
% 1.56/0.57  % (8325)------------------------------
% 1.56/0.57  % (8325)------------------------------
% 1.56/0.58  % (8337)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.56/0.58  % (8323)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.56/0.58  % (8323)Refutation not found, incomplete strategy% (8323)------------------------------
% 1.56/0.58  % (8323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (8323)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  
% 1.56/0.58  % (8323)Memory used [KB]: 6140
% 1.56/0.58  % (8323)Time elapsed: 0.002 s
% 1.56/0.58  % (8323)------------------------------
% 1.56/0.58  % (8323)------------------------------
% 1.56/0.58  fof(f30,plain,(
% 1.56/0.58    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP1(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP1(X3,X1,X0)) & (sP1(X3,X1,X0) | ~r2_hidden(X3,X2))) | ~sP2(X0,X1,X2)))),
% 1.56/0.58    inference(nnf_transformation,[],[f21])).
% 1.56/0.58  fof(f151,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (~sP1(X0,X2,X1) | ~sP0(X0,X1)) )),
% 1.56/0.58    inference(duplicate_literal_removal,[],[f147])).
% 1.56/0.58  fof(f147,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (~sP0(X0,X1) | ~sP1(X0,X2,X1) | ~sP1(X0,X2,X1)) )),
% 1.56/0.58    inference(resolution,[],[f113,f58])).
% 1.56/0.58  fof(f58,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X2) | ~sP1(X0,X1,X2)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f37])).
% 1.56/0.58  fof(f37,plain,(
% 1.56/0.58    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & ((k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)) = X0 & r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X2)) | ~sP1(X0,X1,X2)))),
% 1.56/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f35,f36])).
% 1.56/0.58  fof(f36,plain,(
% 1.56/0.58    ! [X2,X1,X0] : (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) => (k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)) = X0 & r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X2)))),
% 1.56/0.58    introduced(choice_axiom,[])).
% 1.56/0.58  fof(f35,plain,(
% 1.56/0.58    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) | ~sP1(X0,X1,X2)))),
% 1.56/0.58    inference(rectify,[],[f34])).
% 1.56/0.58  fof(f34,plain,(
% 1.56/0.58    ! [X3,X1,X0] : ((sP1(X3,X1,X0) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~sP1(X3,X1,X0)))),
% 1.56/0.58    inference(nnf_transformation,[],[f20])).
% 1.56/0.58  fof(f113,plain,(
% 1.56/0.58    ( ! [X6,X8,X7,X5] : (~r2_hidden(sK8(X5,X6,X7),X8) | ~sP0(X5,X8) | ~sP1(X5,X6,X7)) )),
% 1.56/0.58    inference(superposition,[],[f79,f60])).
% 1.56/0.58  fof(f60,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (k4_tarski(sK8(X0,X1,X2),sK9(X0,X1,X2)) = X0 | ~sP1(X0,X1,X2)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f37])).
% 1.56/0.58  fof(f79,plain,(
% 1.56/0.58    ( ! [X2,X3,X1] : (~sP0(k4_tarski(X2,X3),X1) | ~r2_hidden(X2,X1)) )),
% 1.56/0.58    inference(equality_resolution,[],[f42])).
% 1.56/0.58  fof(f42,plain,(
% 1.56/0.58    ( ! [X2,X0,X3,X1] : (k4_tarski(X2,X3) != X0 | ~r2_hidden(X2,X1) | ~sP0(X0,X1)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f27])).
% 1.56/0.58  fof(f27,plain,(
% 1.56/0.58    ! [X0,X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X0 | (~r2_hidden(X3,X1) & ~r2_hidden(X2,X1))) | ~sP0(X0,X1))),
% 1.56/0.58    inference(rectify,[],[f26])).
% 1.56/0.58  fof(f26,plain,(
% 1.56/0.58    ! [X1,X0] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP0(X1,X0))),
% 1.56/0.58    inference(nnf_transformation,[],[f18])).
% 1.56/0.58  fof(f450,plain,(
% 1.56/0.58    ~spl10_1 | spl10_3),
% 1.56/0.58    inference(avatar_contradiction_clause,[],[f449])).
% 1.56/0.58  fof(f449,plain,(
% 1.56/0.58    $false | (~spl10_1 | spl10_3)),
% 1.56/0.58    inference(subsumption_resolution,[],[f448,f286])).
% 1.56/0.58  % (8324)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.56/0.58  fof(f448,plain,(
% 1.56/0.58    k1_xboole_0 = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) | (~spl10_1 | spl10_3)),
% 1.56/0.58    inference(resolution,[],[f424,f45])).
% 1.56/0.58  fof(f45,plain,(
% 1.56/0.58    ( ! [X0] : (sP0(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 1.56/0.58    inference(cnf_transformation,[],[f29])).
% 1.56/0.58  fof(f424,plain,(
% 1.56/0.58    ~sP0(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | (~spl10_1 | spl10_3)),
% 1.56/0.58    inference(backward_demodulation,[],[f193,f422])).
% 1.56/0.58  fof(f193,plain,(
% 1.56/0.58    ~sP0(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) | spl10_3),
% 1.56/0.58    inference(avatar_component_clause,[],[f191])).
% 1.56/0.58  fof(f412,plain,(
% 1.56/0.58    ~spl10_5),
% 1.56/0.58    inference(avatar_contradiction_clause,[],[f411])).
% 1.56/0.58  fof(f411,plain,(
% 1.56/0.58    $false | ~spl10_5),
% 1.56/0.58    inference(subsumption_resolution,[],[f410,f286])).
% 1.56/0.58  fof(f410,plain,(
% 1.56/0.58    k1_xboole_0 = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) | ~spl10_5),
% 1.56/0.58    inference(resolution,[],[f408,f45])).
% 1.56/0.58  fof(f408,plain,(
% 1.56/0.58    ~sP0(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | ~spl10_5),
% 1.56/0.58    inference(resolution,[],[f403,f237])).
% 1.56/0.58  fof(f237,plain,(
% 1.56/0.58    sP1(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) | ~spl10_5),
% 1.56/0.58    inference(avatar_component_clause,[],[f235])).
% 1.56/0.58  fof(f235,plain,(
% 1.56/0.58    spl10_5 <=> sP1(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))),
% 1.56/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.56/0.58  fof(f403,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X0,X1)) )),
% 1.56/0.58    inference(duplicate_literal_removal,[],[f399])).
% 1.56/0.58  fof(f399,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (~sP0(X0,X1) | ~sP1(X0,X1,X2) | ~sP1(X0,X1,X2)) )),
% 1.56/0.58    inference(resolution,[],[f114,f59])).
% 1.56/0.58  fof(f59,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),X1) | ~sP1(X0,X1,X2)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f37])).
% 1.56/0.58  fof(f114,plain,(
% 1.56/0.58    ( ! [X12,X10,X11,X9] : (~r2_hidden(sK9(X9,X10,X11),X12) | ~sP0(X9,X12) | ~sP1(X9,X10,X11)) )),
% 1.56/0.58    inference(superposition,[],[f78,f60])).
% 1.56/0.58  fof(f78,plain,(
% 1.56/0.58    ( ! [X2,X3,X1] : (~sP0(k4_tarski(X2,X3),X1) | ~r2_hidden(X3,X1)) )),
% 1.56/0.58    inference(equality_resolution,[],[f43])).
% 1.56/0.58  fof(f43,plain,(
% 1.56/0.58    ( ! [X2,X0,X3,X1] : (k4_tarski(X2,X3) != X0 | ~r2_hidden(X3,X1) | ~sP0(X0,X1)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f27])).
% 1.56/0.58  fof(f368,plain,(
% 1.56/0.58    spl10_5 | ~spl10_2),
% 1.56/0.58    inference(avatar_split_clause,[],[f367,f87,f235])).
% 1.56/0.58  fof(f87,plain,(
% 1.56/0.58    spl10_2 <=> sK3 = k2_mcart_1(sK3)),
% 1.56/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.56/0.58  fof(f367,plain,(
% 1.56/0.58    sP1(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) | ~spl10_2),
% 1.56/0.58    inference(subsumption_resolution,[],[f362,f286])).
% 1.56/0.58  fof(f362,plain,(
% 1.56/0.58    sP1(sK6(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) | k1_xboole_0 = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) | ~spl10_2),
% 1.56/0.58    inference(superposition,[],[f102,f220])).
% 1.56/0.58  fof(f220,plain,(
% 1.56/0.58    k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k2_zfmisc_1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | ~spl10_2),
% 1.56/0.58    inference(resolution,[],[f187,f81])).
% 1.56/0.58  fof(f187,plain,(
% 1.56/0.58    ( ! [X0] : (~sP2(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),X0) | k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) = X0) ) | ~spl10_2),
% 1.56/0.58    inference(resolution,[],[f185,f99])).
% 1.56/0.58  fof(f99,plain,(
% 1.56/0.58    ( ! [X2,X0,X3,X1] : (~sP2(X0,X1,X3) | X2 = X3 | ~sP2(X0,X1,X2)) )),
% 1.56/0.58    inference(superposition,[],[f63,f63])).
% 1.56/0.58  fof(f63,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | ~sP2(X0,X1,X2)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f38])).
% 1.56/0.58  fof(f185,plain,(
% 1.56/0.58    sP2(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | ~spl10_2),
% 1.56/0.58    inference(superposition,[],[f174,f94])).
% 1.56/0.58  fof(f94,plain,(
% 1.56/0.58    sK3 = k4_tarski(sK4,sK3) | ~spl10_2),
% 1.56/0.58    inference(backward_demodulation,[],[f39,f93])).
% 1.56/0.58  fof(f93,plain,(
% 1.56/0.58    sK3 = sK5 | ~spl10_2),
% 1.56/0.58    inference(forward_demodulation,[],[f92,f89])).
% 1.56/0.58  fof(f89,plain,(
% 1.56/0.58    sK3 = k2_mcart_1(sK3) | ~spl10_2),
% 1.56/0.58    inference(avatar_component_clause,[],[f87])).
% 1.56/0.58  fof(f92,plain,(
% 1.56/0.58    k2_mcart_1(sK3) = sK5),
% 1.56/0.58    inference(superposition,[],[f50,f39])).
% 1.56/0.58  fof(f50,plain,(
% 1.56/0.58    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.56/0.58    inference(cnf_transformation,[],[f12])).
% 1.56/0.58  fof(f174,plain,(
% 1.56/0.58    ( ! [X2] : (sP2(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,X2),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,k4_tarski(X2,sK3)))) ) | ~spl10_2),
% 1.56/0.58    inference(superposition,[],[f81,f167])).
% 1.56/0.58  fof(f167,plain,(
% 1.56/0.58    ( ! [X0] : (k2_zfmisc_1(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,X0),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,k4_tarski(X0,sK3))) ) | ~spl10_2),
% 1.56/0.58    inference(superposition,[],[f75,f94])).
% 1.56/0.58  fof(f90,plain,(
% 1.56/0.58    spl10_1 | spl10_2),
% 1.56/0.58    inference(avatar_split_clause,[],[f40,f87,f83])).
% 1.56/0.58  fof(f40,plain,(
% 1.56/0.58    sK3 = k2_mcart_1(sK3) | sK3 = k1_mcart_1(sK3)),
% 1.56/0.58    inference(cnf_transformation,[],[f25])).
% 1.56/0.58  % SZS output end Proof for theBenchmark
% 1.56/0.58  % (8336)------------------------------
% 1.56/0.58  % (8336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (8336)Termination reason: Refutation
% 1.56/0.58  
% 1.56/0.58  % (8336)Memory used [KB]: 6524
% 1.56/0.58  % (8336)Time elapsed: 0.157 s
% 1.56/0.58  % (8336)------------------------------
% 1.56/0.58  % (8336)------------------------------
% 1.56/0.58  % (8321)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.56/0.58  % (8299)Success in time 0.2 s
%------------------------------------------------------------------------------
