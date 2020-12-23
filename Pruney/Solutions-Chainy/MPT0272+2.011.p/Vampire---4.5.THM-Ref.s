%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:13 EST 2020

% Result     : Theorem 2.65s
% Output     : Refutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 258 expanded)
%              Number of leaves         :   21 (  84 expanded)
%              Depth                    :   13
%              Number of atoms          :  235 ( 429 expanded)
%              Number of equality atoms :   86 ( 260 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2251,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f642,f2227,f2250])).

fof(f2250,plain,
    ( spl6_1
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f2245])).

fof(f2245,plain,
    ( $false
    | spl6_1
    | ~ spl6_3 ),
    inference(resolution,[],[f2240,f77])).

fof(f77,plain,(
    ! [X2,X3,X1] : sP1(X1,X1,X2,X3) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP1(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP1(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP1(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP1(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X4,X2,X1,X0] :
      ( sP1(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2240,plain,
    ( ! [X4,X2,X3] : ~ sP1(sK3,X2,X3,X4)
    | spl6_1
    | ~ spl6_3 ),
    inference(resolution,[],[f2237,f177])).

fof(f177,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k5_enumset1(X3,X3,X3,X3,X3,X2,X1))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(resolution,[],[f56,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] : sP2(X0,X1,X2,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f63,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP2(X0,X1,X2,X3) )
      & ( sP2(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP2(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f19,f23,f22])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( sP2(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP1(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3)
      | ~ sP1(X5,X2,X1,X0)
      | r2_hidden(X5,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ( ( ~ sP1(sK5(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
          & ( sP1(sK5(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP1(X5,X2,X1,X0) )
            & ( sP1(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

fof(f32,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP1(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP1(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP1(sK5(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( sP1(sK5(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP1(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP1(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP1(X5,X2,X1,X0) )
            & ( sP1(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP1(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP1(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP1(X4,X2,X1,X0) )
            & ( sP1(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f2237,plain,
    ( ! [X1] : ~ r2_hidden(sK3,X1)
    | spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f2236,f635])).

fof(f635,plain,
    ( ~ r2_hidden(sK3,sK4)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f633])).

fof(f633,plain,
    ( spl6_1
  <=> r2_hidden(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f2236,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3,X1)
        | r2_hidden(sK3,sK4) )
    | ~ spl6_3 ),
    inference(duplicate_literal_removal,[],[f2233])).

fof(f2233,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3,X1)
        | r2_hidden(sK3,sK4)
        | ~ r2_hidden(sK3,X1) )
    | ~ spl6_3 ),
    inference(resolution,[],[f2228,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(X1,X2)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) ) ) )
      & ( ( ( ~ r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) )
          & ( r2_hidden(X1,X0)
            | r2_hidden(X1,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2228,plain,
    ( ! [X0] :
        ( ~ sP0(sK4,sK3,X0)
        | ~ r2_hidden(sK3,X0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f2073,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ sP0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ~ sP0(X2,X0,X1) )
      & ( sP0(X2,X0,X1)
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> sP0(X2,X0,X1) ) ),
    inference(definition_folding,[],[f18,f20])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f2073,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3,k5_xboole_0(X1,sK4))
        | ~ r2_hidden(sK3,X1) )
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f2072])).

fof(f2072,plain,
    ( spl6_3
  <=> ! [X1] :
        ( ~ r2_hidden(sK3,X1)
        | ~ r2_hidden(sK3,k5_xboole_0(X1,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f2227,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f2225,f2072])).

fof(f2225,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK3,X2)
      | ~ r2_hidden(sK3,k5_xboole_0(X2,sK4)) ) ),
    inference(trivial_inequality_removal,[],[f2222])).

fof(f2222,plain,(
    ! [X2] :
      ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)
      | ~ r2_hidden(sK3,X2)
      | ~ r2_hidden(sK3,k5_xboole_0(X2,sK4)) ) ),
    inference(superposition,[],[f2034,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f71,f71])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f69])).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f2034,plain,(
    ! [X0] :
      ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k3_xboole_0(k5_xboole_0(X0,sK4),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))
      | ~ r2_hidden(sK3,X0) ) ),
    inference(superposition,[],[f113,f608])).

fof(f608,plain,(
    ! [X6,X4,X5] :
      ( k3_xboole_0(k5_xboole_0(X4,X6),k5_enumset1(X5,X5,X5,X5,X5,X5,X5)) = k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X5),k3_xboole_0(X6,k5_enumset1(X5,X5,X5,X5,X5,X5,X5)))
      | ~ r2_hidden(X5,X4) ) ),
    inference(superposition,[],[f47,f74])).

fof(f47,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f113,plain,(
    k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(sK4,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
    inference(forward_demodulation,[],[f72,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f72,plain,(
    k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) ),
    inference(definition_unfolding,[],[f39,f71,f44,f71])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f39,plain,(
    k1_tarski(sK3) != k4_xboole_0(k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k1_tarski(sK3) != k4_xboole_0(k1_tarski(sK3),sK4)
    & k1_xboole_0 != k4_xboole_0(k1_tarski(sK3),sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f16,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
        & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK3) != k4_xboole_0(k1_tarski(sK3),sK4)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(sK3),sK4) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(f642,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f641,f633])).

fof(f641,plain,(
    ~ r2_hidden(sK3,sK4) ),
    inference(subsumption_resolution,[],[f622,f40])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f622,plain,
    ( k1_xboole_0 != k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))
    | ~ r2_hidden(sK3,sK4) ),
    inference(superposition,[],[f81,f74])).

fof(f81,plain,(
    k1_xboole_0 != k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(sK4,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
    inference(forward_demodulation,[],[f73,f42])).

fof(f73,plain,(
    k1_xboole_0 != k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4)) ),
    inference(definition_unfolding,[],[f38,f44,f71])).

fof(f38,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:30:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (23538)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (23560)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (23536)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (23539)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (23544)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (23565)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (23546)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (23549)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (23541)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (23542)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (23562)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (23550)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (23544)Refutation not found, incomplete strategy% (23544)------------------------------
% 0.21/0.53  % (23544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23544)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23544)Memory used [KB]: 10618
% 0.21/0.53  % (23544)Time elapsed: 0.125 s
% 0.21/0.53  % (23544)------------------------------
% 0.21/0.53  % (23544)------------------------------
% 0.21/0.53  % (23537)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (23538)Refutation not found, incomplete strategy% (23538)------------------------------
% 0.21/0.53  % (23538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23538)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23538)Memory used [KB]: 10618
% 0.21/0.53  % (23538)Time elapsed: 0.124 s
% 0.21/0.53  % (23538)------------------------------
% 0.21/0.53  % (23538)------------------------------
% 0.21/0.54  % (23551)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (23553)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (23555)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (23546)Refutation not found, incomplete strategy% (23546)------------------------------
% 0.21/0.54  % (23546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23546)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23546)Memory used [KB]: 10618
% 0.21/0.54  % (23546)Time elapsed: 0.140 s
% 0.21/0.54  % (23546)------------------------------
% 0.21/0.54  % (23546)------------------------------
% 0.21/0.54  % (23564)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (23543)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (23557)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (23563)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (23540)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (23561)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (23547)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (23554)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (23547)Refutation not found, incomplete strategy% (23547)------------------------------
% 0.21/0.55  % (23547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (23547)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (23547)Memory used [KB]: 10618
% 0.21/0.55  % (23547)Time elapsed: 0.150 s
% 0.21/0.55  % (23547)------------------------------
% 0.21/0.55  % (23547)------------------------------
% 0.21/0.55  % (23545)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (23558)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (23553)Refutation not found, incomplete strategy% (23553)------------------------------
% 0.21/0.55  % (23553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (23553)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (23553)Memory used [KB]: 10618
% 0.21/0.55  % (23553)Time elapsed: 0.131 s
% 0.21/0.55  % (23553)------------------------------
% 0.21/0.55  % (23553)------------------------------
% 0.21/0.55  % (23556)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (23552)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (23559)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (23559)Refutation not found, incomplete strategy% (23559)------------------------------
% 0.21/0.56  % (23559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (23559)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (23559)Memory used [KB]: 1663
% 0.21/0.56  % (23559)Time elapsed: 0.108 s
% 0.21/0.56  % (23559)------------------------------
% 0.21/0.56  % (23559)------------------------------
% 0.21/0.56  % (23556)Refutation not found, incomplete strategy% (23556)------------------------------
% 0.21/0.56  % (23556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (23548)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (23556)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (23556)Memory used [KB]: 10746
% 0.21/0.56  % (23556)Time elapsed: 0.149 s
% 0.21/0.56  % (23556)------------------------------
% 0.21/0.56  % (23556)------------------------------
% 1.60/0.57  % (23557)Refutation not found, incomplete strategy% (23557)------------------------------
% 1.60/0.57  % (23557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (23557)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.58  
% 1.60/0.58  % (23557)Memory used [KB]: 1663
% 1.60/0.58  % (23557)Time elapsed: 0.158 s
% 1.60/0.58  % (23557)------------------------------
% 1.60/0.58  % (23557)------------------------------
% 2.09/0.66  % (23626)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.09/0.67  % (23641)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.09/0.67  % (23625)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.09/0.68  % (23637)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.09/0.68  % (23630)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.09/0.69  % (23650)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.09/0.69  % (23645)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.09/0.71  % (23657)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.65/0.71  % (23563)Refutation found. Thanks to Tanya!
% 2.65/0.71  % SZS status Theorem for theBenchmark
% 2.65/0.71  % SZS output start Proof for theBenchmark
% 2.65/0.71  fof(f2251,plain,(
% 2.65/0.71    $false),
% 2.65/0.71    inference(avatar_sat_refutation,[],[f642,f2227,f2250])).
% 2.65/0.71  fof(f2250,plain,(
% 2.65/0.71    spl6_1 | ~spl6_3),
% 2.65/0.71    inference(avatar_contradiction_clause,[],[f2245])).
% 2.65/0.71  fof(f2245,plain,(
% 2.65/0.71    $false | (spl6_1 | ~spl6_3)),
% 2.65/0.71    inference(resolution,[],[f2240,f77])).
% 2.65/0.71  fof(f77,plain,(
% 2.65/0.71    ( ! [X2,X3,X1] : (sP1(X1,X1,X2,X3)) )),
% 2.65/0.71    inference(equality_resolution,[],[f62])).
% 2.65/0.71  fof(f62,plain,(
% 2.65/0.71    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | X0 != X1) )),
% 2.65/0.71    inference(cnf_transformation,[],[f36])).
% 2.65/0.71  fof(f36,plain,(
% 2.65/0.71    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP1(X0,X1,X2,X3)))),
% 2.65/0.71    inference(rectify,[],[f35])).
% 2.65/0.71  fof(f35,plain,(
% 2.65/0.71    ! [X4,X2,X1,X0] : ((sP1(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP1(X4,X2,X1,X0)))),
% 2.65/0.71    inference(flattening,[],[f34])).
% 2.65/0.71  fof(f34,plain,(
% 2.65/0.71    ! [X4,X2,X1,X0] : ((sP1(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP1(X4,X2,X1,X0)))),
% 2.65/0.71    inference(nnf_transformation,[],[f22])).
% 2.65/0.71  fof(f22,plain,(
% 2.65/0.71    ! [X4,X2,X1,X0] : (sP1(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 2.65/0.71    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.65/0.71  fof(f2240,plain,(
% 2.65/0.71    ( ! [X4,X2,X3] : (~sP1(sK3,X2,X3,X4)) ) | (spl6_1 | ~spl6_3)),
% 2.65/0.71    inference(resolution,[],[f2237,f177])).
% 2.65/0.71  fof(f177,plain,(
% 2.65/0.71    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k5_enumset1(X3,X3,X3,X3,X3,X2,X1)) | ~sP1(X0,X1,X2,X3)) )),
% 2.65/0.71    inference(resolution,[],[f56,f80])).
% 2.65/0.71  fof(f80,plain,(
% 2.65/0.71    ( ! [X2,X0,X1] : (sP2(X0,X1,X2,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) )),
% 2.65/0.71    inference(equality_resolution,[],[f76])).
% 2.65/0.71  fof(f76,plain,(
% 2.65/0.71    ( ! [X2,X0,X3,X1] : (sP2(X0,X1,X2,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.65/0.71    inference(definition_unfolding,[],[f63,f69])).
% 2.65/0.71  fof(f69,plain,(
% 2.65/0.71    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 2.65/0.71    inference(definition_unfolding,[],[f46,f68])).
% 2.65/0.71  fof(f68,plain,(
% 2.65/0.71    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 2.65/0.71    inference(definition_unfolding,[],[f54,f67])).
% 2.65/0.71  fof(f67,plain,(
% 2.65/0.71    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 2.65/0.71    inference(definition_unfolding,[],[f65,f66])).
% 2.65/0.71  fof(f66,plain,(
% 2.65/0.71    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.65/0.71    inference(cnf_transformation,[],[f12])).
% 2.65/0.71  fof(f12,axiom,(
% 2.65/0.71    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.65/0.71  fof(f65,plain,(
% 2.65/0.71    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.65/0.71    inference(cnf_transformation,[],[f11])).
% 2.65/0.71  fof(f11,axiom,(
% 2.65/0.71    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.65/0.71  fof(f54,plain,(
% 2.65/0.71    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.65/0.71    inference(cnf_transformation,[],[f10])).
% 2.65/0.71  fof(f10,axiom,(
% 2.65/0.71    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.65/0.71  fof(f46,plain,(
% 2.65/0.71    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.65/0.71    inference(cnf_transformation,[],[f9])).
% 2.65/0.71  fof(f9,axiom,(
% 2.65/0.71    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.65/0.71  fof(f63,plain,(
% 2.65/0.71    ( ! [X2,X0,X3,X1] : (sP2(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.65/0.71    inference(cnf_transformation,[],[f37])).
% 2.65/0.71  fof(f37,plain,(
% 2.65/0.71    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP2(X0,X1,X2,X3)) & (sP2(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 2.65/0.71    inference(nnf_transformation,[],[f24])).
% 2.65/0.71  fof(f24,plain,(
% 2.65/0.71    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP2(X0,X1,X2,X3))),
% 2.65/0.71    inference(definition_folding,[],[f19,f23,f22])).
% 2.65/0.71  fof(f23,plain,(
% 2.65/0.71    ! [X0,X1,X2,X3] : (sP2(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP1(X4,X2,X1,X0)))),
% 2.65/0.71    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.65/0.71  fof(f19,plain,(
% 2.65/0.71    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.65/0.71    inference(ennf_transformation,[],[f6])).
% 2.65/0.71  fof(f6,axiom,(
% 2.65/0.71    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 2.65/0.71  fof(f56,plain,(
% 2.65/0.71    ( ! [X2,X0,X5,X3,X1] : (~sP2(X0,X1,X2,X3) | ~sP1(X5,X2,X1,X0) | r2_hidden(X5,X3)) )),
% 2.65/0.71    inference(cnf_transformation,[],[f33])).
% 2.65/0.71  fof(f33,plain,(
% 2.65/0.71    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | ((~sP1(sK5(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sP1(sK5(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP1(X5,X2,X1,X0)) & (sP1(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP2(X0,X1,X2,X3)))),
% 2.65/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).
% 2.65/0.71  fof(f32,plain,(
% 2.65/0.71    ! [X3,X2,X1,X0] : (? [X4] : ((~sP1(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP1(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP1(sK5(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK5(X0,X1,X2,X3),X3)) & (sP1(sK5(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK5(X0,X1,X2,X3),X3))))),
% 2.65/0.71    introduced(choice_axiom,[])).
% 2.65/0.71  fof(f31,plain,(
% 2.65/0.71    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | ? [X4] : ((~sP1(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP1(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP1(X5,X2,X1,X0)) & (sP1(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP2(X0,X1,X2,X3)))),
% 2.65/0.71    inference(rectify,[],[f30])).
% 2.65/0.71  fof(f30,plain,(
% 2.65/0.71    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | ? [X4] : ((~sP1(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP1(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP1(X4,X2,X1,X0)) & (sP1(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP2(X0,X1,X2,X3)))),
% 2.65/0.71    inference(nnf_transformation,[],[f23])).
% 2.65/0.71  fof(f2237,plain,(
% 2.65/0.71    ( ! [X1] : (~r2_hidden(sK3,X1)) ) | (spl6_1 | ~spl6_3)),
% 2.65/0.71    inference(subsumption_resolution,[],[f2236,f635])).
% 2.65/0.71  fof(f635,plain,(
% 2.65/0.71    ~r2_hidden(sK3,sK4) | spl6_1),
% 2.65/0.71    inference(avatar_component_clause,[],[f633])).
% 2.65/0.71  fof(f633,plain,(
% 2.65/0.71    spl6_1 <=> r2_hidden(sK3,sK4)),
% 2.65/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.65/0.71  fof(f2236,plain,(
% 2.65/0.71    ( ! [X1] : (~r2_hidden(sK3,X1) | r2_hidden(sK3,sK4)) ) | ~spl6_3),
% 2.65/0.71    inference(duplicate_literal_removal,[],[f2233])).
% 2.65/0.71  fof(f2233,plain,(
% 2.65/0.71    ( ! [X1] : (~r2_hidden(sK3,X1) | r2_hidden(sK3,sK4) | ~r2_hidden(sK3,X1)) ) | ~spl6_3),
% 2.65/0.71    inference(resolution,[],[f2228,f50])).
% 2.65/0.71  fof(f50,plain,(
% 2.65/0.71    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 2.65/0.71    inference(cnf_transformation,[],[f28])).
% 2.65/0.71  fof(f28,plain,(
% 2.65/0.71    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~r2_hidden(X1,X2)))) & (((~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & (r2_hidden(X1,X0) | r2_hidden(X1,X2))) | ~sP0(X0,X1,X2)))),
% 2.65/0.71    inference(rectify,[],[f27])).
% 2.65/0.71  fof(f27,plain,(
% 2.65/0.71    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~sP0(X2,X0,X1)))),
% 2.65/0.71    inference(nnf_transformation,[],[f20])).
% 2.65/0.71  fof(f20,plain,(
% 2.65/0.71    ! [X2,X0,X1] : (sP0(X2,X0,X1) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.65/0.71    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.65/0.71  fof(f2228,plain,(
% 2.65/0.71    ( ! [X0] : (~sP0(sK4,sK3,X0) | ~r2_hidden(sK3,X0)) ) | ~spl6_3),
% 2.65/0.71    inference(resolution,[],[f2073,f53])).
% 2.65/0.71  fof(f53,plain,(
% 2.65/0.71    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP0(X2,X0,X1)) )),
% 2.65/0.71    inference(cnf_transformation,[],[f29])).
% 2.65/0.71  fof(f29,plain,(
% 2.65/0.71    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP0(X2,X0,X1)) & (sP0(X2,X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 2.65/0.71    inference(nnf_transformation,[],[f21])).
% 2.65/0.71  fof(f21,plain,(
% 2.65/0.71    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> sP0(X2,X0,X1))),
% 2.65/0.71    inference(definition_folding,[],[f18,f20])).
% 2.65/0.71  fof(f18,plain,(
% 2.65/0.71    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.65/0.71    inference(ennf_transformation,[],[f2])).
% 2.65/0.71  fof(f2,axiom,(
% 2.65/0.71    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 2.65/0.71  fof(f2073,plain,(
% 2.65/0.71    ( ! [X1] : (~r2_hidden(sK3,k5_xboole_0(X1,sK4)) | ~r2_hidden(sK3,X1)) ) | ~spl6_3),
% 2.65/0.71    inference(avatar_component_clause,[],[f2072])).
% 2.65/0.71  fof(f2072,plain,(
% 2.65/0.71    spl6_3 <=> ! [X1] : (~r2_hidden(sK3,X1) | ~r2_hidden(sK3,k5_xboole_0(X1,sK4)))),
% 2.65/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.65/0.71  fof(f2227,plain,(
% 2.65/0.71    spl6_3),
% 2.65/0.71    inference(avatar_split_clause,[],[f2225,f2072])).
% 2.65/0.71  fof(f2225,plain,(
% 2.65/0.71    ( ! [X2] : (~r2_hidden(sK3,X2) | ~r2_hidden(sK3,k5_xboole_0(X2,sK4))) )),
% 2.65/0.71    inference(trivial_inequality_removal,[],[f2222])).
% 2.65/0.71  fof(f2222,plain,(
% 2.65/0.71    ( ! [X2] : (k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) | ~r2_hidden(sK3,X2) | ~r2_hidden(sK3,k5_xboole_0(X2,sK4))) )),
% 2.65/0.71    inference(superposition,[],[f2034,f74])).
% 2.65/0.71  fof(f74,plain,(
% 2.65/0.71    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) | ~r2_hidden(X0,X1)) )),
% 2.65/0.71    inference(definition_unfolding,[],[f45,f71,f71])).
% 2.65/0.71  fof(f71,plain,(
% 2.65/0.71    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 2.65/0.71    inference(definition_unfolding,[],[f41,f70])).
% 2.65/0.71  fof(f70,plain,(
% 2.65/0.71    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 2.65/0.71    inference(definition_unfolding,[],[f43,f69])).
% 2.65/0.71  fof(f43,plain,(
% 2.65/0.71    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.65/0.71    inference(cnf_transformation,[],[f8])).
% 2.65/0.71  fof(f8,axiom,(
% 2.65/0.71    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.65/0.71  fof(f41,plain,(
% 2.65/0.71    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.65/0.71    inference(cnf_transformation,[],[f7])).
% 2.65/0.71  fof(f7,axiom,(
% 2.65/0.71    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.65/0.71  fof(f45,plain,(
% 2.65/0.71    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 2.65/0.71    inference(cnf_transformation,[],[f17])).
% 2.65/0.71  fof(f17,plain,(
% 2.65/0.71    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 2.65/0.71    inference(ennf_transformation,[],[f13])).
% 2.65/0.71  fof(f13,axiom,(
% 2.65/0.71    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 2.65/0.71  fof(f2034,plain,(
% 2.65/0.71    ( ! [X0] : (k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k3_xboole_0(k5_xboole_0(X0,sK4),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | ~r2_hidden(sK3,X0)) )),
% 2.65/0.71    inference(superposition,[],[f113,f608])).
% 2.65/0.71  fof(f608,plain,(
% 2.65/0.71    ( ! [X6,X4,X5] : (k3_xboole_0(k5_xboole_0(X4,X6),k5_enumset1(X5,X5,X5,X5,X5,X5,X5)) = k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X5),k3_xboole_0(X6,k5_enumset1(X5,X5,X5,X5,X5,X5,X5))) | ~r2_hidden(X5,X4)) )),
% 2.65/0.71    inference(superposition,[],[f47,f74])).
% 2.65/0.71  fof(f47,plain,(
% 2.65/0.71    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 2.65/0.71    inference(cnf_transformation,[],[f4])).
% 2.65/0.71  fof(f4,axiom,(
% 2.65/0.71    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 2.65/0.71  fof(f113,plain,(
% 2.65/0.71    k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(sK4,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),
% 2.65/0.71    inference(forward_demodulation,[],[f72,f42])).
% 2.65/0.71  fof(f42,plain,(
% 2.65/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.65/0.71    inference(cnf_transformation,[],[f1])).
% 2.65/0.71  fof(f1,axiom,(
% 2.65/0.71    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.65/0.71  fof(f72,plain,(
% 2.65/0.71    k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))),
% 2.65/0.71    inference(definition_unfolding,[],[f39,f71,f44,f71])).
% 2.65/0.71  fof(f44,plain,(
% 2.65/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.65/0.71    inference(cnf_transformation,[],[f3])).
% 2.65/0.71  fof(f3,axiom,(
% 2.65/0.71    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.65/0.71  fof(f39,plain,(
% 2.65/0.71    k1_tarski(sK3) != k4_xboole_0(k1_tarski(sK3),sK4)),
% 2.65/0.71    inference(cnf_transformation,[],[f26])).
% 2.65/0.71  fof(f26,plain,(
% 2.65/0.71    k1_tarski(sK3) != k4_xboole_0(k1_tarski(sK3),sK4) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK3),sK4)),
% 2.65/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f16,f25])).
% 2.65/0.71  fof(f25,plain,(
% 2.65/0.71    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK3) != k4_xboole_0(k1_tarski(sK3),sK4) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK3),sK4))),
% 2.65/0.71    introduced(choice_axiom,[])).
% 2.65/0.71  fof(f16,plain,(
% 2.65/0.71    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1))),
% 2.65/0.71    inference(ennf_transformation,[],[f15])).
% 2.65/0.71  fof(f15,negated_conjecture,(
% 2.65/0.71    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 2.65/0.71    inference(negated_conjecture,[],[f14])).
% 2.65/0.71  fof(f14,conjecture,(
% 2.65/0.71    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).
% 2.65/0.71  fof(f642,plain,(
% 2.65/0.71    ~spl6_1),
% 2.65/0.71    inference(avatar_split_clause,[],[f641,f633])).
% 2.65/0.71  fof(f641,plain,(
% 2.65/0.71    ~r2_hidden(sK3,sK4)),
% 2.65/0.71    inference(subsumption_resolution,[],[f622,f40])).
% 2.65/0.71  fof(f40,plain,(
% 2.65/0.71    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 2.65/0.71    inference(cnf_transformation,[],[f5])).
% 2.65/0.71  fof(f5,axiom,(
% 2.65/0.71    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 2.65/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.65/0.71  fof(f622,plain,(
% 2.65/0.71    k1_xboole_0 != k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)) | ~r2_hidden(sK3,sK4)),
% 2.65/0.71    inference(superposition,[],[f81,f74])).
% 2.65/0.71  fof(f81,plain,(
% 2.65/0.71    k1_xboole_0 != k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(sK4,k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),
% 2.65/0.71    inference(forward_demodulation,[],[f73,f42])).
% 2.65/0.71  fof(f73,plain,(
% 2.65/0.71    k1_xboole_0 != k5_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK4))),
% 2.65/0.71    inference(definition_unfolding,[],[f38,f44,f71])).
% 2.65/0.71  fof(f38,plain,(
% 2.65/0.71    k1_xboole_0 != k4_xboole_0(k1_tarski(sK3),sK4)),
% 2.65/0.71    inference(cnf_transformation,[],[f26])).
% 2.65/0.71  % SZS output end Proof for theBenchmark
% 2.65/0.71  % (23563)------------------------------
% 2.65/0.71  % (23563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.65/0.71  % (23563)Termination reason: Refutation
% 2.65/0.71  
% 2.65/0.71  % (23563)Memory used [KB]: 7547
% 2.65/0.71  % (23563)Time elapsed: 0.308 s
% 2.65/0.71  % (23563)------------------------------
% 2.65/0.71  % (23563)------------------------------
% 2.65/0.72  % (23535)Success in time 0.348 s
%------------------------------------------------------------------------------
