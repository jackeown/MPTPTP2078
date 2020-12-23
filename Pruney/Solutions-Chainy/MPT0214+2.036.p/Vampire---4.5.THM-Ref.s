%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 271 expanded)
%              Number of leaves         :   22 (  96 expanded)
%              Depth                    :   15
%              Number of atoms          :  189 ( 415 expanded)
%              Number of equality atoms :   82 ( 266 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f174,f177,f181,f183,f185,f188,f193,f200])).

fof(f200,plain,
    ( ~ spl4_8
    | spl4_4
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f198,f141,f92,f131])).

fof(f131,plain,
    ( spl4_8
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f92,plain,
    ( spl4_4
  <=> ! [X3] : ~ r2_hidden(X3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f141,plain,
    ( spl4_10
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) )
    | ~ spl4_10 ),
    inference(superposition,[],[f24,f143])).

fof(f143,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f141])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f193,plain,
    ( ~ spl4_4
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(resolution,[],[f149,f93])).

fof(f93,plain,
    ( ! [X3] : ~ r2_hidden(X3,k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f149,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl4_11
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f188,plain,
    ( spl4_6
    | spl4_7
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f186,f78,f114,f110])).

fof(f110,plain,
    ( spl4_6
  <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f114,plain,
    ( spl4_7
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f78,plain,
    ( spl4_2
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f186,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f80,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f29,f50,f50])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f23,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f32,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f33,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f42,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f80,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f185,plain,
    ( spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f120,f110,f131])).

fof(f120,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_6 ),
    inference(superposition,[],[f87,f112])).

fof(f112,plain,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f87,plain,(
    ! [X1] : r1_xboole_0(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(trivial_inequality_removal,[],[f85])).

fof(f85,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(superposition,[],[f27,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(resolution,[],[f64,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f64,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f30,f50])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f183,plain,
    ( spl4_10
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f122,f110,f141])).

fof(f122,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_6 ),
    inference(superposition,[],[f83,f112])).

fof(f181,plain,
    ( spl4_11
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f125,f110,f147])).

fof(f125,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl4_6 ),
    inference(superposition,[],[f70,f112])).

fof(f70,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X1,X2)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k6_enumset1(X4,X4,X4,X4,X4,X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f39,f48])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f177,plain,
    ( spl4_1
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f176,f169,f73])).

fof(f73,plain,
    ( spl4_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f169,plain,
    ( spl4_12
  <=> r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f176,plain,
    ( sK0 = sK1
    | ~ spl4_12 ),
    inference(duplicate_literal_removal,[],[f175])).

fof(f175,plain,
    ( sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1
    | ~ spl4_12 ),
    inference(resolution,[],[f171,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f38,f48])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f171,plain,
    ( r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f169])).

fof(f174,plain,
    ( spl4_12
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f166,f114,f169])).

fof(f166,plain,
    ( r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl4_7 ),
    inference(superposition,[],[f66,f116])).

fof(f116,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f66,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f41,f48])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f51,f78])).

fof(f51,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f20,f50,f50])).

fof(f20,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f76,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f21,f73])).

fof(f21,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:07:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (27317)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.48  % (27317)Refutation not found, incomplete strategy% (27317)------------------------------
% 0.21/0.48  % (27317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (27317)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (27317)Memory used [KB]: 1663
% 0.21/0.49  % (27317)Time elapsed: 0.083 s
% 0.21/0.49  % (27317)------------------------------
% 0.21/0.49  % (27317)------------------------------
% 0.21/0.49  % (27336)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.50  % (27344)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.50  % (27325)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (27336)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f201,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f76,f81,f174,f177,f181,f183,f185,f188,f193,f200])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    ~spl4_8 | spl4_4 | ~spl4_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f198,f141,f92,f131])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    spl4_8 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    spl4_4 <=> ! [X3] : ~r2_hidden(X3,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    spl4_10 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,k1_xboole_0)) ) | ~spl4_10),
% 0.21/0.50    inference(superposition,[],[f24,f143])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f141])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    ~spl4_4 | ~spl4_11),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f192])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    $false | (~spl4_4 | ~spl4_11)),
% 0.21/0.51    inference(resolution,[],[f149,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0)) ) | ~spl4_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f92])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    r2_hidden(sK0,k1_xboole_0) | ~spl4_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f147])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    spl4_11 <=> r2_hidden(sK0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    spl4_6 | spl4_7 | ~spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f186,f78,f114,f110])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    spl4_6 <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    spl4_7 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    spl4_2 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl4_2),
% 0.21/0.51    inference(resolution,[],[f80,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(definition_unfolding,[],[f29,f50,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f22,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f23,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f32,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f33,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f42,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f43,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl4_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f78])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    spl4_8 | ~spl4_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f120,f110,f131])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_6),
% 0.21/0.51    inference(superposition,[],[f87,f112])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl4_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f110])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X1] : (r1_xboole_0(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 0.21/0.51    inference(superposition,[],[f27,f83])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 0.21/0.51    inference(resolution,[],[f64,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f30,f50])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    spl4_10 | ~spl4_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f122,f110,f141])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_6),
% 0.21/0.51    inference(superposition,[],[f83,f112])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    spl4_11 | ~spl4_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f125,f110,f147])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    r2_hidden(sK0,k1_xboole_0) | ~spl4_6),
% 0.21/0.51    inference(superposition,[],[f70,f112])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X4,X2,X1] : (r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X1,X2))) )),
% 0.21/0.51    inference(equality_resolution,[],[f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k6_enumset1(X4,X4,X4,X4,X4,X4,X1,X2) != X3) )),
% 0.21/0.51    inference(equality_resolution,[],[f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.21/0.51    inference(definition_unfolding,[],[f39,f48])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    spl4_1 | ~spl4_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f176,f169,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    spl4_1 <=> sK0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    spl4_12 <=> r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    sK0 = sK1 | ~spl4_12),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f175])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | ~spl4_12),
% 0.21/0.51    inference(resolution,[],[f171,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.21/0.51    inference(equality_resolution,[],[f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.21/0.51    inference(definition_unfolding,[],[f38,f48])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl4_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f169])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    spl4_12 | ~spl4_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f166,f114,f169])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl4_7),
% 0.21/0.51    inference(superposition,[],[f66,f116])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl4_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f114])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X4,X0,X1] : (r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X4))) )),
% 0.21/0.51    inference(equality_resolution,[],[f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X4) != X3) )),
% 0.21/0.51    inference(equality_resolution,[],[f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.21/0.51    inference(definition_unfolding,[],[f41,f48])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f51,f78])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.21/0.51    inference(definition_unfolding,[],[f20,f50,f50])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.51    inference(negated_conjecture,[],[f13])).
% 0.21/0.51  fof(f13,conjecture,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ~spl4_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f21,f73])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    sK0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (27336)------------------------------
% 0.21/0.51  % (27336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (27336)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (27336)Memory used [KB]: 10746
% 0.21/0.51  % (27336)Time elapsed: 0.111 s
% 0.21/0.51  % (27336)------------------------------
% 0.21/0.51  % (27336)------------------------------
% 0.21/0.51  % (27312)Success in time 0.149 s
%------------------------------------------------------------------------------
