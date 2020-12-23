%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 321 expanded)
%              Number of leaves         :   32 ( 126 expanded)
%              Depth                    :   12
%              Number of atoms          :  355 ( 651 expanded)
%              Number of equality atoms :   86 ( 229 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f306,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f134,f143,f153,f158,f159,f166,f178,f189,f192,f193,f210,f221,f227,f271,f289,f301,f304,f305])).

% (21156)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f305,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f304,plain,
    ( ~ spl5_2
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | ~ spl5_2
    | spl5_13 ),
    inference(unit_resulting_resolution,[],[f133,f245,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f245,plain,
    ( ~ v1_ordinal1(sK0)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl5_13
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f133,plain,
    ( v3_ordinal1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl5_2
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f301,plain,
    ( spl5_5
    | ~ spl5_13
    | ~ spl5_1
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f294,f170,f126,f244,f150])).

fof(f150,plain,
    ( spl5_5
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f126,plain,
    ( spl5_1
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f170,plain,
    ( spl5_8
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f294,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v1_ordinal1(sK0)
    | r2_hidden(sK0,sK1)
    | ~ spl5_8 ),
    inference(resolution,[],[f171,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

fof(f171,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f170])).

fof(f289,plain,(
    spl5_17 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | spl5_17 ),
    inference(unit_resulting_resolution,[],[f109,f270])).

fof(f270,plain,
    ( ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl5_17
  <=> r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f109,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1,X9] : r2_hidden(X9,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X9)) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1,X9] :
      ( r2_hidden(X9,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X9) != X8 ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( X7 != X9
      | r2_hidden(X9,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

fof(f271,plain,
    ( ~ spl5_17
    | spl5_6
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f265,f207,f155,f268])).

fof(f155,plain,
    ( spl5_6
  <=> r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f207,plain,
    ( spl5_11
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f265,plain,
    ( ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl5_6
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f157,f209])).

fof(f209,plain,
    ( sK0 = sK1
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f207])).

fof(f157,plain,
    ( ~ r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f155])).

fof(f227,plain,
    ( spl5_8
    | spl5_11
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f224,f163,f207,f170])).

fof(f163,plain,
    ( spl5_7
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f224,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK0,sK1)
    | ~ spl5_7 ),
    inference(resolution,[],[f164,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f164,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f163])).

fof(f221,plain,
    ( ~ spl5_2
    | spl5_7
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f211,f140,f126,f163,f131])).

fof(f140,plain,
    ( spl5_4
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f211,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f141,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f141,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f140])).

fof(f210,plain,
    ( spl5_11
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f195,f155,f207])).

fof(f195,plain,
    ( sK0 = sK1
    | ~ spl5_6 ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,
    ( sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1
    | ~ spl5_6 ),
    inference(resolution,[],[f156,f124])).

fof(f124,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( ~ r2_hidden(X9,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))
      | X1 = X9
      | X2 = X9
      | X3 = X9
      | X4 = X9
      | X5 = X9
      | X6 = X9
      | X7 = X9
      | X0 = X9 ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( X0 = X9
      | X1 = X9
      | X2 = X9
      | X3 = X9
      | X4 = X9
      | X5 = X9
      | X6 = X9
      | X7 = X9
      | ~ r2_hidden(X9,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f156,plain,
    ( r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f155])).

fof(f193,plain,
    ( spl5_5
    | spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f179,f136,f155,f150])).

fof(f136,plain,
    ( spl5_3
  <=> r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f179,plain,
    ( r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | r2_hidden(sK0,sK1)
    | ~ spl5_3 ),
    inference(resolution,[],[f137,f107])).

fof(f107,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f62,f92])).

fof(f92,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f91])).

fof(f91,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f65,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f66,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f137,plain,
    ( r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f136])).

fof(f192,plain,
    ( ~ spl5_1
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl5_1
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f128,f188,f43])).

fof(f188,plain,
    ( ~ v1_ordinal1(sK1)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl5_10
  <=> v1_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f128,plain,
    ( v3_ordinal1(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f126])).

fof(f189,plain,
    ( ~ spl5_10
    | ~ spl5_5
    | spl5_7 ),
    inference(avatar_split_clause,[],[f168,f163,f150,f186])).

fof(f168,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ v1_ordinal1(sK1)
    | spl5_7 ),
    inference(resolution,[],[f165,f46])).

% (21157)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f165,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f163])).

fof(f178,plain,
    ( spl5_9
    | ~ spl5_2
    | ~ spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f161,f140,f126,f131,f175])).

fof(f175,plain,
    ( spl5_9
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f161,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | r2_hidden(sK1,sK0)
    | spl5_4 ),
    inference(resolution,[],[f142,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f142,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f140])).

fof(f166,plain,
    ( ~ spl5_2
    | ~ spl5_7
    | ~ spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f160,f140,f126,f163,f131])).

fof(f160,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | spl5_4 ),
    inference(resolution,[],[f142,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f159,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f96,f140,f136])).

fof(f96,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f35,f94])).

fof(f94,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f41,f92,f93])).

fof(f93,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f91])).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f35,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f158,plain,
    ( ~ spl5_6
    | spl5_3 ),
    inference(avatar_split_clause,[],[f145,f136,f155])).

fof(f145,plain,
    ( ~ r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | spl5_3 ),
    inference(resolution,[],[f138,f105])).

fof(f105,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f64,f92])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f138,plain,
    ( ~ r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f136])).

fof(f153,plain,
    ( ~ spl5_5
    | spl5_3 ),
    inference(avatar_split_clause,[],[f144,f136,f150])).

fof(f144,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl5_3 ),
    inference(resolution,[],[f138,f106])).

fof(f106,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f63,f92])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f143,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f95,f140,f136])).

fof(f95,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f36,f94])).

fof(f36,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f134,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f38,f131])).

fof(f38,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f129,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f37,f126])).

fof(f37,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n013.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:36:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.49  % (21178)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.49  % (21179)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.49  % (21170)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.49  % (21163)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (21162)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (21160)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (21161)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (21171)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (21178)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f306,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f129,f134,f143,f153,f158,f159,f166,f178,f189,f192,f193,f210,f221,f227,f271,f289,f301,f304,f305])).
% 0.20/0.51  % (21156)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  fof(f305,plain,(
% 0.20/0.51    sK0 != sK1 | r2_hidden(sK0,sK1) | ~r2_hidden(sK1,sK0)),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f304,plain,(
% 0.20/0.51    ~spl5_2 | spl5_13),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f302])).
% 0.20/0.51  fof(f302,plain,(
% 0.20/0.51    $false | (~spl5_2 | spl5_13)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f133,f245,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.20/0.51  fof(f245,plain,(
% 0.20/0.51    ~v1_ordinal1(sK0) | spl5_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f244])).
% 0.20/0.51  fof(f244,plain,(
% 0.20/0.51    spl5_13 <=> v1_ordinal1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    v3_ordinal1(sK0) | ~spl5_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f131])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    spl5_2 <=> v3_ordinal1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.51  fof(f301,plain,(
% 0.20/0.51    spl5_5 | ~spl5_13 | ~spl5_1 | ~spl5_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f294,f170,f126,f244,f150])).
% 0.20/0.51  fof(f150,plain,(
% 0.20/0.51    spl5_5 <=> r2_hidden(sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    spl5_1 <=> v3_ordinal1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.51  fof(f170,plain,(
% 0.20/0.51    spl5_8 <=> r2_xboole_0(sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.51  fof(f294,plain,(
% 0.20/0.51    ~v3_ordinal1(sK1) | ~v1_ordinal1(sK0) | r2_hidden(sK0,sK1) | ~spl5_8),
% 0.20/0.51    inference(resolution,[],[f171,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0) | r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.20/0.51    inference(flattening,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,axiom,(
% 0.20/0.51    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).
% 0.20/0.51  fof(f171,plain,(
% 0.20/0.51    r2_xboole_0(sK0,sK1) | ~spl5_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f170])).
% 0.20/0.51  fof(f289,plain,(
% 0.20/0.51    spl5_17),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f272])).
% 0.20/0.51  fof(f272,plain,(
% 0.20/0.51    $false | spl5_17),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f109,f270])).
% 0.20/0.51  fof(f270,plain,(
% 0.20/0.51    ~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | spl5_17),
% 0.20/0.51    inference(avatar_component_clause,[],[f268])).
% 0.20/0.51  fof(f268,plain,(
% 0.20/0.51    spl5_17 <=> r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1,X9] : (r2_hidden(X9,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X9))) )),
% 0.20/0.51    inference(equality_resolution,[],[f108])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X8,X5,X3,X1,X9] : (r2_hidden(X9,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X9) != X8) )),
% 0.20/0.51    inference(equality_resolution,[],[f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (X7 != X9 | r2_hidden(X9,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 0.20/0.51    inference(cnf_transformation,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).
% 0.20/0.51  fof(f271,plain,(
% 0.20/0.51    ~spl5_17 | spl5_6 | ~spl5_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f265,f207,f155,f268])).
% 0.20/0.51  fof(f155,plain,(
% 0.20/0.51    spl5_6 <=> r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.51  fof(f207,plain,(
% 0.20/0.51    spl5_11 <=> sK0 = sK1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.51  fof(f265,plain,(
% 0.20/0.51    ~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | (spl5_6 | ~spl5_11)),
% 0.20/0.51    inference(forward_demodulation,[],[f157,f209])).
% 0.20/0.51  fof(f209,plain,(
% 0.20/0.51    sK0 = sK1 | ~spl5_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f207])).
% 0.20/0.51  fof(f157,plain,(
% 0.20/0.51    ~r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | spl5_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f155])).
% 0.20/0.51  fof(f227,plain,(
% 0.20/0.51    spl5_8 | spl5_11 | ~spl5_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f224,f163,f207,f170])).
% 0.20/0.51  fof(f163,plain,(
% 0.20/0.51    spl5_7 <=> r1_tarski(sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.51  fof(f224,plain,(
% 0.20/0.51    sK0 = sK1 | r2_xboole_0(sK0,sK1) | ~spl5_7),
% 0.20/0.51    inference(resolution,[],[f164,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.51  fof(f164,plain,(
% 0.20/0.51    r1_tarski(sK0,sK1) | ~spl5_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f163])).
% 0.20/0.51  fof(f221,plain,(
% 0.20/0.51    ~spl5_2 | spl5_7 | ~spl5_1 | ~spl5_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f211,f140,f126,f163,f131])).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    spl5_4 <=> r1_ordinal1(sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.51  fof(f211,plain,(
% 0.20/0.51    ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | ~spl5_4),
% 0.20/0.51    inference(resolution,[],[f141,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.51    inference(flattening,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,axiom,(
% 0.20/0.51    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    r1_ordinal1(sK0,sK1) | ~spl5_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f140])).
% 0.20/0.51  fof(f210,plain,(
% 0.20/0.51    spl5_11 | ~spl5_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f195,f155,f207])).
% 0.20/0.51  fof(f195,plain,(
% 0.20/0.51    sK0 = sK1 | ~spl5_6),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f194])).
% 0.20/0.51  fof(f194,plain,(
% 0.20/0.51    sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | ~spl5_6),
% 0.20/0.51    inference(resolution,[],[f156,f124])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] : (~r2_hidden(X9,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) | X1 = X9 | X2 = X9 | X3 = X9 | X4 = X9 | X5 = X9 | X6 = X9 | X7 = X9 | X0 = X9) )),
% 0.20/0.51    inference(equality_resolution,[],[f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (X0 = X9 | X1 = X9 | X2 = X9 | X3 = X9 | X4 = X9 | X5 = X9 | X6 = X9 | X7 = X9 | ~r2_hidden(X9,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 0.20/0.51    inference(cnf_transformation,[],[f34])).
% 0.20/0.51  fof(f156,plain,(
% 0.20/0.51    r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl5_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f155])).
% 0.20/0.51  fof(f193,plain,(
% 0.20/0.51    spl5_5 | spl5_6 | ~spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f179,f136,f155,f150])).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    spl5_3 <=> r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.51  fof(f179,plain,(
% 0.20/0.51    r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | r2_hidden(sK0,sK1) | ~spl5_3),
% 0.20/0.51    inference(resolution,[],[f137,f107])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f100])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 0.20/0.51    inference(definition_unfolding,[],[f62,f92])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f49,f91])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f50,f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f58,f89])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f65,f88])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f66,f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f67,f68])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | ~spl5_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f136])).
% 0.20/0.51  fof(f192,plain,(
% 0.20/0.51    ~spl5_1 | spl5_10),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f190])).
% 0.20/0.51  fof(f190,plain,(
% 0.20/0.51    $false | (~spl5_1 | spl5_10)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f128,f188,f43])).
% 0.20/0.51  fof(f188,plain,(
% 0.20/0.51    ~v1_ordinal1(sK1) | spl5_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f186])).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    spl5_10 <=> v1_ordinal1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    v3_ordinal1(sK1) | ~spl5_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f126])).
% 0.20/0.51  fof(f189,plain,(
% 0.20/0.51    ~spl5_10 | ~spl5_5 | spl5_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f168,f163,f150,f186])).
% 0.20/0.51  fof(f168,plain,(
% 0.20/0.51    ~r2_hidden(sK0,sK1) | ~v1_ordinal1(sK1) | spl5_7),
% 0.20/0.51    inference(resolution,[],[f165,f46])).
% 0.20/0.51  % (21157)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0) | ~v1_ordinal1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,axiom,(
% 0.20/0.51    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.20/0.51  fof(f165,plain,(
% 0.20/0.51    ~r1_tarski(sK0,sK1) | spl5_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f163])).
% 0.20/0.51  fof(f178,plain,(
% 0.20/0.51    spl5_9 | ~spl5_2 | ~spl5_1 | spl5_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f161,f140,f126,f131,f175])).
% 0.20/0.51  fof(f175,plain,(
% 0.20/0.51    spl5_9 <=> r2_hidden(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.51  fof(f161,plain,(
% 0.20/0.51    ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | r2_hidden(sK1,sK0) | spl5_4),
% 0.20/0.51    inference(resolution,[],[f142,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.51    inference(flattening,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,axiom,(
% 0.20/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.20/0.51  fof(f142,plain,(
% 0.20/0.51    ~r1_ordinal1(sK0,sK1) | spl5_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f140])).
% 0.20/0.51  fof(f166,plain,(
% 0.20/0.51    ~spl5_2 | ~spl5_7 | ~spl5_1 | spl5_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f160,f140,f126,f163,f131])).
% 0.20/0.51  fof(f160,plain,(
% 0.20/0.51    ~v3_ordinal1(sK1) | ~r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | spl5_4),
% 0.20/0.51    inference(resolution,[],[f142,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f32])).
% 0.20/0.51  fof(f159,plain,(
% 0.20/0.51    spl5_3 | spl5_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f96,f140,f136])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 0.20/0.51    inference(definition_unfolding,[],[f35,f94])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f41,f92,f93])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f40,f91])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,axiom,(
% 0.20/0.51    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.51    inference(negated_conjecture,[],[f21])).
% 0.20/0.51  fof(f21,conjecture,(
% 0.20/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.20/0.51  fof(f158,plain,(
% 0.20/0.51    ~spl5_6 | spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f145,f136,f155])).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    ~r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | spl5_3),
% 0.20/0.51    inference(resolution,[],[f138,f105])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X3,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f98])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 0.20/0.51    inference(definition_unfolding,[],[f64,f92])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    ~r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | spl5_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f136])).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    ~spl5_5 | spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f144,f136,f150])).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    ~r2_hidden(sK0,sK1) | spl5_3),
% 0.20/0.51    inference(resolution,[],[f138,f106])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X3,X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f99])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 0.20/0.51    inference(definition_unfolding,[],[f63,f92])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f143,plain,(
% 0.20/0.51    ~spl5_3 | ~spl5_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f95,f140,f136])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 0.20/0.51    inference(definition_unfolding,[],[f36,f94])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    spl5_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f38,f131])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    v3_ordinal1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    spl5_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f37,f126])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    v3_ordinal1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (21178)------------------------------
% 0.20/0.51  % (21178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (21178)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (21178)Memory used [KB]: 10874
% 0.20/0.51  % (21178)Time elapsed: 0.070 s
% 0.20/0.51  % (21178)------------------------------
% 0.20/0.51  % (21178)------------------------------
% 0.20/0.52  % (21168)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (21155)Success in time 0.168 s
%------------------------------------------------------------------------------
