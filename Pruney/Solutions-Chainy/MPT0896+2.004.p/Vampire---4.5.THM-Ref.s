%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 219 expanded)
%              Number of leaves         :   24 (  89 expanded)
%              Depth                    :    8
%              Number of atoms          :  349 ( 829 expanded)
%              Number of equality atoms :  239 ( 676 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f473,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f94,f99,f148,f155,f189,f194,f279,f344,f358,f401,f432,f445,f471])).

fof(f471,plain,
    ( spl8_6
    | spl8_13
    | ~ spl8_25 ),
    inference(avatar_contradiction_clause,[],[f446])).

fof(f446,plain,
    ( $false
    | spl8_6
    | spl8_13
    | ~ spl8_25 ),
    inference(unit_resulting_resolution,[],[f85,f146,f444,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X1 = X4 ) ),
    inference(definition_unfolding,[],[f40,f30,f30,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

fof(f444,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK5),sK2)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f442])).

fof(f442,plain,
    ( spl8_25
  <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f146,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | spl8_13 ),
    inference(avatar_component_clause,[],[f145])).

% (29468)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f145,plain,
    ( spl8_13
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f85,plain,
    ( sK1 != sK5
    | spl8_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl8_6
  <=> sK1 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f445,plain,
    ( spl8_25
    | ~ spl8_5
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f434,f398,f79,f442])).

fof(f79,plain,
    ( spl8_5
  <=> sK0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f398,plain,
    ( spl8_22
  <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f434,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK5),sK2)
    | ~ spl8_5
    | ~ spl8_22 ),
    inference(backward_demodulation,[],[f400,f80])).

fof(f80,plain,
    ( sK0 = sK4
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f400,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK2)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f398])).

fof(f432,plain,
    ( spl8_5
    | spl8_13
    | ~ spl8_22 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | spl8_5
    | spl8_13
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f81,f146,f400,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X0 = X3 ) ),
    inference(definition_unfolding,[],[f39,f30,f30,f30])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f81,plain,
    ( sK0 != sK4
    | spl8_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f401,plain,
    ( spl8_22
    | spl8_13
    | spl8_4
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f396,f355,f74,f145,f398])).

fof(f74,plain,
    ( spl8_4
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f355,plain,
    ( spl8_21
  <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f396,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK2)
    | ~ spl8_21 ),
    inference(equality_resolution,[],[f370])).

fof(f370,plain,
    ( ! [X21,X22] :
        ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(X21,X22)
        | k1_xboole_0 = X22
        | k1_xboole_0 = X21
        | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK2) = X21 )
    | ~ spl8_21 ),
    inference(superposition,[],[f32,f357])).

fof(f357,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK2),sK3)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f355])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f11])).

% (29460)Refutation not found, incomplete strategy% (29460)------------------------------
% (29460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29460)Termination reason: Refutation not found, incomplete strategy

% (29460)Memory used [KB]: 10746
% (29460)Time elapsed: 0.118 s
% (29460)------------------------------
% (29460)------------------------------
fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f358,plain,
    ( spl8_21
    | ~ spl8_7
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f346,f152,f87,f355])).

fof(f87,plain,
    ( spl8_7
  <=> sK2 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f152,plain,
    ( spl8_14
  <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f346,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK2),sK3)
    | ~ spl8_7
    | ~ spl8_14 ),
    inference(backward_demodulation,[],[f154,f88])).

fof(f88,plain,
    ( sK2 = sK6
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f154,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f152])).

fof(f344,plain,
    ( spl8_7
    | spl8_12
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f343,f96,f132,f87])).

fof(f132,plain,
    ( spl8_12
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f96,plain,
    ( spl8_9
  <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f343,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | sK2 = sK6
    | ~ spl8_9 ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,
    ( ! [X12,X10,X11] :
        ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X10,X11),X12)
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X10,X11),X12)
        | sK6 = X11 )
    | ~ spl8_9 ),
    inference(superposition,[],[f50,f98])).

fof(f98,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f279,plain,
    ( spl8_1
    | spl8_2
    | spl8_3
    | spl8_4
    | ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | spl8_1
    | spl8_2
    | spl8_3
    | spl8_4
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f61,f66,f71,f76,f133,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f34,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f133,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f132])).

fof(f76,plain,
    ( k1_xboole_0 != sK3
    | spl8_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f71,plain,
    ( k1_xboole_0 != sK2
    | spl8_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl8_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f66,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f61,plain,
    ( k1_xboole_0 != sK0
    | spl8_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

% (29470)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f194,plain,(
    spl8_15 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl8_15 ),
    inference(unit_resulting_resolution,[],[f53,f188])).

fof(f188,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | spl8_15 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl8_15
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f53,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f17])).

% (29467)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f17,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f189,plain,
    ( ~ spl8_15
    | spl8_12
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f156,f145,f132,f186])).

fof(f156,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | spl8_12
    | ~ spl8_13 ),
    inference(backward_demodulation,[],[f134,f147])).

fof(f147,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f145])).

fof(f134,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | spl8_12 ),
    inference(avatar_component_clause,[],[f132])).

fof(f155,plain,
    ( spl8_14
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f150,f96,f91,f152])).

fof(f91,plain,
    ( spl8_8
  <=> sK3 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f150,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3)
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(backward_demodulation,[],[f98,f92])).

fof(f92,plain,
    ( sK3 = sK7
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f148,plain,
    ( spl8_8
    | spl8_13
    | spl8_4
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f143,f96,f74,f145,f91])).

fof(f143,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | sK3 = sK7
    | ~ spl8_9 ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,
    ( ! [X26,X25] :
        ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(X25,X26)
        | k1_xboole_0 = X26
        | k1_xboole_0 = X25
        | sK7 = X26 )
    | ~ spl8_9 ),
    inference(superposition,[],[f33,f98])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f99,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f43,f96])).

fof(f43,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f21,f42,f42])).

fof(f21,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f10,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_mcart_1)).

fof(f94,plain,
    ( ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f26,f91,f87,f83,f79])).

fof(f26,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f16])).

fof(f77,plain,(
    ~ spl8_4 ),
    inference(avatar_split_clause,[],[f25,f74])).

fof(f25,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f24,f69])).

fof(f24,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f67,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f23,f64])).

fof(f23,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f22,f59])).

fof(f22,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (29458)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (29474)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (29474)Refutation not found, incomplete strategy% (29474)------------------------------
% 0.21/0.51  % (29474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29474)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29474)Memory used [KB]: 6268
% 0.21/0.51  % (29474)Time elapsed: 0.097 s
% 0.21/0.51  % (29474)------------------------------
% 0.21/0.51  % (29474)------------------------------
% 0.21/0.51  % (29466)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.51  % (29466)Refutation not found, incomplete strategy% (29466)------------------------------
% 0.21/0.51  % (29466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29466)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29466)Memory used [KB]: 1663
% 0.21/0.51  % (29466)Time elapsed: 0.093 s
% 0.21/0.51  % (29466)------------------------------
% 0.21/0.51  % (29466)------------------------------
% 0.21/0.51  % (29452)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (29459)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (29451)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (29457)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (29460)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (29454)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (29449)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (29448)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (29475)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (29462)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (29462)Refutation not found, incomplete strategy% (29462)------------------------------
% 0.21/0.53  % (29462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29462)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29462)Memory used [KB]: 1663
% 0.21/0.53  % (29462)Time elapsed: 0.085 s
% 0.21/0.53  % (29462)------------------------------
% 0.21/0.53  % (29462)------------------------------
% 0.21/0.53  % (29458)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f473,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f94,f99,f148,f155,f189,f194,f279,f344,f358,f401,f432,f445,f471])).
% 0.21/0.53  fof(f471,plain,(
% 0.21/0.53    spl8_6 | spl8_13 | ~spl8_25),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f446])).
% 0.21/0.53  fof(f446,plain,(
% 0.21/0.53    $false | (spl8_6 | spl8_13 | ~spl8_25)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f85,f146,f444,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | X1 = X4) )),
% 0.21/0.53    inference(definition_unfolding,[],[f40,f30,f30,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).
% 0.21/0.53  fof(f444,plain,(
% 0.21/0.53    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK5),sK2) | ~spl8_25),
% 0.21/0.53    inference(avatar_component_clause,[],[f442])).
% 0.21/0.53  fof(f442,plain,(
% 0.21/0.53    spl8_25 <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK5),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | spl8_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f145])).
% 0.21/0.53  % (29468)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    spl8_13 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    sK1 != sK5 | spl8_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    spl8_6 <=> sK1 = sK5),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.53  fof(f445,plain,(
% 0.21/0.53    spl8_25 | ~spl8_5 | ~spl8_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f434,f398,f79,f442])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    spl8_5 <=> sK0 = sK4),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.53  fof(f398,plain,(
% 0.21/0.53    spl8_22 <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.21/0.53  fof(f434,plain,(
% 0.21/0.53    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK5),sK2) | (~spl8_5 | ~spl8_22)),
% 0.21/0.53    inference(backward_demodulation,[],[f400,f80])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    sK0 = sK4 | ~spl8_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f79])).
% 0.21/0.53  fof(f400,plain,(
% 0.21/0.53    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK2) | ~spl8_22),
% 0.21/0.53    inference(avatar_component_clause,[],[f398])).
% 0.21/0.53  fof(f432,plain,(
% 0.21/0.53    spl8_5 | spl8_13 | ~spl8_22),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f407])).
% 0.21/0.53  fof(f407,plain,(
% 0.21/0.53    $false | (spl8_5 | spl8_13 | ~spl8_22)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f81,f146,f400,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | X0 = X3) )),
% 0.21/0.53    inference(definition_unfolding,[],[f39,f30,f30,f30])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    sK0 != sK4 | spl8_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f79])).
% 0.21/0.53  fof(f401,plain,(
% 0.21/0.53    spl8_22 | spl8_13 | spl8_4 | ~spl8_21),
% 0.21/0.53    inference(avatar_split_clause,[],[f396,f355,f74,f145,f398])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    spl8_4 <=> k1_xboole_0 = sK3),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.53  fof(f355,plain,(
% 0.21/0.53    spl8_21 <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK2),sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.21/0.53  fof(f396,plain,(
% 0.21/0.53    k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK2) | ~spl8_21),
% 0.21/0.53    inference(equality_resolution,[],[f370])).
% 0.21/0.53  fof(f370,plain,(
% 0.21/0.53    ( ! [X21,X22] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(X21,X22) | k1_xboole_0 = X22 | k1_xboole_0 = X21 | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK2) = X21) ) | ~spl8_21),
% 0.21/0.53    inference(superposition,[],[f32,f357])).
% 0.21/0.53  fof(f357,plain,(
% 0.21/0.53    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK2),sK3) | ~spl8_21),
% 0.21/0.53    inference(avatar_component_clause,[],[f355])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X0 = X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 0.21/0.53    inference(flattening,[],[f11])).
% 0.21/0.53  % (29460)Refutation not found, incomplete strategy% (29460)------------------------------
% 0.21/0.53  % (29460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29460)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29460)Memory used [KB]: 10746
% 0.21/0.53  % (29460)Time elapsed: 0.118 s
% 0.21/0.53  % (29460)------------------------------
% 0.21/0.53  % (29460)------------------------------
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 0.21/0.53  fof(f358,plain,(
% 0.21/0.53    spl8_21 | ~spl8_7 | ~spl8_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f346,f152,f87,f355])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    spl8_7 <=> sK2 = sK6),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    spl8_14 <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.53  fof(f346,plain,(
% 0.21/0.53    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK2),sK3) | (~spl8_7 | ~spl8_14)),
% 0.21/0.53    inference(backward_demodulation,[],[f154,f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    sK2 = sK6 | ~spl8_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f87])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3) | ~spl8_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f152])).
% 0.21/0.53  fof(f344,plain,(
% 0.21/0.53    spl8_7 | spl8_12 | ~spl8_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f343,f96,f132,f87])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    spl8_12 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    spl8_9 <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.53  fof(f343,plain,(
% 0.21/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | sK2 = sK6 | ~spl8_9),
% 0.21/0.53    inference(equality_resolution,[],[f104])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ( ! [X12,X10,X11] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X10,X11),X12) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X10,X11),X12) | sK6 = X11) ) | ~spl8_9),
% 0.21/0.53    inference(superposition,[],[f50,f98])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) | ~spl8_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f96])).
% 0.21/0.53  fof(f279,plain,(
% 0.21/0.53    spl8_1 | spl8_2 | spl8_3 | spl8_4 | ~spl8_12),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f252])).
% 0.21/0.53  fof(f252,plain,(
% 0.21/0.53    $false | (spl8_1 | spl8_2 | spl8_3 | spl8_4 | ~spl8_12)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f61,f66,f71,f76,f133,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f34,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f31,f30])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.53    inference(flattening,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.53    inference(nnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl8_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f132])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    k1_xboole_0 != sK3 | spl8_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f74])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    k1_xboole_0 != sK2 | spl8_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    spl8_3 <=> k1_xboole_0 = sK2),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    k1_xboole_0 != sK1 | spl8_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    spl8_2 <=> k1_xboole_0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    k1_xboole_0 != sK0 | spl8_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    spl8_1 <=> k1_xboole_0 = sK0),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.53  % (29470)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    spl8_15),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f190])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    $false | spl8_15),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f53,f188])).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | spl8_15),
% 0.21/0.53    inference(avatar_component_clause,[],[f186])).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    spl8_15 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  % (29467)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.53    inference(nnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    ~spl8_15 | spl8_12 | ~spl8_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f156,f145,f132,f186])).
% 0.21/0.53  fof(f156,plain,(
% 0.21/0.53    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | (spl8_12 | ~spl8_13)),
% 0.21/0.53    inference(backward_demodulation,[],[f134,f147])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl8_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f145])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | spl8_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f132])).
% 0.21/0.53  fof(f155,plain,(
% 0.21/0.53    spl8_14 | ~spl8_8 | ~spl8_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f150,f96,f91,f152])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    spl8_8 <=> sK3 = sK7),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3) | (~spl8_8 | ~spl8_9)),
% 0.21/0.53    inference(backward_demodulation,[],[f98,f92])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    sK3 = sK7 | ~spl8_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f91])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    spl8_8 | spl8_13 | spl8_4 | ~spl8_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f143,f96,f74,f145,f91])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | sK3 = sK7 | ~spl8_9),
% 0.21/0.53    inference(equality_resolution,[],[f113])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    ( ! [X26,X25] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(X25,X26) | k1_xboole_0 = X26 | k1_xboole_0 = X25 | sK7 = X26) ) | ~spl8_9),
% 0.21/0.53    inference(superposition,[],[f33,f98])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X1 = X3) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    spl8_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f43,f96])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 0.21/0.53    inference(definition_unfolding,[],[f21,f42,f42])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f10,f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 0.21/0.53    inference(flattening,[],[f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.53    inference(negated_conjecture,[],[f7])).
% 0.21/0.53  fof(f7,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_mcart_1)).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f26,f91,f87,f83,f79])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ~spl8_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f25,f74])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    k1_xboole_0 != sK3),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ~spl8_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f24,f69])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    k1_xboole_0 != sK2),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ~spl8_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f23,f64])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    k1_xboole_0 != sK1),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ~spl8_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f22,f59])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    k1_xboole_0 != sK0),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (29458)------------------------------
% 0.21/0.53  % (29458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29458)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (29471)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (29458)Memory used [KB]: 11001
% 0.21/0.53  % (29458)Time elapsed: 0.112 s
% 0.21/0.53  % (29458)------------------------------
% 0.21/0.53  % (29458)------------------------------
% 0.21/0.53  % (29464)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (29450)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (29447)Success in time 0.175 s
%------------------------------------------------------------------------------
