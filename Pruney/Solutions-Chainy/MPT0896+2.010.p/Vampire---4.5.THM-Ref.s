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
% DateTime   : Thu Dec  3 12:59:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 210 expanded)
%              Number of leaves         :   22 (  81 expanded)
%              Depth                    :    8
%              Number of atoms          :  259 ( 631 expanded)
%              Number of equality atoms :  167 ( 505 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f857,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f98,f103,f155,f157,f197,f353,f377,f572,f573,f721,f779,f856])).

fof(f856,plain,
    ( spl8_8
    | spl8_28
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f847,f350,f719,f95])).

fof(f95,plain,
    ( spl8_8
  <=> sK0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f719,plain,
    ( spl8_28
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f350,plain,
    ( spl8_18
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f847,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)
        | sK0 = sK4 )
    | ~ spl8_18 ),
    inference(equality_resolution,[],[f368])).

fof(f368,plain,
    ( ! [X45,X43,X46,X44] :
        ( k2_zfmisc_1(k2_zfmisc_1(X44,X45),X46) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X43)
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X43)
        | sK4 = X44 )
    | ~ spl8_18 ),
    inference(superposition,[],[f54,f352])).

fof(f352,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f350])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
      | X0 = X3 ) ),
    inference(definition_unfolding,[],[f35,f21,f21,f21])).

% (24923)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f21,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).

fof(f779,plain,
    ( spl8_19
    | ~ spl8_28 ),
    inference(avatar_contradiction_clause,[],[f725])).

fof(f725,plain,
    ( $false
    | spl8_19
    | ~ spl8_28 ),
    inference(unit_resulting_resolution,[],[f376,f720])).

fof(f720,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f719])).

fof(f376,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | spl8_19 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl8_19
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f721,plain,
    ( spl8_7
    | spl8_28
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f709,f350,f719,f91])).

fof(f91,plain,
    ( spl8_7
  <=> sK1 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f709,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)
        | sK1 = sK5 )
    | ~ spl8_18 ),
    inference(equality_resolution,[],[f366])).

fof(f366,plain,
    ( ! [X37,X35,X38,X36] :
        ( k2_zfmisc_1(k2_zfmisc_1(X36,X37),X38) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X35)
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X35)
        | sK5 = X37 )
    | ~ spl8_18 ),
    inference(superposition,[],[f53,f352])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
      | X1 = X4 ) ),
    inference(definition_unfolding,[],[f36,f21,f21,f21])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | X1 = X4 ) ),
    inference(cnf_transformation,[],[f14])).

% (24923)Refutation not found, incomplete strategy% (24923)------------------------------
% (24923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f573,plain,
    ( sK2 != sK6
    | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK2)
    | sK3 != sK7
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

% (24923)Termination reason: Refutation not found, incomplete strategy

% (24923)Memory used [KB]: 1663
% (24923)Time elapsed: 0.153 s
% (24923)------------------------------
% (24923)------------------------------
fof(f572,plain,(
    spl8_26 ),
    inference(avatar_contradiction_clause,[],[f563])).

fof(f563,plain,
    ( $false
    | spl8_26 ),
    inference(unit_resulting_resolution,[],[f553,f553,f61,f553,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f61,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f28,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f26,f21])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f553,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | spl8_26 ),
    inference(avatar_component_clause,[],[f551])).

fof(f551,plain,
    ( spl8_26
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f377,plain,
    ( ~ spl8_19
    | spl8_15
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f355,f350,f244,f374])).

fof(f244,plain,
    ( spl8_15
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f355,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | spl8_15
    | ~ spl8_18 ),
    inference(backward_demodulation,[],[f245,f352])).

fof(f245,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK2)
    | spl8_15 ),
    inference(avatar_component_clause,[],[f244])).

fof(f353,plain,
    ( spl8_18
    | spl8_13
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f345,f100,f150,f350])).

fof(f150,plain,
    ( spl8_13
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f100,plain,
    ( spl8_9
  <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f345,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)
    | ~ spl8_9 ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,
    ( ! [X35,X36,X34] :
        ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X34,X35),X36)
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X34,X35),X36)
        | k2_zfmisc_1(sK4,sK5) = X34 )
    | ~ spl8_9 ),
    inference(superposition,[],[f54,f102])).

fof(f102,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f197,plain,
    ( spl8_1
    | spl8_2
    | spl8_3
    | spl8_4
    | ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl8_1
    | spl8_2
    | spl8_3
    | spl8_4
    | ~ spl8_13 ),
    inference(unit_resulting_resolution,[],[f80,f75,f70,f65,f151,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(definition_unfolding,[],[f27,f38])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f151,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f150])).

fof(f65,plain,
    ( k1_xboole_0 != sK0
    | spl8_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f70,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f75,plain,
    ( k1_xboole_0 != sK2
    | spl8_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl8_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f80,plain,
    ( k1_xboole_0 != sK3
    | spl8_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl8_4
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f157,plain,
    ( spl8_6
    | ~ spl8_9
    | spl8_13 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl8_6
    | ~ spl8_9
    | spl8_13 ),
    inference(unit_resulting_resolution,[],[f152,f102,f89,f53])).

fof(f89,plain,
    ( sK2 != sK6
    | spl8_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl8_6
  <=> sK2 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f152,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | spl8_13 ),
    inference(avatar_component_clause,[],[f150])).

fof(f155,plain,
    ( spl8_5
    | ~ spl8_9
    | spl8_13 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl8_5
    | ~ spl8_9
    | spl8_13 ),
    inference(unit_resulting_resolution,[],[f85,f102,f152,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
      | X2 = X5 ) ),
    inference(definition_unfolding,[],[f37,f21,f21,f21])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | X2 = X5 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f85,plain,
    ( sK3 != sK7
    | spl8_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl8_5
  <=> sK3 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f103,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f39,f100])).

fof(f39,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f16,f38,f38])).

fof(f16,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f10])).

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

% (24925)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).

fof(f98,plain,
    ( ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f15,f95,f91,f87,f83])).

fof(f15,plain,
    ( sK0 != sK4
    | sK1 != sK5
    | sK2 != sK6
    | sK3 != sK7 ),
    inference(cnf_transformation,[],[f10])).

fof(f81,plain,(
    ~ spl8_4 ),
    inference(avatar_split_clause,[],[f20,f78])).

fof(f20,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f10])).

fof(f76,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f19,f73])).

fof(f19,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f10])).

fof(f71,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f18,f68])).

fof(f18,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f66,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f17,f63])).

fof(f17,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:43:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (24934)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.47  % (24934)Refutation not found, incomplete strategy% (24934)------------------------------
% 0.21/0.47  % (24934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (24950)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.47  % (24934)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (24934)Memory used [KB]: 10746
% 0.21/0.47  % (24934)Time elapsed: 0.062 s
% 0.21/0.47  % (24934)------------------------------
% 0.21/0.47  % (24934)------------------------------
% 0.21/0.52  % (24944)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (24945)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (24928)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (24929)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (24924)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.55  % (24950)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (24926)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f857,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f98,f103,f155,f157,f197,f353,f377,f572,f573,f721,f779,f856])).
% 0.21/0.56  fof(f856,plain,(
% 0.21/0.56    spl8_8 | spl8_28 | ~spl8_18),
% 0.21/0.56    inference(avatar_split_clause,[],[f847,f350,f719,f95])).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    spl8_8 <=> sK0 = sK4),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.56  fof(f719,plain,(
% 0.21/0.56    spl8_28 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.21/0.56  fof(f350,plain,(
% 0.21/0.56    spl8_18 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.56  fof(f847,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) | sK0 = sK4) ) | ~spl8_18),
% 0.21/0.56    inference(equality_resolution,[],[f368])).
% 0.21/0.56  fof(f368,plain,(
% 0.21/0.56    ( ! [X45,X43,X46,X44] : (k2_zfmisc_1(k2_zfmisc_1(X44,X45),X46) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X43) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X43) | sK4 = X44) ) | ~spl8_18),
% 0.21/0.56    inference(superposition,[],[f54,f352])).
% 0.21/0.56  fof(f352,plain,(
% 0.21/0.56    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) | ~spl8_18),
% 0.21/0.56    inference(avatar_component_clause,[],[f350])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0 | X0 = X3) )),
% 0.21/0.56    inference(definition_unfolding,[],[f35,f21,f21,f21])).
% 0.21/0.56  % (24923)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 | X0 = X3) )),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.21/0.56    inference(flattening,[],[f13])).
% 0.21/0.56  fof(f13,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.21/0.56    inference(ennf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).
% 0.21/0.56  fof(f779,plain,(
% 0.21/0.56    spl8_19 | ~spl8_28),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f725])).
% 0.21/0.56  fof(f725,plain,(
% 0.21/0.56    $false | (spl8_19 | ~spl8_28)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f376,f720])).
% 0.21/0.56  fof(f720,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)) ) | ~spl8_28),
% 0.21/0.56    inference(avatar_component_clause,[],[f719])).
% 0.21/0.56  fof(f376,plain,(
% 0.21/0.56    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | spl8_19),
% 0.21/0.56    inference(avatar_component_clause,[],[f374])).
% 0.21/0.56  fof(f374,plain,(
% 0.21/0.56    spl8_19 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.56  fof(f721,plain,(
% 0.21/0.56    spl8_7 | spl8_28 | ~spl8_18),
% 0.21/0.56    inference(avatar_split_clause,[],[f709,f350,f719,f91])).
% 0.21/0.56  fof(f91,plain,(
% 0.21/0.56    spl8_7 <=> sK1 = sK5),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.56  fof(f709,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) | sK1 = sK5) ) | ~spl8_18),
% 0.21/0.56    inference(equality_resolution,[],[f366])).
% 0.21/0.56  fof(f366,plain,(
% 0.21/0.56    ( ! [X37,X35,X38,X36] : (k2_zfmisc_1(k2_zfmisc_1(X36,X37),X38) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X35) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X35) | sK5 = X37) ) | ~spl8_18),
% 0.21/0.56    inference(superposition,[],[f53,f352])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0 | X1 = X4) )),
% 0.21/0.56    inference(definition_unfolding,[],[f36,f21,f21,f21])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 | X1 = X4) )),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  % (24923)Refutation not found, incomplete strategy% (24923)------------------------------
% 0.21/0.56  % (24923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  fof(f573,plain,(
% 0.21/0.56    sK2 != sK6 | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK2) | sK3 != sK7 | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 0.21/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.56  % (24923)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (24923)Memory used [KB]: 1663
% 0.21/0.56  % (24923)Time elapsed: 0.153 s
% 0.21/0.56  % (24923)------------------------------
% 0.21/0.56  % (24923)------------------------------
% 0.21/0.56  fof(f572,plain,(
% 0.21/0.56    spl8_26),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f563])).
% 0.21/0.56  fof(f563,plain,(
% 0.21/0.56    $false | spl8_26),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f553,f553,f61,f553,f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 0.21/0.56    inference(definition_unfolding,[],[f22,f21])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    ( ! [X2,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3)) )),
% 0.21/0.56    inference(equality_resolution,[],[f47])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 != X0) )),
% 0.21/0.56    inference(definition_unfolding,[],[f28,f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f26,f21])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).
% 0.21/0.56  fof(f553,plain,(
% 0.21/0.56    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | spl8_26),
% 0.21/0.56    inference(avatar_component_clause,[],[f551])).
% 0.21/0.56  fof(f551,plain,(
% 0.21/0.56    spl8_26 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK3)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.21/0.56  fof(f377,plain,(
% 0.21/0.56    ~spl8_19 | spl8_15 | ~spl8_18),
% 0.21/0.56    inference(avatar_split_clause,[],[f355,f350,f244,f374])).
% 0.21/0.56  fof(f244,plain,(
% 0.21/0.56    spl8_15 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.56  fof(f355,plain,(
% 0.21/0.56    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | (spl8_15 | ~spl8_18)),
% 0.21/0.56    inference(backward_demodulation,[],[f245,f352])).
% 0.21/0.56  fof(f245,plain,(
% 0.21/0.56    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK2) | spl8_15),
% 0.21/0.56    inference(avatar_component_clause,[],[f244])).
% 0.21/0.56  fof(f353,plain,(
% 0.21/0.56    spl8_18 | spl8_13 | ~spl8_9),
% 0.21/0.56    inference(avatar_split_clause,[],[f345,f100,f150,f350])).
% 0.21/0.56  fof(f150,plain,(
% 0.21/0.56    spl8_13 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.56  fof(f100,plain,(
% 0.21/0.56    spl8_9 <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.56  fof(f345,plain,(
% 0.21/0.56    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) | ~spl8_9),
% 0.21/0.56    inference(equality_resolution,[],[f118])).
% 0.21/0.56  fof(f118,plain,(
% 0.21/0.56    ( ! [X35,X36,X34] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X34,X35),X36) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X34,X35),X36) | k2_zfmisc_1(sK4,sK5) = X34) ) | ~spl8_9),
% 0.21/0.56    inference(superposition,[],[f54,f102])).
% 0.21/0.56  fof(f102,plain,(
% 0.21/0.56    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) | ~spl8_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f100])).
% 0.21/0.56  fof(f197,plain,(
% 0.21/0.56    spl8_1 | spl8_2 | spl8_3 | spl8_4 | ~spl8_13),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f161])).
% 0.21/0.56  fof(f161,plain,(
% 0.21/0.56    $false | (spl8_1 | spl8_2 | spl8_3 | spl8_4 | ~spl8_13)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f80,f75,f70,f65,f151,f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 0.21/0.56    inference(definition_unfolding,[],[f27,f38])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 0.21/0.56    inference(cnf_transformation,[],[f6])).
% 0.21/0.56  fof(f151,plain,(
% 0.21/0.56    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl8_13),
% 0.21/0.56    inference(avatar_component_clause,[],[f150])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    k1_xboole_0 != sK0 | spl8_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f63])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    spl8_1 <=> k1_xboole_0 = sK0),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    k1_xboole_0 != sK1 | spl8_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f68])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    spl8_2 <=> k1_xboole_0 = sK1),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    k1_xboole_0 != sK2 | spl8_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f73])).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    spl8_3 <=> k1_xboole_0 = sK2),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.56  fof(f80,plain,(
% 0.21/0.56    k1_xboole_0 != sK3 | spl8_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f78])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    spl8_4 <=> k1_xboole_0 = sK3),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.56  fof(f157,plain,(
% 0.21/0.56    spl8_6 | ~spl8_9 | spl8_13),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f156])).
% 0.21/0.56  fof(f156,plain,(
% 0.21/0.56    $false | (spl8_6 | ~spl8_9 | spl8_13)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f152,f102,f89,f53])).
% 0.21/0.56  fof(f89,plain,(
% 0.21/0.56    sK2 != sK6 | spl8_6),
% 0.21/0.56    inference(avatar_component_clause,[],[f87])).
% 0.21/0.56  fof(f87,plain,(
% 0.21/0.56    spl8_6 <=> sK2 = sK6),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.56  fof(f152,plain,(
% 0.21/0.56    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | spl8_13),
% 0.21/0.56    inference(avatar_component_clause,[],[f150])).
% 0.21/0.56  fof(f155,plain,(
% 0.21/0.56    spl8_5 | ~spl8_9 | spl8_13),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f154])).
% 0.21/0.56  fof(f154,plain,(
% 0.21/0.56    $false | (spl8_5 | ~spl8_9 | spl8_13)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f85,f102,f152,f52])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0 | X2 = X5) )),
% 0.21/0.56    inference(definition_unfolding,[],[f37,f21,f21,f21])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 | X2 = X5) )),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f85,plain,(
% 0.21/0.56    sK3 != sK7 | spl8_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f83])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    spl8_5 <=> sK3 = sK7),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.56  fof(f103,plain,(
% 0.21/0.56    spl8_9),
% 0.21/0.56    inference(avatar_split_clause,[],[f39,f100])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 0.21/0.56    inference(definition_unfolding,[],[f16,f38,f38])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 0.21/0.56    inference(cnf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 0.21/0.56    inference(flattening,[],[f9])).
% 0.21/0.56  % (24925)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.56  fof(f9,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.56    inference(negated_conjecture,[],[f7])).
% 0.21/0.56  fof(f7,conjecture,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).
% 0.21/0.56  fof(f98,plain,(
% 0.21/0.56    ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8),
% 0.21/0.56    inference(avatar_split_clause,[],[f15,f95,f91,f87,f83])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    sK0 != sK4 | sK1 != sK5 | sK2 != sK6 | sK3 != sK7),
% 0.21/0.56    inference(cnf_transformation,[],[f10])).
% 0.21/0.56  fof(f81,plain,(
% 0.21/0.56    ~spl8_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f20,f78])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    k1_xboole_0 != sK3),
% 0.21/0.56    inference(cnf_transformation,[],[f10])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ~spl8_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f19,f73])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    k1_xboole_0 != sK2),
% 0.21/0.56    inference(cnf_transformation,[],[f10])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ~spl8_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f18,f68])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    k1_xboole_0 != sK1),
% 0.21/0.56    inference(cnf_transformation,[],[f10])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ~spl8_1),
% 0.21/0.56    inference(avatar_split_clause,[],[f17,f63])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    k1_xboole_0 != sK0),
% 0.21/0.56    inference(cnf_transformation,[],[f10])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (24950)------------------------------
% 0.21/0.56  % (24950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (24950)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (24950)Memory used [KB]: 11257
% 0.21/0.56  % (24950)Time elapsed: 0.151 s
% 0.21/0.56  % (24950)------------------------------
% 0.21/0.56  % (24950)------------------------------
% 0.21/0.56  % (24927)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.56  % (24930)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.56  % (24921)Success in time 0.205 s
%------------------------------------------------------------------------------
