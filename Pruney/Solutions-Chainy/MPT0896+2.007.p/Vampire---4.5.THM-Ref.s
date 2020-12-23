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
% DateTime   : Thu Dec  3 12:59:13 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 225 expanded)
%              Number of leaves         :   25 (  94 expanded)
%              Depth                    :    8
%              Number of atoms          :  345 ( 913 expanded)
%              Number of equality atoms :  237 ( 760 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f656,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f89,f94,f245,f268,f320,f377,f402,f407,f408,f415,f420,f475,f499,f550,f655])).

fof(f655,plain,
    ( spl8_5
    | spl8_1
    | spl8_2
    | spl8_27
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f642,f374,f497,f59,f54,f74])).

fof(f74,plain,
    ( spl8_5
  <=> sK0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f54,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f59,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f497,plain,
    ( spl8_27
  <=> ! [X0] : k1_xboole_0 = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f374,plain,
    ( spl8_21
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f642,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0
        | sK0 = sK4 )
    | ~ spl8_21 ),
    inference(equality_resolution,[],[f388])).

fof(f388,plain,
    ( ! [X24,X23,X25,X22] :
        ( k2_zfmisc_1(k2_zfmisc_1(X22,X23),X24) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X25)
        | k1_xboole_0 = X24
        | k1_xboole_0 = X23
        | k1_xboole_0 = X22
        | sK4 = X22 )
    | ~ spl8_21 ),
    inference(superposition,[],[f46,f376])).

fof(f376,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f374])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X0 = X3 ) ),
    inference(definition_unfolding,[],[f34,f27,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

fof(f550,plain,
    ( spl8_4
    | ~ spl8_27 ),
    inference(avatar_contradiction_clause,[],[f549])).

fof(f549,plain,
    ( $false
    | spl8_4
    | ~ spl8_27 ),
    inference(trivial_inequality_removal,[],[f536])).

fof(f536,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl8_4
    | ~ spl8_27 ),
    inference(superposition,[],[f71,f498])).

fof(f498,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f497])).

fof(f71,plain,
    ( k1_xboole_0 != sK3
    | spl8_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl8_4
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f499,plain,
    ( spl8_27
    | spl8_6
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f489,f473,f78,f497])).

fof(f78,plain,
    ( spl8_6
  <=> sK1 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f473,plain,
    ( spl8_26
  <=> ! [X11,X13,X10,X12] :
        ( k2_zfmisc_1(k2_zfmisc_1(X11,X12),X13) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10)
        | sK5 = X12
        | k1_xboole_0 = X10 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f489,plain,
    ( ! [X0] :
        ( sK1 = sK5
        | k1_xboole_0 = X0 )
    | ~ spl8_26 ),
    inference(equality_resolution,[],[f474])).

fof(f474,plain,
    ( ! [X12,X10,X13,X11] :
        ( k2_zfmisc_1(k2_zfmisc_1(X11,X12),X13) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10)
        | sK5 = X12
        | k1_xboole_0 = X10 )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f473])).

fof(f475,plain,
    ( spl8_17
    | spl8_16
    | spl8_26
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f385,f374,f473,f193,f197])).

fof(f197,plain,
    ( spl8_17
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f193,plain,
    ( spl8_16
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f385,plain,
    ( ! [X12,X10,X13,X11] :
        ( k2_zfmisc_1(k2_zfmisc_1(X11,X12),X13) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10)
        | k1_xboole_0 = X10
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK4
        | sK5 = X12 )
    | ~ spl8_21 ),
    inference(superposition,[],[f45,f376])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X1 = X4 ) ),
    inference(definition_unfolding,[],[f35,f27,f27])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f420,plain,(
    spl8_24 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | spl8_24 ),
    inference(unit_resulting_resolution,[],[f48,f414])).

fof(f414,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK5)
    | spl8_24 ),
    inference(avatar_component_clause,[],[f412])).

fof(f412,plain,
    ( spl8_24
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f48,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f415,plain,
    ( ~ spl8_24
    | spl8_13
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f410,f197,f128,f412])).

fof(f128,plain,
    ( spl8_13
  <=> k1_xboole_0 = k2_zfmisc_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f410,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK5)
    | spl8_13
    | ~ spl8_17 ),
    inference(forward_demodulation,[],[f129,f199])).

fof(f199,plain,
    ( k1_xboole_0 = sK4
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f197])).

fof(f129,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK4,sK5)
    | spl8_13 ),
    inference(avatar_component_clause,[],[f128])).

fof(f408,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK4,sK5)
    | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK4,sK5)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f407,plain,(
    spl8_23 ),
    inference(avatar_contradiction_clause,[],[f403])).

fof(f403,plain,
    ( $false
    | spl8_23 ),
    inference(unit_resulting_resolution,[],[f47,f401])).

fof(f401,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK4,k1_xboole_0)
    | spl8_23 ),
    inference(avatar_component_clause,[],[f399])).

fof(f399,plain,
    ( spl8_23
  <=> k1_xboole_0 = k2_zfmisc_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f402,plain,
    ( ~ spl8_23
    | spl8_13
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f396,f193,f128,f399])).

fof(f396,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK4,k1_xboole_0)
    | spl8_13
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f129,f195])).

fof(f195,plain,
    ( k1_xboole_0 = sK5
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f193])).

fof(f377,plain,
    ( spl8_21
    | spl8_18
    | spl8_3
    | spl8_4
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f370,f91,f69,f64,f242,f374])).

fof(f242,plain,
    ( spl8_18
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f64,plain,
    ( spl8_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f91,plain,
    ( spl8_9
  <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f370,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)
    | ~ spl8_9 ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,
    ( ! [X17,X18,X16] :
        ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X16,X17),X18)
        | k1_xboole_0 = X18
        | k1_xboole_0 = X17
        | k1_xboole_0 = X16
        | k2_zfmisc_1(sK4,sK5) = X16 )
    | ~ spl8_9 ),
    inference(superposition,[],[f46,f93])).

fof(f93,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f320,plain,
    ( spl8_7
    | spl8_18
    | spl8_3
    | spl8_4
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f317,f91,f69,f64,f242,f82])).

fof(f82,plain,
    ( spl8_7
  <=> sK2 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f317,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | sK2 = sK6
    | ~ spl8_9 ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,
    ( ! [X12,X10,X11] :
        ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X10,X11),X12)
        | k1_xboole_0 = X12
        | k1_xboole_0 = X11
        | k1_xboole_0 = X10
        | sK6 = X11 )
    | ~ spl8_9 ),
    inference(superposition,[],[f45,f93])).

fof(f268,plain,
    ( spl8_1
    | spl8_2
    | ~ spl8_18 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | spl8_1
    | spl8_2
    | ~ spl8_18 ),
    inference(unit_resulting_resolution,[],[f61,f56,f244,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f244,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f242])).

fof(f56,plain,
    ( k1_xboole_0 != sK0
    | spl8_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f61,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f245,plain,
    ( spl8_8
    | spl8_18
    | spl8_3
    | spl8_4
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f238,f91,f69,f64,f242,f86])).

fof(f86,plain,
    ( spl8_8
  <=> sK3 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f238,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | sK3 = sK7
    | ~ spl8_9 ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,
    ( ! [X6,X4,X5] :
        ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6)
        | k1_xboole_0 = X6
        | k1_xboole_0 = X5
        | k1_xboole_0 = X4
        | sK7 = X6 )
    | ~ spl8_9 ),
    inference(superposition,[],[f44,f93])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X2 = X5 ) ),
    inference(definition_unfolding,[],[f36,f27,f27])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f94,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f38,f91])).

fof(f38,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f18,f37,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f18,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f9,f12])).

fof(f12,plain,
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f89,plain,
    ( ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f23,f86,f82,f78,f74])).

fof(f23,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,(
    ~ spl8_4 ),
    inference(avatar_split_clause,[],[f22,f69])).

fof(f22,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f13])).

fof(f67,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f21,f64])).

fof(f21,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f20,f59])).

fof(f20,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f57,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f19,f54])).

fof(f19,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.08  % Command    : run_vampire %s %d
% 0.08/0.27  % Computer   : n015.cluster.edu
% 0.08/0.27  % Model      : x86_64 x86_64
% 0.08/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.27  % Memory     : 8042.1875MB
% 0.08/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.27  % CPULimit   : 60
% 0.08/0.27  % WCLimit    : 600
% 0.08/0.27  % DateTime   : Tue Dec  1 10:16:23 EST 2020
% 0.08/0.27  % CPUTime    : 
% 0.12/0.38  % (26090)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.12/0.39  % (26087)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.12/0.39  % (26084)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.12/0.39  % (26088)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.12/0.40  % (26085)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.12/0.40  % (26086)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.12/0.41  % (26105)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.12/0.41  % (26099)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.12/0.41  % (26107)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.12/0.41  % (26103)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.12/0.41  % (26083)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.12/0.41  % (26091)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.12/0.41  % (26097)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.12/0.42  % (26100)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.12/0.42  % (26102)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.12/0.42  % (26097)Refutation not found, incomplete strategy% (26097)------------------------------
% 0.12/0.42  % (26097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.42  % (26097)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.42  
% 0.12/0.42  % (26097)Memory used [KB]: 1663
% 0.12/0.42  % (26097)Time elapsed: 0.070 s
% 0.12/0.42  % (26097)------------------------------
% 0.12/0.42  % (26097)------------------------------
% 0.12/0.42  % (26101)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.12/0.42  % (26101)Refutation not found, incomplete strategy% (26101)------------------------------
% 0.12/0.42  % (26101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.42  % (26101)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.42  
% 0.12/0.42  % (26101)Memory used [KB]: 1663
% 0.12/0.42  % (26101)Time elapsed: 0.113 s
% 0.12/0.42  % (26101)------------------------------
% 0.12/0.42  % (26101)------------------------------
% 0.12/0.42  % (26099)Refutation not found, incomplete strategy% (26099)------------------------------
% 0.12/0.42  % (26099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.42  % (26099)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.42  
% 0.12/0.42  % (26099)Memory used [KB]: 10618
% 0.12/0.42  % (26099)Time elapsed: 0.109 s
% 0.12/0.42  % (26099)------------------------------
% 0.12/0.42  % (26099)------------------------------
% 0.12/0.42  % (26093)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.12/0.43  % (26094)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.12/0.44  % (26096)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.12/0.44  % (26110)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.12/0.44  % (26089)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.12/0.44  % (26095)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.12/0.44  % (26092)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.12/0.44  % (26095)Refutation not found, incomplete strategy% (26095)------------------------------
% 0.12/0.44  % (26095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.44  % (26095)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.44  
% 0.12/0.44  % (26095)Memory used [KB]: 10746
% 0.12/0.44  % (26095)Time elapsed: 0.131 s
% 0.12/0.44  % (26095)------------------------------
% 0.12/0.44  % (26095)------------------------------
% 0.12/0.44  % (26109)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.12/0.44  % (26112)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.12/0.44  % (26111)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.12/0.45  % (26112)Refutation not found, incomplete strategy% (26112)------------------------------
% 0.12/0.45  % (26112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.45  % (26108)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.12/0.45  % (26112)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.45  
% 0.12/0.45  % (26112)Memory used [KB]: 1663
% 0.12/0.45  % (26112)Time elapsed: 0.137 s
% 0.12/0.45  % (26112)------------------------------
% 0.12/0.45  % (26112)------------------------------
% 0.12/0.45  % (26109)Refutation not found, incomplete strategy% (26109)------------------------------
% 0.12/0.45  % (26109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.45  % (26106)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.12/0.45  % (26109)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.45  
% 0.12/0.45  % (26109)Memory used [KB]: 6268
% 0.12/0.45  % (26109)Time elapsed: 0.135 s
% 0.12/0.45  % (26109)------------------------------
% 0.12/0.45  % (26109)------------------------------
% 0.12/0.47  % (26104)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.12/0.47  % (26098)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.12/0.48  % (26093)Refutation found. Thanks to Tanya!
% 0.12/0.48  % SZS status Theorem for theBenchmark
% 0.12/0.48  % SZS output start Proof for theBenchmark
% 0.12/0.48  fof(f656,plain,(
% 0.12/0.48    $false),
% 0.12/0.48    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f89,f94,f245,f268,f320,f377,f402,f407,f408,f415,f420,f475,f499,f550,f655])).
% 0.12/0.48  fof(f655,plain,(
% 0.12/0.48    spl8_5 | spl8_1 | spl8_2 | spl8_27 | ~spl8_21),
% 0.12/0.48    inference(avatar_split_clause,[],[f642,f374,f497,f59,f54,f74])).
% 0.12/0.48  fof(f74,plain,(
% 0.12/0.48    spl8_5 <=> sK0 = sK4),
% 0.12/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.12/0.48  fof(f54,plain,(
% 0.12/0.48    spl8_1 <=> k1_xboole_0 = sK0),
% 0.12/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.12/0.48  fof(f59,plain,(
% 0.12/0.48    spl8_2 <=> k1_xboole_0 = sK1),
% 0.12/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.12/0.48  fof(f497,plain,(
% 0.12/0.48    spl8_27 <=> ! [X0] : k1_xboole_0 = X0),
% 0.12/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.12/0.48  fof(f374,plain,(
% 0.12/0.48    spl8_21 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)),
% 0.12/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.12/0.48  fof(f642,plain,(
% 0.12/0.48    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK0 = sK4) ) | ~spl8_21),
% 0.12/0.48    inference(equality_resolution,[],[f388])).
% 0.12/0.48  fof(f388,plain,(
% 0.12/0.48    ( ! [X24,X23,X25,X22] : (k2_zfmisc_1(k2_zfmisc_1(X22,X23),X24) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X25) | k1_xboole_0 = X24 | k1_xboole_0 = X23 | k1_xboole_0 = X22 | sK4 = X22) ) | ~spl8_21),
% 0.12/0.48    inference(superposition,[],[f46,f376])).
% 0.12/0.48  fof(f376,plain,(
% 0.12/0.48    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) | ~spl8_21),
% 0.12/0.48    inference(avatar_component_clause,[],[f374])).
% 0.12/0.48  fof(f46,plain,(
% 0.12/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X0 = X3) )),
% 0.12/0.48    inference(definition_unfolding,[],[f34,f27,f27])).
% 0.12/0.48  fof(f27,plain,(
% 0.12/0.48    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.12/0.48    inference(cnf_transformation,[],[f2])).
% 0.12/0.48  fof(f2,axiom,(
% 0.12/0.48    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.12/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.12/0.48  fof(f34,plain,(
% 0.12/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 0.12/0.48    inference(cnf_transformation,[],[f11])).
% 0.12/0.48  fof(f11,plain,(
% 0.12/0.48    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.12/0.48    inference(flattening,[],[f10])).
% 0.12/0.48  fof(f10,plain,(
% 0.12/0.48    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 0.12/0.48    inference(ennf_transformation,[],[f4])).
% 0.12/0.48  fof(f4,axiom,(
% 0.12/0.48    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.12/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).
% 0.12/0.48  fof(f550,plain,(
% 0.12/0.48    spl8_4 | ~spl8_27),
% 0.12/0.48    inference(avatar_contradiction_clause,[],[f549])).
% 0.12/0.48  fof(f549,plain,(
% 0.12/0.48    $false | (spl8_4 | ~spl8_27)),
% 0.12/0.48    inference(trivial_inequality_removal,[],[f536])).
% 0.12/0.48  fof(f536,plain,(
% 0.12/0.48    k1_xboole_0 != k1_xboole_0 | (spl8_4 | ~spl8_27)),
% 0.12/0.48    inference(superposition,[],[f71,f498])).
% 0.12/0.48  fof(f498,plain,(
% 0.12/0.48    ( ! [X0] : (k1_xboole_0 = X0) ) | ~spl8_27),
% 0.12/0.48    inference(avatar_component_clause,[],[f497])).
% 0.12/0.48  fof(f71,plain,(
% 0.12/0.48    k1_xboole_0 != sK3 | spl8_4),
% 0.12/0.48    inference(avatar_component_clause,[],[f69])).
% 0.12/0.48  fof(f69,plain,(
% 0.12/0.48    spl8_4 <=> k1_xboole_0 = sK3),
% 0.12/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.12/0.48  fof(f499,plain,(
% 0.12/0.48    spl8_27 | spl8_6 | ~spl8_26),
% 0.12/0.48    inference(avatar_split_clause,[],[f489,f473,f78,f497])).
% 0.12/0.48  fof(f78,plain,(
% 0.12/0.48    spl8_6 <=> sK1 = sK5),
% 0.12/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.12/0.48  fof(f473,plain,(
% 0.12/0.48    spl8_26 <=> ! [X11,X13,X10,X12] : (k2_zfmisc_1(k2_zfmisc_1(X11,X12),X13) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10) | sK5 = X12 | k1_xboole_0 = X10)),
% 0.12/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.12/0.48  fof(f489,plain,(
% 0.12/0.48    ( ! [X0] : (sK1 = sK5 | k1_xboole_0 = X0) ) | ~spl8_26),
% 0.12/0.48    inference(equality_resolution,[],[f474])).
% 0.12/0.48  fof(f474,plain,(
% 0.12/0.48    ( ! [X12,X10,X13,X11] : (k2_zfmisc_1(k2_zfmisc_1(X11,X12),X13) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10) | sK5 = X12 | k1_xboole_0 = X10) ) | ~spl8_26),
% 0.12/0.48    inference(avatar_component_clause,[],[f473])).
% 0.12/0.48  fof(f475,plain,(
% 0.12/0.48    spl8_17 | spl8_16 | spl8_26 | ~spl8_21),
% 0.12/0.48    inference(avatar_split_clause,[],[f385,f374,f473,f193,f197])).
% 0.12/0.48  fof(f197,plain,(
% 0.12/0.48    spl8_17 <=> k1_xboole_0 = sK4),
% 0.12/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.12/0.48  fof(f193,plain,(
% 0.12/0.48    spl8_16 <=> k1_xboole_0 = sK5),
% 0.12/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.12/0.48  fof(f385,plain,(
% 0.12/0.48    ( ! [X12,X10,X13,X11] : (k2_zfmisc_1(k2_zfmisc_1(X11,X12),X13) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X10) | k1_xboole_0 = X10 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | sK5 = X12) ) | ~spl8_21),
% 0.12/0.48    inference(superposition,[],[f45,f376])).
% 0.12/0.48  fof(f45,plain,(
% 0.12/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X1 = X4) )),
% 0.12/0.48    inference(definition_unfolding,[],[f35,f27,f27])).
% 0.12/0.48  fof(f35,plain,(
% 0.12/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 0.12/0.48    inference(cnf_transformation,[],[f11])).
% 0.12/0.48  fof(f420,plain,(
% 0.12/0.48    spl8_24),
% 0.12/0.48    inference(avatar_contradiction_clause,[],[f416])).
% 0.12/0.48  fof(f416,plain,(
% 0.12/0.48    $false | spl8_24),
% 0.12/0.48    inference(unit_resulting_resolution,[],[f48,f414])).
% 0.12/0.48  fof(f414,plain,(
% 0.12/0.48    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK5) | spl8_24),
% 0.12/0.48    inference(avatar_component_clause,[],[f412])).
% 0.12/0.48  fof(f412,plain,(
% 0.12/0.48    spl8_24 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK5)),
% 0.12/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.12/0.48  fof(f48,plain,(
% 0.12/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.12/0.48    inference(equality_resolution,[],[f25])).
% 0.12/0.48  fof(f25,plain,(
% 0.12/0.48    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.12/0.48    inference(cnf_transformation,[],[f15])).
% 0.12/0.48  fof(f15,plain,(
% 0.12/0.48    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.12/0.48    inference(flattening,[],[f14])).
% 0.12/0.48  fof(f14,plain,(
% 0.12/0.48    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.12/0.48    inference(nnf_transformation,[],[f1])).
% 0.12/0.48  fof(f1,axiom,(
% 0.12/0.48    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.12/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.12/0.48  fof(f415,plain,(
% 0.12/0.48    ~spl8_24 | spl8_13 | ~spl8_17),
% 0.12/0.48    inference(avatar_split_clause,[],[f410,f197,f128,f412])).
% 0.12/0.48  fof(f128,plain,(
% 0.12/0.48    spl8_13 <=> k1_xboole_0 = k2_zfmisc_1(sK4,sK5)),
% 0.12/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.12/0.48  fof(f410,plain,(
% 0.12/0.48    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK5) | (spl8_13 | ~spl8_17)),
% 0.12/0.48    inference(forward_demodulation,[],[f129,f199])).
% 0.12/0.48  fof(f199,plain,(
% 0.12/0.48    k1_xboole_0 = sK4 | ~spl8_17),
% 0.12/0.48    inference(avatar_component_clause,[],[f197])).
% 0.12/0.49  fof(f129,plain,(
% 0.12/0.49    k1_xboole_0 != k2_zfmisc_1(sK4,sK5) | spl8_13),
% 0.12/0.49    inference(avatar_component_clause,[],[f128])).
% 0.12/0.49  fof(f408,plain,(
% 0.12/0.49    k1_xboole_0 != k2_zfmisc_1(sK4,sK5) | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK4,sK5) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.12/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.12/0.49  fof(f407,plain,(
% 0.12/0.49    spl8_23),
% 0.12/0.49    inference(avatar_contradiction_clause,[],[f403])).
% 0.12/0.49  fof(f403,plain,(
% 0.12/0.49    $false | spl8_23),
% 0.12/0.49    inference(unit_resulting_resolution,[],[f47,f401])).
% 0.12/0.49  fof(f401,plain,(
% 0.12/0.49    k1_xboole_0 != k2_zfmisc_1(sK4,k1_xboole_0) | spl8_23),
% 0.12/0.49    inference(avatar_component_clause,[],[f399])).
% 0.12/0.49  fof(f399,plain,(
% 0.12/0.49    spl8_23 <=> k1_xboole_0 = k2_zfmisc_1(sK4,k1_xboole_0)),
% 0.12/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.12/0.49  fof(f47,plain,(
% 0.12/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.12/0.49    inference(equality_resolution,[],[f26])).
% 0.12/0.49  fof(f26,plain,(
% 0.12/0.49    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.12/0.49    inference(cnf_transformation,[],[f15])).
% 0.12/0.49  fof(f402,plain,(
% 0.12/0.49    ~spl8_23 | spl8_13 | ~spl8_16),
% 0.12/0.49    inference(avatar_split_clause,[],[f396,f193,f128,f399])).
% 0.12/0.49  fof(f396,plain,(
% 0.12/0.49    k1_xboole_0 != k2_zfmisc_1(sK4,k1_xboole_0) | (spl8_13 | ~spl8_16)),
% 0.12/0.49    inference(backward_demodulation,[],[f129,f195])).
% 0.12/0.49  fof(f195,plain,(
% 0.12/0.49    k1_xboole_0 = sK5 | ~spl8_16),
% 0.12/0.49    inference(avatar_component_clause,[],[f193])).
% 0.12/0.49  fof(f377,plain,(
% 0.12/0.49    spl8_21 | spl8_18 | spl8_3 | spl8_4 | ~spl8_9),
% 0.12/0.49    inference(avatar_split_clause,[],[f370,f91,f69,f64,f242,f374])).
% 0.12/0.49  fof(f242,plain,(
% 0.12/0.49    spl8_18 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.12/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.12/0.49  fof(f64,plain,(
% 0.12/0.49    spl8_3 <=> k1_xboole_0 = sK2),
% 0.12/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.12/0.49  fof(f91,plain,(
% 0.12/0.49    spl8_9 <=> k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 0.12/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.12/0.49  fof(f370,plain,(
% 0.12/0.49    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) | ~spl8_9),
% 0.12/0.49    inference(equality_resolution,[],[f101])).
% 0.12/0.49  fof(f101,plain,(
% 0.12/0.49    ( ! [X17,X18,X16] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X16,X17),X18) | k1_xboole_0 = X18 | k1_xboole_0 = X17 | k1_xboole_0 = X16 | k2_zfmisc_1(sK4,sK5) = X16) ) | ~spl8_9),
% 0.12/0.49    inference(superposition,[],[f46,f93])).
% 0.12/0.49  fof(f93,plain,(
% 0.12/0.49    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) | ~spl8_9),
% 0.12/0.49    inference(avatar_component_clause,[],[f91])).
% 0.12/0.49  fof(f320,plain,(
% 0.12/0.49    spl8_7 | spl8_18 | spl8_3 | spl8_4 | ~spl8_9),
% 0.12/0.49    inference(avatar_split_clause,[],[f317,f91,f69,f64,f242,f82])).
% 0.12/0.49  fof(f82,plain,(
% 0.12/0.49    spl8_7 <=> sK2 = sK6),
% 0.12/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.12/0.49  fof(f317,plain,(
% 0.12/0.49    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | sK2 = sK6 | ~spl8_9),
% 0.12/0.49    inference(equality_resolution,[],[f99])).
% 0.12/0.49  fof(f99,plain,(
% 0.12/0.49    ( ! [X12,X10,X11] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X10,X11),X12) | k1_xboole_0 = X12 | k1_xboole_0 = X11 | k1_xboole_0 = X10 | sK6 = X11) ) | ~spl8_9),
% 0.12/0.49    inference(superposition,[],[f45,f93])).
% 0.12/0.49  fof(f268,plain,(
% 0.12/0.49    spl8_1 | spl8_2 | ~spl8_18),
% 0.12/0.49    inference(avatar_contradiction_clause,[],[f256])).
% 0.12/0.49  fof(f256,plain,(
% 0.12/0.49    $false | (spl8_1 | spl8_2 | ~spl8_18)),
% 0.12/0.49    inference(unit_resulting_resolution,[],[f61,f56,f244,f24])).
% 0.12/0.49  fof(f24,plain,(
% 0.12/0.49    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.12/0.49    inference(cnf_transformation,[],[f15])).
% 0.12/0.49  fof(f244,plain,(
% 0.12/0.49    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_18),
% 0.12/0.49    inference(avatar_component_clause,[],[f242])).
% 0.12/0.49  fof(f56,plain,(
% 0.12/0.49    k1_xboole_0 != sK0 | spl8_1),
% 0.12/0.49    inference(avatar_component_clause,[],[f54])).
% 0.12/0.49  fof(f61,plain,(
% 0.12/0.49    k1_xboole_0 != sK1 | spl8_2),
% 0.12/0.49    inference(avatar_component_clause,[],[f59])).
% 0.12/0.49  fof(f245,plain,(
% 0.12/0.49    spl8_8 | spl8_18 | spl8_3 | spl8_4 | ~spl8_9),
% 0.12/0.49    inference(avatar_split_clause,[],[f238,f91,f69,f64,f242,f86])).
% 0.12/0.49  fof(f86,plain,(
% 0.12/0.49    spl8_8 <=> sK3 = sK7),
% 0.12/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.12/0.49  fof(f238,plain,(
% 0.12/0.49    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | sK3 = sK7 | ~spl8_9),
% 0.12/0.49    inference(equality_resolution,[],[f97])).
% 0.12/0.49  fof(f97,plain,(
% 0.12/0.49    ( ! [X6,X4,X5] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6) | k1_xboole_0 = X6 | k1_xboole_0 = X5 | k1_xboole_0 = X4 | sK7 = X6) ) | ~spl8_9),
% 0.12/0.49    inference(superposition,[],[f44,f93])).
% 0.12/0.49  fof(f44,plain,(
% 0.12/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X2 = X5) )),
% 0.12/0.49    inference(definition_unfolding,[],[f36,f27,f27])).
% 0.12/0.49  fof(f36,plain,(
% 0.12/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 0.12/0.49    inference(cnf_transformation,[],[f11])).
% 0.12/0.49  fof(f94,plain,(
% 0.12/0.49    spl8_9),
% 0.12/0.49    inference(avatar_split_clause,[],[f38,f91])).
% 0.12/0.49  fof(f38,plain,(
% 0.12/0.49    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 0.12/0.49    inference(definition_unfolding,[],[f18,f37,f37])).
% 0.12/0.49  fof(f37,plain,(
% 0.12/0.49    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.12/0.49    inference(definition_unfolding,[],[f28,f27])).
% 0.12/0.49  fof(f28,plain,(
% 0.12/0.49    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.12/0.49    inference(cnf_transformation,[],[f3])).
% 0.12/0.49  fof(f3,axiom,(
% 0.12/0.49    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.12/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.12/0.49  fof(f18,plain,(
% 0.12/0.49    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 0.12/0.49    inference(cnf_transformation,[],[f13])).
% 0.12/0.49  fof(f13,plain,(
% 0.12/0.49    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 0.12/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f9,f12])).
% 0.12/0.49  fof(f12,plain,(
% 0.12/0.49    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.12/0.49    introduced(choice_axiom,[])).
% 0.12/0.49  fof(f9,plain,(
% 0.12/0.49    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 0.12/0.49    inference(flattening,[],[f8])).
% 0.12/0.49  fof(f8,plain,(
% 0.12/0.49    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 0.12/0.49    inference(ennf_transformation,[],[f7])).
% 0.12/0.49  fof(f7,negated_conjecture,(
% 0.12/0.49    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.12/0.49    inference(negated_conjecture,[],[f6])).
% 0.12/0.49  fof(f6,conjecture,(
% 0.12/0.49    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.12/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_mcart_1)).
% 0.12/0.49  fof(f89,plain,(
% 0.12/0.49    ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8),
% 0.12/0.49    inference(avatar_split_clause,[],[f23,f86,f82,f78,f74])).
% 0.12/0.49  fof(f23,plain,(
% 0.12/0.49    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 0.12/0.49    inference(cnf_transformation,[],[f13])).
% 0.12/0.49  fof(f72,plain,(
% 0.12/0.49    ~spl8_4),
% 0.12/0.49    inference(avatar_split_clause,[],[f22,f69])).
% 0.12/0.49  fof(f22,plain,(
% 0.12/0.49    k1_xboole_0 != sK3),
% 0.12/0.49    inference(cnf_transformation,[],[f13])).
% 0.12/0.49  fof(f67,plain,(
% 0.12/0.49    ~spl8_3),
% 0.12/0.49    inference(avatar_split_clause,[],[f21,f64])).
% 0.12/0.49  fof(f21,plain,(
% 0.12/0.49    k1_xboole_0 != sK2),
% 0.12/0.49    inference(cnf_transformation,[],[f13])).
% 0.12/0.49  fof(f62,plain,(
% 0.12/0.49    ~spl8_2),
% 0.12/0.49    inference(avatar_split_clause,[],[f20,f59])).
% 0.12/0.49  fof(f20,plain,(
% 0.12/0.49    k1_xboole_0 != sK1),
% 0.12/0.49    inference(cnf_transformation,[],[f13])).
% 0.12/0.49  fof(f57,plain,(
% 0.12/0.49    ~spl8_1),
% 0.12/0.49    inference(avatar_split_clause,[],[f19,f54])).
% 0.12/0.49  fof(f19,plain,(
% 0.12/0.49    k1_xboole_0 != sK0),
% 0.12/0.49    inference(cnf_transformation,[],[f13])).
% 0.12/0.49  % SZS output end Proof for theBenchmark
% 0.12/0.49  % (26093)------------------------------
% 0.12/0.49  % (26093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.49  % (26093)Termination reason: Refutation
% 0.12/0.49  
% 0.12/0.49  % (26093)Memory used [KB]: 11129
% 0.12/0.49  % (26093)Time elapsed: 0.181 s
% 0.12/0.49  % (26093)------------------------------
% 0.12/0.49  % (26093)------------------------------
% 0.12/0.49  % (26082)Success in time 0.208 s
%------------------------------------------------------------------------------
