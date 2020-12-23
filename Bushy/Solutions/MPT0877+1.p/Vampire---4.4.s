%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t37_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:07 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 212 expanded)
%              Number of leaves         :   21 (  84 expanded)
%              Depth                    :   11
%              Number of atoms          :  347 ( 681 expanded)
%              Number of equality atoms :  170 ( 411 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f245,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f51,f70,f108,f113,f121,f125,f133,f137,f144,f151,f152,f162,f212,f213,f223,f244])).

fof(f244,plain,
    ( spl6_5
    | spl6_11
    | spl6_13
    | spl6_21
    | ~ spl6_22 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f242,f57])).

fof(f57,plain,
    ( sK2 != sK5
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl6_5
  <=> sK2 != sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f242,plain,
    ( sK2 = sK5
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(equality_resolution,[],[f205])).

fof(f205,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | sK5 = X17 )
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f204,f89])).

fof(f89,plain,
    ( k1_xboole_0 != sK5
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl6_11
  <=> k1_xboole_0 != sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f204,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | k1_xboole_0 = sK5
        | sK5 = X17 )
    | ~ spl6_13
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f203,f95])).

fof(f95,plain,
    ( k1_xboole_0 != sK4
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_13
  <=> k1_xboole_0 != sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f203,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | k1_xboole_0 = sK4
        | k1_xboole_0 = sK5
        | sK5 = X17 )
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f194,f132])).

fof(f132,plain,
    ( k1_xboole_0 != sK0
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl6_21
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f194,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK4
        | k1_xboole_0 = sK5
        | sK5 = X17 )
    | ~ spl6_22 ),
    inference(superposition,[],[f29,f161])).

fof(f161,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK0,sK4,sK5)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl6_22
  <=> k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK0,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | X2 = X5 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t37_mcart_1.p',t36_mcart_1)).

fof(f223,plain,
    ( spl6_24
    | ~ spl6_6
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f215,f160,f59,f221])).

fof(f221,plain,
    ( spl6_24
  <=> k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK0,sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f59,plain,
    ( spl6_6
  <=> sK1 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f215,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK0,sK1,sK5)
    | ~ spl6_6
    | ~ spl6_22 ),
    inference(backward_demodulation,[],[f60,f161])).

fof(f60,plain,
    ( sK1 = sK4
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f213,plain,
    ( spl6_6
    | spl6_11
    | spl6_13
    | spl6_21
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f210,f160,f131,f94,f88,f59])).

fof(f210,plain,
    ( sK1 = sK4
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(equality_resolution,[],[f190])).

fof(f190,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | sK4 = X16 )
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f189,f89])).

fof(f189,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | k1_xboole_0 = sK5
        | sK4 = X16 )
    | ~ spl6_13
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f188,f95])).

fof(f188,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | k1_xboole_0 = sK4
        | k1_xboole_0 = sK5
        | sK4 = X16 )
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f179,f132])).

fof(f179,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK4
        | k1_xboole_0 = sK5
        | sK4 = X16 )
    | ~ spl6_22 ),
    inference(superposition,[],[f28,f161])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | X1 = X4 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f212,plain,
    ( spl6_7
    | spl6_11
    | spl6_13
    | spl6_21
    | ~ spl6_22 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f210,f63])).

fof(f63,plain,
    ( sK1 != sK4
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl6_7
  <=> sK1 != sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f162,plain,
    ( spl6_22
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f154,f65,f49,f160])).

fof(f49,plain,
    ( spl6_2
  <=> k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f65,plain,
    ( spl6_8
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f154,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK0,sK4,sK5)
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f66,f50])).

fof(f50,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f66,plain,
    ( sK0 = sK3
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f152,plain,
    ( spl6_8
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f149,f106,f65])).

fof(f106,plain,
    ( spl6_16
  <=> ! [X1,X0,X2] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X0,X1,X2)
        | sK3 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f149,plain,
    ( sK0 = sK3
    | ~ spl6_16 ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,
    ( ! [X2,X0,X1] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X0,X1,X2)
        | sK3 = X0 )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f106])).

fof(f151,plain,
    ( spl6_9
    | ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | ~ spl6_9
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f149,f69])).

fof(f69,plain,
    ( sK0 != sK3
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl6_9
  <=> sK0 != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f144,plain,
    ( spl6_16
    | ~ spl6_2
    | spl6_11
    | spl6_13
    | spl6_15 ),
    inference(avatar_split_clause,[],[f143,f100,f94,f88,f49,f106])).

fof(f100,plain,
    ( spl6_15
  <=> k1_xboole_0 != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f143,plain,
    ( ! [X4,X5,X3] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X3,X4,X5)
        | sK3 = X3 )
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f142,f89])).

fof(f142,plain,
    ( ! [X4,X5,X3] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X3,X4,X5)
        | k1_xboole_0 = sK5
        | sK3 = X3 )
    | ~ spl6_2
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f141,f95])).

fof(f141,plain,
    ( ! [X4,X5,X3] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X3,X4,X5)
        | k1_xboole_0 = sK4
        | k1_xboole_0 = sK5
        | sK3 = X3 )
    | ~ spl6_2
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f139,f101])).

fof(f101,plain,
    ( k1_xboole_0 != sK3
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f100])).

fof(f139,plain,
    ( ! [X4,X5,X3] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X3,X4,X5)
        | k1_xboole_0 = sK3
        | k1_xboole_0 = sK4
        | k1_xboole_0 = sK5
        | sK3 = X3 )
    | ~ spl6_2 ),
    inference(superposition,[],[f27,f50])).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f137,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f135,f43])).

fof(f43,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) != k1_xboole_0
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl6_1
  <=> k3_zfmisc_1(sK0,sK1,sK2) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f135,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k1_xboole_0
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f134,f37])).

fof(f37,plain,(
    ! [X2,X1] : k3_zfmisc_1(k1_xboole_0,X1,X2) = k1_xboole_0 ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t37_mcart_1.p',t35_mcart_1)).

fof(f134,plain,
    ( k3_zfmisc_1(k1_xboole_0,sK4,sK5) = k3_zfmisc_1(sK0,sK1,sK2)
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f50,f104])).

fof(f104,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_14
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f133,plain,
    ( ~ spl6_21
    | spl6_9
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f126,f103,f68,f131])).

fof(f126,plain,
    ( k1_xboole_0 != sK0
    | ~ spl6_9
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f104,f69])).

fof(f125,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f123,f43])).

fof(f123,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k1_xboole_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f122,f36])).

fof(f36,plain,(
    ! [X2,X0] : k3_zfmisc_1(X0,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f122,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,k1_xboole_0,sK5)
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f50,f98])).

fof(f98,plain,
    ( k1_xboole_0 = sK4
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl6_12
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f121,plain,
    ( ~ spl6_19
    | spl6_7
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f114,f97,f62,f119])).

fof(f119,plain,
    ( spl6_19
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f114,plain,
    ( k1_xboole_0 != sK1
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f98,f63])).

fof(f113,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f111,f43])).

fof(f111,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k1_xboole_0
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f109,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_zfmisc_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_zfmisc_1(X0,X1,X2) = k1_xboole_0
      | k1_xboole_0 != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f109,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f92,f50])).

fof(f92,plain,
    ( k1_xboole_0 = sK5
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl6_10
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f108,plain,
    ( spl6_10
    | spl6_12
    | spl6_14
    | spl6_16
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f75,f49,f106,f103,f97,f91])).

fof(f75,plain,
    ( ! [X2,X0,X1] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = sK3
        | k1_xboole_0 = sK4
        | k1_xboole_0 = sK5
        | sK3 = X0 )
    | ~ spl6_2 ),
    inference(superposition,[],[f27,f50])).

fof(f70,plain,
    ( ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f23,f68,f62,f56])).

fof(f23,plain,
    ( sK0 != sK3
    | sK1 != sK4
    | sK2 != sK5 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
       => ( ( X2 = X5
            & X1 = X4
            & X0 = X3 )
          | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t37_mcart_1.p',t37_mcart_1)).

fof(f51,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f25,f42])).

fof(f25,plain,(
    k3_zfmisc_1(sK0,sK1,sK2) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
