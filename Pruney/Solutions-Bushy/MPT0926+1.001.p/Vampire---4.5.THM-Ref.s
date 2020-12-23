%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0926+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 303 expanded)
%              Number of leaves         :   32 ( 147 expanded)
%              Depth                    :    7
%              Number of atoms          :  408 (1971 expanded)
%              Number of equality atoms :  205 (1454 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f277,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f67,f72,f77,f82,f87,f92,f97,f102,f108,f114,f120,f126,f132,f142,f152,f214,f219,f224,f229,f235,f272,f274,f276])).

fof(f276,plain,
    ( ~ spl11_23
    | spl11_24 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | ~ spl11_23
    | spl11_24 ),
    inference(subsumption_resolution,[],[f267,f218])).

% (5617)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f218,plain,
    ( k9_mcart_1(sK1,sK2,sK3,sK4,sK9) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
    | spl11_24 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl11_24
  <=> k9_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f267,plain,
    ( k9_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
    | ~ spl11_23 ),
    inference(unit_resulting_resolution,[],[f149,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k9_mcart_1(X4,X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k11_mcart_1(X4,X3,X2,X1,X0) = k2_mcart_1(X0)
        & k10_mcart_1(X4,X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0))
        & k9_mcart_1(X4,X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
        & k8_mcart_1(X4,X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0))) )
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
        & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
        & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
        & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
      | ~ sP0(X4,X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
        & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
        & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
        & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
      | ~ sP0(X4,X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f149,plain,
    ( sP0(sK9,sK4,sK3,sK2,sK1)
    | ~ spl11_23 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl11_23
  <=> sP0(sK9,sK4,sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f274,plain,
    ( ~ spl11_23
    | spl11_25 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | ~ spl11_23
    | spl11_25 ),
    inference(subsumption_resolution,[],[f268,f223])).

fof(f223,plain,
    ( k8_mcart_1(sK1,sK2,sK3,sK4,sK9) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
    | spl11_25 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl11_25
  <=> k8_mcart_1(sK1,sK2,sK3,sK4,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).

fof(f268,plain,
    ( k8_mcart_1(sK1,sK2,sK3,sK4,sK9) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
    | ~ spl11_23 ),
    inference(unit_resulting_resolution,[],[f149,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_mcart_1(X4,X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f272,plain,
    ( ~ spl11_23
    | spl11_26 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | ~ spl11_23
    | spl11_26 ),
    inference(subsumption_resolution,[],[f269,f228])).

fof(f228,plain,
    ( k10_mcart_1(sK1,sK2,sK3,sK4,sK9) != k2_mcart_1(k1_mcart_1(sK9))
    | spl11_26 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl11_26
  <=> k10_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(k1_mcart_1(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f269,plain,
    ( k10_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(k1_mcart_1(sK9))
    | ~ spl11_23 ),
    inference(unit_resulting_resolution,[],[f149,f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k10_mcart_1(X4,X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f235,plain,
    ( spl11_23
    | ~ spl11_7
    | spl11_12
    | spl11_13
    | spl11_14
    | spl11_15 ),
    inference(avatar_split_clause,[],[f157,f99,f94,f89,f84,f59,f148])).

fof(f59,plain,
    ( spl11_7
  <=> m1_subset_1(sK9,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f84,plain,
    ( spl11_12
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f89,plain,
    ( spl11_13
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f94,plain,
    ( spl11_14
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f99,plain,
    ( spl11_15
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f157,plain,
    ( sP0(sK9,sK4,sK3,sK2,sK1)
    | ~ spl11_7
    | spl11_12
    | spl11_13
    | spl11_14
    | spl11_15 ),
    inference(unit_resulting_resolution,[],[f101,f96,f91,f86,f61,f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | sP0(X4,X3,X2,X1,X0)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( sP0(X4,X3,X2,X1,X0)
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f5,f6])).

fof(f5,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
            & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
            & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
                & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

fof(f61,plain,
    ( m1_subset_1(sK9,k4_zfmisc_1(sK1,sK2,sK3,sK4))
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f86,plain,
    ( k1_xboole_0 != sK4
    | spl11_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f91,plain,
    ( k1_xboole_0 != sK3
    | spl11_13 ),
    inference(avatar_component_clause,[],[f89])).

fof(f96,plain,
    ( k1_xboole_0 != sK2
    | spl11_14 ),
    inference(avatar_component_clause,[],[f94])).

fof(f101,plain,
    ( k1_xboole_0 != sK1
    | spl11_15 ),
    inference(avatar_component_clause,[],[f99])).

fof(f229,plain,
    ( ~ spl11_21
    | ~ spl11_26
    | spl11_18 ),
    inference(avatar_split_clause,[],[f143,f117,f226,f135])).

fof(f135,plain,
    ( spl11_21
  <=> sP0(sK9,sK8,sK7,sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

% (5626)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f117,plain,
    ( spl11_18
  <=> k10_mcart_1(sK1,sK2,sK3,sK4,sK9) = k10_mcart_1(sK5,sK6,sK7,sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f143,plain,
    ( k10_mcart_1(sK1,sK2,sK3,sK4,sK9) != k2_mcart_1(k1_mcart_1(sK9))
    | ~ sP0(sK9,sK8,sK7,sK6,sK5)
    | spl11_18 ),
    inference(superposition,[],[f119,f28])).

fof(f119,plain,
    ( k10_mcart_1(sK1,sK2,sK3,sK4,sK9) != k10_mcart_1(sK5,sK6,sK7,sK8,sK9)
    | spl11_18 ),
    inference(avatar_component_clause,[],[f117])).

fof(f224,plain,
    ( ~ spl11_21
    | ~ spl11_25
    | spl11_20 ),
    inference(avatar_split_clause,[],[f153,f129,f221,f135])).

fof(f129,plain,
    ( spl11_20
  <=> k8_mcart_1(sK1,sK2,sK3,sK4,sK9) = k8_mcart_1(sK5,sK6,sK7,sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f153,plain,
    ( k8_mcart_1(sK1,sK2,sK3,sK4,sK9) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
    | ~ sP0(sK9,sK8,sK7,sK6,sK5)
    | spl11_20 ),
    inference(superposition,[],[f131,f26])).

fof(f131,plain,
    ( k8_mcart_1(sK1,sK2,sK3,sK4,sK9) != k8_mcart_1(sK5,sK6,sK7,sK8,sK9)
    | spl11_20 ),
    inference(avatar_component_clause,[],[f129])).

fof(f219,plain,
    ( ~ spl11_21
    | ~ spl11_24
    | spl11_19 ),
    inference(avatar_split_clause,[],[f154,f123,f216,f135])).

fof(f123,plain,
    ( spl11_19
  <=> k9_mcart_1(sK1,sK2,sK3,sK4,sK9) = k9_mcart_1(sK5,sK6,sK7,sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

% (5614)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f154,plain,
    ( k9_mcart_1(sK1,sK2,sK3,sK4,sK9) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK9)))
    | ~ sP0(sK9,sK8,sK7,sK6,sK5)
    | spl11_19 ),
    inference(superposition,[],[f125,f27])).

fof(f125,plain,
    ( k9_mcart_1(sK1,sK2,sK3,sK4,sK9) != k9_mcart_1(sK5,sK6,sK7,sK8,sK9)
    | spl11_19 ),
    inference(avatar_component_clause,[],[f123])).

fof(f214,plain,
    ( spl11_21
    | spl11_8
    | spl11_9
    | spl11_10
    | spl11_11
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f163,f105,f79,f74,f69,f64,f135])).

fof(f64,plain,
    ( spl11_8
  <=> k1_xboole_0 = sK8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f69,plain,
    ( spl11_9
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f74,plain,
    ( spl11_10
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f79,plain,
    ( spl11_11
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f105,plain,
    ( spl11_16
  <=> m1_subset_1(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f163,plain,
    ( sP0(sK9,sK8,sK7,sK6,sK5)
    | spl11_8
    | spl11_9
    | spl11_10
    | spl11_11
    | ~ spl11_16 ),
    inference(unit_resulting_resolution,[],[f81,f76,f71,f66,f107,f30])).

fof(f107,plain,
    ( m1_subset_1(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8))
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f105])).

fof(f66,plain,
    ( k1_xboole_0 != sK8
    | spl11_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f71,plain,
    ( k1_xboole_0 != sK7
    | spl11_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f76,plain,
    ( k1_xboole_0 != sK6
    | spl11_10 ),
    inference(avatar_component_clause,[],[f74])).

fof(f81,plain,
    ( k1_xboole_0 != sK5
    | spl11_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f152,plain,
    ( ~ spl11_23
    | spl11_22 ),
    inference(avatar_split_clause,[],[f146,f139,f148])).

fof(f139,plain,
    ( spl11_22
  <=> k11_mcart_1(sK1,sK2,sK3,sK4,sK9) = k2_mcart_1(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f146,plain,
    ( ~ sP0(sK9,sK4,sK3,sK2,sK1)
    | spl11_22 ),
    inference(trivial_inequality_removal,[],[f145])).

fof(f145,plain,
    ( k2_mcart_1(sK9) != k2_mcart_1(sK9)
    | ~ sP0(sK9,sK4,sK3,sK2,sK1)
    | spl11_22 ),
    inference(superposition,[],[f141,f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k11_mcart_1(X4,X3,X2,X1,X0) = k2_mcart_1(X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f141,plain,
    ( k11_mcart_1(sK1,sK2,sK3,sK4,sK9) != k2_mcart_1(sK9)
    | spl11_22 ),
    inference(avatar_component_clause,[],[f139])).

% (5623)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f142,plain,
    ( ~ spl11_21
    | ~ spl11_22
    | spl11_17 ),
    inference(avatar_split_clause,[],[f133,f111,f139,f135])).

fof(f111,plain,
    ( spl11_17
  <=> k11_mcart_1(sK1,sK2,sK3,sK4,sK9) = k11_mcart_1(sK5,sK6,sK7,sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f133,plain,
    ( k11_mcart_1(sK1,sK2,sK3,sK4,sK9) != k2_mcart_1(sK9)
    | ~ sP0(sK9,sK8,sK7,sK6,sK5)
    | spl11_17 ),
    inference(superposition,[],[f113,f29])).

fof(f113,plain,
    ( k11_mcart_1(sK1,sK2,sK3,sK4,sK9) != k11_mcart_1(sK5,sK6,sK7,sK8,sK9)
    | spl11_17 ),
    inference(avatar_component_clause,[],[f111])).

fof(f132,plain,
    ( ~ spl11_20
    | spl11_1
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f127,f49,f32,f129])).

fof(f32,plain,
    ( spl11_1
  <=> k8_mcart_1(sK1,sK2,sK3,sK4,sK9) = k8_mcart_1(sK5,sK6,sK7,sK8,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f49,plain,
    ( spl11_5
  <=> sK9 = sK10 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f127,plain,
    ( k8_mcart_1(sK1,sK2,sK3,sK4,sK9) != k8_mcart_1(sK5,sK6,sK7,sK8,sK9)
    | spl11_1
    | ~ spl11_5 ),
    inference(forward_demodulation,[],[f34,f51])).

fof(f51,plain,
    ( sK9 = sK10
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f34,plain,
    ( k8_mcart_1(sK1,sK2,sK3,sK4,sK9) != k8_mcart_1(sK5,sK6,sK7,sK8,sK10)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f126,plain,
    ( ~ spl11_19
    | spl11_2
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f121,f49,f36,f123])).

fof(f36,plain,
    ( spl11_2
  <=> k9_mcart_1(sK1,sK2,sK3,sK4,sK9) = k9_mcart_1(sK5,sK6,sK7,sK8,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f121,plain,
    ( k9_mcart_1(sK1,sK2,sK3,sK4,sK9) != k9_mcart_1(sK5,sK6,sK7,sK8,sK9)
    | spl11_2
    | ~ spl11_5 ),
    inference(forward_demodulation,[],[f38,f51])).

fof(f38,plain,
    ( k9_mcart_1(sK1,sK2,sK3,sK4,sK9) != k9_mcart_1(sK5,sK6,sK7,sK8,sK10)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f120,plain,
    ( ~ spl11_18
    | spl11_3
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f115,f49,f40,f117])).

fof(f40,plain,
    ( spl11_3
  <=> k10_mcart_1(sK1,sK2,sK3,sK4,sK9) = k10_mcart_1(sK5,sK6,sK7,sK8,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f115,plain,
    ( k10_mcart_1(sK1,sK2,sK3,sK4,sK9) != k10_mcart_1(sK5,sK6,sK7,sK8,sK9)
    | spl11_3
    | ~ spl11_5 ),
    inference(forward_demodulation,[],[f42,f51])).

fof(f42,plain,
    ( k10_mcart_1(sK1,sK2,sK3,sK4,sK9) != k10_mcart_1(sK5,sK6,sK7,sK8,sK10)
    | spl11_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f114,plain,
    ( ~ spl11_17
    | spl11_4
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f109,f49,f44,f111])).

fof(f44,plain,
    ( spl11_4
  <=> k11_mcart_1(sK1,sK2,sK3,sK4,sK9) = k11_mcart_1(sK5,sK6,sK7,sK8,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f109,plain,
    ( k11_mcart_1(sK1,sK2,sK3,sK4,sK9) != k11_mcart_1(sK5,sK6,sK7,sK8,sK9)
    | spl11_4
    | ~ spl11_5 ),
    inference(forward_demodulation,[],[f46,f51])).

fof(f46,plain,
    ( k11_mcart_1(sK1,sK2,sK3,sK4,sK9) != k11_mcart_1(sK5,sK6,sK7,sK8,sK10)
    | spl11_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f108,plain,
    ( spl11_16
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f103,f54,f49,f105])).

fof(f54,plain,
    ( spl11_6
  <=> m1_subset_1(sK10,k4_zfmisc_1(sK5,sK6,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f103,plain,
    ( m1_subset_1(sK9,k4_zfmisc_1(sK5,sK6,sK7,sK8))
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(backward_demodulation,[],[f56,f51])).

fof(f56,plain,
    ( m1_subset_1(sK10,k4_zfmisc_1(sK5,sK6,sK7,sK8))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f102,plain,(
    ~ spl11_15 ),
    inference(avatar_split_clause,[],[f14,f99])).

fof(f14,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( k11_mcart_1(sK1,sK2,sK3,sK4,sK9) != k11_mcart_1(sK5,sK6,sK7,sK8,sK10)
      | k10_mcart_1(sK1,sK2,sK3,sK4,sK9) != k10_mcart_1(sK5,sK6,sK7,sK8,sK10)
      | k9_mcart_1(sK1,sK2,sK3,sK4,sK9) != k9_mcart_1(sK5,sK6,sK7,sK8,sK10)
      | k8_mcart_1(sK1,sK2,sK3,sK4,sK9) != k8_mcart_1(sK5,sK6,sK7,sK8,sK10) )
    & sK9 = sK10
    & m1_subset_1(sK10,k4_zfmisc_1(sK5,sK6,sK7,sK8))
    & m1_subset_1(sK9,k4_zfmisc_1(sK1,sK2,sK3,sK4))
    & k1_xboole_0 != sK8
    & k1_xboole_0 != sK7
    & k1_xboole_0 != sK6
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f4,f10,f9,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ? [X8] :
            ( ? [X9] :
                ( ( k11_mcart_1(X0,X1,X2,X3,X8) != k11_mcart_1(X4,X5,X6,X7,X9)
                  | k10_mcart_1(X0,X1,X2,X3,X8) != k10_mcart_1(X4,X5,X6,X7,X9)
                  | k9_mcart_1(X0,X1,X2,X3,X8) != k9_mcart_1(X4,X5,X6,X7,X9)
                  | k8_mcart_1(X0,X1,X2,X3,X8) != k8_mcart_1(X4,X5,X6,X7,X9) )
                & X8 = X9
                & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7)) )
            & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X7
        & k1_xboole_0 != X6
        & k1_xboole_0 != X5
        & k1_xboole_0 != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X8] :
          ( ? [X9] :
              ( ( k11_mcart_1(sK1,sK2,sK3,sK4,X8) != k11_mcart_1(sK5,sK6,sK7,sK8,X9)
                | k10_mcart_1(sK1,sK2,sK3,sK4,X8) != k10_mcart_1(sK5,sK6,sK7,sK8,X9)
                | k9_mcart_1(sK1,sK2,sK3,sK4,X8) != k9_mcart_1(sK5,sK6,sK7,sK8,X9)
                | k8_mcart_1(sK1,sK2,sK3,sK4,X8) != k8_mcart_1(sK5,sK6,sK7,sK8,X9) )
              & X8 = X9
              & m1_subset_1(X9,k4_zfmisc_1(sK5,sK6,sK7,sK8)) )
          & m1_subset_1(X8,k4_zfmisc_1(sK1,sK2,sK3,sK4)) )
      & k1_xboole_0 != sK8
      & k1_xboole_0 != sK7
      & k1_xboole_0 != sK6
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( ? [X8] :
        ( ? [X9] :
            ( ( k11_mcart_1(sK1,sK2,sK3,sK4,X8) != k11_mcart_1(sK5,sK6,sK7,sK8,X9)
              | k10_mcart_1(sK1,sK2,sK3,sK4,X8) != k10_mcart_1(sK5,sK6,sK7,sK8,X9)
              | k9_mcart_1(sK1,sK2,sK3,sK4,X8) != k9_mcart_1(sK5,sK6,sK7,sK8,X9)
              | k8_mcart_1(sK1,sK2,sK3,sK4,X8) != k8_mcart_1(sK5,sK6,sK7,sK8,X9) )
            & X8 = X9
            & m1_subset_1(X9,k4_zfmisc_1(sK5,sK6,sK7,sK8)) )
        & m1_subset_1(X8,k4_zfmisc_1(sK1,sK2,sK3,sK4)) )
   => ( ? [X9] :
          ( ( k11_mcart_1(sK5,sK6,sK7,sK8,X9) != k11_mcart_1(sK1,sK2,sK3,sK4,sK9)
            | k10_mcart_1(sK5,sK6,sK7,sK8,X9) != k10_mcart_1(sK1,sK2,sK3,sK4,sK9)
            | k9_mcart_1(sK5,sK6,sK7,sK8,X9) != k9_mcart_1(sK1,sK2,sK3,sK4,sK9)
            | k8_mcart_1(sK5,sK6,sK7,sK8,X9) != k8_mcart_1(sK1,sK2,sK3,sK4,sK9) )
          & sK9 = X9
          & m1_subset_1(X9,k4_zfmisc_1(sK5,sK6,sK7,sK8)) )
      & m1_subset_1(sK9,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( ? [X9] :
        ( ( k11_mcart_1(sK5,sK6,sK7,sK8,X9) != k11_mcart_1(sK1,sK2,sK3,sK4,sK9)
          | k10_mcart_1(sK5,sK6,sK7,sK8,X9) != k10_mcart_1(sK1,sK2,sK3,sK4,sK9)
          | k9_mcart_1(sK5,sK6,sK7,sK8,X9) != k9_mcart_1(sK1,sK2,sK3,sK4,sK9)
          | k8_mcart_1(sK5,sK6,sK7,sK8,X9) != k8_mcart_1(sK1,sK2,sK3,sK4,sK9) )
        & sK9 = X9
        & m1_subset_1(X9,k4_zfmisc_1(sK5,sK6,sK7,sK8)) )
   => ( ( k11_mcart_1(sK1,sK2,sK3,sK4,sK9) != k11_mcart_1(sK5,sK6,sK7,sK8,sK10)
        | k10_mcart_1(sK1,sK2,sK3,sK4,sK9) != k10_mcart_1(sK5,sK6,sK7,sK8,sK10)
        | k9_mcart_1(sK1,sK2,sK3,sK4,sK9) != k9_mcart_1(sK5,sK6,sK7,sK8,sK10)
        | k8_mcart_1(sK1,sK2,sK3,sK4,sK9) != k8_mcart_1(sK5,sK6,sK7,sK8,sK10) )
      & sK9 = sK10
      & m1_subset_1(sK10,k4_zfmisc_1(sK5,sK6,sK7,sK8)) ) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ? [X8] :
          ( ? [X9] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X8) != k11_mcart_1(X4,X5,X6,X7,X9)
                | k10_mcart_1(X0,X1,X2,X3,X8) != k10_mcart_1(X4,X5,X6,X7,X9)
                | k9_mcart_1(X0,X1,X2,X3,X8) != k9_mcart_1(X4,X5,X6,X7,X9)
                | k8_mcart_1(X0,X1,X2,X3,X8) != k8_mcart_1(X4,X5,X6,X7,X9) )
              & X8 = X9
              & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7)) )
          & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
      & k1_xboole_0 != X7
      & k1_xboole_0 != X6
      & k1_xboole_0 != X5
      & k1_xboole_0 != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ~ ( ? [X8] :
              ( ? [X9] :
                  ( ~ ( k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9)
                      & k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9)
                      & k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9)
                      & k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9) )
                  & X8 = X9
                  & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7)) )
              & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
          & k1_xboole_0 != X7
          & k1_xboole_0 != X6
          & k1_xboole_0 != X5
          & k1_xboole_0 != X4
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ~ ( ? [X8] :
            ( ? [X9] :
                ( ~ ( k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9)
                    & k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9)
                    & k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9)
                    & k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9) )
                & X8 = X9
                & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7)) )
            & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X7
        & k1_xboole_0 != X6
        & k1_xboole_0 != X5
        & k1_xboole_0 != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_mcart_1)).

fof(f97,plain,(
    ~ spl11_14 ),
    inference(avatar_split_clause,[],[f15,f94])).

fof(f15,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f11])).

fof(f92,plain,(
    ~ spl11_13 ),
    inference(avatar_split_clause,[],[f16,f89])).

fof(f16,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f11])).

fof(f87,plain,(
    ~ spl11_12 ),
    inference(avatar_split_clause,[],[f17,f84])).

fof(f17,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f11])).

fof(f82,plain,(
    ~ spl11_11 ),
    inference(avatar_split_clause,[],[f18,f79])).

fof(f18,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f11])).

fof(f77,plain,(
    ~ spl11_10 ),
    inference(avatar_split_clause,[],[f19,f74])).

fof(f19,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f11])).

fof(f72,plain,(
    ~ spl11_9 ),
    inference(avatar_split_clause,[],[f20,f69])).

fof(f20,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f11])).

fof(f67,plain,(
    ~ spl11_8 ),
    inference(avatar_split_clause,[],[f21,f64])).

fof(f21,plain,(
    k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f11])).

fof(f62,plain,(
    spl11_7 ),
    inference(avatar_split_clause,[],[f22,f59])).

fof(f22,plain,(
    m1_subset_1(sK9,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f23,f54])).

fof(f23,plain,(
    m1_subset_1(sK10,k4_zfmisc_1(sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f11])).

fof(f52,plain,(
    spl11_5 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    sK9 = sK10 ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,
    ( ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f25,f44,f40,f36,f32])).

fof(f25,plain,
    ( k11_mcart_1(sK1,sK2,sK3,sK4,sK9) != k11_mcart_1(sK5,sK6,sK7,sK8,sK10)
    | k10_mcart_1(sK1,sK2,sK3,sK4,sK9) != k10_mcart_1(sK5,sK6,sK7,sK8,sK10)
    | k9_mcart_1(sK1,sK2,sK3,sK4,sK9) != k9_mcart_1(sK5,sK6,sK7,sK8,sK10)
    | k8_mcart_1(sK1,sK2,sK3,sK4,sK9) != k8_mcart_1(sK5,sK6,sK7,sK8,sK10) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
