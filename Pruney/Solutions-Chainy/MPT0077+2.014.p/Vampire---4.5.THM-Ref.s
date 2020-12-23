%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 315 expanded)
%              Number of leaves         :   48 ( 155 expanded)
%              Depth                    :    8
%              Number of atoms          :  441 ( 771 expanded)
%              Number of equality atoms :   79 ( 144 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (26174)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f2298,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f72,f76,f85,f89,f93,f97,f107,f111,f129,f135,f149,f153,f161,f165,f251,f254,f294,f301,f306,f309,f314,f338,f343,f411,f464,f711,f716,f806,f837,f1134,f1139,f1178,f1225,f1390,f2230,f2287])).

fof(f2287,plain,
    ( ~ spl5_4
    | ~ spl5_56
    | spl5_91
    | ~ spl5_118
    | ~ spl5_173 ),
    inference(avatar_contradiction_clause,[],[f2286])).

fof(f2286,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_56
    | spl5_91
    | ~ spl5_118
    | ~ spl5_173 ),
    inference(subsumption_resolution,[],[f2285,f75])).

fof(f75,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl5_4
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f2285,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK1)
    | ~ spl5_56
    | spl5_91
    | ~ spl5_118
    | ~ spl5_173 ),
    inference(forward_demodulation,[],[f2284,f1224])).

fof(f1224,plain,
    ( sK1 = k4_xboole_0(sK1,sK3)
    | ~ spl5_118 ),
    inference(avatar_component_clause,[],[f1222])).

fof(f1222,plain,
    ( spl5_118
  <=> sK1 = k4_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f2284,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl5_56
    | spl5_91
    | ~ spl5_173 ),
    inference(backward_demodulation,[],[f836,f2283])).

fof(f2283,plain,
    ( ! [X1] : k4_xboole_0(sK1,X1) = k4_xboole_0(sK1,k2_xboole_0(sK2,X1))
    | ~ spl5_56
    | ~ spl5_173 ),
    inference(forward_demodulation,[],[f2237,f2229])).

fof(f2229,plain,
    ( ! [X15] : k4_xboole_0(sK1,X15) = k4_xboole_0(sK1,k4_xboole_0(X15,sK2))
    | ~ spl5_173 ),
    inference(avatar_component_clause,[],[f2228])).

fof(f2228,plain,
    ( spl5_173
  <=> ! [X15] : k4_xboole_0(sK1,X15) = k4_xboole_0(sK1,k4_xboole_0(X15,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_173])])).

fof(f2237,plain,
    ( ! [X1] : k4_xboole_0(sK1,k2_xboole_0(sK2,X1)) = k4_xboole_0(sK1,k4_xboole_0(X1,sK2))
    | ~ spl5_56
    | ~ spl5_173 ),
    inference(superposition,[],[f2229,f463])).

fof(f463,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f462])).

fof(f462,plain,
    ( spl5_56
  <=> ! [X1,X2] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f836,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)))
    | spl5_91 ),
    inference(avatar_component_clause,[],[f834])).

fof(f834,plain,
    ( spl5_91
  <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).

fof(f2230,plain,
    ( spl5_173
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_117
    | ~ spl5_129 ),
    inference(avatar_split_clause,[],[f1584,f1388,f1175,f74,f66,f2228])).

fof(f66,plain,
    ( spl5_2
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1175,plain,
    ( spl5_117
  <=> sK1 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_117])])).

fof(f1388,plain,
    ( spl5_129
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_129])])).

fof(f1584,plain,
    ( ! [X15] : k4_xboole_0(sK1,X15) = k4_xboole_0(sK1,k4_xboole_0(X15,sK2))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_117
    | ~ spl5_129 ),
    inference(forward_demodulation,[],[f1583,f67])).

fof(f67,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f1583,plain,
    ( ! [X15] : k4_xboole_0(sK1,k4_xboole_0(X15,sK2)) = k2_xboole_0(k4_xboole_0(sK1,X15),k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_117
    | ~ spl5_129 ),
    inference(forward_demodulation,[],[f1531,f75])).

fof(f1531,plain,
    ( ! [X15] : k4_xboole_0(sK1,k4_xboole_0(X15,sK2)) = k2_xboole_0(k4_xboole_0(sK1,X15),k4_xboole_0(sK1,sK1))
    | ~ spl5_117
    | ~ spl5_129 ),
    inference(superposition,[],[f1389,f1177])).

fof(f1177,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl5_117 ),
    inference(avatar_component_clause,[],[f1175])).

fof(f1389,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))
    | ~ spl5_129 ),
    inference(avatar_component_clause,[],[f1388])).

fof(f1390,plain,(
    spl5_129 ),
    inference(avatar_split_clause,[],[f59,f1388])).

fof(f59,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f51,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f1225,plain,
    ( spl5_118
    | ~ spl5_10
    | ~ spl5_115 ),
    inference(avatar_split_clause,[],[f1194,f1136,f105,f1222])).

fof(f105,plain,
    ( spl5_10
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f1136,plain,
    ( spl5_115
  <=> sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_115])])).

fof(f1194,plain,
    ( sK1 = k4_xboole_0(sK1,sK3)
    | ~ spl5_10
    | ~ spl5_115 ),
    inference(superposition,[],[f1138,f106])).

fof(f106,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f1138,plain,
    ( sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))
    | ~ spl5_115 ),
    inference(avatar_component_clause,[],[f1136])).

fof(f1178,plain,
    ( spl5_117
    | ~ spl5_10
    | ~ spl5_114 ),
    inference(avatar_split_clause,[],[f1140,f1131,f105,f1175])).

fof(f1131,plain,
    ( spl5_114
  <=> sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f1140,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl5_10
    | ~ spl5_114 ),
    inference(superposition,[],[f1133,f106])).

fof(f1133,plain,
    ( sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))
    | ~ spl5_114 ),
    inference(avatar_component_clause,[],[f1131])).

fof(f1139,plain,
    ( spl5_115
    | ~ spl5_74
    | ~ spl5_85 ),
    inference(avatar_split_clause,[],[f898,f804,f713,f1136])).

fof(f713,plain,
    ( spl5_74
  <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f804,plain,
    ( spl5_85
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).

fof(f898,plain,
    ( sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))
    | ~ spl5_74
    | ~ spl5_85 ),
    inference(superposition,[],[f805,f715])).

fof(f715,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl5_74 ),
    inference(avatar_component_clause,[],[f713])).

fof(f805,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0
    | ~ spl5_85 ),
    inference(avatar_component_clause,[],[f804])).

fof(f1134,plain,
    ( spl5_114
    | ~ spl5_73
    | ~ spl5_85 ),
    inference(avatar_split_clause,[],[f897,f804,f708,f1131])).

fof(f708,plain,
    ( spl5_73
  <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f897,plain,
    ( sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))
    | ~ spl5_73
    | ~ spl5_85 ),
    inference(superposition,[],[f805,f710])).

fof(f710,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl5_73 ),
    inference(avatar_component_clause,[],[f708])).

fof(f837,plain,
    ( ~ spl5_91
    | spl5_14
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f611,f341,f126,f834])).

fof(f126,plain,
    ( spl5_14
  <=> r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f341,plain,
    ( spl5_36
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f611,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)))
    | spl5_14
    | ~ spl5_36 ),
    inference(resolution,[],[f342,f127])).

fof(f127,plain,
    ( ~ r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f126])).

fof(f342,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f341])).

fof(f806,plain,(
    spl5_85 ),
    inference(avatar_split_clause,[],[f54,f804])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f45,f42])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f716,plain,
    ( spl5_74
    | ~ spl5_17
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f696,f409,f146,f713])).

fof(f146,plain,
    ( spl5_17
  <=> r1_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f409,plain,
    ( spl5_48
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f696,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl5_17
    | ~ spl5_48 ),
    inference(resolution,[],[f410,f147])).

fof(f147,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f146])).

fof(f410,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f409])).

fof(f711,plain,
    ( spl5_73
    | ~ spl5_16
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f695,f409,f142,f708])).

fof(f142,plain,
    ( spl5_16
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

% (26185)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f695,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl5_16
    | ~ spl5_48 ),
    inference(resolution,[],[f410,f143])).

fof(f143,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f142])).

fof(f464,plain,
    ( spl5_56
    | ~ spl5_9
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f204,f159,f95,f462])).

fof(f95,plain,
    ( spl5_9
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f159,plain,
    ( spl5_20
  <=> ! [X1,X0] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f204,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)
    | ~ spl5_9
    | ~ spl5_20 ),
    inference(superposition,[],[f160,f96])).

fof(f96,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f160,plain,
    ( ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f159])).

fof(f411,plain,(
    spl5_48 ),
    inference(avatar_split_clause,[],[f58,f409])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f42])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f343,plain,(
    spl5_36 ),
    inference(avatar_split_clause,[],[f57,f341])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f50,f42])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f338,plain,
    ( ~ spl5_14
    | ~ spl5_13
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f331,f151,f122,f126])).

fof(f122,plain,
    ( spl5_13
  <=> sP0(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f151,plain,
    ( spl5_18
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X0))
        | ~ sP0(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f331,plain,
    ( ~ r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | ~ spl5_13
    | ~ spl5_18 ),
    inference(resolution,[],[f124,f152])).

fof(f152,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP0(X0,X1,X2)
        | ~ r1_xboole_0(X1,k2_xboole_0(X2,X0)) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f151])).

fof(f124,plain,
    ( sP0(sK3,sK1,sK2)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f122])).

fof(f314,plain,
    ( spl5_17
    | ~ spl5_6
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f311,f258,f83,f146])).

fof(f83,plain,
    ( spl5_6
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f258,plain,
    ( spl5_28
  <=> r1_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f311,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl5_6
    | ~ spl5_28 ),
    inference(resolution,[],[f260,f84])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f260,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f258])).

fof(f309,plain,
    ( spl5_28
    | ~ spl5_11
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f296,f292,f109,f258])).

fof(f109,plain,
    ( spl5_11
  <=> ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f292,plain,
    ( spl5_33
  <=> ! [X0] :
        ( r1_xboole_0(X0,sK1)
        | ~ r1_tarski(X0,k2_xboole_0(sK2,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f296,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ spl5_11
    | ~ spl5_33 ),
    inference(resolution,[],[f293,f110])).

fof(f110,plain,
    ( ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f109])).

fof(f293,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_xboole_0(sK2,sK3))
        | r1_xboole_0(X0,sK1) )
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f292])).

fof(f306,plain,
    ( spl5_16
    | ~ spl5_6
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f303,f263,f83,f142])).

fof(f263,plain,
    ( spl5_29
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f303,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_6
    | ~ spl5_29 ),
    inference(resolution,[],[f265,f84])).

fof(f265,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f263])).

fof(f301,plain,
    ( spl5_29
    | ~ spl5_3
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f295,f292,f70,f263])).

fof(f70,plain,
    ( spl5_3
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f295,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl5_3
    | ~ spl5_33 ),
    inference(resolution,[],[f293,f71])).

fof(f71,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f294,plain,
    ( spl5_33
    | ~ spl5_15
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f269,f163,f132,f292])).

fof(f132,plain,
    ( spl5_15
  <=> r1_xboole_0(k2_xboole_0(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f163,plain,
    ( spl5_21
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f269,plain,
    ( ! [X0] :
        ( r1_xboole_0(X0,sK1)
        | ~ r1_tarski(X0,k2_xboole_0(sK2,sK3)) )
    | ~ spl5_15
    | ~ spl5_21 ),
    inference(resolution,[],[f134,f164])).

fof(f164,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f163])).

fof(f134,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK3),sK1)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f132])).

fof(f254,plain,
    ( spl5_16
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f248,f122,f87,f142])).

fof(f87,plain,
    ( spl5_7
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X1,X2)
        | ~ sP0(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f248,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(resolution,[],[f124,f88])).

fof(f88,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP0(X0,X1,X2)
        | r1_xboole_0(X1,X2) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f251,plain,
    ( spl5_17
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f247,f122,f91,f146])).

fof(f91,plain,
    ( spl5_8
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X1,X0)
        | ~ sP0(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f247,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(resolution,[],[f124,f92])).

fof(f92,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP0(X0,X1,X2)
        | r1_xboole_0(X1,X0) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f165,plain,(
    spl5_21 ),
    inference(avatar_split_clause,[],[f52,f163])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f161,plain,(
    spl5_20 ),
    inference(avatar_split_clause,[],[f44,f159])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f153,plain,(
    spl5_18 ),
    inference(avatar_split_clause,[],[f32,f151])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X0)
        & r1_xboole_0(X1,X2)
        & ~ r1_xboole_0(X1,k2_xboole_0(X2,X0)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) )
      | ~ sP0(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) )
      | ~ sP0(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f149,plain,
    ( spl5_13
    | ~ spl5_16
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f35,f146,f142,f122])).

fof(f35,plain,
    ( ~ r1_xboole_0(sK1,sK3)
    | ~ r1_xboole_0(sK1,sK2)
    | sP0(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
      & ( ~ r1_xboole_0(sK1,sK3)
        | ~ r1_xboole_0(sK1,sK2) ) )
    | sP0(sK3,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | sP0(X2,X0,X1) )
   => ( ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
        & ( ~ r1_xboole_0(sK1,sK3)
          | ~ r1_xboole_0(sK1,sK2) ) )
      | sP0(sK3,sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | sP0(X2,X0,X1) ) ),
    inference(definition_folding,[],[f18,f23])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f135,plain,
    ( spl5_15
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f130,f126,f83,f132])).

fof(f130,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK3),sK1)
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(resolution,[],[f128,f84])).

fof(f128,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f126])).

fof(f129,plain,
    ( spl5_13
    | spl5_14 ),
    inference(avatar_split_clause,[],[f36,f126,f122])).

fof(f36,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | sP0(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f111,plain,
    ( spl5_11
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f101,f95,f70,f109])).

fof(f101,plain,
    ( ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1))
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(superposition,[],[f71,f96])).

fof(f107,plain,
    ( spl5_10
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f98,f95,f66,f105])).

fof(f98,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(superposition,[],[f96,f67])).

fof(f97,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f41,f95])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f93,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f34,f91])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f89,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f33,f87])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f85,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f48,f83])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f76,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f60,f74])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f53,f38])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f37,f42])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f72,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f40,f70])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f68,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f39,f66])).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n012.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:39:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.42  % (26172)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (26179)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (26181)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (26176)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (26173)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (26180)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (26182)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (26179)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  % (26174)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  fof(f2298,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f68,f72,f76,f85,f89,f93,f97,f107,f111,f129,f135,f149,f153,f161,f165,f251,f254,f294,f301,f306,f309,f314,f338,f343,f411,f464,f711,f716,f806,f837,f1134,f1139,f1178,f1225,f1390,f2230,f2287])).
% 0.21/0.51  fof(f2287,plain,(
% 0.21/0.51    ~spl5_4 | ~spl5_56 | spl5_91 | ~spl5_118 | ~spl5_173),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f2286])).
% 0.21/0.51  fof(f2286,plain,(
% 0.21/0.51    $false | (~spl5_4 | ~spl5_56 | spl5_91 | ~spl5_118 | ~spl5_173)),
% 0.21/0.51    inference(subsumption_resolution,[],[f2285,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl5_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    spl5_4 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.51  fof(f2285,plain,(
% 0.21/0.51    k1_xboole_0 != k4_xboole_0(sK1,sK1) | (~spl5_56 | spl5_91 | ~spl5_118 | ~spl5_173)),
% 0.21/0.51    inference(forward_demodulation,[],[f2284,f1224])).
% 0.21/0.51  fof(f1224,plain,(
% 0.21/0.51    sK1 = k4_xboole_0(sK1,sK3) | ~spl5_118),
% 0.21/0.51    inference(avatar_component_clause,[],[f1222])).
% 0.21/0.51  fof(f1222,plain,(
% 0.21/0.51    spl5_118 <=> sK1 = k4_xboole_0(sK1,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).
% 0.21/0.51  fof(f2284,plain,(
% 0.21/0.51    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | (~spl5_56 | spl5_91 | ~spl5_173)),
% 0.21/0.51    inference(backward_demodulation,[],[f836,f2283])).
% 0.21/0.51  fof(f2283,plain,(
% 0.21/0.51    ( ! [X1] : (k4_xboole_0(sK1,X1) = k4_xboole_0(sK1,k2_xboole_0(sK2,X1))) ) | (~spl5_56 | ~spl5_173)),
% 0.21/0.51    inference(forward_demodulation,[],[f2237,f2229])).
% 0.21/0.51  fof(f2229,plain,(
% 0.21/0.51    ( ! [X15] : (k4_xboole_0(sK1,X15) = k4_xboole_0(sK1,k4_xboole_0(X15,sK2))) ) | ~spl5_173),
% 0.21/0.51    inference(avatar_component_clause,[],[f2228])).
% 0.21/0.51  fof(f2228,plain,(
% 0.21/0.51    spl5_173 <=> ! [X15] : k4_xboole_0(sK1,X15) = k4_xboole_0(sK1,k4_xboole_0(X15,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_173])])).
% 0.21/0.51  fof(f2237,plain,(
% 0.21/0.51    ( ! [X1] : (k4_xboole_0(sK1,k2_xboole_0(sK2,X1)) = k4_xboole_0(sK1,k4_xboole_0(X1,sK2))) ) | (~spl5_56 | ~spl5_173)),
% 0.21/0.51    inference(superposition,[],[f2229,f463])).
% 0.21/0.51  fof(f463,plain,(
% 0.21/0.51    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) ) | ~spl5_56),
% 0.21/0.51    inference(avatar_component_clause,[],[f462])).
% 0.21/0.51  fof(f462,plain,(
% 0.21/0.51    spl5_56 <=> ! [X1,X2] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).
% 0.21/0.51  fof(f836,plain,(
% 0.21/0.51    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) | spl5_91),
% 0.21/0.51    inference(avatar_component_clause,[],[f834])).
% 0.21/0.51  fof(f834,plain,(
% 0.21/0.51    spl5_91 <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).
% 0.21/0.51  fof(f2230,plain,(
% 0.21/0.51    spl5_173 | ~spl5_2 | ~spl5_4 | ~spl5_117 | ~spl5_129),
% 0.21/0.51    inference(avatar_split_clause,[],[f1584,f1388,f1175,f74,f66,f2228])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    spl5_2 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.51  fof(f1175,plain,(
% 0.21/0.51    spl5_117 <=> sK1 = k4_xboole_0(sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_117])])).
% 0.21/0.51  fof(f1388,plain,(
% 0.21/0.51    spl5_129 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_129])])).
% 0.21/0.51  fof(f1584,plain,(
% 0.21/0.51    ( ! [X15] : (k4_xboole_0(sK1,X15) = k4_xboole_0(sK1,k4_xboole_0(X15,sK2))) ) | (~spl5_2 | ~spl5_4 | ~spl5_117 | ~spl5_129)),
% 0.21/0.51    inference(forward_demodulation,[],[f1583,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl5_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f66])).
% 0.21/0.51  fof(f1583,plain,(
% 0.21/0.51    ( ! [X15] : (k4_xboole_0(sK1,k4_xboole_0(X15,sK2)) = k2_xboole_0(k4_xboole_0(sK1,X15),k1_xboole_0)) ) | (~spl5_4 | ~spl5_117 | ~spl5_129)),
% 0.21/0.51    inference(forward_demodulation,[],[f1531,f75])).
% 0.21/0.51  fof(f1531,plain,(
% 0.21/0.51    ( ! [X15] : (k4_xboole_0(sK1,k4_xboole_0(X15,sK2)) = k2_xboole_0(k4_xboole_0(sK1,X15),k4_xboole_0(sK1,sK1))) ) | (~spl5_117 | ~spl5_129)),
% 0.21/0.51    inference(superposition,[],[f1389,f1177])).
% 0.21/0.51  fof(f1177,plain,(
% 0.21/0.51    sK1 = k4_xboole_0(sK1,sK2) | ~spl5_117),
% 0.21/0.51    inference(avatar_component_clause,[],[f1175])).
% 0.21/0.51  fof(f1389,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ) | ~spl5_129),
% 0.21/0.51    inference(avatar_component_clause,[],[f1388])).
% 0.21/0.51  fof(f1390,plain,(
% 0.21/0.51    spl5_129),
% 0.21/0.51    inference(avatar_split_clause,[],[f59,f1388])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f51,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.21/0.51  fof(f1225,plain,(
% 0.21/0.51    spl5_118 | ~spl5_10 | ~spl5_115),
% 0.21/0.51    inference(avatar_split_clause,[],[f1194,f1136,f105,f1222])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl5_10 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.51  fof(f1136,plain,(
% 0.21/0.51    spl5_115 <=> sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_115])])).
% 0.21/0.51  fof(f1194,plain,(
% 0.21/0.51    sK1 = k4_xboole_0(sK1,sK3) | (~spl5_10 | ~spl5_115)),
% 0.21/0.51    inference(superposition,[],[f1138,f106])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl5_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f105])).
% 0.21/0.51  fof(f1138,plain,(
% 0.21/0.51    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) | ~spl5_115),
% 0.21/0.51    inference(avatar_component_clause,[],[f1136])).
% 0.21/0.51  fof(f1178,plain,(
% 0.21/0.51    spl5_117 | ~spl5_10 | ~spl5_114),
% 0.21/0.51    inference(avatar_split_clause,[],[f1140,f1131,f105,f1175])).
% 0.21/0.51  fof(f1131,plain,(
% 0.21/0.51    spl5_114 <=> sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).
% 0.21/0.51  fof(f1140,plain,(
% 0.21/0.51    sK1 = k4_xboole_0(sK1,sK2) | (~spl5_10 | ~spl5_114)),
% 0.21/0.51    inference(superposition,[],[f1133,f106])).
% 0.21/0.51  fof(f1133,plain,(
% 0.21/0.51    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) | ~spl5_114),
% 0.21/0.51    inference(avatar_component_clause,[],[f1131])).
% 0.21/0.51  fof(f1139,plain,(
% 0.21/0.51    spl5_115 | ~spl5_74 | ~spl5_85),
% 0.21/0.51    inference(avatar_split_clause,[],[f898,f804,f713,f1136])).
% 0.21/0.51  fof(f713,plain,(
% 0.21/0.51    spl5_74 <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).
% 0.21/0.51  fof(f804,plain,(
% 0.21/0.51    spl5_85 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).
% 0.21/0.51  fof(f898,plain,(
% 0.21/0.51    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) | (~spl5_74 | ~spl5_85)),
% 0.21/0.51    inference(superposition,[],[f805,f715])).
% 0.21/0.51  fof(f715,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | ~spl5_74),
% 0.21/0.51    inference(avatar_component_clause,[],[f713])).
% 0.21/0.51  fof(f805,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) ) | ~spl5_85),
% 0.21/0.51    inference(avatar_component_clause,[],[f804])).
% 0.21/0.51  fof(f1134,plain,(
% 0.21/0.51    spl5_114 | ~spl5_73 | ~spl5_85),
% 0.21/0.51    inference(avatar_split_clause,[],[f897,f804,f708,f1131])).
% 0.21/0.51  fof(f708,plain,(
% 0.21/0.51    spl5_73 <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).
% 0.21/0.51  fof(f897,plain,(
% 0.21/0.51    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) | (~spl5_73 | ~spl5_85)),
% 0.21/0.51    inference(superposition,[],[f805,f710])).
% 0.21/0.51  fof(f710,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | ~spl5_73),
% 0.21/0.51    inference(avatar_component_clause,[],[f708])).
% 0.21/0.51  fof(f837,plain,(
% 0.21/0.51    ~spl5_91 | spl5_14 | ~spl5_36),
% 0.21/0.51    inference(avatar_split_clause,[],[f611,f341,f126,f834])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    spl5_14 <=> r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.51  fof(f341,plain,(
% 0.21/0.51    spl5_36 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.21/0.51  fof(f611,plain,(
% 0.21/0.51    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) | (spl5_14 | ~spl5_36)),
% 0.21/0.51    inference(resolution,[],[f342,f127])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ~r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | spl5_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f126])).
% 0.21/0.51  fof(f342,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl5_36),
% 0.21/0.51    inference(avatar_component_clause,[],[f341])).
% 0.21/0.51  fof(f806,plain,(
% 0.21/0.51    spl5_85),
% 0.21/0.51    inference(avatar_split_clause,[],[f54,f804])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.51    inference(definition_unfolding,[],[f45,f42])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.51  fof(f716,plain,(
% 0.21/0.51    spl5_74 | ~spl5_17 | ~spl5_48),
% 0.21/0.51    inference(avatar_split_clause,[],[f696,f409,f146,f713])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    spl5_17 <=> r1_xboole_0(sK1,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.51  fof(f409,plain,(
% 0.21/0.51    spl5_48 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 0.21/0.51  fof(f696,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | (~spl5_17 | ~spl5_48)),
% 0.21/0.51    inference(resolution,[],[f410,f147])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    r1_xboole_0(sK1,sK3) | ~spl5_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f146])).
% 0.21/0.51  fof(f410,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl5_48),
% 0.21/0.51    inference(avatar_component_clause,[],[f409])).
% 0.21/0.51  fof(f711,plain,(
% 0.21/0.51    spl5_73 | ~spl5_16 | ~spl5_48),
% 0.21/0.51    inference(avatar_split_clause,[],[f695,f409,f142,f708])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    spl5_16 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.51  % (26185)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  fof(f695,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | (~spl5_16 | ~spl5_48)),
% 0.21/0.51    inference(resolution,[],[f410,f143])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    r1_xboole_0(sK1,sK2) | ~spl5_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f142])).
% 0.21/0.51  fof(f464,plain,(
% 0.21/0.51    spl5_56 | ~spl5_9 | ~spl5_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f204,f159,f95,f462])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl5_9 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    spl5_20 <=> ! [X1,X0] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) ) | (~spl5_9 | ~spl5_20)),
% 0.21/0.51    inference(superposition,[],[f160,f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl5_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f95])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) ) | ~spl5_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f159])).
% 0.21/0.51  fof(f411,plain,(
% 0.21/0.51    spl5_48),
% 0.21/0.51    inference(avatar_split_clause,[],[f58,f409])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f49,f42])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.51  fof(f343,plain,(
% 0.21/0.51    spl5_36),
% 0.21/0.51    inference(avatar_split_clause,[],[f57,f341])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f50,f42])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f338,plain,(
% 0.21/0.51    ~spl5_14 | ~spl5_13 | ~spl5_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f331,f151,f122,f126])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    spl5_13 <=> sP0(sK3,sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    spl5_18 <=> ! [X1,X0,X2] : (~r1_xboole_0(X1,k2_xboole_0(X2,X0)) | ~sP0(X0,X1,X2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.51  fof(f331,plain,(
% 0.21/0.51    ~r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | (~spl5_13 | ~spl5_18)),
% 0.21/0.51    inference(resolution,[],[f124,f152])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~r1_xboole_0(X1,k2_xboole_0(X2,X0))) ) | ~spl5_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f151])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    sP0(sK3,sK1,sK2) | ~spl5_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f122])).
% 0.21/0.51  fof(f314,plain,(
% 0.21/0.51    spl5_17 | ~spl5_6 | ~spl5_28),
% 0.21/0.51    inference(avatar_split_clause,[],[f311,f258,f83,f146])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl5_6 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.51  fof(f258,plain,(
% 0.21/0.51    spl5_28 <=> r1_xboole_0(sK3,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.21/0.51  fof(f311,plain,(
% 0.21/0.51    r1_xboole_0(sK1,sK3) | (~spl5_6 | ~spl5_28)),
% 0.21/0.51    inference(resolution,[],[f260,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl5_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f83])).
% 0.21/0.51  fof(f260,plain,(
% 0.21/0.51    r1_xboole_0(sK3,sK1) | ~spl5_28),
% 0.21/0.51    inference(avatar_component_clause,[],[f258])).
% 0.21/0.51  fof(f309,plain,(
% 0.21/0.51    spl5_28 | ~spl5_11 | ~spl5_33),
% 0.21/0.51    inference(avatar_split_clause,[],[f296,f292,f109,f258])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl5_11 <=> ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X2,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.51  fof(f292,plain,(
% 0.21/0.51    spl5_33 <=> ! [X0] : (r1_xboole_0(X0,sK1) | ~r1_tarski(X0,k2_xboole_0(sK2,sK3)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.21/0.51  fof(f296,plain,(
% 0.21/0.51    r1_xboole_0(sK3,sK1) | (~spl5_11 | ~spl5_33)),
% 0.21/0.51    inference(resolution,[],[f293,f110])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) ) | ~spl5_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f109])).
% 0.21/0.51  fof(f293,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK2,sK3)) | r1_xboole_0(X0,sK1)) ) | ~spl5_33),
% 0.21/0.51    inference(avatar_component_clause,[],[f292])).
% 0.21/0.51  fof(f306,plain,(
% 0.21/0.51    spl5_16 | ~spl5_6 | ~spl5_29),
% 0.21/0.51    inference(avatar_split_clause,[],[f303,f263,f83,f142])).
% 0.21/0.51  fof(f263,plain,(
% 0.21/0.51    spl5_29 <=> r1_xboole_0(sK2,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.21/0.51  fof(f303,plain,(
% 0.21/0.51    r1_xboole_0(sK1,sK2) | (~spl5_6 | ~spl5_29)),
% 0.21/0.51    inference(resolution,[],[f265,f84])).
% 0.21/0.51  fof(f265,plain,(
% 0.21/0.51    r1_xboole_0(sK2,sK1) | ~spl5_29),
% 0.21/0.51    inference(avatar_component_clause,[],[f263])).
% 0.21/0.51  fof(f301,plain,(
% 0.21/0.51    spl5_29 | ~spl5_3 | ~spl5_33),
% 0.21/0.51    inference(avatar_split_clause,[],[f295,f292,f70,f263])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    spl5_3 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.51  fof(f295,plain,(
% 0.21/0.51    r1_xboole_0(sK2,sK1) | (~spl5_3 | ~spl5_33)),
% 0.21/0.51    inference(resolution,[],[f293,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl5_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f70])).
% 0.21/0.51  fof(f294,plain,(
% 0.21/0.51    spl5_33 | ~spl5_15 | ~spl5_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f269,f163,f132,f292])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    spl5_15 <=> r1_xboole_0(k2_xboole_0(sK2,sK3),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    spl5_21 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.51  fof(f269,plain,(
% 0.21/0.51    ( ! [X0] : (r1_xboole_0(X0,sK1) | ~r1_tarski(X0,k2_xboole_0(sK2,sK3))) ) | (~spl5_15 | ~spl5_21)),
% 0.21/0.51    inference(resolution,[],[f134,f164])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl5_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f163])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    r1_xboole_0(k2_xboole_0(sK2,sK3),sK1) | ~spl5_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f132])).
% 0.21/0.51  fof(f254,plain,(
% 0.21/0.51    spl5_16 | ~spl5_7 | ~spl5_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f248,f122,f87,f142])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    spl5_7 <=> ! [X1,X0,X2] : (r1_xboole_0(X1,X2) | ~sP0(X0,X1,X2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.51  fof(f248,plain,(
% 0.21/0.51    r1_xboole_0(sK1,sK2) | (~spl5_7 | ~spl5_13)),
% 0.21/0.51    inference(resolution,[],[f124,f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r1_xboole_0(X1,X2)) ) | ~spl5_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f87])).
% 0.21/0.51  fof(f251,plain,(
% 0.21/0.51    spl5_17 | ~spl5_8 | ~spl5_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f247,f122,f91,f146])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    spl5_8 <=> ! [X1,X0,X2] : (r1_xboole_0(X1,X0) | ~sP0(X0,X1,X2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    r1_xboole_0(sK1,sK3) | (~spl5_8 | ~spl5_13)),
% 0.21/0.51    inference(resolution,[],[f124,f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r1_xboole_0(X1,X0)) ) | ~spl5_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f91])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    spl5_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f52,f163])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    spl5_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f44,f159])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    spl5_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f151])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,k2_xboole_0(X2,X0)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r1_xboole_0(X1,X0) & r1_xboole_0(X1,X2) & ~r1_xboole_0(X1,k2_xboole_0(X2,X0))) | ~sP0(X0,X1,X2))),
% 0.21/0.51    inference(rectify,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X2,X0,X1] : ((r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))) | ~sP0(X2,X0,X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X2,X0,X1] : ((r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))) | ~sP0(X2,X0,X1))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    spl5_13 | ~spl5_16 | ~spl5_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f35,f146,f142,f122])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ~r1_xboole_0(sK1,sK3) | ~r1_xboole_0(sK1,sK2) | sP0(sK3,sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    (r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) & (~r1_xboole_0(sK1,sK3) | ~r1_xboole_0(sK1,sK2))) | sP0(sK3,sK1,sK2)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | sP0(X2,X0,X1)) => ((r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) & (~r1_xboole_0(sK1,sK3) | ~r1_xboole_0(sK1,sK2))) | sP0(sK3,sK1,sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | sP0(X2,X0,X1))),
% 0.21/0.51    inference(definition_folding,[],[f18,f23])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.51    inference(negated_conjecture,[],[f15])).
% 0.21/0.51  fof(f15,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    spl5_15 | ~spl5_6 | ~spl5_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f130,f126,f83,f132])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    r1_xboole_0(k2_xboole_0(sK2,sK3),sK1) | (~spl5_6 | ~spl5_14)),
% 0.21/0.51    inference(resolution,[],[f128,f84])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | ~spl5_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f126])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    spl5_13 | spl5_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f36,f126,f122])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | sP0(sK3,sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    spl5_11 | ~spl5_3 | ~spl5_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f101,f95,f70,f109])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) ) | (~spl5_3 | ~spl5_9)),
% 0.21/0.51    inference(superposition,[],[f71,f96])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    spl5_10 | ~spl5_2 | ~spl5_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f98,f95,f66,f105])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl5_2 | ~spl5_9)),
% 0.21/0.51    inference(superposition,[],[f96,f67])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    spl5_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f41,f95])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    spl5_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f34,f91])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_xboole_0(X1,X0) | ~sP0(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    spl5_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f33,f87])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_xboole_0(X1,X2) | ~sP0(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    spl5_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f83])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    spl5_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f60,f74])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.51    inference(backward_demodulation,[],[f53,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f37,f42])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    spl5_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f40,f70])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f39,f66])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (26179)------------------------------
% 0.21/0.51  % (26179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26179)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (26179)Memory used [KB]: 7547
% 0.21/0.51  % (26179)Time elapsed: 0.080 s
% 0.21/0.51  % (26179)------------------------------
% 0.21/0.51  % (26179)------------------------------
% 0.21/0.51  % (26171)Success in time 0.147 s
%------------------------------------------------------------------------------
