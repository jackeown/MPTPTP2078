%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:54 EST 2020

% Result     : Theorem 3.92s
% Output     : Refutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :  310 (1075 expanded)
%              Number of leaves         :   74 ( 458 expanded)
%              Depth                    :    9
%              Number of atoms          :  665 (1787 expanded)
%              Number of equality atoms :  241 (1026 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3265,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f39,f44,f53,f58,f74,f79,f93,f98,f111,f116,f123,f156,f166,f193,f222,f227,f273,f278,f362,f386,f492,f567,f701,f706,f711,f747,f800,f805,f825,f830,f835,f840,f845,f850,f855,f1038,f1271,f1335,f1352,f1357,f1362,f1493,f1543,f1548,f1675,f1680,f1734,f1839,f1844,f1849,f1854,f1859,f2091,f2096,f2221,f2226,f2231,f2236,f2241,f2330,f2541,f2546,f2551,f3232,f3248,f3254])).

fof(f3254,plain,
    ( spl4_3
    | ~ spl4_66 ),
    inference(avatar_contradiction_clause,[],[f3253])).

fof(f3253,plain,
    ( $false
    | spl4_3
    | ~ spl4_66 ),
    inference(subsumption_resolution,[],[f3252,f38])).

fof(f38,plain,
    ( sK1 != sK2
    | spl4_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl4_3
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f3252,plain,
    ( sK1 = sK2
    | ~ spl4_66 ),
    inference(forward_demodulation,[],[f3235,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f3235,plain,
    ( sK2 = k2_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2))
    | ~ spl4_66 ),
    inference(superposition,[],[f80,f3231])).

fof(f3231,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK1)
    | ~ spl4_66 ),
    inference(avatar_component_clause,[],[f3229])).

fof(f3229,plain,
    ( spl4_66
  <=> k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[],[f22,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f3248,plain,
    ( spl4_3
    | ~ spl4_66 ),
    inference(avatar_contradiction_clause,[],[f3247])).

fof(f3247,plain,
    ( $false
    | spl4_3
    | ~ spl4_66 ),
    inference(subsumption_resolution,[],[f3246,f38])).

fof(f3246,plain,
    ( sK1 = sK2
    | ~ spl4_66 ),
    inference(forward_demodulation,[],[f3233,f80])).

fof(f3233,plain,
    ( sK2 = k2_xboole_0(k3_xboole_0(sK2,sK1),k4_xboole_0(sK1,sK2))
    | ~ spl4_66 ),
    inference(superposition,[],[f22,f3231])).

fof(f3232,plain,
    ( spl4_66
    | ~ spl4_38
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f3199,f1672,f1035,f3229])).

fof(f1035,plain,
    ( spl4_38
  <=> k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f1672,plain,
    ( spl4_47
  <=> k4_xboole_0(k4_xboole_0(sK2,sK0),sK1) = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f3199,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK1)
    | ~ spl4_38
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f3184,f1037])).

fof(f1037,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f1035])).

fof(f3184,plain,
    ( k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl4_47 ),
    inference(superposition,[],[f1674,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1674,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK0),sK1) = k4_xboole_0(sK2,sK1)
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f1672])).

fof(f2551,plain,
    ( spl4_65
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f1250,f852,f2548])).

fof(f2548,plain,
    ( spl4_65
  <=> k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK3,k2_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f852,plain,
    ( spl4_37
  <=> k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(k4_xboole_0(sK3,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f1250,plain,
    ( k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK3,k2_xboole_0(sK1,sK3))
    | ~ spl4_37 ),
    inference(superposition,[],[f854,f24])).

fof(f854,plain,
    ( k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(k4_xboole_0(sK3,sK1),sK3)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f852])).

fof(f2546,plain,
    ( spl4_64
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f1232,f842,f2543])).

fof(f2543,plain,
    ( spl4_64
  <=> k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f842,plain,
    ( spl4_35
  <=> k4_xboole_0(sK2,sK3) = k4_xboole_0(k4_xboole_0(sK2,sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f1232,plain,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK3))
    | ~ spl4_35 ),
    inference(superposition,[],[f844,f24])).

fof(f844,plain,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(k4_xboole_0(sK2,sK0),sK3)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f842])).

fof(f2541,plain,
    ( spl4_63
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f1220,f837,f2538])).

fof(f2538,plain,
    ( spl4_63
  <=> k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k2_xboole_0(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f837,plain,
    ( spl4_34
  <=> k4_xboole_0(sK1,sK3) = k4_xboole_0(k4_xboole_0(sK1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f1220,plain,
    ( k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k2_xboole_0(sK3,sK3))
    | ~ spl4_34 ),
    inference(superposition,[],[f839,f24])).

fof(f839,plain,
    ( k4_xboole_0(sK1,sK3) = k4_xboole_0(k4_xboole_0(sK1,sK3),sK3)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f837])).

fof(f2330,plain,
    ( spl4_62
    | ~ spl4_22
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f2139,f2093,f383,f2327])).

fof(f2327,plain,
    ( spl4_62
  <=> k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(k4_xboole_0(sK3,k1_xboole_0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f383,plain,
    ( spl4_22
  <=> k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f2093,plain,
    ( spl4_56
  <=> sK3 = k2_xboole_0(k4_xboole_0(sK3,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f2139,plain,
    ( k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(k4_xboole_0(sK3,k1_xboole_0),sK3)
    | ~ spl4_22
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f2124,f385])).

fof(f385,plain,
    ( k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK3,sK3)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f383])).

fof(f2124,plain,
    ( k4_xboole_0(sK3,sK3) = k4_xboole_0(k4_xboole_0(sK3,k1_xboole_0),sK3)
    | ~ spl4_56 ),
    inference(superposition,[],[f329,f2095])).

fof(f2095,plain,
    ( sK3 = k2_xboole_0(k4_xboole_0(sK3,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK3))
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f2093])).

fof(f329,plain,(
    ! [X10,X11,X9] : k4_xboole_0(X11,X10) = k4_xboole_0(k2_xboole_0(X11,k3_xboole_0(X9,X10)),X10) ),
    inference(superposition,[],[f104,f80])).

fof(f104,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f101,f24])).

fof(f101,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f24,f21])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f2241,plain,
    ( spl4_61
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f2125,f2093,f2238])).

fof(f2238,plain,
    ( spl4_61
  <=> k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK3,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f2125,plain,
    ( k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK3,k1_xboole_0),k1_xboole_0)
    | ~ spl4_56 ),
    inference(superposition,[],[f328,f2095])).

fof(f328,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X8,X6) = k4_xboole_0(k2_xboole_0(X8,k3_xboole_0(X6,X7)),X6) ),
    inference(superposition,[],[f104,f22])).

fof(f2236,plain,
    ( spl4_60
    | ~ spl4_21
    | ~ spl4_55 ),
    inference(avatar_split_clause,[],[f2114,f2088,f359,f2233])).

fof(f2233,plain,
    ( spl4_60
  <=> k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f359,plain,
    ( spl4_21
  <=> k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f2088,plain,
    ( spl4_55
  <=> sK2 = k2_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f2114,plain,
    ( k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2)
    | ~ spl4_21
    | ~ spl4_55 ),
    inference(forward_demodulation,[],[f2099,f361])).

fof(f361,plain,
    ( k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK2,sK2)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f359])).

fof(f2099,plain,
    ( k4_xboole_0(sK2,sK2) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2)
    | ~ spl4_55 ),
    inference(superposition,[],[f329,f2090])).

fof(f2090,plain,
    ( sK2 = k2_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK2))
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f2088])).

fof(f2231,plain,
    ( spl4_59
    | ~ spl4_55 ),
    inference(avatar_split_clause,[],[f2100,f2088,f2228])).

fof(f2228,plain,
    ( spl4_59
  <=> k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f2100,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0)
    | ~ spl4_55 ),
    inference(superposition,[],[f328,f2090])).

fof(f2226,plain,
    ( spl4_58
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f1981,f224,f113,f2223])).

fof(f2223,plain,
    ( spl4_58
  <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f113,plain,
    ( spl4_12
  <=> sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f224,plain,
    ( spl4_18
  <=> k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) = k4_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f1981,plain,
    ( sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK1))
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f1980,f115])).

fof(f115,plain,
    ( sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f113])).

fof(f1980,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k3_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))))
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f1896,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1896,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k3_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0)))
    | ~ spl4_18 ),
    inference(superposition,[],[f246,f226])).

fof(f226,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f224])).

fof(f246,plain,(
    ! [X2,X3] : k2_xboole_0(X3,X2) = k2_xboole_0(k4_xboole_0(X3,X2),k3_xboole_0(X2,k2_xboole_0(X3,X2))) ),
    inference(superposition,[],[f87,f20])).

fof(f87,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X1,k2_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f85,f19])).

fof(f85,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f22,f21])).

fof(f2221,plain,
    ( spl4_57
    | ~ spl4_11
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f1979,f219,f108,f2218])).

fof(f2218,plain,
    ( spl4_57
  <=> sK0 = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f108,plain,
    ( spl4_11
  <=> sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f219,plain,
    ( spl4_17
  <=> k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = k4_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f1979,plain,
    ( sK0 = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK0))
    | ~ spl4_11
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f1978,f110])).

fof(f110,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f1978,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2))))
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f1895,f20])).

fof(f1895,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)))
    | ~ spl4_17 ),
    inference(superposition,[],[f246,f221])).

fof(f221,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f219])).

fof(f2096,plain,
    ( spl4_56
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f1985,f190,f95,f2093])).

fof(f95,plain,
    ( spl4_10
  <=> sK3 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f190,plain,
    ( spl4_16
  <=> k4_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) = k4_xboole_0(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f1985,plain,
    ( sK3 = k2_xboole_0(k4_xboole_0(sK3,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK3))
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f1984,f97])).

fof(f97,plain,
    ( sK3 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f95])).

fof(f1984,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) = k2_xboole_0(k4_xboole_0(sK3,k1_xboole_0),k3_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1))))
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f1898,f20])).

fof(f1898,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK3,k1_xboole_0),k3_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0)))
    | ~ spl4_16 ),
    inference(superposition,[],[f246,f192])).

fof(f192,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) = k4_xboole_0(sK3,k1_xboole_0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f190])).

fof(f2091,plain,
    ( spl4_55
    | ~ spl4_9
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f1983,f163,f90,f2088])).

fof(f90,plain,
    ( spl4_9
  <=> sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f163,plain,
    ( spl4_15
  <=> k4_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) = k4_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f1983,plain,
    ( sK2 = k2_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK2))
    | ~ spl4_9
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f1982,f92])).

fof(f92,plain,
    ( sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f90])).

fof(f1982,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) = k2_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k3_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0))))
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f1897,f20])).

fof(f1897,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k3_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0)))
    | ~ spl4_15 ),
    inference(superposition,[],[f246,f165])).

fof(f165,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) = k4_xboole_0(sK2,k1_xboole_0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f163])).

fof(f1859,plain,
    ( spl4_54
    | ~ spl4_4
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f1207,f832,f41,f1856])).

fof(f1856,plain,
    ( spl4_54
  <=> k4_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f41,plain,
    ( spl4_4
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f832,plain,
    ( spl4_33
  <=> k4_xboole_0(k4_xboole_0(sK0,sK2),sK3) = k4_xboole_0(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f1207,plain,
    ( k4_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f1198,f43])).

fof(f43,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f1198,plain,
    ( k4_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK3))
    | ~ spl4_33 ),
    inference(superposition,[],[f834,f24])).

fof(f834,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),sK3) = k4_xboole_0(sK0,sK3)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f832])).

fof(f1854,plain,
    ( spl4_53
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f1064,f827,f1851])).

fof(f1851,plain,
    ( spl4_53
  <=> k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f827,plain,
    ( spl4_32
  <=> k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k4_xboole_0(sK2,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f1064,plain,
    ( k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK2))
    | ~ spl4_32 ),
    inference(superposition,[],[f829,f24])).

fof(f829,plain,
    ( k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k4_xboole_0(sK2,sK0),sK2)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f827])).

fof(f1849,plain,
    ( spl4_52
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f1050,f822,f1846])).

fof(f1846,plain,
    ( spl4_52
  <=> k4_xboole_0(sK3,sK2) = k4_xboole_0(sK3,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f822,plain,
    ( spl4_31
  <=> k4_xboole_0(sK3,sK2) = k4_xboole_0(k4_xboole_0(sK3,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f1050,plain,
    ( k4_xboole_0(sK3,sK2) = k4_xboole_0(sK3,k2_xboole_0(sK1,sK2))
    | ~ spl4_31 ),
    inference(superposition,[],[f824,f24])).

fof(f824,plain,
    ( k4_xboole_0(sK3,sK2) = k4_xboole_0(k4_xboole_0(sK3,sK1),sK2)
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f822])).

fof(f1844,plain,
    ( spl4_51
    | ~ spl4_4
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f1023,f802,f41,f1841])).

fof(f1841,plain,
    ( spl4_51
  <=> k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f802,plain,
    ( spl4_30
  <=> k4_xboole_0(k4_xboole_0(sK1,sK3),sK2) = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f1023,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f1022,f43])).

fof(f1022,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f1014,f20])).

fof(f1014,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK3,sK2))
    | ~ spl4_30 ),
    inference(superposition,[],[f804,f24])).

fof(f804,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK3),sK2) = k4_xboole_0(sK1,sK2)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f802])).

fof(f1839,plain,
    ( spl4_50
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f987,f797,f1836])).

fof(f1836,plain,
    ( spl4_50
  <=> k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f797,plain,
    ( spl4_29
  <=> k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f987,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK2))
    | ~ spl4_29 ),
    inference(superposition,[],[f799,f24])).

fof(f799,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK2)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f797])).

fof(f1734,plain,
    ( spl4_49
    | ~ spl4_12
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f790,f564,f113,f1731])).

fof(f1731,plain,
    ( spl4_49
  <=> k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f564,plain,
    ( spl4_24
  <=> k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f790,plain,
    ( k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK3),sK1)
    | ~ spl4_12
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f773,f566])).

fof(f566,plain,
    ( k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK1,sK1)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f564])).

fof(f773,plain,
    ( k4_xboole_0(sK1,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK3),sK1)
    | ~ spl4_12 ),
    inference(superposition,[],[f548,f115])).

fof(f548,plain,
    ( ! [X0] : k4_xboole_0(X0,sK1) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),sK1)
    | ~ spl4_12 ),
    inference(superposition,[],[f332,f20])).

fof(f332,plain,
    ( ! [X16] : k4_xboole_0(X16,sK1) = k4_xboole_0(k2_xboole_0(X16,k1_xboole_0),sK1)
    | ~ spl4_12 ),
    inference(superposition,[],[f104,f115])).

fof(f1680,plain,
    ( spl4_48
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f775,f113,f95,f1677])).

fof(f1677,plain,
    ( spl4_48
  <=> k4_xboole_0(sK3,sK1) = k4_xboole_0(k4_xboole_0(sK3,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f775,plain,
    ( k4_xboole_0(sK3,sK1) = k4_xboole_0(k4_xboole_0(sK3,sK1),sK1)
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(superposition,[],[f548,f97])).

fof(f1675,plain,
    ( spl4_47
    | ~ spl4_9
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f774,f113,f90,f1672])).

fof(f774,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK0),sK1) = k4_xboole_0(sK2,sK1)
    | ~ spl4_9
    | ~ spl4_12 ),
    inference(superposition,[],[f548,f92])).

fof(f1548,plain,
    ( spl4_46
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f772,f113,f108,f1545])).

fof(f1545,plain,
    ( spl4_46
  <=> k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f772,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(superposition,[],[f548,f110])).

fof(f1543,plain,
    ( spl4_45
    | ~ spl4_11
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f766,f489,f108,f1540])).

fof(f1540,plain,
    ( spl4_45
  <=> k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f489,plain,
    ( spl4_23
  <=> k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f766,plain,
    ( k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK0)
    | ~ spl4_11
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f748,f491])).

fof(f491,plain,
    ( k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(sK0,sK0)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f489])).

fof(f748,plain,
    ( k4_xboole_0(sK0,sK0) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK0)
    | ~ spl4_11 ),
    inference(superposition,[],[f473,f110])).

fof(f473,plain,
    ( ! [X0] : k4_xboole_0(X0,sK0) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),sK0)
    | ~ spl4_11 ),
    inference(superposition,[],[f331,f20])).

fof(f331,plain,
    ( ! [X15] : k4_xboole_0(X15,sK0) = k4_xboole_0(k2_xboole_0(X15,k1_xboole_0),sK0)
    | ~ spl4_11 ),
    inference(superposition,[],[f104,f110])).

fof(f1493,plain,
    ( spl4_44
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f751,f108,f95,f1490])).

fof(f1490,plain,
    ( spl4_44
  <=> k4_xboole_0(k4_xboole_0(sK3,sK1),sK0) = k4_xboole_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f751,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,sK1),sK0) = k4_xboole_0(sK3,sK0)
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(superposition,[],[f473,f97])).

fof(f1362,plain,
    ( spl4_43
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f750,f108,f90,f1359])).

fof(f1359,plain,
    ( spl4_43
  <=> k4_xboole_0(sK2,sK0) = k4_xboole_0(k4_xboole_0(sK2,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f750,plain,
    ( k4_xboole_0(sK2,sK0) = k4_xboole_0(k4_xboole_0(sK2,sK0),sK0)
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(superposition,[],[f473,f92])).

fof(f1357,plain,
    ( spl4_42
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f749,f113,f108,f1354])).

fof(f1354,plain,
    ( spl4_42
  <=> k4_xboole_0(k4_xboole_0(sK1,sK3),sK0) = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f749,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK3),sK0) = k4_xboole_0(sK1,sK0)
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(superposition,[],[f473,f115])).

fof(f1352,plain,
    ( spl4_41
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f571,f564,f1349])).

fof(f1349,plain,
    ( spl4_41
  <=> sK1 = k2_xboole_0(k3_xboole_0(sK1,sK1),k4_xboole_0(k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f571,plain,
    ( sK1 = k2_xboole_0(k3_xboole_0(sK1,sK1),k4_xboole_0(k1_xboole_0,sK1))
    | ~ spl4_24 ),
    inference(superposition,[],[f80,f566])).

fof(f1335,plain,
    ( spl4_40
    | ~ spl4_4
    | ~ spl4_23
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f1322,f1035,f489,f41,f1332])).

fof(f1332,plain,
    ( spl4_40
  <=> k4_xboole_0(sK1,sK2) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f1322,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_23
    | ~ spl4_38 ),
    inference(forward_demodulation,[],[f1321,f1037])).

fof(f1321,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f1300,f499])).

fof(f499,plain,
    ( ! [X1] : k4_xboole_0(sK0,k2_xboole_0(sK0,X1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X1))
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f497,f24])).

fof(f497,plain,
    ( ! [X1] : k4_xboole_0(sK0,k2_xboole_0(sK0,X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,sK0),X1)
    | ~ spl4_23 ),
    inference(superposition,[],[f24,f491])).

fof(f1300,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))
    | ~ spl4_4 ),
    inference(superposition,[],[f138,f335])).

fof(f335,plain,
    ( ! [X19] : k4_xboole_0(X19,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(X19,sK2),k2_xboole_0(sK0,sK1))
    | ~ spl4_4 ),
    inference(superposition,[],[f104,f43])).

fof(f138,plain,(
    ! [X2,X3,X1] : k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k4_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(forward_demodulation,[],[f136,f24])).

fof(f136,plain,(
    ! [X2,X3,X1] : k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k4_xboole_0(k4_xboole_0(X2,X1),X3) ),
    inference(superposition,[],[f24,f60])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f21,f20])).

fof(f1271,plain,
    ( spl4_39
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f496,f489,f1268])).

fof(f1268,plain,
    ( spl4_39
  <=> sK0 = k2_xboole_0(k3_xboole_0(sK0,sK0),k4_xboole_0(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f496,plain,
    ( sK0 = k2_xboole_0(k3_xboole_0(sK0,sK0),k4_xboole_0(k1_xboole_0,sK0))
    | ~ spl4_23 ),
    inference(superposition,[],[f80,f491])).

fof(f1038,plain,
    ( spl4_38
    | ~ spl4_4
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f1024,f802,f41,f1035])).

fof(f1024,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_30 ),
    inference(backward_demodulation,[],[f925,f1023])).

fof(f925,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f916,f138])).

fof(f916,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))
    | ~ spl4_4 ),
    inference(superposition,[],[f335,f60])).

fof(f855,plain,
    ( spl4_37
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f610,f383,f95,f852])).

fof(f610,plain,
    ( k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(k4_xboole_0(sK3,sK1),sK3)
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f599,f385])).

fof(f599,plain,
    ( k4_xboole_0(sK3,sK3) = k4_xboole_0(k4_xboole_0(sK3,sK1),sK3)
    | ~ spl4_10 ),
    inference(superposition,[],[f369,f97])).

fof(f369,plain,
    ( ! [X0] : k4_xboole_0(X0,sK3) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),sK3)
    | ~ spl4_10 ),
    inference(superposition,[],[f334,f20])).

fof(f334,plain,
    ( ! [X18] : k4_xboole_0(X18,sK3) = k4_xboole_0(k2_xboole_0(X18,k1_xboole_0),sK3)
    | ~ spl4_10 ),
    inference(superposition,[],[f104,f97])).

fof(f850,plain,
    ( spl4_36
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f127,f120,f847])).

fof(f847,plain,
    ( spl4_36
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k3_xboole_0(sK3,k2_xboole_0(sK0,sK1)),k4_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f120,plain,
    ( spl4_13
  <=> k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f127,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(k3_xboole_0(sK3,k2_xboole_0(sK0,sK1)),k4_xboole_0(sK2,sK3))
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f125,f19])).

fof(f125,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),sK3),k4_xboole_0(sK2,sK3))
    | ~ spl4_13 ),
    inference(superposition,[],[f22,f122])).

fof(f122,plain,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f120])).

fof(f845,plain,
    ( spl4_35
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f598,f95,f90,f842])).

fof(f598,plain,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(k4_xboole_0(sK2,sK0),sK3)
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(superposition,[],[f369,f92])).

fof(f840,plain,
    ( spl4_34
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f597,f113,f95,f837])).

fof(f597,plain,
    ( k4_xboole_0(sK1,sK3) = k4_xboole_0(k4_xboole_0(sK1,sK3),sK3)
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(superposition,[],[f369,f115])).

fof(f835,plain,
    ( spl4_33
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f596,f108,f95,f832])).

fof(f596,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),sK3) = k4_xboole_0(sK0,sK3)
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(superposition,[],[f369,f110])).

fof(f830,plain,
    ( spl4_32
    | ~ spl4_9
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f590,f359,f90,f827])).

fof(f590,plain,
    ( k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k4_xboole_0(sK2,sK0),sK2)
    | ~ spl4_9
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f578,f361])).

fof(f578,plain,
    ( k4_xboole_0(sK2,sK2) = k4_xboole_0(k4_xboole_0(sK2,sK0),sK2)
    | ~ spl4_9 ),
    inference(superposition,[],[f345,f92])).

fof(f345,plain,
    ( ! [X0] : k4_xboole_0(X0,sK2) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),sK2)
    | ~ spl4_9 ),
    inference(superposition,[],[f333,f20])).

fof(f333,plain,
    ( ! [X17] : k4_xboole_0(X17,sK2) = k4_xboole_0(k2_xboole_0(X17,k1_xboole_0),sK2)
    | ~ spl4_9 ),
    inference(superposition,[],[f104,f92])).

fof(f825,plain,
    ( spl4_31
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f579,f95,f90,f822])).

fof(f579,plain,
    ( k4_xboole_0(sK3,sK2) = k4_xboole_0(k4_xboole_0(sK3,sK1),sK2)
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(superposition,[],[f345,f97])).

fof(f805,plain,
    ( spl4_30
    | ~ spl4_9
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f577,f113,f90,f802])).

fof(f577,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK3),sK2) = k4_xboole_0(sK1,sK2)
    | ~ spl4_9
    | ~ spl4_12 ),
    inference(superposition,[],[f345,f115])).

fof(f800,plain,
    ( spl4_29
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f576,f108,f90,f797])).

fof(f576,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK2)
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(superposition,[],[f345,f110])).

fof(f747,plain,
    ( spl4_28
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f457,f383,f744])).

fof(f744,plain,
    ( spl4_28
  <=> sK3 = k2_xboole_0(k3_xboole_0(sK3,sK3),k4_xboole_0(k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f457,plain,
    ( sK3 = k2_xboole_0(k3_xboole_0(sK3,sK3),k4_xboole_0(k1_xboole_0,sK3))
    | ~ spl4_22 ),
    inference(superposition,[],[f80,f385])).

fof(f711,plain,
    ( spl4_27
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f365,f359,f708])).

fof(f708,plain,
    ( spl4_27
  <=> sK2 = k2_xboole_0(k3_xboole_0(sK2,sK2),k4_xboole_0(k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f365,plain,
    ( sK2 = k2_xboole_0(k3_xboole_0(sK2,sK2),k4_xboole_0(k1_xboole_0,sK2))
    | ~ spl4_21 ),
    inference(superposition,[],[f80,f361])).

fof(f706,plain,
    ( spl4_26
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f301,f224,f703])).

fof(f703,plain,
    ( spl4_26
  <=> k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,k2_xboole_0(k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f301,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,k2_xboole_0(k1_xboole_0,sK3))
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f294,f20])).

fof(f294,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,k2_xboole_0(sK3,k1_xboole_0))
    | ~ spl4_18 ),
    inference(superposition,[],[f226,f24])).

fof(f701,plain,
    ( spl4_25
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f286,f219,f698])).

fof(f698,plain,
    ( spl4_25
  <=> k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f286,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2))
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f279,f20])).

fof(f279,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k2_xboole_0(sK2,k1_xboole_0))
    | ~ spl4_17 ),
    inference(superposition,[],[f221,f24])).

fof(f567,plain,
    ( spl4_24
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f550,f113,f564])).

fof(f550,plain,
    ( k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK1,sK1)
    | ~ spl4_12 ),
    inference(superposition,[],[f332,f60])).

fof(f492,plain,
    ( spl4_23
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f475,f108,f489])).

fof(f475,plain,
    ( k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(sK0,sK0)
    | ~ spl4_11 ),
    inference(superposition,[],[f331,f60])).

fof(f386,plain,
    ( spl4_22
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f371,f95,f383])).

fof(f371,plain,
    ( k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK3,sK3)
    | ~ spl4_10 ),
    inference(superposition,[],[f334,f60])).

fof(f362,plain,
    ( spl4_21
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f347,f90,f359])).

fof(f347,plain,
    ( k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK2,sK2)
    | ~ spl4_9 ),
    inference(superposition,[],[f333,f60])).

fof(f278,plain,
    ( spl4_20
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f212,f190,f275])).

fof(f275,plain,
    ( spl4_20
  <=> k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,k2_xboole_0(k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f212,plain,
    ( k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,k2_xboole_0(k1_xboole_0,sK1))
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f206,f20])).

fof(f206,plain,
    ( k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,k2_xboole_0(sK1,k1_xboole_0))
    | ~ spl4_16 ),
    inference(superposition,[],[f192,f24])).

fof(f273,plain,
    ( spl4_19
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f200,f163,f270])).

fof(f270,plain,
    ( spl4_19
  <=> k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f200,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK0))
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f194,f20])).

fof(f194,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k2_xboole_0(sK0,k1_xboole_0))
    | ~ spl4_15 ),
    inference(superposition,[],[f165,f24])).

fof(f227,plain,
    ( spl4_18
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f132,f113,f224])).

fof(f132,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_12 ),
    inference(superposition,[],[f60,f115])).

fof(f222,plain,
    ( spl4_17
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f131,f108,f219])).

fof(f131,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl4_11 ),
    inference(superposition,[],[f60,f110])).

fof(f193,plain,
    ( spl4_16
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f134,f95,f190])).

fof(f134,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) = k4_xboole_0(sK3,k1_xboole_0)
    | ~ spl4_10 ),
    inference(superposition,[],[f60,f97])).

fof(f166,plain,
    ( spl4_15
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f133,f90,f163])).

fof(f133,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) = k4_xboole_0(sK2,k1_xboole_0)
    | ~ spl4_9 ),
    inference(superposition,[],[f60,f92])).

fof(f156,plain,
    ( spl4_14
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f135,f41,f153])).

fof(f153,plain,
    ( spl4_14
  <=> k4_xboole_0(sK3,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f135,plain,
    ( k4_xboole_0(sK3,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)
    | ~ spl4_4 ),
    inference(superposition,[],[f60,f43])).

fof(f123,plain,
    ( spl4_13
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f59,f41,f120])).

fof(f59,plain,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)
    | ~ spl4_4 ),
    inference(superposition,[],[f21,f43])).

fof(f116,plain,
    ( spl4_12
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f88,f76,f113])).

fof(f76,plain,
    ( spl4_8
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f88,plain,
    ( sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))
    | ~ spl4_8 ),
    inference(superposition,[],[f22,f78])).

fof(f78,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f76])).

fof(f111,plain,
    ( spl4_11
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f82,f71,f108])).

fof(f71,plain,
    ( spl4_7
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f82,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2))
    | ~ spl4_7 ),
    inference(superposition,[],[f22,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f98,plain,
    ( spl4_10
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f84,f55,f95])).

fof(f55,plain,
    ( spl4_6
  <=> k1_xboole_0 = k3_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f84,plain,
    ( sK3 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1))
    | ~ spl4_6 ),
    inference(superposition,[],[f22,f57])).

fof(f57,plain,
    ( k1_xboole_0 = k3_xboole_0(sK3,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f93,plain,
    ( spl4_9
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f83,f50,f90])).

fof(f50,plain,
    ( spl4_5
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f83,plain,
    ( sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0))
    | ~ spl4_5 ),
    inference(superposition,[],[f22,f52])).

fof(f52,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f79,plain,
    ( spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f66,f55,f76])).

fof(f66,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK3)
    | ~ spl4_6 ),
    inference(superposition,[],[f57,f19])).

fof(f74,plain,
    ( spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f62,f50,f71])).

fof(f62,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl4_5 ),
    inference(superposition,[],[f52,f19])).

fof(f58,plain,
    ( spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f46,f31,f55])).

fof(f31,plain,
    ( spl4_2
  <=> r1_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f46,plain,
    ( k1_xboole_0 = k3_xboole_0(sK3,sK1)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f33,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f33,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f53,plain,
    ( spl4_5
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f45,f26,f50])).

fof(f26,plain,
    ( spl4_1
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f45,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK0)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f28,f23])).

fof(f28,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f44,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f15,f41])).

fof(f15,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f39,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f18,f36])).

fof(f18,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f17,f31])).

fof(f17,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f16,f26])).

fof(f16,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:50:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (10764)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.47  % (10754)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (10762)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (10763)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (10755)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (10752)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (10753)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (10768)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (10750)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (10769)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (10751)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (10765)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (10769)Refutation not found, incomplete strategy% (10769)------------------------------
% 0.22/0.51  % (10769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (10769)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (10769)Memory used [KB]: 10490
% 0.22/0.51  % (10769)Time elapsed: 0.093 s
% 0.22/0.51  % (10769)------------------------------
% 0.22/0.51  % (10769)------------------------------
% 0.22/0.51  % (10758)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (10759)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (10759)Refutation not found, incomplete strategy% (10759)------------------------------
% 0.22/0.52  % (10759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10759)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10759)Memory used [KB]: 6012
% 0.22/0.52  % (10759)Time elapsed: 0.101 s
% 0.22/0.52  % (10759)------------------------------
% 0.22/0.52  % (10759)------------------------------
% 0.22/0.52  % (10760)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (10757)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.52  % (10767)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.52  % (10749)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (10761)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (10761)Refutation not found, incomplete strategy% (10761)------------------------------
% 0.22/0.53  % (10761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10761)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (10761)Memory used [KB]: 6012
% 0.22/0.53  % (10761)Time elapsed: 0.004 s
% 0.22/0.53  % (10761)------------------------------
% 0.22/0.53  % (10761)------------------------------
% 0.22/0.53  % (10756)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.53  % (10766)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 3.92/0.88  % (10756)Refutation found. Thanks to Tanya!
% 3.92/0.88  % SZS status Theorem for theBenchmark
% 3.92/0.88  % SZS output start Proof for theBenchmark
% 3.92/0.88  fof(f3265,plain,(
% 3.92/0.88    $false),
% 3.92/0.88    inference(avatar_sat_refutation,[],[f29,f34,f39,f44,f53,f58,f74,f79,f93,f98,f111,f116,f123,f156,f166,f193,f222,f227,f273,f278,f362,f386,f492,f567,f701,f706,f711,f747,f800,f805,f825,f830,f835,f840,f845,f850,f855,f1038,f1271,f1335,f1352,f1357,f1362,f1493,f1543,f1548,f1675,f1680,f1734,f1839,f1844,f1849,f1854,f1859,f2091,f2096,f2221,f2226,f2231,f2236,f2241,f2330,f2541,f2546,f2551,f3232,f3248,f3254])).
% 3.92/0.88  fof(f3254,plain,(
% 3.92/0.88    spl4_3 | ~spl4_66),
% 3.92/0.88    inference(avatar_contradiction_clause,[],[f3253])).
% 3.92/0.88  fof(f3253,plain,(
% 3.92/0.88    $false | (spl4_3 | ~spl4_66)),
% 3.92/0.88    inference(subsumption_resolution,[],[f3252,f38])).
% 3.92/0.88  fof(f38,plain,(
% 3.92/0.88    sK1 != sK2 | spl4_3),
% 3.92/0.88    inference(avatar_component_clause,[],[f36])).
% 3.92/0.88  fof(f36,plain,(
% 3.92/0.88    spl4_3 <=> sK1 = sK2),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 3.92/0.88  fof(f3252,plain,(
% 3.92/0.88    sK1 = sK2 | ~spl4_66),
% 3.92/0.88    inference(forward_demodulation,[],[f3235,f22])).
% 3.92/0.88  fof(f22,plain,(
% 3.92/0.88    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 3.92/0.88    inference(cnf_transformation,[],[f6])).
% 3.92/0.88  fof(f6,axiom,(
% 3.92/0.88    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 3.92/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 3.92/0.88  fof(f3235,plain,(
% 3.92/0.88    sK2 = k2_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)) | ~spl4_66),
% 3.92/0.88    inference(superposition,[],[f80,f3231])).
% 3.92/0.88  fof(f3231,plain,(
% 3.92/0.88    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK1) | ~spl4_66),
% 3.92/0.88    inference(avatar_component_clause,[],[f3229])).
% 3.92/0.88  fof(f3229,plain,(
% 3.92/0.88    spl4_66 <=> k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK1)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 3.92/0.88  fof(f80,plain,(
% 3.92/0.88    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1)) = X0) )),
% 3.92/0.88    inference(superposition,[],[f22,f19])).
% 3.92/0.88  fof(f19,plain,(
% 3.92/0.88    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.92/0.88    inference(cnf_transformation,[],[f2])).
% 3.92/0.88  fof(f2,axiom,(
% 3.92/0.88    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.92/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.92/0.88  fof(f3248,plain,(
% 3.92/0.88    spl4_3 | ~spl4_66),
% 3.92/0.88    inference(avatar_contradiction_clause,[],[f3247])).
% 3.92/0.88  fof(f3247,plain,(
% 3.92/0.88    $false | (spl4_3 | ~spl4_66)),
% 3.92/0.88    inference(subsumption_resolution,[],[f3246,f38])).
% 3.92/0.88  fof(f3246,plain,(
% 3.92/0.88    sK1 = sK2 | ~spl4_66),
% 3.92/0.88    inference(forward_demodulation,[],[f3233,f80])).
% 3.92/0.88  fof(f3233,plain,(
% 3.92/0.88    sK2 = k2_xboole_0(k3_xboole_0(sK2,sK1),k4_xboole_0(sK1,sK2)) | ~spl4_66),
% 3.92/0.88    inference(superposition,[],[f22,f3231])).
% 3.92/0.88  fof(f3232,plain,(
% 3.92/0.88    spl4_66 | ~spl4_38 | ~spl4_47),
% 3.92/0.88    inference(avatar_split_clause,[],[f3199,f1672,f1035,f3229])).
% 3.92/0.88  fof(f1035,plain,(
% 3.92/0.88    spl4_38 <=> k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 3.92/0.88  fof(f1672,plain,(
% 3.92/0.88    spl4_47 <=> k4_xboole_0(k4_xboole_0(sK2,sK0),sK1) = k4_xboole_0(sK2,sK1)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 3.92/0.88  fof(f3199,plain,(
% 3.92/0.88    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK1) | (~spl4_38 | ~spl4_47)),
% 3.92/0.88    inference(forward_demodulation,[],[f3184,f1037])).
% 3.92/0.88  fof(f1037,plain,(
% 3.92/0.88    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | ~spl4_38),
% 3.92/0.88    inference(avatar_component_clause,[],[f1035])).
% 3.92/0.88  fof(f3184,plain,(
% 3.92/0.88    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | ~spl4_47),
% 3.92/0.88    inference(superposition,[],[f1674,f24])).
% 3.92/0.88  fof(f24,plain,(
% 3.92/0.88    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.92/0.88    inference(cnf_transformation,[],[f5])).
% 3.92/0.88  fof(f5,axiom,(
% 3.92/0.88    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.92/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 3.92/0.88  fof(f1674,plain,(
% 3.92/0.88    k4_xboole_0(k4_xboole_0(sK2,sK0),sK1) = k4_xboole_0(sK2,sK1) | ~spl4_47),
% 3.92/0.88    inference(avatar_component_clause,[],[f1672])).
% 3.92/0.88  fof(f2551,plain,(
% 3.92/0.88    spl4_65 | ~spl4_37),
% 3.92/0.88    inference(avatar_split_clause,[],[f1250,f852,f2548])).
% 3.92/0.88  fof(f2548,plain,(
% 3.92/0.88    spl4_65 <=> k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK3,k2_xboole_0(sK1,sK3))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 3.92/0.88  fof(f852,plain,(
% 3.92/0.88    spl4_37 <=> k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(k4_xboole_0(sK3,sK1),sK3)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 3.92/0.88  fof(f1250,plain,(
% 3.92/0.88    k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK3,k2_xboole_0(sK1,sK3)) | ~spl4_37),
% 3.92/0.88    inference(superposition,[],[f854,f24])).
% 3.92/0.88  fof(f854,plain,(
% 3.92/0.88    k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(k4_xboole_0(sK3,sK1),sK3) | ~spl4_37),
% 3.92/0.88    inference(avatar_component_clause,[],[f852])).
% 3.92/0.88  fof(f2546,plain,(
% 3.92/0.88    spl4_64 | ~spl4_35),
% 3.92/0.88    inference(avatar_split_clause,[],[f1232,f842,f2543])).
% 3.92/0.88  fof(f2543,plain,(
% 3.92/0.88    spl4_64 <=> k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK3))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 3.92/0.88  fof(f842,plain,(
% 3.92/0.88    spl4_35 <=> k4_xboole_0(sK2,sK3) = k4_xboole_0(k4_xboole_0(sK2,sK0),sK3)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 3.92/0.88  fof(f1232,plain,(
% 3.92/0.88    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK3)) | ~spl4_35),
% 3.92/0.88    inference(superposition,[],[f844,f24])).
% 3.92/0.88  fof(f844,plain,(
% 3.92/0.88    k4_xboole_0(sK2,sK3) = k4_xboole_0(k4_xboole_0(sK2,sK0),sK3) | ~spl4_35),
% 3.92/0.88    inference(avatar_component_clause,[],[f842])).
% 3.92/0.88  fof(f2541,plain,(
% 3.92/0.88    spl4_63 | ~spl4_34),
% 3.92/0.88    inference(avatar_split_clause,[],[f1220,f837,f2538])).
% 3.92/0.88  fof(f2538,plain,(
% 3.92/0.88    spl4_63 <=> k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k2_xboole_0(sK3,sK3))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 3.92/0.88  fof(f837,plain,(
% 3.92/0.88    spl4_34 <=> k4_xboole_0(sK1,sK3) = k4_xboole_0(k4_xboole_0(sK1,sK3),sK3)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 3.92/0.88  fof(f1220,plain,(
% 3.92/0.88    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k2_xboole_0(sK3,sK3)) | ~spl4_34),
% 3.92/0.88    inference(superposition,[],[f839,f24])).
% 3.92/0.88  fof(f839,plain,(
% 3.92/0.88    k4_xboole_0(sK1,sK3) = k4_xboole_0(k4_xboole_0(sK1,sK3),sK3) | ~spl4_34),
% 3.92/0.88    inference(avatar_component_clause,[],[f837])).
% 3.92/0.88  fof(f2330,plain,(
% 3.92/0.88    spl4_62 | ~spl4_22 | ~spl4_56),
% 3.92/0.88    inference(avatar_split_clause,[],[f2139,f2093,f383,f2327])).
% 3.92/0.88  fof(f2327,plain,(
% 3.92/0.88    spl4_62 <=> k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(k4_xboole_0(sK3,k1_xboole_0),sK3)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 3.92/0.88  fof(f383,plain,(
% 3.92/0.88    spl4_22 <=> k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK3,sK3)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 3.92/0.88  fof(f2093,plain,(
% 3.92/0.88    spl4_56 <=> sK3 = k2_xboole_0(k4_xboole_0(sK3,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK3))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 3.92/0.88  fof(f2139,plain,(
% 3.92/0.88    k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(k4_xboole_0(sK3,k1_xboole_0),sK3) | (~spl4_22 | ~spl4_56)),
% 3.92/0.88    inference(forward_demodulation,[],[f2124,f385])).
% 3.92/0.88  fof(f385,plain,(
% 3.92/0.88    k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK3,sK3) | ~spl4_22),
% 3.92/0.88    inference(avatar_component_clause,[],[f383])).
% 3.92/0.88  fof(f2124,plain,(
% 3.92/0.88    k4_xboole_0(sK3,sK3) = k4_xboole_0(k4_xboole_0(sK3,k1_xboole_0),sK3) | ~spl4_56),
% 3.92/0.88    inference(superposition,[],[f329,f2095])).
% 3.92/0.88  fof(f2095,plain,(
% 3.92/0.88    sK3 = k2_xboole_0(k4_xboole_0(sK3,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK3)) | ~spl4_56),
% 3.92/0.88    inference(avatar_component_clause,[],[f2093])).
% 3.92/0.88  fof(f329,plain,(
% 3.92/0.88    ( ! [X10,X11,X9] : (k4_xboole_0(X11,X10) = k4_xboole_0(k2_xboole_0(X11,k3_xboole_0(X9,X10)),X10)) )),
% 3.92/0.88    inference(superposition,[],[f104,f80])).
% 3.92/0.88  fof(f104,plain,(
% 3.92/0.88    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))) )),
% 3.92/0.88    inference(forward_demodulation,[],[f101,f24])).
% 3.92/0.88  fof(f101,plain,(
% 3.92/0.88    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))) )),
% 3.92/0.88    inference(superposition,[],[f24,f21])).
% 3.92/0.88  fof(f21,plain,(
% 3.92/0.88    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 3.92/0.88    inference(cnf_transformation,[],[f4])).
% 3.92/0.88  fof(f4,axiom,(
% 3.92/0.88    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 3.92/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 3.92/0.88  fof(f2241,plain,(
% 3.92/0.88    spl4_61 | ~spl4_56),
% 3.92/0.88    inference(avatar_split_clause,[],[f2125,f2093,f2238])).
% 3.92/0.88  fof(f2238,plain,(
% 3.92/0.88    spl4_61 <=> k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK3,k1_xboole_0),k1_xboole_0)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 3.92/0.88  fof(f2125,plain,(
% 3.92/0.88    k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK3,k1_xboole_0),k1_xboole_0) | ~spl4_56),
% 3.92/0.88    inference(superposition,[],[f328,f2095])).
% 3.92/0.88  fof(f328,plain,(
% 3.92/0.88    ( ! [X6,X8,X7] : (k4_xboole_0(X8,X6) = k4_xboole_0(k2_xboole_0(X8,k3_xboole_0(X6,X7)),X6)) )),
% 3.92/0.88    inference(superposition,[],[f104,f22])).
% 3.92/0.88  fof(f2236,plain,(
% 3.92/0.88    spl4_60 | ~spl4_21 | ~spl4_55),
% 3.92/0.88    inference(avatar_split_clause,[],[f2114,f2088,f359,f2233])).
% 3.92/0.88  fof(f2233,plain,(
% 3.92/0.88    spl4_60 <=> k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 3.92/0.88  fof(f359,plain,(
% 3.92/0.88    spl4_21 <=> k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK2,sK2)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 3.92/0.88  fof(f2088,plain,(
% 3.92/0.88    spl4_55 <=> sK2 = k2_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK2))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 3.92/0.88  fof(f2114,plain,(
% 3.92/0.88    k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2) | (~spl4_21 | ~spl4_55)),
% 3.92/0.88    inference(forward_demodulation,[],[f2099,f361])).
% 3.92/0.88  fof(f361,plain,(
% 3.92/0.88    k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK2,sK2) | ~spl4_21),
% 3.92/0.88    inference(avatar_component_clause,[],[f359])).
% 3.92/0.88  fof(f2099,plain,(
% 3.92/0.88    k4_xboole_0(sK2,sK2) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),sK2) | ~spl4_55),
% 3.92/0.88    inference(superposition,[],[f329,f2090])).
% 3.92/0.88  fof(f2090,plain,(
% 3.92/0.88    sK2 = k2_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK2)) | ~spl4_55),
% 3.92/0.88    inference(avatar_component_clause,[],[f2088])).
% 3.92/0.88  fof(f2231,plain,(
% 3.92/0.88    spl4_59 | ~spl4_55),
% 3.92/0.88    inference(avatar_split_clause,[],[f2100,f2088,f2228])).
% 3.92/0.88  fof(f2228,plain,(
% 3.92/0.88    spl4_59 <=> k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 3.92/0.88  fof(f2100,plain,(
% 3.92/0.88    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0) | ~spl4_55),
% 3.92/0.88    inference(superposition,[],[f328,f2090])).
% 3.92/0.88  fof(f2226,plain,(
% 3.92/0.88    spl4_58 | ~spl4_12 | ~spl4_18),
% 3.92/0.88    inference(avatar_split_clause,[],[f1981,f224,f113,f2223])).
% 3.92/0.88  fof(f2223,plain,(
% 3.92/0.88    spl4_58 <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK1))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 3.92/0.88  fof(f113,plain,(
% 3.92/0.88    spl4_12 <=> sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 3.92/0.88  fof(f224,plain,(
% 3.92/0.88    spl4_18 <=> k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) = k4_xboole_0(sK1,k1_xboole_0)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 3.92/0.88  fof(f1981,plain,(
% 3.92/0.88    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK1)) | (~spl4_12 | ~spl4_18)),
% 3.92/0.88    inference(forward_demodulation,[],[f1980,f115])).
% 3.92/0.88  fof(f115,plain,(
% 3.92/0.88    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) | ~spl4_12),
% 3.92/0.88    inference(avatar_component_clause,[],[f113])).
% 3.92/0.88  fof(f1980,plain,(
% 3.92/0.88    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k3_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)))) | ~spl4_18),
% 3.92/0.88    inference(forward_demodulation,[],[f1896,f20])).
% 3.92/0.88  fof(f20,plain,(
% 3.92/0.88    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.92/0.88    inference(cnf_transformation,[],[f1])).
% 3.92/0.88  fof(f1,axiom,(
% 3.92/0.88    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.92/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.92/0.88  fof(f1896,plain,(
% 3.92/0.88    k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k3_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0))) | ~spl4_18),
% 3.92/0.88    inference(superposition,[],[f246,f226])).
% 3.92/0.88  fof(f226,plain,(
% 3.92/0.88    k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) = k4_xboole_0(sK1,k1_xboole_0) | ~spl4_18),
% 3.92/0.88    inference(avatar_component_clause,[],[f224])).
% 3.92/0.88  fof(f246,plain,(
% 3.92/0.88    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = k2_xboole_0(k4_xboole_0(X3,X2),k3_xboole_0(X2,k2_xboole_0(X3,X2)))) )),
% 3.92/0.88    inference(superposition,[],[f87,f20])).
% 3.92/0.88  fof(f87,plain,(
% 3.92/0.88    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X1,k2_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) )),
% 3.92/0.88    inference(forward_demodulation,[],[f85,f19])).
% 3.92/0.88  fof(f85,plain,(
% 3.92/0.88    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1))) )),
% 3.92/0.88    inference(superposition,[],[f22,f21])).
% 3.92/0.88  fof(f2221,plain,(
% 3.92/0.88    spl4_57 | ~spl4_11 | ~spl4_17),
% 3.92/0.88    inference(avatar_split_clause,[],[f1979,f219,f108,f2218])).
% 3.92/0.88  fof(f2218,plain,(
% 3.92/0.88    spl4_57 <=> sK0 = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK0))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 3.92/0.88  fof(f108,plain,(
% 3.92/0.88    spl4_11 <=> sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 3.92/0.88  fof(f219,plain,(
% 3.92/0.88    spl4_17 <=> k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = k4_xboole_0(sK0,k1_xboole_0)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 3.92/0.88  fof(f1979,plain,(
% 3.92/0.88    sK0 = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK0)) | (~spl4_11 | ~spl4_17)),
% 3.92/0.88    inference(forward_demodulation,[],[f1978,f110])).
% 3.92/0.88  fof(f110,plain,(
% 3.92/0.88    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) | ~spl4_11),
% 3.92/0.88    inference(avatar_component_clause,[],[f108])).
% 3.92/0.88  fof(f1978,plain,(
% 3.92/0.88    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)))) | ~spl4_17),
% 3.92/0.88    inference(forward_demodulation,[],[f1895,f20])).
% 3.92/0.88  fof(f1895,plain,(
% 3.92/0.88    k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0))) | ~spl4_17),
% 3.92/0.88    inference(superposition,[],[f246,f221])).
% 3.92/0.88  fof(f221,plain,(
% 3.92/0.88    k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = k4_xboole_0(sK0,k1_xboole_0) | ~spl4_17),
% 3.92/0.88    inference(avatar_component_clause,[],[f219])).
% 3.92/0.88  fof(f2096,plain,(
% 3.92/0.88    spl4_56 | ~spl4_10 | ~spl4_16),
% 3.92/0.88    inference(avatar_split_clause,[],[f1985,f190,f95,f2093])).
% 3.92/0.88  fof(f95,plain,(
% 3.92/0.88    spl4_10 <=> sK3 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 3.92/0.88  fof(f190,plain,(
% 3.92/0.88    spl4_16 <=> k4_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) = k4_xboole_0(sK3,k1_xboole_0)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 3.92/0.88  fof(f1985,plain,(
% 3.92/0.88    sK3 = k2_xboole_0(k4_xboole_0(sK3,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK3)) | (~spl4_10 | ~spl4_16)),
% 3.92/0.88    inference(forward_demodulation,[],[f1984,f97])).
% 3.92/0.88  fof(f97,plain,(
% 3.92/0.88    sK3 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) | ~spl4_10),
% 3.92/0.88    inference(avatar_component_clause,[],[f95])).
% 3.92/0.88  fof(f1984,plain,(
% 3.92/0.88    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) = k2_xboole_0(k4_xboole_0(sK3,k1_xboole_0),k3_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)))) | ~spl4_16),
% 3.92/0.88    inference(forward_demodulation,[],[f1898,f20])).
% 3.92/0.88  fof(f1898,plain,(
% 3.92/0.88    k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK3,k1_xboole_0),k3_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0))) | ~spl4_16),
% 3.92/0.88    inference(superposition,[],[f246,f192])).
% 3.92/0.88  fof(f192,plain,(
% 3.92/0.88    k4_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) = k4_xboole_0(sK3,k1_xboole_0) | ~spl4_16),
% 3.92/0.88    inference(avatar_component_clause,[],[f190])).
% 3.92/0.88  fof(f2091,plain,(
% 3.92/0.88    spl4_55 | ~spl4_9 | ~spl4_15),
% 3.92/0.88    inference(avatar_split_clause,[],[f1983,f163,f90,f2088])).
% 3.92/0.88  fof(f90,plain,(
% 3.92/0.88    spl4_9 <=> sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 3.92/0.88  fof(f163,plain,(
% 3.92/0.88    spl4_15 <=> k4_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) = k4_xboole_0(sK2,k1_xboole_0)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 3.92/0.88  fof(f1983,plain,(
% 3.92/0.88    sK2 = k2_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK2)) | (~spl4_9 | ~spl4_15)),
% 3.92/0.88    inference(forward_demodulation,[],[f1982,f92])).
% 3.92/0.88  fof(f92,plain,(
% 3.92/0.88    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) | ~spl4_9),
% 3.92/0.88    inference(avatar_component_clause,[],[f90])).
% 3.92/0.88  fof(f1982,plain,(
% 3.92/0.88    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) = k2_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k3_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)))) | ~spl4_15),
% 3.92/0.88    inference(forward_demodulation,[],[f1897,f20])).
% 3.92/0.88  fof(f1897,plain,(
% 3.92/0.88    k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k3_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0))) | ~spl4_15),
% 3.92/0.88    inference(superposition,[],[f246,f165])).
% 3.92/0.88  fof(f165,plain,(
% 3.92/0.88    k4_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) = k4_xboole_0(sK2,k1_xboole_0) | ~spl4_15),
% 3.92/0.88    inference(avatar_component_clause,[],[f163])).
% 3.92/0.88  fof(f1859,plain,(
% 3.92/0.88    spl4_54 | ~spl4_4 | ~spl4_33),
% 3.92/0.88    inference(avatar_split_clause,[],[f1207,f832,f41,f1856])).
% 3.92/0.88  fof(f1856,plain,(
% 3.92/0.88    spl4_54 <=> k4_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 3.92/0.88  fof(f41,plain,(
% 3.92/0.88    spl4_4 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 3.92/0.88  fof(f832,plain,(
% 3.92/0.88    spl4_33 <=> k4_xboole_0(k4_xboole_0(sK0,sK2),sK3) = k4_xboole_0(sK0,sK3)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 3.92/0.88  fof(f1207,plain,(
% 3.92/0.88    k4_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) | (~spl4_4 | ~spl4_33)),
% 3.92/0.88    inference(forward_demodulation,[],[f1198,f43])).
% 3.92/0.88  fof(f43,plain,(
% 3.92/0.88    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) | ~spl4_4),
% 3.92/0.88    inference(avatar_component_clause,[],[f41])).
% 3.92/0.88  fof(f1198,plain,(
% 3.92/0.88    k4_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK3)) | ~spl4_33),
% 3.92/0.88    inference(superposition,[],[f834,f24])).
% 3.92/0.88  fof(f834,plain,(
% 3.92/0.88    k4_xboole_0(k4_xboole_0(sK0,sK2),sK3) = k4_xboole_0(sK0,sK3) | ~spl4_33),
% 3.92/0.88    inference(avatar_component_clause,[],[f832])).
% 3.92/0.88  fof(f1854,plain,(
% 3.92/0.88    spl4_53 | ~spl4_32),
% 3.92/0.88    inference(avatar_split_clause,[],[f1064,f827,f1851])).
% 3.92/0.88  fof(f1851,plain,(
% 3.92/0.88    spl4_53 <=> k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK2))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 3.92/0.88  fof(f827,plain,(
% 3.92/0.88    spl4_32 <=> k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k4_xboole_0(sK2,sK0),sK2)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 3.92/0.88  fof(f1064,plain,(
% 3.92/0.88    k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK2)) | ~spl4_32),
% 3.92/0.88    inference(superposition,[],[f829,f24])).
% 3.92/0.88  fof(f829,plain,(
% 3.92/0.88    k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k4_xboole_0(sK2,sK0),sK2) | ~spl4_32),
% 3.92/0.88    inference(avatar_component_clause,[],[f827])).
% 3.92/0.88  fof(f1849,plain,(
% 3.92/0.88    spl4_52 | ~spl4_31),
% 3.92/0.88    inference(avatar_split_clause,[],[f1050,f822,f1846])).
% 3.92/0.88  fof(f1846,plain,(
% 3.92/0.88    spl4_52 <=> k4_xboole_0(sK3,sK2) = k4_xboole_0(sK3,k2_xboole_0(sK1,sK2))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 3.92/0.88  fof(f822,plain,(
% 3.92/0.88    spl4_31 <=> k4_xboole_0(sK3,sK2) = k4_xboole_0(k4_xboole_0(sK3,sK1),sK2)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 3.92/0.88  fof(f1050,plain,(
% 3.92/0.88    k4_xboole_0(sK3,sK2) = k4_xboole_0(sK3,k2_xboole_0(sK1,sK2)) | ~spl4_31),
% 3.92/0.88    inference(superposition,[],[f824,f24])).
% 3.92/0.88  fof(f824,plain,(
% 3.92/0.88    k4_xboole_0(sK3,sK2) = k4_xboole_0(k4_xboole_0(sK3,sK1),sK2) | ~spl4_31),
% 3.92/0.88    inference(avatar_component_clause,[],[f822])).
% 3.92/0.88  fof(f1844,plain,(
% 3.92/0.88    spl4_51 | ~spl4_4 | ~spl4_30),
% 3.92/0.88    inference(avatar_split_clause,[],[f1023,f802,f41,f1841])).
% 3.92/0.88  fof(f1841,plain,(
% 3.92/0.88    spl4_51 <=> k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 3.92/0.88  fof(f802,plain,(
% 3.92/0.88    spl4_30 <=> k4_xboole_0(k4_xboole_0(sK1,sK3),sK2) = k4_xboole_0(sK1,sK2)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 3.92/0.88  fof(f1023,plain,(
% 3.92/0.88    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) | (~spl4_4 | ~spl4_30)),
% 3.92/0.88    inference(forward_demodulation,[],[f1022,f43])).
% 3.92/0.88  fof(f1022,plain,(
% 3.92/0.88    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | ~spl4_30),
% 3.92/0.88    inference(forward_demodulation,[],[f1014,f20])).
% 3.92/0.88  fof(f1014,plain,(
% 3.92/0.88    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK3,sK2)) | ~spl4_30),
% 3.92/0.88    inference(superposition,[],[f804,f24])).
% 3.92/0.88  fof(f804,plain,(
% 3.92/0.88    k4_xboole_0(k4_xboole_0(sK1,sK3),sK2) = k4_xboole_0(sK1,sK2) | ~spl4_30),
% 3.92/0.88    inference(avatar_component_clause,[],[f802])).
% 3.92/0.88  fof(f1839,plain,(
% 3.92/0.88    spl4_50 | ~spl4_29),
% 3.92/0.88    inference(avatar_split_clause,[],[f987,f797,f1836])).
% 3.92/0.88  fof(f1836,plain,(
% 3.92/0.88    spl4_50 <=> k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK2))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 3.92/0.88  fof(f797,plain,(
% 3.92/0.88    spl4_29 <=> k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK2)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 3.92/0.88  fof(f987,plain,(
% 3.92/0.88    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK2)) | ~spl4_29),
% 3.92/0.88    inference(superposition,[],[f799,f24])).
% 3.92/0.88  fof(f799,plain,(
% 3.92/0.88    k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK2) | ~spl4_29),
% 3.92/0.88    inference(avatar_component_clause,[],[f797])).
% 3.92/0.88  fof(f1734,plain,(
% 3.92/0.88    spl4_49 | ~spl4_12 | ~spl4_24),
% 3.92/0.88    inference(avatar_split_clause,[],[f790,f564,f113,f1731])).
% 3.92/0.88  fof(f1731,plain,(
% 3.92/0.88    spl4_49 <=> k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK3),sK1)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 3.92/0.88  fof(f564,plain,(
% 3.92/0.88    spl4_24 <=> k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK1,sK1)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 3.92/0.88  fof(f790,plain,(
% 3.92/0.88    k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK3),sK1) | (~spl4_12 | ~spl4_24)),
% 3.92/0.88    inference(forward_demodulation,[],[f773,f566])).
% 3.92/0.88  fof(f566,plain,(
% 3.92/0.88    k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK1,sK1) | ~spl4_24),
% 3.92/0.88    inference(avatar_component_clause,[],[f564])).
% 3.92/0.88  fof(f773,plain,(
% 3.92/0.88    k4_xboole_0(sK1,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK3),sK1) | ~spl4_12),
% 3.92/0.88    inference(superposition,[],[f548,f115])).
% 3.92/0.88  fof(f548,plain,(
% 3.92/0.88    ( ! [X0] : (k4_xboole_0(X0,sK1) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),sK1)) ) | ~spl4_12),
% 3.92/0.88    inference(superposition,[],[f332,f20])).
% 3.92/0.88  fof(f332,plain,(
% 3.92/0.88    ( ! [X16] : (k4_xboole_0(X16,sK1) = k4_xboole_0(k2_xboole_0(X16,k1_xboole_0),sK1)) ) | ~spl4_12),
% 3.92/0.88    inference(superposition,[],[f104,f115])).
% 3.92/0.88  fof(f1680,plain,(
% 3.92/0.88    spl4_48 | ~spl4_10 | ~spl4_12),
% 3.92/0.88    inference(avatar_split_clause,[],[f775,f113,f95,f1677])).
% 3.92/0.88  fof(f1677,plain,(
% 3.92/0.88    spl4_48 <=> k4_xboole_0(sK3,sK1) = k4_xboole_0(k4_xboole_0(sK3,sK1),sK1)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 3.92/0.88  fof(f775,plain,(
% 3.92/0.88    k4_xboole_0(sK3,sK1) = k4_xboole_0(k4_xboole_0(sK3,sK1),sK1) | (~spl4_10 | ~spl4_12)),
% 3.92/0.88    inference(superposition,[],[f548,f97])).
% 3.92/0.88  fof(f1675,plain,(
% 3.92/0.88    spl4_47 | ~spl4_9 | ~spl4_12),
% 3.92/0.88    inference(avatar_split_clause,[],[f774,f113,f90,f1672])).
% 3.92/0.88  fof(f774,plain,(
% 3.92/0.88    k4_xboole_0(k4_xboole_0(sK2,sK0),sK1) = k4_xboole_0(sK2,sK1) | (~spl4_9 | ~spl4_12)),
% 3.92/0.88    inference(superposition,[],[f548,f92])).
% 3.92/0.88  fof(f1548,plain,(
% 3.92/0.88    spl4_46 | ~spl4_11 | ~spl4_12),
% 3.92/0.88    inference(avatar_split_clause,[],[f772,f113,f108,f1545])).
% 3.92/0.88  fof(f1545,plain,(
% 3.92/0.88    spl4_46 <=> k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) = k4_xboole_0(sK0,sK1)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 3.92/0.88  fof(f772,plain,(
% 3.92/0.88    k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) = k4_xboole_0(sK0,sK1) | (~spl4_11 | ~spl4_12)),
% 3.92/0.88    inference(superposition,[],[f548,f110])).
% 3.92/0.88  fof(f1543,plain,(
% 3.92/0.88    spl4_45 | ~spl4_11 | ~spl4_23),
% 3.92/0.88    inference(avatar_split_clause,[],[f766,f489,f108,f1540])).
% 3.92/0.88  fof(f1540,plain,(
% 3.92/0.88    spl4_45 <=> k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK0)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 3.92/0.88  fof(f489,plain,(
% 3.92/0.88    spl4_23 <=> k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(sK0,sK0)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 3.92/0.88  fof(f766,plain,(
% 3.92/0.88    k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK0) | (~spl4_11 | ~spl4_23)),
% 3.92/0.88    inference(forward_demodulation,[],[f748,f491])).
% 3.92/0.88  fof(f491,plain,(
% 3.92/0.88    k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(sK0,sK0) | ~spl4_23),
% 3.92/0.88    inference(avatar_component_clause,[],[f489])).
% 3.92/0.88  fof(f748,plain,(
% 3.92/0.88    k4_xboole_0(sK0,sK0) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK0) | ~spl4_11),
% 3.92/0.88    inference(superposition,[],[f473,f110])).
% 3.92/0.88  fof(f473,plain,(
% 3.92/0.88    ( ! [X0] : (k4_xboole_0(X0,sK0) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),sK0)) ) | ~spl4_11),
% 3.92/0.88    inference(superposition,[],[f331,f20])).
% 3.92/0.88  fof(f331,plain,(
% 3.92/0.88    ( ! [X15] : (k4_xboole_0(X15,sK0) = k4_xboole_0(k2_xboole_0(X15,k1_xboole_0),sK0)) ) | ~spl4_11),
% 3.92/0.88    inference(superposition,[],[f104,f110])).
% 3.92/0.88  fof(f1493,plain,(
% 3.92/0.88    spl4_44 | ~spl4_10 | ~spl4_11),
% 3.92/0.88    inference(avatar_split_clause,[],[f751,f108,f95,f1490])).
% 3.92/0.88  fof(f1490,plain,(
% 3.92/0.88    spl4_44 <=> k4_xboole_0(k4_xboole_0(sK3,sK1),sK0) = k4_xboole_0(sK3,sK0)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 3.92/0.88  fof(f751,plain,(
% 3.92/0.88    k4_xboole_0(k4_xboole_0(sK3,sK1),sK0) = k4_xboole_0(sK3,sK0) | (~spl4_10 | ~spl4_11)),
% 3.92/0.88    inference(superposition,[],[f473,f97])).
% 3.92/0.88  fof(f1362,plain,(
% 3.92/0.88    spl4_43 | ~spl4_9 | ~spl4_11),
% 3.92/0.88    inference(avatar_split_clause,[],[f750,f108,f90,f1359])).
% 3.92/0.88  fof(f1359,plain,(
% 3.92/0.88    spl4_43 <=> k4_xboole_0(sK2,sK0) = k4_xboole_0(k4_xboole_0(sK2,sK0),sK0)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 3.92/0.88  fof(f750,plain,(
% 3.92/0.88    k4_xboole_0(sK2,sK0) = k4_xboole_0(k4_xboole_0(sK2,sK0),sK0) | (~spl4_9 | ~spl4_11)),
% 3.92/0.88    inference(superposition,[],[f473,f92])).
% 3.92/0.88  fof(f1357,plain,(
% 3.92/0.88    spl4_42 | ~spl4_11 | ~spl4_12),
% 3.92/0.88    inference(avatar_split_clause,[],[f749,f113,f108,f1354])).
% 3.92/0.88  fof(f1354,plain,(
% 3.92/0.88    spl4_42 <=> k4_xboole_0(k4_xboole_0(sK1,sK3),sK0) = k4_xboole_0(sK1,sK0)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 3.92/0.88  fof(f749,plain,(
% 3.92/0.88    k4_xboole_0(k4_xboole_0(sK1,sK3),sK0) = k4_xboole_0(sK1,sK0) | (~spl4_11 | ~spl4_12)),
% 3.92/0.88    inference(superposition,[],[f473,f115])).
% 3.92/0.88  fof(f1352,plain,(
% 3.92/0.88    spl4_41 | ~spl4_24),
% 3.92/0.88    inference(avatar_split_clause,[],[f571,f564,f1349])).
% 3.92/0.88  fof(f1349,plain,(
% 3.92/0.88    spl4_41 <=> sK1 = k2_xboole_0(k3_xboole_0(sK1,sK1),k4_xboole_0(k1_xboole_0,sK1))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 3.92/0.88  fof(f571,plain,(
% 3.92/0.88    sK1 = k2_xboole_0(k3_xboole_0(sK1,sK1),k4_xboole_0(k1_xboole_0,sK1)) | ~spl4_24),
% 3.92/0.88    inference(superposition,[],[f80,f566])).
% 3.92/0.88  fof(f1335,plain,(
% 3.92/0.88    spl4_40 | ~spl4_4 | ~spl4_23 | ~spl4_38),
% 3.92/0.88    inference(avatar_split_clause,[],[f1322,f1035,f489,f41,f1332])).
% 3.92/0.88  fof(f1332,plain,(
% 3.92/0.88    spl4_40 <=> k4_xboole_0(sK1,sK2) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 3.92/0.88  fof(f1322,plain,(
% 3.92/0.88    k4_xboole_0(sK1,sK2) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)) | (~spl4_4 | ~spl4_23 | ~spl4_38)),
% 3.92/0.88    inference(forward_demodulation,[],[f1321,f1037])).
% 3.92/0.88  fof(f1321,plain,(
% 3.92/0.88    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)) | (~spl4_4 | ~spl4_23)),
% 3.92/0.88    inference(forward_demodulation,[],[f1300,f499])).
% 3.92/0.88  fof(f499,plain,(
% 3.92/0.88    ( ! [X1] : (k4_xboole_0(sK0,k2_xboole_0(sK0,X1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X1))) ) | ~spl4_23),
% 3.92/0.88    inference(forward_demodulation,[],[f497,f24])).
% 3.92/0.88  fof(f497,plain,(
% 3.92/0.88    ( ! [X1] : (k4_xboole_0(sK0,k2_xboole_0(sK0,X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,sK0),X1)) ) | ~spl4_23),
% 3.92/0.88    inference(superposition,[],[f24,f491])).
% 3.92/0.88  fof(f1300,plain,(
% 3.92/0.88    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) | ~spl4_4),
% 3.92/0.88    inference(superposition,[],[f138,f335])).
% 3.92/0.88  fof(f335,plain,(
% 3.92/0.88    ( ! [X19] : (k4_xboole_0(X19,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(X19,sK2),k2_xboole_0(sK0,sK1))) ) | ~spl4_4),
% 3.92/0.88    inference(superposition,[],[f104,f43])).
% 3.92/0.88  fof(f138,plain,(
% 3.92/0.88    ( ! [X2,X3,X1] : (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k4_xboole_0(X2,k2_xboole_0(X1,X3))) )),
% 3.92/0.88    inference(forward_demodulation,[],[f136,f24])).
% 3.92/0.88  fof(f136,plain,(
% 3.92/0.88    ( ! [X2,X3,X1] : (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k4_xboole_0(k4_xboole_0(X2,X1),X3)) )),
% 3.92/0.88    inference(superposition,[],[f24,f60])).
% 3.92/0.88  fof(f60,plain,(
% 3.92/0.88    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 3.92/0.88    inference(superposition,[],[f21,f20])).
% 3.92/0.88  fof(f1271,plain,(
% 3.92/0.88    spl4_39 | ~spl4_23),
% 3.92/0.88    inference(avatar_split_clause,[],[f496,f489,f1268])).
% 3.92/0.88  fof(f1268,plain,(
% 3.92/0.88    spl4_39 <=> sK0 = k2_xboole_0(k3_xboole_0(sK0,sK0),k4_xboole_0(k1_xboole_0,sK0))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 3.92/0.88  fof(f496,plain,(
% 3.92/0.88    sK0 = k2_xboole_0(k3_xboole_0(sK0,sK0),k4_xboole_0(k1_xboole_0,sK0)) | ~spl4_23),
% 3.92/0.88    inference(superposition,[],[f80,f491])).
% 3.92/0.88  fof(f1038,plain,(
% 3.92/0.88    spl4_38 | ~spl4_4 | ~spl4_30),
% 3.92/0.88    inference(avatar_split_clause,[],[f1024,f802,f41,f1035])).
% 3.92/0.88  fof(f1024,plain,(
% 3.92/0.88    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | (~spl4_4 | ~spl4_30)),
% 3.92/0.88    inference(backward_demodulation,[],[f925,f1023])).
% 3.92/0.88  fof(f925,plain,(
% 3.92/0.88    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) | ~spl4_4),
% 3.92/0.88    inference(forward_demodulation,[],[f916,f138])).
% 3.92/0.88  fof(f916,plain,(
% 3.92/0.88    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) | ~spl4_4),
% 3.92/0.88    inference(superposition,[],[f335,f60])).
% 3.92/0.88  fof(f855,plain,(
% 3.92/0.88    spl4_37 | ~spl4_10 | ~spl4_22),
% 3.92/0.88    inference(avatar_split_clause,[],[f610,f383,f95,f852])).
% 3.92/0.88  fof(f610,plain,(
% 3.92/0.88    k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(k4_xboole_0(sK3,sK1),sK3) | (~spl4_10 | ~spl4_22)),
% 3.92/0.88    inference(forward_demodulation,[],[f599,f385])).
% 3.92/0.88  fof(f599,plain,(
% 3.92/0.88    k4_xboole_0(sK3,sK3) = k4_xboole_0(k4_xboole_0(sK3,sK1),sK3) | ~spl4_10),
% 3.92/0.88    inference(superposition,[],[f369,f97])).
% 3.92/0.88  fof(f369,plain,(
% 3.92/0.88    ( ! [X0] : (k4_xboole_0(X0,sK3) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),sK3)) ) | ~spl4_10),
% 3.92/0.88    inference(superposition,[],[f334,f20])).
% 3.92/0.88  fof(f334,plain,(
% 3.92/0.88    ( ! [X18] : (k4_xboole_0(X18,sK3) = k4_xboole_0(k2_xboole_0(X18,k1_xboole_0),sK3)) ) | ~spl4_10),
% 3.92/0.88    inference(superposition,[],[f104,f97])).
% 3.92/0.88  fof(f850,plain,(
% 3.92/0.88    spl4_36 | ~spl4_13),
% 3.92/0.88    inference(avatar_split_clause,[],[f127,f120,f847])).
% 3.92/0.88  fof(f847,plain,(
% 3.92/0.88    spl4_36 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k3_xboole_0(sK3,k2_xboole_0(sK0,sK1)),k4_xboole_0(sK2,sK3))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 3.92/0.88  fof(f120,plain,(
% 3.92/0.88    spl4_13 <=> k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 3.92/0.88  fof(f127,plain,(
% 3.92/0.88    k2_xboole_0(sK0,sK1) = k2_xboole_0(k3_xboole_0(sK3,k2_xboole_0(sK0,sK1)),k4_xboole_0(sK2,sK3)) | ~spl4_13),
% 3.92/0.88    inference(forward_demodulation,[],[f125,f19])).
% 3.92/0.88  fof(f125,plain,(
% 3.92/0.88    k2_xboole_0(sK0,sK1) = k2_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),sK3),k4_xboole_0(sK2,sK3)) | ~spl4_13),
% 3.92/0.88    inference(superposition,[],[f22,f122])).
% 3.92/0.88  fof(f122,plain,(
% 3.92/0.88    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) | ~spl4_13),
% 3.92/0.88    inference(avatar_component_clause,[],[f120])).
% 3.92/0.88  fof(f845,plain,(
% 3.92/0.88    spl4_35 | ~spl4_9 | ~spl4_10),
% 3.92/0.88    inference(avatar_split_clause,[],[f598,f95,f90,f842])).
% 3.92/0.88  fof(f598,plain,(
% 3.92/0.88    k4_xboole_0(sK2,sK3) = k4_xboole_0(k4_xboole_0(sK2,sK0),sK3) | (~spl4_9 | ~spl4_10)),
% 3.92/0.88    inference(superposition,[],[f369,f92])).
% 3.92/0.88  fof(f840,plain,(
% 3.92/0.88    spl4_34 | ~spl4_10 | ~spl4_12),
% 3.92/0.88    inference(avatar_split_clause,[],[f597,f113,f95,f837])).
% 3.92/0.88  fof(f597,plain,(
% 3.92/0.88    k4_xboole_0(sK1,sK3) = k4_xboole_0(k4_xboole_0(sK1,sK3),sK3) | (~spl4_10 | ~spl4_12)),
% 3.92/0.88    inference(superposition,[],[f369,f115])).
% 3.92/0.88  fof(f835,plain,(
% 3.92/0.88    spl4_33 | ~spl4_10 | ~spl4_11),
% 3.92/0.88    inference(avatar_split_clause,[],[f596,f108,f95,f832])).
% 3.92/0.88  fof(f596,plain,(
% 3.92/0.88    k4_xboole_0(k4_xboole_0(sK0,sK2),sK3) = k4_xboole_0(sK0,sK3) | (~spl4_10 | ~spl4_11)),
% 3.92/0.88    inference(superposition,[],[f369,f110])).
% 3.92/0.88  fof(f830,plain,(
% 3.92/0.88    spl4_32 | ~spl4_9 | ~spl4_21),
% 3.92/0.88    inference(avatar_split_clause,[],[f590,f359,f90,f827])).
% 3.92/0.88  fof(f590,plain,(
% 3.92/0.88    k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k4_xboole_0(sK2,sK0),sK2) | (~spl4_9 | ~spl4_21)),
% 3.92/0.88    inference(forward_demodulation,[],[f578,f361])).
% 3.92/0.88  fof(f578,plain,(
% 3.92/0.88    k4_xboole_0(sK2,sK2) = k4_xboole_0(k4_xboole_0(sK2,sK0),sK2) | ~spl4_9),
% 3.92/0.88    inference(superposition,[],[f345,f92])).
% 3.92/0.88  fof(f345,plain,(
% 3.92/0.88    ( ! [X0] : (k4_xboole_0(X0,sK2) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),sK2)) ) | ~spl4_9),
% 3.92/0.88    inference(superposition,[],[f333,f20])).
% 3.92/0.88  fof(f333,plain,(
% 3.92/0.88    ( ! [X17] : (k4_xboole_0(X17,sK2) = k4_xboole_0(k2_xboole_0(X17,k1_xboole_0),sK2)) ) | ~spl4_9),
% 3.92/0.88    inference(superposition,[],[f104,f92])).
% 3.92/0.88  fof(f825,plain,(
% 3.92/0.88    spl4_31 | ~spl4_9 | ~spl4_10),
% 3.92/0.88    inference(avatar_split_clause,[],[f579,f95,f90,f822])).
% 3.92/0.88  fof(f579,plain,(
% 3.92/0.88    k4_xboole_0(sK3,sK2) = k4_xboole_0(k4_xboole_0(sK3,sK1),sK2) | (~spl4_9 | ~spl4_10)),
% 3.92/0.88    inference(superposition,[],[f345,f97])).
% 3.92/0.88  fof(f805,plain,(
% 3.92/0.88    spl4_30 | ~spl4_9 | ~spl4_12),
% 3.92/0.88    inference(avatar_split_clause,[],[f577,f113,f90,f802])).
% 3.92/0.88  fof(f577,plain,(
% 3.92/0.88    k4_xboole_0(k4_xboole_0(sK1,sK3),sK2) = k4_xboole_0(sK1,sK2) | (~spl4_9 | ~spl4_12)),
% 3.92/0.88    inference(superposition,[],[f345,f115])).
% 3.92/0.88  fof(f800,plain,(
% 3.92/0.88    spl4_29 | ~spl4_9 | ~spl4_11),
% 3.92/0.88    inference(avatar_split_clause,[],[f576,f108,f90,f797])).
% 3.92/0.88  fof(f576,plain,(
% 3.92/0.88    k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK2) | (~spl4_9 | ~spl4_11)),
% 3.92/0.88    inference(superposition,[],[f345,f110])).
% 3.92/0.88  fof(f747,plain,(
% 3.92/0.88    spl4_28 | ~spl4_22),
% 3.92/0.88    inference(avatar_split_clause,[],[f457,f383,f744])).
% 3.92/0.88  fof(f744,plain,(
% 3.92/0.88    spl4_28 <=> sK3 = k2_xboole_0(k3_xboole_0(sK3,sK3),k4_xboole_0(k1_xboole_0,sK3))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 3.92/0.88  fof(f457,plain,(
% 3.92/0.88    sK3 = k2_xboole_0(k3_xboole_0(sK3,sK3),k4_xboole_0(k1_xboole_0,sK3)) | ~spl4_22),
% 3.92/0.88    inference(superposition,[],[f80,f385])).
% 3.92/0.88  fof(f711,plain,(
% 3.92/0.88    spl4_27 | ~spl4_21),
% 3.92/0.88    inference(avatar_split_clause,[],[f365,f359,f708])).
% 3.92/0.88  fof(f708,plain,(
% 3.92/0.88    spl4_27 <=> sK2 = k2_xboole_0(k3_xboole_0(sK2,sK2),k4_xboole_0(k1_xboole_0,sK2))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 3.92/0.88  fof(f365,plain,(
% 3.92/0.88    sK2 = k2_xboole_0(k3_xboole_0(sK2,sK2),k4_xboole_0(k1_xboole_0,sK2)) | ~spl4_21),
% 3.92/0.88    inference(superposition,[],[f80,f361])).
% 3.92/0.88  fof(f706,plain,(
% 3.92/0.88    spl4_26 | ~spl4_18),
% 3.92/0.88    inference(avatar_split_clause,[],[f301,f224,f703])).
% 3.92/0.88  fof(f703,plain,(
% 3.92/0.88    spl4_26 <=> k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,k2_xboole_0(k1_xboole_0,sK3))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 3.92/0.88  fof(f301,plain,(
% 3.92/0.88    k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,k2_xboole_0(k1_xboole_0,sK3)) | ~spl4_18),
% 3.92/0.88    inference(forward_demodulation,[],[f294,f20])).
% 3.92/0.88  fof(f294,plain,(
% 3.92/0.88    k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,k2_xboole_0(sK3,k1_xboole_0)) | ~spl4_18),
% 3.92/0.88    inference(superposition,[],[f226,f24])).
% 3.92/0.88  fof(f701,plain,(
% 3.92/0.88    spl4_25 | ~spl4_17),
% 3.92/0.88    inference(avatar_split_clause,[],[f286,f219,f698])).
% 3.92/0.88  fof(f698,plain,(
% 3.92/0.88    spl4_25 <=> k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 3.92/0.88  fof(f286,plain,(
% 3.92/0.88    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2)) | ~spl4_17),
% 3.92/0.88    inference(forward_demodulation,[],[f279,f20])).
% 3.92/0.88  fof(f279,plain,(
% 3.92/0.88    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k2_xboole_0(sK2,k1_xboole_0)) | ~spl4_17),
% 3.92/0.88    inference(superposition,[],[f221,f24])).
% 3.92/0.88  fof(f567,plain,(
% 3.92/0.88    spl4_24 | ~spl4_12),
% 3.92/0.88    inference(avatar_split_clause,[],[f550,f113,f564])).
% 3.92/0.88  fof(f550,plain,(
% 3.92/0.88    k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK1,sK1) | ~spl4_12),
% 3.92/0.88    inference(superposition,[],[f332,f60])).
% 3.92/0.88  fof(f492,plain,(
% 3.92/0.88    spl4_23 | ~spl4_11),
% 3.92/0.88    inference(avatar_split_clause,[],[f475,f108,f489])).
% 3.92/0.88  fof(f475,plain,(
% 3.92/0.88    k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(sK0,sK0) | ~spl4_11),
% 3.92/0.88    inference(superposition,[],[f331,f60])).
% 3.92/0.88  fof(f386,plain,(
% 3.92/0.88    spl4_22 | ~spl4_10),
% 3.92/0.88    inference(avatar_split_clause,[],[f371,f95,f383])).
% 3.92/0.88  fof(f371,plain,(
% 3.92/0.88    k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK3,sK3) | ~spl4_10),
% 3.92/0.88    inference(superposition,[],[f334,f60])).
% 3.92/0.88  fof(f362,plain,(
% 3.92/0.88    spl4_21 | ~spl4_9),
% 3.92/0.88    inference(avatar_split_clause,[],[f347,f90,f359])).
% 3.92/0.88  fof(f347,plain,(
% 3.92/0.88    k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK2,sK2) | ~spl4_9),
% 3.92/0.88    inference(superposition,[],[f333,f60])).
% 3.92/0.88  fof(f278,plain,(
% 3.92/0.88    spl4_20 | ~spl4_16),
% 3.92/0.88    inference(avatar_split_clause,[],[f212,f190,f275])).
% 3.92/0.88  fof(f275,plain,(
% 3.92/0.88    spl4_20 <=> k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,k2_xboole_0(k1_xboole_0,sK1))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 3.92/0.88  fof(f212,plain,(
% 3.92/0.88    k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,k2_xboole_0(k1_xboole_0,sK1)) | ~spl4_16),
% 3.92/0.88    inference(forward_demodulation,[],[f206,f20])).
% 3.92/0.88  fof(f206,plain,(
% 3.92/0.88    k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,k2_xboole_0(sK1,k1_xboole_0)) | ~spl4_16),
% 3.92/0.88    inference(superposition,[],[f192,f24])).
% 3.92/0.88  fof(f273,plain,(
% 3.92/0.88    spl4_19 | ~spl4_15),
% 3.92/0.88    inference(avatar_split_clause,[],[f200,f163,f270])).
% 3.92/0.88  fof(f270,plain,(
% 3.92/0.88    spl4_19 <=> k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK0))),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 3.92/0.88  fof(f200,plain,(
% 3.92/0.88    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK0)) | ~spl4_15),
% 3.92/0.88    inference(forward_demodulation,[],[f194,f20])).
% 3.92/0.88  fof(f194,plain,(
% 3.92/0.88    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k2_xboole_0(sK0,k1_xboole_0)) | ~spl4_15),
% 3.92/0.88    inference(superposition,[],[f165,f24])).
% 3.92/0.88  fof(f227,plain,(
% 3.92/0.88    spl4_18 | ~spl4_12),
% 3.92/0.88    inference(avatar_split_clause,[],[f132,f113,f224])).
% 3.92/0.88  fof(f132,plain,(
% 3.92/0.88    k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) = k4_xboole_0(sK1,k1_xboole_0) | ~spl4_12),
% 3.92/0.88    inference(superposition,[],[f60,f115])).
% 3.92/0.88  fof(f222,plain,(
% 3.92/0.88    spl4_17 | ~spl4_11),
% 3.92/0.88    inference(avatar_split_clause,[],[f131,f108,f219])).
% 3.92/0.88  fof(f131,plain,(
% 3.92/0.88    k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = k4_xboole_0(sK0,k1_xboole_0) | ~spl4_11),
% 3.92/0.88    inference(superposition,[],[f60,f110])).
% 3.92/0.88  fof(f193,plain,(
% 3.92/0.88    spl4_16 | ~spl4_10),
% 3.92/0.88    inference(avatar_split_clause,[],[f134,f95,f190])).
% 3.92/0.88  fof(f134,plain,(
% 3.92/0.88    k4_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) = k4_xboole_0(sK3,k1_xboole_0) | ~spl4_10),
% 3.92/0.88    inference(superposition,[],[f60,f97])).
% 3.92/0.88  fof(f166,plain,(
% 3.92/0.88    spl4_15 | ~spl4_9),
% 3.92/0.88    inference(avatar_split_clause,[],[f133,f90,f163])).
% 3.92/0.88  fof(f133,plain,(
% 3.92/0.88    k4_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) = k4_xboole_0(sK2,k1_xboole_0) | ~spl4_9),
% 3.92/0.88    inference(superposition,[],[f60,f92])).
% 3.92/0.88  fof(f156,plain,(
% 3.92/0.88    spl4_14 | ~spl4_4),
% 3.92/0.88    inference(avatar_split_clause,[],[f135,f41,f153])).
% 3.92/0.88  fof(f153,plain,(
% 3.92/0.88    spl4_14 <=> k4_xboole_0(sK3,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 3.92/0.88  fof(f135,plain,(
% 3.92/0.88    k4_xboole_0(sK3,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) | ~spl4_4),
% 3.92/0.88    inference(superposition,[],[f60,f43])).
% 3.92/0.88  fof(f123,plain,(
% 3.92/0.88    spl4_13 | ~spl4_4),
% 3.92/0.88    inference(avatar_split_clause,[],[f59,f41,f120])).
% 3.92/0.88  fof(f59,plain,(
% 3.92/0.88    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) | ~spl4_4),
% 3.92/0.88    inference(superposition,[],[f21,f43])).
% 3.92/0.88  fof(f116,plain,(
% 3.92/0.88    spl4_12 | ~spl4_8),
% 3.92/0.88    inference(avatar_split_clause,[],[f88,f76,f113])).
% 3.92/0.88  fof(f76,plain,(
% 3.92/0.88    spl4_8 <=> k1_xboole_0 = k3_xboole_0(sK1,sK3)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 3.92/0.88  fof(f88,plain,(
% 3.92/0.88    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) | ~spl4_8),
% 3.92/0.88    inference(superposition,[],[f22,f78])).
% 3.92/0.88  fof(f78,plain,(
% 3.92/0.88    k1_xboole_0 = k3_xboole_0(sK1,sK3) | ~spl4_8),
% 3.92/0.88    inference(avatar_component_clause,[],[f76])).
% 3.92/0.88  fof(f111,plain,(
% 3.92/0.88    spl4_11 | ~spl4_7),
% 3.92/0.88    inference(avatar_split_clause,[],[f82,f71,f108])).
% 3.92/0.88  fof(f71,plain,(
% 3.92/0.88    spl4_7 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 3.92/0.88  fof(f82,plain,(
% 3.92/0.88    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) | ~spl4_7),
% 3.92/0.88    inference(superposition,[],[f22,f73])).
% 3.92/0.88  fof(f73,plain,(
% 3.92/0.88    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl4_7),
% 3.92/0.88    inference(avatar_component_clause,[],[f71])).
% 3.92/0.88  fof(f98,plain,(
% 3.92/0.88    spl4_10 | ~spl4_6),
% 3.92/0.88    inference(avatar_split_clause,[],[f84,f55,f95])).
% 3.92/0.88  fof(f55,plain,(
% 3.92/0.88    spl4_6 <=> k1_xboole_0 = k3_xboole_0(sK3,sK1)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 3.92/0.88  fof(f84,plain,(
% 3.92/0.88    sK3 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) | ~spl4_6),
% 3.92/0.88    inference(superposition,[],[f22,f57])).
% 3.92/0.88  fof(f57,plain,(
% 3.92/0.88    k1_xboole_0 = k3_xboole_0(sK3,sK1) | ~spl4_6),
% 3.92/0.88    inference(avatar_component_clause,[],[f55])).
% 3.92/0.88  fof(f93,plain,(
% 3.92/0.88    spl4_9 | ~spl4_5),
% 3.92/0.88    inference(avatar_split_clause,[],[f83,f50,f90])).
% 3.92/0.88  fof(f50,plain,(
% 3.92/0.88    spl4_5 <=> k1_xboole_0 = k3_xboole_0(sK2,sK0)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 3.92/0.88  fof(f83,plain,(
% 3.92/0.88    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) | ~spl4_5),
% 3.92/0.88    inference(superposition,[],[f22,f52])).
% 3.92/0.88  fof(f52,plain,(
% 3.92/0.88    k1_xboole_0 = k3_xboole_0(sK2,sK0) | ~spl4_5),
% 3.92/0.88    inference(avatar_component_clause,[],[f50])).
% 3.92/0.88  fof(f79,plain,(
% 3.92/0.88    spl4_8 | ~spl4_6),
% 3.92/0.88    inference(avatar_split_clause,[],[f66,f55,f76])).
% 3.92/0.88  fof(f66,plain,(
% 3.92/0.88    k1_xboole_0 = k3_xboole_0(sK1,sK3) | ~spl4_6),
% 3.92/0.88    inference(superposition,[],[f57,f19])).
% 3.92/0.88  fof(f74,plain,(
% 3.92/0.88    spl4_7 | ~spl4_5),
% 3.92/0.88    inference(avatar_split_clause,[],[f62,f50,f71])).
% 3.92/0.88  fof(f62,plain,(
% 3.92/0.88    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl4_5),
% 3.92/0.88    inference(superposition,[],[f52,f19])).
% 3.92/0.88  fof(f58,plain,(
% 3.92/0.88    spl4_6 | ~spl4_2),
% 3.92/0.88    inference(avatar_split_clause,[],[f46,f31,f55])).
% 3.92/0.88  fof(f31,plain,(
% 3.92/0.88    spl4_2 <=> r1_xboole_0(sK3,sK1)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 3.92/0.88  fof(f46,plain,(
% 3.92/0.88    k1_xboole_0 = k3_xboole_0(sK3,sK1) | ~spl4_2),
% 3.92/0.88    inference(unit_resulting_resolution,[],[f33,f23])).
% 3.92/0.88  fof(f23,plain,(
% 3.92/0.88    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 3.92/0.88    inference(cnf_transformation,[],[f12])).
% 3.92/0.88  fof(f12,plain,(
% 3.92/0.88    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 3.92/0.88    inference(ennf_transformation,[],[f9])).
% 3.92/0.88  fof(f9,plain,(
% 3.92/0.88    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.92/0.88    inference(unused_predicate_definition_removal,[],[f3])).
% 3.92/0.88  fof(f3,axiom,(
% 3.92/0.88    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.92/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 3.92/0.88  fof(f33,plain,(
% 3.92/0.88    r1_xboole_0(sK3,sK1) | ~spl4_2),
% 3.92/0.88    inference(avatar_component_clause,[],[f31])).
% 3.92/0.88  fof(f53,plain,(
% 3.92/0.88    spl4_5 | ~spl4_1),
% 3.92/0.88    inference(avatar_split_clause,[],[f45,f26,f50])).
% 3.92/0.88  fof(f26,plain,(
% 3.92/0.88    spl4_1 <=> r1_xboole_0(sK2,sK0)),
% 3.92/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 3.92/0.88  fof(f45,plain,(
% 3.92/0.88    k1_xboole_0 = k3_xboole_0(sK2,sK0) | ~spl4_1),
% 3.92/0.88    inference(unit_resulting_resolution,[],[f28,f23])).
% 3.92/0.88  fof(f28,plain,(
% 3.92/0.88    r1_xboole_0(sK2,sK0) | ~spl4_1),
% 3.92/0.88    inference(avatar_component_clause,[],[f26])).
% 3.92/0.88  fof(f44,plain,(
% 3.92/0.88    spl4_4),
% 3.92/0.88    inference(avatar_split_clause,[],[f15,f41])).
% 3.92/0.88  fof(f15,plain,(
% 3.92/0.88    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 3.92/0.88    inference(cnf_transformation,[],[f14])).
% 3.92/0.88  fof(f14,plain,(
% 3.92/0.88    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 3.92/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f13])).
% 3.92/0.88  fof(f13,plain,(
% 3.92/0.88    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 3.92/0.88    introduced(choice_axiom,[])).
% 3.92/0.88  fof(f11,plain,(
% 3.92/0.88    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 3.92/0.88    inference(flattening,[],[f10])).
% 3.92/0.88  fof(f10,plain,(
% 3.92/0.88    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 3.92/0.88    inference(ennf_transformation,[],[f8])).
% 3.92/0.88  fof(f8,negated_conjecture,(
% 3.92/0.88    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 3.92/0.88    inference(negated_conjecture,[],[f7])).
% 3.92/0.88  fof(f7,conjecture,(
% 3.92/0.88    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 3.92/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 3.92/0.88  fof(f39,plain,(
% 3.92/0.88    ~spl4_3),
% 3.92/0.88    inference(avatar_split_clause,[],[f18,f36])).
% 3.92/0.88  fof(f18,plain,(
% 3.92/0.88    sK1 != sK2),
% 3.92/0.88    inference(cnf_transformation,[],[f14])).
% 3.92/0.88  fof(f34,plain,(
% 3.92/0.88    spl4_2),
% 3.92/0.88    inference(avatar_split_clause,[],[f17,f31])).
% 3.92/0.88  fof(f17,plain,(
% 3.92/0.88    r1_xboole_0(sK3,sK1)),
% 3.92/0.88    inference(cnf_transformation,[],[f14])).
% 3.92/0.88  fof(f29,plain,(
% 3.92/0.88    spl4_1),
% 3.92/0.88    inference(avatar_split_clause,[],[f16,f26])).
% 3.92/0.88  fof(f16,plain,(
% 3.92/0.88    r1_xboole_0(sK2,sK0)),
% 3.92/0.88    inference(cnf_transformation,[],[f14])).
% 3.92/0.88  % SZS output end Proof for theBenchmark
% 3.92/0.88  % (10756)------------------------------
% 3.92/0.88  % (10756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.92/0.88  % (10756)Termination reason: Refutation
% 3.92/0.88  
% 3.92/0.88  % (10756)Memory used [KB]: 5373
% 3.92/0.88  % (10756)Time elapsed: 0.418 s
% 3.92/0.88  % (10756)------------------------------
% 3.92/0.88  % (10756)------------------------------
% 3.92/0.88  % (10745)Success in time 0.519 s
%------------------------------------------------------------------------------
