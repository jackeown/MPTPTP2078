%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0374+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:27 EST 2020

% Result     : Theorem 3.62s
% Output     : Refutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 269 expanded)
%              Number of leaves         :   47 ( 109 expanded)
%              Depth                    :    7
%              Number of atoms          :  366 ( 612 expanded)
%              Number of equality atoms :   73 ( 116 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2190,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1057,f1062,f1067,f1072,f1077,f1082,f1087,f1094,f1115,f1143,f1194,f1222,f1260,f1368,f1406,f1440,f1525,f1620,f1771,f1802,f1889,f1941,f2056,f2093,f2155,f2160,f2162,f2164,f2166,f2189])).

fof(f2189,plain,
    ( spl26_2
    | ~ spl26_11 ),
    inference(avatar_contradiction_clause,[],[f2188])).

fof(f2188,plain,
    ( $false
    | spl26_2
    | ~ spl26_11 ),
    inference(subsumption_resolution,[],[f2187,f1061])).

fof(f1061,plain,
    ( k1_xboole_0 != sK0
    | spl26_2 ),
    inference(avatar_component_clause,[],[f1059])).

fof(f1059,plain,
    ( spl26_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_2])])).

fof(f2187,plain,
    ( k1_xboole_0 = sK0
    | ~ spl26_11 ),
    inference(resolution,[],[f1188,f966])).

fof(f966,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f642])).

fof(f642,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f136])).

fof(f136,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f1188,plain,
    ( v1_xboole_0(sK0)
    | ~ spl26_11 ),
    inference(avatar_component_clause,[],[f1187])).

fof(f1187,plain,
    ( spl26_11
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_11])])).

fof(f2166,plain,
    ( spl26_20
    | ~ spl26_24 ),
    inference(avatar_contradiction_clause,[],[f2165])).

fof(f2165,plain,
    ( $false
    | spl26_20
    | ~ spl26_24 ),
    inference(subsumption_resolution,[],[f1769,f2124])).

fof(f2124,plain,
    ( sK0 = k2_xboole_0(k1_tarski(sK1),sK0)
    | ~ spl26_24 ),
    inference(resolution,[],[f2055,f889])).

fof(f889,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f610])).

fof(f610,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f2055,plain,
    ( r1_tarski(k1_tarski(sK1),sK0)
    | ~ spl26_24 ),
    inference(avatar_component_clause,[],[f2053])).

fof(f2053,plain,
    ( spl26_24
  <=> r1_tarski(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_24])])).

fof(f1769,plain,
    ( sK0 != k2_xboole_0(k1_tarski(sK1),sK0)
    | spl26_20 ),
    inference(avatar_component_clause,[],[f1768])).

fof(f1768,plain,
    ( spl26_20
  <=> sK0 = k2_xboole_0(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_20])])).

fof(f2164,plain,
    ( spl26_22
    | ~ spl26_24 ),
    inference(avatar_contradiction_clause,[],[f2163])).

fof(f2163,plain,
    ( $false
    | spl26_22
    | ~ spl26_24 ),
    inference(subsumption_resolution,[],[f2122,f1887])).

fof(f1887,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK1),sK0)
    | spl26_22 ),
    inference(avatar_component_clause,[],[f1886])).

fof(f1886,plain,
    ( spl26_22
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_22])])).

fof(f2122,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),sK0)
    | ~ spl26_24 ),
    inference(resolution,[],[f2055,f936])).

fof(f936,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f2162,plain,
    ( ~ spl26_20
    | spl26_22 ),
    inference(avatar_contradiction_clause,[],[f2161])).

fof(f2161,plain,
    ( $false
    | ~ spl26_20
    | spl26_22 ),
    inference(subsumption_resolution,[],[f1887,f1842])).

fof(f1842,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),sK0)
    | ~ spl26_20 ),
    inference(forward_demodulation,[],[f1834,f1168])).

fof(f1168,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f960,f908])).

fof(f908,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f520])).

fof(f520,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f960,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f1834,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK0) = k4_xboole_0(sK0,sK0)
    | ~ spl26_20 ),
    inference(superposition,[],[f901,f1770])).

fof(f1770,plain,
    ( sK0 = k2_xboole_0(k1_tarski(sK1),sK0)
    | ~ spl26_20 ),
    inference(avatar_component_clause,[],[f1768])).

fof(f901,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f2160,plain,
    ( spl26_17
    | ~ spl26_22 ),
    inference(avatar_contradiction_clause,[],[f2159])).

fof(f2159,plain,
    ( $false
    | spl26_17
    | ~ spl26_22 ),
    inference(subsumption_resolution,[],[f1438,f2027])).

fof(f2027,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl26_22 ),
    inference(trivial_inequality_removal,[],[f2014])).

fof(f2014,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK1,sK0)
    | ~ spl26_22 ),
    inference(superposition,[],[f933,f1888])).

fof(f1888,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),sK0)
    | ~ spl26_22 ),
    inference(avatar_component_clause,[],[f1886])).

fof(f933,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f424])).

fof(f424,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f1438,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl26_17 ),
    inference(avatar_component_clause,[],[f1437])).

fof(f1437,plain,
    ( spl26_17
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_17])])).

fof(f2155,plain,
    ( ~ spl26_16
    | ~ spl26_17
    | spl26_18 ),
    inference(avatar_contradiction_clause,[],[f2154])).

fof(f2154,plain,
    ( $false
    | ~ spl26_16
    | ~ spl26_17
    | spl26_18 ),
    inference(subsumption_resolution,[],[f2153,f1439])).

fof(f1439,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl26_17 ),
    inference(avatar_component_clause,[],[f1437])).

fof(f2153,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl26_16
    | spl26_18 ),
    inference(subsumption_resolution,[],[f2139,f1405])).

fof(f1405,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl26_16 ),
    inference(avatar_component_clause,[],[f1403])).

fof(f1403,plain,
    ( spl26_16
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_16])])).

fof(f2139,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ r2_hidden(sK1,sK0)
    | spl26_18 ),
    inference(resolution,[],[f762,f1524])).

fof(f1524,plain,
    ( ~ r1_tarski(k2_tarski(sK1,sK2),sK0)
    | spl26_18 ),
    inference(avatar_component_clause,[],[f1522])).

fof(f1522,plain,
    ( spl26_18
  <=> r1_tarski(k2_tarski(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_18])])).

fof(f762,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f396])).

fof(f396,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f2093,plain,
    ( ~ spl26_25
    | ~ spl26_22 ),
    inference(avatar_split_clause,[],[f2026,f1886,f2090])).

fof(f2090,plain,
    ( spl26_25
  <=> r2_xboole_0(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_25])])).

fof(f2026,plain,
    ( ~ r2_xboole_0(sK0,k1_tarski(sK1))
    | ~ spl26_22 ),
    inference(trivial_inequality_removal,[],[f2020])).

fof(f2020,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_xboole_0(sK0,k1_tarski(sK1))
    | ~ spl26_22 ),
    inference(superposition,[],[f931,f1888])).

fof(f931,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f630])).

fof(f630,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f53])).

fof(f53,axiom,(
    ! [X0,X1] :
      ~ ( k1_xboole_0 = k4_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).

fof(f2056,plain,
    ( spl26_24
    | ~ spl26_22 ),
    inference(avatar_split_clause,[],[f2025,f1886,f2053])).

fof(f2025,plain,
    ( r1_tarski(k1_tarski(sK1),sK0)
    | ~ spl26_22 ),
    inference(trivial_inequality_removal,[],[f2021])).

fof(f2021,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_tarski(sK1),sK0)
    | ~ spl26_22 ),
    inference(superposition,[],[f937,f1888])).

fof(f937,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f1941,plain,
    ( spl26_23
    | ~ spl26_16 ),
    inference(avatar_split_clause,[],[f1780,f1403,f1938])).

fof(f1938,plain,
    ( spl26_23
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_23])])).

fof(f1780,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK2),sK0)
    | ~ spl26_16 ),
    inference(resolution,[],[f932,f1405])).

fof(f932,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f424])).

fof(f1889,plain,
    ( spl26_22
    | ~ spl26_17 ),
    inference(avatar_split_clause,[],[f1779,f1437,f1886])).

fof(f1779,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),sK0)
    | ~ spl26_17 ),
    inference(resolution,[],[f932,f1439])).

fof(f1802,plain,
    ( spl26_21
    | ~ spl26_16 ),
    inference(avatar_split_clause,[],[f1614,f1403,f1799])).

fof(f1799,plain,
    ( spl26_21
  <=> sK0 = k2_xboole_0(k1_tarski(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_21])])).

fof(f1614,plain,
    ( sK0 = k2_xboole_0(k1_tarski(sK2),sK0)
    | ~ spl26_16 ),
    inference(resolution,[],[f894,f1405])).

fof(f894,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f615])).

fof(f615,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f404])).

fof(f404,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f1771,plain,
    ( spl26_20
    | ~ spl26_17 ),
    inference(avatar_split_clause,[],[f1613,f1437,f1768])).

fof(f1613,plain,
    ( sK0 = k2_xboole_0(k1_tarski(sK1),sK0)
    | ~ spl26_17 ),
    inference(resolution,[],[f894,f1439])).

fof(f1620,plain,
    ( ~ spl26_19
    | spl26_2 ),
    inference(avatar_split_clause,[],[f1604,f1059,f1617])).

fof(f1617,plain,
    ( spl26_19
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_19])])).

fof(f1604,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | spl26_2 ),
    inference(subsumption_resolution,[],[f1570,f976])).

fof(f976,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1570,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK0)
    | spl26_2 ),
    inference(extensionality_resolution,[],[f878,f1061])).

fof(f878,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1525,plain,
    ( ~ spl26_18
    | spl26_15 ),
    inference(avatar_split_clause,[],[f1502,f1365,f1522])).

fof(f1365,plain,
    ( spl26_15
  <=> r2_hidden(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_15])])).

fof(f1502,plain,
    ( ~ r1_tarski(k2_tarski(sK1,sK2),sK0)
    | spl26_15 ),
    inference(resolution,[],[f1367,f988])).

fof(f988,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f651])).

fof(f651,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f285])).

fof(f285,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f1367,plain,
    ( ~ r2_hidden(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))
    | spl26_15 ),
    inference(avatar_component_clause,[],[f1365])).

fof(f1440,plain,
    ( spl26_17
    | ~ spl26_3
    | spl26_11 ),
    inference(avatar_split_clause,[],[f1381,f1187,f1064,f1437])).

fof(f1064,plain,
    ( spl26_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_3])])).

fof(f1381,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl26_3
    | spl26_11 ),
    inference(subsumption_resolution,[],[f1376,f1189])).

fof(f1189,plain,
    ( ~ v1_xboole_0(sK0)
    | spl26_11 ),
    inference(avatar_component_clause,[],[f1187])).

fof(f1376,plain,
    ( r2_hidden(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl26_3 ),
    inference(resolution,[],[f985,f1066])).

fof(f1066,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl26_3 ),
    inference(avatar_component_clause,[],[f1064])).

fof(f985,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f645])).

fof(f645,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f455])).

fof(f455,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f1406,plain,
    ( spl26_16
    | ~ spl26_1
    | spl26_11 ),
    inference(avatar_split_clause,[],[f1380,f1187,f1054,f1403])).

fof(f1054,plain,
    ( spl26_1
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_1])])).

fof(f1380,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl26_1
    | spl26_11 ),
    inference(subsumption_resolution,[],[f1375,f1189])).

fof(f1375,plain,
    ( r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0)
    | ~ spl26_1 ),
    inference(resolution,[],[f985,f1056])).

fof(f1056,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl26_1 ),
    inference(avatar_component_clause,[],[f1054])).

fof(f1368,plain,
    ( ~ spl26_15
    | spl26_4 ),
    inference(avatar_split_clause,[],[f1363,f1069,f1365])).

fof(f1069,plain,
    ( spl26_4
  <=> m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_4])])).

fof(f1363,plain,
    ( ~ r2_hidden(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))
    | spl26_4 ),
    inference(subsumption_resolution,[],[f1361,f707])).

fof(f707,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f471])).

fof(f471,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f1361,plain,
    ( ~ r2_hidden(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | spl26_4 ),
    inference(resolution,[],[f984,f1071])).

fof(f1071,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))
    | spl26_4 ),
    inference(avatar_component_clause,[],[f1069])).

fof(f984,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f645])).

fof(f1260,plain,
    ( spl26_14
    | ~ spl26_8 ),
    inference(avatar_split_clause,[],[f1099,f1091,f1257])).

fof(f1257,plain,
    ( spl26_14
  <=> k1_xboole_0 = k3_tarski(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_14])])).

fof(f1091,plain,
    ( spl26_8
  <=> k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_8])])).

fof(f1099,plain,
    ( k1_xboole_0 = k3_tarski(k1_tarski(k1_xboole_0))
    | ~ spl26_8 ),
    inference(superposition,[],[f705,f1093])).

fof(f1093,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)
    | ~ spl26_8 ),
    inference(avatar_component_clause,[],[f1091])).

fof(f705,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f448])).

fof(f448,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f1222,plain,
    ( ~ spl26_11
    | spl26_13
    | ~ spl26_3 ),
    inference(avatar_split_clause,[],[f1182,f1064,f1219,f1187])).

fof(f1219,plain,
    ( spl26_13
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_13])])).

fof(f1182,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK0)
    | ~ spl26_3 ),
    inference(resolution,[],[f983,f1066])).

fof(f983,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f645])).

fof(f1194,plain,
    ( ~ spl26_11
    | spl26_12
    | ~ spl26_1 ),
    inference(avatar_split_clause,[],[f1181,f1054,f1191,f1187])).

fof(f1191,plain,
    ( spl26_12
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_12])])).

fof(f1181,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0)
    | ~ spl26_1 ),
    inference(resolution,[],[f983,f1056])).

fof(f1143,plain,
    ( spl26_10
    | ~ spl26_8 ),
    inference(avatar_split_clause,[],[f1101,f1091,f1140])).

fof(f1140,plain,
    ( spl26_10
  <=> m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_10])])).

fof(f1101,plain,
    ( m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ spl26_8 ),
    inference(superposition,[],[f706,f1093])).

fof(f706,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f510])).

fof(f510,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f1115,plain,
    ( ~ spl26_9
    | ~ spl26_8 ),
    inference(avatar_split_clause,[],[f1102,f1091,f1112])).

fof(f1112,plain,
    ( spl26_9
  <=> v1_xboole_0(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_9])])).

fof(f1102,plain,
    ( ~ v1_xboole_0(k1_tarski(k1_xboole_0))
    | ~ spl26_8 ),
    inference(superposition,[],[f707,f1093])).

fof(f1094,plain,(
    spl26_8 ),
    inference(avatar_split_clause,[],[f708,f1091])).

fof(f708,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f376])).

fof(f376,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f1087,plain,(
    spl26_7 ),
    inference(avatar_split_clause,[],[f980,f1084])).

fof(f1084,plain,
    ( spl26_7
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_7])])).

fof(f980,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f387])).

fof(f387,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f1082,plain,(
    spl26_6 ),
    inference(avatar_split_clause,[],[f1039,f1079])).

fof(f1079,plain,
    ( spl26_6
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_6])])).

fof(f1039,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f969])).

fof(f969,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f644])).

fof(f644,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f132])).

fof(f132,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f1077,plain,(
    spl26_5 ),
    inference(avatar_split_clause,[],[f981,f1074])).

fof(f1074,plain,
    ( spl26_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_5])])).

fof(f981,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1072,plain,(
    ~ spl26_4 ),
    inference(avatar_split_clause,[],[f648,f1069])).

fof(f648,plain,(
    ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f523])).

fof(f523,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f522])).

fof(f522,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f517])).

fof(f517,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ( k1_xboole_0 != X0
             => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f516])).

fof(f516,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ( k1_xboole_0 != X0
           => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_subset_1)).

fof(f1067,plain,(
    spl26_3 ),
    inference(avatar_split_clause,[],[f649,f1064])).

fof(f649,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f523])).

fof(f1062,plain,(
    ~ spl26_2 ),
    inference(avatar_split_clause,[],[f647,f1059])).

fof(f647,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f523])).

fof(f1057,plain,(
    spl26_1 ),
    inference(avatar_split_clause,[],[f646,f1054])).

fof(f646,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f523])).
%------------------------------------------------------------------------------
