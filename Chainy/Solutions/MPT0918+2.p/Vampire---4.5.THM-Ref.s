%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0918+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:57 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 283 expanded)
%              Number of leaves         :   28 ( 129 expanded)
%              Depth                    :   13
%              Number of atoms          :  532 (1304 expanded)
%              Number of equality atoms :  290 ( 896 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2268,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1560,f1564,f1568,f1572,f1576,f1580,f1584,f2023,f2049,f2065,f2081,f2106,f2226,f2252,f2256,f2260,f2264,f2265,f2266,f2267])).

fof(f2267,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(sK4)
    | sK8 != k2_mcart_1(sK4)
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2266,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(sK4))
    | sK7 != k2_mcart_1(k1_mcart_1(sK4))
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2265,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | sK6 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2264,plain,
    ( spl32_42
    | ~ spl32_5
    | ~ spl32_39 ),
    inference(avatar_split_clause,[],[f2246,f2224,f1562,f2262])).

fof(f2262,plain,
    ( spl32_42
  <=> sK8 = k2_mcart_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_42])])).

fof(f1562,plain,
    ( spl32_5
  <=> sK4 = k4_mcart_1(sK5,sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_5])])).

fof(f2224,plain,
    ( spl32_39
  <=> sK4 = k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_39])])).

fof(f2246,plain,
    ( sK8 = k2_mcart_1(sK4)
    | ~ spl32_5
    | ~ spl32_39 ),
    inference(trivial_inequality_removal,[],[f2245])).

fof(f2245,plain,
    ( sK4 != sK4
    | sK8 = k2_mcart_1(sK4)
    | ~ spl32_5
    | ~ spl32_39 ),
    inference(superposition,[],[f1633,f2225])).

fof(f2225,plain,
    ( sK4 = k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(sK4))
    | ~ spl32_39 ),
    inference(avatar_component_clause,[],[f2224])).

fof(f1633,plain,
    ( ! [X2,X0,X3,X1] :
        ( k4_mcart_1(X0,X1,X2,X3) != sK4
        | sK8 = X3 )
    | ~ spl32_5 ),
    inference(superposition,[],[f1489,f1563])).

fof(f1563,plain,
    ( sK4 = k4_mcart_1(sK5,sK6,sK7,sK8)
    | ~ spl32_5 ),
    inference(avatar_component_clause,[],[f1562])).

fof(f1489,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7)
      | X3 = X7 ) ),
    inference(cnf_transformation,[],[f1405])).

fof(f1405,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f1337])).

fof(f1337,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
     => ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).

fof(f2260,plain,
    ( spl32_41
    | ~ spl32_5
    | ~ spl32_39 ),
    inference(avatar_split_clause,[],[f2247,f2224,f1562,f2258])).

fof(f2258,plain,
    ( spl32_41
  <=> sK7 = k2_mcart_1(k1_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_41])])).

fof(f2247,plain,
    ( sK7 = k2_mcart_1(k1_mcart_1(sK4))
    | ~ spl32_5
    | ~ spl32_39 ),
    inference(trivial_inequality_removal,[],[f2244])).

fof(f2244,plain,
    ( sK4 != sK4
    | sK7 = k2_mcart_1(k1_mcart_1(sK4))
    | ~ spl32_5
    | ~ spl32_39 ),
    inference(superposition,[],[f1629,f2225])).

fof(f1629,plain,
    ( ! [X2,X0,X3,X1] :
        ( k4_mcart_1(X0,X1,X2,X3) != sK4
        | sK7 = X2 )
    | ~ spl32_5 ),
    inference(superposition,[],[f1488,f1563])).

fof(f1488,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7)
      | X2 = X6 ) ),
    inference(cnf_transformation,[],[f1405])).

fof(f2256,plain,
    ( spl32_40
    | ~ spl32_5
    | ~ spl32_39 ),
    inference(avatar_split_clause,[],[f2248,f2224,f1562,f2254])).

fof(f2254,plain,
    ( spl32_40
  <=> sK6 = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_40])])).

fof(f2248,plain,
    ( sK6 = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | ~ spl32_5
    | ~ spl32_39 ),
    inference(trivial_inequality_removal,[],[f2243])).

fof(f2243,plain,
    ( sK4 != sK4
    | sK6 = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | ~ spl32_5
    | ~ spl32_39 ),
    inference(superposition,[],[f1626,f2225])).

fof(f1626,plain,
    ( ! [X2,X0,X3,X1] :
        ( k4_mcart_1(X0,X1,X2,X3) != sK4
        | sK6 = X1 )
    | ~ spl32_5 ),
    inference(superposition,[],[f1487,f1563])).

fof(f1487,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7)
      | X1 = X5 ) ),
    inference(cnf_transformation,[],[f1405])).

fof(f2252,plain,
    ( ~ spl32_5
    | spl32_36
    | ~ spl32_39 ),
    inference(avatar_contradiction_clause,[],[f2251])).

fof(f2251,plain,
    ( $false
    | ~ spl32_5
    | spl32_36
    | ~ spl32_39 ),
    inference(subsumption_resolution,[],[f2249,f2105])).

fof(f2105,plain,
    ( sK5 != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | spl32_36 ),
    inference(avatar_component_clause,[],[f2104])).

fof(f2104,plain,
    ( spl32_36
  <=> sK5 = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_36])])).

fof(f2249,plain,
    ( sK5 = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | ~ spl32_5
    | ~ spl32_39 ),
    inference(trivial_inequality_removal,[],[f2242])).

fof(f2242,plain,
    ( sK4 != sK4
    | sK5 = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | ~ spl32_5
    | ~ spl32_39 ),
    inference(superposition,[],[f1622,f2225])).

fof(f1622,plain,
    ( ! [X2,X0,X3,X1] :
        ( k4_mcart_1(X0,X1,X2,X3) != sK4
        | sK5 = X0 )
    | ~ spl32_5 ),
    inference(superposition,[],[f1486,f1563])).

fof(f1486,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f1405])).

fof(f2226,plain,
    ( spl32_39
    | spl32_6
    | spl32_7
    | spl32_8
    | spl32_9
    | ~ spl32_10
    | ~ spl32_26
    | ~ spl32_29
    | ~ spl32_30
    | ~ spl32_31 ),
    inference(avatar_split_clause,[],[f2222,f2079,f2063,f2047,f2021,f1582,f1578,f1574,f1570,f1566,f2224])).

fof(f1566,plain,
    ( spl32_6
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_6])])).

fof(f1570,plain,
    ( spl32_7
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_7])])).

fof(f1574,plain,
    ( spl32_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_8])])).

fof(f1578,plain,
    ( spl32_9
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_9])])).

fof(f1582,plain,
    ( spl32_10
  <=> m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_10])])).

fof(f2021,plain,
    ( spl32_26
  <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_26])])).

fof(f2047,plain,
    ( spl32_29
  <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_29])])).

fof(f2063,plain,
    ( spl32_30
  <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_30])])).

fof(f2079,plain,
    ( spl32_31
  <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_31])])).

fof(f2222,plain,
    ( sK4 = k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(sK4))
    | spl32_6
    | spl32_7
    | spl32_8
    | spl32_9
    | ~ spl32_10
    | ~ spl32_26
    | ~ spl32_29
    | ~ spl32_30
    | ~ spl32_31 ),
    inference(forward_demodulation,[],[f2221,f2064])).

fof(f2064,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | ~ spl32_30 ),
    inference(avatar_component_clause,[],[f2063])).

fof(f2221,plain,
    ( sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))),k2_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(sK4))
    | spl32_6
    | spl32_7
    | spl32_8
    | spl32_9
    | ~ spl32_10
    | ~ spl32_26
    | ~ spl32_29
    | ~ spl32_31 ),
    inference(forward_demodulation,[],[f2220,f2080])).

fof(f2080,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | ~ spl32_31 ),
    inference(avatar_component_clause,[],[f2079])).

fof(f2220,plain,
    ( sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k2_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(sK4))
    | spl32_6
    | spl32_7
    | spl32_8
    | spl32_9
    | ~ spl32_10
    | ~ spl32_26
    | ~ spl32_29 ),
    inference(forward_demodulation,[],[f2219,f2048])).

fof(f2048,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | ~ spl32_29 ),
    inference(avatar_component_clause,[],[f2047])).

fof(f2219,plain,
    ( sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k2_mcart_1(sK4))
    | spl32_6
    | spl32_7
    | spl32_8
    | spl32_9
    | ~ spl32_10
    | ~ spl32_26 ),
    inference(forward_demodulation,[],[f2218,f2022])).

fof(f2022,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | ~ spl32_26 ),
    inference(avatar_component_clause,[],[f2021])).

fof(f2218,plain,
    ( sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))
    | spl32_6
    | spl32_7
    | spl32_8
    | spl32_9
    | ~ spl32_10 ),
    inference(subsumption_resolution,[],[f2217,f1579])).

fof(f1579,plain,
    ( k1_xboole_0 != sK0
    | spl32_9 ),
    inference(avatar_component_clause,[],[f1578])).

fof(f2217,plain,
    ( sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK0
    | spl32_6
    | spl32_7
    | spl32_8
    | ~ spl32_10 ),
    inference(subsumption_resolution,[],[f2216,f1575])).

fof(f1575,plain,
    ( k1_xboole_0 != sK1
    | spl32_8 ),
    inference(avatar_component_clause,[],[f1574])).

fof(f2216,plain,
    ( sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl32_6
    | spl32_7
    | ~ spl32_10 ),
    inference(subsumption_resolution,[],[f2215,f1571])).

fof(f1571,plain,
    ( k1_xboole_0 != sK2
    | spl32_7 ),
    inference(avatar_component_clause,[],[f1570])).

fof(f2215,plain,
    ( sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl32_6
    | ~ spl32_10 ),
    inference(subsumption_resolution,[],[f2208,f1567])).

fof(f1567,plain,
    ( k1_xboole_0 != sK3
    | spl32_6 ),
    inference(avatar_component_clause,[],[f1566])).

fof(f2208,plain,
    ( sK4 = k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl32_10 ),
    inference(resolution,[],[f1473,f1583])).

fof(f1583,plain,
    ( m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | ~ spl32_10 ),
    inference(avatar_component_clause,[],[f1582])).

fof(f1473,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1398])).

fof(f1398,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1367])).

fof(f1367,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).

fof(f2106,plain,
    ( ~ spl32_36
    | spl32_1
    | ~ spl32_30 ),
    inference(avatar_split_clause,[],[f2094,f2063,f1549,f2104])).

fof(f1549,plain,
    ( spl32_1
  <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_1])])).

fof(f2094,plain,
    ( sK5 != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | spl32_1
    | ~ spl32_30 ),
    inference(superposition,[],[f1550,f2064])).

fof(f1550,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5
    | spl32_1 ),
    inference(avatar_component_clause,[],[f1549])).

fof(f2081,plain,
    ( spl32_31
    | spl32_6
    | spl32_7
    | spl32_8
    | spl32_9
    | ~ spl32_10 ),
    inference(avatar_split_clause,[],[f2077,f1582,f1578,f1574,f1570,f1566,f2079])).

fof(f2077,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | spl32_6
    | spl32_7
    | spl32_8
    | spl32_9
    | ~ spl32_10 ),
    inference(subsumption_resolution,[],[f2076,f1579])).

fof(f2076,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK0
    | spl32_6
    | spl32_7
    | spl32_8
    | ~ spl32_10 ),
    inference(subsumption_resolution,[],[f2075,f1575])).

fof(f2075,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl32_6
    | spl32_7
    | ~ spl32_10 ),
    inference(subsumption_resolution,[],[f2074,f1571])).

fof(f2074,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl32_6
    | ~ spl32_10 ),
    inference(subsumption_resolution,[],[f2067,f1567])).

fof(f2067,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl32_10 ),
    inference(resolution,[],[f1466,f1583])).

fof(f1466,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1396])).

fof(f1396,plain,(
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
    inference(ennf_transformation,[],[f1368])).

fof(f1368,axiom,(
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

fof(f2065,plain,
    ( spl32_30
    | spl32_6
    | spl32_7
    | spl32_8
    | spl32_9
    | ~ spl32_10 ),
    inference(avatar_split_clause,[],[f2061,f1582,f1578,f1574,f1570,f1566,f2063])).

fof(f2061,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | spl32_6
    | spl32_7
    | spl32_8
    | spl32_9
    | ~ spl32_10 ),
    inference(subsumption_resolution,[],[f2060,f1579])).

fof(f2060,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK0
    | spl32_6
    | spl32_7
    | spl32_8
    | ~ spl32_10 ),
    inference(subsumption_resolution,[],[f2059,f1575])).

fof(f2059,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl32_6
    | spl32_7
    | ~ spl32_10 ),
    inference(subsumption_resolution,[],[f2058,f1571])).

% (14285)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_11 on theBenchmark
fof(f2058,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl32_6
    | ~ spl32_10 ),
    inference(subsumption_resolution,[],[f2051,f1567])).

fof(f2051,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl32_10 ),
    inference(resolution,[],[f1465,f1583])).

fof(f1465,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1396])).

fof(f2049,plain,
    ( spl32_29
    | spl32_6
    | spl32_7
    | spl32_8
    | spl32_9
    | ~ spl32_10 ),
    inference(avatar_split_clause,[],[f2045,f1582,f1578,f1574,f1570,f1566,f2047])).

fof(f2045,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | spl32_6
    | spl32_7
    | spl32_8
    | spl32_9
    | ~ spl32_10 ),
    inference(subsumption_resolution,[],[f2044,f1579])).

fof(f2044,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK0
    | spl32_6
    | spl32_7
    | spl32_8
    | ~ spl32_10 ),
    inference(subsumption_resolution,[],[f2043,f1575])).

fof(f2043,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl32_6
    | spl32_7
    | ~ spl32_10 ),
    inference(subsumption_resolution,[],[f2042,f1571])).

fof(f2042,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl32_6
    | ~ spl32_10 ),
    inference(subsumption_resolution,[],[f2035,f1567])).

fof(f2035,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl32_10 ),
    inference(resolution,[],[f1467,f1583])).

fof(f1467,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1396])).

fof(f2023,plain,
    ( spl32_26
    | spl32_6
    | spl32_7
    | spl32_8
    | spl32_9
    | ~ spl32_10 ),
    inference(avatar_split_clause,[],[f2019,f1582,f1578,f1574,f1570,f1566,f2021])).

fof(f2019,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | spl32_6
    | spl32_7
    | spl32_8
    | spl32_9
    | ~ spl32_10 ),
    inference(subsumption_resolution,[],[f2018,f1579])).

fof(f2018,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK0
    | spl32_6
    | spl32_7
    | spl32_8
    | ~ spl32_10 ),
    inference(subsumption_resolution,[],[f2017,f1575])).

fof(f2017,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl32_6
    | spl32_7
    | ~ spl32_10 ),
    inference(subsumption_resolution,[],[f2016,f1571])).

fof(f2016,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl32_6
    | ~ spl32_10 ),
    inference(subsumption_resolution,[],[f2009,f1567])).

fof(f2009,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl32_10 ),
    inference(resolution,[],[f1468,f1583])).

fof(f1468,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1396])).

fof(f1584,plain,(
    spl32_10 ),
    inference(avatar_split_clause,[],[f1450,f1582])).

fof(f1450,plain,(
    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f1420])).

fof(f1420,plain,
    ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5 )
    & sK4 = k4_mcart_1(sK5,sK6,sK7,sK8)
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f1392,f1419,f1418])).

fof(f1418,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ? [X5,X6,X7,X8] :
            ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
              | k10_mcart_1(X0,X1,X2,X3,X4) != X7
              | k9_mcart_1(X0,X1,X2,X3,X4) != X6
              | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
            & k4_mcart_1(X5,X6,X7,X8) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( ? [X8,X7,X6,X5] :
          ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != X8
            | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != X7
            | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != X6
            | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = sK4 )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f1419,plain,
    ( ? [X8,X7,X6,X5] :
        ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != X8
          | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != X7
          | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != X6
          | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != X5 )
        & k4_mcart_1(X5,X6,X7,X8) = sK4 )
   => ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8
        | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7
        | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6
        | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5 )
      & sK4 = k4_mcart_1(sK5,sK6,sK7,sK8) ) ),
    introduced(choice_axiom,[])).

fof(f1392,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
            | k10_mcart_1(X0,X1,X2,X3,X4) != X7
            | k9_mcart_1(X0,X1,X2,X3,X4) != X6
            | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f1391])).

fof(f1391,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
            | k10_mcart_1(X0,X1,X2,X3,X4) != X7
            | k9_mcart_1(X0,X1,X2,X3,X4) != X6
            | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1387])).

fof(f1387,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
       => ~ ( ? [X5,X6,X7,X8] :
                ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                    & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                    & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                    & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
                & k4_mcart_1(X5,X6,X7,X8) = X4 )
            & k1_xboole_0 != X3
            & k1_xboole_0 != X2
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f1386])).

fof(f1386,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => ~ ( ? [X5,X6,X7,X8] :
              ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                  & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                  & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                  & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
              & k4_mcart_1(X5,X6,X7,X8) = X4 )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).

fof(f1580,plain,(
    ~ spl32_9 ),
    inference(avatar_split_clause,[],[f1451,f1578])).

fof(f1451,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f1420])).

fof(f1576,plain,(
    ~ spl32_8 ),
    inference(avatar_split_clause,[],[f1452,f1574])).

fof(f1452,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f1420])).

fof(f1572,plain,(
    ~ spl32_7 ),
    inference(avatar_split_clause,[],[f1453,f1570])).

fof(f1453,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f1420])).

fof(f1568,plain,(
    ~ spl32_6 ),
    inference(avatar_split_clause,[],[f1454,f1566])).

fof(f1454,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f1420])).

fof(f1564,plain,(
    spl32_5 ),
    inference(avatar_split_clause,[],[f1455,f1562])).

fof(f1455,plain,(
    sK4 = k4_mcart_1(sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f1420])).

fof(f1560,plain,
    ( ~ spl32_1
    | ~ spl32_2
    | ~ spl32_3
    | ~ spl32_4 ),
    inference(avatar_split_clause,[],[f1456,f1558,f1555,f1552,f1549])).

fof(f1552,plain,
    ( spl32_2
  <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_2])])).

fof(f1555,plain,
    ( spl32_3
  <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_3])])).

fof(f1558,plain,
    ( spl32_4
  <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_4])])).

fof(f1456,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5 ),
    inference(cnf_transformation,[],[f1420])).
%------------------------------------------------------------------------------
