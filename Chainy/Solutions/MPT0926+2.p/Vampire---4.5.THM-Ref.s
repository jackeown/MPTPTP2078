%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0926+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:58 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 337 expanded)
%              Number of leaves         :   33 ( 168 expanded)
%              Depth                    :    9
%              Number of atoms          :  571 (2225 expanded)
%              Number of equality atoms :  313 (1613 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2116,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1600,f1613,f1617,f1621,f1625,f1629,f1633,f1637,f1641,f1645,f1649,f1653,f1662,f2024,f2032,f2048,f2056,f2072,f2080,f2082,f2103,f2111,f2113,f2114,f2115])).

fof(f2115,plain,
    ( sK8 != sK9
    | k11_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(sK8)
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k2_mcart_1(sK8)
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k11_mcart_1(sK4,sK5,sK6,sK7,sK9) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2114,plain,
    ( sK8 != sK9
    | k10_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(sK8))
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k2_mcart_1(k1_mcart_1(sK8))
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k10_mcart_1(sK4,sK5,sK6,sK7,sK9) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2113,plain,
    ( sK8 != sK9
    | k9_mcart_1(sK4,sK5,sK6,sK7,sK8) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k9_mcart_1(sK4,sK5,sK6,sK7,sK9) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2111,plain,
    ( spl44_45
    | spl44_8
    | spl44_9
    | spl44_10
    | spl44_11
    | ~ spl44_16 ),
    inference(avatar_split_clause,[],[f2107,f1660,f1635,f1631,f1627,f1623,f2109])).

fof(f2109,plain,
    ( spl44_45
  <=> k9_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_45])])).

fof(f1623,plain,
    ( spl44_8
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_8])])).

fof(f1627,plain,
    ( spl44_9
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_9])])).

fof(f1631,plain,
    ( spl44_10
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_10])])).

fof(f1635,plain,
    ( spl44_11
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_11])])).

fof(f1660,plain,
    ( spl44_16
  <=> m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_16])])).

fof(f2107,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | spl44_8
    | spl44_9
    | spl44_10
    | spl44_11
    | ~ spl44_16 ),
    inference(subsumption_resolution,[],[f2106,f1636])).

fof(f1636,plain,
    ( k1_xboole_0 != sK4
    | spl44_11 ),
    inference(avatar_component_clause,[],[f1635])).

fof(f2106,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK4
    | spl44_8
    | spl44_9
    | spl44_10
    | ~ spl44_16 ),
    inference(subsumption_resolution,[],[f2105,f1632])).

fof(f1632,plain,
    ( k1_xboole_0 != sK5
    | spl44_10 ),
    inference(avatar_component_clause,[],[f1631])).

fof(f2105,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | spl44_8
    | spl44_9
    | ~ spl44_16 ),
    inference(subsumption_resolution,[],[f2104,f1628])).

fof(f1628,plain,
    ( k1_xboole_0 != sK6
    | spl44_9 ),
    inference(avatar_component_clause,[],[f1627])).

fof(f2104,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | spl44_8
    | ~ spl44_16 ),
    inference(subsumption_resolution,[],[f2089,f1624])).

fof(f1624,plain,
    ( k1_xboole_0 != sK7
    | spl44_8 ),
    inference(avatar_component_clause,[],[f1623])).

fof(f2089,plain,
    ( k9_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | ~ spl44_16 ),
    inference(resolution,[],[f1509,f1661])).

fof(f1661,plain,
    ( m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    | ~ spl44_16 ),
    inference(avatar_component_clause,[],[f1660])).

fof(f1509,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1407])).

fof(f1407,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

fof(f2103,plain,
    ( spl44_44
    | ~ spl44_7
    | spl44_12
    | spl44_13
    | spl44_14
    | spl44_15 ),
    inference(avatar_split_clause,[],[f2099,f1651,f1647,f1643,f1639,f1619,f2101])).

fof(f2101,plain,
    ( spl44_44
  <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_44])])).

fof(f1619,plain,
    ( spl44_7
  <=> m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_7])])).

fof(f1639,plain,
    ( spl44_12
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_12])])).

fof(f1643,plain,
    ( spl44_13
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_13])])).

fof(f1647,plain,
    ( spl44_14
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_14])])).

fof(f1651,plain,
    ( spl44_15
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_15])])).

fof(f2099,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl44_7
    | spl44_12
    | spl44_13
    | spl44_14
    | spl44_15 ),
    inference(subsumption_resolution,[],[f2098,f1652])).

fof(f1652,plain,
    ( k1_xboole_0 != sK0
    | spl44_15 ),
    inference(avatar_component_clause,[],[f1651])).

fof(f2098,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK0
    | ~ spl44_7
    | spl44_12
    | spl44_13
    | spl44_14 ),
    inference(subsumption_resolution,[],[f2097,f1648])).

fof(f1648,plain,
    ( k1_xboole_0 != sK1
    | spl44_14 ),
    inference(avatar_component_clause,[],[f1647])).

fof(f2097,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl44_7
    | spl44_12
    | spl44_13 ),
    inference(subsumption_resolution,[],[f2096,f1644])).

fof(f1644,plain,
    ( k1_xboole_0 != sK2
    | spl44_13 ),
    inference(avatar_component_clause,[],[f1643])).

fof(f2096,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl44_7
    | spl44_12 ),
    inference(subsumption_resolution,[],[f2088,f1640])).

fof(f1640,plain,
    ( k1_xboole_0 != sK3
    | spl44_12 ),
    inference(avatar_component_clause,[],[f1639])).

fof(f2088,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl44_7 ),
    inference(resolution,[],[f1509,f1620])).

fof(f1620,plain,
    ( m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | ~ spl44_7 ),
    inference(avatar_component_clause,[],[f1619])).

fof(f2082,plain,
    ( sK8 != sK9
    | k8_mcart_1(sK4,sK5,sK6,sK7,sK8) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k8_mcart_1(sK4,sK5,sK6,sK7,sK9) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2080,plain,
    ( spl44_42
    | spl44_8
    | spl44_9
    | spl44_10
    | spl44_11
    | ~ spl44_16 ),
    inference(avatar_split_clause,[],[f2076,f1660,f1635,f1631,f1627,f1623,f2078])).

fof(f2078,plain,
    ( spl44_42
  <=> k8_mcart_1(sK4,sK5,sK6,sK7,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_42])])).

fof(f2076,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | spl44_8
    | spl44_9
    | spl44_10
    | spl44_11
    | ~ spl44_16 ),
    inference(subsumption_resolution,[],[f2075,f1636])).

fof(f2075,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK4
    | spl44_8
    | spl44_9
    | spl44_10
    | ~ spl44_16 ),
    inference(subsumption_resolution,[],[f2074,f1632])).

fof(f2074,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | spl44_8
    | spl44_9
    | ~ spl44_16 ),
    inference(subsumption_resolution,[],[f2073,f1628])).

fof(f2073,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | spl44_8
    | ~ spl44_16 ),
    inference(subsumption_resolution,[],[f2058,f1624])).

fof(f2058,plain,
    ( k8_mcart_1(sK4,sK5,sK6,sK7,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | ~ spl44_16 ),
    inference(resolution,[],[f1508,f1661])).

fof(f1508,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1407])).

fof(f2072,plain,
    ( spl44_41
    | ~ spl44_7
    | spl44_12
    | spl44_13
    | spl44_14
    | spl44_15 ),
    inference(avatar_split_clause,[],[f2068,f1651,f1647,f1643,f1639,f1619,f2070])).

fof(f2070,plain,
    ( spl44_41
  <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_41])])).

fof(f2068,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl44_7
    | spl44_12
    | spl44_13
    | spl44_14
    | spl44_15 ),
    inference(subsumption_resolution,[],[f2067,f1652])).

fof(f2067,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK0
    | ~ spl44_7
    | spl44_12
    | spl44_13
    | spl44_14 ),
    inference(subsumption_resolution,[],[f2066,f1648])).

fof(f2066,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl44_7
    | spl44_12
    | spl44_13 ),
    inference(subsumption_resolution,[],[f2065,f1644])).

fof(f2065,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl44_7
    | spl44_12 ),
    inference(subsumption_resolution,[],[f2057,f1640])).

fof(f2057,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl44_7 ),
    inference(resolution,[],[f1508,f1620])).

fof(f2056,plain,
    ( spl44_40
    | spl44_8
    | spl44_9
    | spl44_10
    | spl44_11
    | ~ spl44_16 ),
    inference(avatar_split_clause,[],[f2052,f1660,f1635,f1631,f1627,f1623,f2054])).

fof(f2054,plain,
    ( spl44_40
  <=> k10_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_40])])).

fof(f2052,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | spl44_8
    | spl44_9
    | spl44_10
    | spl44_11
    | ~ spl44_16 ),
    inference(subsumption_resolution,[],[f2051,f1636])).

fof(f2051,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | k1_xboole_0 = sK4
    | spl44_8
    | spl44_9
    | spl44_10
    | ~ spl44_16 ),
    inference(subsumption_resolution,[],[f2050,f1632])).

fof(f2050,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | spl44_8
    | spl44_9
    | ~ spl44_16 ),
    inference(subsumption_resolution,[],[f2049,f1628])).

fof(f2049,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | spl44_8
    | ~ spl44_16 ),
    inference(subsumption_resolution,[],[f2034,f1624])).

fof(f2034,plain,
    ( k10_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | ~ spl44_16 ),
    inference(resolution,[],[f1510,f1661])).

fof(f1510,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1407])).

fof(f2048,plain,
    ( spl44_39
    | ~ spl44_7
    | spl44_12
    | spl44_13
    | spl44_14
    | spl44_15 ),
    inference(avatar_split_clause,[],[f2044,f1651,f1647,f1643,f1639,f1619,f2046])).

fof(f2046,plain,
    ( spl44_39
  <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_39])])).

fof(f2044,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | ~ spl44_7
    | spl44_12
    | spl44_13
    | spl44_14
    | spl44_15 ),
    inference(subsumption_resolution,[],[f2043,f1652])).

fof(f2043,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | k1_xboole_0 = sK0
    | ~ spl44_7
    | spl44_12
    | spl44_13
    | spl44_14 ),
    inference(subsumption_resolution,[],[f2042,f1648])).

fof(f2042,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl44_7
    | spl44_12
    | spl44_13 ),
    inference(subsumption_resolution,[],[f2041,f1644])).

fof(f2041,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl44_7
    | spl44_12 ),
    inference(subsumption_resolution,[],[f2033,f1640])).

fof(f2033,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl44_7 ),
    inference(resolution,[],[f1510,f1620])).

fof(f2032,plain,
    ( spl44_38
    | spl44_8
    | spl44_9
    | spl44_10
    | spl44_11
    | ~ spl44_16 ),
    inference(avatar_split_clause,[],[f2028,f1660,f1635,f1631,f1627,f1623,f2030])).

fof(f2030,plain,
    ( spl44_38
  <=> k11_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_38])])).

fof(f2028,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(sK8)
    | spl44_8
    | spl44_9
    | spl44_10
    | spl44_11
    | ~ spl44_16 ),
    inference(subsumption_resolution,[],[f2027,f1636])).

fof(f2027,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(sK8)
    | k1_xboole_0 = sK4
    | spl44_8
    | spl44_9
    | spl44_10
    | ~ spl44_16 ),
    inference(subsumption_resolution,[],[f2026,f1632])).

fof(f2026,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(sK8)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | spl44_8
    | spl44_9
    | ~ spl44_16 ),
    inference(subsumption_resolution,[],[f2025,f1628])).

fof(f2025,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(sK8)
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | spl44_8
    | ~ spl44_16 ),
    inference(subsumption_resolution,[],[f2010,f1624])).

fof(f2010,plain,
    ( k11_mcart_1(sK4,sK5,sK6,sK7,sK8) = k2_mcart_1(sK8)
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | ~ spl44_16 ),
    inference(resolution,[],[f1511,f1661])).

fof(f1511,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1407])).

fof(f2024,plain,
    ( spl44_37
    | ~ spl44_7
    | spl44_12
    | spl44_13
    | spl44_14
    | spl44_15 ),
    inference(avatar_split_clause,[],[f2020,f1651,f1647,f1643,f1639,f1619,f2022])).

fof(f2022,plain,
    ( spl44_37
  <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_37])])).

fof(f2020,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | ~ spl44_7
    | spl44_12
    | spl44_13
    | spl44_14
    | spl44_15 ),
    inference(subsumption_resolution,[],[f2019,f1652])).

fof(f2019,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | k1_xboole_0 = sK0
    | ~ spl44_7
    | spl44_12
    | spl44_13
    | spl44_14 ),
    inference(subsumption_resolution,[],[f2018,f1648])).

fof(f2018,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl44_7
    | spl44_12
    | spl44_13 ),
    inference(subsumption_resolution,[],[f2017,f1644])).

fof(f2017,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl44_7
    | spl44_12 ),
    inference(subsumption_resolution,[],[f2009,f1640])).

fof(f2009,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl44_7 ),
    inference(resolution,[],[f1511,f1620])).

fof(f1662,plain,
    ( spl44_16
    | ~ spl44_1
    | ~ spl44_6 ),
    inference(avatar_split_clause,[],[f1658,f1615,f1598,f1660])).

fof(f1598,plain,
    ( spl44_1
  <=> sK8 = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_1])])).

fof(f1615,plain,
    ( spl44_6
  <=> m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_6])])).

fof(f1658,plain,
    ( m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    | ~ spl44_1
    | ~ spl44_6 ),
    inference(forward_demodulation,[],[f1616,f1599])).

fof(f1599,plain,
    ( sK8 = sK9
    | ~ spl44_1 ),
    inference(avatar_component_clause,[],[f1598])).

fof(f1616,plain,
    ( m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    | ~ spl44_6 ),
    inference(avatar_component_clause,[],[f1615])).

fof(f1653,plain,(
    ~ spl44_15 ),
    inference(avatar_split_clause,[],[f1478,f1651])).

fof(f1478,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f1435])).

fof(f1435,plain,
    ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK9)
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK9)
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK9)
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK9) )
    & sK8 = sK9
    & m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    & k1_xboole_0 != sK7
    & k1_xboole_0 != sK6
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f1399,f1434,f1433,f1432])).

fof(f1432,plain,
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
              ( ( k11_mcart_1(sK0,sK1,sK2,sK3,X8) != k11_mcart_1(sK4,sK5,sK6,sK7,X9)
                | k10_mcart_1(sK0,sK1,sK2,sK3,X8) != k10_mcart_1(sK4,sK5,sK6,sK7,X9)
                | k9_mcart_1(sK0,sK1,sK2,sK3,X8) != k9_mcart_1(sK4,sK5,sK6,sK7,X9)
                | k8_mcart_1(sK0,sK1,sK2,sK3,X8) != k8_mcart_1(sK4,sK5,sK6,sK7,X9) )
              & X8 = X9
              & m1_subset_1(X9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) )
          & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
      & k1_xboole_0 != sK7
      & k1_xboole_0 != sK6
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f1433,plain,
    ( ? [X8] :
        ( ? [X9] :
            ( ( k11_mcart_1(sK0,sK1,sK2,sK3,X8) != k11_mcart_1(sK4,sK5,sK6,sK7,X9)
              | k10_mcart_1(sK0,sK1,sK2,sK3,X8) != k10_mcart_1(sK4,sK5,sK6,sK7,X9)
              | k9_mcart_1(sK0,sK1,sK2,sK3,X8) != k9_mcart_1(sK4,sK5,sK6,sK7,X9)
              | k8_mcart_1(sK0,sK1,sK2,sK3,X8) != k8_mcart_1(sK4,sK5,sK6,sK7,X9) )
            & X8 = X9
            & m1_subset_1(X9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) )
        & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
   => ( ? [X9] :
          ( ( k11_mcart_1(sK4,sK5,sK6,sK7,X9) != k11_mcart_1(sK0,sK1,sK2,sK3,sK8)
            | k10_mcart_1(sK4,sK5,sK6,sK7,X9) != k10_mcart_1(sK0,sK1,sK2,sK3,sK8)
            | k9_mcart_1(sK4,sK5,sK6,sK7,X9) != k9_mcart_1(sK0,sK1,sK2,sK3,sK8)
            | k8_mcart_1(sK4,sK5,sK6,sK7,X9) != k8_mcart_1(sK0,sK1,sK2,sK3,sK8) )
          & sK8 = X9
          & m1_subset_1(X9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) )
      & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f1434,plain,
    ( ? [X9] :
        ( ( k11_mcart_1(sK4,sK5,sK6,sK7,X9) != k11_mcart_1(sK0,sK1,sK2,sK3,sK8)
          | k10_mcart_1(sK4,sK5,sK6,sK7,X9) != k10_mcart_1(sK0,sK1,sK2,sK3,sK8)
          | k9_mcart_1(sK4,sK5,sK6,sK7,X9) != k9_mcart_1(sK0,sK1,sK2,sK3,sK8)
          | k8_mcart_1(sK4,sK5,sK6,sK7,X9) != k8_mcart_1(sK0,sK1,sK2,sK3,sK8) )
        & sK8 = X9
        & m1_subset_1(X9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) )
   => ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK9)
        | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK9)
        | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK9)
        | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK9) )
      & sK8 = sK9
      & m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ) ),
    introduced(choice_axiom,[])).

fof(f1399,plain,(
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
    inference(ennf_transformation,[],[f1396])).

fof(f1396,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1395])).

fof(f1395,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_mcart_1)).

fof(f1649,plain,(
    ~ spl44_14 ),
    inference(avatar_split_clause,[],[f1479,f1647])).

fof(f1479,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f1435])).

fof(f1645,plain,(
    ~ spl44_13 ),
    inference(avatar_split_clause,[],[f1480,f1643])).

fof(f1480,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f1435])).

fof(f1641,plain,(
    ~ spl44_12 ),
    inference(avatar_split_clause,[],[f1481,f1639])).

fof(f1481,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f1435])).

fof(f1637,plain,(
    ~ spl44_11 ),
    inference(avatar_split_clause,[],[f1482,f1635])).

fof(f1482,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f1435])).

fof(f1633,plain,(
    ~ spl44_10 ),
    inference(avatar_split_clause,[],[f1483,f1631])).

fof(f1483,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f1435])).

fof(f1629,plain,(
    ~ spl44_9 ),
    inference(avatar_split_clause,[],[f1484,f1627])).

fof(f1484,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f1435])).

fof(f1625,plain,(
    ~ spl44_8 ),
    inference(avatar_split_clause,[],[f1485,f1623])).

fof(f1485,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f1435])).

fof(f1621,plain,(
    spl44_7 ),
    inference(avatar_split_clause,[],[f1486,f1619])).

fof(f1486,plain,(
    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f1435])).

fof(f1617,plain,(
    spl44_6 ),
    inference(avatar_split_clause,[],[f1487,f1615])).

fof(f1487,plain,(
    m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f1435])).

fof(f1613,plain,
    ( ~ spl44_2
    | ~ spl44_3
    | ~ spl44_4
    | ~ spl44_5 ),
    inference(avatar_split_clause,[],[f1489,f1611,f1608,f1605,f1602])).

fof(f1602,plain,
    ( spl44_2
  <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k8_mcart_1(sK4,sK5,sK6,sK7,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_2])])).

fof(f1605,plain,
    ( spl44_3
  <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k9_mcart_1(sK4,sK5,sK6,sK7,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_3])])).

fof(f1608,plain,
    ( spl44_4
  <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k10_mcart_1(sK4,sK5,sK6,sK7,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_4])])).

fof(f1611,plain,
    ( spl44_5
  <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k11_mcart_1(sK4,sK5,sK6,sK7,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl44_5])])).

fof(f1489,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK9) ),
    inference(cnf_transformation,[],[f1435])).

fof(f1600,plain,(
    spl44_1 ),
    inference(avatar_split_clause,[],[f1488,f1598])).

fof(f1488,plain,(
    sK8 = sK9 ),
    inference(cnf_transformation,[],[f1435])).
%------------------------------------------------------------------------------
