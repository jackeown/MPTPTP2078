%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0876+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:55 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 319 expanded)
%              Number of leaves         :   17 (  95 expanded)
%              Depth                    :   15
%              Number of atoms          :  355 (1490 expanded)
%              Number of equality atoms :  221 (1331 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2315,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1685,f1886,f1936,f1976,f1983,f2039,f2040,f2061,f2122,f2185,f2290,f2314])).

fof(f2314,plain,
    ( spl24_2
    | spl24_4
    | spl24_5
    | ~ spl24_32 ),
    inference(avatar_contradiction_clause,[],[f2313])).

fof(f2313,plain,
    ( $false
    | spl24_2
    | spl24_4
    | spl24_5
    | ~ spl24_32 ),
    inference(subsumption_resolution,[],[f2312,f1473])).

fof(f1473,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f1411])).

fof(f1411,plain,
    ( ( sK2 != sK5
      | sK1 != sK4
      | sK0 != sK3 )
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f1335,f1410])).

fof(f1410,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( X2 != X5
          | X1 != X4
          | X0 != X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) )
   => ( ( sK2 != sK5
        | sK1 != sK4
        | sK0 != sK3 )
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f1335,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f1334])).

fof(f1334,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f1323])).

fof(f1323,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
       => ( ( X2 = X5
            & X1 = X4
            & X0 = X3 )
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f1322])).

fof(f1322,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

fof(f2312,plain,
    ( k1_xboole_0 = sK0
    | spl24_2
    | spl24_4
    | spl24_5
    | ~ spl24_32 ),
    inference(subsumption_resolution,[],[f2311,f1474])).

fof(f1474,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f1411])).

fof(f2311,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl24_2
    | spl24_4
    | spl24_5
    | ~ spl24_32 ),
    inference(subsumption_resolution,[],[f2303,f1680])).

fof(f1680,plain,
    ( sK1 != sK4
    | spl24_2 ),
    inference(avatar_component_clause,[],[f1678])).

fof(f1678,plain,
    ( spl24_2
  <=> sK1 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_2])])).

fof(f2303,plain,
    ( sK1 = sK4
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl24_4
    | spl24_5
    | ~ spl24_32 ),
    inference(superposition,[],[f1526,f2269])).

fof(f2269,plain,
    ( sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl24_4
    | spl24_5
    | ~ spl24_32 ),
    inference(subsumption_resolution,[],[f2268,f1711])).

fof(f1711,plain,
    ( k1_xboole_0 != sK3
    | spl24_4 ),
    inference(avatar_component_clause,[],[f1710])).

fof(f1710,plain,
    ( spl24_4
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_4])])).

fof(f2268,plain,
    ( sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK3
    | spl24_5
    | ~ spl24_32 ),
    inference(subsumption_resolution,[],[f2249,f1715])).

fof(f1715,plain,
    ( k1_xboole_0 != sK4
    | spl24_5 ),
    inference(avatar_component_clause,[],[f1714])).

fof(f1714,plain,
    ( spl24_5
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_5])])).

fof(f2249,plain,
    ( sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | ~ spl24_32 ),
    inference(superposition,[],[f1526,f2119])).

fof(f2119,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4)
    | ~ spl24_32 ),
    inference(avatar_component_clause,[],[f2117])).

fof(f2117,plain,
    ( spl24_32
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_32])])).

fof(f1526,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1356])).

fof(f1356,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f798])).

fof(f798,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(f2290,plain,
    ( spl24_1
    | spl24_4
    | spl24_5
    | ~ spl24_32 ),
    inference(avatar_contradiction_clause,[],[f2289])).

fof(f2289,plain,
    ( $false
    | spl24_1
    | spl24_4
    | spl24_5
    | ~ spl24_32 ),
    inference(subsumption_resolution,[],[f2288,f1473])).

fof(f2288,plain,
    ( k1_xboole_0 = sK0
    | spl24_1
    | spl24_4
    | spl24_5
    | ~ spl24_32 ),
    inference(subsumption_resolution,[],[f2287,f1474])).

fof(f2287,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl24_1
    | spl24_4
    | spl24_5
    | ~ spl24_32 ),
    inference(subsumption_resolution,[],[f2282,f1676])).

fof(f1676,plain,
    ( sK0 != sK3
    | spl24_1 ),
    inference(avatar_component_clause,[],[f1674])).

fof(f1674,plain,
    ( spl24_1
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_1])])).

fof(f2282,plain,
    ( sK0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl24_4
    | spl24_5
    | ~ spl24_32 ),
    inference(superposition,[],[f1525,f2267])).

fof(f2267,plain,
    ( sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl24_4
    | spl24_5
    | ~ spl24_32 ),
    inference(subsumption_resolution,[],[f2266,f1711])).

fof(f2266,plain,
    ( sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK3
    | spl24_5
    | ~ spl24_32 ),
    inference(subsumption_resolution,[],[f2248,f1715])).

fof(f2248,plain,
    ( sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | ~ spl24_32 ),
    inference(superposition,[],[f1525,f2119])).

fof(f1525,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1356])).

fof(f2185,plain,(
    ~ spl24_31 ),
    inference(avatar_contradiction_clause,[],[f2184])).

fof(f2184,plain,
    ( $false
    | ~ spl24_31 ),
    inference(subsumption_resolution,[],[f2183,f1474])).

fof(f2183,plain,
    ( k1_xboole_0 = sK1
    | ~ spl24_31 ),
    inference(subsumption_resolution,[],[f2149,f1473])).

fof(f2149,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl24_31 ),
    inference(trivial_inequality_removal,[],[f2143])).

fof(f2143,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl24_31 ),
    inference(superposition,[],[f1531,f2058])).

fof(f2058,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl24_31 ),
    inference(avatar_component_clause,[],[f2056])).

fof(f2056,plain,
    ( spl24_31
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_31])])).

fof(f1531,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f1429])).

fof(f1429,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f1428])).

fof(f1428,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f2122,plain,
    ( spl24_31
    | spl24_32
    | ~ spl24_17 ),
    inference(avatar_split_clause,[],[f2121,f1763,f2117,f2056])).

fof(f1763,plain,
    ( spl24_17
  <=> k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_17])])).

fof(f2121,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl24_17 ),
    inference(subsumption_resolution,[],[f2114,f1475])).

fof(f1475,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f1411])).

fof(f2114,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl24_17 ),
    inference(superposition,[],[f1525,f1765])).

fof(f1765,plain,
    ( k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl24_17 ),
    inference(avatar_component_clause,[],[f1763])).

fof(f2061,plain,
    ( spl24_31
    | spl24_3
    | ~ spl24_18 ),
    inference(avatar_split_clause,[],[f2060,f1768,f1682,f2056])).

fof(f1682,plain,
    ( spl24_3
  <=> sK2 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_3])])).

fof(f1768,plain,
    ( spl24_18
  <=> sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_18])])).

fof(f2060,plain,
    ( sK2 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl24_18 ),
    inference(subsumption_resolution,[],[f2050,f1475])).

fof(f2050,plain,
    ( sK2 = sK5
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl24_18 ),
    inference(superposition,[],[f1526,f1770])).

fof(f1770,plain,
    ( sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl24_18 ),
    inference(avatar_component_clause,[],[f1768])).

fof(f2040,plain,
    ( spl24_10
    | spl24_6
    | spl24_18 ),
    inference(avatar_split_clause,[],[f2020,f1768,f1718,f1735])).

fof(f1735,plain,
    ( spl24_10
  <=> k1_xboole_0 = k2_zfmisc_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_10])])).

fof(f1718,plain,
    ( spl24_6
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl24_6])])).

fof(f2020,plain,
    ( sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) ),
    inference(superposition,[],[f1526,f1637])).

fof(f1637,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) ),
    inference(definition_unfolding,[],[f1472,f1636,f1636])).

fof(f1636,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1275])).

fof(f1275,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f1472,plain,(
    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f1411])).

fof(f2039,plain,
    ( spl24_10
    | spl24_6
    | spl24_17 ),
    inference(avatar_split_clause,[],[f2019,f1763,f1718,f1735])).

fof(f2019,plain,
    ( k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) ),
    inference(superposition,[],[f1525,f1637])).

fof(f1983,plain,
    ( ~ spl24_4
    | spl24_10 ),
    inference(avatar_contradiction_clause,[],[f1982])).

fof(f1982,plain,
    ( $false
    | ~ spl24_4
    | spl24_10 ),
    inference(subsumption_resolution,[],[f1981,f1658])).

fof(f1658,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f1532])).

fof(f1532,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f1429])).

fof(f1981,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK4)
    | ~ spl24_4
    | spl24_10 ),
    inference(forward_demodulation,[],[f1736,f1712])).

fof(f1712,plain,
    ( k1_xboole_0 = sK3
    | ~ spl24_4 ),
    inference(avatar_component_clause,[],[f1710])).

fof(f1736,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK3,sK4)
    | spl24_10 ),
    inference(avatar_component_clause,[],[f1735])).

fof(f1976,plain,
    ( ~ spl24_5
    | spl24_10 ),
    inference(avatar_contradiction_clause,[],[f1975])).

fof(f1975,plain,
    ( $false
    | ~ spl24_5
    | spl24_10 ),
    inference(subsumption_resolution,[],[f1974,f1657])).

fof(f1657,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f1533])).

fof(f1533,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f1429])).

fof(f1974,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK3,k1_xboole_0)
    | ~ spl24_5
    | spl24_10 ),
    inference(forward_demodulation,[],[f1736,f1716])).

fof(f1716,plain,
    ( k1_xboole_0 = sK4
    | ~ spl24_5 ),
    inference(avatar_component_clause,[],[f1714])).

fof(f1936,plain,(
    ~ spl24_10 ),
    inference(avatar_contradiction_clause,[],[f1935])).

fof(f1935,plain,
    ( $false
    | ~ spl24_10 ),
    inference(subsumption_resolution,[],[f1934,f1473])).

fof(f1934,plain,
    ( k1_xboole_0 = sK0
    | ~ spl24_10 ),
    inference(subsumption_resolution,[],[f1933,f1474])).

fof(f1933,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl24_10 ),
    inference(subsumption_resolution,[],[f1932,f1475])).

fof(f1932,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl24_10 ),
    inference(trivial_inequality_removal,[],[f1908])).

fof(f1908,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl24_10 ),
    inference(superposition,[],[f1641,f1903])).

fof(f1903,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl24_10 ),
    inference(forward_demodulation,[],[f1902,f1658])).

fof(f1902,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k1_xboole_0,sK5)
    | ~ spl24_10 ),
    inference(forward_demodulation,[],[f1637,f1737])).

fof(f1737,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | ~ spl24_10 ),
    inference(avatar_component_clause,[],[f1735])).

fof(f1641,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f1632,f1636])).

fof(f1632,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1471])).

fof(f1471,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f1470])).

fof(f1470,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f1321])).

fof(f1321,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f1886,plain,(
    ~ spl24_6 ),
    inference(avatar_contradiction_clause,[],[f1885])).

fof(f1885,plain,
    ( $false
    | ~ spl24_6 ),
    inference(subsumption_resolution,[],[f1884,f1473])).

fof(f1884,plain,
    ( k1_xboole_0 = sK0
    | ~ spl24_6 ),
    inference(subsumption_resolution,[],[f1883,f1474])).

fof(f1883,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl24_6 ),
    inference(subsumption_resolution,[],[f1882,f1475])).

fof(f1882,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl24_6 ),
    inference(trivial_inequality_removal,[],[f1858])).

fof(f1858,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl24_6 ),
    inference(superposition,[],[f1641,f1798])).

fof(f1798,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl24_6 ),
    inference(forward_demodulation,[],[f1797,f1657])).

fof(f1797,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),k1_xboole_0)
    | ~ spl24_6 ),
    inference(backward_demodulation,[],[f1637,f1720])).

fof(f1720,plain,
    ( k1_xboole_0 = sK5
    | ~ spl24_6 ),
    inference(avatar_component_clause,[],[f1718])).

fof(f1685,plain,
    ( ~ spl24_1
    | ~ spl24_2
    | ~ spl24_3 ),
    inference(avatar_split_clause,[],[f1476,f1682,f1678,f1674])).

fof(f1476,plain,
    ( sK2 != sK5
    | sK1 != sK4
    | sK0 != sK3 ),
    inference(cnf_transformation,[],[f1411])).
%------------------------------------------------------------------------------
