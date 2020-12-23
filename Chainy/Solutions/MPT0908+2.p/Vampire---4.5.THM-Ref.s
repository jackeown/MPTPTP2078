%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0908+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:57 EST 2020

% Result     : Theorem 1.77s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 212 expanded)
%              Number of leaves         :   23 (  95 expanded)
%              Depth                    :   11
%              Number of atoms          :  370 ( 874 expanded)
%              Number of equality atoms :  203 ( 587 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2107,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1524,f1528,f1532,f1536,f1540,f1544,f1925,f1939,f1963,f1988,f2057,f2096,f2100,f2104,f2105,f2106])).

fof(f2106,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(sK3)
    | sK6 != k2_mcart_1(sK3)
    | k7_mcart_1(sK0,sK1,sK2,sK3) = sK6 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2105,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(k1_mcart_1(sK3))
    | sK5 != k2_mcart_1(k1_mcart_1(sK3))
    | k6_mcart_1(sK0,sK1,sK2,sK3) = sK5 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2104,plain,
    ( spl22_45
    | ~ spl22_4
    | ~ spl22_43 ),
    inference(avatar_split_clause,[],[f2091,f2055,f1526,f2102])).

fof(f2102,plain,
    ( spl22_45
  <=> sK6 = k2_mcart_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_45])])).

fof(f1526,plain,
    ( spl22_4
  <=> sK3 = k3_mcart_1(sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_4])])).

fof(f2055,plain,
    ( spl22_43
  <=> sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_43])])).

fof(f2091,plain,
    ( sK6 = k2_mcart_1(sK3)
    | ~ spl22_4
    | ~ spl22_43 ),
    inference(trivial_inequality_removal,[],[f2090])).

fof(f2090,plain,
    ( sK3 != sK3
    | sK6 = k2_mcart_1(sK3)
    | ~ spl22_4
    | ~ spl22_43 ),
    inference(superposition,[],[f1570,f2056])).

fof(f2056,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3))
    | ~ spl22_43 ),
    inference(avatar_component_clause,[],[f2055])).

fof(f1570,plain,
    ( ! [X2,X0,X1] :
        ( k3_mcart_1(X0,X1,X2) != sK3
        | sK6 = X2 )
    | ~ spl22_4 ),
    inference(superposition,[],[f1463,f1527])).

fof(f1527,plain,
    ( sK3 = k3_mcart_1(sK4,sK5,sK6)
    | ~ spl22_4 ),
    inference(avatar_component_clause,[],[f1526])).

fof(f1463,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)
      | X2 = X5 ) ),
    inference(cnf_transformation,[],[f1393])).

fof(f1393,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f1332])).

fof(f1332,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
     => ( X2 = X5
        & X1 = X4
        & X0 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).

fof(f2100,plain,
    ( spl22_44
    | ~ spl22_4
    | ~ spl22_43 ),
    inference(avatar_split_clause,[],[f2092,f2055,f1526,f2098])).

fof(f2098,plain,
    ( spl22_44
  <=> sK5 = k2_mcart_1(k1_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_44])])).

fof(f2092,plain,
    ( sK5 = k2_mcart_1(k1_mcart_1(sK3))
    | ~ spl22_4
    | ~ spl22_43 ),
    inference(trivial_inequality_removal,[],[f2089])).

fof(f2089,plain,
    ( sK3 != sK3
    | sK5 = k2_mcart_1(k1_mcart_1(sK3))
    | ~ spl22_4
    | ~ spl22_43 ),
    inference(superposition,[],[f1566,f2056])).

fof(f1566,plain,
    ( ! [X2,X0,X1] :
        ( k3_mcart_1(X0,X1,X2) != sK3
        | sK5 = X1 )
    | ~ spl22_4 ),
    inference(superposition,[],[f1462,f1527])).

fof(f1462,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)
      | X1 = X4 ) ),
    inference(cnf_transformation,[],[f1393])).

fof(f2096,plain,
    ( ~ spl22_4
    | spl22_36
    | ~ spl22_43 ),
    inference(avatar_contradiction_clause,[],[f2095])).

fof(f2095,plain,
    ( $false
    | ~ spl22_4
    | spl22_36
    | ~ spl22_43 ),
    inference(subsumption_resolution,[],[f2093,f1987])).

fof(f1987,plain,
    ( sK4 != k1_mcart_1(k1_mcart_1(sK3))
    | spl22_36 ),
    inference(avatar_component_clause,[],[f1986])).

fof(f1986,plain,
    ( spl22_36
  <=> sK4 = k1_mcart_1(k1_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_36])])).

fof(f2093,plain,
    ( sK4 = k1_mcart_1(k1_mcart_1(sK3))
    | ~ spl22_4
    | ~ spl22_43 ),
    inference(trivial_inequality_removal,[],[f2088])).

fof(f2088,plain,
    ( sK3 != sK3
    | sK4 = k1_mcart_1(k1_mcart_1(sK3))
    | ~ spl22_4
    | ~ spl22_43 ),
    inference(superposition,[],[f1563,f2056])).

fof(f1563,plain,
    ( ! [X2,X0,X1] :
        ( k3_mcart_1(X0,X1,X2) != sK3
        | sK4 = X0 )
    | ~ spl22_4 ),
    inference(superposition,[],[f1461,f1527])).

fof(f1461,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f1393])).

fof(f2057,plain,
    ( spl22_43
    | spl22_5
    | spl22_6
    | spl22_7
    | ~ spl22_8
    | ~ spl22_29
    | ~ spl22_30
    | ~ spl22_33 ),
    inference(avatar_split_clause,[],[f2053,f1961,f1937,f1923,f1542,f1538,f1534,f1530,f2055])).

fof(f1530,plain,
    ( spl22_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_5])])).

fof(f1534,plain,
    ( spl22_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_6])])).

fof(f1538,plain,
    ( spl22_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_7])])).

fof(f1542,plain,
    ( spl22_8
  <=> m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_8])])).

fof(f1923,plain,
    ( spl22_29
  <=> k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_29])])).

fof(f1937,plain,
    ( spl22_30
  <=> k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_30])])).

fof(f1961,plain,
    ( spl22_33
  <=> k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_33])])).

fof(f2053,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3))
    | spl22_5
    | spl22_6
    | spl22_7
    | ~ spl22_8
    | ~ spl22_29
    | ~ spl22_30
    | ~ spl22_33 ),
    inference(forward_demodulation,[],[f2052,f1938])).

fof(f1938,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | ~ spl22_30 ),
    inference(avatar_component_clause,[],[f1937])).

fof(f2052,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3))
    | spl22_5
    | spl22_6
    | spl22_7
    | ~ spl22_8
    | ~ spl22_29
    | ~ spl22_33 ),
    inference(forward_demodulation,[],[f2051,f1962])).

fof(f1962,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | ~ spl22_33 ),
    inference(avatar_component_clause,[],[f1961])).

fof(f2051,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k2_mcart_1(sK3))
    | spl22_5
    | spl22_6
    | spl22_7
    | ~ spl22_8
    | ~ spl22_29 ),
    inference(forward_demodulation,[],[f2050,f1924])).

fof(f1924,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | ~ spl22_29 ),
    inference(avatar_component_clause,[],[f1923])).

fof(f2050,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | spl22_5
    | spl22_6
    | spl22_7
    | ~ spl22_8 ),
    inference(subsumption_resolution,[],[f2049,f1539])).

fof(f1539,plain,
    ( k1_xboole_0 != sK0
    | spl22_7 ),
    inference(avatar_component_clause,[],[f1538])).

fof(f2049,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0
    | spl22_5
    | spl22_6
    | ~ spl22_8 ),
    inference(subsumption_resolution,[],[f2048,f1535])).

fof(f1535,plain,
    ( k1_xboole_0 != sK1
    | spl22_6 ),
    inference(avatar_component_clause,[],[f1534])).

fof(f2048,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl22_5
    | ~ spl22_8 ),
    inference(subsumption_resolution,[],[f2042,f1531])).

fof(f1531,plain,
    ( k1_xboole_0 != sK2
    | spl22_5 ),
    inference(avatar_component_clause,[],[f1530])).

fof(f2042,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl22_8 ),
    inference(resolution,[],[f1452,f1543])).

fof(f1543,plain,
    ( m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl22_8 ),
    inference(avatar_component_clause,[],[f1542])).

fof(f1452,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1388])).

fof(f1388,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1353])).

fof(f1353,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f1988,plain,
    ( ~ spl22_36
    | spl22_1
    | ~ spl22_30 ),
    inference(avatar_split_clause,[],[f1976,f1937,f1516,f1986])).

fof(f1516,plain,
    ( spl22_1
  <=> k5_mcart_1(sK0,sK1,sK2,sK3) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_1])])).

fof(f1976,plain,
    ( sK4 != k1_mcart_1(k1_mcart_1(sK3))
    | spl22_1
    | ~ spl22_30 ),
    inference(superposition,[],[f1517,f1938])).

fof(f1517,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) != sK4
    | spl22_1 ),
    inference(avatar_component_clause,[],[f1516])).

fof(f1963,plain,
    ( spl22_33
    | spl22_5
    | spl22_6
    | spl22_7
    | ~ spl22_8 ),
    inference(avatar_split_clause,[],[f1959,f1542,f1538,f1534,f1530,f1961])).

fof(f1959,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | spl22_5
    | spl22_6
    | spl22_7
    | ~ spl22_8 ),
    inference(subsumption_resolution,[],[f1958,f1539])).

fof(f1958,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK0
    | spl22_5
    | spl22_6
    | ~ spl22_8 ),
    inference(subsumption_resolution,[],[f1957,f1535])).

fof(f1957,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl22_5
    | ~ spl22_8 ),
    inference(subsumption_resolution,[],[f1951,f1531])).

fof(f1951,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl22_8 ),
    inference(resolution,[],[f1447,f1543])).

fof(f1447,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1386])).

fof(f1386,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1356])).

fof(f1356,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f1939,plain,
    ( spl22_30
    | spl22_5
    | spl22_6
    | spl22_7
    | ~ spl22_8 ),
    inference(avatar_split_clause,[],[f1935,f1542,f1538,f1534,f1530,f1937])).

fof(f1935,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | spl22_5
    | spl22_6
    | spl22_7
    | ~ spl22_8 ),
    inference(subsumption_resolution,[],[f1934,f1539])).

fof(f1934,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK0
    | spl22_5
    | spl22_6
    | ~ spl22_8 ),
    inference(subsumption_resolution,[],[f1933,f1535])).

fof(f1933,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl22_5
    | ~ spl22_8 ),
    inference(subsumption_resolution,[],[f1927,f1531])).

fof(f1927,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl22_8 ),
    inference(resolution,[],[f1446,f1543])).

fof(f1446,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1386])).

fof(f1925,plain,
    ( spl22_29
    | spl22_5
    | spl22_6
    | spl22_7
    | ~ spl22_8 ),
    inference(avatar_split_clause,[],[f1921,f1542,f1538,f1534,f1530,f1923])).

fof(f1921,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | spl22_5
    | spl22_6
    | spl22_7
    | ~ spl22_8 ),
    inference(subsumption_resolution,[],[f1920,f1539])).

fof(f1920,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | k1_xboole_0 = sK0
    | spl22_5
    | spl22_6
    | ~ spl22_8 ),
    inference(subsumption_resolution,[],[f1919,f1535])).

fof(f1919,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl22_5
    | ~ spl22_8 ),
    inference(subsumption_resolution,[],[f1913,f1531])).

fof(f1913,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl22_8 ),
    inference(resolution,[],[f1448,f1543])).

fof(f1448,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1386])).

fof(f1544,plain,(
    spl22_8 ),
    inference(avatar_split_clause,[],[f1433,f1542])).

fof(f1433,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f1408])).

fof(f1408,plain,
    ( ( k7_mcart_1(sK0,sK1,sK2,sK3) != sK6
      | k6_mcart_1(sK0,sK1,sK2,sK3) != sK5
      | k5_mcart_1(sK0,sK1,sK2,sK3) != sK4 )
    & sK3 = k3_mcart_1(sK4,sK5,sK6)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f1382,f1407,f1406])).

fof(f1406,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4,X5,X6] :
            ( ( k7_mcart_1(X0,X1,X2,X3) != X6
              | k6_mcart_1(X0,X1,X2,X3) != X5
              | k5_mcart_1(X0,X1,X2,X3) != X4 )
            & k3_mcart_1(X4,X5,X6) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
   => ( ? [X6,X5,X4] :
          ( ( k7_mcart_1(sK0,sK1,sK2,sK3) != X6
            | k6_mcart_1(sK0,sK1,sK2,sK3) != X5
            | k5_mcart_1(sK0,sK1,sK2,sK3) != X4 )
          & k3_mcart_1(X4,X5,X6) = sK3 )
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f1407,plain,
    ( ? [X6,X5,X4] :
        ( ( k7_mcart_1(sK0,sK1,sK2,sK3) != X6
          | k6_mcart_1(sK0,sK1,sK2,sK3) != X5
          | k5_mcart_1(sK0,sK1,sK2,sK3) != X4 )
        & k3_mcart_1(X4,X5,X6) = sK3 )
   => ( ( k7_mcart_1(sK0,sK1,sK2,sK3) != sK6
        | k6_mcart_1(sK0,sK1,sK2,sK3) != sK5
        | k5_mcart_1(sK0,sK1,sK2,sK3) != sK4 )
      & sK3 = k3_mcart_1(sK4,sK5,sK6) ) ),
    introduced(choice_axiom,[])).

fof(f1382,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) != X6
            | k6_mcart_1(X0,X1,X2,X3) != X5
            | k5_mcart_1(X0,X1,X2,X3) != X4 )
          & k3_mcart_1(X4,X5,X6) = X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f1381])).

fof(f1381,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) != X6
            | k6_mcart_1(X0,X1,X2,X3) != X5
            | k5_mcart_1(X0,X1,X2,X3) != X4 )
          & k3_mcart_1(X4,X5,X6) = X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f1376])).

fof(f1376,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
       => ~ ( ? [X4,X5,X6] :
                ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                    & k6_mcart_1(X0,X1,X2,X3) = X5
                    & k5_mcart_1(X0,X1,X2,X3) = X4 )
                & k3_mcart_1(X4,X5,X6) = X3 )
            & k1_xboole_0 != X2
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f1375])).

fof(f1375,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => ~ ( ? [X4,X5,X6] :
              ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                  & k6_mcart_1(X0,X1,X2,X3) = X5
                  & k5_mcart_1(X0,X1,X2,X3) = X4 )
              & k3_mcart_1(X4,X5,X6) = X3 )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_mcart_1)).

fof(f1540,plain,(
    ~ spl22_7 ),
    inference(avatar_split_clause,[],[f1434,f1538])).

fof(f1434,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f1408])).

fof(f1536,plain,(
    ~ spl22_6 ),
    inference(avatar_split_clause,[],[f1435,f1534])).

fof(f1435,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f1408])).

fof(f1532,plain,(
    ~ spl22_5 ),
    inference(avatar_split_clause,[],[f1436,f1530])).

fof(f1436,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f1408])).

fof(f1528,plain,(
    spl22_4 ),
    inference(avatar_split_clause,[],[f1437,f1526])).

fof(f1437,plain,(
    sK3 = k3_mcart_1(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f1408])).

fof(f1524,plain,
    ( ~ spl22_1
    | ~ spl22_2
    | ~ spl22_3 ),
    inference(avatar_split_clause,[],[f1438,f1522,f1519,f1516])).

fof(f1519,plain,
    ( spl22_2
  <=> k6_mcart_1(sK0,sK1,sK2,sK3) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_2])])).

fof(f1522,plain,
    ( spl22_3
  <=> k7_mcart_1(sK0,sK1,sK2,sK3) = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_3])])).

fof(f1438,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) != sK6
    | k6_mcart_1(sK0,sK1,sK2,sK3) != sK5
    | k5_mcart_1(sK0,sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f1408])).
%------------------------------------------------------------------------------
