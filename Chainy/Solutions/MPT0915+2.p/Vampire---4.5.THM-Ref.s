%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0915+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:57 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 241 expanded)
%              Number of leaves         :   27 ( 120 expanded)
%              Depth                    :    8
%              Number of atoms          :  374 (1441 expanded)
%              Number of equality atoms :  205 (1011 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1890,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1542,f1552,f1556,f1560,f1564,f1568,f1572,f1576,f1580,f1584,f1592,f1830,f1837,f1851,f1858,f1860,f1879,f1886,f1888,f1889])).

fof(f1889,plain,
    ( sK6 != sK7
    | k7_mcart_1(sK3,sK4,sK5,sK6) != k2_mcart_1(sK6)
    | k7_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(sK6)
    | k7_mcart_1(sK0,sK1,sK2,sK6) = k7_mcart_1(sK3,sK4,sK5,sK7) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1888,plain,
    ( sK6 != sK7
    | k6_mcart_1(sK3,sK4,sK5,sK6) != k2_mcart_1(k1_mcart_1(sK6))
    | k6_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(k1_mcart_1(sK6))
    | k6_mcart_1(sK0,sK1,sK2,sK6) = k6_mcart_1(sK3,sK4,sK5,sK7) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1886,plain,
    ( spl28_36
    | spl28_7
    | spl28_8
    | spl28_9
    | ~ spl28_13 ),
    inference(avatar_split_clause,[],[f1882,f1590,f1570,f1566,f1562,f1884])).

fof(f1884,plain,
    ( spl28_36
  <=> k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_36])])).

fof(f1562,plain,
    ( spl28_7
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_7])])).

fof(f1566,plain,
    ( spl28_8
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_8])])).

fof(f1570,plain,
    ( spl28_9
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_9])])).

fof(f1590,plain,
    ( spl28_13
  <=> m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_13])])).

fof(f1882,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | spl28_7
    | spl28_8
    | spl28_9
    | ~ spl28_13 ),
    inference(subsumption_resolution,[],[f1881,f1571])).

fof(f1571,plain,
    ( k1_xboole_0 != sK3
    | spl28_9 ),
    inference(avatar_component_clause,[],[f1570])).

fof(f1881,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK3
    | spl28_7
    | spl28_8
    | ~ spl28_13 ),
    inference(subsumption_resolution,[],[f1880,f1567])).

fof(f1567,plain,
    ( k1_xboole_0 != sK4
    | spl28_8 ),
    inference(avatar_component_clause,[],[f1566])).

fof(f1880,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | spl28_7
    | ~ spl28_13 ),
    inference(subsumption_resolution,[],[f1867,f1563])).

fof(f1563,plain,
    ( k1_xboole_0 != sK5
    | spl28_7 ),
    inference(avatar_component_clause,[],[f1562])).

fof(f1867,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | ~ spl28_13 ),
    inference(resolution,[],[f1477,f1591])).

fof(f1591,plain,
    ( m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    | ~ spl28_13 ),
    inference(avatar_component_clause,[],[f1590])).

fof(f1477,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1396])).

fof(f1396,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f1879,plain,
    ( spl28_35
    | ~ spl28_6
    | spl28_10
    | spl28_11
    | spl28_12 ),
    inference(avatar_split_clause,[],[f1875,f1582,f1578,f1574,f1558,f1877])).

fof(f1877,plain,
    ( spl28_35
  <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_35])])).

fof(f1558,plain,
    ( spl28_6
  <=> m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_6])])).

fof(f1574,plain,
    ( spl28_10
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_10])])).

fof(f1578,plain,
    ( spl28_11
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_11])])).

fof(f1582,plain,
    ( spl28_12
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_12])])).

fof(f1875,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | ~ spl28_6
    | spl28_10
    | spl28_11
    | spl28_12 ),
    inference(subsumption_resolution,[],[f1874,f1583])).

fof(f1583,plain,
    ( k1_xboole_0 != sK0
    | spl28_12 ),
    inference(avatar_component_clause,[],[f1582])).

fof(f1874,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK0
    | ~ spl28_6
    | spl28_10
    | spl28_11 ),
    inference(subsumption_resolution,[],[f1873,f1579])).

fof(f1579,plain,
    ( k1_xboole_0 != sK1
    | spl28_11 ),
    inference(avatar_component_clause,[],[f1578])).

fof(f1873,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl28_6
    | spl28_10 ),
    inference(subsumption_resolution,[],[f1866,f1575])).

fof(f1575,plain,
    ( k1_xboole_0 != sK2
    | spl28_10 ),
    inference(avatar_component_clause,[],[f1574])).

fof(f1866,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl28_6 ),
    inference(resolution,[],[f1477,f1559])).

fof(f1559,plain,
    ( m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl28_6 ),
    inference(avatar_component_clause,[],[f1558])).

fof(f1860,plain,
    ( sK6 != sK7
    | k5_mcart_1(sK3,sK4,sK5,sK6) != k1_mcart_1(k1_mcart_1(sK6))
    | k5_mcart_1(sK0,sK1,sK2,sK6) != k1_mcart_1(k1_mcart_1(sK6))
    | k5_mcart_1(sK0,sK1,sK2,sK6) = k5_mcart_1(sK3,sK4,sK5,sK7) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1858,plain,
    ( spl28_33
    | spl28_7
    | spl28_8
    | spl28_9
    | ~ spl28_13 ),
    inference(avatar_split_clause,[],[f1854,f1590,f1570,f1566,f1562,f1856])).

fof(f1856,plain,
    ( spl28_33
  <=> k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_33])])).

fof(f1854,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | spl28_7
    | spl28_8
    | spl28_9
    | ~ spl28_13 ),
    inference(subsumption_resolution,[],[f1853,f1571])).

fof(f1853,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK3
    | spl28_7
    | spl28_8
    | ~ spl28_13 ),
    inference(subsumption_resolution,[],[f1852,f1567])).

fof(f1852,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | spl28_7
    | ~ spl28_13 ),
    inference(subsumption_resolution,[],[f1839,f1563])).

fof(f1839,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | ~ spl28_13 ),
    inference(resolution,[],[f1476,f1591])).

fof(f1476,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1396])).

fof(f1851,plain,
    ( spl28_32
    | ~ spl28_6
    | spl28_10
    | spl28_11
    | spl28_12 ),
    inference(avatar_split_clause,[],[f1847,f1582,f1578,f1574,f1558,f1849])).

fof(f1849,plain,
    ( spl28_32
  <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_32])])).

fof(f1847,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | ~ spl28_6
    | spl28_10
    | spl28_11
    | spl28_12 ),
    inference(subsumption_resolution,[],[f1846,f1583])).

fof(f1846,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK0
    | ~ spl28_6
    | spl28_10
    | spl28_11 ),
    inference(subsumption_resolution,[],[f1845,f1579])).

fof(f1845,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl28_6
    | spl28_10 ),
    inference(subsumption_resolution,[],[f1838,f1575])).

fof(f1838,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl28_6 ),
    inference(resolution,[],[f1476,f1559])).

fof(f1837,plain,
    ( spl28_31
    | spl28_7
    | spl28_8
    | spl28_9
    | ~ spl28_13 ),
    inference(avatar_split_clause,[],[f1833,f1590,f1570,f1566,f1562,f1835])).

fof(f1835,plain,
    ( spl28_31
  <=> k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_31])])).

fof(f1833,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
    | spl28_7
    | spl28_8
    | spl28_9
    | ~ spl28_13 ),
    inference(subsumption_resolution,[],[f1832,f1571])).

fof(f1832,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
    | k1_xboole_0 = sK3
    | spl28_7
    | spl28_8
    | ~ spl28_13 ),
    inference(subsumption_resolution,[],[f1831,f1567])).

fof(f1831,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | spl28_7
    | ~ spl28_13 ),
    inference(subsumption_resolution,[],[f1818,f1563])).

fof(f1818,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK6) = k2_mcart_1(sK6)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | ~ spl28_13 ),
    inference(resolution,[],[f1478,f1591])).

fof(f1478,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1396])).

fof(f1830,plain,
    ( spl28_30
    | ~ spl28_6
    | spl28_10
    | spl28_11
    | spl28_12 ),
    inference(avatar_split_clause,[],[f1826,f1582,f1578,f1574,f1558,f1828])).

fof(f1828,plain,
    ( spl28_30
  <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_30])])).

fof(f1826,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | ~ spl28_6
    | spl28_10
    | spl28_11
    | spl28_12 ),
    inference(subsumption_resolution,[],[f1825,f1583])).

fof(f1825,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | k1_xboole_0 = sK0
    | ~ spl28_6
    | spl28_10
    | spl28_11 ),
    inference(subsumption_resolution,[],[f1824,f1579])).

fof(f1824,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl28_6
    | spl28_10 ),
    inference(subsumption_resolution,[],[f1817,f1575])).

fof(f1817,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl28_6 ),
    inference(resolution,[],[f1478,f1559])).

fof(f1592,plain,
    ( spl28_13
    | ~ spl28_1
    | ~ spl28_5 ),
    inference(avatar_split_clause,[],[f1588,f1554,f1540,f1590])).

fof(f1540,plain,
    ( spl28_1
  <=> sK6 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_1])])).

fof(f1554,plain,
    ( spl28_5
  <=> m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_5])])).

fof(f1588,plain,
    ( m1_subset_1(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    | ~ spl28_1
    | ~ spl28_5 ),
    inference(forward_demodulation,[],[f1555,f1541])).

fof(f1541,plain,
    ( sK6 = sK7
    | ~ spl28_1 ),
    inference(avatar_component_clause,[],[f1540])).

fof(f1555,plain,
    ( m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))
    | ~ spl28_5 ),
    inference(avatar_component_clause,[],[f1554])).

fof(f1584,plain,(
    ~ spl28_12 ),
    inference(avatar_split_clause,[],[f1451,f1582])).

fof(f1451,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f1420])).

fof(f1420,plain,
    ( ( k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK7)
      | k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK7)
      | k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK7) )
    & sK6 = sK7
    & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))
    & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f1388,f1419,f1418,f1417])).

fof(f1417,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ( k7_mcart_1(X0,X1,X2,X6) != k7_mcart_1(X3,X4,X5,X7)
                  | k6_mcart_1(X0,X1,X2,X6) != k6_mcart_1(X3,X4,X5,X7)
                  | k5_mcart_1(X0,X1,X2,X6) != k5_mcart_1(X3,X4,X5,X7) )
                & X6 = X7
                & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5)) )
            & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X5
        & k1_xboole_0 != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X6] :
          ( ? [X7] :
              ( ( k7_mcart_1(sK0,sK1,sK2,X6) != k7_mcart_1(sK3,sK4,sK5,X7)
                | k6_mcart_1(sK0,sK1,sK2,X6) != k6_mcart_1(sK3,sK4,sK5,X7)
                | k5_mcart_1(sK0,sK1,sK2,X6) != k5_mcart_1(sK3,sK4,sK5,X7) )
              & X6 = X7
              & m1_subset_1(X7,k3_zfmisc_1(sK3,sK4,sK5)) )
          & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f1418,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ( k7_mcart_1(sK0,sK1,sK2,X6) != k7_mcart_1(sK3,sK4,sK5,X7)
              | k6_mcart_1(sK0,sK1,sK2,X6) != k6_mcart_1(sK3,sK4,sK5,X7)
              | k5_mcart_1(sK0,sK1,sK2,X6) != k5_mcart_1(sK3,sK4,sK5,X7) )
            & X6 = X7
            & m1_subset_1(X7,k3_zfmisc_1(sK3,sK4,sK5)) )
        & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
   => ( ? [X7] :
          ( ( k7_mcart_1(sK3,sK4,sK5,X7) != k7_mcart_1(sK0,sK1,sK2,sK6)
            | k6_mcart_1(sK3,sK4,sK5,X7) != k6_mcart_1(sK0,sK1,sK2,sK6)
            | k5_mcart_1(sK3,sK4,sK5,X7) != k5_mcart_1(sK0,sK1,sK2,sK6) )
          & sK6 = X7
          & m1_subset_1(X7,k3_zfmisc_1(sK3,sK4,sK5)) )
      & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f1419,plain,
    ( ? [X7] :
        ( ( k7_mcart_1(sK3,sK4,sK5,X7) != k7_mcart_1(sK0,sK1,sK2,sK6)
          | k6_mcart_1(sK3,sK4,sK5,X7) != k6_mcart_1(sK0,sK1,sK2,sK6)
          | k5_mcart_1(sK3,sK4,sK5,X7) != k5_mcart_1(sK0,sK1,sK2,sK6) )
        & sK6 = X7
        & m1_subset_1(X7,k3_zfmisc_1(sK3,sK4,sK5)) )
   => ( ( k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK7)
        | k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK7)
        | k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK7) )
      & sK6 = sK7
      & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f1388,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ? [X6] :
          ( ? [X7] :
              ( ( k7_mcart_1(X0,X1,X2,X6) != k7_mcart_1(X3,X4,X5,X7)
                | k6_mcart_1(X0,X1,X2,X6) != k6_mcart_1(X3,X4,X5,X7)
                | k5_mcart_1(X0,X1,X2,X6) != k5_mcart_1(X3,X4,X5,X7) )
              & X6 = X7
              & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5)) )
          & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X5
      & k1_xboole_0 != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f1384])).

fof(f1384,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ~ ( ? [X6] :
              ( ? [X7] :
                  ( ~ ( k7_mcart_1(X0,X1,X2,X6) = k7_mcart_1(X3,X4,X5,X7)
                      & k6_mcart_1(X0,X1,X2,X6) = k6_mcart_1(X3,X4,X5,X7)
                      & k5_mcart_1(X0,X1,X2,X6) = k5_mcart_1(X3,X4,X5,X7) )
                  & X6 = X7
                  & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5)) )
              & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
          & k1_xboole_0 != X5
          & k1_xboole_0 != X4
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1383])).

fof(f1383,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ~ ( ? [X6] :
            ( ? [X7] :
                ( ~ ( k7_mcart_1(X0,X1,X2,X6) = k7_mcart_1(X3,X4,X5,X7)
                    & k6_mcart_1(X0,X1,X2,X6) = k6_mcart_1(X3,X4,X5,X7)
                    & k5_mcart_1(X0,X1,X2,X6) = k5_mcart_1(X3,X4,X5,X7) )
                & X6 = X7
                & m1_subset_1(X7,k3_zfmisc_1(X3,X4,X5)) )
            & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X5
        & k1_xboole_0 != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_mcart_1)).

fof(f1580,plain,(
    ~ spl28_11 ),
    inference(avatar_split_clause,[],[f1452,f1578])).

fof(f1452,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f1420])).

fof(f1576,plain,(
    ~ spl28_10 ),
    inference(avatar_split_clause,[],[f1453,f1574])).

fof(f1453,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f1420])).

fof(f1572,plain,(
    ~ spl28_9 ),
    inference(avatar_split_clause,[],[f1454,f1570])).

fof(f1454,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f1420])).

fof(f1568,plain,(
    ~ spl28_8 ),
    inference(avatar_split_clause,[],[f1455,f1566])).

fof(f1455,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f1420])).

fof(f1564,plain,(
    ~ spl28_7 ),
    inference(avatar_split_clause,[],[f1456,f1562])).

fof(f1456,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f1420])).

fof(f1560,plain,(
    spl28_6 ),
    inference(avatar_split_clause,[],[f1457,f1558])).

fof(f1457,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f1420])).

fof(f1556,plain,(
    spl28_5 ),
    inference(avatar_split_clause,[],[f1458,f1554])).

fof(f1458,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f1420])).

fof(f1552,plain,
    ( ~ spl28_2
    | ~ spl28_3
    | ~ spl28_4 ),
    inference(avatar_split_clause,[],[f1460,f1550,f1547,f1544])).

fof(f1544,plain,
    ( spl28_2
  <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k5_mcart_1(sK3,sK4,sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_2])])).

fof(f1547,plain,
    ( spl28_3
  <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k6_mcart_1(sK3,sK4,sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_3])])).

fof(f1550,plain,
    ( spl28_4
  <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k7_mcart_1(sK3,sK4,sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_4])])).

fof(f1460,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) != k7_mcart_1(sK3,sK4,sK5,sK7)
    | k6_mcart_1(sK0,sK1,sK2,sK6) != k6_mcart_1(sK3,sK4,sK5,sK7)
    | k5_mcart_1(sK0,sK1,sK2,sK6) != k5_mcart_1(sK3,sK4,sK5,sK7) ),
    inference(cnf_transformation,[],[f1420])).

fof(f1542,plain,(
    spl28_1 ),
    inference(avatar_split_clause,[],[f1459,f1540])).

fof(f1459,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f1420])).
%------------------------------------------------------------------------------
