%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0909+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:57 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 255 expanded)
%              Number of leaves         :   22 ( 115 expanded)
%              Depth                    :   13
%              Number of atoms          :  496 (1213 expanded)
%              Number of equality atoms :  215 ( 587 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2003,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1477,f1481,f1485,f1489,f1493,f1685,f1699,f1713,f1741,f1776,f1796,f1858,f1952,f1998])).

fof(f1998,plain,
    ( spl14_1
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5
    | ~ spl14_16
    | ~ spl14_24 ),
    inference(avatar_contradiction_clause,[],[f1995])).

fof(f1995,plain,
    ( $false
    | spl14_1
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5
    | ~ spl14_16
    | ~ spl14_24 ),
    inference(unit_resulting_resolution,[],[f1488,f1484,f1480,f1795,f1492,f1476,f1949,f1426])).

fof(f1426,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sK5(X3,X4) != X4
      | k5_mcart_1(X0,X1,X2,X3) = X4
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1404])).

fof(f1404,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k5_mcart_1(X0,X1,X2,X3) = X4
                  | ( sK5(X3,X4) != X4
                    & k3_mcart_1(sK5(X3,X4),sK6(X3,X4),sK7(X3,X4)) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X8
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k5_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f1402,f1403])).

fof(f1403,plain,(
    ! [X4,X3] :
      ( ? [X5,X6,X7] :
          ( X4 != X5
          & k3_mcart_1(X5,X6,X7) = X3 )
     => ( sK5(X3,X4) != X4
        & k3_mcart_1(sK5(X3,X4),sK6(X3,X4),sK7(X3,X4)) = X3 ) ) ),
    introduced(choice_axiom,[])).

fof(f1402,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k5_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X5
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X8,X9,X10] :
                      ( X4 = X8
                      | k3_mcart_1(X8,X9,X10) != X3 )
                  | k5_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f1401])).

fof(f1401,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( ( k5_mcart_1(X0,X1,X2,X3) = X4
                  | ? [X5,X6,X7] :
                      ( X4 != X5
                      & k3_mcart_1(X5,X6,X7) = X3 ) )
                & ( ! [X5,X6,X7] :
                      ( X4 = X5
                      | k3_mcart_1(X5,X6,X7) != X3 )
                  | k5_mcart_1(X0,X1,X2,X3) != X4 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f1385])).

fof(f1385,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ( k5_mcart_1(X0,X1,X2,X3) = X4
              <=> ! [X5,X6,X7] :
                    ( X4 = X5
                    | k3_mcart_1(X5,X6,X7) != X3 ) )
              | ~ m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1280])).

fof(f1280,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ( k5_mcart_1(X0,X1,X2,X3) = X4
                  <=> ! [X5,X6,X7] :
                        ( k3_mcart_1(X5,X6,X7) = X3
                       => X4 = X5 ) ) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_mcart_1)).

fof(f1949,plain,
    ( sK3 = sK5(sK4,sK3)
    | ~ spl14_24 ),
    inference(avatar_component_clause,[],[f1948])).

fof(f1948,plain,
    ( spl14_24
  <=> sK3 = sK5(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_24])])).

fof(f1476,plain,
    ( sK3 != k5_mcart_1(sK0,sK1,sK2,sK4)
    | spl14_1 ),
    inference(avatar_component_clause,[],[f1475])).

fof(f1475,plain,
    ( spl14_1
  <=> sK3 = k5_mcart_1(sK0,sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f1492,plain,
    ( m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl14_5 ),
    inference(avatar_component_clause,[],[f1491])).

fof(f1491,plain,
    ( spl14_5
  <=> m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f1795,plain,
    ( m1_subset_1(sK3,sK0)
    | ~ spl14_16 ),
    inference(avatar_component_clause,[],[f1794])).

fof(f1794,plain,
    ( spl14_16
  <=> m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_16])])).

fof(f1480,plain,
    ( k1_xboole_0 != sK2
    | spl14_2 ),
    inference(avatar_component_clause,[],[f1479])).

fof(f1479,plain,
    ( spl14_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f1484,plain,
    ( k1_xboole_0 != sK1
    | spl14_3 ),
    inference(avatar_component_clause,[],[f1483])).

fof(f1483,plain,
    ( spl14_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f1488,plain,
    ( k1_xboole_0 != sK0
    | spl14_4 ),
    inference(avatar_component_clause,[],[f1487])).

fof(f1487,plain,
    ( spl14_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f1952,plain,
    ( spl14_24
    | ~ spl14_13
    | ~ spl14_14
    | ~ spl14_17 ),
    inference(avatar_split_clause,[],[f1951,f1856,f1774,f1739,f1948])).

fof(f1739,plain,
    ( spl14_13
  <=> sK4 = k3_mcart_1(sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4),sK11(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_13])])).

fof(f1774,plain,
    ( spl14_14
  <=> sK3 = sK9(sK0,sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).

fof(f1856,plain,
    ( spl14_17
  <=> sK4 = k3_mcart_1(sK5(sK4,sK3),sK6(sK4,sK3),sK7(sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_17])])).

fof(f1951,plain,
    ( sK3 = sK5(sK4,sK3)
    | ~ spl14_13
    | ~ spl14_14
    | ~ spl14_17 ),
    inference(forward_demodulation,[],[f1936,f1775])).

fof(f1775,plain,
    ( sK3 = sK9(sK0,sK1,sK2,sK4)
    | ~ spl14_14 ),
    inference(avatar_component_clause,[],[f1774])).

fof(f1936,plain,
    ( sK9(sK0,sK1,sK2,sK4) = sK5(sK4,sK3)
    | ~ spl14_13
    | ~ spl14_17 ),
    inference(trivial_inequality_removal,[],[f1928])).

fof(f1928,plain,
    ( sK4 != sK4
    | sK9(sK0,sK1,sK2,sK4) = sK5(sK4,sK3)
    | ~ spl14_13
    | ~ spl14_17 ),
    inference(superposition,[],[f1743,f1857])).

fof(f1857,plain,
    ( sK4 = k3_mcart_1(sK5(sK4,sK3),sK6(sK4,sK3),sK7(sK4,sK3))
    | ~ spl14_17 ),
    inference(avatar_component_clause,[],[f1856])).

fof(f1743,plain,
    ( ! [X2,X0,X1] :
        ( k3_mcart_1(X0,X1,X2) != sK4
        | sK9(sK0,sK1,sK2,sK4) = X0 )
    | ~ spl14_13 ),
    inference(superposition,[],[f1430,f1740])).

fof(f1740,plain,
    ( sK4 = k3_mcart_1(sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4),sK11(sK0,sK1,sK2,sK4))
    | ~ spl14_13 ),
    inference(avatar_component_clause,[],[f1739])).

fof(f1430,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f1388])).

fof(f1388,plain,(
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

fof(f1858,plain,
    ( spl14_17
    | spl14_1
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5
    | ~ spl14_16 ),
    inference(avatar_split_clause,[],[f1854,f1794,f1491,f1487,f1483,f1479,f1475,f1856])).

fof(f1854,plain,
    ( sK4 = k3_mcart_1(sK5(sK4,sK3),sK6(sK4,sK3),sK7(sK4,sK3))
    | spl14_1
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5
    | ~ spl14_16 ),
    inference(subsumption_resolution,[],[f1852,f1476])).

fof(f1852,plain,
    ( sK4 = k3_mcart_1(sK5(sK4,sK3),sK6(sK4,sK3),sK7(sK4,sK3))
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK4)
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5
    | ~ spl14_16 ),
    inference(resolution,[],[f1786,f1795])).

fof(f1786,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,sK0)
        | sK4 = k3_mcart_1(sK5(sK4,X5),sK6(sK4,X5),sK7(sK4,X5))
        | k5_mcart_1(sK0,sK1,sK2,sK4) = X5 )
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1785,f1488])).

fof(f1785,plain,
    ( ! [X5] :
        ( sK4 = k3_mcart_1(sK5(sK4,X5),sK6(sK4,X5),sK7(sK4,X5))
        | ~ m1_subset_1(X5,sK0)
        | k5_mcart_1(sK0,sK1,sK2,sK4) = X5
        | k1_xboole_0 = sK0 )
    | spl14_2
    | spl14_3
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1784,f1484])).

fof(f1784,plain,
    ( ! [X5] :
        ( sK4 = k3_mcart_1(sK5(sK4,X5),sK6(sK4,X5),sK7(sK4,X5))
        | ~ m1_subset_1(X5,sK0)
        | k5_mcart_1(sK0,sK1,sK2,sK4) = X5
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | spl14_2
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1778,f1480])).

fof(f1778,plain,
    ( ! [X5] :
        ( sK4 = k3_mcart_1(sK5(sK4,X5),sK6(sK4,X5),sK7(sK4,X5))
        | ~ m1_subset_1(X5,sK0)
        | k5_mcart_1(sK0,sK1,sK2,sK4) = X5
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl14_5 ),
    inference(resolution,[],[f1425,f1492])).

fof(f1425,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(sK5(X3,X4),sK6(X3,X4),sK7(X3,X4)) = X3
      | ~ m1_subset_1(X4,X0)
      | k5_mcart_1(X0,X1,X2,X3) = X4
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1404])).

fof(f1796,plain,
    ( spl14_16
    | ~ spl14_10
    | ~ spl14_14 ),
    inference(avatar_split_clause,[],[f1788,f1774,f1683,f1794])).

fof(f1683,plain,
    ( spl14_10
  <=> m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).

fof(f1788,plain,
    ( m1_subset_1(sK3,sK0)
    | ~ spl14_10
    | ~ spl14_14 ),
    inference(backward_demodulation,[],[f1684,f1775])).

fof(f1684,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK0)
    | ~ spl14_10 ),
    inference(avatar_component_clause,[],[f1683])).

fof(f1776,plain,
    ( spl14_14
    | ~ spl14_10
    | ~ spl14_11
    | ~ spl14_12
    | ~ spl14_13 ),
    inference(avatar_split_clause,[],[f1772,f1739,f1711,f1697,f1683,f1774])).

fof(f1697,plain,
    ( spl14_11
  <=> m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_11])])).

fof(f1711,plain,
    ( spl14_12
  <=> m1_subset_1(sK11(sK0,sK1,sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).

fof(f1772,plain,
    ( sK3 = sK9(sK0,sK1,sK2,sK4)
    | ~ spl14_10
    | ~ spl14_11
    | ~ spl14_12
    | ~ spl14_13 ),
    inference(subsumption_resolution,[],[f1771,f1684])).

fof(f1771,plain,
    ( sK3 = sK9(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK0)
    | ~ spl14_11
    | ~ spl14_12
    | ~ spl14_13 ),
    inference(subsumption_resolution,[],[f1770,f1698])).

fof(f1698,plain,
    ( m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK1)
    | ~ spl14_11 ),
    inference(avatar_component_clause,[],[f1697])).

fof(f1770,plain,
    ( sK3 = sK9(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK0)
    | ~ spl14_12
    | ~ spl14_13 ),
    inference(subsumption_resolution,[],[f1769,f1712])).

fof(f1712,plain,
    ( m1_subset_1(sK11(sK0,sK1,sK2,sK4),sK2)
    | ~ spl14_12 ),
    inference(avatar_component_clause,[],[f1711])).

fof(f1769,plain,
    ( sK3 = sK9(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK0)
    | ~ spl14_13 ),
    inference(trivial_inequality_removal,[],[f1742])).

fof(f1742,plain,
    ( sK4 != sK4
    | sK3 = sK9(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK0)
    | ~ spl14_13 ),
    inference(superposition,[],[f1418,f1740])).

fof(f1418,plain,(
    ! [X6,X7,X5] :
      ( k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X5
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f1400])).

fof(f1400,plain,
    ( sK3 != k5_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X5
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f1383,f1399])).

fof(f1399,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k5_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X5
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k5_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X5
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f1383,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f1382])).

fof(f1382,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f1377])).

fof(f1377,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X5 ) ) ) )
         => ( k5_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f1376])).

fof(f1376,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X5 ) ) ) )
       => ( k5_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).

fof(f1741,plain,
    ( spl14_13
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(avatar_split_clause,[],[f1737,f1491,f1487,f1483,f1479,f1739])).

fof(f1737,plain,
    ( sK4 = k3_mcart_1(sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4),sK11(sK0,sK1,sK2,sK4))
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1736,f1488])).

fof(f1736,plain,
    ( sK4 = k3_mcart_1(sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4),sK11(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK0
    | spl14_2
    | spl14_3
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1735,f1484])).

fof(f1735,plain,
    ( sK4 = k3_mcart_1(sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4),sK11(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl14_2
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1729,f1480])).

fof(f1729,plain,
    ( sK4 = k3_mcart_1(sK9(sK0,sK1,sK2,sK4),sK10(sK0,sK1,sK2,sK4),sK11(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl14_5 ),
    inference(resolution,[],[f1443,f1492])).

fof(f1443,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3),sK11(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1410])).

fof(f1410,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k3_mcart_1(sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3),sK11(X0,X1,X2,X3)) = X3
            & m1_subset_1(sK11(X0,X1,X2,X3),X2)
            & m1_subset_1(sK10(X0,X1,X2,X3),X1)
            & m1_subset_1(sK9(X0,X1,X2,X3),X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f1389,f1409,f1408,f1407])).

fof(f1407,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( k3_mcart_1(X4,X5,X6) = X3
                  & m1_subset_1(X6,X2) )
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ? [X6] :
                ( k3_mcart_1(sK9(X0,X1,X2,X3),X5,X6) = X3
                & m1_subset_1(X6,X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK9(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1408,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( k3_mcart_1(sK9(X0,X1,X2,X3),X5,X6) = X3
              & m1_subset_1(X6,X2) )
          & m1_subset_1(X5,X1) )
     => ( ? [X6] :
            ( k3_mcart_1(sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3),X6) = X3
            & m1_subset_1(X6,X2) )
        & m1_subset_1(sK10(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f1409,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( k3_mcart_1(sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3),X6) = X3
          & m1_subset_1(X6,X2) )
     => ( k3_mcart_1(sK9(X0,X1,X2,X3),sK10(X0,X1,X2,X3),sK11(X0,X1,X2,X3)) = X3
        & m1_subset_1(sK11(X0,X1,X2,X3),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f1389,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( k3_mcart_1(X4,X5,X6) = X3
                      & m1_subset_1(X6,X2) )
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1299])).

fof(f1299,axiom,(
    ! [X0,X1,X2] :
      ~ ( ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ! [X6] :
                        ( m1_subset_1(X6,X2)
                       => k3_mcart_1(X4,X5,X6) != X3 ) ) )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).

fof(f1713,plain,
    ( spl14_12
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(avatar_split_clause,[],[f1709,f1491,f1487,f1483,f1479,f1711])).

fof(f1709,plain,
    ( m1_subset_1(sK11(sK0,sK1,sK2,sK4),sK2)
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1708,f1488])).

fof(f1708,plain,
    ( m1_subset_1(sK11(sK0,sK1,sK2,sK4),sK2)
    | k1_xboole_0 = sK0
    | spl14_2
    | spl14_3
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1707,f1484])).

fof(f1707,plain,
    ( m1_subset_1(sK11(sK0,sK1,sK2,sK4),sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl14_2
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1701,f1480])).

fof(f1701,plain,
    ( m1_subset_1(sK11(sK0,sK1,sK2,sK4),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl14_5 ),
    inference(resolution,[],[f1442,f1492])).

fof(f1442,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK11(X0,X1,X2,X3),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1410])).

fof(f1699,plain,
    ( spl14_11
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(avatar_split_clause,[],[f1695,f1491,f1487,f1483,f1479,f1697])).

fof(f1695,plain,
    ( m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK1)
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1694,f1488])).

fof(f1694,plain,
    ( m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK1)
    | k1_xboole_0 = sK0
    | spl14_2
    | spl14_3
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1693,f1484])).

fof(f1693,plain,
    ( m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl14_2
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1687,f1480])).

fof(f1687,plain,
    ( m1_subset_1(sK10(sK0,sK1,sK2,sK4),sK1)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl14_5 ),
    inference(resolution,[],[f1441,f1492])).

fof(f1441,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK10(X0,X1,X2,X3),X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1410])).

fof(f1685,plain,
    ( spl14_10
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(avatar_split_clause,[],[f1681,f1491,f1487,f1483,f1479,f1683])).

fof(f1681,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK0)
    | spl14_2
    | spl14_3
    | spl14_4
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1680,f1488])).

fof(f1680,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK0)
    | k1_xboole_0 = sK0
    | spl14_2
    | spl14_3
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1679,f1484])).

fof(f1679,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl14_2
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f1673,f1480])).

fof(f1673,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK2,sK4),sK0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl14_5 ),
    inference(resolution,[],[f1440,f1492])).

fof(f1440,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK9(X0,X1,X2,X3),X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1410])).

fof(f1493,plain,(
    spl14_5 ),
    inference(avatar_split_clause,[],[f1417,f1491])).

fof(f1417,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f1400])).

fof(f1489,plain,(
    ~ spl14_4 ),
    inference(avatar_split_clause,[],[f1419,f1487])).

fof(f1419,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f1400])).

fof(f1485,plain,(
    ~ spl14_3 ),
    inference(avatar_split_clause,[],[f1420,f1483])).

fof(f1420,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f1400])).

fof(f1481,plain,(
    ~ spl14_2 ),
    inference(avatar_split_clause,[],[f1421,f1479])).

fof(f1421,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f1400])).

fof(f1477,plain,(
    ~ spl14_1 ),
    inference(avatar_split_clause,[],[f1422,f1475])).

fof(f1422,plain,(
    sK3 != k5_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f1400])).
%------------------------------------------------------------------------------
