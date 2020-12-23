%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0895+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:56 EST 2020

% Result     : Theorem 1.82s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 213 expanded)
%              Number of leaves         :   16 (  67 expanded)
%              Depth                    :    9
%              Number of atoms          :  294 ( 797 expanded)
%              Number of equality atoms :  163 ( 621 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1965,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1707,f1708,f1709,f1710,f1711,f1716,f1721,f1725,f1728,f1781,f1823,f1873,f1934,f1964])).

fof(f1964,plain,
    ( spl22_3
    | ~ spl22_14 ),
    inference(avatar_contradiction_clause,[],[f1963])).

fof(f1963,plain,
    ( $false
    | spl22_3
    | ~ spl22_14 ),
    inference(subsumption_resolution,[],[f1950,f1697])).

fof(f1697,plain,
    ( k1_xboole_0 != sK2
    | spl22_3 ),
    inference(avatar_component_clause,[],[f1696])).

fof(f1696,plain,
    ( spl22_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_3])])).

fof(f1950,plain,
    ( k1_xboole_0 = sK2
    | ~ spl22_14 ),
    inference(resolution,[],[f1872,f1617])).

fof(f1617,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1413])).

fof(f1413,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X0,X0)) ) ),
    inference(ennf_transformation,[],[f332])).

fof(f332,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(X0,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_zfmisc_1)).

fof(f1872,plain,
    ( ! [X20] : r1_tarski(sK2,X20)
    | ~ spl22_14 ),
    inference(avatar_component_clause,[],[f1871])).

fof(f1871,plain,
    ( spl22_14
  <=> ! [X20] : r1_tarski(sK2,X20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_14])])).

fof(f1934,plain,
    ( spl22_1
    | spl22_2
    | ~ spl22_11 ),
    inference(avatar_contradiction_clause,[],[f1933])).

fof(f1933,plain,
    ( $false
    | spl22_1
    | spl22_2
    | ~ spl22_11 ),
    inference(subsumption_resolution,[],[f1932,f1693])).

fof(f1693,plain,
    ( k1_xboole_0 != sK1
    | spl22_2 ),
    inference(avatar_component_clause,[],[f1692])).

fof(f1692,plain,
    ( spl22_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_2])])).

fof(f1932,plain,
    ( k1_xboole_0 = sK1
    | spl22_1
    | ~ spl22_11 ),
    inference(subsumption_resolution,[],[f1911,f1689])).

fof(f1689,plain,
    ( k1_xboole_0 != sK0
    | spl22_1 ),
    inference(avatar_component_clause,[],[f1688])).

fof(f1688,plain,
    ( spl22_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_1])])).

fof(f1911,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl22_11 ),
    inference(trivial_inequality_removal,[],[f1905])).

fof(f1905,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl22_11 ),
    inference(superposition,[],[f1561,f1856])).

fof(f1856,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl22_11 ),
    inference(avatar_component_clause,[],[f1854])).

fof(f1854,plain,
    ( spl22_11
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_11])])).

fof(f1561,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f1459])).

fof(f1459,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f1458])).

fof(f1458,plain,(
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

fof(f1873,plain,
    ( spl22_11
    | spl22_14
    | ~ spl22_6 ),
    inference(avatar_split_clause,[],[f1869,f1762,f1871,f1854])).

fof(f1762,plain,
    ( spl22_6
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_6])])).

fof(f1869,plain,
    ( ! [X20] :
        ( r1_tarski(sK2,X20)
        | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) )
    | ~ spl22_6 ),
    inference(subsumption_resolution,[],[f1837,f1646])).

fof(f1646,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1837,plain,
    ( ! [X20] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X20))
        | r1_tarski(sK2,X20)
        | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) )
    | ~ spl22_6 ),
    inference(superposition,[],[f1522,f1764])).

fof(f1764,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl22_6 ),
    inference(avatar_component_clause,[],[f1762])).

fof(f1522,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1371])).

fof(f1371,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f333])).

fof(f333,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f1823,plain,
    ( spl22_4
    | ~ spl22_9 ),
    inference(avatar_contradiction_clause,[],[f1822])).

fof(f1822,plain,
    ( $false
    | spl22_4
    | ~ spl22_9 ),
    inference(subsumption_resolution,[],[f1809,f1701])).

fof(f1701,plain,
    ( k1_xboole_0 != sK3
    | spl22_4 ),
    inference(avatar_component_clause,[],[f1700])).

fof(f1700,plain,
    ( spl22_4
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_4])])).

fof(f1809,plain,
    ( k1_xboole_0 = sK3
    | ~ spl22_9 ),
    inference(resolution,[],[f1780,f1617])).

fof(f1780,plain,
    ( ! [X20] : r1_tarski(sK3,X20)
    | ~ spl22_9 ),
    inference(avatar_component_clause,[],[f1779])).

fof(f1779,plain,
    ( spl22_9
  <=> ! [X20] : r1_tarski(sK3,X20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_9])])).

fof(f1781,plain,
    ( spl22_6
    | spl22_9
    | ~ spl22_5 ),
    inference(avatar_split_clause,[],[f1777,f1704,f1779,f1762])).

fof(f1704,plain,
    ( spl22_5
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_5])])).

fof(f1777,plain,
    ( ! [X20] :
        ( r1_tarski(sK3,X20)
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) )
    | ~ spl22_5 ),
    inference(subsumption_resolution,[],[f1745,f1646])).

fof(f1745,plain,
    ( ! [X20] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),X20))
        | r1_tarski(sK3,X20)
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) )
    | ~ spl22_5 ),
    inference(superposition,[],[f1522,f1706])).

fof(f1706,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl22_5 ),
    inference(avatar_component_clause,[],[f1704])).

fof(f1728,plain,
    ( ~ spl22_4
    | spl22_5 ),
    inference(avatar_contradiction_clause,[],[f1727])).

fof(f1727,plain,
    ( $false
    | ~ spl22_4
    | spl22_5 ),
    inference(subsumption_resolution,[],[f1726,f1676])).

fof(f1676,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f1563])).

fof(f1563,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f1459])).

fof(f1726,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k1_xboole_0)
    | ~ spl22_4
    | spl22_5 ),
    inference(forward_demodulation,[],[f1705,f1702])).

fof(f1702,plain,
    ( k1_xboole_0 = sK3
    | ~ spl22_4 ),
    inference(avatar_component_clause,[],[f1700])).

fof(f1705,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | spl22_5 ),
    inference(avatar_component_clause,[],[f1704])).

fof(f1725,plain,
    ( ~ spl22_3
    | spl22_5 ),
    inference(avatar_contradiction_clause,[],[f1724])).

fof(f1724,plain,
    ( $false
    | ~ spl22_3
    | spl22_5 ),
    inference(subsumption_resolution,[],[f1723,f1677])).

fof(f1677,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f1562])).

fof(f1562,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f1459])).

fof(f1723,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl22_3
    | spl22_5 ),
    inference(forward_demodulation,[],[f1722,f1676])).

fof(f1722,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0),sK3)
    | ~ spl22_3
    | spl22_5 ),
    inference(forward_demodulation,[],[f1705,f1698])).

fof(f1698,plain,
    ( k1_xboole_0 = sK2
    | ~ spl22_3 ),
    inference(avatar_component_clause,[],[f1696])).

fof(f1721,plain,
    ( ~ spl22_1
    | spl22_5 ),
    inference(avatar_contradiction_clause,[],[f1720])).

fof(f1720,plain,
    ( $false
    | ~ spl22_1
    | spl22_5 ),
    inference(subsumption_resolution,[],[f1719,f1677])).

fof(f1719,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl22_1
    | spl22_5 ),
    inference(forward_demodulation,[],[f1718,f1677])).

fof(f1718,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3)
    | ~ spl22_1
    | spl22_5 ),
    inference(forward_demodulation,[],[f1717,f1677])).

fof(f1717,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1),sK2),sK3)
    | ~ spl22_1
    | spl22_5 ),
    inference(forward_demodulation,[],[f1705,f1690])).

fof(f1690,plain,
    ( k1_xboole_0 = sK0
    | ~ spl22_1 ),
    inference(avatar_component_clause,[],[f1688])).

fof(f1716,plain,
    ( ~ spl22_2
    | spl22_5 ),
    inference(avatar_contradiction_clause,[],[f1715])).

fof(f1715,plain,
    ( $false
    | ~ spl22_2
    | spl22_5 ),
    inference(subsumption_resolution,[],[f1714,f1677])).

fof(f1714,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | ~ spl22_2
    | spl22_5 ),
    inference(forward_demodulation,[],[f1713,f1677])).

fof(f1713,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2),sK3)
    | ~ spl22_2
    | spl22_5 ),
    inference(forward_demodulation,[],[f1712,f1676])).

fof(f1712,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2),sK3)
    | ~ spl22_2
    | spl22_5 ),
    inference(forward_demodulation,[],[f1705,f1694])).

fof(f1694,plain,
    ( k1_xboole_0 = sK1
    | ~ spl22_2 ),
    inference(avatar_component_clause,[],[f1692])).

fof(f1711,plain,
    ( ~ spl22_1
    | ~ spl22_5 ),
    inference(avatar_split_clause,[],[f1656,f1704,f1688])).

fof(f1656,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f1494,f1499])).

fof(f1499,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f1350])).

fof(f1350,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).

fof(f1494,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f1436])).

fof(f1436,plain,
    ( ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
      | k1_xboole_0 = sK3
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 )
    & ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
      | ( k1_xboole_0 != sK3
        & k1_xboole_0 != sK2
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f1434,f1435])).

fof(f1435,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 )
        & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
          | ( k1_xboole_0 != X3
            & k1_xboole_0 != X2
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0 ) ) )
   => ( ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
        | k1_xboole_0 = sK3
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
      & ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
        | ( k1_xboole_0 != sK3
          & k1_xboole_0 != sK2
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0 ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1434,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(flattening,[],[f1433])).

fof(f1433,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(nnf_transformation,[],[f1362])).

fof(f1362,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <~> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(ennf_transformation,[],[f1353])).

fof(f1353,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
      <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(negated_conjecture,[],[f1352])).

fof(f1352,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f1710,plain,
    ( ~ spl22_2
    | ~ spl22_5 ),
    inference(avatar_split_clause,[],[f1655,f1704,f1692])).

fof(f1655,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f1495,f1499])).

fof(f1495,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f1436])).

fof(f1709,plain,
    ( ~ spl22_3
    | ~ spl22_5 ),
    inference(avatar_split_clause,[],[f1654,f1704,f1696])).

fof(f1654,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f1496,f1499])).

fof(f1496,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f1436])).

fof(f1708,plain,
    ( ~ spl22_4
    | ~ spl22_5 ),
    inference(avatar_split_clause,[],[f1653,f1704,f1700])).

fof(f1653,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f1497,f1499])).

fof(f1497,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f1436])).

fof(f1707,plain,
    ( spl22_1
    | spl22_2
    | spl22_3
    | spl22_4
    | spl22_5 ),
    inference(avatar_split_clause,[],[f1652,f1704,f1700,f1696,f1692,f1688])).

fof(f1652,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(definition_unfolding,[],[f1498,f1499])).

fof(f1498,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f1436])).
%------------------------------------------------------------------------------
