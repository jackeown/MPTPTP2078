%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0380+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:27 EST 2020

% Result     : Theorem 18.54s
% Output     : Refutation 18.54s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 193 expanded)
%              Number of leaves         :   32 (  77 expanded)
%              Depth                    :    8
%              Number of atoms          :  318 ( 776 expanded)
%              Number of equality atoms :   38 (  78 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1966,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1561,f1566,f1571,f1576,f1581,f1586,f1591,f1597,f1602,f1607,f1623,f1721,f1804,f1813,f1815,f1827,f1836,f1920,f1944,f1946,f1965])).

fof(f1965,plain,
    ( spl40_26
    | ~ spl40_31 ),
    inference(avatar_split_clause,[],[f1842,f1727,f1699])).

fof(f1699,plain,
    ( spl40_26
  <=> r2_hidden(sK8,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_26])])).

fof(f1727,plain,
    ( spl40_31
  <=> m1_subset_1(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_31])])).

fof(f1842,plain,
    ( r2_hidden(sK8,sK0)
    | ~ spl40_31 ),
    inference(resolution,[],[f1810,f1479])).

fof(f1479,plain,(
    ! [X4,X2,X0,X8,X5,X3,X1] : r2_hidden(X8,k5_enumset1(X0,X1,X2,X3,X4,X5,X8)) ),
    inference(equality_resolution,[],[f1478])).

fof(f1478,plain,(
    ! [X4,X2,X0,X8,X7,X5,X3,X1] :
      ( r2_hidden(X8,X7)
      | k5_enumset1(X0,X1,X2,X3,X4,X5,X8) != X7 ) ),
    inference(equality_resolution,[],[f876])).

fof(f876,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( X6 != X8
      | r2_hidden(X8,X7)
      | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(cnf_transformation,[],[f597])).

fof(f597,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ( X6 = X8
            | X5 = X8
            | X4 = X8
            | X3 = X8
            | X2 = X8
            | X1 = X8
            | X0 = X8 ) ) ) ),
    inference(ennf_transformation,[],[f461])).

fof(f461,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X6 != X8
              & X5 != X8
              & X4 != X8
              & X3 != X8
              & X2 != X8
              & X1 != X8
              & X0 != X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_enumset1)).

fof(f1810,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8))
        | r2_hidden(X0,sK0) )
    | ~ spl40_31 ),
    inference(resolution,[],[f1728,f803])).

fof(f803,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f565])).

fof(f565,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f487])).

fof(f487,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f1728,plain,
    ( m1_subset_1(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK0))
    | ~ spl40_31 ),
    inference(avatar_component_clause,[],[f1727])).

fof(f1946,plain,
    ( ~ spl40_11
    | ~ spl40_26 ),
    inference(avatar_split_clause,[],[f1793,f1699,f1611])).

fof(f1611,plain,
    ( spl40_11
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_11])])).

fof(f1793,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl40_26 ),
    inference(resolution,[],[f1701,f1067])).

fof(f1067,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f1701,plain,
    ( r2_hidden(sK8,sK0)
    | ~ spl40_26 ),
    inference(avatar_component_clause,[],[f1699])).

fof(f1944,plain,
    ( ~ spl40_13
    | spl40_55 ),
    inference(avatar_split_clause,[],[f1941,f1917,f1620])).

fof(f1620,plain,
    ( spl40_13
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_13])])).

fof(f1917,plain,
    ( spl40_55
  <=> r1_tarski(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_55])])).

fof(f1941,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl40_55 ),
    inference(resolution,[],[f1919,f846])).

fof(f846,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f395])).

fof(f395,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f1919,plain,
    ( ~ r1_tarski(k1_tarski(sK1),sK0)
    | spl40_55 ),
    inference(avatar_component_clause,[],[f1917])).

fof(f1920,plain,
    ( ~ spl40_55
    | ~ spl40_43
    | spl40_42 ),
    inference(avatar_split_clause,[],[f1911,f1824,f1833,f1917])).

fof(f1833,plain,
    ( spl40_43
  <=> r1_tarski(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_43])])).

fof(f1824,plain,
    ( spl40_42
  <=> r1_tarski(k2_xboole_0(k1_tarski(sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_42])])).

fof(f1911,plain,
    ( ~ r1_tarski(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | ~ r1_tarski(k1_tarski(sK1),sK0)
    | spl40_42 ),
    inference(resolution,[],[f1826,f816])).

fof(f816,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f579])).

fof(f579,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f578])).

fof(f578,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f161])).

fof(f161,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f1826,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)),sK0)
    | spl40_42 ),
    inference(avatar_component_clause,[],[f1824])).

fof(f1836,plain,
    ( spl40_43
    | ~ spl40_41 ),
    inference(avatar_split_clause,[],[f1828,f1806,f1833])).

fof(f1806,plain,
    ( spl40_41
  <=> r2_hidden(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_41])])).

fof(f1828,plain,
    ( r1_tarski(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),sK0)
    | ~ spl40_41 ),
    inference(resolution,[],[f1807,f1435])).

fof(f1435,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f690])).

fof(f690,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f285])).

fof(f285,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f1807,plain,
    ( r2_hidden(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK0))
    | ~ spl40_41 ),
    inference(avatar_component_clause,[],[f1806])).

fof(f1827,plain,
    ( ~ spl40_42
    | spl40_29 ),
    inference(avatar_split_clause,[],[f1819,f1718,f1824])).

fof(f1718,plain,
    ( spl40_29
  <=> r2_hidden(k2_xboole_0(k1_tarski(sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_29])])).

fof(f1819,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)),sK0)
    | spl40_29 ),
    inference(resolution,[],[f1720,f1436])).

fof(f1436,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f689])).

fof(f689,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f285])).

fof(f1720,plain,
    ( ~ r2_hidden(k2_xboole_0(k1_tarski(sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k1_zfmisc_1(sK0))
    | spl40_29 ),
    inference(avatar_component_clause,[],[f1718])).

fof(f1815,plain,(
    ~ spl40_28 ),
    inference(avatar_contradiction_clause,[],[f1814])).

fof(f1814,plain,
    ( $false
    | ~ spl40_28 ),
    inference(resolution,[],[f1716,f1075])).

fof(f1075,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f476])).

fof(f476,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f1716,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl40_28 ),
    inference(avatar_component_clause,[],[f1714])).

fof(f1714,plain,
    ( spl40_28
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_28])])).

fof(f1813,plain,
    ( spl40_28
    | spl40_41
    | ~ spl40_31 ),
    inference(avatar_split_clause,[],[f1812,f1727,f1806,f1714])).

fof(f1812,plain,
    ( r2_hidden(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl40_31 ),
    inference(resolution,[],[f1728,f1062])).

fof(f1062,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f639])).

fof(f639,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f456])).

fof(f456,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f1804,plain,
    ( ~ spl40_2
    | spl40_9
    | ~ spl40_10
    | ~ spl40_7
    | ~ spl40_6
    | ~ spl40_5
    | ~ spl40_4
    | ~ spl40_3
    | spl40_31 ),
    inference(avatar_split_clause,[],[f1801,f1727,f1568,f1573,f1578,f1583,f1588,f1604,f1599,f1563])).

fof(f1563,plain,
    ( spl40_2
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_2])])).

fof(f1599,plain,
    ( spl40_9
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_9])])).

fof(f1604,plain,
    ( spl40_10
  <=> m1_subset_1(sK8,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_10])])).

fof(f1588,plain,
    ( spl40_7
  <=> m1_subset_1(sK7,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_7])])).

fof(f1583,plain,
    ( spl40_6
  <=> m1_subset_1(sK6,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_6])])).

fof(f1578,plain,
    ( spl40_5
  <=> m1_subset_1(sK5,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_5])])).

fof(f1573,plain,
    ( spl40_4
  <=> m1_subset_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_4])])).

fof(f1568,plain,
    ( spl40_3
  <=> m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_3])])).

fof(f1801,plain,
    ( ~ m1_subset_1(sK3,sK0)
    | ~ m1_subset_1(sK4,sK0)
    | ~ m1_subset_1(sK5,sK0)
    | ~ m1_subset_1(sK6,sK0)
    | ~ m1_subset_1(sK7,sK0)
    | ~ m1_subset_1(sK8,sK0)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK2,sK0)
    | spl40_31 ),
    inference(resolution,[],[f1729,f889])).

fof(f889,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X5,X0)
      | ~ m1_subset_1(X6,X0)
      | ~ m1_subset_1(X7,X0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f599])).

fof(f599,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( ! [X6] :
                          ( ! [X7] :
                              ( m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                              | k1_xboole_0 = X0
                              | ~ m1_subset_1(X7,X0) )
                          | ~ m1_subset_1(X6,X0) )
                      | ~ m1_subset_1(X5,X0) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f598])).

fof(f598,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( ! [X6] :
                          ( ! [X7] :
                              ( m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0))
                              | k1_xboole_0 = X0
                              | ~ m1_subset_1(X7,X0) )
                          | ~ m1_subset_1(X6,X0) )
                      | ~ m1_subset_1(X5,X0) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f532])).

fof(f532,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ! [X5] :
                      ( m1_subset_1(X5,X0)
                     => ! [X6] :
                          ( m1_subset_1(X6,X0)
                         => ! [X7] :
                              ( m1_subset_1(X7,X0)
                             => ( k1_xboole_0 != X0
                               => m1_subset_1(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_subset_1)).

fof(f1729,plain,
    ( ~ m1_subset_1(k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK0))
    | spl40_31 ),
    inference(avatar_component_clause,[],[f1727])).

fof(f1721,plain,
    ( spl40_28
    | ~ spl40_29
    | spl40_8 ),
    inference(avatar_split_clause,[],[f1709,f1594,f1718,f1714])).

fof(f1594,plain,
    ( spl40_8
  <=> m1_subset_1(k2_xboole_0(k1_tarski(sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_8])])).

fof(f1709,plain,
    ( ~ r2_hidden(k2_xboole_0(k1_tarski(sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | spl40_8 ),
    inference(resolution,[],[f1596,f1061])).

fof(f1061,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f639])).

fof(f1596,plain,
    ( ~ m1_subset_1(k2_xboole_0(k1_tarski(sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k1_zfmisc_1(sK0))
    | spl40_8 ),
    inference(avatar_component_clause,[],[f1594])).

fof(f1623,plain,
    ( spl40_11
    | spl40_13
    | ~ spl40_1 ),
    inference(avatar_split_clause,[],[f1609,f1558,f1620,f1611])).

fof(f1558,plain,
    ( spl40_1
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_1])])).

fof(f1609,plain,
    ( r2_hidden(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl40_1 ),
    inference(resolution,[],[f1560,f1062])).

fof(f1560,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl40_1 ),
    inference(avatar_component_clause,[],[f1558])).

fof(f1607,plain,(
    spl40_10 ),
    inference(avatar_split_clause,[],[f679,f1604])).

fof(f679,plain,(
    m1_subset_1(sK8,sK0) ),
    inference(cnf_transformation,[],[f542])).

fof(f542,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ? [X8] :
                                  ( ~ m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
                                  & k1_xboole_0 != X0
                                  & m1_subset_1(X8,X0) )
                              & m1_subset_1(X7,X0) )
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f541])).

fof(f541,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ? [X8] :
                                  ( ~ m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
                                  & k1_xboole_0 != X0
                                  & m1_subset_1(X8,X0) )
                              & m1_subset_1(X7,X0) )
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f534])).

fof(f534,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ! [X3] :
                ( m1_subset_1(X3,X0)
               => ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ! [X5] :
                        ( m1_subset_1(X5,X0)
                       => ! [X6] :
                            ( m1_subset_1(X6,X0)
                           => ! [X7] :
                                ( m1_subset_1(X7,X0)
                               => ! [X8] :
                                    ( m1_subset_1(X8,X0)
                                   => ( k1_xboole_0 != X0
                                     => m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f533])).

fof(f533,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ! [X5] :
                      ( m1_subset_1(X5,X0)
                     => ! [X6] :
                          ( m1_subset_1(X6,X0)
                         => ! [X7] :
                              ( m1_subset_1(X7,X0)
                             => ! [X8] :
                                  ( m1_subset_1(X8,X0)
                                 => ( k1_xboole_0 != X0
                                   => m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_subset_1)).

fof(f1602,plain,(
    ~ spl40_9 ),
    inference(avatar_split_clause,[],[f680,f1599])).

fof(f680,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f542])).

fof(f1597,plain,(
    ~ spl40_8 ),
    inference(avatar_split_clause,[],[f1592,f1594])).

fof(f1592,plain,(
    ~ m1_subset_1(k2_xboole_0(k1_tarski(sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f1166,f1191])).

fof(f1191,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(definition_unfolding,[],[f721,f714])).

fof(f714,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f253])).

fof(f253,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

fof(f721,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f247])).

fof(f247,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

fof(f1166,plain,(
    ~ m1_subset_1(k2_xboole_0(k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)),k1_zfmisc_1(sK0)) ),
    inference(definition_unfolding,[],[f681,f714])).

fof(f681,plain,(
    ~ m1_subset_1(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f542])).

fof(f1591,plain,(
    spl40_7 ),
    inference(avatar_split_clause,[],[f682,f1588])).

fof(f682,plain,(
    m1_subset_1(sK7,sK0) ),
    inference(cnf_transformation,[],[f542])).

fof(f1586,plain,(
    spl40_6 ),
    inference(avatar_split_clause,[],[f683,f1583])).

fof(f683,plain,(
    m1_subset_1(sK6,sK0) ),
    inference(cnf_transformation,[],[f542])).

fof(f1581,plain,(
    spl40_5 ),
    inference(avatar_split_clause,[],[f684,f1578])).

fof(f684,plain,(
    m1_subset_1(sK5,sK0) ),
    inference(cnf_transformation,[],[f542])).

fof(f1576,plain,(
    spl40_4 ),
    inference(avatar_split_clause,[],[f685,f1573])).

fof(f685,plain,(
    m1_subset_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f542])).

fof(f1571,plain,(
    spl40_3 ),
    inference(avatar_split_clause,[],[f686,f1568])).

fof(f686,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f542])).

fof(f1566,plain,(
    spl40_2 ),
    inference(avatar_split_clause,[],[f687,f1563])).

fof(f687,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f542])).

fof(f1561,plain,(
    spl40_1 ),
    inference(avatar_split_clause,[],[f688,f1558])).

fof(f688,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f542])).
%------------------------------------------------------------------------------
