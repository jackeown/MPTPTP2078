%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 367 expanded)
%              Number of leaves         :   44 ( 178 expanded)
%              Depth                    :    7
%              Number of atoms          :  489 ( 905 expanded)
%              Number of equality atoms :  102 ( 241 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1818,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f46,f50,f54,f58,f62,f71,f87,f91,f95,f99,f107,f112,f129,f140,f148,f151,f191,f195,f215,f219,f347,f355,f494,f732,f736,f941,f955,f1420,f1526,f1563,f1571,f1574,f1729,f1773,f1792,f1803,f1817])).

fof(f1817,plain,
    ( ~ spl4_11
    | ~ spl4_14
    | spl4_19
    | ~ spl4_87 ),
    inference(avatar_contradiction_clause,[],[f1816])).

fof(f1816,plain,
    ( $false
    | ~ spl4_11
    | ~ spl4_14
    | spl4_19
    | ~ spl4_87 ),
    inference(subsumption_resolution,[],[f1793,f1812])).

fof(f1812,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | spl4_19
    | ~ spl4_87 ),
    inference(forward_demodulation,[],[f138,f1728])).

fof(f1728,plain,
    ( ! [X1] : k4_xboole_0(sK1,X1) = k4_xboole_0(sK1,k2_xboole_0(sK2,X1))
    | ~ spl4_87 ),
    inference(avatar_component_clause,[],[f1727])).

fof(f1727,plain,
    ( spl4_87
  <=> ! [X1] : k4_xboole_0(sK1,X1) = k4_xboole_0(sK1,k2_xboole_0(sK2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).

fof(f138,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl4_19
  <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f1793,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(resolution,[],[f85,f98])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_14
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f85,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_11
  <=> r1_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f1803,plain,
    ( ~ spl4_2
    | ~ spl4_7
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_34 ),
    inference(avatar_contradiction_clause,[],[f1802])).

fof(f1802,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f1801,f1796])).

fof(f1796,plain,
    ( ~ r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(resolution,[],[f66,f90])).

fof(f90,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP0(X0,X1,X2)
        | ~ r1_xboole_0(X1,k2_xboole_0(X2,X0)) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X0))
        | ~ sP0(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f66,plain,
    ( sP0(sK3,sK1,sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl4_7
  <=> sP0(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1801,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | ~ spl4_2
    | ~ spl4_13
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f1660,f45])).

fof(f45,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl4_2
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1660,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK1)
    | r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | ~ spl4_13
    | ~ spl4_34 ),
    inference(superposition,[],[f94,f346])).

fof(f346,plain,
    ( sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f344])).

fof(f344,plain,
    ( spl4_34
  <=> sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl4_13
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f1792,plain,
    ( spl4_11
    | ~ spl4_2
    | ~ spl4_13
    | ~ spl4_88 ),
    inference(avatar_split_clause,[],[f1787,f1770,f93,f44,f84])).

fof(f1770,plain,
    ( spl4_88
  <=> sK1 = k4_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f1787,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl4_2
    | ~ spl4_13
    | ~ spl4_88 ),
    inference(subsumption_resolution,[],[f1783,f45])).

fof(f1783,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK1)
    | r1_xboole_0(sK1,sK3)
    | ~ spl4_13
    | ~ spl4_88 ),
    inference(superposition,[],[f94,f1772])).

fof(f1772,plain,
    ( sK1 = k4_xboole_0(sK1,sK3)
    | ~ spl4_88 ),
    inference(avatar_component_clause,[],[f1770])).

fof(f1773,plain,
    ( spl4_88
    | ~ spl4_34
    | ~ spl4_87 ),
    inference(avatar_split_clause,[],[f1732,f1727,f344,f1770])).

fof(f1732,plain,
    ( sK1 = k4_xboole_0(sK1,sK3)
    | ~ spl4_34
    | ~ spl4_87 ),
    inference(superposition,[],[f1728,f346])).

fof(f1729,plain,
    ( spl4_87
    | ~ spl4_2
    | ~ spl4_26
    | ~ spl4_53
    | ~ spl4_82 ),
    inference(avatar_split_clause,[],[f1605,f1568,f730,f213,f44,f1727])).

fof(f213,plain,
    ( spl4_26
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f730,plain,
    ( spl4_53
  <=> ! [X3,X2,X4] : k4_xboole_0(X2,k2_xboole_0(X3,X4)) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f1568,plain,
    ( spl4_82
  <=> sK1 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f1605,plain,
    ( ! [X1] : k4_xboole_0(sK1,X1) = k4_xboole_0(sK1,k2_xboole_0(sK2,X1))
    | ~ spl4_2
    | ~ spl4_26
    | ~ spl4_53
    | ~ spl4_82 ),
    inference(forward_demodulation,[],[f1604,f214])).

fof(f214,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f213])).

fof(f1604,plain,
    ( ! [X1] : k4_xboole_0(sK1,k2_xboole_0(sK2,X1)) = k4_xboole_0(sK1,k2_xboole_0(k1_xboole_0,X1))
    | ~ spl4_2
    | ~ spl4_53
    | ~ spl4_82 ),
    inference(forward_demodulation,[],[f1599,f45])).

fof(f1599,plain,
    ( ! [X1] : k4_xboole_0(sK1,k2_xboole_0(sK2,X1)) = k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK1),X1))
    | ~ spl4_53
    | ~ spl4_82 ),
    inference(superposition,[],[f731,f1570])).

fof(f1570,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl4_82 ),
    inference(avatar_component_clause,[],[f1568])).

fof(f731,plain,
    ( ! [X4,X2,X3] : k4_xboole_0(X2,k2_xboole_0(X3,X4)) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X4))
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f730])).

fof(f1574,plain,
    ( ~ spl4_10
    | ~ spl4_14
    | spl4_81 ),
    inference(avatar_contradiction_clause,[],[f1573])).

fof(f1573,plain,
    ( $false
    | ~ spl4_10
    | ~ spl4_14
    | spl4_81 ),
    inference(subsumption_resolution,[],[f1524,f1564])).

fof(f1564,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(resolution,[],[f81,f98])).

fof(f81,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl4_10
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f1524,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | spl4_81 ),
    inference(avatar_component_clause,[],[f1523])).

fof(f1523,plain,
    ( spl4_81
  <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).

fof(f1571,plain,
    ( spl4_82
    | ~ spl4_1
    | ~ spl4_25
    | ~ spl4_81 ),
    inference(avatar_split_clause,[],[f1544,f1523,f193,f40,f1568])).

fof(f40,plain,
    ( spl4_1
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f193,plain,
    ( spl4_25
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f1544,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl4_1
    | ~ spl4_25
    | ~ spl4_81 ),
    inference(forward_demodulation,[],[f1532,f41])).

fof(f41,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f1532,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_25
    | ~ spl4_81 ),
    inference(superposition,[],[f194,f1525])).

fof(f1525,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl4_81 ),
    inference(avatar_component_clause,[],[f1523])).

fof(f194,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f193])).

fof(f1563,plain,
    ( spl4_10
    | ~ spl4_13
    | ~ spl4_81 ),
    inference(avatar_split_clause,[],[f1540,f1523,f93,f80])).

fof(f1540,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl4_13
    | ~ spl4_81 ),
    inference(trivial_inequality_removal,[],[f1533])).

fof(f1533,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,sK2)
    | ~ spl4_13
    | ~ spl4_81 ),
    inference(superposition,[],[f94,f1525])).

fof(f1526,plain,
    ( spl4_81
    | ~ spl4_65
    | ~ spl4_75 ),
    inference(avatar_split_clause,[],[f1488,f1418,f953,f1523])).

fof(f953,plain,
    ( spl4_65
  <=> ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(X0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f1418,plain,
    ( spl4_75
  <=> ! [X5,X4,X6] : k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X5,k2_xboole_0(k4_xboole_0(X4,X5),X6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f1488,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl4_65
    | ~ spl4_75 ),
    inference(superposition,[],[f1419,f954])).

fof(f954,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(X0,sK3)))
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f953])).

fof(f1419,plain,
    ( ! [X6,X4,X5] : k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X5,k2_xboole_0(k4_xboole_0(X4,X5),X6)))
    | ~ spl4_75 ),
    inference(avatar_component_clause,[],[f1418])).

fof(f1420,plain,
    ( spl4_75
    | ~ spl4_24
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f360,f353,f189,f1418])).

fof(f189,plain,
    ( spl4_24
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f353,plain,
    ( spl4_35
  <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f360,plain,
    ( ! [X6,X4,X5] : k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X5,k2_xboole_0(k4_xboole_0(X4,X5),X6)))
    | ~ spl4_24
    | ~ spl4_35 ),
    inference(superposition,[],[f354,f190])).

fof(f190,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f189])).

fof(f354,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f353])).

fof(f955,plain,
    ( spl4_65
    | ~ spl4_6
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f942,f939,f60,f953])).

fof(f60,plain,
    ( spl4_6
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f939,plain,
    ( spl4_64
  <=> ! [X65] : k4_xboole_0(sK1,X65) = k4_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK3,X65))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f942,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(X0,sK3)))
    | ~ spl4_6
    | ~ spl4_64 ),
    inference(superposition,[],[f940,f61])).

fof(f61,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f940,plain,
    ( ! [X65] : k4_xboole_0(sK1,X65) = k4_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK3,X65)))
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f939])).

fof(f941,plain,
    ( spl4_64
    | ~ spl4_42
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f900,f734,f492,f939])).

fof(f492,plain,
    ( spl4_42
  <=> ! [X9,X7,X8,X10] : k4_xboole_0(X7,k2_xboole_0(k2_xboole_0(X8,X9),X10)) = k4_xboole_0(X7,k2_xboole_0(X8,k2_xboole_0(X9,X10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f734,plain,
    ( spl4_54
  <=> ! [X0] : k4_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK2,sK3),X0)) = k4_xboole_0(sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f900,plain,
    ( ! [X65] : k4_xboole_0(sK1,X65) = k4_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK3,X65)))
    | ~ spl4_42
    | ~ spl4_54 ),
    inference(superposition,[],[f493,f735])).

fof(f735,plain,
    ( ! [X0] : k4_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK2,sK3),X0)) = k4_xboole_0(sK1,X0)
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f734])).

fof(f493,plain,
    ( ! [X10,X8,X7,X9] : k4_xboole_0(X7,k2_xboole_0(k2_xboole_0(X8,X9),X10)) = k4_xboole_0(X7,k2_xboole_0(X8,k2_xboole_0(X9,X10)))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f492])).

fof(f736,plain,
    ( spl4_54
    | ~ spl4_24
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f349,f344,f189,f734])).

fof(f349,plain,
    ( ! [X0] : k4_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK2,sK3),X0)) = k4_xboole_0(sK1,X0)
    | ~ spl4_24
    | ~ spl4_34 ),
    inference(superposition,[],[f190,f346])).

fof(f732,plain,
    ( spl4_53
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f323,f193,f189,f730])).

fof(f323,plain,
    ( ! [X4,X2,X3] : k4_xboole_0(X2,k2_xboole_0(X3,X4)) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X4))
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f294,f190])).

fof(f294,plain,
    ( ! [X4,X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X4))
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(superposition,[],[f190,f194])).

fof(f494,plain,
    ( spl4_42
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f209,f189,f492])).

fof(f209,plain,
    ( ! [X10,X8,X7,X9] : k4_xboole_0(X7,k2_xboole_0(k2_xboole_0(X8,X9),X10)) = k4_xboole_0(X7,k2_xboole_0(X8,k2_xboole_0(X9,X10)))
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f208,f190])).

fof(f208,plain,
    ( ! [X10,X8,X7,X9] : k4_xboole_0(k4_xboole_0(X7,X8),k2_xboole_0(X9,X10)) = k4_xboole_0(X7,k2_xboole_0(k2_xboole_0(X8,X9),X10))
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f200,f190])).

fof(f200,plain,
    ( ! [X10,X8,X7,X9] : k4_xboole_0(k4_xboole_0(X7,X8),k2_xboole_0(X9,X10)) = k4_xboole_0(k4_xboole_0(X7,k2_xboole_0(X8,X9)),X10)
    | ~ spl4_24 ),
    inference(superposition,[],[f190,f190])).

fof(f355,plain,
    ( spl4_35
    | ~ spl4_1
    | ~ spl4_18
    | ~ spl4_25
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f313,f217,f193,f127,f40,f353])).

fof(f127,plain,
    ( spl4_18
  <=> ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f217,plain,
    ( spl4_27
  <=> ! [X3,X2] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f313,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))
    | ~ spl4_1
    | ~ spl4_18
    | ~ spl4_25
    | ~ spl4_27 ),
    inference(backward_demodulation,[],[f218,f309])).

fof(f309,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)
    | ~ spl4_1
    | ~ spl4_18
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f288,f41])).

fof(f288,plain,
    ( ! [X2] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X2)
    | ~ spl4_18
    | ~ spl4_25 ),
    inference(superposition,[],[f194,f128])).

fof(f128,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f127])).

fof(f218,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f217])).

fof(f347,plain,
    ( spl4_34
    | ~ spl4_1
    | ~ spl4_19
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f317,f193,f137,f40,f344])).

fof(f317,plain,
    ( sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | ~ spl4_1
    | ~ spl4_19
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f290,f41])).

fof(f290,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_19
    | ~ spl4_25 ),
    inference(superposition,[],[f194,f139])).

fof(f139,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f137])).

fof(f219,plain,
    ( spl4_27
    | ~ spl4_2
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f197,f189,f44,f217])).

fof(f197,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)
    | ~ spl4_2
    | ~ spl4_24 ),
    inference(superposition,[],[f190,f45])).

fof(f215,plain,
    ( spl4_26
    | ~ spl4_1
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f196,f189,f40,f213])).

fof(f196,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))
    | ~ spl4_1
    | ~ spl4_24 ),
    inference(superposition,[],[f190,f41])).

fof(f195,plain,(
    spl4_25 ),
    inference(avatar_split_clause,[],[f35,f193])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f191,plain,(
    spl4_24 ),
    inference(avatar_split_clause,[],[f33,f189])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f151,plain,
    ( spl4_10
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f145,f64,f52,f80])).

fof(f52,plain,
    ( spl4_4
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X1,X2)
        | ~ sP0(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f145,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(resolution,[],[f66,f53])).

fof(f53,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP0(X0,X1,X2)
        | r1_xboole_0(X1,X2) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f148,plain,
    ( spl4_11
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f144,f64,f56,f84])).

fof(f56,plain,
    ( spl4_5
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X1,X0)
        | ~ sP0(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f144,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(resolution,[],[f66,f57])).

fof(f57,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP0(X0,X1,X2)
        | r1_xboole_0(X1,X0) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f140,plain,
    ( spl4_19
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f123,f97,f68,f137])).

fof(f68,plain,
    ( spl4_8
  <=> r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f123,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)))
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(resolution,[],[f98,f70])).

fof(f70,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f68])).

fof(f129,plain,
    ( spl4_18
    | ~ spl4_14
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f122,f110,f97,f127])).

fof(f110,plain,
    ( spl4_16
  <=> ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f122,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))
    | ~ spl4_14
    | ~ spl4_16 ),
    inference(resolution,[],[f98,f111])).

fof(f111,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f110])).

fof(f112,plain,
    ( spl4_16
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f108,f105,f48,f110])).

fof(f48,plain,
    ( spl4_3
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f105,plain,
    ( spl4_15
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f108,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(resolution,[],[f106,f49])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f106,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f105])).

fof(f107,plain,
    ( spl4_15
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f102,f93,f44,f40,f105])).

fof(f102,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f100,f45])).

fof(f100,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k4_xboole_0(X0,X0)
        | r1_xboole_0(X0,k1_xboole_0) )
    | ~ spl4_1
    | ~ spl4_13 ),
    inference(superposition,[],[f94,f41])).

fof(f99,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f37,f97])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f28])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f95,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f36,f93])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f32,f28])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f91,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f20,f89])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X0)
        & r1_xboole_0(X1,X2)
        & ~ r1_xboole_0(X1,k2_xboole_0(X2,X0)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) )
      | ~ sP0(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) )
      | ~ sP0(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f87,plain,
    ( spl4_7
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f23,f84,f80,f64])).

fof(f23,plain,
    ( ~ r1_xboole_0(sK1,sK3)
    | ~ r1_xboole_0(sK1,sK2)
    | sP0(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
      & ( ~ r1_xboole_0(sK1,sK3)
        | ~ r1_xboole_0(sK1,sK2) ) )
    | sP0(sK3,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | sP0(X2,X0,X1) )
   => ( ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
        & ( ~ r1_xboole_0(sK1,sK3)
          | ~ r1_xboole_0(sK1,sK2) ) )
      | sP0(sK3,sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | sP0(X2,X0,X1) ) ),
    inference(definition_folding,[],[f11,f13])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f71,plain,
    ( spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f24,f68,f64])).

fof(f24,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | sP0(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f27,f60])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f58,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f22,f56])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f54,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f21,f52])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f50,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f30,f48])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f46,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f38,f44])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f34,f26])).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f25,f28])).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f42,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f26,f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:20:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.43  % (10616)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (10606)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (10612)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (10604)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (10614)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (10602)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (10605)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.49  % (10608)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (10611)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (10615)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.50  % (10609)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.50  % (10610)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.50  % (10607)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.50  % (10613)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.50  % (10618)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.51  % (10603)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.51  % (10617)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.52  % (10619)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.56  % (10609)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f1818,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(avatar_sat_refutation,[],[f42,f46,f50,f54,f58,f62,f71,f87,f91,f95,f99,f107,f112,f129,f140,f148,f151,f191,f195,f215,f219,f347,f355,f494,f732,f736,f941,f955,f1420,f1526,f1563,f1571,f1574,f1729,f1773,f1792,f1803,f1817])).
% 0.20/0.57  fof(f1817,plain,(
% 0.20/0.57    ~spl4_11 | ~spl4_14 | spl4_19 | ~spl4_87),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f1816])).
% 0.20/0.57  fof(f1816,plain,(
% 0.20/0.57    $false | (~spl4_11 | ~spl4_14 | spl4_19 | ~spl4_87)),
% 0.20/0.57    inference(subsumption_resolution,[],[f1793,f1812])).
% 0.20/0.57  fof(f1812,plain,(
% 0.20/0.57    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | (spl4_19 | ~spl4_87)),
% 0.20/0.57    inference(forward_demodulation,[],[f138,f1728])).
% 0.20/0.57  fof(f1728,plain,(
% 0.20/0.57    ( ! [X1] : (k4_xboole_0(sK1,X1) = k4_xboole_0(sK1,k2_xboole_0(sK2,X1))) ) | ~spl4_87),
% 0.20/0.57    inference(avatar_component_clause,[],[f1727])).
% 0.20/0.57  fof(f1727,plain,(
% 0.20/0.57    spl4_87 <=> ! [X1] : k4_xboole_0(sK1,X1) = k4_xboole_0(sK1,k2_xboole_0(sK2,X1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).
% 0.20/0.57  fof(f138,plain,(
% 0.20/0.57    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) | spl4_19),
% 0.20/0.57    inference(avatar_component_clause,[],[f137])).
% 0.20/0.57  fof(f137,plain,(
% 0.20/0.57    spl4_19 <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.57  fof(f1793,plain,(
% 0.20/0.57    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | (~spl4_11 | ~spl4_14)),
% 0.20/0.57    inference(resolution,[],[f85,f98])).
% 0.20/0.57  fof(f98,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl4_14),
% 0.20/0.57    inference(avatar_component_clause,[],[f97])).
% 0.20/0.57  fof(f97,plain,(
% 0.20/0.57    spl4_14 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.57  fof(f85,plain,(
% 0.20/0.57    r1_xboole_0(sK1,sK3) | ~spl4_11),
% 0.20/0.57    inference(avatar_component_clause,[],[f84])).
% 0.20/0.57  fof(f84,plain,(
% 0.20/0.57    spl4_11 <=> r1_xboole_0(sK1,sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.57  fof(f1803,plain,(
% 0.20/0.57    ~spl4_2 | ~spl4_7 | ~spl4_12 | ~spl4_13 | ~spl4_34),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f1802])).
% 0.20/0.57  fof(f1802,plain,(
% 0.20/0.57    $false | (~spl4_2 | ~spl4_7 | ~spl4_12 | ~spl4_13 | ~spl4_34)),
% 0.20/0.57    inference(subsumption_resolution,[],[f1801,f1796])).
% 0.20/0.57  fof(f1796,plain,(
% 0.20/0.57    ~r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | (~spl4_7 | ~spl4_12)),
% 0.20/0.57    inference(resolution,[],[f66,f90])).
% 0.20/0.57  fof(f90,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~r1_xboole_0(X1,k2_xboole_0(X2,X0))) ) | ~spl4_12),
% 0.20/0.57    inference(avatar_component_clause,[],[f89])).
% 0.20/0.57  fof(f89,plain,(
% 0.20/0.57    spl4_12 <=> ! [X1,X0,X2] : (~r1_xboole_0(X1,k2_xboole_0(X2,X0)) | ~sP0(X0,X1,X2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.57  fof(f66,plain,(
% 0.20/0.57    sP0(sK3,sK1,sK2) | ~spl4_7),
% 0.20/0.57    inference(avatar_component_clause,[],[f64])).
% 0.20/0.57  fof(f64,plain,(
% 0.20/0.57    spl4_7 <=> sP0(sK3,sK1,sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.57  fof(f1801,plain,(
% 0.20/0.57    r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | (~spl4_2 | ~spl4_13 | ~spl4_34)),
% 0.20/0.57    inference(subsumption_resolution,[],[f1660,f45])).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl4_2),
% 0.20/0.57    inference(avatar_component_clause,[],[f44])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    spl4_2 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.57  fof(f1660,plain,(
% 0.20/0.57    k1_xboole_0 != k4_xboole_0(sK1,sK1) | r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | (~spl4_13 | ~spl4_34)),
% 0.20/0.57    inference(superposition,[],[f94,f346])).
% 0.20/0.57  fof(f346,plain,(
% 0.20/0.57    sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | ~spl4_34),
% 0.20/0.57    inference(avatar_component_clause,[],[f344])).
% 0.20/0.57  fof(f344,plain,(
% 0.20/0.57    spl4_34 <=> sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.20/0.57  fof(f94,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) ) | ~spl4_13),
% 0.20/0.57    inference(avatar_component_clause,[],[f93])).
% 0.20/0.57  fof(f93,plain,(
% 0.20/0.57    spl4_13 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.57  fof(f1792,plain,(
% 0.20/0.57    spl4_11 | ~spl4_2 | ~spl4_13 | ~spl4_88),
% 0.20/0.57    inference(avatar_split_clause,[],[f1787,f1770,f93,f44,f84])).
% 0.20/0.57  fof(f1770,plain,(
% 0.20/0.57    spl4_88 <=> sK1 = k4_xboole_0(sK1,sK3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).
% 0.20/0.57  fof(f1787,plain,(
% 0.20/0.57    r1_xboole_0(sK1,sK3) | (~spl4_2 | ~spl4_13 | ~spl4_88)),
% 0.20/0.57    inference(subsumption_resolution,[],[f1783,f45])).
% 0.20/0.57  fof(f1783,plain,(
% 0.20/0.57    k1_xboole_0 != k4_xboole_0(sK1,sK1) | r1_xboole_0(sK1,sK3) | (~spl4_13 | ~spl4_88)),
% 0.20/0.57    inference(superposition,[],[f94,f1772])).
% 0.20/0.57  fof(f1772,plain,(
% 0.20/0.57    sK1 = k4_xboole_0(sK1,sK3) | ~spl4_88),
% 0.20/0.57    inference(avatar_component_clause,[],[f1770])).
% 0.20/0.57  fof(f1773,plain,(
% 0.20/0.57    spl4_88 | ~spl4_34 | ~spl4_87),
% 0.20/0.57    inference(avatar_split_clause,[],[f1732,f1727,f344,f1770])).
% 0.20/0.57  fof(f1732,plain,(
% 0.20/0.57    sK1 = k4_xboole_0(sK1,sK3) | (~spl4_34 | ~spl4_87)),
% 0.20/0.57    inference(superposition,[],[f1728,f346])).
% 0.20/0.57  fof(f1729,plain,(
% 0.20/0.57    spl4_87 | ~spl4_2 | ~spl4_26 | ~spl4_53 | ~spl4_82),
% 0.20/0.57    inference(avatar_split_clause,[],[f1605,f1568,f730,f213,f44,f1727])).
% 0.20/0.57  fof(f213,plain,(
% 0.20/0.57    spl4_26 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.57  fof(f730,plain,(
% 0.20/0.57    spl4_53 <=> ! [X3,X2,X4] : k4_xboole_0(X2,k2_xboole_0(X3,X4)) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X4))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 0.20/0.57  fof(f1568,plain,(
% 0.20/0.57    spl4_82 <=> sK1 = k4_xboole_0(sK1,sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).
% 0.20/0.57  fof(f1605,plain,(
% 0.20/0.57    ( ! [X1] : (k4_xboole_0(sK1,X1) = k4_xboole_0(sK1,k2_xboole_0(sK2,X1))) ) | (~spl4_2 | ~spl4_26 | ~spl4_53 | ~spl4_82)),
% 0.20/0.57    inference(forward_demodulation,[],[f1604,f214])).
% 0.20/0.57  fof(f214,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))) ) | ~spl4_26),
% 0.20/0.57    inference(avatar_component_clause,[],[f213])).
% 0.20/0.57  fof(f1604,plain,(
% 0.20/0.57    ( ! [X1] : (k4_xboole_0(sK1,k2_xboole_0(sK2,X1)) = k4_xboole_0(sK1,k2_xboole_0(k1_xboole_0,X1))) ) | (~spl4_2 | ~spl4_53 | ~spl4_82)),
% 0.20/0.57    inference(forward_demodulation,[],[f1599,f45])).
% 0.20/0.57  fof(f1599,plain,(
% 0.20/0.57    ( ! [X1] : (k4_xboole_0(sK1,k2_xboole_0(sK2,X1)) = k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK1),X1))) ) | (~spl4_53 | ~spl4_82)),
% 0.20/0.57    inference(superposition,[],[f731,f1570])).
% 0.20/0.57  fof(f1570,plain,(
% 0.20/0.57    sK1 = k4_xboole_0(sK1,sK2) | ~spl4_82),
% 0.20/0.57    inference(avatar_component_clause,[],[f1568])).
% 0.20/0.57  fof(f731,plain,(
% 0.20/0.57    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X3,X4)) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X4))) ) | ~spl4_53),
% 0.20/0.57    inference(avatar_component_clause,[],[f730])).
% 0.20/0.57  fof(f1574,plain,(
% 0.20/0.57    ~spl4_10 | ~spl4_14 | spl4_81),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f1573])).
% 0.20/0.57  fof(f1573,plain,(
% 0.20/0.57    $false | (~spl4_10 | ~spl4_14 | spl4_81)),
% 0.20/0.57    inference(subsumption_resolution,[],[f1524,f1564])).
% 0.20/0.57  fof(f1564,plain,(
% 0.20/0.57    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | (~spl4_10 | ~spl4_14)),
% 0.20/0.57    inference(resolution,[],[f81,f98])).
% 0.20/0.57  fof(f81,plain,(
% 0.20/0.57    r1_xboole_0(sK1,sK2) | ~spl4_10),
% 0.20/0.57    inference(avatar_component_clause,[],[f80])).
% 0.20/0.57  fof(f80,plain,(
% 0.20/0.57    spl4_10 <=> r1_xboole_0(sK1,sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.57  fof(f1524,plain,(
% 0.20/0.57    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | spl4_81),
% 0.20/0.57    inference(avatar_component_clause,[],[f1523])).
% 0.20/0.57  fof(f1523,plain,(
% 0.20/0.57    spl4_81 <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).
% 0.20/0.57  fof(f1571,plain,(
% 0.20/0.57    spl4_82 | ~spl4_1 | ~spl4_25 | ~spl4_81),
% 0.20/0.57    inference(avatar_split_clause,[],[f1544,f1523,f193,f40,f1568])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    spl4_1 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.57  fof(f193,plain,(
% 0.20/0.57    spl4_25 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.57  fof(f1544,plain,(
% 0.20/0.57    sK1 = k4_xboole_0(sK1,sK2) | (~spl4_1 | ~spl4_25 | ~spl4_81)),
% 0.20/0.57    inference(forward_demodulation,[],[f1532,f41])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl4_1),
% 0.20/0.57    inference(avatar_component_clause,[],[f40])).
% 0.20/0.57  fof(f1532,plain,(
% 0.20/0.57    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0) | (~spl4_25 | ~spl4_81)),
% 0.20/0.57    inference(superposition,[],[f194,f1525])).
% 0.20/0.57  fof(f1525,plain,(
% 0.20/0.57    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | ~spl4_81),
% 0.20/0.57    inference(avatar_component_clause,[],[f1523])).
% 0.20/0.57  fof(f194,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl4_25),
% 0.20/0.57    inference(avatar_component_clause,[],[f193])).
% 0.20/0.57  fof(f1563,plain,(
% 0.20/0.57    spl4_10 | ~spl4_13 | ~spl4_81),
% 0.20/0.57    inference(avatar_split_clause,[],[f1540,f1523,f93,f80])).
% 0.20/0.57  fof(f1540,plain,(
% 0.20/0.57    r1_xboole_0(sK1,sK2) | (~spl4_13 | ~spl4_81)),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f1533])).
% 0.20/0.57  fof(f1533,plain,(
% 0.20/0.57    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,sK2) | (~spl4_13 | ~spl4_81)),
% 0.20/0.57    inference(superposition,[],[f94,f1525])).
% 0.20/0.57  fof(f1526,plain,(
% 0.20/0.57    spl4_81 | ~spl4_65 | ~spl4_75),
% 0.20/0.57    inference(avatar_split_clause,[],[f1488,f1418,f953,f1523])).
% 0.20/0.57  fof(f953,plain,(
% 0.20/0.57    spl4_65 <=> ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(X0,sK3)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 0.20/0.57  fof(f1418,plain,(
% 0.20/0.57    spl4_75 <=> ! [X5,X4,X6] : k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X5,k2_xboole_0(k4_xboole_0(X4,X5),X6)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).
% 0.20/0.57  fof(f1488,plain,(
% 0.20/0.57    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | (~spl4_65 | ~spl4_75)),
% 0.20/0.57    inference(superposition,[],[f1419,f954])).
% 0.20/0.57  fof(f954,plain,(
% 0.20/0.57    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(X0,sK3)))) ) | ~spl4_65),
% 0.20/0.57    inference(avatar_component_clause,[],[f953])).
% 0.20/0.57  fof(f1419,plain,(
% 0.20/0.57    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X5,k2_xboole_0(k4_xboole_0(X4,X5),X6)))) ) | ~spl4_75),
% 0.20/0.57    inference(avatar_component_clause,[],[f1418])).
% 0.20/0.57  fof(f1420,plain,(
% 0.20/0.57    spl4_75 | ~spl4_24 | ~spl4_35),
% 0.20/0.57    inference(avatar_split_clause,[],[f360,f353,f189,f1418])).
% 0.20/0.57  fof(f189,plain,(
% 0.20/0.57    spl4_24 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.57  fof(f353,plain,(
% 0.20/0.57    spl4_35 <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.20/0.57  fof(f360,plain,(
% 0.20/0.57    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X5,k2_xboole_0(k4_xboole_0(X4,X5),X6)))) ) | (~spl4_24 | ~spl4_35)),
% 0.20/0.57    inference(superposition,[],[f354,f190])).
% 0.20/0.57  fof(f190,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl4_24),
% 0.20/0.57    inference(avatar_component_clause,[],[f189])).
% 0.20/0.57  fof(f354,plain,(
% 0.20/0.57    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) ) | ~spl4_35),
% 0.20/0.57    inference(avatar_component_clause,[],[f353])).
% 0.20/0.57  fof(f955,plain,(
% 0.20/0.57    spl4_65 | ~spl4_6 | ~spl4_64),
% 0.20/0.57    inference(avatar_split_clause,[],[f942,f939,f60,f953])).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    spl4_6 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.57  fof(f939,plain,(
% 0.20/0.57    spl4_64 <=> ! [X65] : k4_xboole_0(sK1,X65) = k4_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK3,X65)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 0.20/0.57  fof(f942,plain,(
% 0.20/0.57    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(X0,sK3)))) ) | (~spl4_6 | ~spl4_64)),
% 0.20/0.57    inference(superposition,[],[f940,f61])).
% 0.20/0.57  fof(f61,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl4_6),
% 0.20/0.57    inference(avatar_component_clause,[],[f60])).
% 0.20/0.57  fof(f940,plain,(
% 0.20/0.57    ( ! [X65] : (k4_xboole_0(sK1,X65) = k4_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK3,X65)))) ) | ~spl4_64),
% 0.20/0.57    inference(avatar_component_clause,[],[f939])).
% 0.20/0.57  fof(f941,plain,(
% 0.20/0.57    spl4_64 | ~spl4_42 | ~spl4_54),
% 0.20/0.57    inference(avatar_split_clause,[],[f900,f734,f492,f939])).
% 0.20/0.57  fof(f492,plain,(
% 0.20/0.57    spl4_42 <=> ! [X9,X7,X8,X10] : k4_xboole_0(X7,k2_xboole_0(k2_xboole_0(X8,X9),X10)) = k4_xboole_0(X7,k2_xboole_0(X8,k2_xboole_0(X9,X10)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.20/0.57  fof(f734,plain,(
% 0.20/0.57    spl4_54 <=> ! [X0] : k4_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK2,sK3),X0)) = k4_xboole_0(sK1,X0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 0.20/0.57  fof(f900,plain,(
% 0.20/0.57    ( ! [X65] : (k4_xboole_0(sK1,X65) = k4_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK3,X65)))) ) | (~spl4_42 | ~spl4_54)),
% 0.20/0.57    inference(superposition,[],[f493,f735])).
% 0.20/0.57  fof(f735,plain,(
% 0.20/0.57    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK2,sK3),X0)) = k4_xboole_0(sK1,X0)) ) | ~spl4_54),
% 0.20/0.57    inference(avatar_component_clause,[],[f734])).
% 0.20/0.57  fof(f493,plain,(
% 0.20/0.57    ( ! [X10,X8,X7,X9] : (k4_xboole_0(X7,k2_xboole_0(k2_xboole_0(X8,X9),X10)) = k4_xboole_0(X7,k2_xboole_0(X8,k2_xboole_0(X9,X10)))) ) | ~spl4_42),
% 0.20/0.57    inference(avatar_component_clause,[],[f492])).
% 0.20/0.57  fof(f736,plain,(
% 0.20/0.57    spl4_54 | ~spl4_24 | ~spl4_34),
% 0.20/0.57    inference(avatar_split_clause,[],[f349,f344,f189,f734])).
% 0.20/0.57  fof(f349,plain,(
% 0.20/0.57    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK2,sK3),X0)) = k4_xboole_0(sK1,X0)) ) | (~spl4_24 | ~spl4_34)),
% 0.20/0.57    inference(superposition,[],[f190,f346])).
% 0.20/0.57  fof(f732,plain,(
% 0.20/0.57    spl4_53 | ~spl4_24 | ~spl4_25),
% 0.20/0.57    inference(avatar_split_clause,[],[f323,f193,f189,f730])).
% 0.20/0.57  fof(f323,plain,(
% 0.20/0.57    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X3,X4)) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X4))) ) | (~spl4_24 | ~spl4_25)),
% 0.20/0.57    inference(forward_demodulation,[],[f294,f190])).
% 0.20/0.57  fof(f294,plain,(
% 0.20/0.57    ( ! [X4,X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X4))) ) | (~spl4_24 | ~spl4_25)),
% 0.20/0.57    inference(superposition,[],[f190,f194])).
% 0.20/0.57  fof(f494,plain,(
% 0.20/0.57    spl4_42 | ~spl4_24),
% 0.20/0.57    inference(avatar_split_clause,[],[f209,f189,f492])).
% 0.20/0.57  fof(f209,plain,(
% 0.20/0.57    ( ! [X10,X8,X7,X9] : (k4_xboole_0(X7,k2_xboole_0(k2_xboole_0(X8,X9),X10)) = k4_xboole_0(X7,k2_xboole_0(X8,k2_xboole_0(X9,X10)))) ) | ~spl4_24),
% 0.20/0.57    inference(forward_demodulation,[],[f208,f190])).
% 0.20/0.57  fof(f208,plain,(
% 0.20/0.57    ( ! [X10,X8,X7,X9] : (k4_xboole_0(k4_xboole_0(X7,X8),k2_xboole_0(X9,X10)) = k4_xboole_0(X7,k2_xboole_0(k2_xboole_0(X8,X9),X10))) ) | ~spl4_24),
% 0.20/0.57    inference(forward_demodulation,[],[f200,f190])).
% 0.20/0.57  fof(f200,plain,(
% 0.20/0.57    ( ! [X10,X8,X7,X9] : (k4_xboole_0(k4_xboole_0(X7,X8),k2_xboole_0(X9,X10)) = k4_xboole_0(k4_xboole_0(X7,k2_xboole_0(X8,X9)),X10)) ) | ~spl4_24),
% 0.20/0.57    inference(superposition,[],[f190,f190])).
% 0.20/0.57  fof(f355,plain,(
% 0.20/0.57    spl4_35 | ~spl4_1 | ~spl4_18 | ~spl4_25 | ~spl4_27),
% 0.20/0.57    inference(avatar_split_clause,[],[f313,f217,f193,f127,f40,f353])).
% 0.20/0.57  fof(f127,plain,(
% 0.20/0.57    spl4_18 <=> ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.57  fof(f217,plain,(
% 0.20/0.57    spl4_27 <=> ! [X3,X2] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.20/0.57  fof(f313,plain,(
% 0.20/0.57    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) ) | (~spl4_1 | ~spl4_18 | ~spl4_25 | ~spl4_27)),
% 0.20/0.57    inference(backward_demodulation,[],[f218,f309])).
% 0.20/0.57  fof(f309,plain,(
% 0.20/0.57    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) ) | (~spl4_1 | ~spl4_18 | ~spl4_25)),
% 0.20/0.57    inference(forward_demodulation,[],[f288,f41])).
% 0.20/0.57  fof(f288,plain,(
% 0.20/0.57    ( ! [X2] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X2)) ) | (~spl4_18 | ~spl4_25)),
% 0.20/0.57    inference(superposition,[],[f194,f128])).
% 0.20/0.57  fof(f128,plain,(
% 0.20/0.57    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) ) | ~spl4_18),
% 0.20/0.57    inference(avatar_component_clause,[],[f127])).
% 0.20/0.57  fof(f218,plain,(
% 0.20/0.57    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) ) | ~spl4_27),
% 0.20/0.57    inference(avatar_component_clause,[],[f217])).
% 0.20/0.57  fof(f347,plain,(
% 0.20/0.57    spl4_34 | ~spl4_1 | ~spl4_19 | ~spl4_25),
% 0.20/0.57    inference(avatar_split_clause,[],[f317,f193,f137,f40,f344])).
% 0.20/0.57  fof(f317,plain,(
% 0.20/0.57    sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | (~spl4_1 | ~spl4_19 | ~spl4_25)),
% 0.20/0.57    inference(forward_demodulation,[],[f290,f41])).
% 0.20/0.57  fof(f290,plain,(
% 0.20/0.57    k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK1,k1_xboole_0) | (~spl4_19 | ~spl4_25)),
% 0.20/0.57    inference(superposition,[],[f194,f139])).
% 0.20/0.57  fof(f139,plain,(
% 0.20/0.57    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) | ~spl4_19),
% 0.20/0.57    inference(avatar_component_clause,[],[f137])).
% 0.20/0.57  fof(f219,plain,(
% 0.20/0.57    spl4_27 | ~spl4_2 | ~spl4_24),
% 0.20/0.57    inference(avatar_split_clause,[],[f197,f189,f44,f217])).
% 0.20/0.57  fof(f197,plain,(
% 0.20/0.57    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) ) | (~spl4_2 | ~spl4_24)),
% 0.20/0.57    inference(superposition,[],[f190,f45])).
% 0.20/0.57  fof(f215,plain,(
% 0.20/0.57    spl4_26 | ~spl4_1 | ~spl4_24),
% 0.20/0.57    inference(avatar_split_clause,[],[f196,f189,f40,f213])).
% 0.20/0.57  fof(f196,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))) ) | (~spl4_1 | ~spl4_24)),
% 0.20/0.57    inference(superposition,[],[f190,f41])).
% 0.20/0.57  fof(f195,plain,(
% 0.20/0.57    spl4_25),
% 0.20/0.57    inference(avatar_split_clause,[],[f35,f193])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f29,f28])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.57  fof(f191,plain,(
% 0.20/0.57    spl4_24),
% 0.20/0.57    inference(avatar_split_clause,[],[f33,f189])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.57  fof(f151,plain,(
% 0.20/0.57    spl4_10 | ~spl4_4 | ~spl4_7),
% 0.20/0.57    inference(avatar_split_clause,[],[f145,f64,f52,f80])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    spl4_4 <=> ! [X1,X0,X2] : (r1_xboole_0(X1,X2) | ~sP0(X0,X1,X2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.57  fof(f145,plain,(
% 0.20/0.57    r1_xboole_0(sK1,sK2) | (~spl4_4 | ~spl4_7)),
% 0.20/0.57    inference(resolution,[],[f66,f53])).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r1_xboole_0(X1,X2)) ) | ~spl4_4),
% 0.20/0.57    inference(avatar_component_clause,[],[f52])).
% 0.20/0.57  fof(f148,plain,(
% 0.20/0.57    spl4_11 | ~spl4_5 | ~spl4_7),
% 0.20/0.57    inference(avatar_split_clause,[],[f144,f64,f56,f84])).
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    spl4_5 <=> ! [X1,X0,X2] : (r1_xboole_0(X1,X0) | ~sP0(X0,X1,X2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.57  fof(f144,plain,(
% 0.20/0.57    r1_xboole_0(sK1,sK3) | (~spl4_5 | ~spl4_7)),
% 0.20/0.57    inference(resolution,[],[f66,f57])).
% 0.20/0.57  fof(f57,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r1_xboole_0(X1,X0)) ) | ~spl4_5),
% 0.20/0.57    inference(avatar_component_clause,[],[f56])).
% 0.20/0.57  fof(f140,plain,(
% 0.20/0.57    spl4_19 | ~spl4_8 | ~spl4_14),
% 0.20/0.57    inference(avatar_split_clause,[],[f123,f97,f68,f137])).
% 0.20/0.57  fof(f68,plain,(
% 0.20/0.57    spl4_8 <=> r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.57  fof(f123,plain,(
% 0.20/0.57    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) | (~spl4_8 | ~spl4_14)),
% 0.20/0.57    inference(resolution,[],[f98,f70])).
% 0.20/0.57  fof(f70,plain,(
% 0.20/0.57    r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | ~spl4_8),
% 0.20/0.57    inference(avatar_component_clause,[],[f68])).
% 0.20/0.57  fof(f129,plain,(
% 0.20/0.57    spl4_18 | ~spl4_14 | ~spl4_16),
% 0.20/0.57    inference(avatar_split_clause,[],[f122,f110,f97,f127])).
% 0.20/0.57  fof(f110,plain,(
% 0.20/0.57    spl4_16 <=> ! [X0] : r1_xboole_0(k1_xboole_0,X0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.57  fof(f122,plain,(
% 0.20/0.57    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) ) | (~spl4_14 | ~spl4_16)),
% 0.20/0.57    inference(resolution,[],[f98,f111])).
% 0.20/0.57  fof(f111,plain,(
% 0.20/0.57    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | ~spl4_16),
% 0.20/0.57    inference(avatar_component_clause,[],[f110])).
% 0.20/0.57  fof(f112,plain,(
% 0.20/0.57    spl4_16 | ~spl4_3 | ~spl4_15),
% 0.20/0.57    inference(avatar_split_clause,[],[f108,f105,f48,f110])).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    spl4_3 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.57  fof(f105,plain,(
% 0.20/0.57    spl4_15 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.57  fof(f108,plain,(
% 0.20/0.57    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | (~spl4_3 | ~spl4_15)),
% 0.20/0.57    inference(resolution,[],[f106,f49])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl4_3),
% 0.20/0.57    inference(avatar_component_clause,[],[f48])).
% 0.20/0.57  fof(f106,plain,(
% 0.20/0.57    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl4_15),
% 0.20/0.57    inference(avatar_component_clause,[],[f105])).
% 0.20/0.57  fof(f107,plain,(
% 0.20/0.57    spl4_15 | ~spl4_1 | ~spl4_2 | ~spl4_13),
% 0.20/0.57    inference(avatar_split_clause,[],[f102,f93,f44,f40,f105])).
% 0.20/0.57  fof(f102,plain,(
% 0.20/0.57    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | (~spl4_1 | ~spl4_2 | ~spl4_13)),
% 0.20/0.57    inference(subsumption_resolution,[],[f100,f45])).
% 0.20/0.57  fof(f100,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(X0,X0) | r1_xboole_0(X0,k1_xboole_0)) ) | (~spl4_1 | ~spl4_13)),
% 0.20/0.57    inference(superposition,[],[f94,f41])).
% 0.20/0.57  fof(f99,plain,(
% 0.20/0.57    spl4_14),
% 0.20/0.57    inference(avatar_split_clause,[],[f37,f97])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f31,f28])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(nnf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.57  fof(f95,plain,(
% 0.20/0.57    spl4_13),
% 0.20/0.57    inference(avatar_split_clause,[],[f36,f93])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f32,f28])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f91,plain,(
% 0.20/0.57    spl4_12),
% 0.20/0.57    inference(avatar_split_clause,[],[f20,f89])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,k2_xboole_0(X2,X0)) | ~sP0(X0,X1,X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((r1_xboole_0(X1,X0) & r1_xboole_0(X1,X2) & ~r1_xboole_0(X1,k2_xboole_0(X2,X0))) | ~sP0(X0,X1,X2))),
% 0.20/0.57    inference(rectify,[],[f15])).
% 0.20/0.57  fof(f15,plain,(
% 0.20/0.57    ! [X2,X0,X1] : ((r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))) | ~sP0(X2,X0,X1))),
% 0.20/0.57    inference(nnf_transformation,[],[f13])).
% 0.20/0.57  fof(f13,plain,(
% 0.20/0.57    ! [X2,X0,X1] : ((r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))) | ~sP0(X2,X0,X1))),
% 0.20/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.57  fof(f87,plain,(
% 0.20/0.57    spl4_7 | ~spl4_10 | ~spl4_11),
% 0.20/0.57    inference(avatar_split_clause,[],[f23,f84,f80,f64])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ~r1_xboole_0(sK1,sK3) | ~r1_xboole_0(sK1,sK2) | sP0(sK3,sK1,sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f18])).
% 0.20/0.57  fof(f18,plain,(
% 0.20/0.57    (r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) & (~r1_xboole_0(sK1,sK3) | ~r1_xboole_0(sK1,sK2))) | sP0(sK3,sK1,sK2)),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f17])).
% 0.20/0.57  fof(f17,plain,(
% 0.20/0.57    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | sP0(X2,X0,X1)) => ((r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) & (~r1_xboole_0(sK1,sK3) | ~r1_xboole_0(sK1,sK2))) | sP0(sK3,sK1,sK2))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f14,plain,(
% 0.20/0.57    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | sP0(X2,X0,X1))),
% 0.20/0.57    inference(definition_folding,[],[f11,f13])).
% 0.20/0.57  fof(f11,plain,(
% 0.20/0.57    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.57    inference(ennf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.57    inference(negated_conjecture,[],[f9])).
% 0.20/0.57  fof(f9,conjecture,(
% 0.20/0.57    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.20/0.57  fof(f71,plain,(
% 0.20/0.57    spl4_7 | spl4_8),
% 0.20/0.57    inference(avatar_split_clause,[],[f24,f68,f64])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | sP0(sK3,sK1,sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f18])).
% 0.20/0.57  fof(f62,plain,(
% 0.20/0.57    spl4_6),
% 0.20/0.57    inference(avatar_split_clause,[],[f27,f60])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.57  fof(f58,plain,(
% 0.20/0.57    spl4_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f22,f56])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (r1_xboole_0(X1,X0) | ~sP0(X0,X1,X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f16])).
% 0.20/0.57  fof(f54,plain,(
% 0.20/0.57    spl4_4),
% 0.20/0.57    inference(avatar_split_clause,[],[f21,f52])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (r1_xboole_0(X1,X2) | ~sP0(X0,X1,X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f16])).
% 0.20/0.57  fof(f50,plain,(
% 0.20/0.57    spl4_3),
% 0.20/0.57    inference(avatar_split_clause,[],[f30,f48])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f12])).
% 0.20/0.57  fof(f12,plain,(
% 0.20/0.57    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    spl4_2),
% 0.20/0.57    inference(avatar_split_clause,[],[f38,f44])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.57    inference(backward_demodulation,[],[f34,f26])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f25,f28])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    spl4_1),
% 0.20/0.57    inference(avatar_split_clause,[],[f26,f40])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (10609)------------------------------
% 0.20/0.57  % (10609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (10609)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (10609)Memory used [KB]: 7803
% 0.20/0.57  % (10609)Time elapsed: 0.146 s
% 0.20/0.57  % (10609)------------------------------
% 0.20/0.57  % (10609)------------------------------
% 0.20/0.58  % (10601)Success in time 0.215 s
%------------------------------------------------------------------------------
