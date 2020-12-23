%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0897+2 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 198 expanded)
%              Number of leaves         :   24 (  85 expanded)
%              Depth                    :    8
%              Number of atoms          :  374 ( 745 expanded)
%              Number of equality atoms :  232 ( 541 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1694,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1411,f1415,f1419,f1483,f1491,f1495,f1499,f1504,f1526,f1536,f1542,f1556,f1576,f1586,f1592,f1614,f1640,f1650,f1693])).

fof(f1693,plain,
    ( spl9_4
    | ~ spl9_20 ),
    inference(avatar_contradiction_clause,[],[f1692])).

fof(f1692,plain,
    ( $false
    | spl9_4
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f1691,f1410])).

fof(f1410,plain,
    ( sK3 != sK7
    | spl9_4 ),
    inference(avatar_component_clause,[],[f1409])).

fof(f1409,plain,
    ( spl9_4
  <=> sK3 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f1691,plain,
    ( sK3 = sK7
    | ~ spl9_20 ),
    inference(equality_resolution,[],[f1639])).

fof(f1639,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | sK7 = X31 )
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f1638])).

fof(f1638,plain,
    ( spl9_20
  <=> ! [X29,X31,X28,X30] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | sK7 = X31 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f1650,plain,
    ( spl9_3
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f1646,f1574,f1406])).

fof(f1406,plain,
    ( spl9_3
  <=> sK2 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f1574,plain,
    ( spl9_16
  <=> ! [X29,X31,X28,X30] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | sK6 = X30 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f1646,plain,
    ( sK2 = sK6
    | ~ spl9_16 ),
    inference(equality_resolution,[],[f1575])).

fof(f1575,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | sK6 = X30 )
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f1574])).

fof(f1640,plain,
    ( spl9_18
    | spl9_9
    | spl9_10
    | spl9_20
    | spl9_12
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f1636,f1590,f1485,f1638,f1473,f1470,f1603])).

fof(f1603,plain,
    ( spl9_18
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f1470,plain,
    ( spl9_9
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f1473,plain,
    ( spl9_10
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f1485,plain,
    ( spl9_12
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

% (28084)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f1590,plain,
    ( spl9_17
  <=> k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK0,sK1,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f1636,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | k1_xboole_0 = sK7
        | k1_xboole_0 = sK6
        | k1_xboole_0 = sK1
        | sK7 = X31 )
    | spl9_12
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1625,f1486])).

fof(f1486,plain,
    ( k1_xboole_0 != sK0
    | spl9_12 ),
    inference(avatar_component_clause,[],[f1485])).

fof(f1625,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | k1_xboole_0 = sK7
        | k1_xboole_0 = sK6
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0
        | sK7 = X31 )
    | ~ spl9_17 ),
    inference(superposition,[],[f1386,f1591])).

fof(f1591,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK0,sK1,sK6,sK7)
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f1590])).

fof(f1386,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X3 = X7 ) ),
    inference(cnf_transformation,[],[f1369])).

fof(f1369,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f1368])).

fof(f1368,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f1353])).

fof(f1353,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_mcart_1)).

fof(f1614,plain,
    ( k1_xboole_0 != sK1
    | sK1 != sK5
    | k1_xboole_0 = sK5 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1592,plain,
    ( spl9_17
    | ~ spl9_2
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f1588,f1540,f1403,f1590])).

fof(f1403,plain,
    ( spl9_2
  <=> sK1 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f1540,plain,
    ( spl9_14
  <=> k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK0,sK5,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f1588,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK0,sK1,sK6,sK7)
    | ~ spl9_2
    | ~ spl9_14 ),
    inference(backward_demodulation,[],[f1541,f1585])).

fof(f1585,plain,
    ( sK1 = sK5
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f1403])).

fof(f1541,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK0,sK5,sK6,sK7)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f1540])).

fof(f1586,plain,
    ( spl9_2
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f1582,f1524,f1403])).

fof(f1524,plain,
    ( spl9_13
  <=> ! [X29,X31,X28,X30] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | sK5 = X29 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f1582,plain,
    ( sK1 = sK5
    | ~ spl9_13 ),
    inference(equality_resolution,[],[f1525])).

fof(f1525,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | sK5 = X29 )
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f1524])).

fof(f1576,plain,
    ( spl9_8
    | spl9_9
    | spl9_10
    | spl9_16
    | spl9_12
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f1572,f1540,f1485,f1574,f1473,f1470,f1467])).

fof(f1467,plain,
    ( spl9_8
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f1572,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | k1_xboole_0 = sK7
        | k1_xboole_0 = sK6
        | k1_xboole_0 = sK5
        | sK6 = X30 )
    | spl9_12
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f1561,f1486])).

fof(f1561,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | k1_xboole_0 = sK7
        | k1_xboole_0 = sK6
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK0
        | sK6 = X30 )
    | ~ spl9_14 ),
    inference(superposition,[],[f1385,f1541])).

fof(f1385,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X2 = X6 ) ),
    inference(cnf_transformation,[],[f1369])).

fof(f1556,plain,
    ( k1_xboole_0 != sK0
    | sK0 != sK4
    | k1_xboole_0 = sK4 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1542,plain,
    ( spl9_14
    | ~ spl9_1
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f1538,f1417,f1400,f1540])).

fof(f1400,plain,
    ( spl9_1
  <=> sK0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f1417,plain,
    ( spl9_6
  <=> k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f1538,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK0,sK5,sK6,sK7)
    | ~ spl9_1
    | ~ spl9_6 ),
    inference(backward_demodulation,[],[f1418,f1535])).

fof(f1535,plain,
    ( sK0 = sK4
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f1400])).

fof(f1418,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f1417])).

fof(f1536,plain,
    ( spl9_1
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f1532,f1476,f1400])).

fof(f1476,plain,
    ( spl9_11
  <=> ! [X1,X3,X0,X2] :
        ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK1,sK2,sK3)
        | sK4 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f1532,plain,
    ( sK0 = sK4
    | ~ spl9_11 ),
    inference(equality_resolution,[],[f1477])).

fof(f1477,plain,
    ( ! [X2,X0,X3,X1] :
        ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK1,sK2,sK3)
        | sK4 = X0 )
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f1476])).

fof(f1526,plain,
    ( spl9_7
    | spl9_8
    | spl9_9
    | spl9_10
    | spl9_13
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f1512,f1417,f1524,f1473,f1470,f1467,f1464])).

fof(f1464,plain,
    ( spl9_7
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f1512,plain,
    ( ! [X30,X28,X31,X29] :
        ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X28,X29,X30,X31)
        | k1_xboole_0 = sK7
        | k1_xboole_0 = sK6
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK4
        | sK5 = X29 )
    | ~ spl9_6 ),
    inference(superposition,[],[f1384,f1418])).

% (28103)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:lma=on:lwlo=on:nm=4:nwc=10:stl=30:sd=3:ss=axioms:sos=all:sac=on_49 on theBenchmark
fof(f1384,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X1 = X5 ) ),
    inference(cnf_transformation,[],[f1369])).

fof(f1504,plain,
    ( spl9_7
    | spl9_8
    | spl9_9
    | spl9_10
    | spl9_11
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f1501,f1417,f1476,f1473,f1470,f1467,f1464])).

fof(f1501,plain,
    ( ! [X6,X4,X7,X5] :
        ( k4_zfmisc_1(X4,X5,X6,X7) != k4_zfmisc_1(sK0,sK1,sK2,sK3)
        | k1_xboole_0 = sK7
        | k1_xboole_0 = sK6
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK4
        | sK4 = X4 )
    | ~ spl9_6 ),
    inference(superposition,[],[f1383,f1418])).

fof(f1383,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f1369])).

fof(f1499,plain,
    ( spl9_5
    | ~ spl9_6
    | ~ spl9_10 ),
    inference(avatar_contradiction_clause,[],[f1498])).

fof(f1498,plain,
    ( $false
    | spl9_5
    | ~ spl9_6
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f1497,f1414])).

fof(f1414,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | spl9_5 ),
    inference(avatar_component_clause,[],[f1413])).

fof(f1413,plain,
    ( spl9_5
  <=> k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f1497,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | ~ spl9_6
    | ~ spl9_10 ),
    inference(forward_demodulation,[],[f1496,f1395])).

fof(f1395,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,k1_xboole_0) ),
    inference(equality_resolution,[],[f1391])).

fof(f1391,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f1375])).

fof(f1375,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f1374])).

fof(f1374,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f1352])).

fof(f1352,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f1496,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,k1_xboole_0)
    | ~ spl9_6
    | ~ spl9_10 ),
    inference(forward_demodulation,[],[f1418,f1474])).

fof(f1474,plain,
    ( k1_xboole_0 = sK7
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f1473])).

fof(f1495,plain,
    ( spl9_5
    | ~ spl9_6
    | ~ spl9_9 ),
    inference(avatar_contradiction_clause,[],[f1494])).

fof(f1494,plain,
    ( $false
    | spl9_5
    | ~ spl9_6
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f1493,f1414])).

fof(f1493,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | ~ spl9_6
    | ~ spl9_9 ),
    inference(forward_demodulation,[],[f1492,f1396])).

fof(f1396,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k4_zfmisc_1(X0,X1,k1_xboole_0,X3) ),
    inference(equality_resolution,[],[f1390])).

fof(f1390,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f1375])).

fof(f1492,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,k1_xboole_0,sK7)
    | ~ spl9_6
    | ~ spl9_9 ),
    inference(forward_demodulation,[],[f1418,f1471])).

fof(f1471,plain,
    ( k1_xboole_0 = sK6
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f1470])).

fof(f1491,plain,
    ( spl9_5
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f1490])).

fof(f1490,plain,
    ( $false
    | spl9_5
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f1489,f1414])).

fof(f1489,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(forward_demodulation,[],[f1488,f1397])).

fof(f1397,plain,(
    ! [X2,X0,X3] : k1_xboole_0 = k4_zfmisc_1(X0,k1_xboole_0,X2,X3) ),
    inference(equality_resolution,[],[f1389])).

fof(f1389,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f1375])).

fof(f1488,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,k1_xboole_0,sK6,sK7)
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(forward_demodulation,[],[f1418,f1468])).

fof(f1468,plain,
    ( k1_xboole_0 = sK5
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f1467])).

fof(f1483,plain,
    ( spl9_5
    | ~ spl9_6
    | ~ spl9_7 ),
    inference(avatar_contradiction_clause,[],[f1482])).

fof(f1482,plain,
    ( $false
    | spl9_5
    | ~ spl9_6
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f1481,f1414])).

fof(f1481,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | ~ spl9_6
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f1479,f1398])).

fof(f1398,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k4_zfmisc_1(k1_xboole_0,X1,X2,X3) ),
    inference(equality_resolution,[],[f1388])).

fof(f1388,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f1375])).

fof(f1479,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(k1_xboole_0,sK5,sK6,sK7)
    | ~ spl9_6
    | ~ spl9_7 ),
    inference(backward_demodulation,[],[f1418,f1465])).

fof(f1465,plain,
    ( k1_xboole_0 = sK4
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f1464])).

fof(f1419,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f1376,f1417])).

fof(f1376,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f1371])).

fof(f1371,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f1364,f1370])).

fof(f1370,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
      & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f1364,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f1363])).

fof(f1363,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f1355])).

fof(f1355,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    inference(negated_conjecture,[],[f1354])).

fof(f1354,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).

fof(f1415,plain,(
    ~ spl9_5 ),
    inference(avatar_split_clause,[],[f1377,f1413])).

fof(f1377,plain,(
    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f1371])).

fof(f1411,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f1378,f1409,f1406,f1403,f1400])).

fof(f1378,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f1371])).
%------------------------------------------------------------------------------
