%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0877+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:55 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 133 expanded)
%              Number of leaves         :   15 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :  244 ( 473 expanded)
%              Number of equality atoms :  155 ( 348 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1526,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1374,f1378,f1382,f1425,f1433,f1437,f1442,f1459,f1477,f1486,f1518,f1525])).

fof(f1525,plain,
    ( spl7_3
    | ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f1524])).

fof(f1524,plain,
    ( $false
    | spl7_3
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f1523,f1373])).

fof(f1373,plain,
    ( sK2 != sK5
    | spl7_3 ),
    inference(avatar_component_clause,[],[f1372])).

fof(f1372,plain,
    ( spl7_3
  <=> sK2 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f1523,plain,
    ( sK2 = sK5
    | ~ spl7_12 ),
    inference(equality_resolution,[],[f1476])).

fof(f1476,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | sK5 = X17 )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f1475])).

fof(f1475,plain,
    ( spl7_12
  <=> ! [X16,X15,X17] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | sK5 = X17 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f1518,plain,
    ( spl7_2
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f1514,f1457,f1369])).

fof(f1369,plain,
    ( spl7_2
  <=> sK1 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1457,plain,
    ( spl7_11
  <=> ! [X16,X15,X17] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | sK4 = X16 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f1514,plain,
    ( sK1 = sK4
    | ~ spl7_11 ),
    inference(equality_resolution,[],[f1458])).

fof(f1458,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | sK4 = X16 )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f1457])).

fof(f1486,plain,
    ( spl7_1
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f1482,f1418,f1366])).

fof(f1366,plain,
    ( spl7_1
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1418,plain,
    ( spl7_9
  <=> ! [X1,X0,X2] :
        ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
        | sK3 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f1482,plain,
    ( sK0 = sK3
    | ~ spl7_9 ),
    inference(equality_resolution,[],[f1419])).

% (23792)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
% (23790)dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34 on theBenchmark
% (23804)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_88 on theBenchmark
% (23779)lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11 on theBenchmark
fof(f1419,plain,
    ( ! [X2,X0,X1] :
        ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
        | sK3 = X0 )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f1418])).

fof(f1477,plain,
    ( spl7_6
    | spl7_7
    | spl7_8
    | spl7_12
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f1465,f1380,f1475,f1415,f1412,f1409])).

fof(f1409,plain,
    ( spl7_6
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f1412,plain,
    ( spl7_7
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f1415,plain,
    ( spl7_8
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f1380,plain,
    ( spl7_5
  <=> k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f1465,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK4
        | k1_xboole_0 = sK3
        | sK5 = X17 )
    | ~ spl7_5 ),
    inference(superposition,[],[f1356,f1381])).

fof(f1381,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f1380])).

fof(f1356,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X2 = X5 ) ),
    inference(cnf_transformation,[],[f1340])).

fof(f1340,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f1339])).

fof(f1339,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f1322])).

fof(f1322,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

fof(f1459,plain,
    ( spl7_6
    | spl7_7
    | spl7_8
    | spl7_11
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f1447,f1380,f1457,f1415,f1412,f1409])).

fof(f1447,plain,
    ( ! [X17,X15,X16] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(X15,X16,X17)
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK4
        | k1_xboole_0 = sK3
        | sK4 = X16 )
    | ~ spl7_5 ),
    inference(superposition,[],[f1355,f1381])).

fof(f1355,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X1 = X4 ) ),
    inference(cnf_transformation,[],[f1340])).

fof(f1442,plain,
    ( spl7_6
    | spl7_7
    | spl7_8
    | spl7_9
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f1439,f1380,f1418,f1415,f1412,f1409])).

fof(f1439,plain,
    ( ! [X4,X5,X3] :
        ( k3_zfmisc_1(X3,X4,X5) != k3_zfmisc_1(sK0,sK1,sK2)
        | k1_xboole_0 = sK5
        | k1_xboole_0 = sK4
        | k1_xboole_0 = sK3
        | sK3 = X3 )
    | ~ spl7_5 ),
    inference(superposition,[],[f1354,f1381])).

fof(f1354,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f1340])).

fof(f1437,plain,
    ( spl7_4
    | ~ spl7_5
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f1436])).

fof(f1436,plain,
    ( $false
    | spl7_4
    | ~ spl7_5
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f1435,f1377])).

fof(f1377,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f1376])).

fof(f1376,plain,
    ( spl7_4
  <=> k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1435,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | ~ spl7_5
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f1434,f1362])).

fof(f1362,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_zfmisc_1(X0,X1,k1_xboole_0) ),
    inference(equality_resolution,[],[f1360])).

fof(f1360,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f1346])).

fof(f1346,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f1345])).

fof(f1345,plain,(
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

fof(f1434,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,k1_xboole_0)
    | ~ spl7_5
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f1381,f1416])).

fof(f1416,plain,
    ( k1_xboole_0 = sK5
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f1415])).

fof(f1433,plain,
    ( spl7_4
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f1432])).

fof(f1432,plain,
    ( $false
    | spl7_4
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f1431,f1377])).

fof(f1431,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f1430,f1363])).

fof(f1363,plain,(
    ! [X2,X0] : k1_xboole_0 = k3_zfmisc_1(X0,k1_xboole_0,X2) ),
    inference(equality_resolution,[],[f1359])).

fof(f1359,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f1346])).

fof(f1430,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,k1_xboole_0,sK5)
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f1381,f1413])).

fof(f1413,plain,
    ( k1_xboole_0 = sK4
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f1412])).

fof(f1425,plain,
    ( spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f1424])).

fof(f1424,plain,
    ( $false
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f1423,f1377])).

fof(f1423,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f1421,f1364])).

fof(f1364,plain,(
    ! [X2,X1] : k1_xboole_0 = k3_zfmisc_1(k1_xboole_0,X1,X2) ),
    inference(equality_resolution,[],[f1358])).

fof(f1358,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f1346])).

fof(f1421,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(k1_xboole_0,sK4,sK5)
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f1381,f1410])).

fof(f1410,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f1409])).

fof(f1382,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f1347,f1380])).

fof(f1347,plain,(
    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f1342])).

fof(f1342,plain,
    ( ( sK2 != sK5
      | sK1 != sK4
      | sK0 != sK3 )
    & k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
    & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f1335,f1341])).

fof(f1341,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( X2 != X5
          | X1 != X4
          | X0 != X3 )
        & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) )
   => ( ( sK2 != sK5
        | sK1 != sK4
        | sK0 != sK3 )
      & k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
      & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f1335,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f1334])).

fof(f1334,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f1324])).

fof(f1324,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
       => ( ( X2 = X5
            & X1 = X4
            & X0 = X3 )
          | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    inference(negated_conjecture,[],[f1323])).

fof(f1323,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

fof(f1378,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f1348,f1376])).

fof(f1348,plain,(
    k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f1342])).

fof(f1374,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f1349,f1372,f1369,f1366])).

fof(f1349,plain,
    ( sK2 != sK5
    | sK1 != sK4
    | sK0 != sK3 ),
    inference(cnf_transformation,[],[f1342])).
%------------------------------------------------------------------------------
