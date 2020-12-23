%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0377+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:27 EST 2020

% Result     : Theorem 14.77s
% Output     : Refutation 15.11s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 169 expanded)
%              Number of leaves         :   29 (  68 expanded)
%              Depth                    :    8
%              Number of atoms          :  270 ( 530 expanded)
%              Number of equality atoms :   32 (  60 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1607,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1297,f1302,f1307,f1312,f1318,f1323,f1328,f1344,f1406,f1465,f1474,f1476,f1488,f1497,f1582,f1594,f1596,f1598])).

fof(f1598,plain,
    ( ~ spl34_8
    | ~ spl34_17 ),
    inference(avatar_split_clause,[],[f1454,f1384,f1332])).

fof(f1332,plain,
    ( spl34_8
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_8])])).

fof(f1384,plain,
    ( spl34_17
  <=> r2_hidden(sK5,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_17])])).

fof(f1454,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl34_17 ),
    inference(resolution,[],[f1386,f1000])).

fof(f1000,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f1386,plain,
    ( r2_hidden(sK5,sK0)
    | ~ spl34_17 ),
    inference(avatar_component_clause,[],[f1384])).

fof(f1596,plain,
    ( ~ spl34_42
    | ~ spl34_31
    | spl34_30 ),
    inference(avatar_split_clause,[],[f1561,f1485,f1494,f1568])).

fof(f1568,plain,
    ( spl34_42
  <=> r1_tarski(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_42])])).

fof(f1494,plain,
    ( spl34_31
  <=> r1_tarski(k2_enumset1(sK2,sK3,sK4,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_31])])).

fof(f1485,plain,
    ( spl34_30
  <=> r1_tarski(k2_xboole_0(k1_tarski(sK1),k2_enumset1(sK2,sK3,sK4,sK5)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_30])])).

fof(f1561,plain,
    ( ~ r1_tarski(k2_enumset1(sK2,sK3,sK4,sK5),sK0)
    | ~ r1_tarski(k1_tarski(sK1),sK0)
    | spl34_30 ),
    inference(resolution,[],[f1487,f784])).

fof(f784,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f570])).

fof(f570,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f569])).

fof(f569,plain,(
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

fof(f1487,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k2_enumset1(sK2,sK3,sK4,sK5)),sK0)
    | spl34_30 ),
    inference(avatar_component_clause,[],[f1485])).

fof(f1594,plain,
    ( spl34_17
    | ~ spl34_22 ),
    inference(avatar_split_clause,[],[f1503,f1412,f1384])).

fof(f1412,plain,
    ( spl34_22
  <=> m1_subset_1(k2_enumset1(sK2,sK3,sK4,sK5),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_22])])).

fof(f1503,plain,
    ( r2_hidden(sK5,sK0)
    | ~ spl34_22 ),
    inference(resolution,[],[f1471,f1257])).

fof(f1257,plain,(
    ! [X2,X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X1,X2,X5)) ),
    inference(equality_resolution,[],[f1256])).

fof(f1256,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r2_hidden(X5,X4)
      | k2_enumset1(X0,X1,X2,X5) != X4 ) ),
    inference(equality_resolution,[],[f884])).

fof(f884,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X3 != X5
      | r2_hidden(X5,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f607])).

fof(f607,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f455])).

fof(f455,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

fof(f1471,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK2,sK3,sK4,sK5))
        | r2_hidden(X0,sK0) )
    | ~ spl34_22 ),
    inference(resolution,[],[f1413,f771])).

fof(f771,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f556])).

fof(f556,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f481])).

fof(f481,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f1413,plain,
    ( m1_subset_1(k2_enumset1(sK2,sK3,sK4,sK5),k1_zfmisc_1(sK0))
    | ~ spl34_22 ),
    inference(avatar_component_clause,[],[f1412])).

fof(f1582,plain,
    ( ~ spl34_10
    | spl34_42 ),
    inference(avatar_split_clause,[],[f1579,f1568,f1341])).

fof(f1341,plain,
    ( spl34_10
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_10])])).

fof(f1579,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl34_42 ),
    inference(resolution,[],[f1570,f860])).

fof(f860,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f302])).

fof(f302,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f1570,plain,
    ( ~ r1_tarski(k1_tarski(sK1),sK0)
    | spl34_42 ),
    inference(avatar_component_clause,[],[f1568])).

fof(f1497,plain,
    ( spl34_31
    | ~ spl34_29 ),
    inference(avatar_split_clause,[],[f1489,f1467,f1494])).

fof(f1467,plain,
    ( spl34_29
  <=> r2_hidden(k2_enumset1(sK2,sK3,sK4,sK5),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_29])])).

fof(f1489,plain,
    ( r1_tarski(k2_enumset1(sK2,sK3,sK4,sK5),sK0)
    | ~ spl34_29 ),
    inference(resolution,[],[f1468,f1216])).

fof(f1216,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f669])).

fof(f669,plain,(
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

fof(f1468,plain,
    ( r2_hidden(k2_enumset1(sK2,sK3,sK4,sK5),k1_zfmisc_1(sK0))
    | ~ spl34_29 ),
    inference(avatar_component_clause,[],[f1467])).

fof(f1488,plain,
    ( ~ spl34_30
    | spl34_20 ),
    inference(avatar_split_clause,[],[f1480,f1403,f1485])).

fof(f1403,plain,
    ( spl34_20
  <=> r2_hidden(k2_xboole_0(k1_tarski(sK1),k2_enumset1(sK2,sK3,sK4,sK5)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_20])])).

fof(f1480,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k2_enumset1(sK2,sK3,sK4,sK5)),sK0)
    | spl34_20 ),
    inference(resolution,[],[f1405,f1217])).

fof(f1217,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f668])).

fof(f668,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f285])).

fof(f1405,plain,
    ( ~ r2_hidden(k2_xboole_0(k1_tarski(sK1),k2_enumset1(sK2,sK3,sK4,sK5)),k1_zfmisc_1(sK0))
    | spl34_20 ),
    inference(avatar_component_clause,[],[f1403])).

fof(f1476,plain,(
    ~ spl34_19 ),
    inference(avatar_contradiction_clause,[],[f1475])).

fof(f1475,plain,
    ( $false
    | ~ spl34_19 ),
    inference(resolution,[],[f1401,f1008])).

fof(f1008,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f473])).

fof(f473,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f1401,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl34_19 ),
    inference(avatar_component_clause,[],[f1399])).

fof(f1399,plain,
    ( spl34_19
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_19])])).

fof(f1474,plain,
    ( spl34_19
    | spl34_29
    | ~ spl34_22 ),
    inference(avatar_split_clause,[],[f1473,f1412,f1467,f1399])).

fof(f1473,plain,
    ( r2_hidden(k2_enumset1(sK2,sK3,sK4,sK5),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl34_22 ),
    inference(resolution,[],[f1413,f995])).

fof(f995,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f640])).

fof(f640,plain,(
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

fof(f1465,plain,
    ( ~ spl34_2
    | spl34_6
    | ~ spl34_7
    | ~ spl34_4
    | ~ spl34_3
    | spl34_22 ),
    inference(avatar_split_clause,[],[f1462,f1412,f1304,f1309,f1325,f1320,f1299])).

fof(f1299,plain,
    ( spl34_2
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_2])])).

fof(f1320,plain,
    ( spl34_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_6])])).

fof(f1325,plain,
    ( spl34_7
  <=> m1_subset_1(sK5,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_7])])).

fof(f1309,plain,
    ( spl34_4
  <=> m1_subset_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_4])])).

fof(f1304,plain,
    ( spl34_3
  <=> m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_3])])).

fof(f1462,plain,
    ( ~ m1_subset_1(sK3,sK0)
    | ~ m1_subset_1(sK4,sK0)
    | ~ m1_subset_1(sK5,sK0)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK2,sK0)
    | spl34_22 ),
    inference(resolution,[],[f1414,f905])).

fof(f905,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X4,X0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f609])).

fof(f609,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
                  | k1_xboole_0 = X0
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f608])).

fof(f608,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
                  | k1_xboole_0 = X0
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f523])).

fof(f523,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ( k1_xboole_0 != X0
                   => m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_subset_1)).

fof(f1414,plain,
    ( ~ m1_subset_1(k2_enumset1(sK2,sK3,sK4,sK5),k1_zfmisc_1(sK0))
    | spl34_22 ),
    inference(avatar_component_clause,[],[f1412])).

fof(f1406,plain,
    ( spl34_19
    | ~ spl34_20
    | spl34_5 ),
    inference(avatar_split_clause,[],[f1394,f1315,f1403,f1399])).

fof(f1315,plain,
    ( spl34_5
  <=> m1_subset_1(k2_xboole_0(k1_tarski(sK1),k2_enumset1(sK2,sK3,sK4,sK5)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_5])])).

fof(f1394,plain,
    ( ~ r2_hidden(k2_xboole_0(k1_tarski(sK1),k2_enumset1(sK2,sK3,sK4,sK5)),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | spl34_5 ),
    inference(resolution,[],[f1317,f994])).

fof(f994,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f640])).

fof(f1317,plain,
    ( ~ m1_subset_1(k2_xboole_0(k1_tarski(sK1),k2_enumset1(sK2,sK3,sK4,sK5)),k1_zfmisc_1(sK0))
    | spl34_5 ),
    inference(avatar_component_clause,[],[f1315])).

fof(f1344,plain,
    ( spl34_8
    | spl34_10
    | ~ spl34_1 ),
    inference(avatar_split_clause,[],[f1330,f1294,f1341,f1332])).

fof(f1294,plain,
    ( spl34_1
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_1])])).

fof(f1330,plain,
    ( r2_hidden(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl34_1 ),
    inference(resolution,[],[f1296,f995])).

fof(f1296,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl34_1 ),
    inference(avatar_component_clause,[],[f1294])).

fof(f1328,plain,(
    spl34_7 ),
    inference(avatar_split_clause,[],[f661,f1325])).

fof(f661,plain,(
    m1_subset_1(sK5,sK0) ),
    inference(cnf_transformation,[],[f533])).

fof(f533,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
                      & k1_xboole_0 != X0
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f532])).

fof(f532,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
                      & k1_xboole_0 != X0
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f525])).

fof(f525,negated_conjecture,(
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
                       => ( k1_xboole_0 != X0
                         => m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f524])).

fof(f524,conjecture,(
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
                     => ( k1_xboole_0 != X0
                       => m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_subset_1)).

fof(f1323,plain,(
    ~ spl34_6 ),
    inference(avatar_split_clause,[],[f662,f1320])).

fof(f662,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f533])).

fof(f1318,plain,(
    ~ spl34_5 ),
    inference(avatar_split_clause,[],[f1313,f1315])).

fof(f1313,plain,(
    ~ m1_subset_1(k2_xboole_0(k1_tarski(sK1),k2_enumset1(sK2,sK3,sK4,sK5)),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f1049,f1066])).

fof(f1066,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(definition_unfolding,[],[f692,f688])).

fof(f688,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f235])).

fof(f235,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f692,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f232])).

fof(f232,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(f1049,plain,(
    ~ m1_subset_1(k2_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k1_tarski(sK5)),k1_zfmisc_1(sK0)) ),
    inference(definition_unfolding,[],[f663,f688])).

fof(f663,plain,(
    ~ m1_subset_1(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f533])).

fof(f1312,plain,(
    spl34_4 ),
    inference(avatar_split_clause,[],[f664,f1309])).

fof(f664,plain,(
    m1_subset_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f533])).

fof(f1307,plain,(
    spl34_3 ),
    inference(avatar_split_clause,[],[f665,f1304])).

fof(f665,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f533])).

fof(f1302,plain,(
    spl34_2 ),
    inference(avatar_split_clause,[],[f666,f1299])).

fof(f666,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f533])).

fof(f1297,plain,(
    spl34_1 ),
    inference(avatar_split_clause,[],[f667,f1294])).

fof(f667,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f533])).
%------------------------------------------------------------------------------
