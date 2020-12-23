%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0378+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:27 EST 2020

% Result     : Theorem 18.15s
% Output     : Refutation 18.15s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 177 expanded)
%              Number of leaves         :   30 (  71 expanded)
%              Depth                    :    8
%              Number of atoms          :  286 ( 604 expanded)
%              Number of equality atoms :   34 (  66 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1734,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1387,f1392,f1397,f1402,f1407,f1413,f1418,f1423,f1439,f1513,f1580,f1589,f1591,f1603,f1612,f1694,f1718,f1720,f1733])).

fof(f1733,plain,
    ( spl36_20
    | ~ spl36_25 ),
    inference(avatar_split_clause,[],[f1618,f1519,f1491])).

fof(f1491,plain,
    ( spl36_20
  <=> r2_hidden(sK6,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_20])])).

fof(f1519,plain,
    ( spl36_25
  <=> m1_subset_1(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_25])])).

fof(f1618,plain,
    ( r2_hidden(sK6,sK0)
    | ~ spl36_25 ),
    inference(resolution,[],[f1586,f1333])).

fof(f1333,plain,(
    ! [X6,X2,X0,X3,X1] : r2_hidden(X6,k3_enumset1(X0,X1,X2,X3,X6)) ),
    inference(equality_resolution,[],[f1332])).

fof(f1332,plain,(
    ! [X6,X2,X0,X5,X3,X1] :
      ( r2_hidden(X6,X5)
      | k3_enumset1(X0,X1,X2,X3,X6) != X5 ) ),
    inference(equality_resolution,[],[f850])).

fof(f850,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( X4 != X6
      | r2_hidden(X6,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f591])).

fof(f591,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f457])).

fof(f457,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(f1586,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_enumset1(sK2,sK3,sK4,sK5,sK6))
        | r2_hidden(X0,sK0) )
    | ~ spl36_25 ),
    inference(resolution,[],[f1520,f781])).

fof(f781,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f559])).

fof(f559,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f483])).

fof(f483,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f1520,plain,
    ( m1_subset_1(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(sK0))
    | ~ spl36_25 ),
    inference(avatar_component_clause,[],[f1519])).

fof(f1720,plain,
    ( ~ spl36_9
    | ~ spl36_20 ),
    inference(avatar_split_clause,[],[f1569,f1491,f1427])).

fof(f1427,plain,
    ( spl36_9
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_9])])).

fof(f1569,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl36_20 ),
    inference(resolution,[],[f1493,f987])).

fof(f987,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f1493,plain,
    ( r2_hidden(sK6,sK0)
    | ~ spl36_20 ),
    inference(avatar_component_clause,[],[f1491])).

fof(f1718,plain,
    ( ~ spl36_11
    | spl36_47 ),
    inference(avatar_split_clause,[],[f1715,f1691,f1436])).

fof(f1436,plain,
    ( spl36_11
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_11])])).

fof(f1691,plain,
    ( spl36_47
  <=> r1_tarski(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_47])])).

fof(f1715,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl36_47 ),
    inference(resolution,[],[f1693,f824])).

fof(f824,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f395])).

fof(f395,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f1693,plain,
    ( ~ r1_tarski(k1_tarski(sK1),sK0)
    | spl36_47 ),
    inference(avatar_component_clause,[],[f1691])).

fof(f1694,plain,
    ( ~ spl36_47
    | ~ spl36_35
    | spl36_34 ),
    inference(avatar_split_clause,[],[f1685,f1600,f1609,f1691])).

fof(f1609,plain,
    ( spl36_35
  <=> r1_tarski(k3_enumset1(sK2,sK3,sK4,sK5,sK6),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_35])])).

fof(f1600,plain,
    ( spl36_34
  <=> r1_tarski(k2_xboole_0(k1_tarski(sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_34])])).

fof(f1685,plain,
    ( ~ r1_tarski(k3_enumset1(sK2,sK3,sK4,sK5,sK6),sK0)
    | ~ r1_tarski(k1_tarski(sK1),sK0)
    | spl36_34 ),
    inference(resolution,[],[f1602,f794])).

fof(f794,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f573])).

fof(f573,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f572])).

fof(f572,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f1602,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)),sK0)
    | spl36_34 ),
    inference(avatar_component_clause,[],[f1600])).

fof(f1612,plain,
    ( spl36_35
    | ~ spl36_33 ),
    inference(avatar_split_clause,[],[f1604,f1582,f1609])).

fof(f1582,plain,
    ( spl36_33
  <=> r2_hidden(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_33])])).

fof(f1604,plain,
    ( r1_tarski(k3_enumset1(sK2,sK3,sK4,sK5,sK6),sK0)
    | ~ spl36_33 ),
    inference(resolution,[],[f1583,f1293])).

fof(f1293,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f676])).

fof(f676,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f1583,plain,
    ( r2_hidden(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(sK0))
    | ~ spl36_33 ),
    inference(avatar_component_clause,[],[f1582])).

fof(f1603,plain,
    ( ~ spl36_34
    | spl36_23 ),
    inference(avatar_split_clause,[],[f1595,f1510,f1600])).

fof(f1510,plain,
    ( spl36_23
  <=> r2_hidden(k2_xboole_0(k1_tarski(sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_23])])).

fof(f1595,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)),sK0)
    | spl36_23 ),
    inference(resolution,[],[f1512,f1294])).

fof(f1294,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f675])).

fof(f675,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f285])).

fof(f1512,plain,
    ( ~ r2_hidden(k2_xboole_0(k1_tarski(sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)),k1_zfmisc_1(sK0))
    | spl36_23 ),
    inference(avatar_component_clause,[],[f1510])).

fof(f1591,plain,(
    ~ spl36_22 ),
    inference(avatar_contradiction_clause,[],[f1590])).

fof(f1590,plain,
    ( $false
    | ~ spl36_22 ),
    inference(resolution,[],[f1508,f995])).

fof(f995,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f474])).

fof(f474,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f1508,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl36_22 ),
    inference(avatar_component_clause,[],[f1506])).

fof(f1506,plain,
    ( spl36_22
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_22])])).

fof(f1589,plain,
    ( spl36_22
    | spl36_33
    | ~ spl36_25 ),
    inference(avatar_split_clause,[],[f1588,f1519,f1582,f1506])).

fof(f1588,plain,
    ( r2_hidden(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl36_25 ),
    inference(resolution,[],[f1520,f982])).

fof(f982,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f627])).

fof(f627,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f1580,plain,
    ( ~ spl36_2
    | spl36_7
    | ~ spl36_8
    | ~ spl36_5
    | ~ spl36_4
    | ~ spl36_3
    | spl36_25 ),
    inference(avatar_split_clause,[],[f1577,f1519,f1394,f1399,f1404,f1420,f1415,f1389])).

fof(f1389,plain,
    ( spl36_2
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_2])])).

fof(f1415,plain,
    ( spl36_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_7])])).

fof(f1420,plain,
    ( spl36_8
  <=> m1_subset_1(sK6,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_8])])).

fof(f1404,plain,
    ( spl36_5
  <=> m1_subset_1(sK5,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_5])])).

fof(f1399,plain,
    ( spl36_4
  <=> m1_subset_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_4])])).

fof(f1394,plain,
    ( spl36_3
  <=> m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_3])])).

fof(f1577,plain,
    ( ~ m1_subset_1(sK3,sK0)
    | ~ m1_subset_1(sK4,sK0)
    | ~ m1_subset_1(sK5,sK0)
    | ~ m1_subset_1(sK6,sK0)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK2,sK0)
    | spl36_25 ),
    inference(resolution,[],[f1521,f859])).

fof(f859,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X5,X0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f593])).

fof(f593,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
                      | k1_xboole_0 = X0
                      | ~ m1_subset_1(X5,X0) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f592])).

fof(f592,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( m1_subset_1(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X0))
                      | k1_xboole_0 = X0
                      | ~ m1_subset_1(X5,X0) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f526])).

fof(f526,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_subset_1)).

fof(f1521,plain,
    ( ~ m1_subset_1(k3_enumset1(sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(sK0))
    | spl36_25 ),
    inference(avatar_component_clause,[],[f1519])).

fof(f1513,plain,
    ( spl36_22
    | ~ spl36_23
    | spl36_6 ),
    inference(avatar_split_clause,[],[f1501,f1410,f1510,f1506])).

fof(f1410,plain,
    ( spl36_6
  <=> m1_subset_1(k2_xboole_0(k1_tarski(sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_6])])).

fof(f1501,plain,
    ( ~ r2_hidden(k2_xboole_0(k1_tarski(sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | spl36_6 ),
    inference(resolution,[],[f1412,f981])).

fof(f981,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f627])).

fof(f1412,plain,
    ( ~ m1_subset_1(k2_xboole_0(k1_tarski(sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)),k1_zfmisc_1(sK0))
    | spl36_6 ),
    inference(avatar_component_clause,[],[f1410])).

fof(f1439,plain,
    ( spl36_9
    | spl36_11
    | ~ spl36_1 ),
    inference(avatar_split_clause,[],[f1425,f1384,f1436,f1427])).

fof(f1384,plain,
    ( spl36_1
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_1])])).

fof(f1425,plain,
    ( r2_hidden(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl36_1 ),
    inference(resolution,[],[f1386,f982])).

fof(f1386,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl36_1 ),
    inference(avatar_component_clause,[],[f1384])).

fof(f1423,plain,(
    spl36_8 ),
    inference(avatar_split_clause,[],[f667,f1420])).

fof(f667,plain,(
    m1_subset_1(sK6,sK0) ),
    inference(cnf_transformation,[],[f536])).

fof(f536,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                          & k1_xboole_0 != X0
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f535])).

fof(f535,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0))
                          & k1_xboole_0 != X0
                          & m1_subset_1(X6,X0) )
                      & m1_subset_1(X5,X0) )
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f528])).

fof(f528,negated_conjecture,(
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
                           => ( k1_xboole_0 != X0
                             => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f527])).

fof(f527,conjecture,(
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
                         => ( k1_xboole_0 != X0
                           => m1_subset_1(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_subset_1)).

fof(f1418,plain,(
    ~ spl36_7 ),
    inference(avatar_split_clause,[],[f668,f1415])).

fof(f668,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f536])).

fof(f1413,plain,(
    ~ spl36_6 ),
    inference(avatar_split_clause,[],[f1408,f1410])).

fof(f1408,plain,(
    ~ m1_subset_1(k2_xboole_0(k1_tarski(sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f1084,f1103])).

fof(f1103,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(definition_unfolding,[],[f701,f696])).

fof(f696,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f240])).

fof(f240,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(f701,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f236])).

fof(f236,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(f1084,plain,(
    ~ m1_subset_1(k2_xboole_0(k3_enumset1(sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)),k1_zfmisc_1(sK0)) ),
    inference(definition_unfolding,[],[f669,f696])).

fof(f669,plain,(
    ~ m1_subset_1(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f536])).

fof(f1407,plain,(
    spl36_5 ),
    inference(avatar_split_clause,[],[f670,f1404])).

fof(f670,plain,(
    m1_subset_1(sK5,sK0) ),
    inference(cnf_transformation,[],[f536])).

fof(f1402,plain,(
    spl36_4 ),
    inference(avatar_split_clause,[],[f671,f1399])).

fof(f671,plain,(
    m1_subset_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f536])).

fof(f1397,plain,(
    spl36_3 ),
    inference(avatar_split_clause,[],[f672,f1394])).

fof(f672,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f536])).

fof(f1392,plain,(
    spl36_2 ),
    inference(avatar_split_clause,[],[f673,f1389])).

fof(f673,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f536])).

fof(f1387,plain,(
    spl36_1 ),
    inference(avatar_split_clause,[],[f674,f1384])).

fof(f674,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f536])).
%------------------------------------------------------------------------------
