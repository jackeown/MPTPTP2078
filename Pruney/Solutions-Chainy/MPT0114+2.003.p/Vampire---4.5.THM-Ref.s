%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:46 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 305 expanded)
%              Number of leaves         :   40 ( 135 expanded)
%              Depth                    :   11
%              Number of atoms          :  462 ( 824 expanded)
%              Number of equality atoms :   83 ( 181 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4235,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f70,f79,f83,f87,f91,f95,f99,f103,f125,f129,f203,f207,f308,f311,f336,f397,f441,f664,f680,f948,f953,f1050,f1380,f1571,f1581,f1804,f1892,f3501,f3513,f4020,f4079,f4188,f4234])).

fof(f4234,plain,
    ( spl3_25
    | ~ spl3_34
    | ~ spl3_71
    | ~ spl3_109
    | ~ spl3_125 ),
    inference(avatar_contradiction_clause,[],[f4233])).

fof(f4233,plain,
    ( $false
    | spl3_25
    | ~ spl3_34
    | ~ spl3_71
    | ~ spl3_109
    | ~ spl3_125 ),
    inference(subsumption_resolution,[],[f535,f4231])).

fof(f4231,plain,
    ( r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0)
    | ~ spl3_71
    | ~ spl3_109
    | ~ spl3_125 ),
    inference(forward_demodulation,[],[f3536,f4024])).

fof(f4024,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_71
    | ~ spl3_125 ),
    inference(superposition,[],[f4019,f1379])).

fof(f1379,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))
    | ~ spl3_71 ),
    inference(avatar_component_clause,[],[f1378])).

fof(f1378,plain,
    ( spl3_71
  <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k2_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).

fof(f4019,plain,
    ( ! [X27] : k4_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),X27)) = k4_xboole_0(sK0,X27)
    | ~ spl3_125 ),
    inference(avatar_component_clause,[],[f4018])).

fof(f4018,plain,
    ( spl3_125
  <=> ! [X27] : k4_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),X27)) = k4_xboole_0(sK0,X27) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_125])])).

fof(f3536,plain,
    ( r1_tarski(k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k1_xboole_0)
    | ~ spl3_109 ),
    inference(avatar_component_clause,[],[f3535])).

fof(f3535,plain,
    ( spl3_109
  <=> r1_tarski(k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_109])])).

fof(f535,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0)
    | spl3_25
    | ~ spl3_34 ),
    inference(unit_resulting_resolution,[],[f288,f440])).

fof(f440,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f439])).

fof(f439,plain,
    ( spl3_34
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f288,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl3_25 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl3_25
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f4188,plain,
    ( ~ spl3_11
    | ~ spl3_12
    | ~ spl3_26
    | ~ spl3_31
    | spl3_109 ),
    inference(avatar_contradiction_clause,[],[f4187])).

fof(f4187,plain,
    ( $false
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_26
    | ~ spl3_31
    | spl3_109 ),
    inference(subsumption_resolution,[],[f396,f4185])).

fof(f4185,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_26
    | spl3_109 ),
    inference(subsumption_resolution,[],[f3546,f4132])).

fof(f4132,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_11
    | ~ spl3_26 ),
    inference(trivial_inequality_removal,[],[f542])).

fof(f542,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_11
    | ~ spl3_26 ),
    inference(superposition,[],[f98,f305])).

fof(f305,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl3_26
  <=> k1_xboole_0 = k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != k1_xboole_0
        | r1_tarski(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f3546,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_12
    | spl3_109 ),
    inference(superposition,[],[f3537,f102])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f3537,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k1_xboole_0)
    | spl3_109 ),
    inference(avatar_component_clause,[],[f3535])).

fof(f396,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f394])).

fof(f394,plain,
    ( spl3_31
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f4079,plain,
    ( ~ spl3_25
    | spl3_26
    | ~ spl3_71
    | ~ spl3_125 ),
    inference(avatar_contradiction_clause,[],[f4078])).

fof(f4078,plain,
    ( $false
    | ~ spl3_25
    | spl3_26
    | ~ spl3_71
    | ~ spl3_125 ),
    inference(subsumption_resolution,[],[f304,f4077])).

fof(f4077,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_25
    | ~ spl3_71
    | ~ spl3_125 ),
    inference(forward_demodulation,[],[f4024,f289])).

fof(f289,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f287])).

fof(f304,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k5_xboole_0(sK1,sK2))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f303])).

fof(f4020,plain,
    ( spl3_125
    | ~ spl3_24
    | ~ spl3_59
    | ~ spl3_84 ),
    inference(avatar_split_clause,[],[f1856,f1802,f951,f278,f4018])).

fof(f278,plain,
    ( spl3_24
  <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f951,plain,
    ( spl3_59
  <=> ! [X9,X10] : k4_xboole_0(X9,k2_xboole_0(k1_xboole_0,X10)) = k4_xboole_0(X9,X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f1802,plain,
    ( spl3_84
  <=> ! [X3,X5,X4] : k4_xboole_0(X3,k2_xboole_0(k3_xboole_0(X3,X4),X5)) = k4_xboole_0(X3,k2_xboole_0(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).

fof(f1856,plain,
    ( ! [X27] : k4_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),X27)) = k4_xboole_0(sK0,X27)
    | ~ spl3_24
    | ~ spl3_59
    | ~ spl3_84 ),
    inference(forward_demodulation,[],[f1812,f952])).

fof(f952,plain,
    ( ! [X10,X9] : k4_xboole_0(X9,k2_xboole_0(k1_xboole_0,X10)) = k4_xboole_0(X9,X10)
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f951])).

fof(f1812,plain,
    ( ! [X27] : k4_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),X27)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X27))
    | ~ spl3_24
    | ~ spl3_84 ),
    inference(superposition,[],[f1803,f279])).

fof(f279,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f278])).

fof(f1803,plain,
    ( ! [X4,X5,X3] : k4_xboole_0(X3,k2_xboole_0(k3_xboole_0(X3,X4),X5)) = k4_xboole_0(X3,k2_xboole_0(X4,X5))
    | ~ spl3_84 ),
    inference(avatar_component_clause,[],[f1802])).

fof(f3513,plain,
    ( ~ spl3_1
    | ~ spl3_12
    | spl3_26 ),
    inference(avatar_split_clause,[],[f3317,f303,f101,f48])).

fof(f48,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f3317,plain,
    ( ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_12
    | spl3_26 ),
    inference(trivial_inequality_removal,[],[f427])).

fof(f427,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_12
    | spl3_26 ),
    inference(superposition,[],[f304,f102])).

fof(f3501,plain,
    ( spl3_2
    | ~ spl3_11
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f3315,f287,f97,f52])).

fof(f52,plain,
    ( spl3_2
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f3315,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_11
    | ~ spl3_25 ),
    inference(trivial_inequality_removal,[],[f417])).

fof(f417,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_11
    | ~ spl3_25 ),
    inference(superposition,[],[f98,f289])).

fof(f1892,plain,
    ( spl3_3
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f351,f278,f93,f60])).

fof(f60,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f93,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f351,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(trivial_inequality_removal,[],[f347])).

fof(f347,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(superposition,[],[f94,f279])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f93])).

fof(f1804,plain,
    ( spl3_84
    | ~ spl3_17
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f255,f205,f123,f1802])).

fof(f123,plain,
    ( spl3_17
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f205,plain,
    ( spl3_23
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f255,plain,
    ( ! [X4,X5,X3] : k4_xboole_0(X3,k2_xboole_0(k3_xboole_0(X3,X4),X5)) = k4_xboole_0(X3,k2_xboole_0(X4,X5))
    | ~ spl3_17
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f237,f206])).

fof(f206,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f205])).

fof(f237,plain,
    ( ! [X4,X5,X3] : k4_xboole_0(X3,k2_xboole_0(k3_xboole_0(X3,X4),X5)) = k4_xboole_0(k4_xboole_0(X3,X4),X5)
    | ~ spl3_17
    | ~ spl3_23 ),
    inference(superposition,[],[f206,f124])).

fof(f124,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f123])).

fof(f1581,plain,
    ( ~ spl3_47
    | ~ spl3_48
    | spl3_78 ),
    inference(avatar_contradiction_clause,[],[f1573])).

fof(f1573,plain,
    ( $false
    | ~ spl3_47
    | ~ spl3_48
    | spl3_78 ),
    inference(unit_resulting_resolution,[],[f679,f1570,f663])).

fof(f663,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 != k3_xboole_0(X3,X2)
        | r1_xboole_0(X2,X3) )
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f662])).

fof(f662,plain,
    ( spl3_47
  <=> ! [X3,X2] :
        ( k1_xboole_0 != k3_xboole_0(X3,X2)
        | r1_xboole_0(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f1570,plain,
    ( ~ r1_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
    | spl3_78 ),
    inference(avatar_component_clause,[],[f1568])).

fof(f1568,plain,
    ( spl3_78
  <=> r1_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).

fof(f679,plain,
    ( ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f678])).

fof(f678,plain,
    ( spl3_48
  <=> ! [X1,X0] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f1571,plain,
    ( ~ spl3_78
    | ~ spl3_1
    | spl3_3
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f191,f127,f60,f48,f1568])).

fof(f127,plain,
    ( spl3_18
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f191,plain,
    ( ~ r1_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
    | ~ spl3_1
    | spl3_3
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f61,f50,f128])).

fof(f128,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f127])).

fof(f50,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f61,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f1380,plain,
    ( spl3_71
    | ~ spl3_6
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f230,f201,f77,f1378])).

fof(f77,plain,
    ( spl3_6
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f201,plain,
    ( spl3_22
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f230,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))
    | ~ spl3_6
    | ~ spl3_22 ),
    inference(superposition,[],[f202,f78])).

fof(f78,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f202,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f201])).

fof(f1050,plain,
    ( spl3_1
    | ~ spl3_11
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f528,f303,f97,f48])).

fof(f528,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_11
    | ~ spl3_26 ),
    inference(trivial_inequality_removal,[],[f377])).

fof(f377,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_11
    | ~ spl3_26 ),
    inference(superposition,[],[f98,f305])).

fof(f953,plain,
    ( spl3_59
    | ~ spl3_4
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f239,f205,f68,f951])).

fof(f68,plain,
    ( spl3_4
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f239,plain,
    ( ! [X10,X9] : k4_xboole_0(X9,k2_xboole_0(k1_xboole_0,X10)) = k4_xboole_0(X9,X10)
    | ~ spl3_4
    | ~ spl3_23 ),
    inference(superposition,[],[f206,f69])).

fof(f69,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f948,plain,
    ( ~ spl3_2
    | ~ spl3_12
    | spl3_25 ),
    inference(avatar_split_clause,[],[f374,f287,f101,f52])).

fof(f374,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_12
    | spl3_25 ),
    inference(trivial_inequality_removal,[],[f373])).

fof(f373,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_12
    | spl3_25 ),
    inference(superposition,[],[f288,f102])).

fof(f680,plain,
    ( spl3_48
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f131,f89,f85,f678])).

fof(f85,plain,
    ( spl3_8
  <=> ! [X1,X0] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f89,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f131,plain,
    ( ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f86,f90])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f89])).

fof(f86,plain,
    ( ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f664,plain,
    ( spl3_47
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f149,f93,f81,f662])).

fof(f81,plain,
    ( spl3_7
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f149,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 != k3_xboole_0(X3,X2)
        | r1_xboole_0(X2,X3) )
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(superposition,[],[f94,f82])).

fof(f82,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f441,plain,
    ( spl3_34
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f155,f101,f68,f439])).

fof(f155,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(superposition,[],[f102,f69])).

fof(f397,plain,
    ( spl3_31
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f151,f97,f68,f394])).

fof(f151,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f69,f98])).

fof(f336,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f50,f334])).

fof(f334,plain,
    ( ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f56,f62])).

fof(f62,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f56,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f29,f54])).

fof(f54,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f29,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
      | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) )
    & ( ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
        & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) )
      | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
          | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
          | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
        & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
            & r1_tarski(X0,k2_xboole_0(X1,X2)) )
          | r1_tarski(X0,k5_xboole_0(X1,X2)) ) )
   => ( ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
        | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
        | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) )
      & ( ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
          & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) )
        | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <~> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k5_xboole_0(X1,X2))
      <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

fof(f311,plain,
    ( spl3_1
    | ~ spl3_9
    | spl3_24 ),
    inference(avatar_split_clause,[],[f310,f278,f89,f48])).

fof(f310,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_9
    | spl3_24 ),
    inference(subsumption_resolution,[],[f28,f285])).

fof(f285,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_9
    | spl3_24 ),
    inference(trivial_inequality_removal,[],[f284])).

fof(f284,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_9
    | spl3_24 ),
    inference(superposition,[],[f280,f90])).

fof(f280,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f278])).

fof(f28,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f308,plain,
    ( ~ spl3_3
    | ~ spl3_9
    | spl3_24 ),
    inference(avatar_contradiction_clause,[],[f307])).

fof(f307,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_9
    | spl3_24 ),
    inference(subsumption_resolution,[],[f285,f62])).

fof(f207,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f45,f205])).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f203,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f40,f201])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f129,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f46,f127])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f125,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f38,f123])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f103,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f44,f101])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f99,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f43,f97])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f95,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f42,f93])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f91,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f41,f89])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f87,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f34,f85])).

fof(f34,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f83,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f33,f81])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f79,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f32,f77])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f70,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f30,f68])).

fof(f30,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f55,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f27,f52,f48])).

fof(f27,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:28:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.41  % (16655)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (16645)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (16654)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (16650)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (16660)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (16647)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (16648)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (16657)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (16658)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (16652)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (16656)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (16651)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (16649)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (16659)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (16646)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.52  % (16653)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (16661)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (16662)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 2.14/0.67  % (16650)Refutation found. Thanks to Tanya!
% 2.14/0.67  % SZS status Theorem for theBenchmark
% 2.14/0.67  % SZS output start Proof for theBenchmark
% 2.14/0.67  fof(f4235,plain,(
% 2.14/0.67    $false),
% 2.14/0.67    inference(avatar_sat_refutation,[],[f55,f70,f79,f83,f87,f91,f95,f99,f103,f125,f129,f203,f207,f308,f311,f336,f397,f441,f664,f680,f948,f953,f1050,f1380,f1571,f1581,f1804,f1892,f3501,f3513,f4020,f4079,f4188,f4234])).
% 2.14/0.67  fof(f4234,plain,(
% 2.14/0.67    spl3_25 | ~spl3_34 | ~spl3_71 | ~spl3_109 | ~spl3_125),
% 2.14/0.67    inference(avatar_contradiction_clause,[],[f4233])).
% 2.14/0.67  fof(f4233,plain,(
% 2.14/0.67    $false | (spl3_25 | ~spl3_34 | ~spl3_71 | ~spl3_109 | ~spl3_125)),
% 2.14/0.67    inference(subsumption_resolution,[],[f535,f4231])).
% 2.14/0.67  fof(f4231,plain,(
% 2.14/0.67    r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0) | (~spl3_71 | ~spl3_109 | ~spl3_125)),
% 2.14/0.67    inference(forward_demodulation,[],[f3536,f4024])).
% 2.14/0.67  fof(f4024,plain,(
% 2.14/0.67    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) | (~spl3_71 | ~spl3_125)),
% 2.14/0.67    inference(superposition,[],[f4019,f1379])).
% 2.14/0.67  fof(f1379,plain,(
% 2.14/0.67    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))) ) | ~spl3_71),
% 2.14/0.67    inference(avatar_component_clause,[],[f1378])).
% 2.14/0.67  fof(f1378,plain,(
% 2.14/0.67    spl3_71 <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k2_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).
% 2.14/0.67  fof(f4019,plain,(
% 2.14/0.67    ( ! [X27] : (k4_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),X27)) = k4_xboole_0(sK0,X27)) ) | ~spl3_125),
% 2.14/0.67    inference(avatar_component_clause,[],[f4018])).
% 2.14/0.67  fof(f4018,plain,(
% 2.14/0.67    spl3_125 <=> ! [X27] : k4_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),X27)) = k4_xboole_0(sK0,X27)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_125])])).
% 2.14/0.67  fof(f3536,plain,(
% 2.14/0.67    r1_tarski(k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k1_xboole_0) | ~spl3_109),
% 2.14/0.67    inference(avatar_component_clause,[],[f3535])).
% 2.14/0.67  fof(f3535,plain,(
% 2.14/0.67    spl3_109 <=> r1_tarski(k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k1_xboole_0)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_109])])).
% 2.14/0.67  fof(f535,plain,(
% 2.14/0.67    ~r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0) | (spl3_25 | ~spl3_34)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f288,f440])).
% 2.14/0.67  fof(f440,plain,(
% 2.14/0.67    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl3_34),
% 2.14/0.67    inference(avatar_component_clause,[],[f439])).
% 2.14/0.67  fof(f439,plain,(
% 2.14/0.67    spl3_34 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 2.14/0.67  fof(f288,plain,(
% 2.14/0.67    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl3_25),
% 2.14/0.67    inference(avatar_component_clause,[],[f287])).
% 2.14/0.67  fof(f287,plain,(
% 2.14/0.67    spl3_25 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 2.14/0.67  fof(f4188,plain,(
% 2.14/0.67    ~spl3_11 | ~spl3_12 | ~spl3_26 | ~spl3_31 | spl3_109),
% 2.14/0.67    inference(avatar_contradiction_clause,[],[f4187])).
% 2.14/0.67  fof(f4187,plain,(
% 2.14/0.67    $false | (~spl3_11 | ~spl3_12 | ~spl3_26 | ~spl3_31 | spl3_109)),
% 2.14/0.67    inference(subsumption_resolution,[],[f396,f4185])).
% 2.14/0.67  fof(f4185,plain,(
% 2.14/0.67    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl3_11 | ~spl3_12 | ~spl3_26 | spl3_109)),
% 2.14/0.67    inference(subsumption_resolution,[],[f3546,f4132])).
% 2.14/0.67  fof(f4132,plain,(
% 2.14/0.67    r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | (~spl3_11 | ~spl3_26)),
% 2.14/0.67    inference(trivial_inequality_removal,[],[f542])).
% 2.14/0.67  fof(f542,plain,(
% 2.14/0.67    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | (~spl3_11 | ~spl3_26)),
% 2.14/0.67    inference(superposition,[],[f98,f305])).
% 2.14/0.67  fof(f305,plain,(
% 2.14/0.67    k1_xboole_0 = k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) | ~spl3_26),
% 2.14/0.67    inference(avatar_component_clause,[],[f303])).
% 2.14/0.67  fof(f303,plain,(
% 2.14/0.67    spl3_26 <=> k1_xboole_0 = k4_xboole_0(sK0,k5_xboole_0(sK1,sK2))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 2.14/0.67  fof(f98,plain,(
% 2.14/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) ) | ~spl3_11),
% 2.14/0.67    inference(avatar_component_clause,[],[f97])).
% 2.14/0.67  fof(f97,plain,(
% 2.14/0.67    spl3_11 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 2.14/0.67  fof(f3546,plain,(
% 2.14/0.67    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | (~spl3_12 | spl3_109)),
% 2.14/0.67    inference(superposition,[],[f3537,f102])).
% 2.14/0.67  fof(f102,plain,(
% 2.14/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) ) | ~spl3_12),
% 2.14/0.67    inference(avatar_component_clause,[],[f101])).
% 2.14/0.67  fof(f101,plain,(
% 2.14/0.67    spl3_12 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 2.14/0.67  fof(f3537,plain,(
% 2.14/0.67    ~r1_tarski(k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k1_xboole_0) | spl3_109),
% 2.14/0.67    inference(avatar_component_clause,[],[f3535])).
% 2.14/0.67  fof(f396,plain,(
% 2.14/0.67    r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl3_31),
% 2.14/0.67    inference(avatar_component_clause,[],[f394])).
% 2.14/0.67  fof(f394,plain,(
% 2.14/0.67    spl3_31 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 2.14/0.67  fof(f4079,plain,(
% 2.14/0.67    ~spl3_25 | spl3_26 | ~spl3_71 | ~spl3_125),
% 2.14/0.67    inference(avatar_contradiction_clause,[],[f4078])).
% 2.14/0.67  fof(f4078,plain,(
% 2.14/0.67    $false | (~spl3_25 | spl3_26 | ~spl3_71 | ~spl3_125)),
% 2.14/0.67    inference(subsumption_resolution,[],[f304,f4077])).
% 2.14/0.67  fof(f4077,plain,(
% 2.14/0.67    k1_xboole_0 = k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) | (~spl3_25 | ~spl3_71 | ~spl3_125)),
% 2.14/0.67    inference(forward_demodulation,[],[f4024,f289])).
% 2.14/0.67  fof(f289,plain,(
% 2.14/0.67    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_25),
% 2.14/0.67    inference(avatar_component_clause,[],[f287])).
% 2.14/0.67  fof(f304,plain,(
% 2.14/0.67    k1_xboole_0 != k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) | spl3_26),
% 2.14/0.67    inference(avatar_component_clause,[],[f303])).
% 2.14/0.67  fof(f4020,plain,(
% 2.14/0.67    spl3_125 | ~spl3_24 | ~spl3_59 | ~spl3_84),
% 2.14/0.67    inference(avatar_split_clause,[],[f1856,f1802,f951,f278,f4018])).
% 2.14/0.67  fof(f278,plain,(
% 2.14/0.67    spl3_24 <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 2.14/0.67  fof(f951,plain,(
% 2.14/0.67    spl3_59 <=> ! [X9,X10] : k4_xboole_0(X9,k2_xboole_0(k1_xboole_0,X10)) = k4_xboole_0(X9,X10)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 2.14/0.67  fof(f1802,plain,(
% 2.14/0.67    spl3_84 <=> ! [X3,X5,X4] : k4_xboole_0(X3,k2_xboole_0(k3_xboole_0(X3,X4),X5)) = k4_xboole_0(X3,k2_xboole_0(X4,X5))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).
% 2.14/0.67  fof(f1856,plain,(
% 2.14/0.67    ( ! [X27] : (k4_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),X27)) = k4_xboole_0(sK0,X27)) ) | (~spl3_24 | ~spl3_59 | ~spl3_84)),
% 2.14/0.67    inference(forward_demodulation,[],[f1812,f952])).
% 2.14/0.67  fof(f952,plain,(
% 2.14/0.67    ( ! [X10,X9] : (k4_xboole_0(X9,k2_xboole_0(k1_xboole_0,X10)) = k4_xboole_0(X9,X10)) ) | ~spl3_59),
% 2.14/0.67    inference(avatar_component_clause,[],[f951])).
% 2.14/0.67  fof(f1812,plain,(
% 2.14/0.67    ( ! [X27] : (k4_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),X27)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X27))) ) | (~spl3_24 | ~spl3_84)),
% 2.14/0.67    inference(superposition,[],[f1803,f279])).
% 2.14/0.67  fof(f279,plain,(
% 2.14/0.67    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_24),
% 2.14/0.67    inference(avatar_component_clause,[],[f278])).
% 2.14/0.67  fof(f1803,plain,(
% 2.14/0.67    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k2_xboole_0(k3_xboole_0(X3,X4),X5)) = k4_xboole_0(X3,k2_xboole_0(X4,X5))) ) | ~spl3_84),
% 2.14/0.67    inference(avatar_component_clause,[],[f1802])).
% 2.14/0.67  fof(f3513,plain,(
% 2.14/0.67    ~spl3_1 | ~spl3_12 | spl3_26),
% 2.14/0.67    inference(avatar_split_clause,[],[f3317,f303,f101,f48])).
% 2.14/0.67  fof(f48,plain,(
% 2.14/0.67    spl3_1 <=> r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.14/0.67  fof(f3317,plain,(
% 2.14/0.67    ~r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | (~spl3_12 | spl3_26)),
% 2.14/0.67    inference(trivial_inequality_removal,[],[f427])).
% 2.14/0.67  fof(f427,plain,(
% 2.14/0.67    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | (~spl3_12 | spl3_26)),
% 2.14/0.67    inference(superposition,[],[f304,f102])).
% 2.14/0.67  fof(f3501,plain,(
% 2.14/0.67    spl3_2 | ~spl3_11 | ~spl3_25),
% 2.14/0.67    inference(avatar_split_clause,[],[f3315,f287,f97,f52])).
% 2.14/0.67  fof(f52,plain,(
% 2.14/0.67    spl3_2 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.14/0.67  fof(f3315,plain,(
% 2.14/0.67    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | (~spl3_11 | ~spl3_25)),
% 2.14/0.67    inference(trivial_inequality_removal,[],[f417])).
% 2.14/0.67  fof(f417,plain,(
% 2.14/0.67    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | (~spl3_11 | ~spl3_25)),
% 2.14/0.67    inference(superposition,[],[f98,f289])).
% 2.14/0.67  fof(f1892,plain,(
% 2.14/0.67    spl3_3 | ~spl3_10 | ~spl3_24),
% 2.14/0.67    inference(avatar_split_clause,[],[f351,f278,f93,f60])).
% 2.14/0.67  fof(f60,plain,(
% 2.14/0.67    spl3_3 <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.14/0.67  fof(f93,plain,(
% 2.14/0.67    spl3_10 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.14/0.67  fof(f351,plain,(
% 2.14/0.67    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | (~spl3_10 | ~spl3_24)),
% 2.14/0.67    inference(trivial_inequality_removal,[],[f347])).
% 2.14/0.67  fof(f347,plain,(
% 2.14/0.67    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | (~spl3_10 | ~spl3_24)),
% 2.14/0.67    inference(superposition,[],[f94,f279])).
% 2.14/0.67  fof(f94,plain,(
% 2.14/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) ) | ~spl3_10),
% 2.14/0.67    inference(avatar_component_clause,[],[f93])).
% 2.14/0.67  fof(f1804,plain,(
% 2.14/0.67    spl3_84 | ~spl3_17 | ~spl3_23),
% 2.14/0.67    inference(avatar_split_clause,[],[f255,f205,f123,f1802])).
% 2.14/0.67  fof(f123,plain,(
% 2.14/0.67    spl3_17 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 2.14/0.67  fof(f205,plain,(
% 2.14/0.67    spl3_23 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 2.14/0.67  fof(f255,plain,(
% 2.14/0.67    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k2_xboole_0(k3_xboole_0(X3,X4),X5)) = k4_xboole_0(X3,k2_xboole_0(X4,X5))) ) | (~spl3_17 | ~spl3_23)),
% 2.14/0.67    inference(forward_demodulation,[],[f237,f206])).
% 2.14/0.67  fof(f206,plain,(
% 2.14/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl3_23),
% 2.14/0.67    inference(avatar_component_clause,[],[f205])).
% 2.14/0.67  fof(f237,plain,(
% 2.14/0.67    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k2_xboole_0(k3_xboole_0(X3,X4),X5)) = k4_xboole_0(k4_xboole_0(X3,X4),X5)) ) | (~spl3_17 | ~spl3_23)),
% 2.14/0.67    inference(superposition,[],[f206,f124])).
% 2.14/0.67  fof(f124,plain,(
% 2.14/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl3_17),
% 2.14/0.67    inference(avatar_component_clause,[],[f123])).
% 2.14/0.67  fof(f1581,plain,(
% 2.14/0.67    ~spl3_47 | ~spl3_48 | spl3_78),
% 2.14/0.67    inference(avatar_contradiction_clause,[],[f1573])).
% 2.14/0.67  fof(f1573,plain,(
% 2.14/0.67    $false | (~spl3_47 | ~spl3_48 | spl3_78)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f679,f1570,f663])).
% 2.14/0.67  fof(f663,plain,(
% 2.14/0.67    ( ! [X2,X3] : (k1_xboole_0 != k3_xboole_0(X3,X2) | r1_xboole_0(X2,X3)) ) | ~spl3_47),
% 2.14/0.67    inference(avatar_component_clause,[],[f662])).
% 2.14/0.67  fof(f662,plain,(
% 2.14/0.67    spl3_47 <=> ! [X3,X2] : (k1_xboole_0 != k3_xboole_0(X3,X2) | r1_xboole_0(X2,X3))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 2.14/0.67  fof(f1570,plain,(
% 2.14/0.67    ~r1_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) | spl3_78),
% 2.14/0.67    inference(avatar_component_clause,[],[f1568])).
% 2.14/0.67  fof(f1568,plain,(
% 2.14/0.67    spl3_78 <=> r1_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).
% 2.14/0.67  fof(f679,plain,(
% 2.14/0.67    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) ) | ~spl3_48),
% 2.14/0.67    inference(avatar_component_clause,[],[f678])).
% 2.14/0.67  fof(f678,plain,(
% 2.14/0.67    spl3_48 <=> ! [X1,X0] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 2.14/0.67  fof(f1571,plain,(
% 2.14/0.67    ~spl3_78 | ~spl3_1 | spl3_3 | ~spl3_18),
% 2.14/0.67    inference(avatar_split_clause,[],[f191,f127,f60,f48,f1568])).
% 2.14/0.67  fof(f127,plain,(
% 2.14/0.67    spl3_18 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 2.14/0.67  fof(f191,plain,(
% 2.14/0.67    ~r1_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) | (~spl3_1 | spl3_3 | ~spl3_18)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f61,f50,f128])).
% 2.14/0.67  fof(f128,plain,(
% 2.14/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) ) | ~spl3_18),
% 2.14/0.67    inference(avatar_component_clause,[],[f127])).
% 2.14/0.67  fof(f50,plain,(
% 2.14/0.67    r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | ~spl3_1),
% 2.14/0.67    inference(avatar_component_clause,[],[f48])).
% 2.14/0.67  fof(f61,plain,(
% 2.14/0.67    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | spl3_3),
% 2.14/0.67    inference(avatar_component_clause,[],[f60])).
% 2.14/0.67  fof(f1380,plain,(
% 2.14/0.67    spl3_71 | ~spl3_6 | ~spl3_22),
% 2.14/0.67    inference(avatar_split_clause,[],[f230,f201,f77,f1378])).
% 2.14/0.67  fof(f77,plain,(
% 2.14/0.67    spl3_6 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.14/0.67  fof(f201,plain,(
% 2.14/0.67    spl3_22 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 2.14/0.67  fof(f230,plain,(
% 2.14/0.67    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))) ) | (~spl3_6 | ~spl3_22)),
% 2.14/0.67    inference(superposition,[],[f202,f78])).
% 2.14/0.67  fof(f78,plain,(
% 2.14/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_6),
% 2.14/0.67    inference(avatar_component_clause,[],[f77])).
% 2.14/0.67  fof(f202,plain,(
% 2.14/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ) | ~spl3_22),
% 2.14/0.67    inference(avatar_component_clause,[],[f201])).
% 2.14/0.67  fof(f1050,plain,(
% 2.14/0.67    spl3_1 | ~spl3_11 | ~spl3_26),
% 2.14/0.67    inference(avatar_split_clause,[],[f528,f303,f97,f48])).
% 2.14/0.67  fof(f528,plain,(
% 2.14/0.67    r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | (~spl3_11 | ~spl3_26)),
% 2.14/0.67    inference(trivial_inequality_removal,[],[f377])).
% 2.14/0.67  fof(f377,plain,(
% 2.14/0.67    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | (~spl3_11 | ~spl3_26)),
% 2.14/0.67    inference(superposition,[],[f98,f305])).
% 2.14/0.67  fof(f953,plain,(
% 2.14/0.67    spl3_59 | ~spl3_4 | ~spl3_23),
% 2.14/0.67    inference(avatar_split_clause,[],[f239,f205,f68,f951])).
% 2.14/0.67  fof(f68,plain,(
% 2.14/0.67    spl3_4 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.14/0.67  fof(f239,plain,(
% 2.14/0.67    ( ! [X10,X9] : (k4_xboole_0(X9,k2_xboole_0(k1_xboole_0,X10)) = k4_xboole_0(X9,X10)) ) | (~spl3_4 | ~spl3_23)),
% 2.14/0.67    inference(superposition,[],[f206,f69])).
% 2.14/0.67  fof(f69,plain,(
% 2.14/0.67    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_4),
% 2.14/0.67    inference(avatar_component_clause,[],[f68])).
% 2.14/0.67  fof(f948,plain,(
% 2.14/0.67    ~spl3_2 | ~spl3_12 | spl3_25),
% 2.14/0.67    inference(avatar_split_clause,[],[f374,f287,f101,f52])).
% 2.14/0.67  fof(f374,plain,(
% 2.14/0.67    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | (~spl3_12 | spl3_25)),
% 2.14/0.67    inference(trivial_inequality_removal,[],[f373])).
% 2.14/0.67  fof(f373,plain,(
% 2.14/0.67    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | (~spl3_12 | spl3_25)),
% 2.14/0.67    inference(superposition,[],[f288,f102])).
% 2.14/0.67  fof(f680,plain,(
% 2.14/0.67    spl3_48 | ~spl3_8 | ~spl3_9),
% 2.14/0.67    inference(avatar_split_clause,[],[f131,f89,f85,f678])).
% 2.14/0.67  fof(f85,plain,(
% 2.14/0.67    spl3_8 <=> ! [X1,X0] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 2.14/0.67  fof(f89,plain,(
% 2.14/0.67    spl3_9 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.14/0.67  fof(f131,plain,(
% 2.14/0.67    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) ) | (~spl3_8 | ~spl3_9)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f86,f90])).
% 2.14/0.67  fof(f90,plain,(
% 2.14/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) ) | ~spl3_9),
% 2.14/0.67    inference(avatar_component_clause,[],[f89])).
% 2.14/0.67  fof(f86,plain,(
% 2.14/0.67    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) ) | ~spl3_8),
% 2.14/0.67    inference(avatar_component_clause,[],[f85])).
% 2.14/0.67  fof(f664,plain,(
% 2.14/0.67    spl3_47 | ~spl3_7 | ~spl3_10),
% 2.14/0.67    inference(avatar_split_clause,[],[f149,f93,f81,f662])).
% 2.14/0.67  fof(f81,plain,(
% 2.14/0.67    spl3_7 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.14/0.67  fof(f149,plain,(
% 2.14/0.67    ( ! [X2,X3] : (k1_xboole_0 != k3_xboole_0(X3,X2) | r1_xboole_0(X2,X3)) ) | (~spl3_7 | ~spl3_10)),
% 2.14/0.67    inference(superposition,[],[f94,f82])).
% 2.14/0.67  fof(f82,plain,(
% 2.14/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_7),
% 2.14/0.67    inference(avatar_component_clause,[],[f81])).
% 2.14/0.67  fof(f441,plain,(
% 2.14/0.67    spl3_34 | ~spl3_4 | ~spl3_12),
% 2.14/0.67    inference(avatar_split_clause,[],[f155,f101,f68,f439])).
% 2.14/0.67  fof(f155,plain,(
% 2.14/0.67    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) ) | (~spl3_4 | ~spl3_12)),
% 2.14/0.67    inference(superposition,[],[f102,f69])).
% 2.14/0.67  fof(f397,plain,(
% 2.14/0.67    spl3_31 | ~spl3_4 | ~spl3_11),
% 2.14/0.67    inference(avatar_split_clause,[],[f151,f97,f68,f394])).
% 2.14/0.67  fof(f151,plain,(
% 2.14/0.67    r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl3_4 | ~spl3_11)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f69,f98])).
% 2.14/0.67  fof(f336,plain,(
% 2.14/0.67    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 2.14/0.67    inference(avatar_contradiction_clause,[],[f335])).
% 2.14/0.67  fof(f335,plain,(
% 2.14/0.67    $false | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 2.14/0.67    inference(subsumption_resolution,[],[f50,f334])).
% 2.14/0.67  fof(f334,plain,(
% 2.14/0.67    ~r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | (~spl3_2 | ~spl3_3)),
% 2.14/0.67    inference(subsumption_resolution,[],[f56,f62])).
% 2.14/0.67  fof(f62,plain,(
% 2.14/0.67    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_3),
% 2.14/0.67    inference(avatar_component_clause,[],[f60])).
% 2.14/0.67  fof(f56,plain,(
% 2.14/0.67    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | ~spl3_2),
% 2.14/0.67    inference(subsumption_resolution,[],[f29,f54])).
% 2.14/0.67  fof(f54,plain,(
% 2.14/0.67    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_2),
% 2.14/0.67    inference(avatar_component_clause,[],[f52])).
% 2.14/0.67  fof(f29,plain,(
% 2.14/0.67    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 2.14/0.67    inference(cnf_transformation,[],[f24])).
% 2.14/0.67  fof(f24,plain,(
% 2.14/0.67    (~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))) & ((r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))) | r1_tarski(sK0,k5_xboole_0(sK1,sK2)))),
% 2.14/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).
% 2.14/0.67  fof(f23,plain,(
% 2.14/0.67    ? [X0,X1,X2] : ((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2)))) => ((~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))) & ((r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))))),
% 2.14/0.67    introduced(choice_axiom,[])).
% 2.14/0.67  fof(f22,plain,(
% 2.14/0.67    ? [X0,X1,X2] : ((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 2.14/0.67    inference(flattening,[],[f21])).
% 2.14/0.67  fof(f21,plain,(
% 2.14/0.67    ? [X0,X1,X2] : (((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 2.14/0.67    inference(nnf_transformation,[],[f18])).
% 2.14/0.67  fof(f18,plain,(
% 2.14/0.67    ? [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <~> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 2.14/0.67    inference(ennf_transformation,[],[f17])).
% 2.14/0.67  fof(f17,negated_conjecture,(
% 2.14/0.67    ~! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 2.14/0.67    inference(negated_conjecture,[],[f16])).
% 2.14/0.67  fof(f16,conjecture,(
% 2.14/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).
% 2.14/0.67  fof(f311,plain,(
% 2.14/0.67    spl3_1 | ~spl3_9 | spl3_24),
% 2.14/0.67    inference(avatar_split_clause,[],[f310,f278,f89,f48])).
% 2.14/0.67  fof(f310,plain,(
% 2.14/0.67    r1_tarski(sK0,k5_xboole_0(sK1,sK2)) | (~spl3_9 | spl3_24)),
% 2.14/0.67    inference(subsumption_resolution,[],[f28,f285])).
% 2.14/0.67  fof(f285,plain,(
% 2.14/0.67    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | (~spl3_9 | spl3_24)),
% 2.14/0.67    inference(trivial_inequality_removal,[],[f284])).
% 2.14/0.67  fof(f284,plain,(
% 2.14/0.67    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | (~spl3_9 | spl3_24)),
% 2.14/0.67    inference(superposition,[],[f280,f90])).
% 2.14/0.67  fof(f280,plain,(
% 2.14/0.67    k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | spl3_24),
% 2.14/0.67    inference(avatar_component_clause,[],[f278])).
% 2.14/0.67  fof(f28,plain,(
% 2.14/0.67    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 2.14/0.67    inference(cnf_transformation,[],[f24])).
% 2.14/0.67  fof(f308,plain,(
% 2.14/0.67    ~spl3_3 | ~spl3_9 | spl3_24),
% 2.14/0.67    inference(avatar_contradiction_clause,[],[f307])).
% 2.14/0.67  fof(f307,plain,(
% 2.14/0.67    $false | (~spl3_3 | ~spl3_9 | spl3_24)),
% 2.14/0.67    inference(subsumption_resolution,[],[f285,f62])).
% 2.14/0.67  fof(f207,plain,(
% 2.14/0.67    spl3_23),
% 2.14/0.67    inference(avatar_split_clause,[],[f45,f205])).
% 2.14/0.67  fof(f45,plain,(
% 2.14/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.14/0.67    inference(cnf_transformation,[],[f9])).
% 2.14/0.67  fof(f9,axiom,(
% 2.14/0.67    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.14/0.67  fof(f203,plain,(
% 2.14/0.67    spl3_22),
% 2.14/0.67    inference(avatar_split_clause,[],[f40,f201])).
% 2.14/0.67  fof(f40,plain,(
% 2.14/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.14/0.67    inference(cnf_transformation,[],[f14])).
% 2.14/0.67  fof(f14,axiom,(
% 2.14/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 2.14/0.67  fof(f129,plain,(
% 2.14/0.67    spl3_18),
% 2.14/0.67    inference(avatar_split_clause,[],[f46,f127])).
% 2.14/0.67  fof(f46,plain,(
% 2.14/0.67    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f20])).
% 2.14/0.67  fof(f20,plain,(
% 2.14/0.67    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.14/0.67    inference(flattening,[],[f19])).
% 2.14/0.67  fof(f19,plain,(
% 2.14/0.67    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.14/0.67    inference(ennf_transformation,[],[f12])).
% 2.14/0.67  fof(f12,axiom,(
% 2.14/0.67    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 2.14/0.67  fof(f125,plain,(
% 2.14/0.67    spl3_17),
% 2.14/0.67    inference(avatar_split_clause,[],[f38,f123])).
% 2.14/0.67  fof(f38,plain,(
% 2.14/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.14/0.67    inference(cnf_transformation,[],[f10])).
% 2.14/0.67  fof(f10,axiom,(
% 2.14/0.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.14/0.67  fof(f103,plain,(
% 2.14/0.67    spl3_12),
% 2.14/0.67    inference(avatar_split_clause,[],[f44,f101])).
% 2.14/0.67  fof(f44,plain,(
% 2.14/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f26])).
% 2.14/0.67  fof(f26,plain,(
% 2.14/0.67    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.14/0.67    inference(nnf_transformation,[],[f5])).
% 2.14/0.67  fof(f5,axiom,(
% 2.14/0.67    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.14/0.67  fof(f99,plain,(
% 2.14/0.67    spl3_11),
% 2.14/0.67    inference(avatar_split_clause,[],[f43,f97])).
% 2.14/0.67  fof(f43,plain,(
% 2.14/0.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.14/0.67    inference(cnf_transformation,[],[f26])).
% 2.14/0.67  fof(f95,plain,(
% 2.14/0.67    spl3_10),
% 2.14/0.67    inference(avatar_split_clause,[],[f42,f93])).
% 2.14/0.67  fof(f42,plain,(
% 2.14/0.67    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.14/0.67    inference(cnf_transformation,[],[f25])).
% 2.14/0.67  fof(f25,plain,(
% 2.14/0.67    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.14/0.67    inference(nnf_transformation,[],[f4])).
% 2.14/0.67  fof(f4,axiom,(
% 2.14/0.67    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.14/0.67  fof(f91,plain,(
% 2.14/0.67    spl3_9),
% 2.14/0.67    inference(avatar_split_clause,[],[f41,f89])).
% 2.14/0.67  fof(f41,plain,(
% 2.14/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f25])).
% 2.14/0.67  fof(f87,plain,(
% 2.14/0.67    spl3_8),
% 2.14/0.67    inference(avatar_split_clause,[],[f34,f85])).
% 2.14/0.67  fof(f34,plain,(
% 2.14/0.67    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 2.14/0.67    inference(cnf_transformation,[],[f6])).
% 2.14/0.67  fof(f6,axiom,(
% 2.14/0.67    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 2.14/0.67  fof(f83,plain,(
% 2.14/0.67    spl3_7),
% 2.14/0.67    inference(avatar_split_clause,[],[f33,f81])).
% 2.14/0.67  fof(f33,plain,(
% 2.14/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f2])).
% 2.14/0.67  fof(f2,axiom,(
% 2.14/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.14/0.67  fof(f79,plain,(
% 2.14/0.67    spl3_6),
% 2.14/0.67    inference(avatar_split_clause,[],[f32,f77])).
% 2.14/0.67  fof(f32,plain,(
% 2.14/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f1])).
% 2.14/0.67  fof(f1,axiom,(
% 2.14/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.14/0.67  fof(f70,plain,(
% 2.14/0.67    spl3_4),
% 2.14/0.67    inference(avatar_split_clause,[],[f30,f68])).
% 2.14/0.67  fof(f30,plain,(
% 2.14/0.67    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.14/0.67    inference(cnf_transformation,[],[f8])).
% 2.14/0.67  fof(f8,axiom,(
% 2.14/0.67    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.14/0.67  fof(f55,plain,(
% 2.14/0.67    spl3_1 | spl3_2),
% 2.14/0.67    inference(avatar_split_clause,[],[f27,f52,f48])).
% 2.14/0.67  fof(f27,plain,(
% 2.14/0.67    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 2.14/0.67    inference(cnf_transformation,[],[f24])).
% 2.14/0.67  % SZS output end Proof for theBenchmark
% 2.14/0.67  % (16650)------------------------------
% 2.14/0.67  % (16650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.67  % (16650)Termination reason: Refutation
% 2.14/0.67  
% 2.14/0.67  % (16650)Memory used [KB]: 9083
% 2.14/0.67  % (16650)Time elapsed: 0.251 s
% 2.14/0.67  % (16650)------------------------------
% 2.14/0.67  % (16650)------------------------------
% 2.14/0.68  % (16644)Success in time 0.314 s
%------------------------------------------------------------------------------
