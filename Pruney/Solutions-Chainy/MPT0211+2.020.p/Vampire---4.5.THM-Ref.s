%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 236 expanded)
%              Number of leaves         :   35 ( 120 expanded)
%              Depth                    :    6
%              Number of atoms          :  293 ( 514 expanded)
%              Number of equality atoms :  101 ( 210 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1549,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f53,f61,f73,f85,f129,f133,f137,f141,f157,f161,f190,f279,f284,f297,f305,f459,f625,f629,f747,f1023,f1304,f1510,f1524,f1538])).

fof(f1538,plain,
    ( ~ spl3_38
    | ~ spl3_48
    | spl3_75
    | ~ spl3_82
    | ~ spl3_83 ),
    inference(avatar_contradiction_clause,[],[f1537])).

fof(f1537,plain,
    ( $false
    | ~ spl3_38
    | ~ spl3_48
    | spl3_75
    | ~ spl3_82
    | ~ spl3_83 ),
    inference(subsumption_resolution,[],[f1518,f1536])).

fof(f1536,plain,
    ( ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k2_enumset1(X3,X4,X3,X5)
    | ~ spl3_38
    | ~ spl3_48
    | ~ spl3_83 ),
    inference(forward_demodulation,[],[f1525,f624])).

fof(f624,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f623])).

fof(f623,plain,
    ( spl3_48
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f1525,plain,
    ( ! [X4,X5,X3] : k2_enumset1(X3,X4,X3,X5) = k2_enumset1(X3,X4,X5,X5)
    | ~ spl3_38
    | ~ spl3_83 ),
    inference(superposition,[],[f1523,f458])).

fof(f458,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3)
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f457])).

fof(f457,plain,
    ( spl3_38
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f1523,plain,
    ( ! [X47,X45,X46,X44] : k2_enumset1(X44,X45,X46,X47) = k3_enumset1(X44,X45,X44,X46,X47)
    | ~ spl3_83 ),
    inference(avatar_component_clause,[],[f1522])).

fof(f1522,plain,
    ( spl3_83
  <=> ! [X44,X46,X45,X47] : k2_enumset1(X44,X45,X46,X47) = k3_enumset1(X44,X45,X44,X46,X47) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).

fof(f1518,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK0,sK2)
    | spl3_75
    | ~ spl3_82 ),
    inference(superposition,[],[f1303,f1509])).

fof(f1509,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl3_82 ),
    inference(avatar_component_clause,[],[f1508])).

fof(f1508,plain,
    ( spl3_82
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).

fof(f1303,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2))
    | spl3_75 ),
    inference(avatar_component_clause,[],[f1301])).

fof(f1301,plain,
    ( spl3_75
  <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f1524,plain,
    ( spl3_83
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f643,f627,f131,f127,f59,f1522])).

fof(f59,plain,
    ( spl3_4
  <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f127,plain,
    ( spl3_11
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f131,plain,
    ( spl3_12
  <=> ! [X1,X3,X0,X2] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f627,plain,
    ( spl3_49
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f643,plain,
    ( ! [X47,X45,X46,X44] : k2_enumset1(X44,X45,X46,X47) = k3_enumset1(X44,X45,X44,X46,X47)
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_49 ),
    inference(forward_demodulation,[],[f639,f642])).

fof(f642,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_49 ),
    inference(forward_demodulation,[],[f630,f132])).

fof(f132,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f131])).

fof(f630,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl3_4
    | ~ spl3_49 ),
    inference(superposition,[],[f628,f60])).

fof(f60,plain,
    ( ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f628,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f627])).

fof(f639,plain,
    ( ! [X47,X45,X46,X44] : k3_enumset1(X44,X45,X44,X46,X47) = k2_xboole_0(k2_tarski(X44,X45),k2_tarski(X46,X47))
    | ~ spl3_11
    | ~ spl3_49 ),
    inference(superposition,[],[f628,f128])).

fof(f128,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f127])).

fof(f1510,plain,
    ( spl3_82
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f642,f627,f131,f59,f1508])).

fof(f1304,plain,
    ( ~ spl3_75
    | spl3_1
    | ~ spl3_66 ),
    inference(avatar_split_clause,[],[f1206,f1021,f46,f1301])).

fof(f46,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1021,plain,
    ( spl3_66
  <=> ! [X3,X2] : k2_tarski(X2,X3) = k2_tarski(X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f1206,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2))
    | spl3_1
    | ~ spl3_66 ),
    inference(forward_demodulation,[],[f1194,f1022])).

fof(f1022,plain,
    ( ! [X2,X3] : k2_tarski(X2,X3) = k2_tarski(X3,X2)
    | ~ spl3_66 ),
    inference(avatar_component_clause,[],[f1021])).

fof(f1194,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK0))
    | spl3_1
    | ~ spl3_66 ),
    inference(superposition,[],[f48,f1022])).

fof(f48,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f1023,plain,
    ( spl3_66
    | ~ spl3_4
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f856,f745,f59,f1021])).

fof(f745,plain,
    ( spl3_57
  <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f856,plain,
    ( ! [X2,X3] : k2_tarski(X2,X3) = k2_tarski(X3,X2)
    | ~ spl3_4
    | ~ spl3_57 ),
    inference(superposition,[],[f746,f60])).

fof(f746,plain,
    ( ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X1,X0)
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f745])).

fof(f747,plain,
    ( spl3_57
    | ~ spl3_10
    | ~ spl3_20
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f676,f623,f188,f83,f745])).

fof(f83,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f188,plain,
    ( spl3_20
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f676,plain,
    ( ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X1,X0)
    | ~ spl3_10
    | ~ spl3_20
    | ~ spl3_48 ),
    inference(forward_demodulation,[],[f668,f189])).

fof(f189,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f188])).

fof(f668,plain,
    ( ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X0,X1,X1)
    | ~ spl3_10
    | ~ spl3_48 ),
    inference(superposition,[],[f624,f84])).

fof(f84,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f83])).

fof(f629,plain,
    ( spl3_49
    | ~ spl3_10
    | ~ spl3_13
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f287,f282,f135,f83,f627])).

fof(f135,plain,
    ( spl3_13
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f282,plain,
    ( spl3_26
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f287,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))
    | ~ spl3_10
    | ~ spl3_13
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f285,f136])).

fof(f136,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f135])).

fof(f285,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))
    | ~ spl3_10
    | ~ spl3_26 ),
    inference(superposition,[],[f283,f84])).

fof(f283,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f282])).

fof(f625,plain,
    ( spl3_48
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f503,f457,f131,f83,f623])).

fof(f503,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f493,f84])).

fof(f493,plain,
    ( ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)
    | ~ spl3_12
    | ~ spl3_38 ),
    inference(superposition,[],[f458,f132])).

fof(f459,plain,
    ( spl3_38
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f369,f303,f135,f131,f457])).

fof(f303,plain,
    ( spl3_29
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f369,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3)
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f364,f132])).

fof(f364,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3)
    | ~ spl3_13
    | ~ spl3_29 ),
    inference(superposition,[],[f304,f136])).

fof(f304,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f303])).

fof(f305,plain,
    ( spl3_29
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f300,f295,f139,f135,f303])).

fof(f139,plain,
    ( spl3_14
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f295,plain,
    ( spl3_28
  <=> ! [X1,X3,X5,X0,X2,X4] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X5,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f300,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f298,f136])).

fof(f298,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)
    | ~ spl3_14
    | ~ spl3_28 ),
    inference(superposition,[],[f296,f140])).

fof(f140,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f139])).

fof(f296,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X5,X0)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f295])).

fof(f297,plain,
    ( spl3_28
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_17
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f280,f277,f159,f139,f135,f295])).

fof(f159,plain,
    ( spl3_17
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f277,plain,
    ( spl3_25
  <=> ! [X1,X3,X5,X0,X2,X4] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f280,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X5,X0)
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_17
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f278,f166])).

fof(f166,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f165,f140])).

fof(f165,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(superposition,[],[f160,f136])).

fof(f160,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f159])).

fof(f278,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f277])).

fof(f284,plain,
    ( spl3_26
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f164,f155,f139,f131,f282])).

fof(f155,plain,
    ( spl3_16
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f164,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f162,f140])).

fof(f162,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(superposition,[],[f156,f132])).

fof(f156,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f155])).

fof(f279,plain,
    ( spl3_25
    | ~ spl3_2
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f163,f155,f51,f277])).

fof(f51,plain,
    ( spl3_2
  <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f163,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))
    | ~ spl3_2
    | ~ spl3_16 ),
    inference(superposition,[],[f156,f52])).

fof(f52,plain,
    ( ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f190,plain,
    ( spl3_20
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f90,f71,f59,f188])).

fof(f71,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f90,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(superposition,[],[f72,f60])).

fof(f72,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f161,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f40,f159])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

fof(f157,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f39,f155])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

fof(f141,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f37,f139])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f137,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f36,f135])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f133,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f35,f131])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f129,plain,
    ( spl3_11
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f88,f71,f59,f127])).

fof(f88,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(superposition,[],[f72,f60])).

fof(f85,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f34,f83])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f73,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f31,f71])).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

fof(f61,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f28,f59])).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f53,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f26,f51])).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f25,f46])).

fof(f25,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:53:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (19159)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (19163)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (19161)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (19173)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (19175)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (19165)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (19167)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (19171)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (19168)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (19169)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (19169)Refutation not found, incomplete strategy% (19169)------------------------------
% 0.21/0.49  % (19169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19169)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (19169)Memory used [KB]: 10618
% 0.21/0.49  % (19169)Time elapsed: 0.069 s
% 0.21/0.49  % (19169)------------------------------
% 0.21/0.49  % (19169)------------------------------
% 0.21/0.50  % (19170)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (19160)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (19164)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (19174)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (19166)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (19162)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (19172)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.52  % (19158)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.53  % (19163)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f1549,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f49,f53,f61,f73,f85,f129,f133,f137,f141,f157,f161,f190,f279,f284,f297,f305,f459,f625,f629,f747,f1023,f1304,f1510,f1524,f1538])).
% 0.21/0.53  fof(f1538,plain,(
% 0.21/0.53    ~spl3_38 | ~spl3_48 | spl3_75 | ~spl3_82 | ~spl3_83),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f1537])).
% 0.21/0.53  fof(f1537,plain,(
% 0.21/0.53    $false | (~spl3_38 | ~spl3_48 | spl3_75 | ~spl3_82 | ~spl3_83)),
% 0.21/0.53    inference(subsumption_resolution,[],[f1518,f1536])).
% 0.21/0.53  fof(f1536,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k2_enumset1(X3,X4,X3,X5)) ) | (~spl3_38 | ~spl3_48 | ~spl3_83)),
% 0.21/0.53    inference(forward_demodulation,[],[f1525,f624])).
% 0.21/0.53  fof(f624,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)) ) | ~spl3_48),
% 0.21/0.53    inference(avatar_component_clause,[],[f623])).
% 0.21/0.53  fof(f623,plain,(
% 0.21/0.53    spl3_48 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.21/0.53  fof(f1525,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (k2_enumset1(X3,X4,X3,X5) = k2_enumset1(X3,X4,X5,X5)) ) | (~spl3_38 | ~spl3_83)),
% 0.21/0.53    inference(superposition,[],[f1523,f458])).
% 0.21/0.53  fof(f458,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3)) ) | ~spl3_38),
% 0.21/0.53    inference(avatar_component_clause,[],[f457])).
% 0.21/0.53  fof(f457,plain,(
% 0.21/0.53    spl3_38 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.53  fof(f1523,plain,(
% 0.21/0.53    ( ! [X47,X45,X46,X44] : (k2_enumset1(X44,X45,X46,X47) = k3_enumset1(X44,X45,X44,X46,X47)) ) | ~spl3_83),
% 0.21/0.53    inference(avatar_component_clause,[],[f1522])).
% 0.21/0.53  fof(f1522,plain,(
% 0.21/0.53    spl3_83 <=> ! [X44,X46,X45,X47] : k2_enumset1(X44,X45,X46,X47) = k3_enumset1(X44,X45,X44,X46,X47)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).
% 0.21/0.53  fof(f1518,plain,(
% 0.21/0.53    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK0,sK2) | (spl3_75 | ~spl3_82)),
% 0.21/0.53    inference(superposition,[],[f1303,f1509])).
% 0.21/0.53  fof(f1509,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | ~spl3_82),
% 0.21/0.53    inference(avatar_component_clause,[],[f1508])).
% 0.21/0.53  fof(f1508,plain,(
% 0.21/0.53    spl3_82 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).
% 0.21/0.53  fof(f1303,plain,(
% 0.21/0.53    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2)) | spl3_75),
% 0.21/0.53    inference(avatar_component_clause,[],[f1301])).
% 0.21/0.53  fof(f1301,plain,(
% 0.21/0.53    spl3_75 <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 0.21/0.53  fof(f1524,plain,(
% 0.21/0.53    spl3_83 | ~spl3_4 | ~spl3_11 | ~spl3_12 | ~spl3_49),
% 0.21/0.53    inference(avatar_split_clause,[],[f643,f627,f131,f127,f59,f1522])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    spl3_4 <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    spl3_11 <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    spl3_12 <=> ! [X1,X3,X0,X2] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.53  fof(f627,plain,(
% 0.21/0.53    spl3_49 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.21/0.53  fof(f643,plain,(
% 0.21/0.53    ( ! [X47,X45,X46,X44] : (k2_enumset1(X44,X45,X46,X47) = k3_enumset1(X44,X45,X44,X46,X47)) ) | (~spl3_4 | ~spl3_11 | ~spl3_12 | ~spl3_49)),
% 0.21/0.53    inference(forward_demodulation,[],[f639,f642])).
% 0.21/0.53  fof(f642,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | (~spl3_4 | ~spl3_12 | ~spl3_49)),
% 0.21/0.53    inference(forward_demodulation,[],[f630,f132])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) ) | ~spl3_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f131])).
% 0.21/0.53  fof(f630,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | (~spl3_4 | ~spl3_49)),
% 0.21/0.53    inference(superposition,[],[f628,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) ) | ~spl3_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f59])).
% 0.21/0.53  fof(f628,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) ) | ~spl3_49),
% 0.21/0.53    inference(avatar_component_clause,[],[f627])).
% 0.21/0.53  fof(f639,plain,(
% 0.21/0.53    ( ! [X47,X45,X46,X44] : (k3_enumset1(X44,X45,X44,X46,X47) = k2_xboole_0(k2_tarski(X44,X45),k2_tarski(X46,X47))) ) | (~spl3_11 | ~spl3_49)),
% 0.21/0.53    inference(superposition,[],[f628,f128])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)) ) | ~spl3_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f127])).
% 0.21/0.53  fof(f1510,plain,(
% 0.21/0.53    spl3_82 | ~spl3_4 | ~spl3_12 | ~spl3_49),
% 0.21/0.53    inference(avatar_split_clause,[],[f642,f627,f131,f59,f1508])).
% 0.21/0.53  fof(f1304,plain,(
% 0.21/0.53    ~spl3_75 | spl3_1 | ~spl3_66),
% 0.21/0.53    inference(avatar_split_clause,[],[f1206,f1021,f46,f1301])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    spl3_1 <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.53  fof(f1021,plain,(
% 0.21/0.53    spl3_66 <=> ! [X3,X2] : k2_tarski(X2,X3) = k2_tarski(X3,X2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 0.21/0.53  fof(f1206,plain,(
% 0.21/0.53    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2)) | (spl3_1 | ~spl3_66)),
% 0.21/0.53    inference(forward_demodulation,[],[f1194,f1022])).
% 0.21/0.53  fof(f1022,plain,(
% 0.21/0.53    ( ! [X2,X3] : (k2_tarski(X2,X3) = k2_tarski(X3,X2)) ) | ~spl3_66),
% 0.21/0.53    inference(avatar_component_clause,[],[f1021])).
% 0.21/0.53  fof(f1194,plain,(
% 0.21/0.53    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK0)) | (spl3_1 | ~spl3_66)),
% 0.21/0.53    inference(superposition,[],[f48,f1022])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) | spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f46])).
% 0.21/0.53  fof(f1023,plain,(
% 0.21/0.53    spl3_66 | ~spl3_4 | ~spl3_57),
% 0.21/0.53    inference(avatar_split_clause,[],[f856,f745,f59,f1021])).
% 0.21/0.53  fof(f745,plain,(
% 0.21/0.53    spl3_57 <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.21/0.53  fof(f856,plain,(
% 0.21/0.53    ( ! [X2,X3] : (k2_tarski(X2,X3) = k2_tarski(X3,X2)) ) | (~spl3_4 | ~spl3_57)),
% 0.21/0.53    inference(superposition,[],[f746,f60])).
% 0.21/0.53  fof(f746,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X1,X0)) ) | ~spl3_57),
% 0.21/0.53    inference(avatar_component_clause,[],[f745])).
% 0.21/0.53  fof(f747,plain,(
% 0.21/0.53    spl3_57 | ~spl3_10 | ~spl3_20 | ~spl3_48),
% 0.21/0.53    inference(avatar_split_clause,[],[f676,f623,f188,f83,f745])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    spl3_10 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    spl3_20 <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.53  fof(f676,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X1,X0)) ) | (~spl3_10 | ~spl3_20 | ~spl3_48)),
% 0.21/0.53    inference(forward_demodulation,[],[f668,f189])).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)) ) | ~spl3_20),
% 0.21/0.53    inference(avatar_component_clause,[],[f188])).
% 0.21/0.53  fof(f668,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X0,X1,X1)) ) | (~spl3_10 | ~spl3_48)),
% 0.21/0.53    inference(superposition,[],[f624,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) ) | ~spl3_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f83])).
% 0.21/0.53  fof(f629,plain,(
% 0.21/0.53    spl3_49 | ~spl3_10 | ~spl3_13 | ~spl3_26),
% 0.21/0.53    inference(avatar_split_clause,[],[f287,f282,f135,f83,f627])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    spl3_13 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.53  fof(f282,plain,(
% 0.21/0.53    spl3_26 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.53  fof(f287,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) ) | (~spl3_10 | ~spl3_13 | ~spl3_26)),
% 0.21/0.53    inference(forward_demodulation,[],[f285,f136])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) ) | ~spl3_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f135])).
% 0.21/0.53  fof(f285,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) ) | (~spl3_10 | ~spl3_26)),
% 0.21/0.53    inference(superposition,[],[f283,f84])).
% 0.21/0.53  fof(f283,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) ) | ~spl3_26),
% 0.21/0.53    inference(avatar_component_clause,[],[f282])).
% 1.36/0.53  fof(f625,plain,(
% 1.36/0.53    spl3_48 | ~spl3_10 | ~spl3_12 | ~spl3_38),
% 1.36/0.53    inference(avatar_split_clause,[],[f503,f457,f131,f83,f623])).
% 1.36/0.53  fof(f503,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)) ) | (~spl3_10 | ~spl3_12 | ~spl3_38)),
% 1.36/0.53    inference(forward_demodulation,[],[f493,f84])).
% 1.36/0.53  fof(f493,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)) ) | (~spl3_12 | ~spl3_38)),
% 1.36/0.53    inference(superposition,[],[f458,f132])).
% 1.36/0.53  fof(f459,plain,(
% 1.36/0.53    spl3_38 | ~spl3_12 | ~spl3_13 | ~spl3_29),
% 1.36/0.53    inference(avatar_split_clause,[],[f369,f303,f135,f131,f457])).
% 1.36/0.53  fof(f303,plain,(
% 1.36/0.53    spl3_29 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)),
% 1.36/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 1.36/0.53  fof(f369,plain,(
% 1.36/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3)) ) | (~spl3_12 | ~spl3_13 | ~spl3_29)),
% 1.36/0.53    inference(forward_demodulation,[],[f364,f132])).
% 1.36/0.53  fof(f364,plain,(
% 1.36/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3)) ) | (~spl3_13 | ~spl3_29)),
% 1.36/0.53    inference(superposition,[],[f304,f136])).
% 1.36/0.53  fof(f304,plain,(
% 1.36/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)) ) | ~spl3_29),
% 1.36/0.53    inference(avatar_component_clause,[],[f303])).
% 1.36/0.53  fof(f305,plain,(
% 1.36/0.53    spl3_29 | ~spl3_13 | ~spl3_14 | ~spl3_28),
% 1.36/0.53    inference(avatar_split_clause,[],[f300,f295,f139,f135,f303])).
% 1.36/0.53  fof(f139,plain,(
% 1.36/0.53    spl3_14 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.36/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.36/0.53  fof(f295,plain,(
% 1.36/0.53    spl3_28 <=> ! [X1,X3,X5,X0,X2,X4] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X5,X0)),
% 1.36/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 1.36/0.53  fof(f300,plain,(
% 1.36/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)) ) | (~spl3_13 | ~spl3_14 | ~spl3_28)),
% 1.36/0.53    inference(forward_demodulation,[],[f298,f136])).
% 1.36/0.53  fof(f298,plain,(
% 1.36/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)) ) | (~spl3_14 | ~spl3_28)),
% 1.36/0.53    inference(superposition,[],[f296,f140])).
% 1.36/0.53  fof(f140,plain,(
% 1.36/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) ) | ~spl3_14),
% 1.36/0.53    inference(avatar_component_clause,[],[f139])).
% 1.36/0.53  fof(f296,plain,(
% 1.36/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X5,X0)) ) | ~spl3_28),
% 1.36/0.53    inference(avatar_component_clause,[],[f295])).
% 1.36/0.53  fof(f297,plain,(
% 1.36/0.53    spl3_28 | ~spl3_13 | ~spl3_14 | ~spl3_17 | ~spl3_25),
% 1.36/0.53    inference(avatar_split_clause,[],[f280,f277,f159,f139,f135,f295])).
% 1.36/0.53  fof(f159,plain,(
% 1.36/0.53    spl3_17 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 1.36/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.36/0.53  fof(f277,plain,(
% 1.36/0.53    spl3_25 <=> ! [X1,X3,X5,X0,X2,X4] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))),
% 1.36/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 1.36/0.53  fof(f280,plain,(
% 1.36/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X5,X0)) ) | (~spl3_13 | ~spl3_14 | ~spl3_17 | ~spl3_25)),
% 1.36/0.53    inference(forward_demodulation,[],[f278,f166])).
% 1.36/0.53  fof(f166,plain,(
% 1.36/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) ) | (~spl3_13 | ~spl3_14 | ~spl3_17)),
% 1.36/0.53    inference(forward_demodulation,[],[f165,f140])).
% 1.36/0.53  fof(f165,plain,(
% 1.36/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) ) | (~spl3_13 | ~spl3_17)),
% 1.36/0.53    inference(superposition,[],[f160,f136])).
% 1.36/0.53  fof(f160,plain,(
% 1.36/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) ) | ~spl3_17),
% 1.36/0.53    inference(avatar_component_clause,[],[f159])).
% 1.36/0.53  fof(f278,plain,(
% 1.36/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) ) | ~spl3_25),
% 1.36/0.53    inference(avatar_component_clause,[],[f277])).
% 1.36/0.53  fof(f284,plain,(
% 1.36/0.53    spl3_26 | ~spl3_12 | ~spl3_14 | ~spl3_16),
% 1.36/0.53    inference(avatar_split_clause,[],[f164,f155,f139,f131,f282])).
% 1.36/0.53  fof(f155,plain,(
% 1.36/0.53    spl3_16 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 1.36/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.36/0.53  fof(f164,plain,(
% 1.36/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) ) | (~spl3_12 | ~spl3_14 | ~spl3_16)),
% 1.36/0.53    inference(forward_demodulation,[],[f162,f140])).
% 1.36/0.53  fof(f162,plain,(
% 1.36/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) ) | (~spl3_12 | ~spl3_16)),
% 1.36/0.53    inference(superposition,[],[f156,f132])).
% 1.36/0.53  fof(f156,plain,(
% 1.36/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) ) | ~spl3_16),
% 1.36/0.53    inference(avatar_component_clause,[],[f155])).
% 1.36/0.53  fof(f279,plain,(
% 1.36/0.53    spl3_25 | ~spl3_2 | ~spl3_16),
% 1.36/0.53    inference(avatar_split_clause,[],[f163,f155,f51,f277])).
% 1.36/0.53  fof(f51,plain,(
% 1.36/0.53    spl3_2 <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.36/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.36/0.53  fof(f163,plain,(
% 1.36/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) ) | (~spl3_2 | ~spl3_16)),
% 1.36/0.53    inference(superposition,[],[f156,f52])).
% 1.36/0.53  fof(f52,plain,(
% 1.36/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) ) | ~spl3_2),
% 1.36/0.53    inference(avatar_component_clause,[],[f51])).
% 1.36/0.53  fof(f190,plain,(
% 1.36/0.53    spl3_20 | ~spl3_4 | ~spl3_7),
% 1.36/0.53    inference(avatar_split_clause,[],[f90,f71,f59,f188])).
% 1.36/0.53  fof(f71,plain,(
% 1.36/0.53    spl3_7 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 1.36/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.36/0.53  fof(f90,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)) ) | (~spl3_4 | ~spl3_7)),
% 1.36/0.53    inference(superposition,[],[f72,f60])).
% 1.36/0.53  fof(f72,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) ) | ~spl3_7),
% 1.36/0.53    inference(avatar_component_clause,[],[f71])).
% 1.36/0.53  fof(f161,plain,(
% 1.36/0.53    spl3_17),
% 1.36/0.53    inference(avatar_split_clause,[],[f40,f159])).
% 1.36/0.53  fof(f40,plain,(
% 1.36/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 1.36/0.53    inference(cnf_transformation,[],[f9])).
% 1.36/0.53  fof(f9,axiom,(
% 1.36/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).
% 1.36/0.53  fof(f157,plain,(
% 1.36/0.53    spl3_16),
% 1.36/0.53    inference(avatar_split_clause,[],[f39,f155])).
% 1.36/0.53  fof(f39,plain,(
% 1.36/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 1.36/0.53    inference(cnf_transformation,[],[f8])).
% 1.36/0.53  fof(f8,axiom,(
% 1.36/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).
% 1.36/0.53  fof(f141,plain,(
% 1.36/0.53    spl3_14),
% 1.36/0.53    inference(avatar_split_clause,[],[f37,f139])).
% 1.36/0.53  fof(f37,plain,(
% 1.36/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f17])).
% 1.36/0.53  fof(f17,axiom,(
% 1.36/0.53    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.36/0.53  fof(f137,plain,(
% 1.36/0.53    spl3_13),
% 1.36/0.53    inference(avatar_split_clause,[],[f36,f135])).
% 1.36/0.53  fof(f36,plain,(
% 1.36/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f16])).
% 1.36/0.53  fof(f16,axiom,(
% 1.36/0.53    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.36/0.53  fof(f133,plain,(
% 1.36/0.53    spl3_12),
% 1.36/0.53    inference(avatar_split_clause,[],[f35,f131])).
% 1.36/0.53  fof(f35,plain,(
% 1.36/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f15])).
% 1.36/0.53  fof(f15,axiom,(
% 1.36/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.36/0.53  fof(f129,plain,(
% 1.36/0.53    spl3_11 | ~spl3_4 | ~spl3_7),
% 1.36/0.53    inference(avatar_split_clause,[],[f88,f71,f59,f127])).
% 1.36/0.53  fof(f88,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)) ) | (~spl3_4 | ~spl3_7)),
% 1.36/0.53    inference(superposition,[],[f72,f60])).
% 1.36/0.53  fof(f85,plain,(
% 1.36/0.53    spl3_10),
% 1.36/0.53    inference(avatar_split_clause,[],[f34,f83])).
% 1.36/0.53  fof(f34,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f14])).
% 1.36/0.53  fof(f14,axiom,(
% 1.36/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.36/0.53  fof(f73,plain,(
% 1.36/0.53    spl3_7),
% 1.36/0.53    inference(avatar_split_clause,[],[f31,f71])).
% 1.36/0.53  fof(f31,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f4])).
% 1.36/0.53  fof(f4,axiom,(
% 1.36/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).
% 1.36/0.53  fof(f61,plain,(
% 1.36/0.53    spl3_4),
% 1.36/0.53    inference(avatar_split_clause,[],[f28,f59])).
% 1.36/0.53  fof(f28,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f13])).
% 1.36/0.53  fof(f13,axiom,(
% 1.36/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.36/0.53  fof(f53,plain,(
% 1.36/0.53    spl3_2),
% 1.36/0.53    inference(avatar_split_clause,[],[f26,f51])).
% 1.36/0.53  fof(f26,plain,(
% 1.36/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f12])).
% 1.36/0.53  fof(f12,axiom,(
% 1.36/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.36/0.53  fof(f49,plain,(
% 1.36/0.53    ~spl3_1),
% 1.36/0.53    inference(avatar_split_clause,[],[f25,f46])).
% 1.36/0.53  fof(f25,plain,(
% 1.36/0.53    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.36/0.53    inference(cnf_transformation,[],[f24])).
% 1.36/0.53  fof(f24,plain,(
% 1.36/0.53    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.36/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).
% 1.36/0.53  fof(f23,plain,(
% 1.36/0.53    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.36/0.53    introduced(choice_axiom,[])).
% 1.36/0.53  fof(f22,plain,(
% 1.36/0.53    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.36/0.53    inference(ennf_transformation,[],[f21])).
% 1.36/0.53  fof(f21,negated_conjecture,(
% 1.36/0.53    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.36/0.53    inference(negated_conjecture,[],[f20])).
% 1.36/0.53  fof(f20,conjecture,(
% 1.36/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 1.36/0.53  % SZS output end Proof for theBenchmark
% 1.36/0.53  % (19163)------------------------------
% 1.36/0.53  % (19163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  % (19163)Termination reason: Refutation
% 1.36/0.53  
% 1.36/0.53  % (19163)Memory used [KB]: 7164
% 1.36/0.53  % (19163)Time elapsed: 0.099 s
% 1.36/0.53  % (19163)------------------------------
% 1.36/0.53  % (19163)------------------------------
% 1.36/0.53  % (19157)Success in time 0.166 s
%------------------------------------------------------------------------------
