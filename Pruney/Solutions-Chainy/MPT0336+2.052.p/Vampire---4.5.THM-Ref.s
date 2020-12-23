%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:30 EST 2020

% Result     : Theorem 6.53s
% Output     : Refutation 6.53s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 270 expanded)
%              Number of leaves         :   41 ( 125 expanded)
%              Depth                    :    7
%              Number of atoms          :  437 ( 762 expanded)
%              Number of equality atoms :   70 ( 138 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9084,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f84,f88,f108,f112,f116,f120,f142,f155,f164,f177,f210,f312,f322,f359,f370,f425,f496,f541,f1274,f3251,f3636,f3642,f7604,f8763,f9019,f9079])).

fof(f9079,plain,
    ( ~ spl5_29
    | spl5_120
    | ~ spl5_141 ),
    inference(avatar_contradiction_clause,[],[f9078])).

fof(f9078,plain,
    ( $false
    | ~ spl5_29
    | spl5_120
    | ~ spl5_141 ),
    inference(subsumption_resolution,[],[f8762,f9028])).

fof(f9028,plain,
    ( ! [X0] : r1_xboole_0(k1_tarski(sK3),k3_xboole_0(X0,sK1))
    | ~ spl5_29
    | ~ spl5_141 ),
    inference(unit_resulting_resolution,[],[f321,f9018])).

fof(f9018,plain,
    ( ! [X61,X59,X60] :
        ( r1_xboole_0(X59,k3_xboole_0(X60,X61))
        | ~ r1_xboole_0(X59,X61) )
    | ~ spl5_141 ),
    inference(avatar_component_clause,[],[f9017])).

fof(f9017,plain,
    ( spl5_141
  <=> ! [X60,X59,X61] :
        ( r1_xboole_0(X59,k3_xboole_0(X60,X61))
        | ~ r1_xboole_0(X59,X61) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_141])])).

fof(f321,plain,
    ( r1_xboole_0(k1_tarski(sK3),sK1)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl5_29
  <=> r1_xboole_0(k1_tarski(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f8762,plain,
    ( ~ r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))
    | spl5_120 ),
    inference(avatar_component_clause,[],[f8760])).

fof(f8760,plain,
    ( spl5_120
  <=> r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).

fof(f9019,plain,
    ( spl5_141
    | ~ spl5_14
    | ~ spl5_82 ),
    inference(avatar_split_clause,[],[f3769,f3640,f114,f9017])).

fof(f114,plain,
    ( spl5_14
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f3640,plain,
    ( spl5_82
  <=> ! [X1,X0,X2] :
        ( k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(X2,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f3769,plain,
    ( ! [X61,X59,X60] :
        ( r1_xboole_0(X59,k3_xboole_0(X60,X61))
        | ~ r1_xboole_0(X59,X61) )
    | ~ spl5_14
    | ~ spl5_82 ),
    inference(trivial_inequality_removal,[],[f3714])).

fof(f3714,plain,
    ( ! [X61,X59,X60] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_xboole_0(X59,k3_xboole_0(X60,X61))
        | ~ r1_xboole_0(X59,X61) )
    | ~ spl5_14
    | ~ spl5_82 ),
    inference(superposition,[],[f115,f3641])).

fof(f3641,plain,
    ( ! [X2,X0,X1] :
        ( k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(X2,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_82 ),
    inference(avatar_component_clause,[],[f3640])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f114])).

fof(f8763,plain,
    ( ~ spl5_120
    | ~ spl5_39
    | ~ spl5_42
    | spl5_94 ),
    inference(avatar_split_clause,[],[f7417,f7413,f494,f422,f8760])).

fof(f422,plain,
    ( spl5_39
  <=> k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f494,plain,
    ( spl5_42
  <=> ! [X5,X4] :
        ( k1_xboole_0 = k3_xboole_0(X5,X4)
        | ~ r1_xboole_0(X4,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f7413,plain,
    ( spl5_94
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f7417,plain,
    ( ~ r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))
    | ~ spl5_39
    | ~ spl5_42
    | spl5_94 ),
    inference(subsumption_resolution,[],[f508,f7415])).

fof(f7415,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | spl5_94 ),
    inference(avatar_component_clause,[],[f7413])).

fof(f508,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))
    | ~ spl5_39
    | ~ spl5_42 ),
    inference(superposition,[],[f495,f424])).

fof(f424,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f422])).

fof(f495,plain,
    ( ! [X4,X5] :
        ( k1_xboole_0 = k3_xboole_0(X5,X4)
        | ~ r1_xboole_0(X4,X5) )
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f494])).

fof(f7604,plain,
    ( ~ spl5_6
    | ~ spl5_16
    | spl5_35
    | ~ spl5_44
    | ~ spl5_63
    | ~ spl5_94 ),
    inference(avatar_contradiction_clause,[],[f7601])).

fof(f7601,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_16
    | spl5_35
    | ~ spl5_44
    | ~ spl5_63
    | ~ spl5_94 ),
    inference(subsumption_resolution,[],[f1337,f7534])).

fof(f7534,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl5_44
    | ~ spl5_94 ),
    inference(unit_resulting_resolution,[],[f7414,f540])).

fof(f540,plain,
    ( ! [X4,X5] :
        ( k1_xboole_0 != k3_xboole_0(X5,X4)
        | r1_xboole_0(X4,X5) )
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f539])).

fof(f539,plain,
    ( spl5_44
  <=> ! [X5,X4] :
        ( k1_xboole_0 != k3_xboole_0(X5,X4)
        | r1_xboole_0(X4,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f7414,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl5_94 ),
    inference(avatar_component_clause,[],[f7413])).

fof(f1337,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ spl5_6
    | ~ spl5_16
    | spl5_35
    | ~ spl5_63 ),
    inference(trivial_inequality_removal,[],[f1336])).

fof(f1336,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(sK1,sK0)
    | ~ spl5_6
    | ~ spl5_16
    | spl5_35
    | ~ spl5_63 ),
    inference(forward_demodulation,[],[f1292,f292])).

fof(f292,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl5_6
    | ~ spl5_16 ),
    inference(superposition,[],[f141,f83])).

fof(f83,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_6
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f141,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl5_16
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f1292,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0)
    | spl5_35
    | ~ spl5_63 ),
    inference(superposition,[],[f358,f1273])).

fof(f1273,plain,
    ( ! [X10,X11,X9] :
        ( k3_xboole_0(X9,X11) = k3_xboole_0(k2_xboole_0(X10,X11),X9)
        | ~ r1_xboole_0(X9,X10) )
    | ~ spl5_63 ),
    inference(avatar_component_clause,[],[f1272])).

fof(f1272,plain,
    ( spl5_63
  <=> ! [X9,X11,X10] :
        ( k3_xboole_0(X9,X11) = k3_xboole_0(k2_xboole_0(X10,X11),X9)
        | ~ r1_xboole_0(X9,X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f358,plain,
    ( k1_xboole_0 != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl5_35 ),
    inference(avatar_component_clause,[],[f356])).

fof(f356,plain,
    ( spl5_35
  <=> k1_xboole_0 = k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f3642,plain,
    ( spl5_82
    | ~ spl5_16
    | ~ spl5_36
    | ~ spl5_76
    | ~ spl5_81 ),
    inference(avatar_split_clause,[],[f3638,f3634,f3249,f368,f139,f3640])).

fof(f368,plain,
    ( spl5_36
  <=> ! [X0] : r1_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f3249,plain,
    ( spl5_76
  <=> ! [X7,X8,X6] :
        ( k1_xboole_0 = k3_xboole_0(X6,k3_xboole_0(X7,X8))
        | ~ r1_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X8)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f3634,plain,
    ( spl5_81
  <=> ! [X1,X0,X2] :
        ( k3_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(X0,k3_xboole_0(X2,k1_xboole_0))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f3638,plain,
    ( ! [X2,X0,X1] :
        ( k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(X2,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_16
    | ~ spl5_36
    | ~ spl5_76
    | ~ spl5_81 ),
    inference(forward_demodulation,[],[f3637,f3314])).

fof(f3314,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl5_16
    | ~ spl5_36
    | ~ spl5_76 ),
    inference(forward_demodulation,[],[f3252,f141])).

fof(f3252,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(sK2,sK1))
    | ~ spl5_36
    | ~ spl5_76 ),
    inference(unit_resulting_resolution,[],[f369,f3250])).

fof(f3250,plain,
    ( ! [X6,X8,X7] :
        ( ~ r1_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X8))
        | k1_xboole_0 = k3_xboole_0(X6,k3_xboole_0(X7,X8)) )
    | ~ spl5_76 ),
    inference(avatar_component_clause,[],[f3249])).

fof(f369,plain,
    ( ! [X0] : r1_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(X0,sK1))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f368])).

fof(f3637,plain,
    ( ! [X2,X0,X1] :
        ( k3_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(X0,k1_xboole_0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_16
    | ~ spl5_36
    | ~ spl5_76
    | ~ spl5_81 ),
    inference(forward_demodulation,[],[f3635,f3314])).

fof(f3635,plain,
    ( ! [X2,X0,X1] :
        ( k3_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(X0,k3_xboole_0(X2,k1_xboole_0))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_81 ),
    inference(avatar_component_clause,[],[f3634])).

fof(f3636,plain,
    ( spl5_81
    | ~ spl5_13
    | ~ spl5_19
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f267,f208,f162,f110,f3634])).

fof(f110,plain,
    ( spl5_13
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f162,plain,
    ( spl5_19
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f208,plain,
    ( spl5_23
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f267,plain,
    ( ! [X2,X0,X1] :
        ( k3_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(X0,k3_xboole_0(X2,k1_xboole_0))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_13
    | ~ spl5_19
    | ~ spl5_23 ),
    inference(forward_demodulation,[],[f240,f163])).

fof(f163,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f162])).

fof(f240,plain,
    ( ! [X2,X0,X1] :
        ( k3_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k3_xboole_0(X0,X2),k1_xboole_0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_13
    | ~ spl5_23 ),
    inference(superposition,[],[f209,f111])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f110])).

fof(f209,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f208])).

fof(f3251,plain,
    ( spl5_76
    | ~ spl5_13
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f248,f208,f110,f3249])).

fof(f248,plain,
    ( ! [X6,X8,X7] :
        ( k1_xboole_0 = k3_xboole_0(X6,k3_xboole_0(X7,X8))
        | ~ r1_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X8)) )
    | ~ spl5_13
    | ~ spl5_23 ),
    inference(superposition,[],[f209,f111])).

fof(f1274,plain,
    ( spl5_63
    | ~ spl5_6
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f214,f175,f82,f1272])).

fof(f175,plain,
    ( spl5_20
  <=> ! [X1,X0,X2] :
        ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f214,plain,
    ( ! [X10,X11,X9] :
        ( k3_xboole_0(X9,X11) = k3_xboole_0(k2_xboole_0(X10,X11),X9)
        | ~ r1_xboole_0(X9,X10) )
    | ~ spl5_6
    | ~ spl5_20 ),
    inference(superposition,[],[f176,f83])).

fof(f176,plain,
    ( ! [X2,X0,X1] :
        ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f175])).

fof(f541,plain,
    ( spl5_44
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f146,f114,f82,f539])).

fof(f146,plain,
    ( ! [X4,X5] :
        ( k1_xboole_0 != k3_xboole_0(X5,X4)
        | r1_xboole_0(X4,X5) )
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(superposition,[],[f115,f83])).

fof(f496,plain,
    ( spl5_42
    | ~ spl5_6
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f132,f110,f82,f494])).

fof(f132,plain,
    ( ! [X4,X5] :
        ( k1_xboole_0 = k3_xboole_0(X5,X4)
        | ~ r1_xboole_0(X4,X5) )
    | ~ spl5_6
    | ~ spl5_13 ),
    inference(superposition,[],[f111,f83])).

fof(f425,plain,
    ( spl5_39
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f124,f106,f73,f422])).

fof(f73,plain,
    ( spl5_4
  <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f106,plain,
    ( spl5_12
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f124,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f75,f107])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f106])).

fof(f75,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f370,plain,
    ( spl5_36
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f165,f153,f63,f368])).

fof(f63,plain,
    ( spl5_2
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f153,plain,
    ( spl5_18
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f165,plain,
    ( ! [X0] : r1_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(X0,sK1))
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f65,f154])).

fof(f154,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f153])).

fof(f65,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f359,plain,
    ( ~ spl5_35
    | spl5_3
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f143,f114,f68,f356])).

fof(f68,plain,
    ( spl5_3
  <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f143,plain,
    ( k1_xboole_0 != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl5_3
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f70,f115])).

fof(f70,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f322,plain,
    ( spl5_29
    | ~ spl5_7
    | spl5_27 ),
    inference(avatar_split_clause,[],[f313,f309,f86,f319])).

fof(f86,plain,
    ( spl5_7
  <=> ! [X1,X0] :
        ( r1_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f309,plain,
    ( spl5_27
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f313,plain,
    ( r1_xboole_0(k1_tarski(sK3),sK1)
    | ~ spl5_7
    | spl5_27 ),
    inference(unit_resulting_resolution,[],[f311,f87])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f311,plain,
    ( ~ r2_hidden(sK3,sK1)
    | spl5_27 ),
    inference(avatar_component_clause,[],[f309])).

fof(f312,plain,
    ( ~ spl5_27
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f156,f118,f63,f58,f309])).

fof(f58,plain,
    ( spl5_1
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f118,plain,
    ( spl5_15
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f156,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f60,f65,f119])).

fof(f119,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,X1)
        | ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f118])).

fof(f60,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f210,plain,(
    spl5_23 ),
    inference(avatar_split_clause,[],[f50,f208])).

fof(f50,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_xboole_1)).

fof(f177,plain,(
    spl5_20 ),
    inference(avatar_split_clause,[],[f52,f175])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f164,plain,(
    spl5_19 ),
    inference(avatar_split_clause,[],[f49,f162])).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f155,plain,(
    spl5_18 ),
    inference(avatar_split_clause,[],[f51,f153])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

fof(f142,plain,
    ( spl5_16
    | ~ spl5_2
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f130,f110,f63,f139])).

fof(f130,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl5_2
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f65,f111])).

fof(f120,plain,(
    spl5_15 ),
    inference(avatar_split_clause,[],[f43,f118])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f116,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f47,f114])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f112,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f46,f110])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f108,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f45,f106])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f88,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f44,f86])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f84,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f38,f82])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f76,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f33,f73])).

fof(f33,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f71,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f36,f68])).

fof(f36,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f35,f63])).

fof(f35,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f34,f58])).

fof(f34,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:44:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (17397)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.51  % (17391)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (17390)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.51  % (17393)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (17396)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (17399)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.51  % (17398)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.52  % (17401)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.52  % (17404)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.55  % (17403)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.50/0.56  % (17394)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.50/0.56  % (17392)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 1.50/0.56  % (17395)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.50/0.56  % (17387)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.50/0.56  % (17400)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.50/0.56  % (17389)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 1.50/0.57  % (17388)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.50/0.57  % (17402)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 5.18/1.05  % (17391)Time limit reached!
% 5.18/1.05  % (17391)------------------------------
% 5.18/1.05  % (17391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.18/1.05  % (17391)Termination reason: Time limit
% 5.18/1.05  
% 5.18/1.05  % (17391)Memory used [KB]: 13048
% 5.18/1.05  % (17391)Time elapsed: 0.604 s
% 5.18/1.05  % (17391)------------------------------
% 5.18/1.05  % (17391)------------------------------
% 6.53/1.24  % (17392)Refutation found. Thanks to Tanya!
% 6.53/1.24  % SZS status Theorem for theBenchmark
% 6.53/1.24  % SZS output start Proof for theBenchmark
% 6.53/1.24  fof(f9084,plain,(
% 6.53/1.24    $false),
% 6.53/1.24    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f84,f88,f108,f112,f116,f120,f142,f155,f164,f177,f210,f312,f322,f359,f370,f425,f496,f541,f1274,f3251,f3636,f3642,f7604,f8763,f9019,f9079])).
% 6.53/1.24  fof(f9079,plain,(
% 6.53/1.24    ~spl5_29 | spl5_120 | ~spl5_141),
% 6.53/1.24    inference(avatar_contradiction_clause,[],[f9078])).
% 6.53/1.24  fof(f9078,plain,(
% 6.53/1.24    $false | (~spl5_29 | spl5_120 | ~spl5_141)),
% 6.53/1.24    inference(subsumption_resolution,[],[f8762,f9028])).
% 6.53/1.24  fof(f9028,plain,(
% 6.53/1.24    ( ! [X0] : (r1_xboole_0(k1_tarski(sK3),k3_xboole_0(X0,sK1))) ) | (~spl5_29 | ~spl5_141)),
% 6.53/1.24    inference(unit_resulting_resolution,[],[f321,f9018])).
% 6.53/1.24  fof(f9018,plain,(
% 6.53/1.24    ( ! [X61,X59,X60] : (r1_xboole_0(X59,k3_xboole_0(X60,X61)) | ~r1_xboole_0(X59,X61)) ) | ~spl5_141),
% 6.53/1.24    inference(avatar_component_clause,[],[f9017])).
% 6.53/1.24  fof(f9017,plain,(
% 6.53/1.24    spl5_141 <=> ! [X60,X59,X61] : (r1_xboole_0(X59,k3_xboole_0(X60,X61)) | ~r1_xboole_0(X59,X61))),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_141])])).
% 6.53/1.24  fof(f321,plain,(
% 6.53/1.24    r1_xboole_0(k1_tarski(sK3),sK1) | ~spl5_29),
% 6.53/1.24    inference(avatar_component_clause,[],[f319])).
% 6.53/1.24  fof(f319,plain,(
% 6.53/1.24    spl5_29 <=> r1_xboole_0(k1_tarski(sK3),sK1)),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 6.53/1.24  fof(f8762,plain,(
% 6.53/1.24    ~r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) | spl5_120),
% 6.53/1.24    inference(avatar_component_clause,[],[f8760])).
% 6.53/1.24  fof(f8760,plain,(
% 6.53/1.24    spl5_120 <=> r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).
% 6.53/1.24  fof(f9019,plain,(
% 6.53/1.24    spl5_141 | ~spl5_14 | ~spl5_82),
% 6.53/1.24    inference(avatar_split_clause,[],[f3769,f3640,f114,f9017])).
% 6.53/1.24  fof(f114,plain,(
% 6.53/1.24    spl5_14 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 6.53/1.24  fof(f3640,plain,(
% 6.53/1.24    spl5_82 <=> ! [X1,X0,X2] : (k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1))),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).
% 6.53/1.24  fof(f3769,plain,(
% 6.53/1.24    ( ! [X61,X59,X60] : (r1_xboole_0(X59,k3_xboole_0(X60,X61)) | ~r1_xboole_0(X59,X61)) ) | (~spl5_14 | ~spl5_82)),
% 6.53/1.24    inference(trivial_inequality_removal,[],[f3714])).
% 6.53/1.24  fof(f3714,plain,(
% 6.53/1.24    ( ! [X61,X59,X60] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(X59,k3_xboole_0(X60,X61)) | ~r1_xboole_0(X59,X61)) ) | (~spl5_14 | ~spl5_82)),
% 6.53/1.24    inference(superposition,[],[f115,f3641])).
% 6.53/1.24  fof(f3641,plain,(
% 6.53/1.24    ( ! [X2,X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl5_82),
% 6.53/1.24    inference(avatar_component_clause,[],[f3640])).
% 6.53/1.24  fof(f115,plain,(
% 6.53/1.24    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) ) | ~spl5_14),
% 6.53/1.24    inference(avatar_component_clause,[],[f114])).
% 6.53/1.24  fof(f8763,plain,(
% 6.53/1.24    ~spl5_120 | ~spl5_39 | ~spl5_42 | spl5_94),
% 6.53/1.24    inference(avatar_split_clause,[],[f7417,f7413,f494,f422,f8760])).
% 6.53/1.24  fof(f422,plain,(
% 6.53/1.24    spl5_39 <=> k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 6.53/1.24  fof(f494,plain,(
% 6.53/1.24    spl5_42 <=> ! [X5,X4] : (k1_xboole_0 = k3_xboole_0(X5,X4) | ~r1_xboole_0(X4,X5))),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 6.53/1.24  fof(f7413,plain,(
% 6.53/1.24    spl5_94 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).
% 6.53/1.24  fof(f7417,plain,(
% 6.53/1.24    ~r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) | (~spl5_39 | ~spl5_42 | spl5_94)),
% 6.53/1.24    inference(subsumption_resolution,[],[f508,f7415])).
% 6.53/1.24  fof(f7415,plain,(
% 6.53/1.24    k1_xboole_0 != k3_xboole_0(sK0,sK1) | spl5_94),
% 6.53/1.24    inference(avatar_component_clause,[],[f7413])).
% 6.53/1.24  fof(f508,plain,(
% 6.53/1.24    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) | (~spl5_39 | ~spl5_42)),
% 6.53/1.24    inference(superposition,[],[f495,f424])).
% 6.53/1.24  fof(f424,plain,(
% 6.53/1.24    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | ~spl5_39),
% 6.53/1.24    inference(avatar_component_clause,[],[f422])).
% 6.53/1.24  fof(f495,plain,(
% 6.53/1.24    ( ! [X4,X5] : (k1_xboole_0 = k3_xboole_0(X5,X4) | ~r1_xboole_0(X4,X5)) ) | ~spl5_42),
% 6.53/1.24    inference(avatar_component_clause,[],[f494])).
% 6.53/1.24  fof(f7604,plain,(
% 6.53/1.24    ~spl5_6 | ~spl5_16 | spl5_35 | ~spl5_44 | ~spl5_63 | ~spl5_94),
% 6.53/1.24    inference(avatar_contradiction_clause,[],[f7601])).
% 6.53/1.24  fof(f7601,plain,(
% 6.53/1.24    $false | (~spl5_6 | ~spl5_16 | spl5_35 | ~spl5_44 | ~spl5_63 | ~spl5_94)),
% 6.53/1.24    inference(subsumption_resolution,[],[f1337,f7534])).
% 6.53/1.24  fof(f7534,plain,(
% 6.53/1.24    r1_xboole_0(sK1,sK0) | (~spl5_44 | ~spl5_94)),
% 6.53/1.24    inference(unit_resulting_resolution,[],[f7414,f540])).
% 6.53/1.24  fof(f540,plain,(
% 6.53/1.24    ( ! [X4,X5] : (k1_xboole_0 != k3_xboole_0(X5,X4) | r1_xboole_0(X4,X5)) ) | ~spl5_44),
% 6.53/1.24    inference(avatar_component_clause,[],[f539])).
% 6.53/1.24  fof(f539,plain,(
% 6.53/1.24    spl5_44 <=> ! [X5,X4] : (k1_xboole_0 != k3_xboole_0(X5,X4) | r1_xboole_0(X4,X5))),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 6.53/1.24  fof(f7414,plain,(
% 6.53/1.24    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl5_94),
% 6.53/1.24    inference(avatar_component_clause,[],[f7413])).
% 6.53/1.24  fof(f1337,plain,(
% 6.53/1.24    ~r1_xboole_0(sK1,sK0) | (~spl5_6 | ~spl5_16 | spl5_35 | ~spl5_63)),
% 6.53/1.24    inference(trivial_inequality_removal,[],[f1336])).
% 6.53/1.24  fof(f1336,plain,(
% 6.53/1.24    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(sK1,sK0) | (~spl5_6 | ~spl5_16 | spl5_35 | ~spl5_63)),
% 6.53/1.24    inference(forward_demodulation,[],[f1292,f292])).
% 6.53/1.24  fof(f292,plain,(
% 6.53/1.24    k1_xboole_0 = k3_xboole_0(sK1,sK2) | (~spl5_6 | ~spl5_16)),
% 6.53/1.24    inference(superposition,[],[f141,f83])).
% 6.53/1.24  fof(f83,plain,(
% 6.53/1.24    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl5_6),
% 6.53/1.24    inference(avatar_component_clause,[],[f82])).
% 6.53/1.24  fof(f82,plain,(
% 6.53/1.24    spl5_6 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 6.53/1.24  fof(f141,plain,(
% 6.53/1.24    k1_xboole_0 = k3_xboole_0(sK2,sK1) | ~spl5_16),
% 6.53/1.24    inference(avatar_component_clause,[],[f139])).
% 6.53/1.24  fof(f139,plain,(
% 6.53/1.24    spl5_16 <=> k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 6.53/1.24  fof(f1292,plain,(
% 6.53/1.24    k1_xboole_0 != k3_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0) | (spl5_35 | ~spl5_63)),
% 6.53/1.24    inference(superposition,[],[f358,f1273])).
% 6.53/1.24  fof(f1273,plain,(
% 6.53/1.24    ( ! [X10,X11,X9] : (k3_xboole_0(X9,X11) = k3_xboole_0(k2_xboole_0(X10,X11),X9) | ~r1_xboole_0(X9,X10)) ) | ~spl5_63),
% 6.53/1.24    inference(avatar_component_clause,[],[f1272])).
% 6.53/1.24  fof(f1272,plain,(
% 6.53/1.24    spl5_63 <=> ! [X9,X11,X10] : (k3_xboole_0(X9,X11) = k3_xboole_0(k2_xboole_0(X10,X11),X9) | ~r1_xboole_0(X9,X10))),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).
% 6.53/1.24  fof(f358,plain,(
% 6.53/1.24    k1_xboole_0 != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) | spl5_35),
% 6.53/1.24    inference(avatar_component_clause,[],[f356])).
% 6.53/1.24  fof(f356,plain,(
% 6.53/1.24    spl5_35 <=> k1_xboole_0 = k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 6.53/1.24  fof(f3642,plain,(
% 6.53/1.24    spl5_82 | ~spl5_16 | ~spl5_36 | ~spl5_76 | ~spl5_81),
% 6.53/1.24    inference(avatar_split_clause,[],[f3638,f3634,f3249,f368,f139,f3640])).
% 6.53/1.24  fof(f368,plain,(
% 6.53/1.24    spl5_36 <=> ! [X0] : r1_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(X0,sK1))),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 6.53/1.24  fof(f3249,plain,(
% 6.53/1.24    spl5_76 <=> ! [X7,X8,X6] : (k1_xboole_0 = k3_xboole_0(X6,k3_xboole_0(X7,X8)) | ~r1_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X8)))),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).
% 6.53/1.24  fof(f3634,plain,(
% 6.53/1.24    spl5_81 <=> ! [X1,X0,X2] : (k3_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(X0,k3_xboole_0(X2,k1_xboole_0)) | ~r1_xboole_0(X0,X1))),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).
% 6.53/1.24  fof(f3638,plain,(
% 6.53/1.24    ( ! [X2,X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1)) ) | (~spl5_16 | ~spl5_36 | ~spl5_76 | ~spl5_81)),
% 6.53/1.24    inference(forward_demodulation,[],[f3637,f3314])).
% 6.53/1.24  fof(f3314,plain,(
% 6.53/1.24    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | (~spl5_16 | ~spl5_36 | ~spl5_76)),
% 6.53/1.24    inference(forward_demodulation,[],[f3252,f141])).
% 6.53/1.24  fof(f3252,plain,(
% 6.53/1.24    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(sK2,sK1))) ) | (~spl5_36 | ~spl5_76)),
% 6.53/1.24    inference(unit_resulting_resolution,[],[f369,f3250])).
% 6.53/1.24  fof(f3250,plain,(
% 6.53/1.24    ( ! [X6,X8,X7] : (~r1_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X8)) | k1_xboole_0 = k3_xboole_0(X6,k3_xboole_0(X7,X8))) ) | ~spl5_76),
% 6.53/1.24    inference(avatar_component_clause,[],[f3249])).
% 6.53/1.24  fof(f369,plain,(
% 6.53/1.24    ( ! [X0] : (r1_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(X0,sK1))) ) | ~spl5_36),
% 6.53/1.24    inference(avatar_component_clause,[],[f368])).
% 6.53/1.24  fof(f3637,plain,(
% 6.53/1.24    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(X0,k1_xboole_0) | ~r1_xboole_0(X0,X1)) ) | (~spl5_16 | ~spl5_36 | ~spl5_76 | ~spl5_81)),
% 6.53/1.24    inference(forward_demodulation,[],[f3635,f3314])).
% 6.53/1.24  fof(f3635,plain,(
% 6.53/1.24    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(X0,k3_xboole_0(X2,k1_xboole_0)) | ~r1_xboole_0(X0,X1)) ) | ~spl5_81),
% 6.53/1.24    inference(avatar_component_clause,[],[f3634])).
% 6.53/1.24  fof(f3636,plain,(
% 6.53/1.24    spl5_81 | ~spl5_13 | ~spl5_19 | ~spl5_23),
% 6.53/1.24    inference(avatar_split_clause,[],[f267,f208,f162,f110,f3634])).
% 6.53/1.24  fof(f110,plain,(
% 6.53/1.24    spl5_13 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 6.53/1.24  fof(f162,plain,(
% 6.53/1.24    spl5_19 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 6.53/1.24  fof(f208,plain,(
% 6.53/1.24    spl5_23 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 6.53/1.24  fof(f267,plain,(
% 6.53/1.24    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(X0,k3_xboole_0(X2,k1_xboole_0)) | ~r1_xboole_0(X0,X1)) ) | (~spl5_13 | ~spl5_19 | ~spl5_23)),
% 6.53/1.24    inference(forward_demodulation,[],[f240,f163])).
% 6.53/1.24  fof(f163,plain,(
% 6.53/1.24    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) ) | ~spl5_19),
% 6.53/1.24    inference(avatar_component_clause,[],[f162])).
% 6.53/1.24  fof(f240,plain,(
% 6.53/1.24    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k3_xboole_0(X0,X2),k1_xboole_0) | ~r1_xboole_0(X0,X1)) ) | (~spl5_13 | ~spl5_23)),
% 6.53/1.24    inference(superposition,[],[f209,f111])).
% 6.53/1.24  fof(f111,plain,(
% 6.53/1.24    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) ) | ~spl5_13),
% 6.53/1.24    inference(avatar_component_clause,[],[f110])).
% 6.53/1.24  fof(f209,plain,(
% 6.53/1.24    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) ) | ~spl5_23),
% 6.53/1.24    inference(avatar_component_clause,[],[f208])).
% 6.53/1.24  fof(f3251,plain,(
% 6.53/1.24    spl5_76 | ~spl5_13 | ~spl5_23),
% 6.53/1.24    inference(avatar_split_clause,[],[f248,f208,f110,f3249])).
% 6.53/1.24  fof(f248,plain,(
% 6.53/1.24    ( ! [X6,X8,X7] : (k1_xboole_0 = k3_xboole_0(X6,k3_xboole_0(X7,X8)) | ~r1_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X8))) ) | (~spl5_13 | ~spl5_23)),
% 6.53/1.24    inference(superposition,[],[f209,f111])).
% 6.53/1.24  fof(f1274,plain,(
% 6.53/1.24    spl5_63 | ~spl5_6 | ~spl5_20),
% 6.53/1.24    inference(avatar_split_clause,[],[f214,f175,f82,f1272])).
% 6.53/1.24  fof(f175,plain,(
% 6.53/1.24    spl5_20 <=> ! [X1,X0,X2] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1))),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 6.53/1.24  fof(f214,plain,(
% 6.53/1.24    ( ! [X10,X11,X9] : (k3_xboole_0(X9,X11) = k3_xboole_0(k2_xboole_0(X10,X11),X9) | ~r1_xboole_0(X9,X10)) ) | (~spl5_6 | ~spl5_20)),
% 6.53/1.24    inference(superposition,[],[f176,f83])).
% 6.53/1.24  fof(f176,plain,(
% 6.53/1.24    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) ) | ~spl5_20),
% 6.53/1.24    inference(avatar_component_clause,[],[f175])).
% 6.53/1.24  fof(f541,plain,(
% 6.53/1.24    spl5_44 | ~spl5_6 | ~spl5_14),
% 6.53/1.24    inference(avatar_split_clause,[],[f146,f114,f82,f539])).
% 6.53/1.24  fof(f146,plain,(
% 6.53/1.24    ( ! [X4,X5] : (k1_xboole_0 != k3_xboole_0(X5,X4) | r1_xboole_0(X4,X5)) ) | (~spl5_6 | ~spl5_14)),
% 6.53/1.24    inference(superposition,[],[f115,f83])).
% 6.53/1.24  fof(f496,plain,(
% 6.53/1.24    spl5_42 | ~spl5_6 | ~spl5_13),
% 6.53/1.24    inference(avatar_split_clause,[],[f132,f110,f82,f494])).
% 6.53/1.24  fof(f132,plain,(
% 6.53/1.24    ( ! [X4,X5] : (k1_xboole_0 = k3_xboole_0(X5,X4) | ~r1_xboole_0(X4,X5)) ) | (~spl5_6 | ~spl5_13)),
% 6.53/1.24    inference(superposition,[],[f111,f83])).
% 6.53/1.24  fof(f425,plain,(
% 6.53/1.24    spl5_39 | ~spl5_4 | ~spl5_12),
% 6.53/1.24    inference(avatar_split_clause,[],[f124,f106,f73,f422])).
% 6.53/1.24  fof(f73,plain,(
% 6.53/1.24    spl5_4 <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 6.53/1.24  fof(f106,plain,(
% 6.53/1.24    spl5_12 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 6.53/1.24  fof(f124,plain,(
% 6.53/1.24    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | (~spl5_4 | ~spl5_12)),
% 6.53/1.24    inference(unit_resulting_resolution,[],[f75,f107])).
% 6.53/1.24  fof(f107,plain,(
% 6.53/1.24    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl5_12),
% 6.53/1.24    inference(avatar_component_clause,[],[f106])).
% 6.53/1.24  fof(f75,plain,(
% 6.53/1.24    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | ~spl5_4),
% 6.53/1.24    inference(avatar_component_clause,[],[f73])).
% 6.53/1.24  fof(f370,plain,(
% 6.53/1.24    spl5_36 | ~spl5_2 | ~spl5_18),
% 6.53/1.24    inference(avatar_split_clause,[],[f165,f153,f63,f368])).
% 6.53/1.24  fof(f63,plain,(
% 6.53/1.24    spl5_2 <=> r1_xboole_0(sK2,sK1)),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 6.53/1.24  fof(f153,plain,(
% 6.53/1.24    spl5_18 <=> ! [X1,X0,X2] : (r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1))),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 6.53/1.24  fof(f165,plain,(
% 6.53/1.24    ( ! [X0] : (r1_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(X0,sK1))) ) | (~spl5_2 | ~spl5_18)),
% 6.53/1.24    inference(unit_resulting_resolution,[],[f65,f154])).
% 6.53/1.24  fof(f154,plain,(
% 6.53/1.24    ( ! [X2,X0,X1] : (r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl5_18),
% 6.53/1.24    inference(avatar_component_clause,[],[f153])).
% 6.53/1.24  fof(f65,plain,(
% 6.53/1.24    r1_xboole_0(sK2,sK1) | ~spl5_2),
% 6.53/1.24    inference(avatar_component_clause,[],[f63])).
% 6.53/1.24  fof(f359,plain,(
% 6.53/1.24    ~spl5_35 | spl5_3 | ~spl5_14),
% 6.53/1.24    inference(avatar_split_clause,[],[f143,f114,f68,f356])).
% 6.53/1.24  fof(f68,plain,(
% 6.53/1.24    spl5_3 <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 6.53/1.24  fof(f143,plain,(
% 6.53/1.24    k1_xboole_0 != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) | (spl5_3 | ~spl5_14)),
% 6.53/1.24    inference(unit_resulting_resolution,[],[f70,f115])).
% 6.53/1.24  fof(f70,plain,(
% 6.53/1.24    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) | spl5_3),
% 6.53/1.24    inference(avatar_component_clause,[],[f68])).
% 6.53/1.24  fof(f322,plain,(
% 6.53/1.24    spl5_29 | ~spl5_7 | spl5_27),
% 6.53/1.24    inference(avatar_split_clause,[],[f313,f309,f86,f319])).
% 6.53/1.24  fof(f86,plain,(
% 6.53/1.24    spl5_7 <=> ! [X1,X0] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 6.53/1.24  fof(f309,plain,(
% 6.53/1.24    spl5_27 <=> r2_hidden(sK3,sK1)),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 6.53/1.24  fof(f313,plain,(
% 6.53/1.24    r1_xboole_0(k1_tarski(sK3),sK1) | (~spl5_7 | spl5_27)),
% 6.53/1.24    inference(unit_resulting_resolution,[],[f311,f87])).
% 6.53/1.24  fof(f87,plain,(
% 6.53/1.24    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) ) | ~spl5_7),
% 6.53/1.24    inference(avatar_component_clause,[],[f86])).
% 6.53/1.24  fof(f311,plain,(
% 6.53/1.24    ~r2_hidden(sK3,sK1) | spl5_27),
% 6.53/1.24    inference(avatar_component_clause,[],[f309])).
% 6.53/1.24  fof(f312,plain,(
% 6.53/1.24    ~spl5_27 | ~spl5_1 | ~spl5_2 | ~spl5_15),
% 6.53/1.24    inference(avatar_split_clause,[],[f156,f118,f63,f58,f309])).
% 6.53/1.24  fof(f58,plain,(
% 6.53/1.24    spl5_1 <=> r2_hidden(sK3,sK2)),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 6.53/1.24  fof(f118,plain,(
% 6.53/1.24    spl5_15 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))),
% 6.53/1.24    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 6.53/1.24  fof(f156,plain,(
% 6.53/1.24    ~r2_hidden(sK3,sK1) | (~spl5_1 | ~spl5_2 | ~spl5_15)),
% 6.53/1.24    inference(unit_resulting_resolution,[],[f60,f65,f119])).
% 6.53/1.24  fof(f119,plain,(
% 6.53/1.24    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) ) | ~spl5_15),
% 6.53/1.24    inference(avatar_component_clause,[],[f118])).
% 6.53/1.24  fof(f60,plain,(
% 6.53/1.24    r2_hidden(sK3,sK2) | ~spl5_1),
% 6.53/1.24    inference(avatar_component_clause,[],[f58])).
% 6.53/1.24  fof(f210,plain,(
% 6.53/1.24    spl5_23),
% 6.53/1.24    inference(avatar_split_clause,[],[f50,f208])).
% 6.53/1.24  fof(f50,plain,(
% 6.53/1.24    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 6.53/1.24    inference(cnf_transformation,[],[f4])).
% 6.53/1.24  fof(f4,axiom,(
% 6.53/1.24    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 6.53/1.24    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_xboole_1)).
% 6.53/1.24  fof(f177,plain,(
% 6.53/1.24    spl5_20),
% 6.53/1.24    inference(avatar_split_clause,[],[f52,f175])).
% 6.53/1.24  fof(f52,plain,(
% 6.53/1.24    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 6.53/1.24    inference(cnf_transformation,[],[f27])).
% 6.53/1.24  fof(f27,plain,(
% 6.53/1.24    ! [X0,X1,X2] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1))),
% 6.53/1.24    inference(ennf_transformation,[],[f8])).
% 6.53/1.24  fof(f8,axiom,(
% 6.53/1.24    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 6.53/1.24    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).
% 6.53/1.24  fof(f164,plain,(
% 6.53/1.24    spl5_19),
% 6.53/1.24    inference(avatar_split_clause,[],[f49,f162])).
% 6.53/1.24  fof(f49,plain,(
% 6.53/1.24    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 6.53/1.24    inference(cnf_transformation,[],[f5])).
% 6.53/1.24  fof(f5,axiom,(
% 6.53/1.24    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 6.53/1.24    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 6.53/1.24  fof(f155,plain,(
% 6.53/1.24    spl5_18),
% 6.53/1.24    inference(avatar_split_clause,[],[f51,f153])).
% 6.53/1.24  fof(f51,plain,(
% 6.53/1.24    ( ! [X2,X0,X1] : (r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1)) )),
% 6.53/1.24    inference(cnf_transformation,[],[f26])).
% 6.53/1.24  fof(f26,plain,(
% 6.53/1.24    ! [X0,X1,X2] : (r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1))),
% 6.53/1.24    inference(ennf_transformation,[],[f7])).
% 6.53/1.24  fof(f7,axiom,(
% 6.53/1.24    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 6.53/1.24    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).
% 6.53/1.24  fof(f142,plain,(
% 6.53/1.24    spl5_16 | ~spl5_2 | ~spl5_13),
% 6.53/1.24    inference(avatar_split_clause,[],[f130,f110,f63,f139])).
% 6.53/1.24  fof(f130,plain,(
% 6.53/1.24    k1_xboole_0 = k3_xboole_0(sK2,sK1) | (~spl5_2 | ~spl5_13)),
% 6.53/1.24    inference(unit_resulting_resolution,[],[f65,f111])).
% 6.53/1.24  fof(f120,plain,(
% 6.53/1.24    spl5_15),
% 6.53/1.24    inference(avatar_split_clause,[],[f43,f118])).
% 6.53/1.24  fof(f43,plain,(
% 6.53/1.24    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 6.53/1.24    inference(cnf_transformation,[],[f31])).
% 6.53/1.24  fof(f31,plain,(
% 6.53/1.24    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 6.53/1.24    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f30])).
% 6.53/1.24  fof(f30,plain,(
% 6.53/1.24    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 6.53/1.24    introduced(choice_axiom,[])).
% 6.53/1.24  fof(f23,plain,(
% 6.53/1.24    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 6.53/1.24    inference(ennf_transformation,[],[f20])).
% 6.53/1.24  fof(f20,plain,(
% 6.53/1.24    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 6.53/1.24    inference(rectify,[],[f3])).
% 6.53/1.24  fof(f3,axiom,(
% 6.53/1.24    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 6.53/1.24    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 6.53/1.24  fof(f116,plain,(
% 6.53/1.24    spl5_14),
% 6.53/1.24    inference(avatar_split_clause,[],[f47,f114])).
% 6.53/1.24  fof(f47,plain,(
% 6.53/1.24    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 6.53/1.24    inference(cnf_transformation,[],[f32])).
% 6.53/1.24  fof(f32,plain,(
% 6.53/1.24    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 6.53/1.24    inference(nnf_transformation,[],[f2])).
% 6.53/1.24  fof(f2,axiom,(
% 6.53/1.24    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 6.53/1.24    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 6.53/1.24  fof(f112,plain,(
% 6.53/1.24    spl5_13),
% 6.53/1.24    inference(avatar_split_clause,[],[f46,f110])).
% 6.53/1.24  fof(f46,plain,(
% 6.53/1.24    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 6.53/1.24    inference(cnf_transformation,[],[f32])).
% 6.53/1.24  fof(f108,plain,(
% 6.53/1.24    spl5_12),
% 6.53/1.24    inference(avatar_split_clause,[],[f45,f106])).
% 6.53/1.24  fof(f45,plain,(
% 6.53/1.24    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 6.53/1.24    inference(cnf_transformation,[],[f25])).
% 6.53/1.24  fof(f25,plain,(
% 6.53/1.24    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 6.53/1.24    inference(ennf_transformation,[],[f6])).
% 6.53/1.24  fof(f6,axiom,(
% 6.53/1.24    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 6.53/1.24    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 6.53/1.24  fof(f88,plain,(
% 6.53/1.24    spl5_7),
% 6.53/1.24    inference(avatar_split_clause,[],[f44,f86])).
% 6.53/1.24  fof(f44,plain,(
% 6.53/1.24    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 6.53/1.24    inference(cnf_transformation,[],[f24])).
% 6.53/1.24  fof(f24,plain,(
% 6.53/1.24    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 6.53/1.24    inference(ennf_transformation,[],[f16])).
% 6.53/1.24  fof(f16,axiom,(
% 6.53/1.24    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 6.53/1.24    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 6.53/1.24  fof(f84,plain,(
% 6.53/1.24    spl5_6),
% 6.53/1.24    inference(avatar_split_clause,[],[f38,f82])).
% 6.53/1.24  fof(f38,plain,(
% 6.53/1.24    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.53/1.24    inference(cnf_transformation,[],[f1])).
% 6.53/1.24  fof(f1,axiom,(
% 6.53/1.24    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.53/1.24    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 6.53/1.24  fof(f76,plain,(
% 6.53/1.24    spl5_4),
% 6.53/1.24    inference(avatar_split_clause,[],[f33,f73])).
% 6.53/1.24  fof(f33,plain,(
% 6.53/1.24    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 6.53/1.24    inference(cnf_transformation,[],[f29])).
% 6.53/1.24  fof(f29,plain,(
% 6.53/1.24    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 6.53/1.24    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f28])).
% 6.53/1.24  fof(f28,plain,(
% 6.53/1.24    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 6.53/1.24    introduced(choice_axiom,[])).
% 6.53/1.24  fof(f22,plain,(
% 6.53/1.24    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 6.53/1.24    inference(flattening,[],[f21])).
% 6.53/1.24  fof(f21,plain,(
% 6.53/1.24    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 6.53/1.24    inference(ennf_transformation,[],[f19])).
% 6.53/1.24  fof(f19,negated_conjecture,(
% 6.53/1.24    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 6.53/1.24    inference(negated_conjecture,[],[f18])).
% 6.53/1.24  fof(f18,conjecture,(
% 6.53/1.24    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 6.53/1.24    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 6.53/1.24  fof(f71,plain,(
% 6.53/1.24    ~spl5_3),
% 6.53/1.24    inference(avatar_split_clause,[],[f36,f68])).
% 6.53/1.24  fof(f36,plain,(
% 6.53/1.24    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 6.53/1.24    inference(cnf_transformation,[],[f29])).
% 6.53/1.24  fof(f66,plain,(
% 6.53/1.24    spl5_2),
% 6.53/1.24    inference(avatar_split_clause,[],[f35,f63])).
% 6.53/1.24  fof(f35,plain,(
% 6.53/1.24    r1_xboole_0(sK2,sK1)),
% 6.53/1.24    inference(cnf_transformation,[],[f29])).
% 6.53/1.24  fof(f61,plain,(
% 6.53/1.24    spl5_1),
% 6.53/1.24    inference(avatar_split_clause,[],[f34,f58])).
% 6.53/1.24  fof(f34,plain,(
% 6.53/1.24    r2_hidden(sK3,sK2)),
% 6.53/1.24    inference(cnf_transformation,[],[f29])).
% 6.53/1.24  % SZS output end Proof for theBenchmark
% 6.53/1.24  % (17392)------------------------------
% 6.53/1.24  % (17392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.53/1.24  % (17392)Termination reason: Refutation
% 6.53/1.24  
% 6.53/1.24  % (17392)Memory used [KB]: 23794
% 6.53/1.24  % (17392)Time elapsed: 0.741 s
% 6.53/1.24  % (17392)------------------------------
% 6.53/1.24  % (17392)------------------------------
% 6.95/1.24  % (17386)Success in time 0.871 s
%------------------------------------------------------------------------------
