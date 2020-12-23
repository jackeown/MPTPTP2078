%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:17 EST 2020

% Result     : Theorem 14.19s
% Output     : Refutation 14.19s
% Verified   : 
% Statistics : Number of formulae       :  334 ( 689 expanded)
%              Number of leaves         :   81 ( 303 expanded)
%              Depth                    :    9
%              Number of atoms          :  986 (1908 expanded)
%              Number of equality atoms :  174 ( 442 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13651,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f130,f134,f142,f146,f150,f154,f162,f166,f171,f178,f186,f190,f206,f217,f225,f237,f241,f245,f265,f269,f277,f315,f337,f348,f352,f364,f368,f372,f402,f481,f499,f521,f540,f620,f644,f691,f737,f741,f834,f874,f1071,f1109,f1250,f1267,f2273,f2459,f2972,f3022,f3323,f5202,f6670,f6719,f6909,f7049,f7074,f7333,f8161,f12587,f13242,f13537,f13562,f13650])).

fof(f13650,plain,
    ( spl11_34
    | ~ spl11_42
    | ~ spl11_300 ),
    inference(avatar_contradiction_clause,[],[f13649])).

fof(f13649,plain,
    ( $false
    | spl11_34
    | ~ spl11_42
    | ~ spl11_300 ),
    inference(subsumption_resolution,[],[f13563,f367])).

fof(f367,plain,
    ( sP0(sK6,sK6,sK8)
    | ~ spl11_42 ),
    inference(avatar_component_clause,[],[f366])).

fof(f366,plain,
    ( spl11_42
  <=> sP0(sK6,sK6,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).

fof(f13563,plain,
    ( ~ sP0(sK6,sK6,sK8)
    | spl11_34
    | ~ spl11_300 ),
    inference(superposition,[],[f314,f6624])).

fof(f6624,plain,
    ( sK6 = sK7
    | ~ spl11_300 ),
    inference(avatar_component_clause,[],[f6623])).

fof(f6623,plain,
    ( spl11_300
  <=> sK6 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_300])])).

fof(f314,plain,
    ( ~ sP0(sK7,sK6,sK8)
    | spl11_34 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl11_34
  <=> sP0(sK7,sK6,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f13562,plain,
    ( spl11_300
    | ~ spl11_48
    | ~ spl11_444 ),
    inference(avatar_split_clause,[],[f13556,f13535,f479,f6623])).

fof(f479,plain,
    ( spl11_48
  <=> ! [X1,X3,X0,X2] :
        ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP4(X0,X1,X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_48])])).

fof(f13535,plain,
    ( spl11_444
  <=> sP4(sK7,sK6,sK6,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_444])])).

fof(f13556,plain,
    ( sK6 = sK7
    | ~ spl11_48
    | ~ spl11_444 ),
    inference(duplicate_literal_removal,[],[f13555])).

fof(f13555,plain,
    ( sK6 = sK7
    | sK6 = sK7
    | sK6 = sK7
    | ~ spl11_48
    | ~ spl11_444 ),
    inference(resolution,[],[f13536,f480])).

fof(f480,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ sP4(X0,X1,X2,X3)
        | X0 = X2
        | X0 = X3
        | X0 = X1 )
    | ~ spl11_48 ),
    inference(avatar_component_clause,[],[f479])).

fof(f13536,plain,
    ( sP4(sK7,sK6,sK6,sK6)
    | ~ spl11_444 ),
    inference(avatar_component_clause,[],[f13535])).

fof(f13537,plain,
    ( spl11_444
    | ~ spl11_41
    | ~ spl11_103
    | ~ spl11_443 ),
    inference(avatar_split_clause,[],[f13314,f13240,f1265,f362,f13535])).

fof(f362,plain,
    ( spl11_41
  <=> ! [X1,X3,X5,X0,X2] :
        ( sP4(X5,X2,X1,X0)
        | ~ r2_hidden(X5,X3)
        | ~ sP5(X0,X1,X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_41])])).

fof(f1265,plain,
    ( spl11_103
  <=> ! [X1,X0,X2] : sP5(X0,X1,X2,k4_enumset1(X1,X1,X1,X1,X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_103])])).

fof(f13240,plain,
    ( spl11_443
  <=> r2_hidden(sK7,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_443])])).

fof(f13314,plain,
    ( sP4(sK7,sK6,sK6,sK6)
    | ~ spl11_41
    | ~ spl11_103
    | ~ spl11_443 ),
    inference(unit_resulting_resolution,[],[f1266,f13241,f363])).

fof(f363,plain,
    ( ! [X2,X0,X5,X3,X1] :
        ( ~ sP5(X0,X1,X2,X3)
        | ~ r2_hidden(X5,X3)
        | sP4(X5,X2,X1,X0) )
    | ~ spl11_41 ),
    inference(avatar_component_clause,[],[f362])).

fof(f13241,plain,
    ( r2_hidden(sK7,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6))
    | ~ spl11_443 ),
    inference(avatar_component_clause,[],[f13240])).

fof(f1266,plain,
    ( ! [X2,X0,X1] : sP5(X0,X1,X2,k4_enumset1(X1,X1,X1,X1,X0,X2))
    | ~ spl11_103 ),
    inference(avatar_component_clause,[],[f1265])).

fof(f13242,plain,
    ( spl11_443
    | ~ spl11_27
    | ~ spl11_196
    | ~ spl11_430 ),
    inference(avatar_split_clause,[],[f13177,f12585,f3321,f267,f13240])).

fof(f267,plain,
    ( spl11_27
  <=> ! [X1,X0,X2,X4] :
        ( r2_hidden(X4,X2)
        | ~ sP1(X1,X4,X0)
        | ~ sP2(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).

fof(f3321,plain,
    ( spl11_196
  <=> sP2(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_196])])).

fof(f12585,plain,
    ( spl11_430
  <=> ! [X1,X0] : sP1(sK8,sK7,k4_enumset1(X0,X0,X0,X0,X1,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_430])])).

fof(f13177,plain,
    ( r2_hidden(sK7,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6))
    | ~ spl11_27
    | ~ spl11_196
    | ~ spl11_430 ),
    inference(unit_resulting_resolution,[],[f3322,f12586,f268])).

fof(f268,plain,
    ( ! [X4,X2,X0,X1] :
        ( ~ sP2(X0,X1,X2)
        | ~ sP1(X1,X4,X0)
        | r2_hidden(X4,X2) )
    | ~ spl11_27 ),
    inference(avatar_component_clause,[],[f267])).

fof(f12586,plain,
    ( ! [X0,X1] : sP1(sK8,sK7,k4_enumset1(X0,X0,X0,X0,X1,sK7))
    | ~ spl11_430 ),
    inference(avatar_component_clause,[],[f12585])).

fof(f3322,plain,
    ( sP2(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6))
    | ~ spl11_196 ),
    inference(avatar_component_clause,[],[f3321])).

fof(f12587,plain,
    ( spl11_430
    | ~ spl11_21
    | spl11_46
    | ~ spl11_79 ),
    inference(avatar_split_clause,[],[f8184,f832,f448,f223,f12585])).

fof(f223,plain,
    ( spl11_21
  <=> ! [X1,X0,X2] :
        ( sP1(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f448,plain,
    ( spl11_46
  <=> r2_hidden(sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f832,plain,
    ( spl11_79
  <=> ! [X1,X0,X2] : r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_79])])).

fof(f8184,plain,
    ( ! [X0,X1] : sP1(sK8,sK7,k4_enumset1(X0,X0,X0,X0,X1,sK7))
    | ~ spl11_21
    | spl11_46
    | ~ spl11_79 ),
    inference(unit_resulting_resolution,[],[f833,f449,f224])).

fof(f224,plain,
    ( ! [X2,X0,X1] :
        ( sP1(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
    | ~ spl11_21 ),
    inference(avatar_component_clause,[],[f223])).

fof(f449,plain,
    ( ~ r2_hidden(sK7,sK8)
    | spl11_46 ),
    inference(avatar_component_clause,[],[f448])).

fof(f833,plain,
    ( ! [X2,X0,X1] : r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0))
    | ~ spl11_79 ),
    inference(avatar_component_clause,[],[f832])).

fof(f8161,plain,
    ( ~ spl11_12
    | ~ spl11_154
    | ~ spl11_186
    | spl11_206
    | ~ spl11_309 ),
    inference(avatar_contradiction_clause,[],[f8160])).

fof(f8160,plain,
    ( $false
    | ~ spl11_12
    | ~ spl11_154
    | ~ spl11_186
    | spl11_206
    | ~ spl11_309 ),
    inference(subsumption_resolution,[],[f8099,f7596])).

fof(f7596,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK7,k5_xboole_0(sK8,k4_enumset1(X0,X0,X0,X0,X1,sK7)))
    | ~ spl11_12
    | ~ spl11_309 ),
    inference(unit_resulting_resolution,[],[f7332,f177])).

fof(f177,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
        | sP3(X2,X0,X1) )
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl11_12
  <=> ! [X1,X0,X2] :
        ( sP3(X2,X0,X1)
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f7332,plain,
    ( ! [X0,X1] : ~ sP3(k4_enumset1(X0,X0,X0,X0,X1,sK7),sK7,sK8)
    | ~ spl11_309 ),
    inference(avatar_component_clause,[],[f7331])).

fof(f7331,plain,
    ( spl11_309
  <=> ! [X1,X0] : ~ sP3(k4_enumset1(X0,X0,X0,X0,X1,sK7),sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_309])])).

fof(f8099,plain,
    ( r2_hidden(sK7,k5_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)))
    | ~ spl11_154
    | ~ spl11_186
    | spl11_206 ),
    inference(unit_resulting_resolution,[],[f3021,f8096,f2458])).

fof(f2458,plain,
    ( ! [X14,X15,X13,X16] :
        ( ~ sP3(X15,X16,X14)
        | k4_enumset1(X16,X16,X16,X16,X16,X16) = k3_xboole_0(k4_enumset1(X16,X16,X16,X16,X16,X13),k5_xboole_0(X14,X15))
        | r2_hidden(X13,k5_xboole_0(X14,X15)) )
    | ~ spl11_154 ),
    inference(avatar_component_clause,[],[f2457])).

fof(f2457,plain,
    ( spl11_154
  <=> ! [X16,X13,X15,X14] :
        ( r2_hidden(X13,k5_xboole_0(X14,X15))
        | k4_enumset1(X16,X16,X16,X16,X16,X16) = k3_xboole_0(k4_enumset1(X16,X16,X16,X16,X16,X13),k5_xboole_0(X14,X15))
        | ~ sP3(X15,X16,X14) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_154])])).

fof(f8096,plain,
    ( k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) != k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k5_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)))
    | spl11_206 ),
    inference(avatar_component_clause,[],[f3695])).

fof(f3695,plain,
    ( spl11_206
  <=> k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) = k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k5_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_206])])).

fof(f3021,plain,
    ( ! [X0,X1] : sP3(k4_enumset1(sK6,sK6,sK6,sK6,X0,X1),sK6,sK8)
    | ~ spl11_186 ),
    inference(avatar_component_clause,[],[f3020])).

fof(f3020,plain,
    ( spl11_186
  <=> ! [X1,X0] : sP3(k4_enumset1(sK6,sK6,sK6,sK6,X0,X1),sK6,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_186])])).

fof(f7333,plain,
    ( spl11_309
    | ~ spl11_23
    | ~ spl11_46
    | ~ spl11_79 ),
    inference(avatar_split_clause,[],[f7091,f832,f448,f235,f7331])).

fof(f235,plain,
    ( spl11_23
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2)
        | ~ sP3(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f7091,plain,
    ( ! [X0,X1] : ~ sP3(k4_enumset1(X0,X0,X0,X0,X1,sK7),sK7,sK8)
    | ~ spl11_23
    | ~ spl11_46
    | ~ spl11_79 ),
    inference(unit_resulting_resolution,[],[f833,f7073,f236])).

fof(f236,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP3(X0,X1,X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X1,X0) )
    | ~ spl11_23 ),
    inference(avatar_component_clause,[],[f235])).

fof(f7073,plain,
    ( r2_hidden(sK7,sK8)
    | ~ spl11_46 ),
    inference(avatar_component_clause,[],[f448])).

fof(f7074,plain,
    ( spl11_300
    | spl11_46
    | ~ spl11_17
    | ~ spl11_34 ),
    inference(avatar_split_clause,[],[f6619,f313,f204,f448,f6623])).

fof(f204,plain,
    ( spl11_17
  <=> ! [X1,X0,X2] :
        ( X0 = X1
        | r2_hidden(X0,X2)
        | ~ sP0(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f6619,plain,
    ( r2_hidden(sK7,sK8)
    | sK6 = sK7
    | ~ spl11_17
    | ~ spl11_34 ),
    inference(resolution,[],[f336,f205])).

fof(f205,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP0(X0,X1,X2)
        | r2_hidden(X0,X2)
        | X0 = X1 )
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f204])).

fof(f336,plain,
    ( sP0(sK7,sK6,sK8)
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f313])).

fof(f7049,plain,
    ( spl11_36
    | ~ spl11_206
    | ~ spl11_264 ),
    inference(avatar_contradiction_clause,[],[f7048])).

fof(f7048,plain,
    ( $false
    | spl11_36
    | ~ spl11_206
    | ~ spl11_264 ),
    inference(subsumption_resolution,[],[f6953,f3696])).

fof(f3696,plain,
    ( k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) = k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k5_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)))
    | ~ spl11_206 ),
    inference(avatar_component_clause,[],[f3695])).

fof(f6953,plain,
    ( k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) != k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k5_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)))
    | spl11_36
    | ~ spl11_264 ),
    inference(superposition,[],[f329,f5201])).

fof(f5201,plain,
    ( ! [X2,X3] : k5_xboole_0(X3,k3_xboole_0(X2,X3)) = k3_xboole_0(X3,k5_xboole_0(X2,X3))
    | ~ spl11_264 ),
    inference(avatar_component_clause,[],[f5200])).

fof(f5200,plain,
    ( spl11_264
  <=> ! [X3,X2] : k5_xboole_0(X3,k3_xboole_0(X2,X3)) = k3_xboole_0(X3,k5_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_264])])).

fof(f329,plain,
    ( k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) != k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)))
    | spl11_36 ),
    inference(avatar_component_clause,[],[f328])).

fof(f328,plain,
    ( spl11_36
  <=> k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) = k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_36])])).

fof(f6909,plain,
    ( ~ spl11_6
    | ~ spl11_142
    | ~ spl11_180
    | ~ spl11_264
    | spl11_301 ),
    inference(avatar_contradiction_clause,[],[f6908])).

fof(f6908,plain,
    ( $false
    | ~ spl11_6
    | ~ spl11_142
    | ~ spl11_180
    | ~ spl11_264
    | spl11_301 ),
    inference(subsumption_resolution,[],[f6813,f3207])).

fof(f3207,plain,
    ( ! [X0,X1] : k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) = k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6),k5_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,X0,X1)))
    | ~ spl11_6
    | ~ spl11_142
    | ~ spl11_180 ),
    inference(forward_demodulation,[],[f3199,f149])).

fof(f149,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl11_6
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f3199,plain,
    ( ! [X0,X1] : k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) = k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6),k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,X0,X1),sK8))
    | ~ spl11_142
    | ~ spl11_180 ),
    inference(unit_resulting_resolution,[],[f2971,f2272])).

fof(f2272,plain,
    ( ! [X4,X5,X3] :
        ( ~ sP3(X5,X3,X4)
        | k4_enumset1(X3,X3,X3,X3,X3,X3) = k3_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X3),k5_xboole_0(X4,X5)) )
    | ~ spl11_142 ),
    inference(avatar_component_clause,[],[f2271])).

fof(f2271,plain,
    ( spl11_142
  <=> ! [X3,X5,X4] :
        ( k4_enumset1(X3,X3,X3,X3,X3,X3) = k3_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X3),k5_xboole_0(X4,X5))
        | ~ sP3(X5,X3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_142])])).

fof(f2971,plain,
    ( ! [X0,X1] : sP3(sK8,sK6,k4_enumset1(sK6,sK6,sK6,sK6,X0,X1))
    | ~ spl11_180 ),
    inference(avatar_component_clause,[],[f2970])).

fof(f2970,plain,
    ( spl11_180
  <=> ! [X1,X0] : sP3(sK8,sK6,k4_enumset1(sK6,sK6,sK6,sK6,X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_180])])).

fof(f6813,plain,
    ( k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) != k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6),k5_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6)))
    | ~ spl11_264
    | spl11_301 ),
    inference(superposition,[],[f6718,f5201])).

fof(f6718,plain,
    ( k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) != k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6),k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6)))
    | spl11_301 ),
    inference(avatar_component_clause,[],[f6717])).

fof(f6717,plain,
    ( spl11_301
  <=> k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) = k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6),k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_301])])).

fof(f6719,plain,
    ( ~ spl11_301
    | spl11_36
    | ~ spl11_300 ),
    inference(avatar_split_clause,[],[f6671,f6623,f328,f6717])).

fof(f6671,plain,
    ( k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) != k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6),k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6)))
    | spl11_36
    | ~ spl11_300 ),
    inference(forward_demodulation,[],[f329,f6624])).

fof(f6670,plain,
    ( ~ spl11_36
    | ~ spl11_7
    | spl11_33 ),
    inference(avatar_split_clause,[],[f6614,f310,f152,f328])).

fof(f152,plain,
    ( spl11_7
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f310,plain,
    ( spl11_33
  <=> k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) = k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).

fof(f6614,plain,
    ( k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) != k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)))
    | ~ spl11_7
    | spl11_33 ),
    inference(forward_demodulation,[],[f311,f153])).

fof(f153,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f152])).

fof(f311,plain,
    ( k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) != k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),sK8))
    | spl11_33 ),
    inference(avatar_component_clause,[],[f310])).

fof(f5202,plain,
    ( spl11_264
    | ~ spl11_6
    | ~ spl11_101 ),
    inference(avatar_split_clause,[],[f1312,f1248,f148,f5200])).

fof(f1248,plain,
    ( spl11_101
  <=> ! [X1,X0] : k5_xboole_0(k3_xboole_0(X1,X0),X0) = k3_xboole_0(X0,k5_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_101])])).

fof(f1312,plain,
    ( ! [X2,X3] : k5_xboole_0(X3,k3_xboole_0(X2,X3)) = k3_xboole_0(X3,k5_xboole_0(X2,X3))
    | ~ spl11_6
    | ~ spl11_101 ),
    inference(superposition,[],[f1249,f149])).

fof(f1249,plain,
    ( ! [X0,X1] : k5_xboole_0(k3_xboole_0(X1,X0),X0) = k3_xboole_0(X0,k5_xboole_0(X1,X0))
    | ~ spl11_101 ),
    inference(avatar_component_clause,[],[f1248])).

fof(f3323,plain,
    ( spl11_196
    | ~ spl11_15
    | ~ spl11_36 ),
    inference(avatar_split_clause,[],[f383,f328,f188,f3321])).

fof(f188,plain,
    ( spl11_15
  <=> ! [X1,X2] : sP2(X1,X2,k5_xboole_0(X1,k3_xboole_0(X2,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f383,plain,
    ( sP2(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6))
    | ~ spl11_15
    | ~ spl11_36 ),
    inference(superposition,[],[f189,f371])).

fof(f371,plain,
    ( k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) = k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)))
    | ~ spl11_36 ),
    inference(avatar_component_clause,[],[f328])).

fof(f189,plain,
    ( ! [X2,X1] : sP2(X1,X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f188])).

fof(f3022,plain,
    ( spl11_186
    | ~ spl11_25
    | spl11_38
    | ~ spl11_82 ),
    inference(avatar_split_clause,[],[f1157,f872,f346,f243,f3020])).

fof(f243,plain,
    ( spl11_25
  <=> ! [X1,X0,X2] :
        ( sP3(X0,X1,X2)
        | r2_hidden(X1,X2)
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).

fof(f346,plain,
    ( spl11_38
  <=> r2_hidden(sK6,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).

fof(f872,plain,
    ( spl11_82
  <=> ! [X1,X0,X2] : r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_82])])).

fof(f1157,plain,
    ( ! [X0,X1] : sP3(k4_enumset1(sK6,sK6,sK6,sK6,X0,X1),sK6,sK8)
    | ~ spl11_25
    | spl11_38
    | ~ spl11_82 ),
    inference(unit_resulting_resolution,[],[f873,f347,f244])).

fof(f244,plain,
    ( ! [X2,X0,X1] :
        ( sP3(X0,X1,X2)
        | r2_hidden(X1,X2)
        | ~ r2_hidden(X1,X0) )
    | ~ spl11_25 ),
    inference(avatar_component_clause,[],[f243])).

fof(f347,plain,
    ( ~ r2_hidden(sK6,sK8)
    | spl11_38 ),
    inference(avatar_component_clause,[],[f346])).

fof(f873,plain,
    ( ! [X2,X0,X1] : r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2))
    | ~ spl11_82 ),
    inference(avatar_component_clause,[],[f872])).

fof(f2972,plain,
    ( spl11_180
    | ~ spl11_24
    | spl11_38
    | ~ spl11_82 ),
    inference(avatar_split_clause,[],[f1150,f872,f346,f239,f2970])).

fof(f239,plain,
    ( spl11_24
  <=> ! [X1,X0,X2] :
        ( sP3(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f1150,plain,
    ( ! [X0,X1] : sP3(sK8,sK6,k4_enumset1(sK6,sK6,sK6,sK6,X0,X1))
    | ~ spl11_24
    | spl11_38
    | ~ spl11_82 ),
    inference(unit_resulting_resolution,[],[f873,f347,f240])).

fof(f240,plain,
    ( ! [X2,X0,X1] :
        ( sP3(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f239])).

fof(f2459,plain,
    ( spl11_154
    | ~ spl11_14
    | ~ spl11_73 ),
    inference(avatar_split_clause,[],[f809,f739,f184,f2457])).

fof(f184,plain,
    ( spl11_14
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ~ sP3(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f739,plain,
    ( spl11_73
  <=> ! [X1,X0,X2] :
        ( k4_enumset1(X0,X0,X0,X0,X0,X0) = k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1)
        | r2_hidden(X2,X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_73])])).

fof(f809,plain,
    ( ! [X14,X15,X13,X16] :
        ( r2_hidden(X13,k5_xboole_0(X14,X15))
        | k4_enumset1(X16,X16,X16,X16,X16,X16) = k3_xboole_0(k4_enumset1(X16,X16,X16,X16,X16,X13),k5_xboole_0(X14,X15))
        | ~ sP3(X15,X16,X14) )
    | ~ spl11_14
    | ~ spl11_73 ),
    inference(resolution,[],[f740,f185])).

fof(f185,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ~ sP3(X2,X0,X1) )
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f184])).

fof(f740,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | r2_hidden(X2,X1)
        | k4_enumset1(X0,X0,X0,X0,X0,X0) = k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) )
    | ~ spl11_73 ),
    inference(avatar_component_clause,[],[f739])).

fof(f2273,plain,
    ( spl11_142
    | ~ spl11_14
    | ~ spl11_63 ),
    inference(avatar_split_clause,[],[f636,f618,f184,f2271])).

fof(f618,plain,
    ( spl11_63
  <=> ! [X1,X2] :
        ( k4_enumset1(X2,X2,X2,X2,X2,X2) = k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),X1)
        | ~ r2_hidden(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_63])])).

fof(f636,plain,
    ( ! [X4,X5,X3] :
        ( k4_enumset1(X3,X3,X3,X3,X3,X3) = k3_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X3),k5_xboole_0(X4,X5))
        | ~ sP3(X5,X3,X4) )
    | ~ spl11_14
    | ~ spl11_63 ),
    inference(resolution,[],[f619,f185])).

fof(f619,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,X1)
        | k4_enumset1(X2,X2,X2,X2,X2,X2) = k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),X1) )
    | ~ spl11_63 ),
    inference(avatar_component_clause,[],[f618])).

fof(f1267,plain,
    ( spl11_103
    | ~ spl11_29
    | ~ spl11_53 ),
    inference(avatar_split_clause,[],[f545,f538,f275,f1265])).

fof(f275,plain,
    ( spl11_29
  <=> ! [X1,X0,X2] : sP5(X0,X1,X2,k4_enumset1(X0,X0,X0,X0,X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).

fof(f538,plain,
    ( spl11_53
  <=> ! [X1,X0,X2] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X1,X1,X1,X1,X0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_53])])).

fof(f545,plain,
    ( ! [X2,X0,X1] : sP5(X0,X1,X2,k4_enumset1(X1,X1,X1,X1,X0,X2))
    | ~ spl11_29
    | ~ spl11_53 ),
    inference(superposition,[],[f276,f539])).

fof(f539,plain,
    ( ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X1,X1,X1,X1,X0,X2)
    | ~ spl11_53 ),
    inference(avatar_component_clause,[],[f538])).

fof(f276,plain,
    ( ! [X2,X0,X1] : sP5(X0,X1,X2,k4_enumset1(X0,X0,X0,X0,X1,X2))
    | ~ spl11_29 ),
    inference(avatar_component_clause,[],[f275])).

fof(f1250,plain,
    ( spl11_101
    | ~ spl11_1
    | ~ spl11_7
    | ~ spl11_39 ),
    inference(avatar_split_clause,[],[f435,f350,f152,f128,f1248])).

fof(f128,plain,
    ( spl11_1
  <=> ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f350,plain,
    ( spl11_39
  <=> ! [X1,X0,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_39])])).

fof(f435,plain,
    ( ! [X0,X1] : k5_xboole_0(k3_xboole_0(X1,X0),X0) = k3_xboole_0(X0,k5_xboole_0(X1,X0))
    | ~ spl11_1
    | ~ spl11_7
    | ~ spl11_39 ),
    inference(forward_demodulation,[],[f419,f153])).

fof(f419,plain,
    ( ! [X0,X1] : k5_xboole_0(k3_xboole_0(X1,X0),X0) = k3_xboole_0(k5_xboole_0(X1,X0),X0)
    | ~ spl11_1
    | ~ spl11_39 ),
    inference(superposition,[],[f351,f129])).

fof(f129,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f128])).

fof(f351,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)
    | ~ spl11_39 ),
    inference(avatar_component_clause,[],[f350])).

fof(f1109,plain,
    ( ~ spl11_72
    | ~ spl11_82
    | ~ spl11_93 ),
    inference(avatar_contradiction_clause,[],[f1108])).

fof(f1108,plain,
    ( $false
    | ~ spl11_72
    | ~ spl11_82
    | ~ spl11_93 ),
    inference(subsumption_resolution,[],[f1097,f736])).

fof(f736,plain,
    ( ! [X0] : ~ sP3(k3_xboole_0(sK8,X0),sK6,X0)
    | ~ spl11_72 ),
    inference(avatar_component_clause,[],[f735])).

fof(f735,plain,
    ( spl11_72
  <=> ! [X0] : ~ sP3(k3_xboole_0(sK8,X0),sK6,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_72])])).

fof(f1097,plain,
    ( sP3(k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)),sK6,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7))
    | ~ spl11_82
    | ~ spl11_93 ),
    inference(unit_resulting_resolution,[],[f873,f1070])).

fof(f1070,plain,
    ( ! [X3] :
        ( sP3(k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)),X3,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7))
        | ~ r2_hidden(X3,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6)) )
    | ~ spl11_93 ),
    inference(avatar_component_clause,[],[f1069])).

fof(f1069,plain,
    ( spl11_93
  <=> ! [X3] :
        ( ~ r2_hidden(X3,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6))
        | sP3(k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)),X3,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_93])])).

fof(f1071,plain,
    ( spl11_93
    | ~ spl11_12
    | ~ spl11_36 ),
    inference(avatar_split_clause,[],[f387,f328,f176,f1069])).

fof(f387,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6))
        | sP3(k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)),X3,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)) )
    | ~ spl11_12
    | ~ spl11_36 ),
    inference(superposition,[],[f177,f371])).

fof(f874,plain,
    ( spl11_82
    | ~ spl11_4
    | ~ spl11_29
    | ~ spl11_45 ),
    inference(avatar_split_clause,[],[f471,f400,f275,f140,f872])).

fof(f140,plain,
    ( spl11_4
  <=> ! [X1,X3,X2] : sP4(X3,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f400,plain,
    ( spl11_45
  <=> ! [X1,X3,X5,X0,X2] :
        ( r2_hidden(X5,X3)
        | ~ sP4(X5,X2,X1,X0)
        | ~ sP5(X0,X1,X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_45])])).

fof(f471,plain,
    ( ! [X2,X0,X1] : r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2))
    | ~ spl11_4
    | ~ spl11_29
    | ~ spl11_45 ),
    inference(unit_resulting_resolution,[],[f141,f276,f401])).

fof(f401,plain,
    ( ! [X2,X0,X5,X3,X1] :
        ( ~ sP5(X0,X1,X2,X3)
        | ~ sP4(X5,X2,X1,X0)
        | r2_hidden(X5,X3) )
    | ~ spl11_45 ),
    inference(avatar_component_clause,[],[f400])).

fof(f141,plain,
    ( ! [X2,X3,X1] : sP4(X3,X1,X2,X3)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f140])).

fof(f834,plain,
    ( spl11_79
    | ~ spl11_2
    | ~ spl11_29
    | ~ spl11_45 ),
    inference(avatar_split_clause,[],[f469,f400,f275,f132,f832])).

fof(f132,plain,
    ( spl11_2
  <=> ! [X1,X3,X2] : sP4(X1,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f469,plain,
    ( ! [X2,X0,X1] : r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0))
    | ~ spl11_2
    | ~ spl11_29
    | ~ spl11_45 ),
    inference(unit_resulting_resolution,[],[f133,f276,f401])).

fof(f133,plain,
    ( ! [X2,X3,X1] : sP4(X1,X1,X2,X3)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f132])).

fof(f741,plain,(
    spl11_73 ),
    inference(avatar_split_clause,[],[f114,f739])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k4_enumset1(X0,X0,X0,X0,X0,X0) = k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f76,f109,f108])).

fof(f108,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f71,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f74,f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f94,f105])).

fof(f105,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f94,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f71,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f109,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f67,f108])).

fof(f67,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f737,plain,
    ( spl11_72
    | ~ spl11_7
    | ~ spl11_70 ),
    inference(avatar_split_clause,[],[f722,f689,f152,f735])).

fof(f689,plain,
    ( spl11_70
  <=> ! [X0] : ~ sP3(k3_xboole_0(X0,sK8),sK6,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_70])])).

fof(f722,plain,
    ( ! [X0] : ~ sP3(k3_xboole_0(sK8,X0),sK6,X0)
    | ~ spl11_7
    | ~ spl11_70 ),
    inference(superposition,[],[f690,f153])).

fof(f690,plain,
    ( ! [X0] : ~ sP3(k3_xboole_0(X0,sK8),sK6,X0)
    | ~ spl11_70 ),
    inference(avatar_component_clause,[],[f689])).

fof(f691,plain,
    ( spl11_70
    | ~ spl11_14
    | ~ spl11_65 ),
    inference(avatar_split_clause,[],[f654,f642,f184,f689])).

fof(f642,plain,
    ( spl11_65
  <=> ! [X0] : ~ r2_hidden(sK6,k5_xboole_0(X0,k3_xboole_0(X0,sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_65])])).

fof(f654,plain,
    ( ! [X0] : ~ sP3(k3_xboole_0(X0,sK8),sK6,X0)
    | ~ spl11_14
    | ~ spl11_65 ),
    inference(unit_resulting_resolution,[],[f643,f185])).

fof(f643,plain,
    ( ! [X0] : ~ r2_hidden(sK6,k5_xboole_0(X0,k3_xboole_0(X0,sK8)))
    | ~ spl11_65 ),
    inference(avatar_component_clause,[],[f642])).

fof(f644,plain,
    ( spl11_65
    | ~ spl11_11
    | ~ spl11_26
    | ~ spl11_52 ),
    inference(avatar_split_clause,[],[f528,f519,f263,f169,f642])).

fof(f169,plain,
    ( spl11_11
  <=> ! [X1,X0] : sP2(X0,X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f263,plain,
    ( spl11_26
  <=> ! [X1,X0,X2,X4] :
        ( sP1(X1,X4,X0)
        | ~ r2_hidden(X4,X2)
        | ~ sP2(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f519,plain,
    ( spl11_52
  <=> ! [X0] : ~ sP1(sK8,sK6,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f528,plain,
    ( ! [X0] : ~ r2_hidden(sK6,k5_xboole_0(X0,k3_xboole_0(X0,sK8)))
    | ~ spl11_11
    | ~ spl11_26
    | ~ spl11_52 ),
    inference(unit_resulting_resolution,[],[f170,f520,f264])).

fof(f264,plain,
    ( ! [X4,X2,X0,X1] :
        ( ~ sP2(X0,X1,X2)
        | ~ r2_hidden(X4,X2)
        | sP1(X1,X4,X0) )
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f263])).

fof(f520,plain,
    ( ! [X0] : ~ sP1(sK8,sK6,X0)
    | ~ spl11_52 ),
    inference(avatar_component_clause,[],[f519])).

fof(f170,plain,
    ( ! [X0,X1] : sP2(X0,X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f169])).

fof(f620,plain,(
    spl11_63 ),
    inference(avatar_split_clause,[],[f121,f618])).

fof(f121,plain,(
    ! [X2,X1] :
      ( k4_enumset1(X2,X2,X2,X2,X2,X2) = k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),X1)
      | ~ r2_hidden(X2,X1) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( k4_enumset1(X0,X0,X0,X0,X0,X0) = k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1)
      | X0 != X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f77,f109,f108])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | X0 != X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f540,plain,(
    spl11_53 ),
    inference(avatar_split_clause,[],[f112,f538])).

fof(f112,plain,(
    ! [X2,X0,X1] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X1,X1,X1,X1,X0,X2) ),
    inference(definition_unfolding,[],[f73,f107,f107])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

fof(f521,plain,
    ( spl11_52
    | ~ spl11_9
    | ~ spl11_38 ),
    inference(avatar_split_clause,[],[f501,f346,f160,f519])).

fof(f160,plain,
    ( spl11_9
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X1,X0)
        | ~ sP1(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f501,plain,
    ( ! [X0] : ~ sP1(sK8,sK6,X0)
    | ~ spl11_9
    | ~ spl11_38 ),
    inference(unit_resulting_resolution,[],[f498,f161])).

fof(f161,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP1(X0,X1,X2)
        | ~ r2_hidden(X1,X0) )
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f160])).

fof(f498,plain,
    ( r2_hidden(sK6,sK8)
    | ~ spl11_38 ),
    inference(avatar_component_clause,[],[f346])).

fof(f499,plain,
    ( spl11_38
    | ~ spl11_46
    | ~ spl11_19
    | spl11_34 ),
    inference(avatar_split_clause,[],[f370,f313,f215,f448,f346])).

fof(f215,plain,
    ( spl11_19
  <=> ! [X1,X0,X2] :
        ( sP0(X0,X1,X2)
        | ~ r2_hidden(X0,X2)
        | r2_hidden(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f370,plain,
    ( ~ r2_hidden(sK7,sK8)
    | r2_hidden(sK6,sK8)
    | ~ spl11_19
    | spl11_34 ),
    inference(resolution,[],[f314,f216])).

fof(f216,plain,
    ( ! [X2,X0,X1] :
        ( sP0(X0,X1,X2)
        | ~ r2_hidden(X0,X2)
        | r2_hidden(X1,X2) )
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f215])).

fof(f481,plain,(
    spl11_48 ),
    inference(avatar_split_clause,[],[f99,f479])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X1
      | X0 = X2
      | X0 = X3
      | ~ sP4(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP4(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP4(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP4(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP4(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP4(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP4(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X1,X0] :
      ( sP4(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f402,plain,(
    spl11_45 ),
    inference(avatar_split_clause,[],[f96,f400])).

fof(f96,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | ~ sP4(X5,X2,X1,X0)
      | ~ sP5(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP5(X0,X1,X2,X3)
        | ( ( ~ sP4(sK10(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK10(X0,X1,X2,X3),X3) )
          & ( sP4(sK10(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK10(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP4(X5,X2,X1,X0) )
            & ( sP4(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP5(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f54,f55])).

fof(f55,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP4(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP4(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP4(sK10(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK10(X0,X1,X2,X3),X3) )
        & ( sP4(sK10(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK10(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP5(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP4(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP4(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP4(X5,X2,X1,X0) )
            & ( sP4(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP5(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP5(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP4(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP4(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP4(X4,X2,X1,X0) )
            & ( sP4(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP5(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( sP5(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP4(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f372,plain,
    ( spl11_36
    | ~ spl11_7
    | ~ spl11_33 ),
    inference(avatar_split_clause,[],[f369,f310,f152,f328])).

fof(f369,plain,
    ( k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) = k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)))
    | ~ spl11_7
    | ~ spl11_33 ),
    inference(forward_demodulation,[],[f335,f153])).

fof(f335,plain,
    ( k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) = k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),sK8))
    | ~ spl11_33 ),
    inference(avatar_component_clause,[],[f310])).

fof(f368,plain,
    ( spl11_42
    | ~ spl11_10
    | spl11_38 ),
    inference(avatar_split_clause,[],[f354,f346,f164,f366])).

fof(f164,plain,
    ( spl11_10
  <=> ! [X1,X2] :
        ( sP0(X1,X1,X2)
        | r2_hidden(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f354,plain,
    ( sP0(sK6,sK6,sK8)
    | ~ spl11_10
    | spl11_38 ),
    inference(unit_resulting_resolution,[],[f347,f165])).

fof(f165,plain,
    ( ! [X2,X1] :
        ( sP0(X1,X1,X2)
        | r2_hidden(X1,X2) )
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f164])).

fof(f364,plain,(
    spl11_41 ),
    inference(avatar_split_clause,[],[f95,f362])).

fof(f95,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( sP4(X5,X2,X1,X0)
      | ~ r2_hidden(X5,X3)
      | ~ sP5(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f352,plain,(
    spl11_39 ),
    inference(avatar_split_clause,[],[f75,f350])).

fof(f75,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f348,plain,
    ( ~ spl11_38
    | ~ spl11_5
    | ~ spl11_34 ),
    inference(avatar_split_clause,[],[f342,f313,f144,f346])).

fof(f144,plain,
    ( spl11_5
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X1,X2)
        | ~ sP0(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f342,plain,
    ( ~ r2_hidden(sK6,sK8)
    | ~ spl11_5
    | ~ spl11_34 ),
    inference(unit_resulting_resolution,[],[f336,f145])).

fof(f145,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP0(X0,X1,X2)
        | ~ r2_hidden(X1,X2) )
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f144])).

fof(f337,plain,
    ( spl11_33
    | spl11_34 ),
    inference(avatar_split_clause,[],[f111,f313,f310])).

fof(f111,plain,
    ( sP0(sK7,sK6,sK8)
    | k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) = k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),sK8)) ),
    inference(definition_unfolding,[],[f65,f109,f72,f108])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f65,plain,
    ( sP0(sK7,sK6,sK8)
    | k1_tarski(sK6) = k4_xboole_0(k2_tarski(sK6,sK7),sK8) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ sP0(sK7,sK6,sK8)
      | k1_tarski(sK6) != k4_xboole_0(k2_tarski(sK6,sK7),sK8) )
    & ( sP0(sK7,sK6,sK8)
      | k1_tarski(sK6) = k4_xboole_0(k2_tarski(sK6,sK7),sK8) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f39,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ sP0(X1,X0,X2)
          | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( sP0(X1,X0,X2)
          | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ sP0(sK7,sK6,sK8)
        | k1_tarski(sK6) != k4_xboole_0(k2_tarski(sK6,sK7),sK8) )
      & ( sP0(sK7,sK6,sK8)
        | k1_tarski(sK6) = k4_xboole_0(k2_tarski(sK6,sK7),sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ( ~ sP0(X1,X0,X2)
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( sP0(X1,X0,X2)
        | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f20,f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_zfmisc_1)).

fof(f315,plain,
    ( ~ spl11_33
    | ~ spl11_34 ),
    inference(avatar_split_clause,[],[f110,f313,f310])).

fof(f110,plain,
    ( ~ sP0(sK7,sK6,sK8)
    | k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) != k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),sK8)) ),
    inference(definition_unfolding,[],[f66,f109,f72,f108])).

fof(f66,plain,
    ( ~ sP0(sK7,sK6,sK8)
    | k1_tarski(sK6) != k4_xboole_0(k2_tarski(sK6,sK7),sK8) ),
    inference(cnf_transformation,[],[f41])).

fof(f277,plain,(
    spl11_29 ),
    inference(avatar_split_clause,[],[f126,f275])).

fof(f126,plain,(
    ! [X2,X0,X1] : sP5(X0,X1,X2,k4_enumset1(X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X0,X1,X2,X3)
      | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f103,f107])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP5(X0,X1,X2,X3) )
      & ( sP5(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP5(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f25,f34,f33])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f269,plain,(
    spl11_27 ),
    inference(avatar_split_clause,[],[f79,f267])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ sP1(X1,X4,X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ~ sP1(X1,sK9(X0,X1,X2),X0)
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( sP1(X1,sK9(X0,X1,X2),X0)
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X1,X4,X0) )
            & ( sP1(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP1(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP1(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP1(X1,sK9(X0,X1,X2),X0)
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( sP1(X1,sK9(X0,X1,X2),X0)
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X1,X4,X0) )
            & ( sP1(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP1(X1,X3,X0) )
            & ( sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP1(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f265,plain,(
    spl11_26 ),
    inference(avatar_split_clause,[],[f78,f263])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( sP1(X1,X4,X0)
      | ~ r2_hidden(X4,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f245,plain,(
    spl11_25 ),
    inference(avatar_split_clause,[],[f90,f243])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | r2_hidden(X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ( r2_hidden(X1,X2)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) ) ) )
      & ( ( ( ~ r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) )
          & ( r2_hidden(X1,X0)
            | r2_hidden(X1,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ( sP3(X2,X0,X1)
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ sP3(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X0,X1)
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f241,plain,(
    spl11_24 ),
    inference(avatar_split_clause,[],[f89,f239])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f237,plain,(
    spl11_23 ),
    inference(avatar_split_clause,[],[f88,f235])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f225,plain,(
    spl11_21 ),
    inference(avatar_split_clause,[],[f84,f223])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X1,X3,X0] :
      ( ( sP1(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP1(X1,X3,X0) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X1,X3,X0] :
      ( ( sP1(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP1(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X1,X3,X0] :
      ( sP1(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f217,plain,(
    spl11_19 ),
    inference(avatar_split_clause,[],[f63,f215])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( X0 != X1
          & ~ r2_hidden(X0,X2) )
        | r2_hidden(X1,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X0,X2) )
          & ~ r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f206,plain,(
    spl11_17 ),
    inference(avatar_split_clause,[],[f62,f204])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f190,plain,
    ( spl11_15
    | ~ spl11_7
    | ~ spl11_11 ),
    inference(avatar_split_clause,[],[f173,f169,f152,f188])).

fof(f173,plain,
    ( ! [X2,X1] : sP2(X1,X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))
    | ~ spl11_7
    | ~ spl11_11 ),
    inference(superposition,[],[f170,f153])).

fof(f186,plain,(
    spl11_14 ),
    inference(avatar_split_clause,[],[f92,f184])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ sP3(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ~ sP3(X2,X0,X1) )
      & ( sP3(X2,X0,X1)
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> sP3(X2,X0,X1) ) ),
    inference(definition_folding,[],[f23,f31])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f178,plain,(
    spl11_12 ),
    inference(avatar_split_clause,[],[f91,f176])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f171,plain,(
    spl11_11 ),
    inference(avatar_split_clause,[],[f122,f169])).

fof(f122,plain,(
    ! [X0,X1] : sP2(X0,X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f85,f72])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP2(X0,X1,X2) )
      & ( sP2(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP2(X0,X1,X2) ) ),
    inference(definition_folding,[],[f3,f29,f28])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f166,plain,(
    spl11_10 ),
    inference(avatar_split_clause,[],[f120,f164])).

fof(f120,plain,(
    ! [X2,X1] :
      ( sP0(X1,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | X0 != X1
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f162,plain,(
    spl11_9 ),
    inference(avatar_split_clause,[],[f83,f160])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f154,plain,(
    spl11_7 ),
    inference(avatar_split_clause,[],[f70,f152])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f150,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f69,f148])).

fof(f69,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f146,plain,(
    spl11_5 ),
    inference(avatar_split_clause,[],[f61,f144])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f142,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f125,f140])).

fof(f125,plain,(
    ! [X2,X3,X1] : sP4(X3,X1,X2,X3) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X0,X1,X2,X3)
      | X0 != X3 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f134,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f123,f132])).

fof(f123,plain,(
    ! [X2,X3,X1] : sP4(X1,X1,X2,X3) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X0,X1,X2,X3)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f130,plain,(
    spl11_1 ),
    inference(avatar_split_clause,[],[f68,f128])).

fof(f68,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:47:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (21625)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.51  % (21603)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (21600)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (21596)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (21620)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (21612)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (21597)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (21608)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (21611)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (21609)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (21599)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (21619)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (21604)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (21598)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (21602)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (21617)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (21615)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (21605)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (21613)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (21606)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (21605)Refutation not found, incomplete strategy% (21605)------------------------------
% 0.22/0.54  % (21605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (21605)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (21605)Memory used [KB]: 10746
% 0.22/0.54  % (21605)Time elapsed: 0.128 s
% 0.22/0.54  % (21605)------------------------------
% 0.22/0.54  % (21605)------------------------------
% 0.22/0.54  % (21621)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (21607)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (21622)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (21614)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (21614)Refutation not found, incomplete strategy% (21614)------------------------------
% 0.22/0.55  % (21614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (21614)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (21614)Memory used [KB]: 10618
% 0.22/0.55  % (21614)Time elapsed: 0.148 s
% 0.22/0.55  % (21614)------------------------------
% 0.22/0.55  % (21614)------------------------------
% 0.22/0.55  % (21623)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (21616)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (21624)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (21626)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.56  % (21617)Refutation not found, incomplete strategy% (21617)------------------------------
% 0.22/0.56  % (21617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (21617)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (21617)Memory used [KB]: 10746
% 0.22/0.56  % (21617)Time elapsed: 0.152 s
% 0.22/0.56  % (21617)------------------------------
% 0.22/0.56  % (21617)------------------------------
% 0.22/0.56  % (21618)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (21610)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.02/0.69  % (21638)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.02/0.70  % (21639)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.02/0.70  % (21640)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.26/0.83  % (21602)Time limit reached!
% 3.26/0.83  % (21602)------------------------------
% 3.26/0.83  % (21602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.26/0.85  % (21602)Termination reason: Time limit
% 3.26/0.85  
% 3.26/0.85  % (21602)Memory used [KB]: 9466
% 3.26/0.86  % (21602)Time elapsed: 0.417 s
% 3.26/0.86  % (21602)------------------------------
% 3.26/0.86  % (21602)------------------------------
% 4.28/0.91  % (21607)Time limit reached!
% 4.28/0.91  % (21607)------------------------------
% 4.28/0.91  % (21607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.28/0.91  % (21607)Termination reason: Time limit
% 4.28/0.91  
% 4.28/0.91  % (21607)Memory used [KB]: 13944
% 4.28/0.91  % (21607)Time elapsed: 0.508 s
% 4.28/0.91  % (21607)------------------------------
% 4.28/0.91  % (21607)------------------------------
% 4.28/0.92  % (21609)Time limit reached!
% 4.28/0.92  % (21609)------------------------------
% 4.28/0.92  % (21609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.28/0.92  % (21609)Termination reason: Time limit
% 4.28/0.92  % (21609)Termination phase: Saturation
% 4.28/0.92  
% 4.28/0.92  % (21609)Memory used [KB]: 9722
% 4.28/0.92  % (21609)Time elapsed: 0.500 s
% 4.28/0.92  % (21609)------------------------------
% 4.28/0.92  % (21609)------------------------------
% 4.40/0.93  % (21596)Time limit reached!
% 4.40/0.93  % (21596)------------------------------
% 4.40/0.93  % (21596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.40/0.93  % (21596)Termination reason: Time limit
% 4.40/0.93  % (21596)Termination phase: Saturation
% 4.40/0.93  
% 4.40/0.93  % (21596)Memory used [KB]: 2558
% 4.40/0.93  % (21596)Time elapsed: 0.516 s
% 4.40/0.93  % (21596)------------------------------
% 4.40/0.93  % (21596)------------------------------
% 4.40/0.94  % (21597)Time limit reached!
% 4.40/0.94  % (21597)------------------------------
% 4.40/0.94  % (21597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.40/0.94  % (21597)Termination reason: Time limit
% 4.40/0.94  % (21597)Termination phase: Saturation
% 4.40/0.94  
% 4.40/0.94  % (21597)Memory used [KB]: 9083
% 4.40/0.94  % (21597)Time elapsed: 0.500 s
% 4.40/0.94  % (21597)------------------------------
% 4.40/0.94  % (21597)------------------------------
% 4.40/0.95  % (21719)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.40/1.00  % (21625)Time limit reached!
% 4.40/1.00  % (21625)------------------------------
% 4.40/1.00  % (21625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.00/1.01  % (21625)Termination reason: Time limit
% 5.00/1.01  % (21625)Termination phase: Saturation
% 5.00/1.01  
% 5.00/1.01  % (21625)Memory used [KB]: 9338
% 5.00/1.01  % (21625)Time elapsed: 0.600 s
% 5.00/1.01  % (21625)------------------------------
% 5.00/1.01  % (21625)------------------------------
% 5.00/1.03  % (21613)Time limit reached!
% 5.00/1.03  % (21613)------------------------------
% 5.00/1.03  % (21613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.00/1.03  % (21774)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.00/1.03  % (21613)Termination reason: Time limit
% 5.00/1.03  % (21613)Termination phase: Saturation
% 5.00/1.03  
% 5.00/1.03  % (21613)Memory used [KB]: 18933
% 5.00/1.03  % (21613)Time elapsed: 0.600 s
% 5.00/1.03  % (21613)------------------------------
% 5.00/1.03  % (21613)------------------------------
% 5.00/1.04  % (21758)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.00/1.04  % (21604)Time limit reached!
% 5.00/1.04  % (21604)------------------------------
% 5.00/1.04  % (21604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.00/1.04  % (21604)Termination reason: Time limit
% 5.00/1.04  % (21604)Termination phase: Saturation
% 5.00/1.04  
% 5.00/1.04  % (21604)Memory used [KB]: 11129
% 5.00/1.04  % (21604)Time elapsed: 0.600 s
% 5.00/1.04  % (21604)------------------------------
% 5.00/1.04  % (21604)------------------------------
% 5.00/1.05  % (21764)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.00/1.06  % (21765)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.47/1.13  % (21802)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 5.47/1.14  % (21803)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.42/1.19  % (21804)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.82/1.24  % (21618)Time limit reached!
% 6.82/1.24  % (21618)------------------------------
% 6.82/1.24  % (21618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.82/1.24  % (21618)Termination reason: Time limit
% 6.82/1.24  % (21618)Termination phase: Saturation
% 6.82/1.24  
% 6.82/1.24  % (21618)Memory used [KB]: 3326
% 6.82/1.24  % (21618)Time elapsed: 0.800 s
% 6.82/1.24  % (21618)------------------------------
% 6.82/1.24  % (21618)------------------------------
% 7.41/1.31  % (21719)Time limit reached!
% 7.41/1.31  % (21719)------------------------------
% 7.41/1.31  % (21719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.41/1.31  % (21719)Termination reason: Time limit
% 7.41/1.31  % (21719)Termination phase: Saturation
% 7.41/1.31  
% 7.41/1.31  % (21719)Memory used [KB]: 8443
% 7.41/1.31  % (21719)Time elapsed: 0.400 s
% 7.41/1.31  % (21719)------------------------------
% 7.41/1.31  % (21719)------------------------------
% 7.41/1.33  % (21758)Time limit reached!
% 7.41/1.33  % (21758)------------------------------
% 7.41/1.33  % (21758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.41/1.34  % (21844)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 7.41/1.35  % (21758)Termination reason: Time limit
% 7.41/1.35  
% 7.41/1.35  % (21758)Memory used [KB]: 13944
% 7.41/1.35  % (21758)Time elapsed: 0.408 s
% 7.41/1.35  % (21758)------------------------------
% 7.41/1.35  % (21758)------------------------------
% 7.92/1.43  % (21598)Time limit reached!
% 7.92/1.43  % (21598)------------------------------
% 7.92/1.43  % (21598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.92/1.43  % (21598)Termination reason: Time limit
% 7.92/1.43  % (21598)Termination phase: Saturation
% 7.92/1.43  
% 7.92/1.43  % (21598)Memory used [KB]: 17270
% 7.92/1.43  % (21598)Time elapsed: 1.025 s
% 7.92/1.43  % (21598)------------------------------
% 7.92/1.43  % (21598)------------------------------
% 7.92/1.45  % (21879)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 8.58/1.48  % (21880)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 9.03/1.54  % (21881)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 9.56/1.61  % (21623)Time limit reached!
% 9.56/1.61  % (21623)------------------------------
% 9.56/1.61  % (21623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.56/1.62  % (21623)Termination reason: Time limit
% 9.56/1.62  % (21623)Termination phase: Saturation
% 9.56/1.62  
% 9.56/1.62  % (21623)Memory used [KB]: 18549
% 9.56/1.62  % (21623)Time elapsed: 1.200 s
% 9.56/1.62  % (21623)------------------------------
% 9.56/1.62  % (21623)------------------------------
% 9.56/1.64  % (21619)Time limit reached!
% 9.56/1.64  % (21619)------------------------------
% 9.56/1.64  % (21619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.56/1.64  % (21619)Termination reason: Time limit
% 9.56/1.64  % (21619)Termination phase: Saturation
% 9.56/1.64  
% 9.56/1.64  % (21619)Memory used [KB]: 17270
% 9.56/1.64  % (21619)Time elapsed: 1.200 s
% 9.56/1.64  % (21619)------------------------------
% 9.56/1.64  % (21619)------------------------------
% 10.43/1.75  % (21621)Time limit reached!
% 10.43/1.75  % (21621)------------------------------
% 10.43/1.75  % (21621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.43/1.75  % (21612)Time limit reached!
% 10.43/1.75  % (21612)------------------------------
% 10.43/1.75  % (21612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.43/1.75  % (21621)Termination reason: Time limit
% 10.43/1.75  
% 10.43/1.75  % (21621)Memory used [KB]: 19317
% 10.43/1.75  % (21621)Time elapsed: 1.330 s
% 10.43/1.75  % (21621)------------------------------
% 10.43/1.75  % (21621)------------------------------
% 10.43/1.76  % (21612)Termination reason: Time limit
% 10.43/1.76  
% 10.43/1.76  % (21612)Memory used [KB]: 12025
% 10.43/1.76  % (21612)Time elapsed: 1.308 s
% 10.43/1.76  % (21612)------------------------------
% 10.43/1.76  % (21612)------------------------------
% 10.43/1.76  % (21882)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 10.43/1.77  % (21883)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 11.51/1.86  % (21884)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 11.51/1.86  % (21879)Time limit reached!
% 11.51/1.86  % (21879)------------------------------
% 11.51/1.86  % (21879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.51/1.86  % (21879)Termination reason: Time limit
% 11.51/1.86  
% 11.51/1.86  % (21879)Memory used [KB]: 3709
% 11.51/1.86  % (21879)Time elapsed: 0.512 s
% 11.51/1.86  % (21879)------------------------------
% 11.51/1.86  % (21879)------------------------------
% 11.51/1.87  % (21885)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 12.20/1.92  % (21624)Time limit reached!
% 12.20/1.92  % (21624)------------------------------
% 12.20/1.92  % (21624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.20/1.92  % (21624)Termination reason: Time limit
% 12.20/1.92  % (21624)Termination phase: Saturation
% 12.20/1.92  
% 12.20/1.92  % (21624)Memory used [KB]: 15223
% 12.20/1.92  % (21624)Time elapsed: 1.500 s
% 12.20/1.92  % (21624)------------------------------
% 12.20/1.92  % (21624)------------------------------
% 12.20/1.95  % (21600)Time limit reached!
% 12.20/1.95  % (21600)------------------------------
% 12.20/1.95  % (21600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.20/1.95  % (21600)Termination reason: Time limit
% 12.20/1.95  
% 12.20/1.95  % (21600)Memory used [KB]: 17782
% 12.20/1.95  % (21600)Time elapsed: 1.522 s
% 12.20/1.95  % (21600)------------------------------
% 12.20/1.95  % (21600)------------------------------
% 12.72/1.99  % (21886)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 12.72/2.04  % (21887)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 13.30/2.08  % (21888)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 13.30/2.09  % (21883)Time limit reached!
% 13.30/2.09  % (21883)------------------------------
% 13.30/2.09  % (21883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.30/2.09  % (21883)Termination reason: Time limit
% 13.30/2.09  % (21883)Termination phase: Saturation
% 13.30/2.09  
% 13.30/2.09  % (21883)Memory used [KB]: 4093
% 13.30/2.09  % (21883)Time elapsed: 0.400 s
% 13.30/2.09  % (21883)------------------------------
% 13.30/2.09  % (21883)------------------------------
% 13.49/2.10  % (21608)Time limit reached!
% 13.49/2.10  % (21608)------------------------------
% 13.49/2.10  % (21608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.49/2.10  % (21608)Termination reason: Time limit
% 13.49/2.10  
% 13.49/2.10  % (21608)Memory used [KB]: 16502
% 13.49/2.10  % (21608)Time elapsed: 1.687 s
% 13.49/2.10  % (21608)------------------------------
% 13.49/2.10  % (21608)------------------------------
% 13.60/2.15  % (21765)Time limit reached!
% 13.60/2.15  % (21765)------------------------------
% 13.60/2.15  % (21765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.60/2.15  % (21765)Termination reason: Time limit
% 13.60/2.15  
% 13.60/2.15  % (21765)Memory used [KB]: 10618
% 13.60/2.15  % (21765)Time elapsed: 1.207 s
% 13.60/2.15  % (21765)------------------------------
% 13.60/2.15  % (21765)------------------------------
% 14.19/2.23  % (21889)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 14.19/2.23  % (21881)Refutation found. Thanks to Tanya!
% 14.19/2.23  % SZS status Theorem for theBenchmark
% 14.19/2.24  % (21890)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 14.19/2.24  % SZS output start Proof for theBenchmark
% 14.19/2.25  fof(f13651,plain,(
% 14.19/2.25    $false),
% 14.19/2.25    inference(avatar_sat_refutation,[],[f130,f134,f142,f146,f150,f154,f162,f166,f171,f178,f186,f190,f206,f217,f225,f237,f241,f245,f265,f269,f277,f315,f337,f348,f352,f364,f368,f372,f402,f481,f499,f521,f540,f620,f644,f691,f737,f741,f834,f874,f1071,f1109,f1250,f1267,f2273,f2459,f2972,f3022,f3323,f5202,f6670,f6719,f6909,f7049,f7074,f7333,f8161,f12587,f13242,f13537,f13562,f13650])).
% 14.19/2.25  fof(f13650,plain,(
% 14.19/2.25    spl11_34 | ~spl11_42 | ~spl11_300),
% 14.19/2.25    inference(avatar_contradiction_clause,[],[f13649])).
% 14.19/2.25  fof(f13649,plain,(
% 14.19/2.25    $false | (spl11_34 | ~spl11_42 | ~spl11_300)),
% 14.19/2.25    inference(subsumption_resolution,[],[f13563,f367])).
% 14.19/2.25  fof(f367,plain,(
% 14.19/2.25    sP0(sK6,sK6,sK8) | ~spl11_42),
% 14.19/2.25    inference(avatar_component_clause,[],[f366])).
% 14.19/2.25  fof(f366,plain,(
% 14.19/2.25    spl11_42 <=> sP0(sK6,sK6,sK8)),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).
% 14.19/2.25  fof(f13563,plain,(
% 14.19/2.25    ~sP0(sK6,sK6,sK8) | (spl11_34 | ~spl11_300)),
% 14.19/2.25    inference(superposition,[],[f314,f6624])).
% 14.19/2.25  fof(f6624,plain,(
% 14.19/2.25    sK6 = sK7 | ~spl11_300),
% 14.19/2.25    inference(avatar_component_clause,[],[f6623])).
% 14.19/2.25  fof(f6623,plain,(
% 14.19/2.25    spl11_300 <=> sK6 = sK7),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_300])])).
% 14.19/2.25  fof(f314,plain,(
% 14.19/2.25    ~sP0(sK7,sK6,sK8) | spl11_34),
% 14.19/2.25    inference(avatar_component_clause,[],[f313])).
% 14.19/2.25  fof(f313,plain,(
% 14.19/2.25    spl11_34 <=> sP0(sK7,sK6,sK8)),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).
% 14.19/2.25  fof(f13562,plain,(
% 14.19/2.25    spl11_300 | ~spl11_48 | ~spl11_444),
% 14.19/2.25    inference(avatar_split_clause,[],[f13556,f13535,f479,f6623])).
% 14.19/2.25  fof(f479,plain,(
% 14.19/2.25    spl11_48 <=> ! [X1,X3,X0,X2] : (X0 = X1 | X0 = X2 | X0 = X3 | ~sP4(X0,X1,X2,X3))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_48])])).
% 14.19/2.25  fof(f13535,plain,(
% 14.19/2.25    spl11_444 <=> sP4(sK7,sK6,sK6,sK6)),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_444])])).
% 14.19/2.25  fof(f13556,plain,(
% 14.19/2.25    sK6 = sK7 | (~spl11_48 | ~spl11_444)),
% 14.19/2.25    inference(duplicate_literal_removal,[],[f13555])).
% 14.19/2.25  fof(f13555,plain,(
% 14.19/2.25    sK6 = sK7 | sK6 = sK7 | sK6 = sK7 | (~spl11_48 | ~spl11_444)),
% 14.19/2.25    inference(resolution,[],[f13536,f480])).
% 14.19/2.25  fof(f480,plain,(
% 14.19/2.25    ( ! [X2,X0,X3,X1] : (~sP4(X0,X1,X2,X3) | X0 = X2 | X0 = X3 | X0 = X1) ) | ~spl11_48),
% 14.19/2.25    inference(avatar_component_clause,[],[f479])).
% 14.19/2.25  fof(f13536,plain,(
% 14.19/2.25    sP4(sK7,sK6,sK6,sK6) | ~spl11_444),
% 14.19/2.25    inference(avatar_component_clause,[],[f13535])).
% 14.19/2.25  fof(f13537,plain,(
% 14.19/2.25    spl11_444 | ~spl11_41 | ~spl11_103 | ~spl11_443),
% 14.19/2.25    inference(avatar_split_clause,[],[f13314,f13240,f1265,f362,f13535])).
% 14.19/2.25  fof(f362,plain,(
% 14.19/2.25    spl11_41 <=> ! [X1,X3,X5,X0,X2] : (sP4(X5,X2,X1,X0) | ~r2_hidden(X5,X3) | ~sP5(X0,X1,X2,X3))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_41])])).
% 14.19/2.25  fof(f1265,plain,(
% 14.19/2.25    spl11_103 <=> ! [X1,X0,X2] : sP5(X0,X1,X2,k4_enumset1(X1,X1,X1,X1,X0,X2))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_103])])).
% 14.19/2.25  fof(f13240,plain,(
% 14.19/2.25    spl11_443 <=> r2_hidden(sK7,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_443])])).
% 14.19/2.25  fof(f13314,plain,(
% 14.19/2.25    sP4(sK7,sK6,sK6,sK6) | (~spl11_41 | ~spl11_103 | ~spl11_443)),
% 14.19/2.25    inference(unit_resulting_resolution,[],[f1266,f13241,f363])).
% 14.19/2.25  fof(f363,plain,(
% 14.19/2.25    ( ! [X2,X0,X5,X3,X1] : (~sP5(X0,X1,X2,X3) | ~r2_hidden(X5,X3) | sP4(X5,X2,X1,X0)) ) | ~spl11_41),
% 14.19/2.25    inference(avatar_component_clause,[],[f362])).
% 14.19/2.25  fof(f13241,plain,(
% 14.19/2.25    r2_hidden(sK7,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6)) | ~spl11_443),
% 14.19/2.25    inference(avatar_component_clause,[],[f13240])).
% 14.19/2.25  fof(f1266,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (sP5(X0,X1,X2,k4_enumset1(X1,X1,X1,X1,X0,X2))) ) | ~spl11_103),
% 14.19/2.25    inference(avatar_component_clause,[],[f1265])).
% 14.19/2.25  fof(f13242,plain,(
% 14.19/2.25    spl11_443 | ~spl11_27 | ~spl11_196 | ~spl11_430),
% 14.19/2.25    inference(avatar_split_clause,[],[f13177,f12585,f3321,f267,f13240])).
% 14.19/2.25  fof(f267,plain,(
% 14.19/2.25    spl11_27 <=> ! [X1,X0,X2,X4] : (r2_hidden(X4,X2) | ~sP1(X1,X4,X0) | ~sP2(X0,X1,X2))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).
% 14.19/2.25  fof(f3321,plain,(
% 14.19/2.25    spl11_196 <=> sP2(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_196])])).
% 14.19/2.25  fof(f12585,plain,(
% 14.19/2.25    spl11_430 <=> ! [X1,X0] : sP1(sK8,sK7,k4_enumset1(X0,X0,X0,X0,X1,sK7))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_430])])).
% 14.19/2.25  fof(f13177,plain,(
% 14.19/2.25    r2_hidden(sK7,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6)) | (~spl11_27 | ~spl11_196 | ~spl11_430)),
% 14.19/2.25    inference(unit_resulting_resolution,[],[f3322,f12586,f268])).
% 14.19/2.25  fof(f268,plain,(
% 14.19/2.25    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~sP1(X1,X4,X0) | r2_hidden(X4,X2)) ) | ~spl11_27),
% 14.19/2.25    inference(avatar_component_clause,[],[f267])).
% 14.19/2.25  fof(f12586,plain,(
% 14.19/2.25    ( ! [X0,X1] : (sP1(sK8,sK7,k4_enumset1(X0,X0,X0,X0,X1,sK7))) ) | ~spl11_430),
% 14.19/2.25    inference(avatar_component_clause,[],[f12585])).
% 14.19/2.25  fof(f3322,plain,(
% 14.19/2.25    sP2(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6)) | ~spl11_196),
% 14.19/2.25    inference(avatar_component_clause,[],[f3321])).
% 14.19/2.25  fof(f12587,plain,(
% 14.19/2.25    spl11_430 | ~spl11_21 | spl11_46 | ~spl11_79),
% 14.19/2.25    inference(avatar_split_clause,[],[f8184,f832,f448,f223,f12585])).
% 14.19/2.25  fof(f223,plain,(
% 14.19/2.25    spl11_21 <=> ! [X1,X0,X2] : (sP1(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).
% 14.19/2.25  fof(f448,plain,(
% 14.19/2.25    spl11_46 <=> r2_hidden(sK7,sK8)),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).
% 14.19/2.25  fof(f832,plain,(
% 14.19/2.25    spl11_79 <=> ! [X1,X0,X2] : r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_79])])).
% 14.19/2.25  fof(f8184,plain,(
% 14.19/2.25    ( ! [X0,X1] : (sP1(sK8,sK7,k4_enumset1(X0,X0,X0,X0,X1,sK7))) ) | (~spl11_21 | spl11_46 | ~spl11_79)),
% 14.19/2.25    inference(unit_resulting_resolution,[],[f833,f449,f224])).
% 14.19/2.25  fof(f224,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) ) | ~spl11_21),
% 14.19/2.25    inference(avatar_component_clause,[],[f223])).
% 14.19/2.25  fof(f449,plain,(
% 14.19/2.25    ~r2_hidden(sK7,sK8) | spl11_46),
% 14.19/2.25    inference(avatar_component_clause,[],[f448])).
% 14.19/2.25  fof(f833,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0))) ) | ~spl11_79),
% 14.19/2.25    inference(avatar_component_clause,[],[f832])).
% 14.19/2.25  fof(f8161,plain,(
% 14.19/2.25    ~spl11_12 | ~spl11_154 | ~spl11_186 | spl11_206 | ~spl11_309),
% 14.19/2.25    inference(avatar_contradiction_clause,[],[f8160])).
% 14.19/2.25  fof(f8160,plain,(
% 14.19/2.25    $false | (~spl11_12 | ~spl11_154 | ~spl11_186 | spl11_206 | ~spl11_309)),
% 14.19/2.25    inference(subsumption_resolution,[],[f8099,f7596])).
% 14.19/2.25  fof(f7596,plain,(
% 14.19/2.25    ( ! [X0,X1] : (~r2_hidden(sK7,k5_xboole_0(sK8,k4_enumset1(X0,X0,X0,X0,X1,sK7)))) ) | (~spl11_12 | ~spl11_309)),
% 14.19/2.25    inference(unit_resulting_resolution,[],[f7332,f177])).
% 14.19/2.25  fof(f177,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | sP3(X2,X0,X1)) ) | ~spl11_12),
% 14.19/2.25    inference(avatar_component_clause,[],[f176])).
% 14.19/2.25  fof(f176,plain,(
% 14.19/2.25    spl11_12 <=> ! [X1,X0,X2] : (sP3(X2,X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2)))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 14.19/2.25  fof(f7332,plain,(
% 14.19/2.25    ( ! [X0,X1] : (~sP3(k4_enumset1(X0,X0,X0,X0,X1,sK7),sK7,sK8)) ) | ~spl11_309),
% 14.19/2.25    inference(avatar_component_clause,[],[f7331])).
% 14.19/2.25  fof(f7331,plain,(
% 14.19/2.25    spl11_309 <=> ! [X1,X0] : ~sP3(k4_enumset1(X0,X0,X0,X0,X1,sK7),sK7,sK8)),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_309])])).
% 14.19/2.25  fof(f8099,plain,(
% 14.19/2.25    r2_hidden(sK7,k5_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7))) | (~spl11_154 | ~spl11_186 | spl11_206)),
% 14.19/2.25    inference(unit_resulting_resolution,[],[f3021,f8096,f2458])).
% 14.19/2.25  fof(f2458,plain,(
% 14.19/2.25    ( ! [X14,X15,X13,X16] : (~sP3(X15,X16,X14) | k4_enumset1(X16,X16,X16,X16,X16,X16) = k3_xboole_0(k4_enumset1(X16,X16,X16,X16,X16,X13),k5_xboole_0(X14,X15)) | r2_hidden(X13,k5_xboole_0(X14,X15))) ) | ~spl11_154),
% 14.19/2.25    inference(avatar_component_clause,[],[f2457])).
% 14.19/2.25  fof(f2457,plain,(
% 14.19/2.25    spl11_154 <=> ! [X16,X13,X15,X14] : (r2_hidden(X13,k5_xboole_0(X14,X15)) | k4_enumset1(X16,X16,X16,X16,X16,X16) = k3_xboole_0(k4_enumset1(X16,X16,X16,X16,X16,X13),k5_xboole_0(X14,X15)) | ~sP3(X15,X16,X14))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_154])])).
% 14.19/2.25  fof(f8096,plain,(
% 14.19/2.25    k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) != k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k5_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7))) | spl11_206),
% 14.19/2.25    inference(avatar_component_clause,[],[f3695])).
% 14.19/2.25  fof(f3695,plain,(
% 14.19/2.25    spl11_206 <=> k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) = k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k5_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_206])])).
% 14.19/2.25  fof(f3021,plain,(
% 14.19/2.25    ( ! [X0,X1] : (sP3(k4_enumset1(sK6,sK6,sK6,sK6,X0,X1),sK6,sK8)) ) | ~spl11_186),
% 14.19/2.25    inference(avatar_component_clause,[],[f3020])).
% 14.19/2.25  fof(f3020,plain,(
% 14.19/2.25    spl11_186 <=> ! [X1,X0] : sP3(k4_enumset1(sK6,sK6,sK6,sK6,X0,X1),sK6,sK8)),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_186])])).
% 14.19/2.25  fof(f7333,plain,(
% 14.19/2.25    spl11_309 | ~spl11_23 | ~spl11_46 | ~spl11_79),
% 14.19/2.25    inference(avatar_split_clause,[],[f7091,f832,f448,f235,f7331])).
% 14.19/2.25  fof(f235,plain,(
% 14.19/2.25    spl11_23 <=> ! [X1,X0,X2] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,X2) | ~sP3(X0,X1,X2))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).
% 14.19/2.25  fof(f7091,plain,(
% 14.19/2.25    ( ! [X0,X1] : (~sP3(k4_enumset1(X0,X0,X0,X0,X1,sK7),sK7,sK8)) ) | (~spl11_23 | ~spl11_46 | ~spl11_79)),
% 14.19/2.25    inference(unit_resulting_resolution,[],[f833,f7073,f236])).
% 14.19/2.25  fof(f236,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) ) | ~spl11_23),
% 14.19/2.25    inference(avatar_component_clause,[],[f235])).
% 14.19/2.25  fof(f7073,plain,(
% 14.19/2.25    r2_hidden(sK7,sK8) | ~spl11_46),
% 14.19/2.25    inference(avatar_component_clause,[],[f448])).
% 14.19/2.25  fof(f7074,plain,(
% 14.19/2.25    spl11_300 | spl11_46 | ~spl11_17 | ~spl11_34),
% 14.19/2.25    inference(avatar_split_clause,[],[f6619,f313,f204,f448,f6623])).
% 14.19/2.25  fof(f204,plain,(
% 14.19/2.25    spl11_17 <=> ! [X1,X0,X2] : (X0 = X1 | r2_hidden(X0,X2) | ~sP0(X0,X1,X2))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).
% 14.19/2.25  fof(f6619,plain,(
% 14.19/2.25    r2_hidden(sK7,sK8) | sK6 = sK7 | (~spl11_17 | ~spl11_34)),
% 14.19/2.25    inference(resolution,[],[f336,f205])).
% 14.19/2.25  fof(f205,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X0,X2) | X0 = X1) ) | ~spl11_17),
% 14.19/2.25    inference(avatar_component_clause,[],[f204])).
% 14.19/2.25  fof(f336,plain,(
% 14.19/2.25    sP0(sK7,sK6,sK8) | ~spl11_34),
% 14.19/2.25    inference(avatar_component_clause,[],[f313])).
% 14.19/2.25  fof(f7049,plain,(
% 14.19/2.25    spl11_36 | ~spl11_206 | ~spl11_264),
% 14.19/2.25    inference(avatar_contradiction_clause,[],[f7048])).
% 14.19/2.25  fof(f7048,plain,(
% 14.19/2.25    $false | (spl11_36 | ~spl11_206 | ~spl11_264)),
% 14.19/2.25    inference(subsumption_resolution,[],[f6953,f3696])).
% 14.19/2.25  fof(f3696,plain,(
% 14.19/2.25    k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) = k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k5_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7))) | ~spl11_206),
% 14.19/2.25    inference(avatar_component_clause,[],[f3695])).
% 14.19/2.25  fof(f6953,plain,(
% 14.19/2.25    k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) != k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k5_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7))) | (spl11_36 | ~spl11_264)),
% 14.19/2.25    inference(superposition,[],[f329,f5201])).
% 14.19/2.25  fof(f5201,plain,(
% 14.19/2.25    ( ! [X2,X3] : (k5_xboole_0(X3,k3_xboole_0(X2,X3)) = k3_xboole_0(X3,k5_xboole_0(X2,X3))) ) | ~spl11_264),
% 14.19/2.25    inference(avatar_component_clause,[],[f5200])).
% 14.19/2.25  fof(f5200,plain,(
% 14.19/2.25    spl11_264 <=> ! [X3,X2] : k5_xboole_0(X3,k3_xboole_0(X2,X3)) = k3_xboole_0(X3,k5_xboole_0(X2,X3))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_264])])).
% 14.19/2.25  fof(f329,plain,(
% 14.19/2.25    k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) != k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7))) | spl11_36),
% 14.19/2.25    inference(avatar_component_clause,[],[f328])).
% 14.19/2.25  fof(f328,plain,(
% 14.19/2.25    spl11_36 <=> k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) = k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_36])])).
% 14.19/2.25  fof(f6909,plain,(
% 14.19/2.25    ~spl11_6 | ~spl11_142 | ~spl11_180 | ~spl11_264 | spl11_301),
% 14.19/2.25    inference(avatar_contradiction_clause,[],[f6908])).
% 14.19/2.25  fof(f6908,plain,(
% 14.19/2.25    $false | (~spl11_6 | ~spl11_142 | ~spl11_180 | ~spl11_264 | spl11_301)),
% 14.19/2.25    inference(subsumption_resolution,[],[f6813,f3207])).
% 14.19/2.25  fof(f3207,plain,(
% 14.19/2.25    ( ! [X0,X1] : (k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) = k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6),k5_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,X0,X1)))) ) | (~spl11_6 | ~spl11_142 | ~spl11_180)),
% 14.19/2.25    inference(forward_demodulation,[],[f3199,f149])).
% 14.19/2.25  fof(f149,plain,(
% 14.19/2.25    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) ) | ~spl11_6),
% 14.19/2.25    inference(avatar_component_clause,[],[f148])).
% 14.19/2.25  fof(f148,plain,(
% 14.19/2.25    spl11_6 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 14.19/2.25  fof(f3199,plain,(
% 14.19/2.25    ( ! [X0,X1] : (k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) = k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6),k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,X0,X1),sK8))) ) | (~spl11_142 | ~spl11_180)),
% 14.19/2.25    inference(unit_resulting_resolution,[],[f2971,f2272])).
% 14.19/2.25  fof(f2272,plain,(
% 14.19/2.25    ( ! [X4,X5,X3] : (~sP3(X5,X3,X4) | k4_enumset1(X3,X3,X3,X3,X3,X3) = k3_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X3),k5_xboole_0(X4,X5))) ) | ~spl11_142),
% 14.19/2.25    inference(avatar_component_clause,[],[f2271])).
% 14.19/2.25  fof(f2271,plain,(
% 14.19/2.25    spl11_142 <=> ! [X3,X5,X4] : (k4_enumset1(X3,X3,X3,X3,X3,X3) = k3_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X3),k5_xboole_0(X4,X5)) | ~sP3(X5,X3,X4))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_142])])).
% 14.19/2.25  fof(f2971,plain,(
% 14.19/2.25    ( ! [X0,X1] : (sP3(sK8,sK6,k4_enumset1(sK6,sK6,sK6,sK6,X0,X1))) ) | ~spl11_180),
% 14.19/2.25    inference(avatar_component_clause,[],[f2970])).
% 14.19/2.25  fof(f2970,plain,(
% 14.19/2.25    spl11_180 <=> ! [X1,X0] : sP3(sK8,sK6,k4_enumset1(sK6,sK6,sK6,sK6,X0,X1))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_180])])).
% 14.19/2.25  fof(f6813,plain,(
% 14.19/2.25    k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) != k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6),k5_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6))) | (~spl11_264 | spl11_301)),
% 14.19/2.25    inference(superposition,[],[f6718,f5201])).
% 14.19/2.25  fof(f6718,plain,(
% 14.19/2.25    k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) != k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6),k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6))) | spl11_301),
% 14.19/2.25    inference(avatar_component_clause,[],[f6717])).
% 14.19/2.25  fof(f6717,plain,(
% 14.19/2.25    spl11_301 <=> k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) = k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6),k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6)))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_301])])).
% 14.19/2.25  fof(f6719,plain,(
% 14.19/2.25    ~spl11_301 | spl11_36 | ~spl11_300),
% 14.19/2.25    inference(avatar_split_clause,[],[f6671,f6623,f328,f6717])).
% 14.19/2.25  fof(f6671,plain,(
% 14.19/2.25    k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) != k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6),k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6))) | (spl11_36 | ~spl11_300)),
% 14.19/2.25    inference(forward_demodulation,[],[f329,f6624])).
% 14.19/2.25  fof(f6670,plain,(
% 14.19/2.25    ~spl11_36 | ~spl11_7 | spl11_33),
% 14.19/2.25    inference(avatar_split_clause,[],[f6614,f310,f152,f328])).
% 14.19/2.25  fof(f152,plain,(
% 14.19/2.25    spl11_7 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 14.19/2.25  fof(f310,plain,(
% 14.19/2.25    spl11_33 <=> k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) = k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),sK8))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).
% 14.19/2.25  fof(f6614,plain,(
% 14.19/2.25    k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) != k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7))) | (~spl11_7 | spl11_33)),
% 14.19/2.25    inference(forward_demodulation,[],[f311,f153])).
% 14.19/2.25  fof(f153,plain,(
% 14.19/2.25    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl11_7),
% 14.19/2.25    inference(avatar_component_clause,[],[f152])).
% 14.19/2.25  fof(f311,plain,(
% 14.19/2.25    k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) != k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),sK8)) | spl11_33),
% 14.19/2.25    inference(avatar_component_clause,[],[f310])).
% 14.19/2.25  fof(f5202,plain,(
% 14.19/2.25    spl11_264 | ~spl11_6 | ~spl11_101),
% 14.19/2.25    inference(avatar_split_clause,[],[f1312,f1248,f148,f5200])).
% 14.19/2.25  fof(f1248,plain,(
% 14.19/2.25    spl11_101 <=> ! [X1,X0] : k5_xboole_0(k3_xboole_0(X1,X0),X0) = k3_xboole_0(X0,k5_xboole_0(X1,X0))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_101])])).
% 14.19/2.25  fof(f1312,plain,(
% 14.19/2.25    ( ! [X2,X3] : (k5_xboole_0(X3,k3_xboole_0(X2,X3)) = k3_xboole_0(X3,k5_xboole_0(X2,X3))) ) | (~spl11_6 | ~spl11_101)),
% 14.19/2.25    inference(superposition,[],[f1249,f149])).
% 14.19/2.25  fof(f1249,plain,(
% 14.19/2.25    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X1,X0),X0) = k3_xboole_0(X0,k5_xboole_0(X1,X0))) ) | ~spl11_101),
% 14.19/2.25    inference(avatar_component_clause,[],[f1248])).
% 14.19/2.25  fof(f3323,plain,(
% 14.19/2.25    spl11_196 | ~spl11_15 | ~spl11_36),
% 14.19/2.25    inference(avatar_split_clause,[],[f383,f328,f188,f3321])).
% 14.19/2.25  fof(f188,plain,(
% 14.19/2.25    spl11_15 <=> ! [X1,X2] : sP2(X1,X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).
% 14.19/2.25  fof(f383,plain,(
% 14.19/2.25    sP2(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6)) | (~spl11_15 | ~spl11_36)),
% 14.19/2.25    inference(superposition,[],[f189,f371])).
% 14.19/2.25  fof(f371,plain,(
% 14.19/2.25    k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) = k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7))) | ~spl11_36),
% 14.19/2.25    inference(avatar_component_clause,[],[f328])).
% 14.19/2.25  fof(f189,plain,(
% 14.19/2.25    ( ! [X2,X1] : (sP2(X1,X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) ) | ~spl11_15),
% 14.19/2.25    inference(avatar_component_clause,[],[f188])).
% 14.19/2.25  fof(f3022,plain,(
% 14.19/2.25    spl11_186 | ~spl11_25 | spl11_38 | ~spl11_82),
% 14.19/2.25    inference(avatar_split_clause,[],[f1157,f872,f346,f243,f3020])).
% 14.19/2.25  fof(f243,plain,(
% 14.19/2.25    spl11_25 <=> ! [X1,X0,X2] : (sP3(X0,X1,X2) | r2_hidden(X1,X2) | ~r2_hidden(X1,X0))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).
% 14.19/2.25  fof(f346,plain,(
% 14.19/2.25    spl11_38 <=> r2_hidden(sK6,sK8)),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).
% 14.19/2.25  fof(f872,plain,(
% 14.19/2.25    spl11_82 <=> ! [X1,X0,X2] : r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_82])])).
% 14.19/2.25  fof(f1157,plain,(
% 14.19/2.25    ( ! [X0,X1] : (sP3(k4_enumset1(sK6,sK6,sK6,sK6,X0,X1),sK6,sK8)) ) | (~spl11_25 | spl11_38 | ~spl11_82)),
% 14.19/2.25    inference(unit_resulting_resolution,[],[f873,f347,f244])).
% 14.19/2.25  fof(f244,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) ) | ~spl11_25),
% 14.19/2.25    inference(avatar_component_clause,[],[f243])).
% 14.19/2.25  fof(f347,plain,(
% 14.19/2.25    ~r2_hidden(sK6,sK8) | spl11_38),
% 14.19/2.25    inference(avatar_component_clause,[],[f346])).
% 14.19/2.25  fof(f873,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2))) ) | ~spl11_82),
% 14.19/2.25    inference(avatar_component_clause,[],[f872])).
% 14.19/2.25  fof(f2972,plain,(
% 14.19/2.25    spl11_180 | ~spl11_24 | spl11_38 | ~spl11_82),
% 14.19/2.25    inference(avatar_split_clause,[],[f1150,f872,f346,f239,f2970])).
% 14.19/2.25  fof(f239,plain,(
% 14.19/2.25    spl11_24 <=> ! [X1,X0,X2] : (sP3(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).
% 14.19/2.25  fof(f1150,plain,(
% 14.19/2.25    ( ! [X0,X1] : (sP3(sK8,sK6,k4_enumset1(sK6,sK6,sK6,sK6,X0,X1))) ) | (~spl11_24 | spl11_38 | ~spl11_82)),
% 14.19/2.25    inference(unit_resulting_resolution,[],[f873,f347,f240])).
% 14.19/2.25  fof(f240,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) ) | ~spl11_24),
% 14.19/2.25    inference(avatar_component_clause,[],[f239])).
% 14.19/2.25  fof(f2459,plain,(
% 14.19/2.25    spl11_154 | ~spl11_14 | ~spl11_73),
% 14.19/2.25    inference(avatar_split_clause,[],[f809,f739,f184,f2457])).
% 14.19/2.25  fof(f184,plain,(
% 14.19/2.25    spl11_14 <=> ! [X1,X0,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP3(X2,X0,X1))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 14.19/2.25  fof(f739,plain,(
% 14.19/2.25    spl11_73 <=> ! [X1,X0,X2] : (k4_enumset1(X0,X0,X0,X0,X0,X0) = k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_73])])).
% 14.19/2.25  fof(f809,plain,(
% 14.19/2.25    ( ! [X14,X15,X13,X16] : (r2_hidden(X13,k5_xboole_0(X14,X15)) | k4_enumset1(X16,X16,X16,X16,X16,X16) = k3_xboole_0(k4_enumset1(X16,X16,X16,X16,X16,X13),k5_xboole_0(X14,X15)) | ~sP3(X15,X16,X14)) ) | (~spl11_14 | ~spl11_73)),
% 14.19/2.25    inference(resolution,[],[f740,f185])).
% 14.19/2.25  fof(f185,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP3(X2,X0,X1)) ) | ~spl11_14),
% 14.19/2.25    inference(avatar_component_clause,[],[f184])).
% 14.19/2.25  fof(f740,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(X2,X1) | k4_enumset1(X0,X0,X0,X0,X0,X0) = k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1)) ) | ~spl11_73),
% 14.19/2.25    inference(avatar_component_clause,[],[f739])).
% 14.19/2.25  fof(f2273,plain,(
% 14.19/2.25    spl11_142 | ~spl11_14 | ~spl11_63),
% 14.19/2.25    inference(avatar_split_clause,[],[f636,f618,f184,f2271])).
% 14.19/2.25  fof(f618,plain,(
% 14.19/2.25    spl11_63 <=> ! [X1,X2] : (k4_enumset1(X2,X2,X2,X2,X2,X2) = k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),X1) | ~r2_hidden(X2,X1))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_63])])).
% 14.19/2.25  fof(f636,plain,(
% 14.19/2.25    ( ! [X4,X5,X3] : (k4_enumset1(X3,X3,X3,X3,X3,X3) = k3_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X3),k5_xboole_0(X4,X5)) | ~sP3(X5,X3,X4)) ) | (~spl11_14 | ~spl11_63)),
% 14.19/2.25    inference(resolution,[],[f619,f185])).
% 14.19/2.25  fof(f619,plain,(
% 14.19/2.25    ( ! [X2,X1] : (~r2_hidden(X2,X1) | k4_enumset1(X2,X2,X2,X2,X2,X2) = k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),X1)) ) | ~spl11_63),
% 14.19/2.25    inference(avatar_component_clause,[],[f618])).
% 14.19/2.25  fof(f1267,plain,(
% 14.19/2.25    spl11_103 | ~spl11_29 | ~spl11_53),
% 14.19/2.25    inference(avatar_split_clause,[],[f545,f538,f275,f1265])).
% 14.19/2.25  fof(f275,plain,(
% 14.19/2.25    spl11_29 <=> ! [X1,X0,X2] : sP5(X0,X1,X2,k4_enumset1(X0,X0,X0,X0,X1,X2))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).
% 14.19/2.25  fof(f538,plain,(
% 14.19/2.25    spl11_53 <=> ! [X1,X0,X2] : k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X1,X1,X1,X1,X0,X2)),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_53])])).
% 14.19/2.25  fof(f545,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (sP5(X0,X1,X2,k4_enumset1(X1,X1,X1,X1,X0,X2))) ) | (~spl11_29 | ~spl11_53)),
% 14.19/2.25    inference(superposition,[],[f276,f539])).
% 14.19/2.25  fof(f539,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X1,X1,X1,X1,X0,X2)) ) | ~spl11_53),
% 14.19/2.25    inference(avatar_component_clause,[],[f538])).
% 14.19/2.25  fof(f276,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (sP5(X0,X1,X2,k4_enumset1(X0,X0,X0,X0,X1,X2))) ) | ~spl11_29),
% 14.19/2.25    inference(avatar_component_clause,[],[f275])).
% 14.19/2.25  fof(f1250,plain,(
% 14.19/2.25    spl11_101 | ~spl11_1 | ~spl11_7 | ~spl11_39),
% 14.19/2.25    inference(avatar_split_clause,[],[f435,f350,f152,f128,f1248])).
% 14.19/2.25  fof(f128,plain,(
% 14.19/2.25    spl11_1 <=> ! [X0] : k3_xboole_0(X0,X0) = X0),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 14.19/2.25  fof(f350,plain,(
% 14.19/2.25    spl11_39 <=> ! [X1,X0,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_39])])).
% 14.19/2.25  fof(f435,plain,(
% 14.19/2.25    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X1,X0),X0) = k3_xboole_0(X0,k5_xboole_0(X1,X0))) ) | (~spl11_1 | ~spl11_7 | ~spl11_39)),
% 14.19/2.25    inference(forward_demodulation,[],[f419,f153])).
% 14.19/2.25  fof(f419,plain,(
% 14.19/2.25    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X1,X0),X0) = k3_xboole_0(k5_xboole_0(X1,X0),X0)) ) | (~spl11_1 | ~spl11_39)),
% 14.19/2.25    inference(superposition,[],[f351,f129])).
% 14.19/2.25  fof(f129,plain,(
% 14.19/2.25    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | ~spl11_1),
% 14.19/2.25    inference(avatar_component_clause,[],[f128])).
% 14.19/2.25  fof(f351,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) ) | ~spl11_39),
% 14.19/2.25    inference(avatar_component_clause,[],[f350])).
% 14.19/2.25  fof(f1109,plain,(
% 14.19/2.25    ~spl11_72 | ~spl11_82 | ~spl11_93),
% 14.19/2.25    inference(avatar_contradiction_clause,[],[f1108])).
% 14.19/2.25  fof(f1108,plain,(
% 14.19/2.25    $false | (~spl11_72 | ~spl11_82 | ~spl11_93)),
% 14.19/2.25    inference(subsumption_resolution,[],[f1097,f736])).
% 14.19/2.25  fof(f736,plain,(
% 14.19/2.25    ( ! [X0] : (~sP3(k3_xboole_0(sK8,X0),sK6,X0)) ) | ~spl11_72),
% 14.19/2.25    inference(avatar_component_clause,[],[f735])).
% 14.19/2.25  fof(f735,plain,(
% 14.19/2.25    spl11_72 <=> ! [X0] : ~sP3(k3_xboole_0(sK8,X0),sK6,X0)),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_72])])).
% 14.19/2.25  fof(f1097,plain,(
% 14.19/2.25    sP3(k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)),sK6,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)) | (~spl11_82 | ~spl11_93)),
% 14.19/2.25    inference(unit_resulting_resolution,[],[f873,f1070])).
% 14.19/2.25  fof(f1070,plain,(
% 14.19/2.25    ( ! [X3] : (sP3(k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)),X3,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)) | ~r2_hidden(X3,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6))) ) | ~spl11_93),
% 14.19/2.25    inference(avatar_component_clause,[],[f1069])).
% 14.19/2.25  fof(f1069,plain,(
% 14.19/2.25    spl11_93 <=> ! [X3] : (~r2_hidden(X3,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6)) | sP3(k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)),X3,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_93])])).
% 14.19/2.25  fof(f1071,plain,(
% 14.19/2.25    spl11_93 | ~spl11_12 | ~spl11_36),
% 14.19/2.25    inference(avatar_split_clause,[],[f387,f328,f176,f1069])).
% 14.19/2.25  fof(f387,plain,(
% 14.19/2.25    ( ! [X3] : (~r2_hidden(X3,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6)) | sP3(k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7)),X3,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7))) ) | (~spl11_12 | ~spl11_36)),
% 14.19/2.25    inference(superposition,[],[f177,f371])).
% 14.19/2.25  fof(f874,plain,(
% 14.19/2.25    spl11_82 | ~spl11_4 | ~spl11_29 | ~spl11_45),
% 14.19/2.25    inference(avatar_split_clause,[],[f471,f400,f275,f140,f872])).
% 14.19/2.25  fof(f140,plain,(
% 14.19/2.25    spl11_4 <=> ! [X1,X3,X2] : sP4(X3,X1,X2,X3)),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 14.19/2.25  fof(f400,plain,(
% 14.19/2.25    spl11_45 <=> ! [X1,X3,X5,X0,X2] : (r2_hidden(X5,X3) | ~sP4(X5,X2,X1,X0) | ~sP5(X0,X1,X2,X3))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_45])])).
% 14.19/2.25  fof(f471,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2))) ) | (~spl11_4 | ~spl11_29 | ~spl11_45)),
% 14.19/2.25    inference(unit_resulting_resolution,[],[f141,f276,f401])).
% 14.19/2.25  fof(f401,plain,(
% 14.19/2.25    ( ! [X2,X0,X5,X3,X1] : (~sP5(X0,X1,X2,X3) | ~sP4(X5,X2,X1,X0) | r2_hidden(X5,X3)) ) | ~spl11_45),
% 14.19/2.25    inference(avatar_component_clause,[],[f400])).
% 14.19/2.25  fof(f141,plain,(
% 14.19/2.25    ( ! [X2,X3,X1] : (sP4(X3,X1,X2,X3)) ) | ~spl11_4),
% 14.19/2.25    inference(avatar_component_clause,[],[f140])).
% 14.19/2.25  fof(f834,plain,(
% 14.19/2.25    spl11_79 | ~spl11_2 | ~spl11_29 | ~spl11_45),
% 14.19/2.25    inference(avatar_split_clause,[],[f469,f400,f275,f132,f832])).
% 14.19/2.25  fof(f132,plain,(
% 14.19/2.25    spl11_2 <=> ! [X1,X3,X2] : sP4(X1,X1,X2,X3)),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 14.19/2.25  fof(f469,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0))) ) | (~spl11_2 | ~spl11_29 | ~spl11_45)),
% 14.19/2.25    inference(unit_resulting_resolution,[],[f133,f276,f401])).
% 14.19/2.25  fof(f133,plain,(
% 14.19/2.25    ( ! [X2,X3,X1] : (sP4(X1,X1,X2,X3)) ) | ~spl11_2),
% 14.19/2.25    inference(avatar_component_clause,[],[f132])).
% 14.19/2.25  fof(f741,plain,(
% 14.19/2.25    spl11_73),
% 14.19/2.25    inference(avatar_split_clause,[],[f114,f739])).
% 14.19/2.25  fof(f114,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X0) = k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 14.19/2.25    inference(definition_unfolding,[],[f76,f109,f108])).
% 14.19/2.25  fof(f108,plain,(
% 14.19/2.25    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 14.19/2.25    inference(definition_unfolding,[],[f71,f107])).
% 14.19/2.25  fof(f107,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 14.19/2.25    inference(definition_unfolding,[],[f74,f106])).
% 14.19/2.25  fof(f106,plain,(
% 14.19/2.25    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 14.19/2.25    inference(definition_unfolding,[],[f94,f105])).
% 14.19/2.25  fof(f105,plain,(
% 14.19/2.25    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 14.19/2.25    inference(cnf_transformation,[],[f13])).
% 14.19/2.25  fof(f13,axiom,(
% 14.19/2.25    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 14.19/2.25    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 14.19/2.25  fof(f94,plain,(
% 14.19/2.25    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 14.19/2.25    inference(cnf_transformation,[],[f12])).
% 14.19/2.25  fof(f12,axiom,(
% 14.19/2.25    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 14.19/2.25    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 14.19/2.25  fof(f74,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 14.19/2.25    inference(cnf_transformation,[],[f11])).
% 14.19/2.25  fof(f11,axiom,(
% 14.19/2.25    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 14.19/2.25    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 14.19/2.25  fof(f71,plain,(
% 14.19/2.25    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 14.19/2.25    inference(cnf_transformation,[],[f10])).
% 14.19/2.25  fof(f10,axiom,(
% 14.19/2.25    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 14.19/2.25    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 14.19/2.25  fof(f109,plain,(
% 14.19/2.25    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 14.19/2.25    inference(definition_unfolding,[],[f67,f108])).
% 14.19/2.25  fof(f67,plain,(
% 14.19/2.25    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 14.19/2.25    inference(cnf_transformation,[],[f9])).
% 14.19/2.25  fof(f9,axiom,(
% 14.19/2.25    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 14.19/2.25    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 14.19/2.25  fof(f76,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 14.19/2.25    inference(cnf_transformation,[],[f22])).
% 14.19/2.25  fof(f22,plain,(
% 14.19/2.25    ! [X0,X1,X2] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 14.19/2.25    inference(flattening,[],[f21])).
% 14.19/2.25  fof(f21,plain,(
% 14.19/2.25    ! [X0,X1,X2] : ((k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))) | ~r2_hidden(X0,X1))),
% 14.19/2.25    inference(ennf_transformation,[],[f16])).
% 14.19/2.25  fof(f16,axiom,(
% 14.19/2.25    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 14.19/2.25    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 14.19/2.25  fof(f737,plain,(
% 14.19/2.25    spl11_72 | ~spl11_7 | ~spl11_70),
% 14.19/2.25    inference(avatar_split_clause,[],[f722,f689,f152,f735])).
% 14.19/2.25  fof(f689,plain,(
% 14.19/2.25    spl11_70 <=> ! [X0] : ~sP3(k3_xboole_0(X0,sK8),sK6,X0)),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_70])])).
% 14.19/2.25  fof(f722,plain,(
% 14.19/2.25    ( ! [X0] : (~sP3(k3_xboole_0(sK8,X0),sK6,X0)) ) | (~spl11_7 | ~spl11_70)),
% 14.19/2.25    inference(superposition,[],[f690,f153])).
% 14.19/2.25  fof(f690,plain,(
% 14.19/2.25    ( ! [X0] : (~sP3(k3_xboole_0(X0,sK8),sK6,X0)) ) | ~spl11_70),
% 14.19/2.25    inference(avatar_component_clause,[],[f689])).
% 14.19/2.25  fof(f691,plain,(
% 14.19/2.25    spl11_70 | ~spl11_14 | ~spl11_65),
% 14.19/2.25    inference(avatar_split_clause,[],[f654,f642,f184,f689])).
% 14.19/2.25  fof(f642,plain,(
% 14.19/2.25    spl11_65 <=> ! [X0] : ~r2_hidden(sK6,k5_xboole_0(X0,k3_xboole_0(X0,sK8)))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_65])])).
% 14.19/2.25  fof(f654,plain,(
% 14.19/2.25    ( ! [X0] : (~sP3(k3_xboole_0(X0,sK8),sK6,X0)) ) | (~spl11_14 | ~spl11_65)),
% 14.19/2.25    inference(unit_resulting_resolution,[],[f643,f185])).
% 14.19/2.25  fof(f643,plain,(
% 14.19/2.25    ( ! [X0] : (~r2_hidden(sK6,k5_xboole_0(X0,k3_xboole_0(X0,sK8)))) ) | ~spl11_65),
% 14.19/2.25    inference(avatar_component_clause,[],[f642])).
% 14.19/2.25  fof(f644,plain,(
% 14.19/2.25    spl11_65 | ~spl11_11 | ~spl11_26 | ~spl11_52),
% 14.19/2.25    inference(avatar_split_clause,[],[f528,f519,f263,f169,f642])).
% 14.19/2.25  fof(f169,plain,(
% 14.19/2.25    spl11_11 <=> ! [X1,X0] : sP2(X0,X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 14.19/2.25  fof(f263,plain,(
% 14.19/2.25    spl11_26 <=> ! [X1,X0,X2,X4] : (sP1(X1,X4,X0) | ~r2_hidden(X4,X2) | ~sP2(X0,X1,X2))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).
% 14.19/2.25  fof(f519,plain,(
% 14.19/2.25    spl11_52 <=> ! [X0] : ~sP1(sK8,sK6,X0)),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).
% 14.19/2.25  fof(f528,plain,(
% 14.19/2.25    ( ! [X0] : (~r2_hidden(sK6,k5_xboole_0(X0,k3_xboole_0(X0,sK8)))) ) | (~spl11_11 | ~spl11_26 | ~spl11_52)),
% 14.19/2.25    inference(unit_resulting_resolution,[],[f170,f520,f264])).
% 14.19/2.25  fof(f264,plain,(
% 14.19/2.25    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_hidden(X4,X2) | sP1(X1,X4,X0)) ) | ~spl11_26),
% 14.19/2.25    inference(avatar_component_clause,[],[f263])).
% 14.19/2.25  fof(f520,plain,(
% 14.19/2.25    ( ! [X0] : (~sP1(sK8,sK6,X0)) ) | ~spl11_52),
% 14.19/2.25    inference(avatar_component_clause,[],[f519])).
% 14.19/2.25  fof(f170,plain,(
% 14.19/2.25    ( ! [X0,X1] : (sP2(X0,X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ) | ~spl11_11),
% 14.19/2.25    inference(avatar_component_clause,[],[f169])).
% 14.19/2.25  fof(f620,plain,(
% 14.19/2.25    spl11_63),
% 14.19/2.25    inference(avatar_split_clause,[],[f121,f618])).
% 14.19/2.25  fof(f121,plain,(
% 14.19/2.25    ( ! [X2,X1] : (k4_enumset1(X2,X2,X2,X2,X2,X2) = k3_xboole_0(k4_enumset1(X2,X2,X2,X2,X2,X2),X1) | ~r2_hidden(X2,X1)) )),
% 14.19/2.25    inference(equality_resolution,[],[f113])).
% 14.19/2.25  fof(f113,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X0) = k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) | X0 != X2 | ~r2_hidden(X0,X1)) )),
% 14.19/2.25    inference(definition_unfolding,[],[f77,f109,f108])).
% 14.19/2.25  fof(f77,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | X0 != X2 | ~r2_hidden(X0,X1)) )),
% 14.19/2.25    inference(cnf_transformation,[],[f22])).
% 14.19/2.25  fof(f540,plain,(
% 14.19/2.25    spl11_53),
% 14.19/2.25    inference(avatar_split_clause,[],[f112,f538])).
% 14.19/2.25  fof(f112,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = k4_enumset1(X1,X1,X1,X1,X0,X2)) )),
% 14.19/2.25    inference(definition_unfolding,[],[f73,f107,f107])).
% 14.19/2.25  fof(f73,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)) )),
% 14.19/2.25    inference(cnf_transformation,[],[f14])).
% 14.19/2.25  fof(f14,axiom,(
% 14.19/2.25    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 14.19/2.25    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).
% 14.19/2.25  fof(f521,plain,(
% 14.19/2.25    spl11_52 | ~spl11_9 | ~spl11_38),
% 14.19/2.25    inference(avatar_split_clause,[],[f501,f346,f160,f519])).
% 14.19/2.25  fof(f160,plain,(
% 14.19/2.25    spl11_9 <=> ! [X1,X0,X2] : (~r2_hidden(X1,X0) | ~sP1(X0,X1,X2))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 14.19/2.25  fof(f501,plain,(
% 14.19/2.25    ( ! [X0] : (~sP1(sK8,sK6,X0)) ) | (~spl11_9 | ~spl11_38)),
% 14.19/2.25    inference(unit_resulting_resolution,[],[f498,f161])).
% 14.19/2.25  fof(f161,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X1,X0)) ) | ~spl11_9),
% 14.19/2.25    inference(avatar_component_clause,[],[f160])).
% 14.19/2.25  fof(f498,plain,(
% 14.19/2.25    r2_hidden(sK6,sK8) | ~spl11_38),
% 14.19/2.25    inference(avatar_component_clause,[],[f346])).
% 14.19/2.25  fof(f499,plain,(
% 14.19/2.25    spl11_38 | ~spl11_46 | ~spl11_19 | spl11_34),
% 14.19/2.25    inference(avatar_split_clause,[],[f370,f313,f215,f448,f346])).
% 14.19/2.25  fof(f215,plain,(
% 14.19/2.25    spl11_19 <=> ! [X1,X0,X2] : (sP0(X0,X1,X2) | ~r2_hidden(X0,X2) | r2_hidden(X1,X2))),
% 14.19/2.25    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).
% 14.19/2.25  fof(f370,plain,(
% 14.19/2.25    ~r2_hidden(sK7,sK8) | r2_hidden(sK6,sK8) | (~spl11_19 | spl11_34)),
% 14.19/2.25    inference(resolution,[],[f314,f216])).
% 14.19/2.25  fof(f216,plain,(
% 14.19/2.25    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r2_hidden(X0,X2) | r2_hidden(X1,X2)) ) | ~spl11_19),
% 14.19/2.25    inference(avatar_component_clause,[],[f215])).
% 14.19/2.25  fof(f481,plain,(
% 14.19/2.25    spl11_48),
% 14.19/2.25    inference(avatar_split_clause,[],[f99,f479])).
% 14.19/2.25  fof(f99,plain,(
% 14.19/2.25    ( ! [X2,X0,X3,X1] : (X0 = X1 | X0 = X2 | X0 = X3 | ~sP4(X0,X1,X2,X3)) )),
% 14.19/2.25    inference(cnf_transformation,[],[f59])).
% 14.19/2.25  fof(f59,plain,(
% 14.19/2.25    ! [X0,X1,X2,X3] : ((sP4(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP4(X0,X1,X2,X3)))),
% 14.19/2.25    inference(rectify,[],[f58])).
% 14.19/2.25  fof(f58,plain,(
% 14.19/2.25    ! [X4,X2,X1,X0] : ((sP4(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP4(X4,X2,X1,X0)))),
% 14.19/2.25    inference(flattening,[],[f57])).
% 14.19/2.25  fof(f57,plain,(
% 14.19/2.25    ! [X4,X2,X1,X0] : ((sP4(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP4(X4,X2,X1,X0)))),
% 14.19/2.25    inference(nnf_transformation,[],[f33])).
% 14.19/2.25  fof(f33,plain,(
% 14.19/2.25    ! [X4,X2,X1,X0] : (sP4(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 14.19/2.25    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 14.19/2.25  fof(f402,plain,(
% 14.19/2.25    spl11_45),
% 14.19/2.25    inference(avatar_split_clause,[],[f96,f400])).
% 14.19/2.25  fof(f96,plain,(
% 14.19/2.25    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | ~sP4(X5,X2,X1,X0) | ~sP5(X0,X1,X2,X3)) )),
% 14.19/2.25    inference(cnf_transformation,[],[f56])).
% 14.19/2.25  fof(f56,plain,(
% 14.19/2.25    ! [X0,X1,X2,X3] : ((sP5(X0,X1,X2,X3) | ((~sP4(sK10(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK10(X0,X1,X2,X3),X3)) & (sP4(sK10(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK10(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP4(X5,X2,X1,X0)) & (sP4(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP5(X0,X1,X2,X3)))),
% 14.19/2.25    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f54,f55])).
% 14.19/2.25  fof(f55,plain,(
% 14.19/2.25    ! [X3,X2,X1,X0] : (? [X4] : ((~sP4(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP4(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP4(sK10(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK10(X0,X1,X2,X3),X3)) & (sP4(sK10(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK10(X0,X1,X2,X3),X3))))),
% 14.19/2.25    introduced(choice_axiom,[])).
% 14.19/2.25  fof(f54,plain,(
% 14.19/2.25    ! [X0,X1,X2,X3] : ((sP5(X0,X1,X2,X3) | ? [X4] : ((~sP4(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP4(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP4(X5,X2,X1,X0)) & (sP4(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP5(X0,X1,X2,X3)))),
% 14.19/2.25    inference(rectify,[],[f53])).
% 14.19/2.26  fof(f53,plain,(
% 14.19/2.26    ! [X0,X1,X2,X3] : ((sP5(X0,X1,X2,X3) | ? [X4] : ((~sP4(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP4(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP4(X4,X2,X1,X0)) & (sP4(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP5(X0,X1,X2,X3)))),
% 14.19/2.26    inference(nnf_transformation,[],[f34])).
% 14.19/2.26  fof(f34,plain,(
% 14.19/2.26    ! [X0,X1,X2,X3] : (sP5(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP4(X4,X2,X1,X0)))),
% 14.19/2.26    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 14.19/2.26  fof(f372,plain,(
% 14.19/2.26    spl11_36 | ~spl11_7 | ~spl11_33),
% 14.19/2.26    inference(avatar_split_clause,[],[f369,f310,f152,f328])).
% 14.19/2.26  fof(f369,plain,(
% 14.19/2.26    k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) = k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k3_xboole_0(sK8,k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7))) | (~spl11_7 | ~spl11_33)),
% 14.19/2.26    inference(forward_demodulation,[],[f335,f153])).
% 14.19/2.26  fof(f335,plain,(
% 14.19/2.26    k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) = k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),sK8)) | ~spl11_33),
% 14.19/2.26    inference(avatar_component_clause,[],[f310])).
% 14.19/2.26  fof(f368,plain,(
% 14.19/2.26    spl11_42 | ~spl11_10 | spl11_38),
% 14.19/2.26    inference(avatar_split_clause,[],[f354,f346,f164,f366])).
% 14.19/2.26  fof(f164,plain,(
% 14.19/2.26    spl11_10 <=> ! [X1,X2] : (sP0(X1,X1,X2) | r2_hidden(X1,X2))),
% 14.19/2.26    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 14.19/2.26  fof(f354,plain,(
% 14.19/2.26    sP0(sK6,sK6,sK8) | (~spl11_10 | spl11_38)),
% 14.19/2.26    inference(unit_resulting_resolution,[],[f347,f165])).
% 14.19/2.26  fof(f165,plain,(
% 14.19/2.26    ( ! [X2,X1] : (sP0(X1,X1,X2) | r2_hidden(X1,X2)) ) | ~spl11_10),
% 14.19/2.26    inference(avatar_component_clause,[],[f164])).
% 14.19/2.26  fof(f364,plain,(
% 14.19/2.26    spl11_41),
% 14.19/2.26    inference(avatar_split_clause,[],[f95,f362])).
% 14.19/2.26  fof(f95,plain,(
% 14.19/2.26    ( ! [X2,X0,X5,X3,X1] : (sP4(X5,X2,X1,X0) | ~r2_hidden(X5,X3) | ~sP5(X0,X1,X2,X3)) )),
% 14.19/2.26    inference(cnf_transformation,[],[f56])).
% 14.19/2.26  fof(f352,plain,(
% 14.19/2.26    spl11_39),
% 14.19/2.26    inference(avatar_split_clause,[],[f75,f350])).
% 14.19/2.26  fof(f75,plain,(
% 14.19/2.26    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 14.19/2.26    inference(cnf_transformation,[],[f7])).
% 14.19/2.26  fof(f7,axiom,(
% 14.19/2.26    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 14.19/2.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 14.19/2.26  fof(f348,plain,(
% 14.19/2.26    ~spl11_38 | ~spl11_5 | ~spl11_34),
% 14.19/2.26    inference(avatar_split_clause,[],[f342,f313,f144,f346])).
% 14.19/2.26  fof(f144,plain,(
% 14.19/2.26    spl11_5 <=> ! [X1,X0,X2] : (~r2_hidden(X1,X2) | ~sP0(X0,X1,X2))),
% 14.19/2.26    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 14.19/2.26  fof(f342,plain,(
% 14.19/2.26    ~r2_hidden(sK6,sK8) | (~spl11_5 | ~spl11_34)),
% 14.19/2.26    inference(unit_resulting_resolution,[],[f336,f145])).
% 14.19/2.26  fof(f145,plain,(
% 14.19/2.26    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X1,X2)) ) | ~spl11_5),
% 14.19/2.26    inference(avatar_component_clause,[],[f144])).
% 14.19/2.26  fof(f337,plain,(
% 14.19/2.26    spl11_33 | spl11_34),
% 14.19/2.26    inference(avatar_split_clause,[],[f111,f313,f310])).
% 14.19/2.26  fof(f111,plain,(
% 14.19/2.26    sP0(sK7,sK6,sK8) | k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) = k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),sK8))),
% 14.19/2.26    inference(definition_unfolding,[],[f65,f109,f72,f108])).
% 14.19/2.26  fof(f72,plain,(
% 14.19/2.26    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 14.19/2.26    inference(cnf_transformation,[],[f6])).
% 14.19/2.26  fof(f6,axiom,(
% 14.19/2.26    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 14.19/2.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 14.19/2.26  fof(f65,plain,(
% 14.19/2.26    sP0(sK7,sK6,sK8) | k1_tarski(sK6) = k4_xboole_0(k2_tarski(sK6,sK7),sK8)),
% 14.19/2.26    inference(cnf_transformation,[],[f41])).
% 14.19/2.26  fof(f41,plain,(
% 14.19/2.26    (~sP0(sK7,sK6,sK8) | k1_tarski(sK6) != k4_xboole_0(k2_tarski(sK6,sK7),sK8)) & (sP0(sK7,sK6,sK8) | k1_tarski(sK6) = k4_xboole_0(k2_tarski(sK6,sK7),sK8))),
% 14.19/2.26    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f39,f40])).
% 14.19/2.26  fof(f40,plain,(
% 14.19/2.26    ? [X0,X1,X2] : ((~sP0(X1,X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (sP0(X1,X0,X2) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((~sP0(sK7,sK6,sK8) | k1_tarski(sK6) != k4_xboole_0(k2_tarski(sK6,sK7),sK8)) & (sP0(sK7,sK6,sK8) | k1_tarski(sK6) = k4_xboole_0(k2_tarski(sK6,sK7),sK8)))),
% 14.19/2.26    introduced(choice_axiom,[])).
% 14.19/2.26  fof(f39,plain,(
% 14.19/2.26    ? [X0,X1,X2] : ((~sP0(X1,X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (sP0(X1,X0,X2) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 14.19/2.26    inference(nnf_transformation,[],[f27])).
% 14.19/2.26  fof(f27,plain,(
% 14.19/2.26    ? [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> sP0(X1,X0,X2))),
% 14.19/2.26    inference(definition_folding,[],[f20,f26])).
% 14.19/2.26  fof(f26,plain,(
% 14.19/2.26    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 14.19/2.26    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 14.19/2.26  fof(f20,plain,(
% 14.19/2.26    ? [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 14.19/2.26    inference(ennf_transformation,[],[f18])).
% 14.19/2.26  fof(f18,negated_conjecture,(
% 14.19/2.26    ~! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 14.19/2.26    inference(negated_conjecture,[],[f17])).
% 14.19/2.26  fof(f17,conjecture,(
% 14.19/2.26    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 14.19/2.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_zfmisc_1)).
% 14.19/2.26  fof(f315,plain,(
% 14.19/2.26    ~spl11_33 | ~spl11_34),
% 14.19/2.26    inference(avatar_split_clause,[],[f110,f313,f310])).
% 14.19/2.26  fof(f110,plain,(
% 14.19/2.26    ~sP0(sK7,sK6,sK8) | k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK6) != k5_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),k3_xboole_0(k4_enumset1(sK6,sK6,sK6,sK6,sK6,sK7),sK8))),
% 14.19/2.26    inference(definition_unfolding,[],[f66,f109,f72,f108])).
% 14.19/2.26  fof(f66,plain,(
% 14.19/2.26    ~sP0(sK7,sK6,sK8) | k1_tarski(sK6) != k4_xboole_0(k2_tarski(sK6,sK7),sK8)),
% 14.19/2.26    inference(cnf_transformation,[],[f41])).
% 14.19/2.26  fof(f277,plain,(
% 14.19/2.26    spl11_29),
% 14.19/2.26    inference(avatar_split_clause,[],[f126,f275])).
% 14.19/2.26  fof(f126,plain,(
% 14.19/2.26    ( ! [X2,X0,X1] : (sP5(X0,X1,X2,k4_enumset1(X0,X0,X0,X0,X1,X2))) )),
% 14.19/2.26    inference(equality_resolution,[],[f119])).
% 14.19/2.26  fof(f119,plain,(
% 14.19/2.26    ( ! [X2,X0,X3,X1] : (sP5(X0,X1,X2,X3) | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3) )),
% 14.19/2.26    inference(definition_unfolding,[],[f103,f107])).
% 14.19/2.26  fof(f103,plain,(
% 14.19/2.26    ( ! [X2,X0,X3,X1] : (sP5(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 14.19/2.26    inference(cnf_transformation,[],[f60])).
% 14.19/2.26  fof(f60,plain,(
% 14.19/2.26    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP5(X0,X1,X2,X3)) & (sP5(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 14.19/2.26    inference(nnf_transformation,[],[f35])).
% 14.19/2.26  fof(f35,plain,(
% 14.19/2.26    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP5(X0,X1,X2,X3))),
% 14.19/2.26    inference(definition_folding,[],[f25,f34,f33])).
% 14.19/2.26  fof(f25,plain,(
% 14.19/2.26    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 14.19/2.26    inference(ennf_transformation,[],[f8])).
% 14.19/2.26  fof(f8,axiom,(
% 14.19/2.26    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 14.19/2.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 14.19/2.26  fof(f269,plain,(
% 14.19/2.26    spl11_27),
% 14.19/2.26    inference(avatar_split_clause,[],[f79,f267])).
% 14.19/2.26  fof(f79,plain,(
% 14.19/2.26    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~sP1(X1,X4,X0) | ~sP2(X0,X1,X2)) )),
% 14.19/2.26    inference(cnf_transformation,[],[f45])).
% 14.19/2.26  fof(f45,plain,(
% 14.19/2.26    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((~sP1(X1,sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (sP1(X1,sK9(X0,X1,X2),X0) | r2_hidden(sK9(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X1,X4,X0)) & (sP1(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 14.19/2.26    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f43,f44])).
% 14.19/2.26  fof(f44,plain,(
% 14.19/2.26    ! [X2,X1,X0] : (? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP1(X1,sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (sP1(X1,sK9(X0,X1,X2),X0) | r2_hidden(sK9(X0,X1,X2),X2))))),
% 14.19/2.26    introduced(choice_axiom,[])).
% 14.19/2.26  fof(f43,plain,(
% 14.19/2.26    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X1,X4,X0)) & (sP1(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 14.19/2.26    inference(rectify,[],[f42])).
% 14.19/2.26  fof(f42,plain,(
% 14.19/2.26    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP1(X1,X3,X0)) & (sP1(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP2(X0,X1,X2)))),
% 14.19/2.26    inference(nnf_transformation,[],[f29])).
% 14.19/2.26  fof(f29,plain,(
% 14.19/2.26    ! [X0,X1,X2] : (sP2(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP1(X1,X3,X0)))),
% 14.19/2.26    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 14.19/2.26  fof(f265,plain,(
% 14.19/2.26    spl11_26),
% 14.19/2.26    inference(avatar_split_clause,[],[f78,f263])).
% 14.19/2.26  fof(f78,plain,(
% 14.19/2.26    ( ! [X4,X2,X0,X1] : (sP1(X1,X4,X0) | ~r2_hidden(X4,X2) | ~sP2(X0,X1,X2)) )),
% 14.19/2.26    inference(cnf_transformation,[],[f45])).
% 14.19/2.26  fof(f245,plain,(
% 14.19/2.26    spl11_25),
% 14.19/2.26    inference(avatar_split_clause,[],[f90,f243])).
% 14.19/2.26  fof(f90,plain,(
% 14.19/2.26    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) )),
% 14.19/2.26    inference(cnf_transformation,[],[f51])).
% 14.19/2.26  fof(f51,plain,(
% 14.19/2.26    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ((r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~r2_hidden(X1,X2)))) & (((~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & (r2_hidden(X1,X0) | r2_hidden(X1,X2))) | ~sP3(X0,X1,X2)))),
% 14.19/2.26    inference(rectify,[],[f50])).
% 14.19/2.26  fof(f50,plain,(
% 14.19/2.26    ! [X2,X0,X1] : ((sP3(X2,X0,X1) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~sP3(X2,X0,X1)))),
% 14.19/2.26    inference(nnf_transformation,[],[f31])).
% 14.19/2.26  fof(f31,plain,(
% 14.19/2.26    ! [X2,X0,X1] : (sP3(X2,X0,X1) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 14.19/2.26    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 14.19/2.26  fof(f241,plain,(
% 14.19/2.26    spl11_24),
% 14.19/2.26    inference(avatar_split_clause,[],[f89,f239])).
% 14.19/2.26  fof(f89,plain,(
% 14.19/2.26    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 14.19/2.26    inference(cnf_transformation,[],[f51])).
% 14.19/2.26  fof(f237,plain,(
% 14.19/2.26    spl11_23),
% 14.19/2.26    inference(avatar_split_clause,[],[f88,f235])).
% 14.19/2.26  fof(f88,plain,(
% 14.19/2.26    ( ! [X2,X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,X2) | ~sP3(X0,X1,X2)) )),
% 14.19/2.26    inference(cnf_transformation,[],[f51])).
% 14.19/2.26  fof(f225,plain,(
% 14.19/2.26    spl11_21),
% 14.19/2.26    inference(avatar_split_clause,[],[f84,f223])).
% 14.19/2.26  fof(f84,plain,(
% 14.19/2.26    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 14.19/2.26    inference(cnf_transformation,[],[f48])).
% 14.19/2.26  fof(f48,plain,(
% 14.19/2.26    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP1(X0,X1,X2)))),
% 14.19/2.26    inference(rectify,[],[f47])).
% 14.19/2.26  fof(f47,plain,(
% 14.19/2.26    ! [X1,X3,X0] : ((sP1(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP1(X1,X3,X0)))),
% 14.19/2.26    inference(flattening,[],[f46])).
% 14.19/2.26  fof(f46,plain,(
% 14.19/2.26    ! [X1,X3,X0] : ((sP1(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP1(X1,X3,X0)))),
% 14.19/2.26    inference(nnf_transformation,[],[f28])).
% 14.19/2.26  fof(f28,plain,(
% 14.19/2.26    ! [X1,X3,X0] : (sP1(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 14.19/2.26    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 14.19/2.26  fof(f217,plain,(
% 14.19/2.26    spl11_19),
% 14.19/2.26    inference(avatar_split_clause,[],[f63,f215])).
% 14.19/2.26  fof(f63,plain,(
% 14.19/2.26    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r2_hidden(X0,X2) | r2_hidden(X1,X2)) )),
% 14.19/2.26    inference(cnf_transformation,[],[f38])).
% 14.19/2.26  fof(f38,plain,(
% 14.19/2.26    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (X0 != X1 & ~r2_hidden(X0,X2)) | r2_hidden(X1,X2)) & (((X0 = X1 | r2_hidden(X0,X2)) & ~r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 14.19/2.26    inference(rectify,[],[f37])).
% 14.19/2.26  fof(f37,plain,(
% 14.19/2.26    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | ~sP0(X1,X0,X2)))),
% 14.19/2.26    inference(flattening,[],[f36])).
% 14.19/2.26  fof(f36,plain,(
% 14.19/2.26    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | ~sP0(X1,X0,X2)))),
% 14.19/2.26    inference(nnf_transformation,[],[f26])).
% 14.19/2.26  fof(f206,plain,(
% 14.19/2.26    spl11_17),
% 14.19/2.26    inference(avatar_split_clause,[],[f62,f204])).
% 14.19/2.26  fof(f62,plain,(
% 14.19/2.26    ( ! [X2,X0,X1] : (X0 = X1 | r2_hidden(X0,X2) | ~sP0(X0,X1,X2)) )),
% 14.19/2.26    inference(cnf_transformation,[],[f38])).
% 14.19/2.26  fof(f190,plain,(
% 14.19/2.26    spl11_15 | ~spl11_7 | ~spl11_11),
% 14.19/2.26    inference(avatar_split_clause,[],[f173,f169,f152,f188])).
% 14.19/2.26  fof(f173,plain,(
% 14.19/2.26    ( ! [X2,X1] : (sP2(X1,X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) ) | (~spl11_7 | ~spl11_11)),
% 14.19/2.26    inference(superposition,[],[f170,f153])).
% 14.19/2.26  fof(f186,plain,(
% 14.19/2.26    spl11_14),
% 14.19/2.26    inference(avatar_split_clause,[],[f92,f184])).
% 14.19/2.26  fof(f92,plain,(
% 14.19/2.26    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP3(X2,X0,X1)) )),
% 14.19/2.26    inference(cnf_transformation,[],[f52])).
% 14.19/2.26  fof(f52,plain,(
% 14.19/2.26    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP3(X2,X0,X1)) & (sP3(X2,X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 14.19/2.26    inference(nnf_transformation,[],[f32])).
% 14.19/2.26  fof(f32,plain,(
% 14.19/2.26    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> sP3(X2,X0,X1))),
% 14.19/2.26    inference(definition_folding,[],[f23,f31])).
% 14.19/2.26  fof(f23,plain,(
% 14.19/2.26    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 14.19/2.26    inference(ennf_transformation,[],[f5])).
% 14.19/2.26  fof(f5,axiom,(
% 14.19/2.26    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 14.19/2.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 14.19/2.26  fof(f178,plain,(
% 14.19/2.26    spl11_12),
% 14.19/2.26    inference(avatar_split_clause,[],[f91,f176])).
% 14.19/2.26  fof(f91,plain,(
% 14.19/2.26    ( ! [X2,X0,X1] : (sP3(X2,X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 14.19/2.26    inference(cnf_transformation,[],[f52])).
% 14.19/2.26  fof(f171,plain,(
% 14.19/2.26    spl11_11),
% 14.19/2.26    inference(avatar_split_clause,[],[f122,f169])).
% 14.19/2.26  fof(f122,plain,(
% 14.19/2.26    ( ! [X0,X1] : (sP2(X0,X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 14.19/2.26    inference(equality_resolution,[],[f116])).
% 14.19/2.26  fof(f116,plain,(
% 14.19/2.26    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 14.19/2.26    inference(definition_unfolding,[],[f85,f72])).
% 14.19/2.26  fof(f85,plain,(
% 14.19/2.26    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | k4_xboole_0(X0,X1) != X2) )),
% 14.19/2.26    inference(cnf_transformation,[],[f49])).
% 14.19/2.26  fof(f49,plain,(
% 14.19/2.26    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP2(X0,X1,X2)) & (sP2(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 14.19/2.26    inference(nnf_transformation,[],[f30])).
% 14.19/2.26  fof(f30,plain,(
% 14.19/2.26    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP2(X0,X1,X2))),
% 14.19/2.26    inference(definition_folding,[],[f3,f29,f28])).
% 14.19/2.26  fof(f3,axiom,(
% 14.19/2.26    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 14.19/2.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 14.19/2.26  fof(f166,plain,(
% 14.19/2.26    spl11_10),
% 14.19/2.26    inference(avatar_split_clause,[],[f120,f164])).
% 14.19/2.26  fof(f120,plain,(
% 14.19/2.26    ( ! [X2,X1] : (sP0(X1,X1,X2) | r2_hidden(X1,X2)) )),
% 14.19/2.26    inference(equality_resolution,[],[f64])).
% 14.19/2.26  fof(f64,plain,(
% 14.19/2.26    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | X0 != X1 | r2_hidden(X1,X2)) )),
% 14.19/2.26    inference(cnf_transformation,[],[f38])).
% 14.19/2.26  fof(f162,plain,(
% 14.19/2.26    spl11_9),
% 14.19/2.26    inference(avatar_split_clause,[],[f83,f160])).
% 14.19/2.26  fof(f83,plain,(
% 14.19/2.26    ( ! [X2,X0,X1] : (~r2_hidden(X1,X0) | ~sP1(X0,X1,X2)) )),
% 14.19/2.26    inference(cnf_transformation,[],[f48])).
% 14.19/2.26  fof(f154,plain,(
% 14.19/2.26    spl11_7),
% 14.19/2.26    inference(avatar_split_clause,[],[f70,f152])).
% 14.19/2.26  fof(f70,plain,(
% 14.19/2.26    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 14.19/2.26    inference(cnf_transformation,[],[f1])).
% 14.19/2.26  fof(f1,axiom,(
% 14.19/2.26    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 14.19/2.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 14.19/2.26  fof(f150,plain,(
% 14.19/2.26    spl11_6),
% 14.19/2.26    inference(avatar_split_clause,[],[f69,f148])).
% 14.19/2.26  fof(f69,plain,(
% 14.19/2.26    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 14.19/2.26    inference(cnf_transformation,[],[f2])).
% 14.19/2.26  fof(f2,axiom,(
% 14.19/2.26    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 14.19/2.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 14.19/2.26  fof(f146,plain,(
% 14.19/2.26    spl11_5),
% 14.19/2.26    inference(avatar_split_clause,[],[f61,f144])).
% 14.19/2.26  fof(f61,plain,(
% 14.19/2.26    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | ~sP0(X0,X1,X2)) )),
% 14.19/2.26    inference(cnf_transformation,[],[f38])).
% 14.19/2.26  fof(f142,plain,(
% 14.19/2.26    spl11_4),
% 14.19/2.26    inference(avatar_split_clause,[],[f125,f140])).
% 14.19/2.26  fof(f125,plain,(
% 14.19/2.26    ( ! [X2,X3,X1] : (sP4(X3,X1,X2,X3)) )),
% 14.19/2.26    inference(equality_resolution,[],[f100])).
% 14.19/2.26  fof(f100,plain,(
% 14.19/2.26    ( ! [X2,X0,X3,X1] : (sP4(X0,X1,X2,X3) | X0 != X3) )),
% 14.19/2.26    inference(cnf_transformation,[],[f59])).
% 14.19/2.26  fof(f134,plain,(
% 14.19/2.26    spl11_2),
% 14.19/2.26    inference(avatar_split_clause,[],[f123,f132])).
% 14.19/2.26  fof(f123,plain,(
% 14.19/2.26    ( ! [X2,X3,X1] : (sP4(X1,X1,X2,X3)) )),
% 14.19/2.26    inference(equality_resolution,[],[f102])).
% 14.19/2.26  fof(f102,plain,(
% 14.19/2.26    ( ! [X2,X0,X3,X1] : (sP4(X0,X1,X2,X3) | X0 != X1) )),
% 14.19/2.26    inference(cnf_transformation,[],[f59])).
% 14.19/2.26  fof(f130,plain,(
% 14.19/2.26    spl11_1),
% 14.19/2.26    inference(avatar_split_clause,[],[f68,f128])).
% 14.19/2.26  fof(f68,plain,(
% 14.19/2.26    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 14.19/2.26    inference(cnf_transformation,[],[f19])).
% 14.19/2.26  fof(f19,plain,(
% 14.19/2.26    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 14.19/2.26    inference(rectify,[],[f4])).
% 14.19/2.26  fof(f4,axiom,(
% 14.19/2.26    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 14.19/2.26    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 14.19/2.26  % SZS output end Proof for theBenchmark
% 14.19/2.26  % (21881)------------------------------
% 14.19/2.26  % (21881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.19/2.26  % (21881)Termination reason: Refutation
% 14.19/2.26  
% 14.19/2.26  % (21881)Memory used [KB]: 20596
% 14.19/2.26  % (21881)Time elapsed: 0.772 s
% 14.19/2.26  % (21881)------------------------------
% 14.19/2.26  % (21881)------------------------------
% 14.19/2.26  % (21595)Success in time 1.896 s
%------------------------------------------------------------------------------
