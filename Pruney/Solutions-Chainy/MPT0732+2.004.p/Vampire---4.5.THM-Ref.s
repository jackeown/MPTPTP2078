%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:15 EST 2020

% Result     : Theorem 10.33s
% Output     : Refutation 10.33s
% Verified   : 
% Statistics : Number of formulae       :  245 ( 444 expanded)
%              Number of leaves         :   64 ( 221 expanded)
%              Depth                    :    7
%              Number of atoms          :  636 (1147 expanded)
%              Number of equality atoms :   93 ( 198 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6025,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f129,f134,f139,f144,f148,f152,f156,f160,f164,f176,f184,f188,f192,f200,f204,f208,f224,f305,f320,f336,f345,f354,f565,f591,f603,f671,f679,f751,f791,f805,f830,f839,f850,f981,f1018,f1260,f1503,f2041,f2201,f2453,f2755,f2784,f2882,f2958,f5502,f5518,f5587,f5725,f5924,f6004])).

fof(f6004,plain,
    ( ~ spl4_8
    | ~ spl4_633
    | ~ spl4_687 ),
    inference(avatar_contradiction_clause,[],[f6003])).

fof(f6003,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_633
    | ~ spl4_687 ),
    inference(subsumption_resolution,[],[f5979,f138])).

fof(f138,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl4_8
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f5979,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl4_633
    | ~ spl4_687 ),
    inference(resolution,[],[f5923,f5586])).

fof(f5586,plain,
    ( r1_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl4_633 ),
    inference(avatar_component_clause,[],[f5584])).

fof(f5584,plain,
    ( spl4_633
  <=> r1_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_633])])).

fof(f5923,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(k1_tarski(X2),X3)
        | ~ r2_hidden(X2,X3) )
    | ~ spl4_687 ),
    inference(avatar_component_clause,[],[f5922])).

fof(f5922,plain,
    ( spl4_687
  <=> ! [X3,X2] :
        ( ~ r1_xboole_0(k1_tarski(X2),X3)
        | ~ r2_hidden(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_687])])).

fof(f5924,plain,
    ( spl4_687
    | ~ spl4_29
    | ~ spl4_656 ),
    inference(avatar_split_clause,[],[f5904,f5722,f222,f5922])).

fof(f222,plain,
    ( spl4_29
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X2)
        | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f5722,plain,
    ( spl4_656
  <=> ! [X1] : k1_tarski(X1) = k2_tarski(X1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_656])])).

fof(f5904,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(k1_tarski(X2),X3)
        | ~ r2_hidden(X2,X3) )
    | ~ spl4_29
    | ~ spl4_656 ),
    inference(superposition,[],[f223,f5723])).

fof(f5723,plain,
    ( ! [X1] : k1_tarski(X1) = k2_tarski(X1,X1)
    | ~ spl4_656 ),
    inference(avatar_component_clause,[],[f5722])).

fof(f223,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X0,X2) )
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f222])).

fof(f5725,plain,
    ( spl4_656
    | ~ spl4_367
    | ~ spl4_624 ),
    inference(avatar_split_clause,[],[f5701,f5516,f2782,f5722])).

fof(f2782,plain,
    ( spl4_367
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_367])])).

fof(f5516,plain,
    ( spl4_624
  <=> ! [X7] : k1_tarski(X7) = k4_xboole_0(k2_tarski(X7,X7),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_624])])).

fof(f5701,plain,
    ( ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)
    | ~ spl4_367
    | ~ spl4_624 ),
    inference(superposition,[],[f2783,f5517])).

fof(f5517,plain,
    ( ! [X7] : k1_tarski(X7) = k4_xboole_0(k2_tarski(X7,X7),k1_xboole_0)
    | ~ spl4_624 ),
    inference(avatar_component_clause,[],[f5516])).

fof(f2783,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_367 ),
    inference(avatar_component_clause,[],[f2782])).

fof(f5587,plain,
    ( spl4_633
    | ~ spl4_383
    | ~ spl4_620 ),
    inference(avatar_split_clause,[],[f5536,f5499,f2956,f5584])).

fof(f2956,plain,
    ( spl4_383
  <=> ! [X9] : r1_xboole_0(k4_xboole_0(X9,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_383])])).

fof(f5499,plain,
    ( spl4_620
  <=> k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_620])])).

fof(f5536,plain,
    ( r1_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl4_383
    | ~ spl4_620 ),
    inference(superposition,[],[f2957,f5501])).

fof(f5501,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK0),sK2)
    | ~ spl4_620 ),
    inference(avatar_component_clause,[],[f5499])).

fof(f2957,plain,
    ( ! [X9] : r1_xboole_0(k4_xboole_0(X9,sK2),sK1)
    | ~ spl4_383 ),
    inference(avatar_component_clause,[],[f2956])).

fof(f5518,plain,
    ( spl4_624
    | ~ spl4_25
    | ~ spl4_122 ),
    inference(avatar_split_clause,[],[f5494,f837,f206,f5516])).

fof(f206,plain,
    ( spl4_25
  <=> ! [X1,X2] :
        ( k1_tarski(X1) = k4_xboole_0(k2_tarski(X1,X1),X2)
        | r2_hidden(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f837,plain,
    ( spl4_122
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_122])])).

fof(f5494,plain,
    ( ! [X7] : k1_tarski(X7) = k4_xboole_0(k2_tarski(X7,X7),k1_xboole_0)
    | ~ spl4_25
    | ~ spl4_122 ),
    inference(resolution,[],[f207,f838])).

fof(f838,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_122 ),
    inference(avatar_component_clause,[],[f837])).

fof(f207,plain,
    ( ! [X2,X1] :
        ( r2_hidden(X1,X2)
        | k1_tarski(X1) = k4_xboole_0(k2_tarski(X1,X1),X2) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f206])).

fof(f5502,plain,
    ( spl4_620
    | spl4_6
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f5490,f206,f126,f5499])).

fof(f126,plain,
    ( spl4_6
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f5490,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK0),sK2)
    | spl4_6
    | ~ spl4_25 ),
    inference(resolution,[],[f207,f128])).

fof(f128,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f2958,plain,
    ( spl4_383
    | ~ spl4_123
    | ~ spl4_372 ),
    inference(avatar_split_clause,[],[f2914,f2880,f848,f2956])).

fof(f848,plain,
    ( spl4_123
  <=> ! [X0] : r1_xboole_0(sK1,k4_xboole_0(X0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_123])])).

fof(f2880,plain,
    ( spl4_372
  <=> ! [X5,X4] :
        ( r1_xboole_0(X4,X5)
        | ~ r1_xboole_0(X5,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_372])])).

fof(f2914,plain,
    ( ! [X9] : r1_xboole_0(k4_xboole_0(X9,sK2),sK1)
    | ~ spl4_123
    | ~ spl4_372 ),
    inference(resolution,[],[f2881,f849])).

fof(f849,plain,
    ( ! [X0] : r1_xboole_0(sK1,k4_xboole_0(X0,sK2))
    | ~ spl4_123 ),
    inference(avatar_component_clause,[],[f848])).

fof(f2881,plain,
    ( ! [X4,X5] :
        ( ~ r1_xboole_0(X5,X4)
        | r1_xboole_0(X4,X5) )
    | ~ spl4_372 ),
    inference(avatar_component_clause,[],[f2880])).

fof(f2882,plain,
    ( spl4_372
    | ~ spl4_21
    | ~ spl4_367 ),
    inference(avatar_split_clause,[],[f2878,f2782,f190,f2880])).

fof(f190,plain,
    ( spl4_21
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
        | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f2878,plain,
    ( ! [X4,X5] :
        ( r1_xboole_0(X4,X5)
        | ~ r1_xboole_0(X5,X4) )
    | ~ spl4_21
    | ~ spl4_367 ),
    inference(forward_demodulation,[],[f2860,f2783])).

fof(f2860,plain,
    ( ! [X4,X5] :
        ( ~ r1_xboole_0(X5,X4)
        | r1_xboole_0(X4,k4_xboole_0(X5,k1_xboole_0)) )
    | ~ spl4_21
    | ~ spl4_367 ),
    inference(superposition,[],[f191,f2783])).

fof(f191,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
        | r1_xboole_0(X1,k4_xboole_0(X0,X2)) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f190])).

fof(f2784,plain,
    ( spl4_367
    | ~ spl4_90
    | ~ spl4_100
    | ~ spl4_362 ),
    inference(avatar_split_clause,[],[f2780,f2753,f677,f589,f2782])).

fof(f589,plain,
    ( spl4_90
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f677,plain,
    ( spl4_100
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_100])])).

fof(f2753,plain,
    ( spl4_362
  <=> ! [X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k1_xboole_0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_362])])).

fof(f2780,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_90
    | ~ spl4_100
    | ~ spl4_362 ),
    inference(forward_demodulation,[],[f2769,f590])).

fof(f590,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_90 ),
    inference(avatar_component_clause,[],[f589])).

fof(f2769,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0)
    | ~ spl4_100
    | ~ spl4_362 ),
    inference(backward_demodulation,[],[f678,f2754])).

fof(f2754,plain,
    ( ! [X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k1_xboole_0),X1)
    | ~ spl4_362 ),
    inference(avatar_component_clause,[],[f2753])).

fof(f678,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X0))
    | ~ spl4_100 ),
    inference(avatar_component_clause,[],[f677])).

fof(f2755,plain,
    ( spl4_362
    | ~ spl4_19
    | ~ spl4_321 ),
    inference(avatar_split_clause,[],[f2739,f2451,f182,f2753])).

fof(f182,plain,
    ( spl4_19
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f2451,plain,
    ( spl4_321
  <=> ! [X8] : r1_tarski(k4_xboole_0(X8,k1_xboole_0),X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_321])])).

fof(f2739,plain,
    ( ! [X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k1_xboole_0),X1)
    | ~ spl4_19
    | ~ spl4_321 ),
    inference(resolution,[],[f2452,f183])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f182])).

fof(f2452,plain,
    ( ! [X8] : r1_tarski(k4_xboole_0(X8,k1_xboole_0),X8)
    | ~ spl4_321 ),
    inference(avatar_component_clause,[],[f2451])).

fof(f2453,plain,
    ( spl4_321
    | ~ spl4_86
    | ~ spl4_273
    | ~ spl4_305 ),
    inference(avatar_split_clause,[],[f2449,f2199,f2039,f563,f2451])).

fof(f563,plain,
    ( spl4_86
  <=> ! [X2] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k1_xboole_0)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f2039,plain,
    ( spl4_273
  <=> ! [X7] : k5_xboole_0(k1_xboole_0,X7) = X7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_273])])).

fof(f2199,plain,
    ( spl4_305
  <=> ! [X3,X2] : r1_tarski(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_305])])).

fof(f2449,plain,
    ( ! [X8] : r1_tarski(k4_xboole_0(X8,k1_xboole_0),X8)
    | ~ spl4_86
    | ~ spl4_273
    | ~ spl4_305 ),
    inference(forward_demodulation,[],[f2414,f2040])).

fof(f2040,plain,
    ( ! [X7] : k5_xboole_0(k1_xboole_0,X7) = X7
    | ~ spl4_273 ),
    inference(avatar_component_clause,[],[f2039])).

fof(f2414,plain,
    ( ! [X8] : r1_tarski(k5_xboole_0(k1_xboole_0,k4_xboole_0(X8,k1_xboole_0)),X8)
    | ~ spl4_86
    | ~ spl4_305 ),
    inference(superposition,[],[f2200,f564])).

fof(f564,plain,
    ( ! [X2] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k1_xboole_0)) = X2
    | ~ spl4_86 ),
    inference(avatar_component_clause,[],[f563])).

fof(f2200,plain,
    ( ! [X2,X3] : r1_tarski(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))
    | ~ spl4_305 ),
    inference(avatar_component_clause,[],[f2199])).

fof(f2201,plain,
    ( spl4_305
    | ~ spl4_86
    | ~ spl4_220
    | ~ spl4_273 ),
    inference(avatar_split_clause,[],[f2197,f2039,f1501,f563,f2199])).

fof(f1501,plain,
    ( spl4_220
  <=> ! [X3,X2] : r1_tarski(k2_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X2,X3),k1_xboole_0))),k2_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_220])])).

fof(f2197,plain,
    ( ! [X2,X3] : r1_tarski(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))
    | ~ spl4_86
    | ~ spl4_220
    | ~ spl4_273 ),
    inference(forward_demodulation,[],[f2178,f564])).

fof(f2178,plain,
    ( ! [X2,X3] : r1_tarski(k2_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X2,X3),k1_xboole_0)),k2_xboole_0(X2,X3))
    | ~ spl4_220
    | ~ spl4_273 ),
    inference(backward_demodulation,[],[f1502,f2040])).

fof(f1502,plain,
    ( ! [X2,X3] : r1_tarski(k2_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X2,X3),k1_xboole_0))),k2_xboole_0(X2,X3))
    | ~ spl4_220 ),
    inference(avatar_component_clause,[],[f1501])).

fof(f2041,plain,
    ( spl4_273
    | ~ spl4_3
    | ~ spl4_52
    | ~ spl4_86 ),
    inference(avatar_split_clause,[],[f2037,f563,f334,f114,f2039])).

fof(f114,plain,
    ( spl4_3
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f334,plain,
    ( spl4_52
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f2037,plain,
    ( ! [X7] : k5_xboole_0(k1_xboole_0,X7) = X7
    | ~ spl4_3
    | ~ spl4_52
    | ~ spl4_86 ),
    inference(forward_demodulation,[],[f1968,f564])).

fof(f1968,plain,
    ( ! [X7] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X7,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,X7)
    | ~ spl4_3
    | ~ spl4_52 ),
    inference(superposition,[],[f115,f335])).

fof(f335,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f334])).

fof(f115,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f1503,plain,
    ( spl4_220
    | ~ spl4_24
    | ~ spl4_179 ),
    inference(avatar_split_clause,[],[f1487,f1258,f202,f1501])).

fof(f202,plain,
    ( spl4_24
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f1258,plain,
    ( spl4_179
  <=> ! [X7] : r1_tarski(k2_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(X7,k1_xboole_0))),X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_179])])).

fof(f1487,plain,
    ( ! [X2,X3] : r1_tarski(k2_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X2,X3),k1_xboole_0))),k2_xboole_0(X2,X3))
    | ~ spl4_24
    | ~ spl4_179 ),
    inference(resolution,[],[f1259,f203])).

fof(f203,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k5_xboole_0(X1,X2))
        | r1_tarski(X0,k2_xboole_0(X1,X2)) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f202])).

fof(f1259,plain,
    ( ! [X7] : r1_tarski(k2_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(X7,k1_xboole_0))),X7)
    | ~ spl4_179 ),
    inference(avatar_component_clause,[],[f1258])).

fof(f1260,plain,
    ( spl4_179
    | ~ spl4_86
    | ~ spl4_148 ),
    inference(avatar_split_clause,[],[f1223,f1016,f563,f1258])).

fof(f1016,plain,
    ( spl4_148
  <=> ! [X3,X2] : r1_tarski(k2_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)),k2_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_148])])).

fof(f1223,plain,
    ( ! [X7] : r1_tarski(k2_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(X7,k1_xboole_0))),X7)
    | ~ spl4_86
    | ~ spl4_148 ),
    inference(superposition,[],[f1017,f564])).

fof(f1017,plain,
    ( ! [X2,X3] : r1_tarski(k2_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)),k2_xboole_0(X2,X3))
    | ~ spl4_148 ),
    inference(avatar_component_clause,[],[f1016])).

fof(f1018,plain,
    ( spl4_148
    | ~ spl4_24
    | ~ spl4_142 ),
    inference(avatar_split_clause,[],[f999,f979,f202,f1016])).

fof(f979,plain,
    ( spl4_142
  <=> ! [X3] : r1_tarski(k2_xboole_0(k1_xboole_0,X3),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_142])])).

fof(f999,plain,
    ( ! [X2,X3] : r1_tarski(k2_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)),k2_xboole_0(X2,X3))
    | ~ spl4_24
    | ~ spl4_142 ),
    inference(resolution,[],[f980,f203])).

fof(f980,plain,
    ( ! [X3] : r1_tarski(k2_xboole_0(k1_xboole_0,X3),X3)
    | ~ spl4_142 ),
    inference(avatar_component_clause,[],[f979])).

fof(f981,plain,
    ( spl4_142
    | ~ spl4_52
    | ~ spl4_55 ),
    inference(avatar_split_clause,[],[f968,f352,f334,f979])).

fof(f352,plain,
    ( spl4_55
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) != k1_xboole_0
        | r1_tarski(k2_xboole_0(X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f968,plain,
    ( ! [X3] : r1_tarski(k2_xboole_0(k1_xboole_0,X3),X3)
    | ~ spl4_52
    | ~ spl4_55 ),
    inference(trivial_inequality_removal,[],[f961])).

fof(f961,plain,
    ( ! [X3] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_tarski(k2_xboole_0(k1_xboole_0,X3),X3) )
    | ~ spl4_52
    | ~ spl4_55 ),
    inference(superposition,[],[f353,f335])).

fof(f353,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != k1_xboole_0
        | r1_tarski(k2_xboole_0(X0,X1),X1) )
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f352])).

fof(f850,plain,
    ( spl4_123
    | ~ spl4_14
    | ~ spl4_109
    | ~ spl4_121 ),
    inference(avatar_split_clause,[],[f846,f828,f749,f162,f848])).

fof(f162,plain,
    ( spl4_14
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f749,plain,
    ( spl4_109
  <=> ! [X8] :
        ( ~ r1_xboole_0(X8,k1_xboole_0)
        | r1_xboole_0(sK1,k4_xboole_0(X8,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_109])])).

fof(f828,plain,
    ( spl4_121
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_121])])).

fof(f846,plain,
    ( ! [X0] : r1_xboole_0(sK1,k4_xboole_0(X0,sK2))
    | ~ spl4_14
    | ~ spl4_109
    | ~ spl4_121 ),
    inference(subsumption_resolution,[],[f841,f829])).

fof(f829,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl4_121 ),
    inference(avatar_component_clause,[],[f828])).

fof(f841,plain,
    ( ! [X0] :
        ( r1_xboole_0(sK1,k4_xboole_0(X0,sK2))
        | ~ r1_xboole_0(k2_xboole_0(X0,sK2),k1_xboole_0) )
    | ~ spl4_14
    | ~ spl4_109 ),
    inference(superposition,[],[f750,f163])).

fof(f163,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f162])).

fof(f750,plain,
    ( ! [X8] :
        ( r1_xboole_0(sK1,k4_xboole_0(X8,sK2))
        | ~ r1_xboole_0(X8,k1_xboole_0) )
    | ~ spl4_109 ),
    inference(avatar_component_clause,[],[f749])).

fof(f839,plain,
    ( spl4_122
    | ~ spl4_29
    | ~ spl4_121 ),
    inference(avatar_split_clause,[],[f831,f828,f222,f837])).

fof(f831,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_29
    | ~ spl4_121 ),
    inference(resolution,[],[f829,f223])).

fof(f830,plain,
    ( spl4_121
    | ~ spl4_21
    | ~ spl4_52
    | ~ spl4_117 ),
    inference(avatar_split_clause,[],[f826,f802,f334,f190,f828])).

fof(f802,plain,
    ( spl4_117
  <=> ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_117])])).

fof(f826,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl4_21
    | ~ spl4_52
    | ~ spl4_117 ),
    inference(forward_demodulation,[],[f825,f335])).

fof(f825,plain,
    ( ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))
    | ~ spl4_21
    | ~ spl4_117 ),
    inference(resolution,[],[f803,f191])).

fof(f803,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl4_117 ),
    inference(avatar_component_clause,[],[f802])).

fof(f805,plain,
    ( spl4_117
    | ~ spl4_47
    | ~ spl4_116 ),
    inference(avatar_split_clause,[],[f793,f789,f303,f802])).

fof(f303,plain,
    ( spl4_47
  <=> ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f789,plain,
    ( spl4_116
  <=> ! [X1,X0] : r1_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_116])])).

fof(f793,plain,
    ( ! [X2] : r1_xboole_0(k1_xboole_0,X2)
    | ~ spl4_47
    | ~ spl4_116 ),
    inference(superposition,[],[f790,f304])).

fof(f304,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f303])).

fof(f790,plain,
    ( ! [X0,X1] : r1_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1))
    | ~ spl4_116 ),
    inference(avatar_component_clause,[],[f789])).

fof(f791,plain,
    ( spl4_116
    | ~ spl4_10
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f787,f198,f146,f789])).

fof(f146,plain,
    ( spl4_10
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f198,plain,
    ( spl4_23
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f787,plain,
    ( ! [X0,X1] : r1_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1))
    | ~ spl4_10
    | ~ spl4_23 ),
    inference(resolution,[],[f199,f147])).

fof(f147,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f146])).

fof(f199,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k5_xboole_0(X1,X2))
        | r1_xboole_0(X0,k3_xboole_0(X1,X2)) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f198])).

fof(f751,plain,
    ( spl4_109
    | ~ spl4_21
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f730,f342,f190,f749])).

fof(f342,plain,
    ( spl4_54
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f730,plain,
    ( ! [X8] :
        ( ~ r1_xboole_0(X8,k1_xboole_0)
        | r1_xboole_0(sK1,k4_xboole_0(X8,sK2)) )
    | ~ spl4_21
    | ~ spl4_54 ),
    inference(superposition,[],[f191,f344])).

fof(f344,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f342])).

fof(f679,plain,
    ( spl4_100
    | ~ spl4_17
    | ~ spl4_99 ),
    inference(avatar_split_clause,[],[f672,f669,f174,f677])).

fof(f174,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f669,plain,
    ( spl4_99
  <=> ! [X1] : r1_tarski(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_99])])).

fof(f672,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X0))
    | ~ spl4_17
    | ~ spl4_99 ),
    inference(resolution,[],[f670,f175])).

fof(f175,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f174])).

fof(f670,plain,
    ( ! [X1] : r1_tarski(X1,k4_xboole_0(X1,k1_xboole_0))
    | ~ spl4_99 ),
    inference(avatar_component_clause,[],[f669])).

fof(f671,plain,
    ( spl4_99
    | ~ spl4_20
    | ~ spl4_92 ),
    inference(avatar_split_clause,[],[f662,f601,f186,f669])).

fof(f186,plain,
    ( spl4_20
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f601,plain,
    ( spl4_92
  <=> ! [X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f662,plain,
    ( ! [X1] : r1_tarski(X1,k4_xboole_0(X1,k1_xboole_0))
    | ~ spl4_20
    | ~ spl4_92 ),
    inference(trivial_inequality_removal,[],[f661])).

fof(f661,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_tarski(X1,k4_xboole_0(X1,k1_xboole_0)) )
    | ~ spl4_20
    | ~ spl4_92 ),
    inference(superposition,[],[f187,f602])).

fof(f602,plain,
    ( ! [X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))
    | ~ spl4_92 ),
    inference(avatar_component_clause,[],[f601])).

fof(f187,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != k1_xboole_0
        | r1_tarski(X0,X1) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f186])).

fof(f603,plain,
    ( spl4_92
    | ~ spl4_14
    | ~ spl4_52
    | ~ spl4_86 ),
    inference(avatar_split_clause,[],[f599,f563,f334,f162,f601])).

fof(f599,plain,
    ( ! [X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))
    | ~ spl4_14
    | ~ spl4_52
    | ~ spl4_86 ),
    inference(forward_demodulation,[],[f585,f335])).

fof(f585,plain,
    ( ! [X1] : k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))
    | ~ spl4_14
    | ~ spl4_86 ),
    inference(superposition,[],[f163,f564])).

fof(f591,plain,
    ( spl4_90
    | ~ spl4_14
    | ~ spl4_86 ),
    inference(avatar_split_clause,[],[f587,f563,f162,f589])).

fof(f587,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_14
    | ~ spl4_86 ),
    inference(forward_demodulation,[],[f581,f564])).

fof(f581,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,k1_xboole_0)
    | ~ spl4_14
    | ~ spl4_86 ),
    inference(superposition,[],[f564,f163])).

fof(f565,plain,
    ( spl4_86
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f554,f174,f146,f563])).

fof(f554,plain,
    ( ! [X2] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k1_xboole_0)) = X2
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(resolution,[],[f175,f147])).

fof(f354,plain,
    ( spl4_55
    | ~ spl4_14
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f350,f186,f162,f352])).

fof(f350,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != k1_xboole_0
        | r1_tarski(k2_xboole_0(X0,X1),X1) )
    | ~ spl4_14
    | ~ spl4_20 ),
    inference(superposition,[],[f187,f163])).

fof(f345,plain,
    ( spl4_54
    | ~ spl4_19
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f332,f317,f182,f342])).

fof(f317,plain,
    ( spl4_49
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f332,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl4_19
    | ~ spl4_49 ),
    inference(resolution,[],[f183,f319])).

fof(f319,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f317])).

fof(f336,plain,
    ( spl4_52
    | ~ spl4_10
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f330,f182,f146,f334])).

fof(f330,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl4_10
    | ~ spl4_19 ),
    inference(resolution,[],[f183,f147])).

fof(f320,plain,
    ( spl4_49
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f315,f150,f141,f131,f317])).

fof(f131,plain,
    ( spl4_7
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f141,plain,
    ( spl4_9
  <=> v1_ordinal1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f150,plain,
    ( spl4_11
  <=> ! [X1,X0] :
        ( r1_tarski(X1,X0)
        | ~ r2_hidden(X1,X0)
        | ~ v1_ordinal1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f315,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f313,f143])).

fof(f143,plain,
    ( v1_ordinal1(sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f141])).

fof(f313,plain,
    ( r1_tarski(sK1,sK2)
    | ~ v1_ordinal1(sK2)
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(resolution,[],[f151,f133])).

fof(f133,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f131])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | r1_tarski(X1,X0)
        | ~ v1_ordinal1(X0) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f150])).

fof(f305,plain,
    ( spl4_47
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f297,f158,f154,f303])).

fof(f154,plain,
    ( spl4_12
  <=> ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f158,plain,
    ( spl4_13
  <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f297,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(superposition,[],[f155,f159])).

fof(f159,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f158])).

fof(f155,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f224,plain,(
    spl4_29 ),
    inference(avatar_split_clause,[],[f70,f222])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f208,plain,(
    spl4_25 ),
    inference(avatar_split_clause,[],[f89,f206])).

fof(f89,plain,(
    ! [X2,X1] :
      ( k1_tarski(X1) = k4_xboole_0(k2_tarski(X1,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f204,plain,(
    spl4_24 ),
    inference(avatar_split_clause,[],[f63,f202])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

fof(f200,plain,(
    spl4_23 ),
    inference(avatar_split_clause,[],[f64,f198])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f192,plain,(
    spl4_21 ),
    inference(avatar_split_clause,[],[f62,f190])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f188,plain,(
    spl4_20 ),
    inference(avatar_split_clause,[],[f60,f186])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f184,plain,(
    spl4_19 ),
    inference(avatar_split_clause,[],[f61,f182])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f176,plain,(
    spl4_17 ),
    inference(avatar_split_clause,[],[f58,f174])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f164,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f54,f162])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f160,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f52,f158])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f156,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f51,f154])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f152,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f50,f150])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f148,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f48,f146])).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f144,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f44,f141])).

fof(f44,plain,(
    v1_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r2_hidden(sK1,sK2)
    & r2_hidden(sK0,sK1)
    & v1_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1)
        & v1_ordinal1(X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r2_hidden(sK1,sK2)
      & r2_hidden(sK0,sK1)
      & v1_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r2_hidden(X1,X2)
      & r2_hidden(X0,X1)
      & v1_ordinal1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r2_hidden(X1,X2)
      & r2_hidden(X0,X1)
      & v1_ordinal1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_ordinal1(X2)
       => ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X1) )
         => r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( v1_ordinal1(X2)
     => ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X1) )
       => r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_ordinal1)).

fof(f139,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f45,f136])).

fof(f45,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f134,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f46,f131])).

fof(f46,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f129,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f47,f126])).

fof(f47,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f116,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f57,f114])).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:58:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (3102)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.46  % (3127)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.46  % (3110)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.46  % (3127)Refutation not found, incomplete strategy% (3127)------------------------------
% 0.21/0.46  % (3127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (3110)Refutation not found, incomplete strategy% (3110)------------------------------
% 0.21/0.46  % (3110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (3127)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (3127)Memory used [KB]: 10746
% 0.21/0.46  % (3127)Time elapsed: 0.078 s
% 0.21/0.46  % (3127)------------------------------
% 0.21/0.46  % (3127)------------------------------
% 0.21/0.46  % (3110)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (3110)Memory used [KB]: 10618
% 0.21/0.46  % (3110)Time elapsed: 0.078 s
% 0.21/0.46  % (3110)------------------------------
% 0.21/0.46  % (3110)------------------------------
% 0.21/0.51  % (3103)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (3104)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (3107)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (3098)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (3101)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (3108)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (3105)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (3121)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (3111)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (3113)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (3120)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (3115)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (3099)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (3099)Refutation not found, incomplete strategy% (3099)------------------------------
% 0.21/0.53  % (3099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3099)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3099)Memory used [KB]: 1663
% 0.21/0.53  % (3099)Time elapsed: 0.123 s
% 0.21/0.53  % (3099)------------------------------
% 0.21/0.53  % (3099)------------------------------
% 0.21/0.54  % (3123)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (3122)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (3100)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (3114)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (3126)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (3114)Refutation not found, incomplete strategy% (3114)------------------------------
% 0.21/0.54  % (3114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3114)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3114)Memory used [KB]: 10618
% 0.21/0.54  % (3114)Time elapsed: 0.138 s
% 0.21/0.54  % (3114)------------------------------
% 0.21/0.54  % (3114)------------------------------
% 0.21/0.54  % (3119)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (3128)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (3108)Refutation not found, incomplete strategy% (3108)------------------------------
% 0.21/0.54  % (3108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3108)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3108)Memory used [KB]: 10746
% 0.21/0.54  % (3108)Time elapsed: 0.135 s
% 0.21/0.54  % (3108)------------------------------
% 0.21/0.54  % (3108)------------------------------
% 0.21/0.54  % (3112)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (3128)Refutation not found, incomplete strategy% (3128)------------------------------
% 0.21/0.54  % (3128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3128)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3128)Memory used [KB]: 1663
% 0.21/0.54  % (3128)Time elapsed: 0.002 s
% 0.21/0.54  % (3128)------------------------------
% 0.21/0.54  % (3128)------------------------------
% 0.21/0.55  % (3125)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (3106)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (3118)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (3117)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (3124)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (3109)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (3168)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 0.21/0.56  % (3169)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.04/0.66  % (3204)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.04/0.66  % (3204)Refutation not found, incomplete strategy% (3204)------------------------------
% 2.04/0.66  % (3204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.67  % (3098)Refutation not found, incomplete strategy% (3098)------------------------------
% 2.04/0.67  % (3098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.68  % (3210)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.04/0.68  % (3204)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.68  
% 2.04/0.68  % (3204)Memory used [KB]: 6140
% 2.04/0.68  % (3204)Time elapsed: 0.103 s
% 2.04/0.68  % (3204)------------------------------
% 2.04/0.68  % (3204)------------------------------
% 2.04/0.68  % (3101)Refutation not found, incomplete strategy% (3101)------------------------------
% 2.04/0.68  % (3101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.68  % (3209)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.04/0.69  % (3101)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.69  
% 2.04/0.69  % (3101)Memory used [KB]: 6140
% 2.04/0.69  % (3101)Time elapsed: 0.259 s
% 2.04/0.69  % (3101)------------------------------
% 2.04/0.69  % (3101)------------------------------
% 2.04/0.69  % (3098)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.69  
% 2.04/0.69  % (3098)Memory used [KB]: 1663
% 2.04/0.69  % (3098)Time elapsed: 0.271 s
% 2.04/0.69  % (3098)------------------------------
% 2.04/0.69  % (3098)------------------------------
% 2.64/0.70  % (3113)Refutation not found, incomplete strategy% (3113)------------------------------
% 2.64/0.70  % (3113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.64/0.71  % (3225)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.64/0.71  % (3113)Termination reason: Refutation not found, incomplete strategy
% 2.64/0.71  
% 2.64/0.71  % (3113)Memory used [KB]: 6140
% 2.64/0.71  % (3113)Time elapsed: 0.279 s
% 2.64/0.71  % (3113)------------------------------
% 2.64/0.71  % (3113)------------------------------
% 3.14/0.82  % (3290)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 3.14/0.83  % (3285)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 3.14/0.83  % (3123)Time limit reached!
% 3.14/0.83  % (3123)------------------------------
% 3.14/0.83  % (3123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.14/0.84  % (3291)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 3.14/0.84  % (3123)Termination reason: Time limit
% 3.14/0.84  
% 3.14/0.84  % (3123)Memory used [KB]: 13176
% 3.14/0.84  % (3123)Time elapsed: 0.421 s
% 3.14/0.84  % (3123)------------------------------
% 3.14/0.84  % (3123)------------------------------
% 3.14/0.84  % (3292)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 4.00/0.92  % (3104)Time limit reached!
% 4.00/0.92  % (3104)------------------------------
% 4.00/0.92  % (3104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.00/0.92  % (3104)Termination reason: Time limit
% 4.00/0.92  % (3104)Termination phase: Saturation
% 4.00/0.92  
% 4.00/0.92  % (3104)Memory used [KB]: 15863
% 4.00/0.92  % (3104)Time elapsed: 0.506 s
% 4.00/0.92  % (3104)------------------------------
% 4.00/0.92  % (3104)------------------------------
% 4.19/0.94  % (3112)Time limit reached!
% 4.19/0.94  % (3112)------------------------------
% 4.19/0.94  % (3112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.19/0.94  % (3112)Termination reason: Time limit
% 4.19/0.94  % (3112)Termination phase: Saturation
% 4.19/0.94  
% 4.19/0.94  % (3112)Memory used [KB]: 4349
% 4.19/0.94  % (3112)Time elapsed: 0.500 s
% 4.19/0.94  % (3112)------------------------------
% 4.19/0.94  % (3112)------------------------------
% 4.19/0.95  % (3100)Time limit reached!
% 4.19/0.95  % (3100)------------------------------
% 4.19/0.95  % (3100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.19/0.95  % (3100)Termination reason: Time limit
% 4.19/0.95  % (3100)Termination phase: Saturation
% 4.19/0.95  
% 4.19/0.95  % (3100)Memory used [KB]: 7419
% 4.19/0.95  % (3100)Time elapsed: 0.400 s
% 4.19/0.95  % (3100)------------------------------
% 4.19/0.95  % (3100)------------------------------
% 4.19/0.97  % (3325)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 5.08/1.07  % (3360)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 5.08/1.08  % (3368)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 5.08/1.08  % (3373)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 7.53/1.38  % (3373)Time limit reached!
% 7.53/1.38  % (3373)------------------------------
% 7.53/1.38  % (3373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.53/1.39  % (3105)Time limit reached!
% 7.53/1.39  % (3105)------------------------------
% 7.53/1.39  % (3105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.04/1.40  % (3373)Termination reason: Time limit
% 8.04/1.40  % (3373)Termination phase: Saturation
% 8.04/1.40  
% 8.04/1.40  % (3373)Memory used [KB]: 13048
% 8.04/1.40  % (3373)Time elapsed: 0.400 s
% 8.04/1.40  % (3373)------------------------------
% 8.04/1.40  % (3373)------------------------------
% 8.04/1.41  % (3105)Termination reason: Time limit
% 8.04/1.41  % (3105)Termination phase: Saturation
% 8.04/1.41  
% 8.04/1.41  % (3105)Memory used [KB]: 3709
% 8.04/1.41  % (3105)Time elapsed: 0.600 s
% 8.04/1.41  % (3105)------------------------------
% 8.04/1.41  % (3105)------------------------------
% 8.04/1.43  % (3126)Time limit reached!
% 8.04/1.43  % (3126)------------------------------
% 8.04/1.43  % (3126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.04/1.43  % (3126)Termination reason: Time limit
% 8.04/1.43  % (3126)Termination phase: Saturation
% 8.04/1.43  
% 8.04/1.43  % (3126)Memory used [KB]: 9594
% 8.04/1.43  % (3126)Time elapsed: 1.0000 s
% 8.04/1.43  % (3126)------------------------------
% 8.04/1.43  % (3126)------------------------------
% 9.01/1.53  % (3285)Time limit reached!
% 9.01/1.53  % (3285)------------------------------
% 9.01/1.53  % (3285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.16/1.53  % (3285)Termination reason: Time limit
% 9.16/1.53  
% 9.16/1.53  % (3285)Memory used [KB]: 16502
% 9.16/1.53  % (3285)Time elapsed: 0.818 s
% 9.16/1.53  % (3285)------------------------------
% 9.16/1.53  % (3285)------------------------------
% 9.16/1.54  % (3374)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 9.16/1.54  % (3292)Time limit reached!
% 9.16/1.54  % (3292)------------------------------
% 9.16/1.54  % (3292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.16/1.54  % (3292)Termination reason: Time limit
% 9.16/1.54  
% 9.16/1.54  % (3292)Memory used [KB]: 15223
% 9.16/1.54  % (3292)Time elapsed: 0.806 s
% 9.16/1.54  % (3292)------------------------------
% 9.16/1.54  % (3292)------------------------------
% 9.16/1.54  % (3375)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 9.16/1.57  % (3376)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 9.83/1.65  % (3377)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 9.83/1.67  % (3374)Refutation not found, incomplete strategy% (3374)------------------------------
% 9.83/1.67  % (3374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.83/1.69  % (3374)Termination reason: Refutation not found, incomplete strategy
% 9.83/1.69  
% 9.83/1.69  % (3374)Memory used [KB]: 6268
% 9.83/1.69  % (3374)Time elapsed: 0.247 s
% 9.83/1.69  % (3374)------------------------------
% 9.83/1.69  % (3374)------------------------------
% 9.83/1.69  % (3375)Refutation not found, incomplete strategy% (3375)------------------------------
% 9.83/1.69  % (3375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.33/1.70  % (3378)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 10.33/1.70  % (3375)Termination reason: Refutation not found, incomplete strategy
% 10.33/1.70  
% 10.33/1.70  % (3375)Memory used [KB]: 6268
% 10.33/1.70  % (3375)Time elapsed: 0.259 s
% 10.33/1.70  % (3375)------------------------------
% 10.33/1.70  % (3375)------------------------------
% 10.33/1.72  % (3103)Time limit reached!
% 10.33/1.72  % (3103)------------------------------
% 10.33/1.72  % (3103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.33/1.73  % (3103)Termination reason: Time limit
% 10.33/1.73  % (3103)Termination phase: Saturation
% 10.33/1.73  
% 10.33/1.73  % (3103)Memory used [KB]: 4861
% 10.33/1.73  % (3103)Time elapsed: 1.300 s
% 10.33/1.73  % (3103)------------------------------
% 10.33/1.73  % (3103)------------------------------
% 10.33/1.74  % (3376)Refutation found. Thanks to Tanya!
% 10.33/1.74  % SZS status Theorem for theBenchmark
% 10.33/1.74  % SZS output start Proof for theBenchmark
% 10.33/1.74  fof(f6025,plain,(
% 10.33/1.74    $false),
% 10.33/1.74    inference(avatar_sat_refutation,[],[f116,f129,f134,f139,f144,f148,f152,f156,f160,f164,f176,f184,f188,f192,f200,f204,f208,f224,f305,f320,f336,f345,f354,f565,f591,f603,f671,f679,f751,f791,f805,f830,f839,f850,f981,f1018,f1260,f1503,f2041,f2201,f2453,f2755,f2784,f2882,f2958,f5502,f5518,f5587,f5725,f5924,f6004])).
% 10.33/1.75  fof(f6004,plain,(
% 10.33/1.75    ~spl4_8 | ~spl4_633 | ~spl4_687),
% 10.33/1.75    inference(avatar_contradiction_clause,[],[f6003])).
% 10.33/1.75  fof(f6003,plain,(
% 10.33/1.75    $false | (~spl4_8 | ~spl4_633 | ~spl4_687)),
% 10.33/1.75    inference(subsumption_resolution,[],[f5979,f138])).
% 10.33/1.75  fof(f138,plain,(
% 10.33/1.75    r2_hidden(sK0,sK1) | ~spl4_8),
% 10.33/1.75    inference(avatar_component_clause,[],[f136])).
% 10.33/1.75  fof(f136,plain,(
% 10.33/1.75    spl4_8 <=> r2_hidden(sK0,sK1)),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 10.33/1.75  fof(f5979,plain,(
% 10.33/1.75    ~r2_hidden(sK0,sK1) | (~spl4_633 | ~spl4_687)),
% 10.33/1.75    inference(resolution,[],[f5923,f5586])).
% 10.33/1.75  fof(f5586,plain,(
% 10.33/1.75    r1_xboole_0(k1_tarski(sK0),sK1) | ~spl4_633),
% 10.33/1.75    inference(avatar_component_clause,[],[f5584])).
% 10.33/1.75  fof(f5584,plain,(
% 10.33/1.75    spl4_633 <=> r1_xboole_0(k1_tarski(sK0),sK1)),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_633])])).
% 10.33/1.75  fof(f5923,plain,(
% 10.33/1.75    ( ! [X2,X3] : (~r1_xboole_0(k1_tarski(X2),X3) | ~r2_hidden(X2,X3)) ) | ~spl4_687),
% 10.33/1.75    inference(avatar_component_clause,[],[f5922])).
% 10.33/1.75  fof(f5922,plain,(
% 10.33/1.75    spl4_687 <=> ! [X3,X2] : (~r1_xboole_0(k1_tarski(X2),X3) | ~r2_hidden(X2,X3))),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_687])])).
% 10.33/1.75  fof(f5924,plain,(
% 10.33/1.75    spl4_687 | ~spl4_29 | ~spl4_656),
% 10.33/1.75    inference(avatar_split_clause,[],[f5904,f5722,f222,f5922])).
% 10.33/1.75  fof(f222,plain,(
% 10.33/1.75    spl4_29 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 10.33/1.75  fof(f5722,plain,(
% 10.33/1.75    spl4_656 <=> ! [X1] : k1_tarski(X1) = k2_tarski(X1,X1)),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_656])])).
% 10.33/1.75  fof(f5904,plain,(
% 10.33/1.75    ( ! [X2,X3] : (~r1_xboole_0(k1_tarski(X2),X3) | ~r2_hidden(X2,X3)) ) | (~spl4_29 | ~spl4_656)),
% 10.33/1.75    inference(superposition,[],[f223,f5723])).
% 10.33/1.75  fof(f5723,plain,(
% 10.33/1.75    ( ! [X1] : (k1_tarski(X1) = k2_tarski(X1,X1)) ) | ~spl4_656),
% 10.33/1.75    inference(avatar_component_clause,[],[f5722])).
% 10.33/1.75  fof(f223,plain,(
% 10.33/1.75    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) ) | ~spl4_29),
% 10.33/1.75    inference(avatar_component_clause,[],[f222])).
% 10.33/1.75  fof(f5725,plain,(
% 10.33/1.75    spl4_656 | ~spl4_367 | ~spl4_624),
% 10.33/1.75    inference(avatar_split_clause,[],[f5701,f5516,f2782,f5722])).
% 10.33/1.75  fof(f2782,plain,(
% 10.33/1.75    spl4_367 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_367])])).
% 10.33/1.75  fof(f5516,plain,(
% 10.33/1.75    spl4_624 <=> ! [X7] : k1_tarski(X7) = k4_xboole_0(k2_tarski(X7,X7),k1_xboole_0)),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_624])])).
% 10.33/1.75  fof(f5701,plain,(
% 10.33/1.75    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) ) | (~spl4_367 | ~spl4_624)),
% 10.33/1.75    inference(superposition,[],[f2783,f5517])).
% 10.33/1.75  fof(f5517,plain,(
% 10.33/1.75    ( ! [X7] : (k1_tarski(X7) = k4_xboole_0(k2_tarski(X7,X7),k1_xboole_0)) ) | ~spl4_624),
% 10.33/1.75    inference(avatar_component_clause,[],[f5516])).
% 10.33/1.75  fof(f2783,plain,(
% 10.33/1.75    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl4_367),
% 10.33/1.75    inference(avatar_component_clause,[],[f2782])).
% 10.33/1.75  fof(f5587,plain,(
% 10.33/1.75    spl4_633 | ~spl4_383 | ~spl4_620),
% 10.33/1.75    inference(avatar_split_clause,[],[f5536,f5499,f2956,f5584])).
% 10.33/1.75  fof(f2956,plain,(
% 10.33/1.75    spl4_383 <=> ! [X9] : r1_xboole_0(k4_xboole_0(X9,sK2),sK1)),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_383])])).
% 10.33/1.75  fof(f5499,plain,(
% 10.33/1.75    spl4_620 <=> k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK0),sK2)),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_620])])).
% 10.33/1.75  fof(f5536,plain,(
% 10.33/1.75    r1_xboole_0(k1_tarski(sK0),sK1) | (~spl4_383 | ~spl4_620)),
% 10.33/1.75    inference(superposition,[],[f2957,f5501])).
% 10.33/1.75  fof(f5501,plain,(
% 10.33/1.75    k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK0),sK2) | ~spl4_620),
% 10.33/1.75    inference(avatar_component_clause,[],[f5499])).
% 10.33/1.75  fof(f2957,plain,(
% 10.33/1.75    ( ! [X9] : (r1_xboole_0(k4_xboole_0(X9,sK2),sK1)) ) | ~spl4_383),
% 10.33/1.75    inference(avatar_component_clause,[],[f2956])).
% 10.33/1.75  fof(f5518,plain,(
% 10.33/1.75    spl4_624 | ~spl4_25 | ~spl4_122),
% 10.33/1.75    inference(avatar_split_clause,[],[f5494,f837,f206,f5516])).
% 10.33/1.75  fof(f206,plain,(
% 10.33/1.75    spl4_25 <=> ! [X1,X2] : (k1_tarski(X1) = k4_xboole_0(k2_tarski(X1,X1),X2) | r2_hidden(X1,X2))),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 10.33/1.75  fof(f837,plain,(
% 10.33/1.75    spl4_122 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_122])])).
% 10.33/1.75  fof(f5494,plain,(
% 10.33/1.75    ( ! [X7] : (k1_tarski(X7) = k4_xboole_0(k2_tarski(X7,X7),k1_xboole_0)) ) | (~spl4_25 | ~spl4_122)),
% 10.33/1.75    inference(resolution,[],[f207,f838])).
% 10.33/1.75  fof(f838,plain,(
% 10.33/1.75    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl4_122),
% 10.33/1.75    inference(avatar_component_clause,[],[f837])).
% 10.33/1.75  fof(f207,plain,(
% 10.33/1.75    ( ! [X2,X1] : (r2_hidden(X1,X2) | k1_tarski(X1) = k4_xboole_0(k2_tarski(X1,X1),X2)) ) | ~spl4_25),
% 10.33/1.75    inference(avatar_component_clause,[],[f206])).
% 10.33/1.75  fof(f5502,plain,(
% 10.33/1.75    spl4_620 | spl4_6 | ~spl4_25),
% 10.33/1.75    inference(avatar_split_clause,[],[f5490,f206,f126,f5499])).
% 10.33/1.75  fof(f126,plain,(
% 10.33/1.75    spl4_6 <=> r2_hidden(sK0,sK2)),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 10.33/1.75  fof(f5490,plain,(
% 10.33/1.75    k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK0),sK2) | (spl4_6 | ~spl4_25)),
% 10.33/1.75    inference(resolution,[],[f207,f128])).
% 10.33/1.75  fof(f128,plain,(
% 10.33/1.75    ~r2_hidden(sK0,sK2) | spl4_6),
% 10.33/1.75    inference(avatar_component_clause,[],[f126])).
% 10.33/1.75  fof(f2958,plain,(
% 10.33/1.75    spl4_383 | ~spl4_123 | ~spl4_372),
% 10.33/1.75    inference(avatar_split_clause,[],[f2914,f2880,f848,f2956])).
% 10.33/1.75  fof(f848,plain,(
% 10.33/1.75    spl4_123 <=> ! [X0] : r1_xboole_0(sK1,k4_xboole_0(X0,sK2))),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_123])])).
% 10.33/1.75  fof(f2880,plain,(
% 10.33/1.75    spl4_372 <=> ! [X5,X4] : (r1_xboole_0(X4,X5) | ~r1_xboole_0(X5,X4))),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_372])])).
% 10.33/1.75  fof(f2914,plain,(
% 10.33/1.75    ( ! [X9] : (r1_xboole_0(k4_xboole_0(X9,sK2),sK1)) ) | (~spl4_123 | ~spl4_372)),
% 10.33/1.75    inference(resolution,[],[f2881,f849])).
% 10.33/1.75  fof(f849,plain,(
% 10.33/1.75    ( ! [X0] : (r1_xboole_0(sK1,k4_xboole_0(X0,sK2))) ) | ~spl4_123),
% 10.33/1.75    inference(avatar_component_clause,[],[f848])).
% 10.33/1.75  fof(f2881,plain,(
% 10.33/1.75    ( ! [X4,X5] : (~r1_xboole_0(X5,X4) | r1_xboole_0(X4,X5)) ) | ~spl4_372),
% 10.33/1.75    inference(avatar_component_clause,[],[f2880])).
% 10.33/1.75  fof(f2882,plain,(
% 10.33/1.75    spl4_372 | ~spl4_21 | ~spl4_367),
% 10.33/1.75    inference(avatar_split_clause,[],[f2878,f2782,f190,f2880])).
% 10.33/1.75  fof(f190,plain,(
% 10.33/1.75    spl4_21 <=> ! [X1,X0,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 10.33/1.75  fof(f2878,plain,(
% 10.33/1.75    ( ! [X4,X5] : (r1_xboole_0(X4,X5) | ~r1_xboole_0(X5,X4)) ) | (~spl4_21 | ~spl4_367)),
% 10.33/1.75    inference(forward_demodulation,[],[f2860,f2783])).
% 10.33/1.75  fof(f2860,plain,(
% 10.33/1.75    ( ! [X4,X5] : (~r1_xboole_0(X5,X4) | r1_xboole_0(X4,k4_xboole_0(X5,k1_xboole_0))) ) | (~spl4_21 | ~spl4_367)),
% 10.33/1.75    inference(superposition,[],[f191,f2783])).
% 10.33/1.75  fof(f191,plain,(
% 10.33/1.75    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X1,k4_xboole_0(X0,X2))) ) | ~spl4_21),
% 10.33/1.75    inference(avatar_component_clause,[],[f190])).
% 10.33/1.75  fof(f2784,plain,(
% 10.33/1.75    spl4_367 | ~spl4_90 | ~spl4_100 | ~spl4_362),
% 10.33/1.75    inference(avatar_split_clause,[],[f2780,f2753,f677,f589,f2782])).
% 10.33/1.75  fof(f589,plain,(
% 10.33/1.75    spl4_90 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).
% 10.33/1.75  fof(f677,plain,(
% 10.33/1.75    spl4_100 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X0))),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_100])])).
% 10.33/1.75  fof(f2753,plain,(
% 10.33/1.75    spl4_362 <=> ! [X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k1_xboole_0),X1)),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_362])])).
% 10.33/1.75  fof(f2780,plain,(
% 10.33/1.75    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl4_90 | ~spl4_100 | ~spl4_362)),
% 10.33/1.75    inference(forward_demodulation,[],[f2769,f590])).
% 10.33/1.75  fof(f590,plain,(
% 10.33/1.75    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl4_90),
% 10.33/1.75    inference(avatar_component_clause,[],[f589])).
% 10.33/1.75  fof(f2769,plain,(
% 10.33/1.75    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0)) ) | (~spl4_100 | ~spl4_362)),
% 10.33/1.75    inference(backward_demodulation,[],[f678,f2754])).
% 10.33/1.75  fof(f2754,plain,(
% 10.33/1.75    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k1_xboole_0),X1)) ) | ~spl4_362),
% 10.33/1.75    inference(avatar_component_clause,[],[f2753])).
% 10.33/1.75  fof(f678,plain,(
% 10.33/1.75    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X0))) ) | ~spl4_100),
% 10.33/1.75    inference(avatar_component_clause,[],[f677])).
% 10.33/1.75  fof(f2755,plain,(
% 10.33/1.75    spl4_362 | ~spl4_19 | ~spl4_321),
% 10.33/1.75    inference(avatar_split_clause,[],[f2739,f2451,f182,f2753])).
% 10.33/1.75  fof(f182,plain,(
% 10.33/1.75    spl4_19 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 10.33/1.75  fof(f2451,plain,(
% 10.33/1.75    spl4_321 <=> ! [X8] : r1_tarski(k4_xboole_0(X8,k1_xboole_0),X8)),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_321])])).
% 10.33/1.75  fof(f2739,plain,(
% 10.33/1.75    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k1_xboole_0),X1)) ) | (~spl4_19 | ~spl4_321)),
% 10.33/1.75    inference(resolution,[],[f2452,f183])).
% 10.33/1.75  fof(f183,plain,(
% 10.33/1.75    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl4_19),
% 10.33/1.75    inference(avatar_component_clause,[],[f182])).
% 10.33/1.75  fof(f2452,plain,(
% 10.33/1.75    ( ! [X8] : (r1_tarski(k4_xboole_0(X8,k1_xboole_0),X8)) ) | ~spl4_321),
% 10.33/1.75    inference(avatar_component_clause,[],[f2451])).
% 10.33/1.75  fof(f2453,plain,(
% 10.33/1.75    spl4_321 | ~spl4_86 | ~spl4_273 | ~spl4_305),
% 10.33/1.75    inference(avatar_split_clause,[],[f2449,f2199,f2039,f563,f2451])).
% 10.33/1.75  fof(f563,plain,(
% 10.33/1.75    spl4_86 <=> ! [X2] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k1_xboole_0)) = X2),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).
% 10.33/1.75  fof(f2039,plain,(
% 10.33/1.75    spl4_273 <=> ! [X7] : k5_xboole_0(k1_xboole_0,X7) = X7),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_273])])).
% 10.33/1.75  fof(f2199,plain,(
% 10.33/1.75    spl4_305 <=> ! [X3,X2] : r1_tarski(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_305])])).
% 10.33/1.75  fof(f2449,plain,(
% 10.33/1.75    ( ! [X8] : (r1_tarski(k4_xboole_0(X8,k1_xboole_0),X8)) ) | (~spl4_86 | ~spl4_273 | ~spl4_305)),
% 10.33/1.75    inference(forward_demodulation,[],[f2414,f2040])).
% 10.33/1.75  fof(f2040,plain,(
% 10.33/1.75    ( ! [X7] : (k5_xboole_0(k1_xboole_0,X7) = X7) ) | ~spl4_273),
% 10.33/1.75    inference(avatar_component_clause,[],[f2039])).
% 10.33/1.75  fof(f2414,plain,(
% 10.33/1.75    ( ! [X8] : (r1_tarski(k5_xboole_0(k1_xboole_0,k4_xboole_0(X8,k1_xboole_0)),X8)) ) | (~spl4_86 | ~spl4_305)),
% 10.33/1.75    inference(superposition,[],[f2200,f564])).
% 10.33/1.75  fof(f564,plain,(
% 10.33/1.75    ( ! [X2] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k1_xboole_0)) = X2) ) | ~spl4_86),
% 10.33/1.75    inference(avatar_component_clause,[],[f563])).
% 10.33/1.75  fof(f2200,plain,(
% 10.33/1.75    ( ! [X2,X3] : (r1_tarski(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))) ) | ~spl4_305),
% 10.33/1.75    inference(avatar_component_clause,[],[f2199])).
% 10.33/1.75  fof(f2201,plain,(
% 10.33/1.75    spl4_305 | ~spl4_86 | ~spl4_220 | ~spl4_273),
% 10.33/1.75    inference(avatar_split_clause,[],[f2197,f2039,f1501,f563,f2199])).
% 10.33/1.75  fof(f1501,plain,(
% 10.33/1.75    spl4_220 <=> ! [X3,X2] : r1_tarski(k2_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X2,X3),k1_xboole_0))),k2_xboole_0(X2,X3))),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_220])])).
% 10.33/1.75  fof(f2197,plain,(
% 10.33/1.75    ( ! [X2,X3] : (r1_tarski(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))) ) | (~spl4_86 | ~spl4_220 | ~spl4_273)),
% 10.33/1.75    inference(forward_demodulation,[],[f2178,f564])).
% 10.33/1.75  fof(f2178,plain,(
% 10.33/1.75    ( ! [X2,X3] : (r1_tarski(k2_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X2,X3),k1_xboole_0)),k2_xboole_0(X2,X3))) ) | (~spl4_220 | ~spl4_273)),
% 10.33/1.75    inference(backward_demodulation,[],[f1502,f2040])).
% 10.33/1.75  fof(f1502,plain,(
% 10.33/1.75    ( ! [X2,X3] : (r1_tarski(k2_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X2,X3),k1_xboole_0))),k2_xboole_0(X2,X3))) ) | ~spl4_220),
% 10.33/1.75    inference(avatar_component_clause,[],[f1501])).
% 10.33/1.75  fof(f2041,plain,(
% 10.33/1.75    spl4_273 | ~spl4_3 | ~spl4_52 | ~spl4_86),
% 10.33/1.75    inference(avatar_split_clause,[],[f2037,f563,f334,f114,f2039])).
% 10.33/1.75  fof(f114,plain,(
% 10.33/1.75    spl4_3 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 10.33/1.75  fof(f334,plain,(
% 10.33/1.75    spl4_52 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 10.33/1.75  fof(f2037,plain,(
% 10.33/1.75    ( ! [X7] : (k5_xboole_0(k1_xboole_0,X7) = X7) ) | (~spl4_3 | ~spl4_52 | ~spl4_86)),
% 10.33/1.75    inference(forward_demodulation,[],[f1968,f564])).
% 10.33/1.75  fof(f1968,plain,(
% 10.33/1.75    ( ! [X7] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X7,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,X7)) ) | (~spl4_3 | ~spl4_52)),
% 10.33/1.75    inference(superposition,[],[f115,f335])).
% 10.33/1.75  fof(f335,plain,(
% 10.33/1.75    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl4_52),
% 10.33/1.75    inference(avatar_component_clause,[],[f334])).
% 10.33/1.75  fof(f115,plain,(
% 10.33/1.75    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ) | ~spl4_3),
% 10.33/1.75    inference(avatar_component_clause,[],[f114])).
% 10.33/1.75  fof(f1503,plain,(
% 10.33/1.75    spl4_220 | ~spl4_24 | ~spl4_179),
% 10.33/1.75    inference(avatar_split_clause,[],[f1487,f1258,f202,f1501])).
% 10.33/1.75  fof(f202,plain,(
% 10.33/1.75    spl4_24 <=> ! [X1,X0,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2)))),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 10.33/1.75  fof(f1258,plain,(
% 10.33/1.75    spl4_179 <=> ! [X7] : r1_tarski(k2_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(X7,k1_xboole_0))),X7)),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_179])])).
% 10.33/1.75  fof(f1487,plain,(
% 10.33/1.75    ( ! [X2,X3] : (r1_tarski(k2_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X2,X3),k1_xboole_0))),k2_xboole_0(X2,X3))) ) | (~spl4_24 | ~spl4_179)),
% 10.33/1.75    inference(resolution,[],[f1259,f203])).
% 10.33/1.75  fof(f203,plain,(
% 10.33/1.75    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,X2)) | r1_tarski(X0,k2_xboole_0(X1,X2))) ) | ~spl4_24),
% 10.33/1.75    inference(avatar_component_clause,[],[f202])).
% 10.33/1.75  fof(f1259,plain,(
% 10.33/1.75    ( ! [X7] : (r1_tarski(k2_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(X7,k1_xboole_0))),X7)) ) | ~spl4_179),
% 10.33/1.75    inference(avatar_component_clause,[],[f1258])).
% 10.33/1.75  fof(f1260,plain,(
% 10.33/1.75    spl4_179 | ~spl4_86 | ~spl4_148),
% 10.33/1.75    inference(avatar_split_clause,[],[f1223,f1016,f563,f1258])).
% 10.33/1.75  fof(f1016,plain,(
% 10.33/1.75    spl4_148 <=> ! [X3,X2] : r1_tarski(k2_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)),k2_xboole_0(X2,X3))),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_148])])).
% 10.33/1.75  fof(f1223,plain,(
% 10.33/1.75    ( ! [X7] : (r1_tarski(k2_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(X7,k1_xboole_0))),X7)) ) | (~spl4_86 | ~spl4_148)),
% 10.33/1.75    inference(superposition,[],[f1017,f564])).
% 10.33/1.75  fof(f1017,plain,(
% 10.33/1.75    ( ! [X2,X3] : (r1_tarski(k2_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)),k2_xboole_0(X2,X3))) ) | ~spl4_148),
% 10.33/1.75    inference(avatar_component_clause,[],[f1016])).
% 10.33/1.75  fof(f1018,plain,(
% 10.33/1.75    spl4_148 | ~spl4_24 | ~spl4_142),
% 10.33/1.75    inference(avatar_split_clause,[],[f999,f979,f202,f1016])).
% 10.33/1.75  fof(f979,plain,(
% 10.33/1.75    spl4_142 <=> ! [X3] : r1_tarski(k2_xboole_0(k1_xboole_0,X3),X3)),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_142])])).
% 10.33/1.75  fof(f999,plain,(
% 10.33/1.75    ( ! [X2,X3] : (r1_tarski(k2_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)),k2_xboole_0(X2,X3))) ) | (~spl4_24 | ~spl4_142)),
% 10.33/1.75    inference(resolution,[],[f980,f203])).
% 10.33/1.75  fof(f980,plain,(
% 10.33/1.75    ( ! [X3] : (r1_tarski(k2_xboole_0(k1_xboole_0,X3),X3)) ) | ~spl4_142),
% 10.33/1.75    inference(avatar_component_clause,[],[f979])).
% 10.33/1.75  fof(f981,plain,(
% 10.33/1.75    spl4_142 | ~spl4_52 | ~spl4_55),
% 10.33/1.75    inference(avatar_split_clause,[],[f968,f352,f334,f979])).
% 10.33/1.75  fof(f352,plain,(
% 10.33/1.75    spl4_55 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(k2_xboole_0(X0,X1),X1))),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 10.33/1.75  fof(f968,plain,(
% 10.33/1.75    ( ! [X3] : (r1_tarski(k2_xboole_0(k1_xboole_0,X3),X3)) ) | (~spl4_52 | ~spl4_55)),
% 10.33/1.75    inference(trivial_inequality_removal,[],[f961])).
% 10.33/1.75  fof(f961,plain,(
% 10.33/1.75    ( ! [X3] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k2_xboole_0(k1_xboole_0,X3),X3)) ) | (~spl4_52 | ~spl4_55)),
% 10.33/1.75    inference(superposition,[],[f353,f335])).
% 10.33/1.75  fof(f353,plain,(
% 10.33/1.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(k2_xboole_0(X0,X1),X1)) ) | ~spl4_55),
% 10.33/1.75    inference(avatar_component_clause,[],[f352])).
% 10.33/1.75  fof(f850,plain,(
% 10.33/1.75    spl4_123 | ~spl4_14 | ~spl4_109 | ~spl4_121),
% 10.33/1.75    inference(avatar_split_clause,[],[f846,f828,f749,f162,f848])).
% 10.33/1.75  fof(f162,plain,(
% 10.33/1.75    spl4_14 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 10.33/1.75  fof(f749,plain,(
% 10.33/1.75    spl4_109 <=> ! [X8] : (~r1_xboole_0(X8,k1_xboole_0) | r1_xboole_0(sK1,k4_xboole_0(X8,sK2)))),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_109])])).
% 10.33/1.75  fof(f828,plain,(
% 10.33/1.75    spl4_121 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_121])])).
% 10.33/1.75  fof(f846,plain,(
% 10.33/1.75    ( ! [X0] : (r1_xboole_0(sK1,k4_xboole_0(X0,sK2))) ) | (~spl4_14 | ~spl4_109 | ~spl4_121)),
% 10.33/1.75    inference(subsumption_resolution,[],[f841,f829])).
% 10.33/1.75  fof(f829,plain,(
% 10.33/1.75    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl4_121),
% 10.33/1.75    inference(avatar_component_clause,[],[f828])).
% 10.33/1.75  fof(f841,plain,(
% 10.33/1.75    ( ! [X0] : (r1_xboole_0(sK1,k4_xboole_0(X0,sK2)) | ~r1_xboole_0(k2_xboole_0(X0,sK2),k1_xboole_0)) ) | (~spl4_14 | ~spl4_109)),
% 10.33/1.75    inference(superposition,[],[f750,f163])).
% 10.33/1.75  fof(f163,plain,(
% 10.33/1.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) ) | ~spl4_14),
% 10.33/1.75    inference(avatar_component_clause,[],[f162])).
% 10.33/1.75  fof(f750,plain,(
% 10.33/1.75    ( ! [X8] : (r1_xboole_0(sK1,k4_xboole_0(X8,sK2)) | ~r1_xboole_0(X8,k1_xboole_0)) ) | ~spl4_109),
% 10.33/1.75    inference(avatar_component_clause,[],[f749])).
% 10.33/1.75  fof(f839,plain,(
% 10.33/1.75    spl4_122 | ~spl4_29 | ~spl4_121),
% 10.33/1.75    inference(avatar_split_clause,[],[f831,f828,f222,f837])).
% 10.33/1.75  fof(f831,plain,(
% 10.33/1.75    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl4_29 | ~spl4_121)),
% 10.33/1.75    inference(resolution,[],[f829,f223])).
% 10.33/1.75  fof(f830,plain,(
% 10.33/1.75    spl4_121 | ~spl4_21 | ~spl4_52 | ~spl4_117),
% 10.33/1.75    inference(avatar_split_clause,[],[f826,f802,f334,f190,f828])).
% 10.33/1.75  fof(f802,plain,(
% 10.33/1.75    spl4_117 <=> ! [X0] : r1_xboole_0(k1_xboole_0,X0)),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_117])])).
% 10.33/1.75  fof(f826,plain,(
% 10.33/1.75    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | (~spl4_21 | ~spl4_52 | ~spl4_117)),
% 10.33/1.75    inference(forward_demodulation,[],[f825,f335])).
% 10.33/1.75  fof(f825,plain,(
% 10.33/1.75    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) ) | (~spl4_21 | ~spl4_117)),
% 10.33/1.75    inference(resolution,[],[f803,f191])).
% 10.33/1.75  fof(f803,plain,(
% 10.33/1.75    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | ~spl4_117),
% 10.33/1.75    inference(avatar_component_clause,[],[f802])).
% 10.33/1.75  fof(f805,plain,(
% 10.33/1.75    spl4_117 | ~spl4_47 | ~spl4_116),
% 10.33/1.75    inference(avatar_split_clause,[],[f793,f789,f303,f802])).
% 10.33/1.75  fof(f303,plain,(
% 10.33/1.75    spl4_47 <=> ! [X0] : k3_xboole_0(X0,X0) = X0),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 10.33/1.75  fof(f789,plain,(
% 10.33/1.75    spl4_116 <=> ! [X1,X0] : r1_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1))),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_116])])).
% 10.33/1.75  fof(f793,plain,(
% 10.33/1.75    ( ! [X2] : (r1_xboole_0(k1_xboole_0,X2)) ) | (~spl4_47 | ~spl4_116)),
% 10.33/1.75    inference(superposition,[],[f790,f304])).
% 10.33/1.75  fof(f304,plain,(
% 10.33/1.75    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | ~spl4_47),
% 10.33/1.75    inference(avatar_component_clause,[],[f303])).
% 10.33/1.75  fof(f790,plain,(
% 10.33/1.75    ( ! [X0,X1] : (r1_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1))) ) | ~spl4_116),
% 10.33/1.75    inference(avatar_component_clause,[],[f789])).
% 10.33/1.75  fof(f791,plain,(
% 10.33/1.75    spl4_116 | ~spl4_10 | ~spl4_23),
% 10.33/1.75    inference(avatar_split_clause,[],[f787,f198,f146,f789])).
% 10.33/1.75  fof(f146,plain,(
% 10.33/1.75    spl4_10 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 10.33/1.75  fof(f198,plain,(
% 10.33/1.75    spl4_23 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2)))),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 10.33/1.75  fof(f787,plain,(
% 10.33/1.75    ( ! [X0,X1] : (r1_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1))) ) | (~spl4_10 | ~spl4_23)),
% 10.33/1.75    inference(resolution,[],[f199,f147])).
% 10.33/1.75  fof(f147,plain,(
% 10.33/1.75    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_10),
% 10.33/1.75    inference(avatar_component_clause,[],[f146])).
% 10.33/1.75  fof(f199,plain,(
% 10.33/1.75    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,X2)) | r1_xboole_0(X0,k3_xboole_0(X1,X2))) ) | ~spl4_23),
% 10.33/1.75    inference(avatar_component_clause,[],[f198])).
% 10.33/1.75  fof(f751,plain,(
% 10.33/1.75    spl4_109 | ~spl4_21 | ~spl4_54),
% 10.33/1.75    inference(avatar_split_clause,[],[f730,f342,f190,f749])).
% 10.33/1.75  fof(f342,plain,(
% 10.33/1.75    spl4_54 <=> k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 10.33/1.75  fof(f730,plain,(
% 10.33/1.75    ( ! [X8] : (~r1_xboole_0(X8,k1_xboole_0) | r1_xboole_0(sK1,k4_xboole_0(X8,sK2))) ) | (~spl4_21 | ~spl4_54)),
% 10.33/1.75    inference(superposition,[],[f191,f344])).
% 10.33/1.75  fof(f344,plain,(
% 10.33/1.75    k1_xboole_0 = k4_xboole_0(sK1,sK2) | ~spl4_54),
% 10.33/1.75    inference(avatar_component_clause,[],[f342])).
% 10.33/1.75  fof(f679,plain,(
% 10.33/1.75    spl4_100 | ~spl4_17 | ~spl4_99),
% 10.33/1.75    inference(avatar_split_clause,[],[f672,f669,f174,f677])).
% 10.33/1.75  fof(f174,plain,(
% 10.33/1.75    spl4_17 <=> ! [X1,X0] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 10.33/1.75  fof(f669,plain,(
% 10.33/1.75    spl4_99 <=> ! [X1] : r1_tarski(X1,k4_xboole_0(X1,k1_xboole_0))),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_99])])).
% 10.33/1.75  fof(f672,plain,(
% 10.33/1.75    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X0))) ) | (~spl4_17 | ~spl4_99)),
% 10.33/1.75    inference(resolution,[],[f670,f175])).
% 10.33/1.75  fof(f175,plain,(
% 10.33/1.75    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) ) | ~spl4_17),
% 10.33/1.75    inference(avatar_component_clause,[],[f174])).
% 10.33/1.75  fof(f670,plain,(
% 10.33/1.75    ( ! [X1] : (r1_tarski(X1,k4_xboole_0(X1,k1_xboole_0))) ) | ~spl4_99),
% 10.33/1.75    inference(avatar_component_clause,[],[f669])).
% 10.33/1.75  fof(f671,plain,(
% 10.33/1.75    spl4_99 | ~spl4_20 | ~spl4_92),
% 10.33/1.75    inference(avatar_split_clause,[],[f662,f601,f186,f669])).
% 10.33/1.75  fof(f186,plain,(
% 10.33/1.75    spl4_20 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 10.33/1.75  fof(f601,plain,(
% 10.33/1.75    spl4_92 <=> ! [X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).
% 10.33/1.75  fof(f662,plain,(
% 10.33/1.75    ( ! [X1] : (r1_tarski(X1,k4_xboole_0(X1,k1_xboole_0))) ) | (~spl4_20 | ~spl4_92)),
% 10.33/1.75    inference(trivial_inequality_removal,[],[f661])).
% 10.33/1.75  fof(f661,plain,(
% 10.33/1.75    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X1,k4_xboole_0(X1,k1_xboole_0))) ) | (~spl4_20 | ~spl4_92)),
% 10.33/1.75    inference(superposition,[],[f187,f602])).
% 10.33/1.75  fof(f602,plain,(
% 10.33/1.75    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) ) | ~spl4_92),
% 10.33/1.75    inference(avatar_component_clause,[],[f601])).
% 10.33/1.75  fof(f187,plain,(
% 10.33/1.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) ) | ~spl4_20),
% 10.33/1.75    inference(avatar_component_clause,[],[f186])).
% 10.33/1.75  fof(f603,plain,(
% 10.33/1.75    spl4_92 | ~spl4_14 | ~spl4_52 | ~spl4_86),
% 10.33/1.75    inference(avatar_split_clause,[],[f599,f563,f334,f162,f601])).
% 10.33/1.75  fof(f599,plain,(
% 10.33/1.75    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) ) | (~spl4_14 | ~spl4_52 | ~spl4_86)),
% 10.33/1.75    inference(forward_demodulation,[],[f585,f335])).
% 10.33/1.75  fof(f585,plain,(
% 10.33/1.75    ( ! [X1] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) ) | (~spl4_14 | ~spl4_86)),
% 10.33/1.75    inference(superposition,[],[f163,f564])).
% 10.33/1.75  fof(f591,plain,(
% 10.33/1.75    spl4_90 | ~spl4_14 | ~spl4_86),
% 10.33/1.75    inference(avatar_split_clause,[],[f587,f563,f162,f589])).
% 10.33/1.75  fof(f587,plain,(
% 10.33/1.75    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl4_14 | ~spl4_86)),
% 10.33/1.75    inference(forward_demodulation,[],[f581,f564])).
% 10.33/1.75  fof(f581,plain,(
% 10.33/1.75    ( ! [X0] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,k1_xboole_0)) ) | (~spl4_14 | ~spl4_86)),
% 10.33/1.75    inference(superposition,[],[f564,f163])).
% 10.33/1.75  fof(f565,plain,(
% 10.33/1.75    spl4_86 | ~spl4_10 | ~spl4_17),
% 10.33/1.75    inference(avatar_split_clause,[],[f554,f174,f146,f563])).
% 10.33/1.75  fof(f554,plain,(
% 10.33/1.75    ( ! [X2] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k1_xboole_0)) = X2) ) | (~spl4_10 | ~spl4_17)),
% 10.33/1.75    inference(resolution,[],[f175,f147])).
% 10.33/1.75  fof(f354,plain,(
% 10.33/1.75    spl4_55 | ~spl4_14 | ~spl4_20),
% 10.33/1.75    inference(avatar_split_clause,[],[f350,f186,f162,f352])).
% 10.33/1.75  fof(f350,plain,(
% 10.33/1.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(k2_xboole_0(X0,X1),X1)) ) | (~spl4_14 | ~spl4_20)),
% 10.33/1.75    inference(superposition,[],[f187,f163])).
% 10.33/1.75  fof(f345,plain,(
% 10.33/1.75    spl4_54 | ~spl4_19 | ~spl4_49),
% 10.33/1.75    inference(avatar_split_clause,[],[f332,f317,f182,f342])).
% 10.33/1.75  fof(f317,plain,(
% 10.33/1.75    spl4_49 <=> r1_tarski(sK1,sK2)),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 10.33/1.75  fof(f332,plain,(
% 10.33/1.75    k1_xboole_0 = k4_xboole_0(sK1,sK2) | (~spl4_19 | ~spl4_49)),
% 10.33/1.75    inference(resolution,[],[f183,f319])).
% 10.33/1.75  fof(f319,plain,(
% 10.33/1.75    r1_tarski(sK1,sK2) | ~spl4_49),
% 10.33/1.75    inference(avatar_component_clause,[],[f317])).
% 10.33/1.75  fof(f336,plain,(
% 10.33/1.75    spl4_52 | ~spl4_10 | ~spl4_19),
% 10.33/1.75    inference(avatar_split_clause,[],[f330,f182,f146,f334])).
% 10.33/1.75  fof(f330,plain,(
% 10.33/1.75    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | (~spl4_10 | ~spl4_19)),
% 10.33/1.75    inference(resolution,[],[f183,f147])).
% 10.33/1.75  fof(f320,plain,(
% 10.33/1.75    spl4_49 | ~spl4_7 | ~spl4_9 | ~spl4_11),
% 10.33/1.75    inference(avatar_split_clause,[],[f315,f150,f141,f131,f317])).
% 10.33/1.75  fof(f131,plain,(
% 10.33/1.75    spl4_7 <=> r2_hidden(sK1,sK2)),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 10.33/1.75  fof(f141,plain,(
% 10.33/1.75    spl4_9 <=> v1_ordinal1(sK2)),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 10.33/1.75  fof(f150,plain,(
% 10.33/1.75    spl4_11 <=> ! [X1,X0] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0) | ~v1_ordinal1(X0))),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 10.33/1.75  fof(f315,plain,(
% 10.33/1.75    r1_tarski(sK1,sK2) | (~spl4_7 | ~spl4_9 | ~spl4_11)),
% 10.33/1.75    inference(subsumption_resolution,[],[f313,f143])).
% 10.33/1.75  fof(f143,plain,(
% 10.33/1.75    v1_ordinal1(sK2) | ~spl4_9),
% 10.33/1.75    inference(avatar_component_clause,[],[f141])).
% 10.33/1.75  fof(f313,plain,(
% 10.33/1.75    r1_tarski(sK1,sK2) | ~v1_ordinal1(sK2) | (~spl4_7 | ~spl4_11)),
% 10.33/1.75    inference(resolution,[],[f151,f133])).
% 10.33/1.75  fof(f133,plain,(
% 10.33/1.75    r2_hidden(sK1,sK2) | ~spl4_7),
% 10.33/1.75    inference(avatar_component_clause,[],[f131])).
% 10.33/1.75  fof(f151,plain,(
% 10.33/1.75    ( ! [X0,X1] : (~r2_hidden(X1,X0) | r1_tarski(X1,X0) | ~v1_ordinal1(X0)) ) | ~spl4_11),
% 10.33/1.75    inference(avatar_component_clause,[],[f150])).
% 10.33/1.75  fof(f305,plain,(
% 10.33/1.75    spl4_47 | ~spl4_12 | ~spl4_13),
% 10.33/1.75    inference(avatar_split_clause,[],[f297,f158,f154,f303])).
% 10.33/1.75  fof(f154,plain,(
% 10.33/1.75    spl4_12 <=> ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 10.33/1.75  fof(f158,plain,(
% 10.33/1.75    spl4_13 <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 10.33/1.75    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 10.33/1.75  fof(f297,plain,(
% 10.33/1.75    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | (~spl4_12 | ~spl4_13)),
% 10.33/1.75    inference(superposition,[],[f155,f159])).
% 10.33/1.75  fof(f159,plain,(
% 10.33/1.75    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) ) | ~spl4_13),
% 10.33/1.75    inference(avatar_component_clause,[],[f158])).
% 10.33/1.75  fof(f155,plain,(
% 10.33/1.75    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) ) | ~spl4_12),
% 10.33/1.75    inference(avatar_component_clause,[],[f154])).
% 10.33/1.75  fof(f224,plain,(
% 10.33/1.75    spl4_29),
% 10.33/1.75    inference(avatar_split_clause,[],[f70,f222])).
% 10.33/1.75  fof(f70,plain,(
% 10.33/1.75    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 10.33/1.75    inference(cnf_transformation,[],[f30])).
% 10.33/1.75  fof(f30,plain,(
% 10.33/1.75    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 10.33/1.75    inference(ennf_transformation,[],[f18])).
% 10.33/1.75  fof(f18,axiom,(
% 10.33/1.75    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 10.33/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 10.33/1.75  fof(f208,plain,(
% 10.33/1.75    spl4_25),
% 10.33/1.75    inference(avatar_split_clause,[],[f89,f206])).
% 10.33/1.75  fof(f89,plain,(
% 10.33/1.75    ( ! [X2,X1] : (k1_tarski(X1) = k4_xboole_0(k2_tarski(X1,X1),X2) | r2_hidden(X1,X2)) )),
% 10.33/1.75    inference(equality_resolution,[],[f69])).
% 10.33/1.75  fof(f69,plain,(
% 10.33/1.75    ( ! [X2,X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | X0 != X1 | r2_hidden(X0,X2)) )),
% 10.33/1.75    inference(cnf_transformation,[],[f38])).
% 10.33/1.75  fof(f38,plain,(
% 10.33/1.75    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 10.33/1.75    inference(flattening,[],[f37])).
% 10.33/1.75  fof(f37,plain,(
% 10.33/1.75    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 10.33/1.75    inference(nnf_transformation,[],[f14])).
% 10.33/1.75  fof(f14,axiom,(
% 10.33/1.75    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 10.33/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 10.33/1.75  fof(f204,plain,(
% 10.33/1.75    spl4_24),
% 10.33/1.75    inference(avatar_split_clause,[],[f63,f202])).
% 10.33/1.75  fof(f63,plain,(
% 10.33/1.75    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) )),
% 10.33/1.75    inference(cnf_transformation,[],[f36])).
% 10.33/1.75  fof(f36,plain,(
% 10.33/1.75    ! [X0,X1,X2] : ((r1_tarski(X0,k5_xboole_0(X1,X2)) | ~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 10.33/1.75    inference(flattening,[],[f35])).
% 10.33/1.75  fof(f35,plain,(
% 10.33/1.75    ! [X0,X1,X2] : ((r1_tarski(X0,k5_xboole_0(X1,X2)) | (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 10.33/1.75    inference(nnf_transformation,[],[f3])).
% 10.33/1.75  fof(f3,axiom,(
% 10.33/1.75    ! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 10.33/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).
% 10.33/1.75  fof(f200,plain,(
% 10.33/1.75    spl4_23),
% 10.33/1.75    inference(avatar_split_clause,[],[f64,f198])).
% 10.33/1.75  fof(f64,plain,(
% 10.33/1.75    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) )),
% 10.33/1.75    inference(cnf_transformation,[],[f36])).
% 10.33/1.75  fof(f192,plain,(
% 10.33/1.75    spl4_21),
% 10.33/1.75    inference(avatar_split_clause,[],[f62,f190])).
% 10.33/1.75  fof(f62,plain,(
% 10.33/1.75    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 10.33/1.75    inference(cnf_transformation,[],[f29])).
% 10.33/1.75  fof(f29,plain,(
% 10.33/1.75    ! [X0,X1,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 10.33/1.75    inference(ennf_transformation,[],[f10])).
% 10.33/1.75  fof(f10,axiom,(
% 10.33/1.75    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 10.33/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
% 10.33/1.75  fof(f188,plain,(
% 10.33/1.75    spl4_20),
% 10.33/1.75    inference(avatar_split_clause,[],[f60,f186])).
% 10.33/1.75  fof(f60,plain,(
% 10.33/1.75    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 10.33/1.75    inference(cnf_transformation,[],[f34])).
% 10.33/1.75  fof(f34,plain,(
% 10.33/1.75    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 10.33/1.75    inference(nnf_transformation,[],[f2])).
% 10.33/1.75  fof(f2,axiom,(
% 10.33/1.75    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 10.33/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 10.33/1.75  fof(f184,plain,(
% 10.33/1.75    spl4_19),
% 10.33/1.75    inference(avatar_split_clause,[],[f61,f182])).
% 10.33/1.75  fof(f61,plain,(
% 10.33/1.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 10.33/1.75    inference(cnf_transformation,[],[f34])).
% 10.33/1.75  fof(f176,plain,(
% 10.33/1.75    spl4_17),
% 10.33/1.75    inference(avatar_split_clause,[],[f58,f174])).
% 10.33/1.75  fof(f58,plain,(
% 10.33/1.75    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 10.33/1.75    inference(cnf_transformation,[],[f27])).
% 10.33/1.75  fof(f27,plain,(
% 10.33/1.75    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 10.33/1.75    inference(ennf_transformation,[],[f8])).
% 10.33/1.75  fof(f8,axiom,(
% 10.33/1.75    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 10.33/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 10.33/1.75  fof(f164,plain,(
% 10.33/1.75    spl4_14),
% 10.33/1.75    inference(avatar_split_clause,[],[f54,f162])).
% 10.33/1.75  fof(f54,plain,(
% 10.33/1.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 10.33/1.75    inference(cnf_transformation,[],[f7])).
% 10.33/1.75  fof(f7,axiom,(
% 10.33/1.75    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 10.33/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 10.33/1.75  fof(f160,plain,(
% 10.33/1.75    spl4_13),
% 10.33/1.75    inference(avatar_split_clause,[],[f52,f158])).
% 10.33/1.75  fof(f52,plain,(
% 10.33/1.75    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 10.33/1.75    inference(cnf_transformation,[],[f5])).
% 10.33/1.75  fof(f5,axiom,(
% 10.33/1.75    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 10.33/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 10.33/1.75  fof(f156,plain,(
% 10.33/1.75    spl4_12),
% 10.33/1.75    inference(avatar_split_clause,[],[f51,f154])).
% 10.33/1.75  fof(f51,plain,(
% 10.33/1.75    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 10.33/1.75    inference(cnf_transformation,[],[f4])).
% 10.33/1.75  fof(f4,axiom,(
% 10.33/1.75    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 10.33/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 10.33/1.75  fof(f152,plain,(
% 10.33/1.75    spl4_11),
% 10.33/1.75    inference(avatar_split_clause,[],[f50,f150])).
% 10.33/1.75  fof(f50,plain,(
% 10.33/1.75    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0) | ~v1_ordinal1(X0)) )),
% 10.33/1.75    inference(cnf_transformation,[],[f26])).
% 10.33/1.75  fof(f26,plain,(
% 10.33/1.75    ! [X0] : (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0))),
% 10.33/1.75    inference(ennf_transformation,[],[f23])).
% 10.33/1.75  fof(f23,plain,(
% 10.33/1.75    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 10.33/1.75    inference(unused_predicate_definition_removal,[],[f20])).
% 10.33/1.75  fof(f20,axiom,(
% 10.33/1.75    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 10.33/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).
% 10.33/1.75  fof(f148,plain,(
% 10.33/1.75    spl4_10),
% 10.33/1.75    inference(avatar_split_clause,[],[f48,f146])).
% 10.33/1.75  fof(f48,plain,(
% 10.33/1.75    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 10.33/1.75    inference(cnf_transformation,[],[f6])).
% 10.33/1.75  fof(f6,axiom,(
% 10.33/1.75    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 10.33/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 10.33/1.75  fof(f144,plain,(
% 10.33/1.75    spl4_9),
% 10.33/1.75    inference(avatar_split_clause,[],[f44,f141])).
% 10.33/1.75  fof(f44,plain,(
% 10.33/1.75    v1_ordinal1(sK2)),
% 10.33/1.75    inference(cnf_transformation,[],[f33])).
% 10.33/1.75  fof(f33,plain,(
% 10.33/1.75    ~r2_hidden(sK0,sK2) & r2_hidden(sK1,sK2) & r2_hidden(sK0,sK1) & v1_ordinal1(sK2)),
% 10.33/1.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f32])).
% 10.33/1.75  fof(f32,plain,(
% 10.33/1.75    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r2_hidden(X1,X2) & r2_hidden(X0,X1) & v1_ordinal1(X2)) => (~r2_hidden(sK0,sK2) & r2_hidden(sK1,sK2) & r2_hidden(sK0,sK1) & v1_ordinal1(sK2))),
% 10.33/1.75    introduced(choice_axiom,[])).
% 10.33/1.75  fof(f25,plain,(
% 10.33/1.75    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r2_hidden(X1,X2) & r2_hidden(X0,X1) & v1_ordinal1(X2))),
% 10.33/1.75    inference(flattening,[],[f24])).
% 10.33/1.75  fof(f24,plain,(
% 10.33/1.75    ? [X0,X1,X2] : ((~r2_hidden(X0,X2) & (r2_hidden(X1,X2) & r2_hidden(X0,X1))) & v1_ordinal1(X2))),
% 10.33/1.75    inference(ennf_transformation,[],[f22])).
% 10.33/1.75  fof(f22,negated_conjecture,(
% 10.33/1.75    ~! [X0,X1,X2] : (v1_ordinal1(X2) => ((r2_hidden(X1,X2) & r2_hidden(X0,X1)) => r2_hidden(X0,X2)))),
% 10.33/1.75    inference(negated_conjecture,[],[f21])).
% 10.33/1.75  fof(f21,conjecture,(
% 10.33/1.75    ! [X0,X1,X2] : (v1_ordinal1(X2) => ((r2_hidden(X1,X2) & r2_hidden(X0,X1)) => r2_hidden(X0,X2)))),
% 10.33/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_ordinal1)).
% 10.33/1.75  fof(f139,plain,(
% 10.33/1.75    spl4_8),
% 10.33/1.75    inference(avatar_split_clause,[],[f45,f136])).
% 10.33/1.75  fof(f45,plain,(
% 10.33/1.75    r2_hidden(sK0,sK1)),
% 10.33/1.75    inference(cnf_transformation,[],[f33])).
% 10.33/1.75  fof(f134,plain,(
% 10.33/1.75    spl4_7),
% 10.33/1.75    inference(avatar_split_clause,[],[f46,f131])).
% 10.33/1.75  fof(f46,plain,(
% 10.33/1.75    r2_hidden(sK1,sK2)),
% 10.33/1.75    inference(cnf_transformation,[],[f33])).
% 10.33/1.75  fof(f129,plain,(
% 10.33/1.75    ~spl4_6),
% 10.33/1.75    inference(avatar_split_clause,[],[f47,f126])).
% 10.33/1.75  fof(f47,plain,(
% 10.33/1.75    ~r2_hidden(sK0,sK2)),
% 10.33/1.75    inference(cnf_transformation,[],[f33])).
% 10.33/1.75  fof(f116,plain,(
% 10.33/1.75    spl4_3),
% 10.33/1.75    inference(avatar_split_clause,[],[f57,f114])).
% 10.33/1.75  fof(f57,plain,(
% 10.33/1.75    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 10.33/1.75    inference(cnf_transformation,[],[f1])).
% 10.33/1.75  fof(f1,axiom,(
% 10.33/1.75    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 10.33/1.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 10.33/1.75  % SZS output end Proof for theBenchmark
% 10.33/1.75  % (3376)------------------------------
% 10.33/1.75  % (3376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.33/1.75  % (3376)Termination reason: Refutation
% 10.33/1.75  
% 10.33/1.75  % (3376)Memory used [KB]: 9722
% 10.33/1.75  % (3376)Time elapsed: 0.295 s
% 10.33/1.75  % (3376)------------------------------
% 10.33/1.75  % (3376)------------------------------
% 10.33/1.76  % (3097)Success in time 1.384 s
%------------------------------------------------------------------------------
