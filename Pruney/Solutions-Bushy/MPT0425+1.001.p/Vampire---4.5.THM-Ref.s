%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0425+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:57 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 255 expanded)
%              Number of leaves         :   44 ( 125 expanded)
%              Depth                    :    7
%              Number of atoms          :  393 ( 668 expanded)
%              Number of equality atoms :   40 (  68 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7800,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f49,f54,f58,f62,f66,f70,f74,f78,f82,f90,f94,f98,f102,f107,f114,f129,f137,f153,f169,f180,f209,f252,f313,f390,f773,f787,f2729,f7517,f7724,f7749,f7799])).

fof(f7799,plain,
    ( spl4_1
    | ~ spl4_5
    | ~ spl4_1134 ),
    inference(avatar_contradiction_clause,[],[f7798])).

fof(f7798,plain,
    ( $false
    | spl4_1
    | ~ spl4_5
    | ~ spl4_1134 ),
    inference(subsumption_resolution,[],[f7775,f44])).

fof(f44,plain,
    ( ~ r1_tarski(sK2,k3_tarski(sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_1
  <=> r1_tarski(sK2,k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f7775,plain,
    ( r1_tarski(sK2,k3_tarski(sK0))
    | ~ spl4_5
    | ~ spl4_1134 ),
    inference(superposition,[],[f7748,f61])).

fof(f61,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_5
  <=> ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f7748,plain,
    ( ! [X2] : r1_tarski(k3_xboole_0(sK2,X2),k3_tarski(sK0))
    | ~ spl4_1134 ),
    inference(avatar_component_clause,[],[f7747])).

fof(f7747,plain,
    ( spl4_1134
  <=> ! [X2] : r1_tarski(k3_xboole_0(sK2,X2),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1134])])).

fof(f7749,plain,
    ( spl4_1134
    | ~ spl4_403
    | ~ spl4_1130 ),
    inference(avatar_split_clause,[],[f7739,f7715,f2727,f7747])).

fof(f2727,plain,
    ( spl4_403
  <=> ! [X16,X13,X15,X14] :
        ( ~ r1_tarski(X13,k3_xboole_0(X14,X15))
        | r1_tarski(k3_xboole_0(X13,X16),X15) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_403])])).

fof(f7715,plain,
    ( spl4_1130
  <=> r1_tarski(sK2,k3_xboole_0(sK2,k3_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1130])])).

fof(f7739,plain,
    ( ! [X2] : r1_tarski(k3_xboole_0(sK2,X2),k3_tarski(sK0))
    | ~ spl4_403
    | ~ spl4_1130 ),
    inference(resolution,[],[f7717,f2728])).

fof(f2728,plain,
    ( ! [X14,X15,X13,X16] :
        ( ~ r1_tarski(X13,k3_xboole_0(X14,X15))
        | r1_tarski(k3_xboole_0(X13,X16),X15) )
    | ~ spl4_403 ),
    inference(avatar_component_clause,[],[f2727])).

fof(f7717,plain,
    ( r1_tarski(sK2,k3_xboole_0(sK2,k3_tarski(sK0)))
    | ~ spl4_1130 ),
    inference(avatar_component_clause,[],[f7715])).

fof(f7724,plain,
    ( spl4_1130
    | ~ spl4_5
    | ~ spl4_1092 ),
    inference(avatar_split_clause,[],[f7690,f7515,f60,f7715])).

fof(f7515,plain,
    ( spl4_1092
  <=> ! [X118] : r1_tarski(k3_xboole_0(sK2,X118),k3_xboole_0(sK2,k3_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1092])])).

fof(f7690,plain,
    ( r1_tarski(sK2,k3_xboole_0(sK2,k3_tarski(sK0)))
    | ~ spl4_5
    | ~ spl4_1092 ),
    inference(superposition,[],[f7516,f61])).

fof(f7516,plain,
    ( ! [X118] : r1_tarski(k3_xboole_0(sK2,X118),k3_xboole_0(sK2,k3_tarski(sK0)))
    | ~ spl4_1092 ),
    inference(avatar_component_clause,[],[f7515])).

fof(f7517,plain,
    ( spl4_1092
    | ~ spl4_62
    | ~ spl4_127
    | ~ spl4_403 ),
    inference(avatar_split_clause,[],[f7513,f2727,f785,f387,f7515])).

fof(f387,plain,
    ( spl4_62
  <=> r1_tarski(sK2,k3_xboole_0(sK2,k3_xboole_0(sK2,k3_tarski(k2_xboole_0(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f785,plain,
    ( spl4_127
  <=> ! [X0] : k3_xboole_0(sK2,k3_tarski(X0)) = k3_xboole_0(sK2,k3_tarski(k2_xboole_0(X0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_127])])).

fof(f7513,plain,
    ( ! [X118] : r1_tarski(k3_xboole_0(sK2,X118),k3_xboole_0(sK2,k3_tarski(sK0)))
    | ~ spl4_62
    | ~ spl4_127
    | ~ spl4_403 ),
    inference(forward_demodulation,[],[f7370,f786])).

fof(f786,plain,
    ( ! [X0] : k3_xboole_0(sK2,k3_tarski(X0)) = k3_xboole_0(sK2,k3_tarski(k2_xboole_0(X0,sK1)))
    | ~ spl4_127 ),
    inference(avatar_component_clause,[],[f785])).

fof(f7370,plain,
    ( ! [X118] : r1_tarski(k3_xboole_0(sK2,X118),k3_xboole_0(sK2,k3_tarski(k2_xboole_0(sK0,sK1))))
    | ~ spl4_62
    | ~ spl4_403 ),
    inference(resolution,[],[f2728,f389])).

fof(f389,plain,
    ( r1_tarski(sK2,k3_xboole_0(sK2,k3_xboole_0(sK2,k3_tarski(k2_xboole_0(sK0,sK1)))))
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f387])).

fof(f2729,plain,
    ( spl4_403
    | ~ spl4_17
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f2629,f151,f111,f2727])).

fof(f111,plain,
    ( spl4_17
  <=> ! [X1,X2] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f151,plain,
    ( spl4_23
  <=> ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(k3_xboole_0(X0,X3),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f2629,plain,
    ( ! [X14,X15,X13,X16] :
        ( ~ r1_tarski(X13,k3_xboole_0(X14,X15))
        | r1_tarski(k3_xboole_0(X13,X16),X15) )
    | ~ spl4_17
    | ~ spl4_23 ),
    inference(resolution,[],[f152,f112])).

fof(f112,plain,
    ( ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f111])).

fof(f152,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1)
        | r1_tarski(k3_xboole_0(X0,X3),X2) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f151])).

fof(f787,plain,
    ( spl4_127
    | ~ spl4_8
    | ~ spl4_126 ),
    inference(avatar_split_clause,[],[f774,f771,f72,f785])).

fof(f72,plain,
    ( spl4_8
  <=> ! [X1,X0] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f771,plain,
    ( spl4_126
  <=> ! [X9] : k3_xboole_0(sK2,X9) = k3_xboole_0(sK2,k2_xboole_0(X9,k3_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_126])])).

fof(f774,plain,
    ( ! [X0] : k3_xboole_0(sK2,k3_tarski(X0)) = k3_xboole_0(sK2,k3_tarski(k2_xboole_0(X0,sK1)))
    | ~ spl4_8
    | ~ spl4_126 ),
    inference(superposition,[],[f772,f73])).

fof(f73,plain,
    ( ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f72])).

fof(f772,plain,
    ( ! [X9] : k3_xboole_0(sK2,X9) = k3_xboole_0(sK2,k2_xboole_0(X9,k3_tarski(sK1)))
    | ~ spl4_126 ),
    inference(avatar_component_clause,[],[f771])).

fof(f773,plain,
    ( spl4_126
    | ~ spl4_4
    | ~ spl4_13
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f769,f190,f92,f56,f771])).

fof(f56,plain,
    ( spl4_4
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f92,plain,
    ( spl4_13
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f190,plain,
    ( spl4_28
  <=> k1_xboole_0 = k3_xboole_0(sK2,k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f769,plain,
    ( ! [X9] : k3_xboole_0(sK2,X9) = k3_xboole_0(sK2,k2_xboole_0(X9,k3_tarski(sK1)))
    | ~ spl4_4
    | ~ spl4_13
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f737,f57])).

fof(f57,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f737,plain,
    ( ! [X9] : k3_xboole_0(sK2,k2_xboole_0(X9,k3_tarski(sK1))) = k2_xboole_0(k3_xboole_0(sK2,X9),k1_xboole_0)
    | ~ spl4_13
    | ~ spl4_28 ),
    inference(superposition,[],[f93,f192])).

fof(f192,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k3_tarski(sK1))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f190])).

fof(f93,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f92])).

fof(f390,plain,
    ( spl4_62
    | ~ spl4_36
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f378,f310,f250,f387])).

fof(f250,plain,
    ( spl4_36
  <=> ! [X3,X4] :
        ( ~ r1_tarski(X3,X4)
        | r1_tarski(X3,k3_xboole_0(X3,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f310,plain,
    ( spl4_48
  <=> r1_tarski(sK2,k3_xboole_0(sK2,k3_tarski(k2_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f378,plain,
    ( r1_tarski(sK2,k3_xboole_0(sK2,k3_xboole_0(sK2,k3_tarski(k2_xboole_0(sK0,sK1)))))
    | ~ spl4_36
    | ~ spl4_48 ),
    inference(resolution,[],[f312,f251])).

fof(f251,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(X3,X4)
        | r1_tarski(X3,k3_xboole_0(X3,X4)) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f250])).

fof(f312,plain,
    ( r1_tarski(sK2,k3_xboole_0(sK2,k3_tarski(k2_xboole_0(sK0,sK1))))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f310])).

fof(f313,plain,
    ( spl4_48
    | ~ spl4_3
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f286,f250,f51,f310])).

fof(f51,plain,
    ( spl4_3
  <=> r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f286,plain,
    ( r1_tarski(sK2,k3_xboole_0(sK2,k3_tarski(k2_xboole_0(sK0,sK1))))
    | ~ spl4_3
    | ~ spl4_36 ),
    inference(resolution,[],[f251,f53])).

fof(f53,plain,
    ( r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f252,plain,
    ( spl4_36
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f237,f105,f100,f250])).

fof(f100,plain,
    ( spl4_15
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f105,plain,
    ( spl4_16
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f237,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(X3,X4)
        | r1_tarski(X3,k3_xboole_0(X3,X4)) )
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(resolution,[],[f101,f106])).

fof(f106,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f105])).

fof(f101,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X0,X2)
        | r1_tarski(X0,k3_xboole_0(X1,X2)) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f100])).

fof(f209,plain,
    ( spl4_28
    | ~ spl4_7
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f187,f177,f68,f190])).

fof(f68,plain,
    ( spl4_7
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f177,plain,
    ( spl4_27
  <=> k1_xboole_0 = k3_xboole_0(k3_tarski(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f187,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k3_tarski(sK1))
    | ~ spl4_7
    | ~ spl4_27 ),
    inference(superposition,[],[f69,f179])).

fof(f179,plain,
    ( k1_xboole_0 = k3_xboole_0(k3_tarski(sK1),sK2)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f177])).

fof(f69,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f180,plain,
    ( spl4_27
    | ~ spl4_12
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f175,f166,f88,f177])).

fof(f88,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f166,plain,
    ( spl4_25
  <=> r1_xboole_0(k3_tarski(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f175,plain,
    ( k1_xboole_0 = k3_xboole_0(k3_tarski(sK1),sK2)
    | ~ spl4_12
    | ~ spl4_25 ),
    inference(resolution,[],[f168,f89])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f88])).

fof(f168,plain,
    ( r1_xboole_0(k3_tarski(sK1),sK2)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f166])).

fof(f169,plain,
    ( spl4_25
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f164,f127,f76,f166])).

fof(f76,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( r1_xboole_0(k3_tarski(X0),X1)
        | ~ r1_xboole_0(sK3(X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f127,plain,
    ( spl4_19
  <=> ! [X0] :
        ( r1_xboole_0(k3_tarski(sK1),X0)
        | r1_xboole_0(sK3(sK1,X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f164,plain,
    ( r1_xboole_0(k3_tarski(sK1),sK2)
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,
    ( r1_xboole_0(k3_tarski(sK1),sK2)
    | r1_xboole_0(k3_tarski(sK1),sK2)
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(resolution,[],[f128,f77])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(sK3(X0,X1),X1)
        | r1_xboole_0(k3_tarski(X0),X1) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f76])).

fof(f128,plain,
    ( ! [X0] :
        ( r1_xboole_0(sK3(sK1,X0),sK2)
        | r1_xboole_0(k3_tarski(sK1),X0) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f127])).

fof(f153,plain,
    ( spl4_23
    | ~ spl4_14
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f146,f135,f96,f151])).

fof(f96,plain,
    ( spl4_14
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f135,plain,
    ( spl4_20
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f146,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(k3_xboole_0(X0,X3),X2) )
    | ~ spl4_14
    | ~ spl4_20 ),
    inference(resolution,[],[f136,f97])).

fof(f97,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f96])).

fof(f136,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k3_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f135])).

fof(f137,plain,
    ( spl4_20
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f130,f96,f64,f135])).

fof(f64,plain,
    ( spl4_6
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f130,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k3_xboole_0(X0,X2),X1) )
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(resolution,[],[f97,f65])).

fof(f65,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f129,plain,
    ( spl4_19
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f125,f80,f47,f127])).

fof(f47,plain,
    ( spl4_2
  <=> ! [X3] :
        ( r1_xboole_0(X3,sK2)
        | ~ r2_hidden(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f80,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( r1_xboole_0(k3_tarski(X0),X1)
        | r2_hidden(sK3(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f125,plain,
    ( ! [X0] :
        ( r1_xboole_0(k3_tarski(sK1),X0)
        | r1_xboole_0(sK3(sK1,X0),sK2) )
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(resolution,[],[f81,f48])).

fof(f48,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | r1_xboole_0(X3,sK2) )
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),X0)
        | r1_xboole_0(k3_tarski(X0),X1) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f80])).

fof(f114,plain,
    ( spl4_17
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f109,f68,f64,f111])).

fof(f109,plain,
    ( ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1)
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(superposition,[],[f65,f69])).

fof(f107,plain,
    ( spl4_16
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f103,f64,f60,f105])).

fof(f103,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(superposition,[],[f65,f61])).

fof(f102,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f40,f100])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f98,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f39,f96])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f94,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f38,f92])).

fof(f38,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f90,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f36,f88])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f82,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f34,f80])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ( ~ r1_xboole_0(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_xboole_0(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_xboole_0(X2,X1) )
     => r1_xboole_0(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_zfmisc_1)).

fof(f78,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f35,f76])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ~ r1_xboole_0(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f33,f72])).

fof(f33,plain,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(f70,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f32,f68])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f66,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f31,f64])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f62,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f30,f60])).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f58,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f29,f56])).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f54,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f26,f51])).

fof(f26,plain,(
    r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(sK2,k3_tarski(sK0))
    & ! [X3] :
        ( r1_xboole_0(X3,sK2)
        | ~ r2_hidden(X3,sK1) )
    & r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X2,k3_tarski(X0))
        & ! [X3] :
            ( r1_xboole_0(X3,X2)
            | ~ r2_hidden(X3,X1) )
        & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) )
   => ( ~ r1_tarski(sK2,k3_tarski(sK0))
      & ! [X3] :
          ( r1_xboole_0(X3,sK2)
          | ~ r2_hidden(X3,sK1) )
      & r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,k3_tarski(X0))
      & ! [X3] :
          ( r1_xboole_0(X3,X2)
          | ~ r2_hidden(X3,X1) )
      & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,k3_tarski(X0))
      & ! [X3] :
          ( r1_xboole_0(X3,X2)
          | ~ r2_hidden(X3,X1) )
      & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( ! [X3] :
              ( r2_hidden(X3,X1)
             => r1_xboole_0(X3,X2) )
          & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) )
       => r1_tarski(X2,k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( r2_hidden(X3,X1)
           => r1_xboole_0(X3,X2) )
        & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) )
     => r1_tarski(X2,k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_setfam_1)).

fof(f49,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f27,f47])).

fof(f27,plain,(
    ! [X3] :
      ( r1_xboole_0(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f28,f42])).

fof(f28,plain,(
    ~ r1_tarski(sK2,k3_tarski(sK0)) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
