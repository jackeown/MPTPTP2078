%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:29 EST 2020

% Result     : Theorem 12.15s
% Output     : Refutation 12.15s
% Verified   : 
% Statistics : Number of formulae       :  212 ( 587 expanded)
%              Number of leaves         :   55 ( 247 expanded)
%              Depth                    :   10
%              Number of atoms          :  560 (1101 expanded)
%              Number of equality atoms :  178 ( 548 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4870,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f96,f108,f112,f124,f145,f149,f153,f242,f279,f283,f594,f603,f620,f1067,f1072,f1141,f1145,f1159,f1173,f1355,f1712,f2046,f2099,f2103,f2152,f2262,f4835,f4853,f4860,f4869])).

fof(f4869,plain,
    ( ~ spl5_5
    | ~ spl5_15
    | ~ spl5_34
    | ~ spl5_46
    | ~ spl5_57
    | spl5_71
    | ~ spl5_74 ),
    inference(avatar_contradiction_clause,[],[f4868])).

fof(f4868,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_15
    | ~ spl5_34
    | ~ spl5_46
    | ~ spl5_57
    | spl5_71
    | ~ spl5_74 ),
    inference(subsumption_resolution,[],[f4867,f278])).

fof(f278,plain,
    ( ! [X2,X0,X1] : sP1(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl5_15
  <=> ! [X1,X0,X2] : sP1(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f4867,plain,
    ( ~ sP1(sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_5
    | ~ spl5_34
    | ~ spl5_46
    | ~ spl5_57
    | spl5_71
    | ~ spl5_74 ),
    inference(forward_demodulation,[],[f4866,f2102])).

fof(f2102,plain,
    ( ! [X6] : k3_xboole_0(X6,X6) = X6
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f2101])).

fof(f2101,plain,
    ( spl5_46
  <=> ! [X6] : k3_xboole_0(X6,X6) = X6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f4866,plain,
    ( ~ sP1(sK2,sK2,sK2,k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | ~ spl5_5
    | ~ spl5_34
    | ~ spl5_46
    | ~ spl5_57
    | spl5_71
    | ~ spl5_74 ),
    inference(forward_demodulation,[],[f4865,f1354])).

fof(f1354,plain,
    ( ! [X8,X9] : k5_xboole_0(X8,k5_xboole_0(X9,X8)) = X9
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f1353])).

fof(f1353,plain,
    ( spl5_34
  <=> ! [X9,X8] : k5_xboole_0(X8,k5_xboole_0(X9,X8)) = X9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f4865,plain,
    ( ~ sP1(sK2,sK2,sK2,k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))
    | ~ spl5_5
    | ~ spl5_46
    | ~ spl5_57
    | spl5_71
    | ~ spl5_74 ),
    inference(forward_demodulation,[],[f4862,f3372])).

fof(f3372,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))
    | ~ spl5_5
    | ~ spl5_46
    | ~ spl5_57 ),
    inference(forward_demodulation,[],[f3319,f107])).

fof(f107,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl5_5
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f3319,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,X1),X0)
    | ~ spl5_46
    | ~ spl5_57 ),
    inference(superposition,[],[f2261,f2102])).

fof(f2261,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X2,X0),X1) = k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X1,X0))
    | ~ spl5_57 ),
    inference(avatar_component_clause,[],[f2260])).

fof(f2260,plain,
    ( spl5_57
  <=> ! [X1,X0,X2] : k3_xboole_0(k5_xboole_0(X2,X0),X1) = k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f4862,plain,
    ( ~ sP1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))
    | spl5_71
    | ~ spl5_74 ),
    inference(superposition,[],[f4834,f4849])).

fof(f4849,plain,
    ( sK2 = sK3
    | ~ spl5_74 ),
    inference(avatar_component_clause,[],[f4848])).

fof(f4848,plain,
    ( spl5_74
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f4834,plain,
    ( ~ sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))
    | spl5_71 ),
    inference(avatar_component_clause,[],[f4833])).

fof(f4833,plain,
    ( spl5_71
  <=> sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f4860,plain,
    ( spl5_74
    | ~ spl5_15
    | ~ spl5_45
    | spl5_75 ),
    inference(avatar_split_clause,[],[f4855,f4851,f2097,f277,f4848])).

fof(f2097,plain,
    ( spl5_45
  <=> ! [X1,X0] :
        ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f4851,plain,
    ( spl5_75
  <=> sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f4855,plain,
    ( sK2 = sK3
    | ~ spl5_15
    | ~ spl5_45
    | spl5_75 ),
    inference(subsumption_resolution,[],[f4854,f278])).

fof(f4854,plain,
    ( ~ sP1(sK2,sK2,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | sK2 = sK3
    | ~ spl5_45
    | spl5_75 ),
    inference(superposition,[],[f4852,f2098])).

fof(f2098,plain,
    ( ! [X0,X1] :
        ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
        | X0 = X1 )
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f2097])).

fof(f4852,plain,
    ( ~ sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))
    | spl5_75 ),
    inference(avatar_component_clause,[],[f4851])).

fof(f4853,plain,
    ( spl5_74
    | ~ spl5_75
    | ~ spl5_5
    | ~ spl5_21
    | ~ spl5_43
    | ~ spl5_45
    | spl5_71 ),
    inference(avatar_split_clause,[],[f4846,f4833,f2097,f1710,f601,f106,f4851,f4848])).

fof(f601,plain,
    ( spl5_21
  <=> ! [X1,X0,X2] : r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f1710,plain,
    ( spl5_43
  <=> ! [X1,X0] :
        ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f4846,plain,
    ( ~ sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))
    | sK2 = sK3
    | ~ spl5_5
    | ~ spl5_21
    | ~ spl5_43
    | ~ spl5_45
    | spl5_71 ),
    inference(forward_demodulation,[],[f4845,f2036])).

fof(f2036,plain,
    ( ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | ~ spl5_21
    | ~ spl5_43 ),
    inference(unit_resulting_resolution,[],[f602,f1711])).

fof(f1711,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f1710])).

fof(f602,plain,
    ( ! [X2,X0,X1] : r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f601])).

fof(f4845,plain,
    ( ~ sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | sK2 = sK3
    | ~ spl5_5
    | ~ spl5_45
    | spl5_71 ),
    inference(forward_demodulation,[],[f4844,f107])).

fof(f4844,plain,
    ( ~ sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))))
    | sK2 = sK3
    | ~ spl5_45
    | spl5_71 ),
    inference(superposition,[],[f4834,f2098])).

fof(f4835,plain,
    ( ~ spl5_71
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_29
    | ~ spl5_32
    | ~ spl5_46
    | spl5_49 ),
    inference(avatar_split_clause,[],[f2236,f2150,f2101,f1171,f1139,f151,f143,f110,f106,f4833])).

fof(f110,plain,
    ( spl5_6
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f143,plain,
    ( spl5_9
  <=> ! [X1,X0,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f151,plain,
    ( spl5_11
  <=> ! [X5,X7,X6] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f1139,plain,
    ( spl5_29
  <=> ! [X1,X3,X0,X2] :
        ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
        | ~ sP1(X0,X1,X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f1171,plain,
    ( spl5_32
  <=> ! [X1,X0] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f2150,plain,
    ( spl5_49
  <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f2236,plain,
    ( ~ sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_29
    | ~ spl5_32
    | ~ spl5_46
    | spl5_49 ),
    inference(forward_demodulation,[],[f2235,f111])).

fof(f111,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f2235,plain,
    ( ~ sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_29
    | ~ spl5_32
    | ~ spl5_46
    | spl5_49 ),
    inference(forward_demodulation,[],[f2234,f2109])).

fof(f2109,plain,
    ( ! [X4,X5] : k5_xboole_0(X4,k3_xboole_0(X5,X4)) = k3_xboole_0(X4,k5_xboole_0(X4,X5))
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_46 ),
    inference(forward_demodulation,[],[f2106,f107])).

fof(f2106,plain,
    ( ! [X4,X5] : k5_xboole_0(X4,k3_xboole_0(X5,X4)) = k3_xboole_0(k5_xboole_0(X4,X5),X4)
    | ~ spl5_9
    | ~ spl5_46 ),
    inference(superposition,[],[f144,f2102])).

fof(f144,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f143])).

fof(f2234,plain,
    ( ~ sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))
    | ~ spl5_6
    | ~ spl5_11
    | ~ spl5_29
    | ~ spl5_32
    | spl5_49 ),
    inference(forward_demodulation,[],[f2233,f152])).

fof(f152,plain,
    ( ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f151])).

fof(f2233,plain,
    ( ~ sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | ~ spl5_6
    | ~ spl5_11
    | ~ spl5_29
    | ~ spl5_32
    | spl5_49 ),
    inference(forward_demodulation,[],[f2232,f152])).

fof(f2232,plain,
    ( ~ sP1(sK2,sK2,sK3,k5_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | ~ spl5_6
    | ~ spl5_29
    | ~ spl5_32
    | spl5_49 ),
    inference(forward_demodulation,[],[f2231,f111])).

fof(f2231,plain,
    ( ~ sP1(sK2,sK2,sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | ~ spl5_29
    | ~ spl5_32
    | spl5_49 ),
    inference(forward_demodulation,[],[f2161,f1172])).

fof(f1172,plain,
    ( ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f1171])).

fof(f2161,plain,
    ( ~ sP1(sK2,sK2,sK3,k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | ~ spl5_29
    | spl5_49 ),
    inference(unit_resulting_resolution,[],[f2151,f1140])).

fof(f1140,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ sP1(X0,X1,X2,X3)
        | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 )
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f1139])).

fof(f2151,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))
    | spl5_49 ),
    inference(avatar_component_clause,[],[f2150])).

fof(f2262,plain,
    ( spl5_57
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f290,f143,f106,f2260])).

fof(f290,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X2,X0),X1) = k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X1,X0))
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(superposition,[],[f144,f107])).

fof(f2152,plain,(
    ~ spl5_49 ),
    inference(avatar_split_clause,[],[f77,f2150])).

fof(f77,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f40,f74,f74,f76,f76])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f74])).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f67,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    k2_tarski(sK2,sK3) != k3_tarski(k2_tarski(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    k2_tarski(sK2,sK3) != k3_tarski(k2_tarski(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f23,f30])).

fof(f30,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK2,sK3) != k3_tarski(k2_tarski(k1_tarski(sK2),k1_tarski(sK3))) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

fof(f2103,plain,
    ( spl5_46
    | ~ spl5_31
    | ~ spl5_34
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f2078,f2044,f1353,f1157,f2101])).

fof(f1157,plain,
    ( spl5_31
  <=> ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f2044,plain,
    ( spl5_44
  <=> ! [X1,X0] : k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f2078,plain,
    ( ! [X6] : k3_xboole_0(X6,X6) = X6
    | ~ spl5_31
    | ~ spl5_34
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f2050,f1354])).

fof(f2050,plain,
    ( ! [X6] : k3_xboole_0(X6,k5_xboole_0(k1_xboole_0,k5_xboole_0(X6,k1_xboole_0))) = X6
    | ~ spl5_31
    | ~ spl5_44 ),
    inference(superposition,[],[f2045,f1158])).

fof(f1158,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f1157])).

fof(f2045,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f2044])).

fof(f2099,plain,(
    spl5_45 ),
    inference(avatar_split_clause,[],[f81,f2097])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f51,f74,f76,f76])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f2046,plain,
    ( spl5_44
    | ~ spl5_6
    | ~ spl5_11
    | ~ spl5_20
    | ~ spl5_25
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f1351,f1171,f618,f592,f151,f110,f2044])).

fof(f592,plain,
    ( spl5_20
  <=> ! [X7,X8,X6] : k5_xboole_0(X7,k5_xboole_0(X8,X6)) = k5_xboole_0(X7,k5_xboole_0(X6,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f618,plain,
    ( spl5_25
  <=> ! [X1,X0] : k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f1351,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0
    | ~ spl5_6
    | ~ spl5_11
    | ~ spl5_20
    | ~ spl5_25
    | ~ spl5_32 ),
    inference(forward_demodulation,[],[f1350,f593])).

fof(f593,plain,
    ( ! [X6,X8,X7] : k5_xboole_0(X7,k5_xboole_0(X8,X6)) = k5_xboole_0(X7,k5_xboole_0(X6,X8))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f592])).

fof(f1350,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X0,X1),X0))) = X0
    | ~ spl5_6
    | ~ spl5_11
    | ~ spl5_25
    | ~ spl5_32 ),
    inference(forward_demodulation,[],[f1349,f152])).

fof(f1349,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) = X0
    | ~ spl5_6
    | ~ spl5_25
    | ~ spl5_32 ),
    inference(forward_demodulation,[],[f1324,f111])).

fof(f1324,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = X0
    | ~ spl5_25
    | ~ spl5_32 ),
    inference(superposition,[],[f619,f1172])).

fof(f619,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f618])).

fof(f1712,plain,(
    spl5_43 ),
    inference(avatar_split_clause,[],[f82,f1710])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f76,f76])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f1355,plain,
    ( spl5_34
    | ~ spl5_1
    | ~ spl5_11
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f1125,f1070,f151,f90,f1353])).

fof(f90,plain,
    ( spl5_1
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1070,plain,
    ( spl5_28
  <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f1125,plain,
    ( ! [X8,X9] : k5_xboole_0(X8,k5_xboole_0(X9,X8)) = X9
    | ~ spl5_1
    | ~ spl5_11
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f1091,f91])).

fof(f91,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f1091,plain,
    ( ! [X8,X9] : k5_xboole_0(X9,k1_xboole_0) = k5_xboole_0(X8,k5_xboole_0(X9,X8))
    | ~ spl5_11
    | ~ spl5_28 ),
    inference(superposition,[],[f152,f1071])).

fof(f1071,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f1070])).

fof(f1173,plain,(
    spl5_32 ),
    inference(avatar_split_clause,[],[f80,f1171])).

fof(f80,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f47,f74])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f1159,plain,
    ( spl5_31
    | ~ spl5_5
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f1146,f1143,f106,f1157])).

fof(f1143,plain,
    ( spl5_30
  <=> ! [X22] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f1146,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)
    | ~ spl5_5
    | ~ spl5_30 ),
    inference(superposition,[],[f1144,f107])).

fof(f1144,plain,
    ( ! [X22] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X22)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f1143])).

fof(f1145,plain,
    ( spl5_30
    | ~ spl5_9
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f1119,f1070,f143,f1143])).

fof(f1119,plain,
    ( ! [X22] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X22)
    | ~ spl5_9
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f1082,f1071])).

fof(f1082,plain,
    ( ! [X21,X22] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X21,X21),X22)
    | ~ spl5_9
    | ~ spl5_28 ),
    inference(superposition,[],[f1071,f144])).

fof(f1141,plain,(
    spl5_29 ),
    inference(avatar_split_clause,[],[f83,f1139])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(definition_unfolding,[],[f66,f73])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP1(X0,X1,X2,X3) )
      & ( sP1(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP1(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f26,f28,f27])).

fof(f27,plain,(
    ! [X4,X2,X1,X0] :
      ( sP0(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( sP1(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP0(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f1072,plain,
    ( spl5_28
    | ~ spl5_25
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f1068,f1065,f618,f1070])).

fof(f1065,plain,
    ( spl5_27
  <=> ! [X1,X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f1068,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl5_25
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f1066,f619])).

fof(f1066,plain,
    ( ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f1065])).

fof(f1067,plain,(
    spl5_27 ),
    inference(avatar_split_clause,[],[f78,f1065])).

fof(f78,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f45,f49,f75])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f620,plain,(
    spl5_25 ),
    inference(avatar_split_clause,[],[f79,f618])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f46,f75])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f603,plain,
    ( spl5_21
    | ~ spl5_2
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f595,f277,f240,f94,f601])).

fof(f94,plain,
    ( spl5_2
  <=> ! [X1,X3,X2] : sP0(X1,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f240,plain,
    ( spl5_13
  <=> ! [X1,X3,X5,X0,X2] :
        ( r2_hidden(X5,X3)
        | ~ sP0(X5,X2,X1,X0)
        | ~ sP1(X0,X1,X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f595,plain,
    ( ! [X2,X0,X1] : r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))
    | ~ spl5_2
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f95,f278,f241])).

fof(f241,plain,
    ( ! [X2,X0,X5,X3,X1] :
        ( ~ sP1(X0,X1,X2,X3)
        | ~ sP0(X5,X2,X1,X0)
        | r2_hidden(X5,X3) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f240])).

fof(f95,plain,
    ( ! [X2,X3,X1] : sP0(X1,X1,X2,X3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f594,plain,
    ( spl5_20
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f318,f281,f151,f592])).

fof(f281,plain,
    ( spl5_16
  <=> ! [X3,X5,X4] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f318,plain,
    ( ! [X6,X8,X7] : k5_xboole_0(X7,k5_xboole_0(X8,X6)) = k5_xboole_0(X7,k5_xboole_0(X6,X8))
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(superposition,[],[f282,f152])).

fof(f282,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f281])).

fof(f283,plain,
    ( spl5_16
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f164,f147,f122,f281])).

fof(f122,plain,
    ( spl5_8
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f147,plain,
    ( spl5_10
  <=> ! [X3,X2,X4] : k5_xboole_0(X2,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_xboole_0(X3,X2),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f164,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(superposition,[],[f148,f123])).

fof(f123,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f148,plain,
    ( ! [X4,X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_xboole_0(X3,X2),X4)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f147])).

fof(f279,plain,(
    spl5_15 ),
    inference(avatar_split_clause,[],[f88,f277])).

fof(f88,plain,(
    ! [X2,X0,X1] : sP1(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f65,f73])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f242,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f58,f240])).

fof(f58,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | ~ sP0(X5,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ~ sP0(sK4(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sP0(sK4(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X5,X2,X1,X0) )
            & ( sP0(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP0(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP0(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP0(sK4(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sP0(sK4(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X5,X2,X1,X0) )
            & ( sP0(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP0(X4,X2,X1,X0) )
            & ( sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f153,plain,
    ( spl5_11
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f135,f122,f110,f151])).

fof(f135,plain,
    ( ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(superposition,[],[f123,f111])).

fof(f149,plain,
    ( spl5_10
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f130,f122,f110,f147])).

fof(f130,plain,
    ( ! [X4,X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_xboole_0(X3,X2),X4)
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(superposition,[],[f123,f111])).

fof(f145,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f55,f143])).

fof(f55,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f124,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f54,f122])).

fof(f54,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f112,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f44,f110])).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f108,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f43,f106])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f96,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f85,f94])).

fof(f85,plain,(
    ! [X2,X3,X1] : sP0(X1,X1,X2,X3) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP0(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP0(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP0(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP0(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f92,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f41,f90])).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:09:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (18466)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (18473)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (18465)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (18472)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (18489)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (18473)Refutation not found, incomplete strategy% (18473)------------------------------
% 0.21/0.52  % (18473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18473)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (18473)Memory used [KB]: 10618
% 0.21/0.52  % (18473)Time elapsed: 0.105 s
% 0.21/0.52  % (18473)------------------------------
% 0.21/0.52  % (18473)------------------------------
% 0.21/0.52  % (18477)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (18463)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (18484)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (18491)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (18480)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (18475)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (18472)Refutation not found, incomplete strategy% (18472)------------------------------
% 0.21/0.53  % (18472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18472)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18472)Memory used [KB]: 10618
% 0.21/0.53  % (18472)Time elapsed: 0.118 s
% 0.21/0.53  % (18472)------------------------------
% 0.21/0.53  % (18472)------------------------------
% 0.21/0.53  % (18486)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (18471)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (18485)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (18485)Refutation not found, incomplete strategy% (18485)------------------------------
% 0.21/0.53  % (18485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18485)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18485)Memory used [KB]: 1663
% 0.21/0.53  % (18485)Time elapsed: 0.096 s
% 0.21/0.53  % (18485)------------------------------
% 0.21/0.53  % (18485)------------------------------
% 0.21/0.54  % (18468)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (18462)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (18462)Refutation not found, incomplete strategy% (18462)------------------------------
% 0.21/0.54  % (18462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18462)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18462)Memory used [KB]: 1663
% 0.21/0.54  % (18462)Time elapsed: 0.135 s
% 0.21/0.54  % (18462)------------------------------
% 0.21/0.54  % (18462)------------------------------
% 0.21/0.54  % (18477)Refutation not found, incomplete strategy% (18477)------------------------------
% 0.21/0.54  % (18477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18477)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18477)Memory used [KB]: 6140
% 0.21/0.54  % (18477)Time elapsed: 0.128 s
% 0.21/0.54  % (18477)------------------------------
% 0.21/0.54  % (18477)------------------------------
% 0.21/0.54  % (18467)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (18469)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (18464)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.41/0.55  % (18483)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.55  % (18482)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.56  % (18470)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.56  % (18479)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.56  % (18478)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.56  % (18464)Refutation not found, incomplete strategy% (18464)------------------------------
% 1.41/0.56  % (18464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (18474)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.56  % (18481)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.56  % (18488)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.56  % (18490)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.56  % (18464)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (18464)Memory used [KB]: 10746
% 1.41/0.56  % (18464)Time elapsed: 0.140 s
% 1.41/0.56  % (18464)------------------------------
% 1.41/0.56  % (18464)------------------------------
% 1.41/0.56  % (18476)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.63/0.57  % (18483)Refutation not found, incomplete strategy% (18483)------------------------------
% 1.63/0.57  % (18483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (18483)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.57  
% 1.63/0.57  % (18483)Memory used [KB]: 1791
% 1.63/0.57  % (18483)Time elapsed: 0.173 s
% 1.63/0.57  % (18483)------------------------------
% 1.63/0.57  % (18483)------------------------------
% 1.63/0.57  % (18487)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.63/0.57  % (18470)Refutation not found, incomplete strategy% (18470)------------------------------
% 1.63/0.57  % (18470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (18470)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.57  
% 1.63/0.57  % (18470)Memory used [KB]: 10746
% 1.63/0.57  % (18470)Time elapsed: 0.169 s
% 1.63/0.57  % (18470)------------------------------
% 1.63/0.57  % (18470)------------------------------
% 1.63/0.57  % (18479)Refutation not found, incomplete strategy% (18479)------------------------------
% 1.63/0.57  % (18479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (18479)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.57  
% 1.63/0.57  % (18479)Memory used [KB]: 10618
% 1.63/0.57  % (18479)Time elapsed: 0.163 s
% 1.63/0.57  % (18479)------------------------------
% 1.63/0.57  % (18479)------------------------------
% 1.63/0.57  % (18482)Refutation not found, incomplete strategy% (18482)------------------------------
% 1.63/0.57  % (18482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (18482)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.57  
% 1.63/0.57  % (18482)Memory used [KB]: 10746
% 1.63/0.57  % (18482)Time elapsed: 0.169 s
% 1.63/0.57  % (18482)------------------------------
% 1.63/0.57  % (18482)------------------------------
% 2.22/0.66  % (18492)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.22/0.67  % (18492)Refutation not found, incomplete strategy% (18492)------------------------------
% 2.22/0.67  % (18492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.67  % (18492)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.67  
% 2.22/0.67  % (18492)Memory used [KB]: 6140
% 2.22/0.67  % (18492)Time elapsed: 0.115 s
% 2.22/0.67  % (18492)------------------------------
% 2.22/0.67  % (18492)------------------------------
% 2.22/0.67  % (18494)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.22/0.67  % (18493)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.22/0.68  % (18496)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.22/0.69  % (18497)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.22/0.70  % (18498)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.22/0.71  % (18499)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.22/0.71  % (18501)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.22/0.71  % (18495)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.22/0.72  % (18500)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.75/0.82  % (18502)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 3.13/0.83  % (18467)Time limit reached!
% 3.13/0.83  % (18467)------------------------------
% 3.13/0.83  % (18467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.13/0.83  % (18467)Termination reason: Time limit
% 3.13/0.83  
% 3.13/0.83  % (18467)Memory used [KB]: 9978
% 3.13/0.83  % (18467)Time elapsed: 0.427 s
% 3.13/0.83  % (18467)------------------------------
% 3.13/0.83  % (18467)------------------------------
% 3.37/0.92  % (18463)Time limit reached!
% 3.37/0.92  % (18463)------------------------------
% 3.37/0.92  % (18463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.37/0.92  % (18474)Time limit reached!
% 3.37/0.92  % (18474)------------------------------
% 3.37/0.92  % (18474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.37/0.92  % (18474)Termination reason: Time limit
% 3.37/0.92  
% 3.37/0.92  % (18474)Memory used [KB]: 10618
% 3.37/0.92  % (18474)Time elapsed: 0.520 s
% 3.37/0.92  % (18474)------------------------------
% 3.37/0.92  % (18474)------------------------------
% 3.37/0.92  % (18463)Termination reason: Time limit
% 3.37/0.92  
% 3.37/0.92  % (18463)Memory used [KB]: 10362
% 3.37/0.92  % (18463)Time elapsed: 0.514 s
% 3.37/0.92  % (18463)------------------------------
% 3.37/0.92  % (18463)------------------------------
% 3.89/0.96  % (18503)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 3.89/0.97  % (18496)Time limit reached!
% 3.89/0.97  % (18496)------------------------------
% 3.89/0.97  % (18496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.89/0.98  % (18496)Termination reason: Time limit
% 3.89/0.98  
% 3.89/0.98  % (18496)Memory used [KB]: 13176
% 3.89/0.98  % (18496)Time elapsed: 0.402 s
% 3.89/0.98  % (18496)------------------------------
% 3.89/0.98  % (18496)------------------------------
% 3.89/0.98  % (18495)Time limit reached!
% 3.89/0.98  % (18495)------------------------------
% 3.89/0.98  % (18495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.89/0.98  % (18495)Termination reason: Time limit
% 3.89/0.98  % (18495)Termination phase: Saturation
% 3.89/0.98  
% 3.89/0.98  % (18495)Memory used [KB]: 7419
% 3.89/0.98  % (18495)Time elapsed: 0.400 s
% 3.89/0.98  % (18495)------------------------------
% 3.89/0.98  % (18495)------------------------------
% 3.89/1.02  % (18490)Time limit reached!
% 3.89/1.02  % (18490)------------------------------
% 3.89/1.02  % (18490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.89/1.02  % (18490)Termination reason: Time limit
% 3.89/1.02  % (18490)Termination phase: Saturation
% 3.89/1.02  
% 3.89/1.02  % (18490)Memory used [KB]: 9594
% 3.89/1.02  % (18490)Time elapsed: 0.600 s
% 3.89/1.02  % (18490)------------------------------
% 3.89/1.02  % (18490)------------------------------
% 3.89/1.02  % (18469)Time limit reached!
% 3.89/1.02  % (18469)------------------------------
% 3.89/1.02  % (18469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.89/1.02  % (18469)Termination reason: Time limit
% 3.89/1.02  
% 3.89/1.02  % (18469)Memory used [KB]: 11129
% 3.89/1.02  % (18469)Time elapsed: 0.611 s
% 3.89/1.02  % (18469)------------------------------
% 3.89/1.02  % (18469)------------------------------
% 4.39/1.04  % (18478)Time limit reached!
% 4.39/1.04  % (18478)------------------------------
% 4.39/1.04  % (18478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/1.04  % (18478)Termination reason: Time limit
% 4.39/1.04  
% 4.39/1.04  % (18478)Memory used [KB]: 15607
% 4.39/1.04  % (18478)Time elapsed: 0.629 s
% 4.39/1.04  % (18478)------------------------------
% 4.39/1.04  % (18478)------------------------------
% 5.57/1.08  % (18504)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 5.57/1.08  % (18505)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 5.57/1.08  % (18505)Refutation not found, incomplete strategy% (18505)------------------------------
% 5.57/1.08  % (18505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.57/1.08  % (18505)Termination reason: Refutation not found, incomplete strategy
% 5.57/1.08  
% 5.57/1.08  % (18505)Memory used [KB]: 1663
% 5.57/1.08  % (18505)Time elapsed: 0.117 s
% 5.57/1.08  % (18505)------------------------------
% 5.57/1.08  % (18505)------------------------------
% 5.57/1.10  % (18506)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 5.57/1.13  % (18508)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 5.57/1.14  % (18507)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 6.11/1.15  % (18509)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 6.11/1.16  % (18510)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 6.43/1.23  % (18511)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 8.40/1.46  % (18508)Time limit reached!
% 8.40/1.46  % (18508)------------------------------
% 8.40/1.46  % (18508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.40/1.46  % (18508)Termination reason: Time limit
% 8.40/1.46  % (18508)Termination phase: Saturation
% 8.40/1.46  
% 8.40/1.46  % (18508)Memory used [KB]: 5245
% 8.40/1.46  % (18508)Time elapsed: 0.400 s
% 8.40/1.46  % (18508)------------------------------
% 8.40/1.46  % (18508)------------------------------
% 8.72/1.49  % (18504)Time limit reached!
% 8.72/1.49  % (18504)------------------------------
% 8.72/1.49  % (18504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.72/1.49  % (18504)Termination reason: Time limit
% 8.72/1.49  % (18504)Termination phase: Saturation
% 8.72/1.49  
% 8.72/1.49  % (18504)Memory used [KB]: 4605
% 8.72/1.49  % (18504)Time elapsed: 0.532 s
% 8.72/1.49  % (18504)------------------------------
% 8.72/1.49  % (18504)------------------------------
% 8.72/1.53  % (18511)Time limit reached!
% 8.72/1.53  % (18511)------------------------------
% 8.72/1.53  % (18511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.72/1.53  % (18511)Termination reason: Time limit
% 8.72/1.53  
% 8.72/1.53  % (18511)Memory used [KB]: 4093
% 8.72/1.53  % (18511)Time elapsed: 0.413 s
% 8.72/1.53  % (18511)------------------------------
% 8.72/1.53  % (18511)------------------------------
% 9.28/1.58  % (18512)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 9.28/1.62  % (18488)Time limit reached!
% 9.28/1.62  % (18488)------------------------------
% 9.28/1.62  % (18488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.28/1.62  % (18488)Termination reason: Time limit
% 9.28/1.62  
% 9.28/1.62  % (18488)Memory used [KB]: 16502
% 9.28/1.62  % (18488)Time elapsed: 1.217 s
% 9.28/1.62  % (18488)------------------------------
% 9.28/1.62  % (18488)------------------------------
% 9.28/1.63  % (18484)Time limit reached!
% 9.28/1.63  % (18484)------------------------------
% 9.28/1.63  % (18484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.28/1.63  % (18484)Termination reason: Time limit
% 9.28/1.63  
% 9.28/1.63  % (18484)Memory used [KB]: 14072
% 9.28/1.63  % (18484)Time elapsed: 1.217 s
% 9.28/1.63  % (18484)------------------------------
% 9.28/1.63  % (18484)------------------------------
% 10.01/1.66  % (18513)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 10.50/1.72  % (18486)Time limit reached!
% 10.50/1.72  % (18486)------------------------------
% 10.50/1.72  % (18486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.50/1.72  % (18486)Termination reason: Time limit
% 10.50/1.72  
% 10.50/1.72  % (18486)Memory used [KB]: 17270
% 10.50/1.72  % (18486)Time elapsed: 1.308 s
% 10.50/1.72  % (18486)------------------------------
% 10.50/1.72  % (18486)------------------------------
% 10.50/1.73  % (18514)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 11.09/1.78  % (18516)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 11.09/1.78  % (18515)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 11.29/1.80  % (18498)Time limit reached!
% 11.29/1.80  % (18498)------------------------------
% 11.29/1.80  % (18498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.29/1.80  % (18498)Termination reason: Time limit
% 11.29/1.80  
% 11.29/1.80  % (18498)Memory used [KB]: 12920
% 11.29/1.80  % (18498)Time elapsed: 1.210 s
% 11.29/1.80  % (18498)------------------------------
% 11.29/1.80  % (18498)------------------------------
% 11.40/1.90  % (18517)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 11.40/1.90  % (18517)Refutation not found, incomplete strategy% (18517)------------------------------
% 11.40/1.90  % (18517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.40/1.90  % (18517)Termination reason: Refutation not found, incomplete strategy
% 11.40/1.90  
% 11.40/1.90  % (18517)Memory used [KB]: 6140
% 11.40/1.90  % (18517)Time elapsed: 0.134 s
% 11.40/1.90  % (18517)------------------------------
% 11.40/1.90  % (18517)------------------------------
% 12.15/1.94  % (18489)Time limit reached!
% 12.15/1.94  % (18489)------------------------------
% 12.15/1.94  % (18489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.15/1.94  % (18489)Termination reason: Time limit
% 12.15/1.94  
% 12.15/1.94  % (18489)Memory used [KB]: 22259
% 12.15/1.94  % (18489)Time elapsed: 1.520 s
% 12.15/1.94  % (18489)------------------------------
% 12.15/1.94  % (18489)------------------------------
% 12.15/1.95  % (18506)Refutation found. Thanks to Tanya!
% 12.15/1.95  % SZS status Theorem for theBenchmark
% 12.15/1.95  % SZS output start Proof for theBenchmark
% 12.15/1.96  fof(f4870,plain,(
% 12.15/1.96    $false),
% 12.15/1.96    inference(avatar_sat_refutation,[],[f92,f96,f108,f112,f124,f145,f149,f153,f242,f279,f283,f594,f603,f620,f1067,f1072,f1141,f1145,f1159,f1173,f1355,f1712,f2046,f2099,f2103,f2152,f2262,f4835,f4853,f4860,f4869])).
% 12.15/1.96  fof(f4869,plain,(
% 12.15/1.96    ~spl5_5 | ~spl5_15 | ~spl5_34 | ~spl5_46 | ~spl5_57 | spl5_71 | ~spl5_74),
% 12.15/1.96    inference(avatar_contradiction_clause,[],[f4868])).
% 12.15/1.96  fof(f4868,plain,(
% 12.15/1.96    $false | (~spl5_5 | ~spl5_15 | ~spl5_34 | ~spl5_46 | ~spl5_57 | spl5_71 | ~spl5_74)),
% 12.15/1.96    inference(subsumption_resolution,[],[f4867,f278])).
% 12.15/1.96  fof(f278,plain,(
% 12.15/1.96    ( ! [X2,X0,X1] : (sP1(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) ) | ~spl5_15),
% 12.15/1.96    inference(avatar_component_clause,[],[f277])).
% 12.15/1.96  fof(f277,plain,(
% 12.15/1.96    spl5_15 <=> ! [X1,X0,X2] : sP1(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 12.15/1.96  fof(f4867,plain,(
% 12.15/1.96    ~sP1(sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | (~spl5_5 | ~spl5_34 | ~spl5_46 | ~spl5_57 | spl5_71 | ~spl5_74)),
% 12.15/1.96    inference(forward_demodulation,[],[f4866,f2102])).
% 12.15/1.96  fof(f2102,plain,(
% 12.15/1.96    ( ! [X6] : (k3_xboole_0(X6,X6) = X6) ) | ~spl5_46),
% 12.15/1.96    inference(avatar_component_clause,[],[f2101])).
% 12.15/1.96  fof(f2101,plain,(
% 12.15/1.96    spl5_46 <=> ! [X6] : k3_xboole_0(X6,X6) = X6),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 12.15/1.96  fof(f4866,plain,(
% 12.15/1.96    ~sP1(sK2,sK2,sK2,k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | (~spl5_5 | ~spl5_34 | ~spl5_46 | ~spl5_57 | spl5_71 | ~spl5_74)),
% 12.15/1.96    inference(forward_demodulation,[],[f4865,f1354])).
% 12.15/1.96  fof(f1354,plain,(
% 12.15/1.96    ( ! [X8,X9] : (k5_xboole_0(X8,k5_xboole_0(X9,X8)) = X9) ) | ~spl5_34),
% 12.15/1.96    inference(avatar_component_clause,[],[f1353])).
% 12.15/1.96  fof(f1353,plain,(
% 12.15/1.96    spl5_34 <=> ! [X9,X8] : k5_xboole_0(X8,k5_xboole_0(X9,X8)) = X9),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 12.15/1.96  fof(f4865,plain,(
% 12.15/1.96    ~sP1(sK2,sK2,sK2,k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) | (~spl5_5 | ~spl5_46 | ~spl5_57 | spl5_71 | ~spl5_74)),
% 12.15/1.96    inference(forward_demodulation,[],[f4862,f3372])).
% 12.15/1.96  fof(f3372,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) ) | (~spl5_5 | ~spl5_46 | ~spl5_57)),
% 12.15/1.96    inference(forward_demodulation,[],[f3319,f107])).
% 12.15/1.96  fof(f107,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl5_5),
% 12.15/1.96    inference(avatar_component_clause,[],[f106])).
% 12.15/1.96  fof(f106,plain,(
% 12.15/1.96    spl5_5 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 12.15/1.96  fof(f3319,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,X1),X0)) ) | (~spl5_46 | ~spl5_57)),
% 12.15/1.96    inference(superposition,[],[f2261,f2102])).
% 12.15/1.96  fof(f2261,plain,(
% 12.15/1.96    ( ! [X2,X0,X1] : (k3_xboole_0(k5_xboole_0(X2,X0),X1) = k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X1,X0))) ) | ~spl5_57),
% 12.15/1.96    inference(avatar_component_clause,[],[f2260])).
% 12.15/1.96  fof(f2260,plain,(
% 12.15/1.96    spl5_57 <=> ! [X1,X0,X2] : k3_xboole_0(k5_xboole_0(X2,X0),X1) = k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X1,X0))),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 12.15/1.96  fof(f4862,plain,(
% 12.15/1.96    ~sP1(sK2,sK2,sK2,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) | (spl5_71 | ~spl5_74)),
% 12.15/1.96    inference(superposition,[],[f4834,f4849])).
% 12.15/1.96  fof(f4849,plain,(
% 12.15/1.96    sK2 = sK3 | ~spl5_74),
% 12.15/1.96    inference(avatar_component_clause,[],[f4848])).
% 12.15/1.96  fof(f4848,plain,(
% 12.15/1.96    spl5_74 <=> sK2 = sK3),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).
% 12.15/1.96  fof(f4834,plain,(
% 12.15/1.96    ~sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) | spl5_71),
% 12.15/1.96    inference(avatar_component_clause,[],[f4833])).
% 12.15/1.96  fof(f4833,plain,(
% 12.15/1.96    spl5_71 <=> sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).
% 12.15/1.96  fof(f4860,plain,(
% 12.15/1.96    spl5_74 | ~spl5_15 | ~spl5_45 | spl5_75),
% 12.15/1.96    inference(avatar_split_clause,[],[f4855,f4851,f2097,f277,f4848])).
% 12.15/1.96  fof(f2097,plain,(
% 12.15/1.96    spl5_45 <=> ! [X1,X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1)),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 12.15/1.96  fof(f4851,plain,(
% 12.15/1.96    spl5_75 <=> sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).
% 12.15/1.96  fof(f4855,plain,(
% 12.15/1.96    sK2 = sK3 | (~spl5_15 | ~spl5_45 | spl5_75)),
% 12.15/1.96    inference(subsumption_resolution,[],[f4854,f278])).
% 12.15/1.96  fof(f4854,plain,(
% 12.15/1.96    ~sP1(sK2,sK2,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | sK2 = sK3 | (~spl5_45 | spl5_75)),
% 12.15/1.96    inference(superposition,[],[f4852,f2098])).
% 12.15/1.96  fof(f2098,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1) ) | ~spl5_45),
% 12.15/1.96    inference(avatar_component_clause,[],[f2097])).
% 12.15/1.96  fof(f4852,plain,(
% 12.15/1.96    ~sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) | spl5_75),
% 12.15/1.96    inference(avatar_component_clause,[],[f4851])).
% 12.15/1.96  fof(f4853,plain,(
% 12.15/1.96    spl5_74 | ~spl5_75 | ~spl5_5 | ~spl5_21 | ~spl5_43 | ~spl5_45 | spl5_71),
% 12.15/1.96    inference(avatar_split_clause,[],[f4846,f4833,f2097,f1710,f601,f106,f4851,f4848])).
% 12.15/1.96  fof(f601,plain,(
% 12.15/1.96    spl5_21 <=> ! [X1,X0,X2] : r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 12.15/1.96  fof(f1710,plain,(
% 12.15/1.96    spl5_43 <=> ! [X1,X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | ~r2_hidden(X0,X1))),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 12.15/1.96  fof(f4846,plain,(
% 12.15/1.96    ~sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) | sK2 = sK3 | (~spl5_5 | ~spl5_21 | ~spl5_43 | ~spl5_45 | spl5_71)),
% 12.15/1.96    inference(forward_demodulation,[],[f4845,f2036])).
% 12.15/1.96  fof(f2036,plain,(
% 12.15/1.96    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ) | (~spl5_21 | ~spl5_43)),
% 12.15/1.96    inference(unit_resulting_resolution,[],[f602,f1711])).
% 12.15/1.96  fof(f1711,plain,(
% 12.15/1.96    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ) | ~spl5_43),
% 12.15/1.96    inference(avatar_component_clause,[],[f1710])).
% 12.15/1.96  fof(f602,plain,(
% 12.15/1.96    ( ! [X2,X0,X1] : (r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))) ) | ~spl5_21),
% 12.15/1.96    inference(avatar_component_clause,[],[f601])).
% 12.15/1.96  fof(f4845,plain,(
% 12.15/1.96    ~sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) | sK2 = sK3 | (~spl5_5 | ~spl5_45 | spl5_71)),
% 12.15/1.96    inference(forward_demodulation,[],[f4844,f107])).
% 12.15/1.96  fof(f4844,plain,(
% 12.15/1.96    ~sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))) | sK2 = sK3 | (~spl5_45 | spl5_71)),
% 12.15/1.96    inference(superposition,[],[f4834,f2098])).
% 12.15/1.96  fof(f4835,plain,(
% 12.15/1.96    ~spl5_71 | ~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_29 | ~spl5_32 | ~spl5_46 | spl5_49),
% 12.15/1.96    inference(avatar_split_clause,[],[f2236,f2150,f2101,f1171,f1139,f151,f143,f110,f106,f4833])).
% 12.15/1.96  fof(f110,plain,(
% 12.15/1.96    spl5_6 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 12.15/1.96  fof(f143,plain,(
% 12.15/1.96    spl5_9 <=> ! [X1,X0,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 12.15/1.96  fof(f151,plain,(
% 12.15/1.96    spl5_11 <=> ! [X5,X7,X6] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 12.15/1.96  fof(f1139,plain,(
% 12.15/1.96    spl5_29 <=> ! [X1,X3,X0,X2] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 | ~sP1(X0,X1,X2,X3))),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 12.15/1.96  fof(f1171,plain,(
% 12.15/1.96    spl5_32 <=> ! [X1,X0] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 12.15/1.96  fof(f2150,plain,(
% 12.15/1.96    spl5_49 <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 12.15/1.96  fof(f2236,plain,(
% 12.15/1.96    ~sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) | (~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_29 | ~spl5_32 | ~spl5_46 | spl5_49)),
% 12.15/1.96    inference(forward_demodulation,[],[f2235,f111])).
% 12.15/1.96  fof(f111,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) ) | ~spl5_6),
% 12.15/1.96    inference(avatar_component_clause,[],[f110])).
% 12.15/1.96  fof(f2235,plain,(
% 12.15/1.96    ~sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) | (~spl5_5 | ~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_29 | ~spl5_32 | ~spl5_46 | spl5_49)),
% 12.15/1.96    inference(forward_demodulation,[],[f2234,f2109])).
% 12.15/1.96  fof(f2109,plain,(
% 12.15/1.96    ( ! [X4,X5] : (k5_xboole_0(X4,k3_xboole_0(X5,X4)) = k3_xboole_0(X4,k5_xboole_0(X4,X5))) ) | (~spl5_5 | ~spl5_9 | ~spl5_46)),
% 12.15/1.96    inference(forward_demodulation,[],[f2106,f107])).
% 12.15/1.96  fof(f2106,plain,(
% 12.15/1.96    ( ! [X4,X5] : (k5_xboole_0(X4,k3_xboole_0(X5,X4)) = k3_xboole_0(k5_xboole_0(X4,X5),X4)) ) | (~spl5_9 | ~spl5_46)),
% 12.15/1.96    inference(superposition,[],[f144,f2102])).
% 12.15/1.96  fof(f144,plain,(
% 12.15/1.96    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) ) | ~spl5_9),
% 12.15/1.96    inference(avatar_component_clause,[],[f143])).
% 12.15/1.96  fof(f2234,plain,(
% 12.15/1.96    ~sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) | (~spl5_6 | ~spl5_11 | ~spl5_29 | ~spl5_32 | spl5_49)),
% 12.15/1.96    inference(forward_demodulation,[],[f2233,f152])).
% 12.15/1.96  fof(f152,plain,(
% 12.15/1.96    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))) ) | ~spl5_11),
% 12.15/1.96    inference(avatar_component_clause,[],[f151])).
% 12.15/1.96  fof(f2233,plain,(
% 12.15/1.96    ~sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | (~spl5_6 | ~spl5_11 | ~spl5_29 | ~spl5_32 | spl5_49)),
% 12.15/1.96    inference(forward_demodulation,[],[f2232,f152])).
% 12.15/1.96  fof(f2232,plain,(
% 12.15/1.96    ~sP1(sK2,sK2,sK3,k5_xboole_0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) | (~spl5_6 | ~spl5_29 | ~spl5_32 | spl5_49)),
% 12.15/1.96    inference(forward_demodulation,[],[f2231,f111])).
% 12.15/1.96  fof(f2231,plain,(
% 12.15/1.96    ~sP1(sK2,sK2,sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) | (~spl5_29 | ~spl5_32 | spl5_49)),
% 12.15/1.96    inference(forward_demodulation,[],[f2161,f1172])).
% 12.15/1.96  fof(f1172,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) | ~spl5_32),
% 12.15/1.96    inference(avatar_component_clause,[],[f1171])).
% 12.15/1.96  fof(f2161,plain,(
% 12.15/1.96    ~sP1(sK2,sK2,sK3,k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) | (~spl5_29 | spl5_49)),
% 12.15/1.96    inference(unit_resulting_resolution,[],[f2151,f1140])).
% 12.15/1.96  fof(f1140,plain,(
% 12.15/1.96    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3) ) | ~spl5_29),
% 12.15/1.96    inference(avatar_component_clause,[],[f1139])).
% 12.15/1.96  fof(f2151,plain,(
% 12.15/1.96    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) | spl5_49),
% 12.15/1.96    inference(avatar_component_clause,[],[f2150])).
% 12.15/1.96  fof(f2262,plain,(
% 12.15/1.96    spl5_57 | ~spl5_5 | ~spl5_9),
% 12.15/1.96    inference(avatar_split_clause,[],[f290,f143,f106,f2260])).
% 12.15/1.96  fof(f290,plain,(
% 12.15/1.96    ( ! [X2,X0,X1] : (k3_xboole_0(k5_xboole_0(X2,X0),X1) = k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X1,X0))) ) | (~spl5_5 | ~spl5_9)),
% 12.15/1.96    inference(superposition,[],[f144,f107])).
% 12.15/1.96  fof(f2152,plain,(
% 12.15/1.96    ~spl5_49),
% 12.15/1.96    inference(avatar_split_clause,[],[f77,f2150])).
% 12.15/1.96  fof(f77,plain,(
% 12.15/1.96    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),
% 12.15/1.96    inference(definition_unfolding,[],[f40,f74,f74,f76,f76])).
% 12.15/1.96  fof(f76,plain,(
% 12.15/1.96    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 12.15/1.96    inference(definition_unfolding,[],[f42,f74])).
% 12.15/1.96  fof(f42,plain,(
% 12.15/1.96    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 12.15/1.96    inference(cnf_transformation,[],[f11])).
% 12.15/1.96  fof(f11,axiom,(
% 12.15/1.96    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 12.15/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 12.15/1.96  fof(f74,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 12.15/1.96    inference(definition_unfolding,[],[f48,f73])).
% 12.15/1.96  fof(f73,plain,(
% 12.15/1.96    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 12.15/1.96    inference(definition_unfolding,[],[f53,f72])).
% 12.15/1.96  fof(f72,plain,(
% 12.15/1.96    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 12.15/1.96    inference(definition_unfolding,[],[f56,f71])).
% 12.15/1.96  fof(f71,plain,(
% 12.15/1.96    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 12.15/1.96    inference(definition_unfolding,[],[f67,f70])).
% 12.15/1.96  fof(f70,plain,(
% 12.15/1.96    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 12.15/1.96    inference(definition_unfolding,[],[f68,f69])).
% 12.15/1.96  fof(f69,plain,(
% 12.15/1.96    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 12.15/1.96    inference(cnf_transformation,[],[f17])).
% 12.15/1.96  fof(f17,axiom,(
% 12.15/1.96    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 12.15/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 12.15/1.96  fof(f68,plain,(
% 12.15/1.96    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 12.15/1.96    inference(cnf_transformation,[],[f16])).
% 12.15/1.96  fof(f16,axiom,(
% 12.15/1.96    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 12.15/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 12.15/1.96  fof(f67,plain,(
% 12.15/1.96    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 12.15/1.96    inference(cnf_transformation,[],[f15])).
% 12.15/1.96  fof(f15,axiom,(
% 12.15/1.96    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 12.15/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 12.15/1.96  fof(f56,plain,(
% 12.15/1.96    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 12.15/1.96    inference(cnf_transformation,[],[f14])).
% 12.15/1.96  fof(f14,axiom,(
% 12.15/1.96    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 12.15/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 12.15/1.96  fof(f53,plain,(
% 12.15/1.96    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 12.15/1.96    inference(cnf_transformation,[],[f13])).
% 12.15/1.96  fof(f13,axiom,(
% 12.15/1.96    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 12.15/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 12.15/1.96  fof(f48,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 12.15/1.96    inference(cnf_transformation,[],[f12])).
% 12.15/1.96  fof(f12,axiom,(
% 12.15/1.96    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 12.15/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 12.15/1.96  fof(f40,plain,(
% 12.15/1.96    k2_tarski(sK2,sK3) != k3_tarski(k2_tarski(k1_tarski(sK2),k1_tarski(sK3)))),
% 12.15/1.96    inference(cnf_transformation,[],[f31])).
% 12.15/1.96  fof(f31,plain,(
% 12.15/1.96    k2_tarski(sK2,sK3) != k3_tarski(k2_tarski(k1_tarski(sK2),k1_tarski(sK3)))),
% 12.15/1.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f23,f30])).
% 12.15/1.96  fof(f30,plain,(
% 12.15/1.96    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK2,sK3) != k3_tarski(k2_tarski(k1_tarski(sK2),k1_tarski(sK3)))),
% 12.15/1.96    introduced(choice_axiom,[])).
% 12.15/1.96  fof(f23,plain,(
% 12.15/1.96    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 12.15/1.96    inference(ennf_transformation,[],[f22])).
% 12.15/1.96  fof(f22,negated_conjecture,(
% 12.15/1.96    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 12.15/1.96    inference(negated_conjecture,[],[f21])).
% 12.15/1.96  fof(f21,conjecture,(
% 12.15/1.96    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 12.15/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).
% 12.15/1.96  fof(f2103,plain,(
% 12.15/1.96    spl5_46 | ~spl5_31 | ~spl5_34 | ~spl5_44),
% 12.15/1.96    inference(avatar_split_clause,[],[f2078,f2044,f1353,f1157,f2101])).
% 12.15/1.96  fof(f1157,plain,(
% 12.15/1.96    spl5_31 <=> ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 12.15/1.96  fof(f2044,plain,(
% 12.15/1.96    spl5_44 <=> ! [X1,X0] : k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 12.15/1.96  fof(f2078,plain,(
% 12.15/1.96    ( ! [X6] : (k3_xboole_0(X6,X6) = X6) ) | (~spl5_31 | ~spl5_34 | ~spl5_44)),
% 12.15/1.96    inference(forward_demodulation,[],[f2050,f1354])).
% 12.15/1.96  fof(f2050,plain,(
% 12.15/1.96    ( ! [X6] : (k3_xboole_0(X6,k5_xboole_0(k1_xboole_0,k5_xboole_0(X6,k1_xboole_0))) = X6) ) | (~spl5_31 | ~spl5_44)),
% 12.15/1.96    inference(superposition,[],[f2045,f1158])).
% 12.15/1.96  fof(f1158,plain,(
% 12.15/1.96    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) ) | ~spl5_31),
% 12.15/1.96    inference(avatar_component_clause,[],[f1157])).
% 12.15/1.96  fof(f2045,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0) ) | ~spl5_44),
% 12.15/1.96    inference(avatar_component_clause,[],[f2044])).
% 12.15/1.96  fof(f2099,plain,(
% 12.15/1.96    spl5_45),
% 12.15/1.96    inference(avatar_split_clause,[],[f81,f2097])).
% 12.15/1.96  fof(f81,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1) )),
% 12.15/1.96    inference(definition_unfolding,[],[f51,f74,f76,f76])).
% 12.15/1.96  fof(f51,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 12.15/1.96    inference(cnf_transformation,[],[f24])).
% 12.15/1.96  fof(f24,plain,(
% 12.15/1.96    ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 12.15/1.96    inference(ennf_transformation,[],[f20])).
% 12.15/1.96  fof(f20,axiom,(
% 12.15/1.96    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 12.15/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 12.15/1.96  fof(f2046,plain,(
% 12.15/1.96    spl5_44 | ~spl5_6 | ~spl5_11 | ~spl5_20 | ~spl5_25 | ~spl5_32),
% 12.15/1.96    inference(avatar_split_clause,[],[f1351,f1171,f618,f592,f151,f110,f2044])).
% 12.15/1.96  fof(f592,plain,(
% 12.15/1.96    spl5_20 <=> ! [X7,X8,X6] : k5_xboole_0(X7,k5_xboole_0(X8,X6)) = k5_xboole_0(X7,k5_xboole_0(X6,X8))),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 12.15/1.96  fof(f618,plain,(
% 12.15/1.96    spl5_25 <=> ! [X1,X0] : k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 12.15/1.96  fof(f1351,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0) ) | (~spl5_6 | ~spl5_11 | ~spl5_20 | ~spl5_25 | ~spl5_32)),
% 12.15/1.96    inference(forward_demodulation,[],[f1350,f593])).
% 12.15/1.96  fof(f593,plain,(
% 12.15/1.96    ( ! [X6,X8,X7] : (k5_xboole_0(X7,k5_xboole_0(X8,X6)) = k5_xboole_0(X7,k5_xboole_0(X6,X8))) ) | ~spl5_20),
% 12.15/1.96    inference(avatar_component_clause,[],[f592])).
% 12.15/1.96  fof(f1350,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X0,X1),X0))) = X0) ) | (~spl5_6 | ~spl5_11 | ~spl5_25 | ~spl5_32)),
% 12.15/1.96    inference(forward_demodulation,[],[f1349,f152])).
% 12.15/1.96  fof(f1349,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) = X0) ) | (~spl5_6 | ~spl5_25 | ~spl5_32)),
% 12.15/1.96    inference(forward_demodulation,[],[f1324,f111])).
% 12.15/1.96  fof(f1324,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = X0) ) | (~spl5_25 | ~spl5_32)),
% 12.15/1.96    inference(superposition,[],[f619,f1172])).
% 12.15/1.96  fof(f619,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0) ) | ~spl5_25),
% 12.15/1.96    inference(avatar_component_clause,[],[f618])).
% 12.15/1.96  fof(f1712,plain,(
% 12.15/1.96    spl5_43),
% 12.15/1.96    inference(avatar_split_clause,[],[f82,f1710])).
% 12.15/1.96  fof(f82,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | ~r2_hidden(X0,X1)) )),
% 12.15/1.96    inference(definition_unfolding,[],[f52,f76,f76])).
% 12.15/1.96  fof(f52,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 12.15/1.96    inference(cnf_transformation,[],[f25])).
% 12.15/1.96  fof(f25,plain,(
% 12.15/1.96    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 12.15/1.96    inference(ennf_transformation,[],[f18])).
% 12.15/1.96  fof(f18,axiom,(
% 12.15/1.96    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 12.15/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 12.15/1.96  fof(f1355,plain,(
% 12.15/1.96    spl5_34 | ~spl5_1 | ~spl5_11 | ~spl5_28),
% 12.15/1.96    inference(avatar_split_clause,[],[f1125,f1070,f151,f90,f1353])).
% 12.15/1.96  fof(f90,plain,(
% 12.15/1.96    spl5_1 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 12.15/1.96  fof(f1070,plain,(
% 12.15/1.96    spl5_28 <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 12.15/1.96  fof(f1125,plain,(
% 12.15/1.96    ( ! [X8,X9] : (k5_xboole_0(X8,k5_xboole_0(X9,X8)) = X9) ) | (~spl5_1 | ~spl5_11 | ~spl5_28)),
% 12.15/1.96    inference(forward_demodulation,[],[f1091,f91])).
% 12.15/1.96  fof(f91,plain,(
% 12.15/1.96    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl5_1),
% 12.15/1.96    inference(avatar_component_clause,[],[f90])).
% 12.15/1.96  fof(f1091,plain,(
% 12.15/1.96    ( ! [X8,X9] : (k5_xboole_0(X9,k1_xboole_0) = k5_xboole_0(X8,k5_xboole_0(X9,X8))) ) | (~spl5_11 | ~spl5_28)),
% 12.15/1.96    inference(superposition,[],[f152,f1071])).
% 12.15/1.96  fof(f1071,plain,(
% 12.15/1.96    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl5_28),
% 12.15/1.96    inference(avatar_component_clause,[],[f1070])).
% 12.15/1.96  fof(f1173,plain,(
% 12.15/1.96    spl5_32),
% 12.15/1.96    inference(avatar_split_clause,[],[f80,f1171])).
% 12.15/1.96  fof(f80,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 12.15/1.96    inference(definition_unfolding,[],[f50,f75])).
% 12.15/1.96  fof(f75,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 12.15/1.96    inference(definition_unfolding,[],[f47,f74])).
% 12.15/1.96  fof(f47,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 12.15/1.96    inference(cnf_transformation,[],[f19])).
% 12.15/1.96  fof(f19,axiom,(
% 12.15/1.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 12.15/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 12.15/1.96  fof(f50,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 12.15/1.96    inference(cnf_transformation,[],[f9])).
% 12.15/1.96  fof(f9,axiom,(
% 12.15/1.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 12.15/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 12.15/1.96  fof(f1159,plain,(
% 12.15/1.96    spl5_31 | ~spl5_5 | ~spl5_30),
% 12.15/1.96    inference(avatar_split_clause,[],[f1146,f1143,f106,f1157])).
% 12.15/1.96  fof(f1143,plain,(
% 12.15/1.96    spl5_30 <=> ! [X22] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X22)),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 12.15/1.96  fof(f1146,plain,(
% 12.15/1.96    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) ) | (~spl5_5 | ~spl5_30)),
% 12.15/1.96    inference(superposition,[],[f1144,f107])).
% 12.15/1.96  fof(f1144,plain,(
% 12.15/1.96    ( ! [X22] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X22)) ) | ~spl5_30),
% 12.15/1.96    inference(avatar_component_clause,[],[f1143])).
% 12.15/1.96  fof(f1145,plain,(
% 12.15/1.96    spl5_30 | ~spl5_9 | ~spl5_28),
% 12.15/1.96    inference(avatar_split_clause,[],[f1119,f1070,f143,f1143])).
% 12.15/1.96  fof(f1119,plain,(
% 12.15/1.96    ( ! [X22] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X22)) ) | (~spl5_9 | ~spl5_28)),
% 12.15/1.96    inference(forward_demodulation,[],[f1082,f1071])).
% 12.15/1.96  fof(f1082,plain,(
% 12.15/1.96    ( ! [X21,X22] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X21,X21),X22)) ) | (~spl5_9 | ~spl5_28)),
% 12.15/1.96    inference(superposition,[],[f1071,f144])).
% 12.15/1.96  fof(f1141,plain,(
% 12.15/1.96    spl5_29),
% 12.15/1.96    inference(avatar_split_clause,[],[f83,f1139])).
% 12.15/1.96  fof(f83,plain,(
% 12.15/1.96    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 | ~sP1(X0,X1,X2,X3)) )),
% 12.15/1.96    inference(definition_unfolding,[],[f66,f73])).
% 12.15/1.96  fof(f66,plain,(
% 12.15/1.96    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | ~sP1(X0,X1,X2,X3)) )),
% 12.15/1.96    inference(cnf_transformation,[],[f39])).
% 12.15/1.96  fof(f39,plain,(
% 12.15/1.96    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP1(X0,X1,X2,X3)) & (sP1(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 12.15/1.96    inference(nnf_transformation,[],[f29])).
% 12.15/1.96  fof(f29,plain,(
% 12.15/1.96    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP1(X0,X1,X2,X3))),
% 12.15/1.96    inference(definition_folding,[],[f26,f28,f27])).
% 12.15/1.96  fof(f27,plain,(
% 12.15/1.96    ! [X4,X2,X1,X0] : (sP0(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 12.15/1.96    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 12.15/1.96  fof(f28,plain,(
% 12.15/1.96    ! [X0,X1,X2,X3] : (sP1(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP0(X4,X2,X1,X0)))),
% 12.15/1.96    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 12.15/1.96  fof(f26,plain,(
% 12.15/1.96    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 12.15/1.96    inference(ennf_transformation,[],[f10])).
% 12.15/1.96  fof(f10,axiom,(
% 12.15/1.96    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 12.15/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 12.15/1.96  fof(f1072,plain,(
% 12.15/1.96    spl5_28 | ~spl5_25 | ~spl5_27),
% 12.15/1.96    inference(avatar_split_clause,[],[f1068,f1065,f618,f1070])).
% 12.15/1.96  fof(f1065,plain,(
% 12.15/1.96    spl5_27 <=> ! [X1,X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 12.15/1.96  fof(f1068,plain,(
% 12.15/1.96    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | (~spl5_25 | ~spl5_27)),
% 12.15/1.96    inference(forward_demodulation,[],[f1066,f619])).
% 12.15/1.96  fof(f1066,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) ) | ~spl5_27),
% 12.15/1.96    inference(avatar_component_clause,[],[f1065])).
% 12.15/1.96  fof(f1067,plain,(
% 12.15/1.96    spl5_27),
% 12.15/1.96    inference(avatar_split_clause,[],[f78,f1065])).
% 12.15/1.96  fof(f78,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 12.15/1.96    inference(definition_unfolding,[],[f45,f49,f75])).
% 12.15/1.96  fof(f49,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 12.15/1.96    inference(cnf_transformation,[],[f3])).
% 12.15/1.96  fof(f3,axiom,(
% 12.15/1.96    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 12.15/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 12.15/1.96  fof(f45,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 12.15/1.96    inference(cnf_transformation,[],[f6])).
% 12.15/1.96  fof(f6,axiom,(
% 12.15/1.96    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 12.15/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 12.15/1.96  fof(f620,plain,(
% 12.15/1.96    spl5_25),
% 12.15/1.96    inference(avatar_split_clause,[],[f79,f618])).
% 12.15/1.96  fof(f79,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0) )),
% 12.15/1.96    inference(definition_unfolding,[],[f46,f75])).
% 12.15/1.96  fof(f46,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 12.15/1.96    inference(cnf_transformation,[],[f5])).
% 12.15/1.96  fof(f5,axiom,(
% 12.15/1.96    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 12.15/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 12.15/1.96  fof(f603,plain,(
% 12.15/1.96    spl5_21 | ~spl5_2 | ~spl5_13 | ~spl5_15),
% 12.15/1.96    inference(avatar_split_clause,[],[f595,f277,f240,f94,f601])).
% 12.15/1.96  fof(f94,plain,(
% 12.15/1.96    spl5_2 <=> ! [X1,X3,X2] : sP0(X1,X1,X2,X3)),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 12.15/1.96  fof(f240,plain,(
% 12.15/1.96    spl5_13 <=> ! [X1,X3,X5,X0,X2] : (r2_hidden(X5,X3) | ~sP0(X5,X2,X1,X0) | ~sP1(X0,X1,X2,X3))),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 12.15/1.96  fof(f595,plain,(
% 12.15/1.96    ( ! [X2,X0,X1] : (r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))) ) | (~spl5_2 | ~spl5_13 | ~spl5_15)),
% 12.15/1.96    inference(unit_resulting_resolution,[],[f95,f278,f241])).
% 12.15/1.96  fof(f241,plain,(
% 12.15/1.96    ( ! [X2,X0,X5,X3,X1] : (~sP1(X0,X1,X2,X3) | ~sP0(X5,X2,X1,X0) | r2_hidden(X5,X3)) ) | ~spl5_13),
% 12.15/1.96    inference(avatar_component_clause,[],[f240])).
% 12.15/1.96  fof(f95,plain,(
% 12.15/1.96    ( ! [X2,X3,X1] : (sP0(X1,X1,X2,X3)) ) | ~spl5_2),
% 12.15/1.96    inference(avatar_component_clause,[],[f94])).
% 12.15/1.96  fof(f594,plain,(
% 12.15/1.96    spl5_20 | ~spl5_11 | ~spl5_16),
% 12.15/1.96    inference(avatar_split_clause,[],[f318,f281,f151,f592])).
% 12.15/1.96  fof(f281,plain,(
% 12.15/1.96    spl5_16 <=> ! [X3,X5,X4] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 12.15/1.96  fof(f318,plain,(
% 12.15/1.96    ( ! [X6,X8,X7] : (k5_xboole_0(X7,k5_xboole_0(X8,X6)) = k5_xboole_0(X7,k5_xboole_0(X6,X8))) ) | (~spl5_11 | ~spl5_16)),
% 12.15/1.96    inference(superposition,[],[f282,f152])).
% 12.15/1.96  fof(f282,plain,(
% 12.15/1.96    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))) ) | ~spl5_16),
% 12.15/1.96    inference(avatar_component_clause,[],[f281])).
% 12.15/1.96  fof(f283,plain,(
% 12.15/1.96    spl5_16 | ~spl5_8 | ~spl5_10),
% 12.15/1.96    inference(avatar_split_clause,[],[f164,f147,f122,f281])).
% 12.15/1.96  fof(f122,plain,(
% 12.15/1.96    spl5_8 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 12.15/1.96  fof(f147,plain,(
% 12.15/1.96    spl5_10 <=> ! [X3,X2,X4] : k5_xboole_0(X2,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_xboole_0(X3,X2),X4)),
% 12.15/1.96    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 12.15/1.96  fof(f164,plain,(
% 12.15/1.96    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(X3,X5))) ) | (~spl5_8 | ~spl5_10)),
% 12.15/1.96    inference(superposition,[],[f148,f123])).
% 12.15/1.96  fof(f123,plain,(
% 12.15/1.96    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl5_8),
% 12.15/1.96    inference(avatar_component_clause,[],[f122])).
% 12.15/1.96  fof(f148,plain,(
% 12.15/1.96    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_xboole_0(X3,X2),X4)) ) | ~spl5_10),
% 12.15/1.96    inference(avatar_component_clause,[],[f147])).
% 12.15/1.96  fof(f279,plain,(
% 12.15/1.96    spl5_15),
% 12.15/1.96    inference(avatar_split_clause,[],[f88,f277])).
% 12.15/1.96  fof(f88,plain,(
% 12.15/1.96    ( ! [X2,X0,X1] : (sP1(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 12.15/1.96    inference(equality_resolution,[],[f84])).
% 12.15/1.96  fof(f84,plain,(
% 12.15/1.96    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 12.15/1.96    inference(definition_unfolding,[],[f65,f73])).
% 12.15/1.96  fof(f65,plain,(
% 12.15/1.96    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 12.15/1.96    inference(cnf_transformation,[],[f39])).
% 12.15/1.96  fof(f242,plain,(
% 12.15/1.96    spl5_13),
% 12.15/1.96    inference(avatar_split_clause,[],[f58,f240])).
% 12.15/1.96  fof(f58,plain,(
% 12.15/1.96    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | ~sP0(X5,X2,X1,X0) | ~sP1(X0,X1,X2,X3)) )),
% 12.15/1.96    inference(cnf_transformation,[],[f35])).
% 12.15/1.96  fof(f35,plain,(
% 12.15/1.96    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ((~sP0(sK4(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sP0(sK4(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X5,X2,X1,X0)) & (sP0(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 12.15/1.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 12.15/1.96  fof(f34,plain,(
% 12.15/1.96    ! [X3,X2,X1,X0] : (? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP0(sK4(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sP0(sK4(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 12.15/1.96    introduced(choice_axiom,[])).
% 12.15/1.96  fof(f33,plain,(
% 12.15/1.96    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X5,X2,X1,X0)) & (sP0(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 12.15/1.96    inference(rectify,[],[f32])).
% 12.15/1.96  fof(f32,plain,(
% 12.15/1.96    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP0(X4,X2,X1,X0)) & (sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP1(X0,X1,X2,X3)))),
% 12.15/1.96    inference(nnf_transformation,[],[f28])).
% 12.15/1.96  fof(f153,plain,(
% 12.15/1.96    spl5_11 | ~spl5_6 | ~spl5_8),
% 12.15/1.96    inference(avatar_split_clause,[],[f135,f122,f110,f151])).
% 12.15/1.96  fof(f135,plain,(
% 12.15/1.96    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))) ) | (~spl5_6 | ~spl5_8)),
% 12.15/1.96    inference(superposition,[],[f123,f111])).
% 12.15/1.96  fof(f149,plain,(
% 12.15/1.96    spl5_10 | ~spl5_6 | ~spl5_8),
% 12.15/1.96    inference(avatar_split_clause,[],[f130,f122,f110,f147])).
% 12.15/1.96  fof(f130,plain,(
% 12.15/1.96    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_xboole_0(X3,X2),X4)) ) | (~spl5_6 | ~spl5_8)),
% 12.15/1.96    inference(superposition,[],[f123,f111])).
% 12.15/1.96  fof(f145,plain,(
% 12.15/1.96    spl5_9),
% 12.15/1.96    inference(avatar_split_clause,[],[f55,f143])).
% 12.15/1.96  fof(f55,plain,(
% 12.15/1.96    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 12.15/1.96    inference(cnf_transformation,[],[f4])).
% 12.15/1.96  fof(f4,axiom,(
% 12.15/1.96    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 12.15/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 12.15/1.96  fof(f124,plain,(
% 12.15/1.96    spl5_8),
% 12.15/1.96    inference(avatar_split_clause,[],[f54,f122])).
% 12.15/1.96  fof(f54,plain,(
% 12.15/1.96    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 12.15/1.96    inference(cnf_transformation,[],[f8])).
% 12.15/1.96  fof(f8,axiom,(
% 12.15/1.96    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 12.15/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 12.15/1.96  fof(f112,plain,(
% 12.15/1.96    spl5_6),
% 12.15/1.96    inference(avatar_split_clause,[],[f44,f110])).
% 12.15/1.96  fof(f44,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 12.15/1.96    inference(cnf_transformation,[],[f2])).
% 12.15/1.96  fof(f2,axiom,(
% 12.15/1.96    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 12.15/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 12.15/1.96  fof(f108,plain,(
% 12.15/1.96    spl5_5),
% 12.15/1.96    inference(avatar_split_clause,[],[f43,f106])).
% 12.15/1.96  fof(f43,plain,(
% 12.15/1.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 12.15/1.96    inference(cnf_transformation,[],[f1])).
% 12.15/1.96  fof(f1,axiom,(
% 12.15/1.96    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 12.15/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 12.15/1.96  fof(f96,plain,(
% 12.15/1.96    spl5_2),
% 12.15/1.96    inference(avatar_split_clause,[],[f85,f94])).
% 12.15/1.96  fof(f85,plain,(
% 12.15/1.96    ( ! [X2,X3,X1] : (sP0(X1,X1,X2,X3)) )),
% 12.15/1.96    inference(equality_resolution,[],[f64])).
% 12.15/1.96  fof(f64,plain,(
% 12.15/1.96    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | X0 != X1) )),
% 12.15/1.96    inference(cnf_transformation,[],[f38])).
% 12.15/1.96  fof(f38,plain,(
% 12.15/1.96    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP0(X0,X1,X2,X3)))),
% 12.15/1.96    inference(rectify,[],[f37])).
% 12.15/1.96  fof(f37,plain,(
% 12.15/1.96    ! [X4,X2,X1,X0] : ((sP0(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP0(X4,X2,X1,X0)))),
% 12.15/1.96    inference(flattening,[],[f36])).
% 12.15/1.96  fof(f36,plain,(
% 12.15/1.96    ! [X4,X2,X1,X0] : ((sP0(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP0(X4,X2,X1,X0)))),
% 12.15/1.96    inference(nnf_transformation,[],[f27])).
% 12.15/1.96  fof(f92,plain,(
% 12.15/1.96    spl5_1),
% 12.15/1.96    inference(avatar_split_clause,[],[f41,f90])).
% 12.15/1.96  fof(f41,plain,(
% 12.15/1.96    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.15/1.96    inference(cnf_transformation,[],[f7])).
% 12.15/1.96  fof(f7,axiom,(
% 12.15/1.96    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 12.15/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 12.15/1.96  % SZS output end Proof for theBenchmark
% 12.15/1.96  % (18506)------------------------------
% 12.15/1.96  % (18506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.15/1.96  % (18506)Termination reason: Refutation
% 12.15/1.96  
% 12.15/1.96  % (18506)Memory used [KB]: 20980
% 12.15/1.96  % (18506)Time elapsed: 0.933 s
% 12.15/1.96  % (18506)------------------------------
% 12.15/1.96  % (18506)------------------------------
% 12.15/1.97  % (18461)Success in time 1.6 s
%------------------------------------------------------------------------------
