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
% DateTime   : Thu Dec  3 12:33:00 EST 2020

% Result     : Theorem 11.28s
% Output     : Refutation 11.28s
% Verified   : 
% Statistics : Number of formulae       :  281 ( 681 expanded)
%              Number of leaves         :   64 ( 332 expanded)
%              Depth                    :   12
%              Number of atoms          :  790 (1620 expanded)
%              Number of equality atoms :  188 ( 541 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23208,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f56,f60,f68,f75,f83,f89,f97,f103,f110,f121,f184,f194,f206,f232,f378,f402,f436,f497,f501,f552,f811,f926,f936,f1329,f1444,f1529,f1533,f1608,f1653,f1705,f1949,f2134,f2190,f2194,f2382,f2418,f2455,f2631,f3412,f5753,f6627,f6994,f8189,f8250,f13300,f14949,f17765,f22025,f22070,f22976])).

fof(f22976,plain,
    ( ~ spl3_11
    | ~ spl3_45
    | ~ spl3_57
    | ~ spl3_77
    | ~ spl3_123
    | ~ spl3_164
    | ~ spl3_212
    | ~ spl3_257
    | spl3_268 ),
    inference(avatar_contradiction_clause,[],[f22975])).

fof(f22975,plain,
    ( $false
    | ~ spl3_11
    | ~ spl3_45
    | ~ spl3_57
    | ~ spl3_77
    | ~ spl3_123
    | ~ spl3_164
    | ~ spl3_212
    | ~ spl3_257
    | spl3_268 ),
    inference(subsumption_resolution,[],[f22069,f22974])).

fof(f22974,plain,
    ( ! [X46] : k4_xboole_0(X46,sK2) = k5_xboole_0(k4_xboole_0(X46,sK1),k4_xboole_0(X46,k4_xboole_0(X46,k4_xboole_0(sK1,sK2))))
    | ~ spl3_11
    | ~ spl3_45
    | ~ spl3_57
    | ~ spl3_77
    | ~ spl3_123
    | ~ spl3_164
    | ~ spl3_212
    | ~ spl3_257 ),
    inference(forward_demodulation,[],[f22973,f500])).

fof(f500,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f499])).

fof(f499,plain,
    ( spl3_45
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f22973,plain,
    ( ! [X46] : k4_xboole_0(X46,sK2) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X46,sK1),k1_xboole_0),k4_xboole_0(X46,k4_xboole_0(X46,k4_xboole_0(sK1,sK2))))
    | ~ spl3_11
    | ~ spl3_45
    | ~ spl3_57
    | ~ spl3_77
    | ~ spl3_123
    | ~ spl3_164
    | ~ spl3_212
    | ~ spl3_257 ),
    inference(forward_demodulation,[],[f22796,f15816])).

fof(f15816,plain,
    ( ! [X14,X15,X13] : k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X15)) = k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X15,X14)))
    | ~ spl3_11
    | ~ spl3_45
    | ~ spl3_57
    | ~ spl3_77
    | ~ spl3_123
    | ~ spl3_212 ),
    inference(backward_demodulation,[],[f4102,f15815])).

fof(f15815,plain,
    ( ! [X10,X11,X9] : k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(k4_xboole_0(X10,X11),X9)) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X9,X11)))
    | ~ spl3_57
    | ~ spl3_77
    | ~ spl3_212 ),
    inference(forward_demodulation,[],[f15345,f1607])).

fof(f1607,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | ~ spl3_77 ),
    inference(avatar_component_clause,[],[f1606])).

fof(f1606,plain,
    ( spl3_77
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).

fof(f15345,plain,
    ( ! [X10,X11,X9] : k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(k4_xboole_0(X10,X11),X9)) = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),X11)
    | ~ spl3_57
    | ~ spl3_212 ),
    inference(superposition,[],[f13299,f925])).

fof(f925,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f924])).

fof(f924,plain,
    ( spl3_57
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f13299,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)
    | ~ spl3_212 ),
    inference(avatar_component_clause,[],[f13298])).

fof(f13298,plain,
    ( spl3_212
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_212])])).

fof(f4102,plain,
    ( ! [X14,X15,X13] : k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X15)) = k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),X15))
    | ~ spl3_11
    | ~ spl3_45
    | ~ spl3_77
    | ~ spl3_123 ),
    inference(forward_demodulation,[],[f4101,f1850])).

fof(f1850,plain,
    ( ! [X12,X10,X11] : k4_xboole_0(k4_xboole_0(X10,X11),X12) = k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X10,X12)))
    | ~ spl3_11
    | ~ spl3_45
    | ~ spl3_77 ),
    inference(forward_demodulation,[],[f1756,f500])).

fof(f1756,plain,
    ( ! [X12,X10,X11] : k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X10,X12))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),k1_xboole_0),X12)
    | ~ spl3_11
    | ~ spl3_77 ),
    inference(superposition,[],[f1607,f109])).

fof(f109,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl3_11
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f4101,plain,
    ( ! [X14,X15,X13] : k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,k4_xboole_0(X13,X15)))) = k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),X15))
    | ~ spl3_11
    | ~ spl3_45
    | ~ spl3_77
    | ~ spl3_123 ),
    inference(forward_demodulation,[],[f4100,f500])).

fof(f4100,plain,
    ( ! [X14,X15,X13] : k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,k4_xboole_0(X13,X15)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X13,X14),k1_xboole_0),k4_xboole_0(k4_xboole_0(X13,X14),X15))
    | ~ spl3_11
    | ~ spl3_45
    | ~ spl3_77
    | ~ spl3_123 ),
    inference(forward_demodulation,[],[f3945,f1850])).

fof(f3945,plain,
    ( ! [X14,X15,X13] : k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,k4_xboole_0(X13,X15)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X13,X14),k1_xboole_0),k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X15))))
    | ~ spl3_11
    | ~ spl3_123 ),
    inference(superposition,[],[f3411,f109])).

fof(f3411,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))
    | ~ spl3_123 ),
    inference(avatar_component_clause,[],[f3410])).

fof(f3410,plain,
    ( spl3_123
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_123])])).

fof(f22796,plain,
    ( ! [X46] : k4_xboole_0(X46,sK2) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X46,sK1),k1_xboole_0),k4_xboole_0(k4_xboole_0(X46,sK2),k4_xboole_0(X46,sK1)))
    | ~ spl3_164
    | ~ spl3_257 ),
    inference(superposition,[],[f22024,f8249])).

fof(f8249,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,sK1),k4_xboole_0(X3,sK2))
    | ~ spl3_164 ),
    inference(avatar_component_clause,[],[f8248])).

fof(f8248,plain,
    ( spl3_164
  <=> ! [X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,sK1),k4_xboole_0(X3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_164])])).

fof(f22024,plain,
    ( ! [X6,X7] : k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X6
    | ~ spl3_257 ),
    inference(avatar_component_clause,[],[f22023])).

fof(f22023,plain,
    ( spl3_257
  <=> ! [X7,X6] : k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_257])])).

fof(f22069,plain,
    ( k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))))
    | spl3_268 ),
    inference(avatar_component_clause,[],[f22067])).

fof(f22067,plain,
    ( spl3_268
  <=> k4_xboole_0(sK0,sK2) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_268])])).

fof(f22070,plain,
    ( ~ spl3_268
    | ~ spl3_11
    | ~ spl3_45
    | ~ spl3_57
    | ~ spl3_73
    | ~ spl3_77
    | spl3_101
    | ~ spl3_114
    | ~ spl3_123
    | ~ spl3_228 ),
    inference(avatar_split_clause,[],[f20968,f17763,f3410,f2629,f2452,f1606,f1527,f924,f499,f108,f22067])).

fof(f1527,plain,
    ( spl3_73
  <=> ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f2452,plain,
    ( spl3_101
  <=> k4_xboole_0(sK0,sK2) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_101])])).

fof(f2629,plain,
    ( spl3_114
  <=> ! [X7,X6] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_114])])).

fof(f17763,plain,
    ( spl3_228
  <=> ! [X22,X23,X24] : k4_xboole_0(X24,k4_xboole_0(X24,k4_xboole_0(X22,k4_xboole_0(X22,X23)))) = k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,k4_xboole_0(X22,X24)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_228])])).

fof(f20968,plain,
    ( k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))))
    | ~ spl3_11
    | ~ spl3_45
    | ~ spl3_57
    | ~ spl3_73
    | ~ spl3_77
    | spl3_101
    | ~ spl3_114
    | ~ spl3_123
    | ~ spl3_228 ),
    inference(backward_demodulation,[],[f2454,f20967])).

fof(f20967,plain,
    ( ! [X21,X22,X20] : k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(X21,X22))) = k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k4_xboole_0(X21,X22),k4_xboole_0(X20,X21))))
    | ~ spl3_11
    | ~ spl3_45
    | ~ spl3_57
    | ~ spl3_73
    | ~ spl3_77
    | ~ spl3_114
    | ~ spl3_123
    | ~ spl3_228 ),
    inference(forward_demodulation,[],[f20966,f1176])).

fof(f1176,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X4,X5)))
    | ~ spl3_11
    | ~ spl3_45
    | ~ spl3_57 ),
    inference(forward_demodulation,[],[f1060,f500])).

fof(f1060,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k4_xboole_0(k4_xboole_0(X4,X5),k1_xboole_0)
    | ~ spl3_11
    | ~ spl3_57 ),
    inference(superposition,[],[f925,f109])).

fof(f20966,plain,
    ( ! [X21,X22,X20] : k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(X21,X22))) = k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k4_xboole_0(X21,X22),k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(X20,X21))))))
    | ~ spl3_73
    | ~ spl3_77
    | ~ spl3_114
    | ~ spl3_123
    | ~ spl3_228 ),
    inference(forward_demodulation,[],[f20233,f2763])).

fof(f2763,plain,
    ( ! [X101,X102,X100] : k4_xboole_0(X100,k4_xboole_0(X100,k4_xboole_0(X101,X102))) = k4_xboole_0(k4_xboole_0(X100,k4_xboole_0(X100,X101)),k4_xboole_0(X100,k4_xboole_0(X100,k4_xboole_0(X101,k4_xboole_0(X101,X102)))))
    | ~ spl3_73
    | ~ spl3_77
    | ~ spl3_114 ),
    inference(forward_demodulation,[],[f2762,f1607])).

fof(f2762,plain,
    ( ! [X101,X102,X100] : k4_xboole_0(k4_xboole_0(X100,k4_xboole_0(X100,X101)),k4_xboole_0(k4_xboole_0(X100,k4_xboole_0(X100,X101)),k4_xboole_0(X101,X102))) = k4_xboole_0(X100,k4_xboole_0(X100,k4_xboole_0(X101,X102)))
    | ~ spl3_73
    | ~ spl3_77
    | ~ spl3_114 ),
    inference(forward_demodulation,[],[f2761,f1528])).

fof(f1528,plain,
    ( ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2
    | ~ spl3_73 ),
    inference(avatar_component_clause,[],[f1527])).

fof(f2761,plain,
    ( ! [X101,X102,X100] : k4_xboole_0(k4_xboole_0(X100,k4_xboole_0(X100,X101)),k4_xboole_0(k4_xboole_0(X100,k4_xboole_0(X100,X101)),k4_xboole_0(X101,X102))) = k4_xboole_0(X100,k4_xboole_0(X100,k4_xboole_0(k4_xboole_0(X101,k1_xboole_0),X102)))
    | ~ spl3_77
    | ~ spl3_114 ),
    inference(forward_demodulation,[],[f2760,f1607])).

fof(f2760,plain,
    ( ! [X101,X102,X100] : k4_xboole_0(k4_xboole_0(X100,k4_xboole_0(X100,X101)),k4_xboole_0(k4_xboole_0(X100,k4_xboole_0(X100,X101)),k4_xboole_0(X101,X102))) = k4_xboole_0(k4_xboole_0(X100,k4_xboole_0(X100,k4_xboole_0(X101,k1_xboole_0))),X102)
    | ~ spl3_77
    | ~ spl3_114 ),
    inference(forward_demodulation,[],[f2708,f1607])).

fof(f2708,plain,
    ( ! [X101,X102,X100] : k4_xboole_0(k4_xboole_0(X100,k4_xboole_0(X100,X101)),k4_xboole_0(k4_xboole_0(X100,k4_xboole_0(X100,X101)),k4_xboole_0(X101,X102))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X100,k4_xboole_0(X100,X101)),k1_xboole_0),X102)
    | ~ spl3_77
    | ~ spl3_114 ),
    inference(superposition,[],[f1607,f2630])).

fof(f2630,plain,
    ( ! [X6,X7] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6)
    | ~ spl3_114 ),
    inference(avatar_component_clause,[],[f2629])).

fof(f20233,plain,
    ( ! [X21,X22,X20] : k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k4_xboole_0(X21,X22),k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(X20,X21)))))) = k4_xboole_0(k4_xboole_0(X20,k4_xboole_0(X20,X21)),k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(X21,k4_xboole_0(X21,X22)))))
    | ~ spl3_123
    | ~ spl3_228 ),
    inference(superposition,[],[f17764,f3411])).

fof(f17764,plain,
    ( ! [X24,X23,X22] : k4_xboole_0(X24,k4_xboole_0(X24,k4_xboole_0(X22,k4_xboole_0(X22,X23)))) = k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,k4_xboole_0(X22,X24))))
    | ~ spl3_228 ),
    inference(avatar_component_clause,[],[f17763])).

fof(f2454,plain,
    ( k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1)))))
    | spl3_101 ),
    inference(avatar_component_clause,[],[f2452])).

fof(f22025,plain,
    ( spl3_257
    | ~ spl3_100
    | ~ spl3_139 ),
    inference(avatar_split_clause,[],[f6345,f5751,f2416,f22023])).

fof(f2416,plain,
    ( spl3_100
  <=> ! [X5,X4] : k5_xboole_0(X5,k5_xboole_0(X4,X5)) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_100])])).

fof(f5751,plain,
    ( spl3_139
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_139])])).

fof(f6345,plain,
    ( ! [X6,X7] : k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X6
    | ~ spl3_100
    | ~ spl3_139 ),
    inference(superposition,[],[f2417,f5752])).

fof(f5752,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl3_139 ),
    inference(avatar_component_clause,[],[f5751])).

fof(f2417,plain,
    ( ! [X4,X5] : k5_xboole_0(X5,k5_xboole_0(X4,X5)) = X4
    | ~ spl3_100 ),
    inference(avatar_component_clause,[],[f2416])).

fof(f17765,plain,
    ( spl3_228
    | ~ spl3_56
    | ~ spl3_57
    | ~ spl3_77
    | ~ spl3_212
    | ~ spl3_214 ),
    inference(avatar_split_clause,[],[f16131,f14947,f13298,f1606,f924,f809,f17763])).

fof(f809,plain,
    ( spl3_56
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f14947,plain,
    ( spl3_214
  <=> ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_214])])).

fof(f16131,plain,
    ( ! [X24,X23,X22] : k4_xboole_0(X24,k4_xboole_0(X24,k4_xboole_0(X22,k4_xboole_0(X22,X23)))) = k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,k4_xboole_0(X22,X24))))
    | ~ spl3_56
    | ~ spl3_57
    | ~ spl3_77
    | ~ spl3_212
    | ~ spl3_214 ),
    inference(backward_demodulation,[],[f1884,f16128])).

fof(f16128,plain,
    ( ! [X215,X213,X214] : k4_xboole_0(X213,k4_xboole_0(X214,X215)) = k4_xboole_0(X213,k4_xboole_0(X214,k4_xboole_0(X214,k4_xboole_0(X213,X215))))
    | ~ spl3_56
    | ~ spl3_77
    | ~ spl3_212
    | ~ spl3_214 ),
    inference(forward_demodulation,[],[f16127,f16061])).

fof(f16061,plain,
    ( ! [X28,X26,X27] : k4_xboole_0(X26,k4_xboole_0(X27,X28)) = k5_xboole_0(X26,k4_xboole_0(X27,k4_xboole_0(X27,k4_xboole_0(X26,X28))))
    | ~ spl3_56
    | ~ spl3_77
    | ~ spl3_212 ),
    inference(forward_demodulation,[],[f15425,f1607])).

fof(f15425,plain,
    ( ! [X28,X26,X27] : k4_xboole_0(X26,k4_xboole_0(X27,X28)) = k5_xboole_0(X26,k4_xboole_0(k4_xboole_0(X27,k4_xboole_0(X27,X26)),X28))
    | ~ spl3_56
    | ~ spl3_212 ),
    inference(superposition,[],[f810,f13299])).

fof(f810,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f809])).

fof(f16127,plain,
    ( ! [X215,X213,X214] : k4_xboole_0(X213,k4_xboole_0(X214,k4_xboole_0(X214,k4_xboole_0(X213,X215)))) = k5_xboole_0(X213,k4_xboole_0(X214,k4_xboole_0(X214,k4_xboole_0(X213,X215))))
    | ~ spl3_77
    | ~ spl3_212
    | ~ spl3_214 ),
    inference(forward_demodulation,[],[f15476,f1607])).

fof(f15476,plain,
    ( ! [X215,X213,X214] : k4_xboole_0(X213,k4_xboole_0(k4_xboole_0(X214,k4_xboole_0(X214,X213)),X215)) = k5_xboole_0(X213,k4_xboole_0(k4_xboole_0(X214,k4_xboole_0(X214,X213)),X215))
    | ~ spl3_212
    | ~ spl3_214 ),
    inference(superposition,[],[f14948,f13299])).

fof(f14948,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ spl3_214 ),
    inference(avatar_component_clause,[],[f14947])).

fof(f1884,plain,
    ( ! [X24,X23,X22] : k4_xboole_0(X24,k4_xboole_0(X24,k4_xboole_0(X22,k4_xboole_0(X22,X23)))) = k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,X24))))))
    | ~ spl3_57
    | ~ spl3_77 ),
    inference(forward_demodulation,[],[f1788,f1607])).

fof(f1788,plain,
    ( ! [X24,X23,X22] : k4_xboole_0(X24,k4_xboole_0(X24,k4_xboole_0(X22,k4_xboole_0(X22,X23)))) = k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X23)),X24))))
    | ~ spl3_57
    | ~ spl3_77 ),
    inference(superposition,[],[f1607,f925])).

fof(f14949,plain,
    ( spl3_214
    | ~ spl3_2
    | ~ spl3_56
    | ~ spl3_74
    | ~ spl3_95 ),
    inference(avatar_split_clause,[],[f2333,f2192,f1531,f809,f54,f14947])).

fof(f54,plain,
    ( spl3_2
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1531,plain,
    ( spl3_74
  <=> ! [X18] : k1_xboole_0 = k5_xboole_0(X18,X18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).

fof(f2192,plain,
    ( spl3_95
  <=> ! [X1,X0] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_95])])).

fof(f2333,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ spl3_2
    | ~ spl3_56
    | ~ spl3_74
    | ~ spl3_95 ),
    inference(forward_demodulation,[],[f2292,f2321])).

fof(f2321,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl3_2
    | ~ spl3_74
    | ~ spl3_95 ),
    inference(forward_demodulation,[],[f2291,f55])).

fof(f55,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f2291,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)
    | ~ spl3_74
    | ~ spl3_95 ),
    inference(superposition,[],[f2193,f1532])).

fof(f1532,plain,
    ( ! [X18] : k1_xboole_0 = k5_xboole_0(X18,X18)
    | ~ spl3_74 ),
    inference(avatar_component_clause,[],[f1531])).

fof(f2193,plain,
    ( ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))
    | ~ spl3_95 ),
    inference(avatar_component_clause,[],[f2192])).

fof(f2292,plain,
    ( ! [X2,X1] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ spl3_56
    | ~ spl3_95 ),
    inference(superposition,[],[f2193,f810])).

fof(f13300,plain,
    ( spl3_212
    | ~ spl3_57
    | ~ spl3_77 ),
    inference(avatar_split_clause,[],[f1774,f1606,f924,f13298])).

fof(f1774,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)
    | ~ spl3_57
    | ~ spl3_77 ),
    inference(superposition,[],[f1607,f925])).

fof(f8250,plain,
    ( spl3_164
    | ~ spl3_23
    | ~ spl3_45
    | ~ spl3_47
    | ~ spl3_163 ),
    inference(avatar_split_clause,[],[f8218,f8187,f550,f499,f204,f8248])).

fof(f204,plain,
    ( spl3_23
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f550,plain,
    ( spl3_47
  <=> ! [X13,X14] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X14)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f8187,plain,
    ( spl3_163
  <=> ! [X43] : r1_tarski(k4_xboole_0(k4_xboole_0(X43,sK1),k4_xboole_0(X43,sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_163])])).

fof(f8218,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,sK1),k4_xboole_0(X3,sK2))
    | ~ spl3_23
    | ~ spl3_45
    | ~ spl3_47
    | ~ spl3_163 ),
    inference(forward_demodulation,[],[f8217,f551])).

fof(f551,plain,
    ( ! [X14,X13] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X14))
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f550])).

fof(f8217,plain,
    ( ! [X3] : k4_xboole_0(k4_xboole_0(X3,sK1),k4_xboole_0(X3,sK2)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,sK1),k4_xboole_0(X3,sK2)),k4_xboole_0(k4_xboole_0(X3,sK1),k4_xboole_0(X3,sK2)))
    | ~ spl3_23
    | ~ spl3_45
    | ~ spl3_163 ),
    inference(forward_demodulation,[],[f8191,f500])).

fof(f8191,plain,
    ( ! [X3] : k4_xboole_0(k4_xboole_0(X3,sK1),k4_xboole_0(X3,sK2)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,sK1),k4_xboole_0(X3,sK2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,sK1),k4_xboole_0(X3,sK2)),k1_xboole_0))
    | ~ spl3_23
    | ~ spl3_163 ),
    inference(resolution,[],[f8188,f205])).

fof(f205,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f204])).

fof(f8188,plain,
    ( ! [X43] : r1_tarski(k4_xboole_0(k4_xboole_0(X43,sK1),k4_xboole_0(X43,sK2)),k1_xboole_0)
    | ~ spl3_163 ),
    inference(avatar_component_clause,[],[f8187])).

fof(f8189,plain,
    ( spl3_163
    | ~ spl3_11
    | ~ spl3_45
    | ~ spl3_72
    | ~ spl3_77
    | ~ spl3_93
    | ~ spl3_123
    | ~ spl3_159 ),
    inference(avatar_split_clause,[],[f8173,f6992,f3410,f2132,f1606,f1442,f499,f108,f8187])).

fof(f1442,plain,
    ( spl3_72
  <=> ! [X23] : k1_xboole_0 = k4_xboole_0(X23,X23) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f2132,plain,
    ( spl3_93
  <=> ! [X34] : sK2 = k4_xboole_0(sK2,k4_xboole_0(X34,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).

fof(f6992,plain,
    ( spl3_159
  <=> ! [X55,X56] : r1_tarski(k4_xboole_0(X55,k4_xboole_0(X55,X56)),k4_xboole_0(X56,k4_xboole_0(X56,X55))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_159])])).

fof(f8173,plain,
    ( ! [X43] : r1_tarski(k4_xboole_0(k4_xboole_0(X43,sK1),k4_xboole_0(X43,sK2)),k1_xboole_0)
    | ~ spl3_11
    | ~ spl3_45
    | ~ spl3_72
    | ~ spl3_77
    | ~ spl3_93
    | ~ spl3_123
    | ~ spl3_159 ),
    inference(forward_demodulation,[],[f8172,f4102])).

fof(f8172,plain,
    ( ! [X43] : r1_tarski(k4_xboole_0(k4_xboole_0(X43,sK1),k4_xboole_0(k4_xboole_0(X43,sK1),sK2)),k1_xboole_0)
    | ~ spl3_72
    | ~ spl3_93
    | ~ spl3_159 ),
    inference(forward_demodulation,[],[f8016,f1443])).

fof(f1443,plain,
    ( ! [X23] : k1_xboole_0 = k4_xboole_0(X23,X23)
    | ~ spl3_72 ),
    inference(avatar_component_clause,[],[f1442])).

fof(f8016,plain,
    ( ! [X43] : r1_tarski(k4_xboole_0(k4_xboole_0(X43,sK1),k4_xboole_0(k4_xboole_0(X43,sK1),sK2)),k4_xboole_0(sK2,sK2))
    | ~ spl3_93
    | ~ spl3_159 ),
    inference(superposition,[],[f6993,f2133])).

fof(f2133,plain,
    ( ! [X34] : sK2 = k4_xboole_0(sK2,k4_xboole_0(X34,sK1))
    | ~ spl3_93 ),
    inference(avatar_component_clause,[],[f2132])).

fof(f6993,plain,
    ( ! [X56,X55] : r1_tarski(k4_xboole_0(X55,k4_xboole_0(X55,X56)),k4_xboole_0(X56,k4_xboole_0(X56,X55)))
    | ~ spl3_159 ),
    inference(avatar_component_clause,[],[f6992])).

fof(f6994,plain,
    ( spl3_159
    | ~ spl3_89
    | ~ spl3_147 ),
    inference(avatar_split_clause,[],[f6696,f6625,f1703,f6992])).

fof(f1703,plain,
    ( spl3_89
  <=> ! [X3,X2] : r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_89])])).

fof(f6625,plain,
    ( spl3_147
  <=> ! [X15,X14] : k4_xboole_0(X15,X14) = k4_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,X15))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_147])])).

fof(f6696,plain,
    ( ! [X56,X55] : r1_tarski(k4_xboole_0(X55,k4_xboole_0(X55,X56)),k4_xboole_0(X56,k4_xboole_0(X56,X55)))
    | ~ spl3_89
    | ~ spl3_147 ),
    inference(superposition,[],[f1704,f6626])).

fof(f6626,plain,
    ( ! [X14,X15] : k4_xboole_0(X15,X14) = k4_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,X15)))
    | ~ spl3_147 ),
    inference(avatar_component_clause,[],[f6625])).

fof(f1704,plain,
    ( ! [X2,X3] : r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)
    | ~ spl3_89 ),
    inference(avatar_component_clause,[],[f1703])).

fof(f6627,plain,
    ( spl3_147
    | ~ spl3_73
    | ~ spl3_77
    | ~ spl3_114
    | ~ spl3_139 ),
    inference(avatar_split_clause,[],[f6363,f5751,f2629,f1606,f1527,f6625])).

fof(f6363,plain,
    ( ! [X14,X15] : k4_xboole_0(X15,X14) = k4_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,X15)))
    | ~ spl3_73
    | ~ spl3_77
    | ~ spl3_114
    | ~ spl3_139 ),
    inference(forward_demodulation,[],[f6362,f5752])).

fof(f6362,plain,
    ( ! [X14,X15] : k4_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k5_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,X15)))
    | ~ spl3_73
    | ~ spl3_77
    | ~ spl3_114
    | ~ spl3_139 ),
    inference(forward_demodulation,[],[f6361,f1528])).

fof(f6361,plain,
    ( ! [X14,X15] : k4_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k5_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,k1_xboole_0))))
    | ~ spl3_77
    | ~ spl3_114
    | ~ spl3_139 ),
    inference(forward_demodulation,[],[f6311,f1607])).

fof(f6311,plain,
    ( ! [X14,X15] : k4_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k5_xboole_0(X15,k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X15)),k1_xboole_0))
    | ~ spl3_114
    | ~ spl3_139 ),
    inference(superposition,[],[f5752,f2630])).

fof(f5753,plain,
    ( spl3_139
    | ~ spl3_56
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f1084,f924,f809,f5751])).

fof(f1084,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl3_56
    | ~ spl3_57 ),
    inference(superposition,[],[f810,f925])).

fof(f3412,plain,(
    spl3_123 ),
    inference(avatar_split_clause,[],[f47,f3410])).

fof(f47,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    inference(forward_demodulation,[],[f45,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f36,f31,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f37,f31,f31,f31,f31])).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f2631,plain,
    ( spl3_114
    | ~ spl3_11
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f1087,f924,f108,f2629])).

fof(f1087,plain,
    ( ! [X6,X7] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6)
    | ~ spl3_11
    | ~ spl3_57 ),
    inference(superposition,[],[f109,f925])).

fof(f2455,plain,(
    ~ spl3_101 ),
    inference(avatar_split_clause,[],[f46,f2452])).

fof(f46,plain,(
    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1))))) ),
    inference(backward_demodulation,[],[f40,f44])).

fof(f40,plain,(
    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f24,f29,f31])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f24,plain,(
    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    & r1_tarski(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
        & r1_tarski(X2,X1) )
   => ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).

fof(f2418,plain,
    ( spl3_100
    | ~ spl3_2
    | ~ spl3_94
    | ~ spl3_99 ),
    inference(avatar_split_clause,[],[f2406,f2380,f2188,f54,f2416])).

fof(f2188,plain,
    ( spl3_94
  <=> ! [X5,X4] : k1_xboole_0 = k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,X5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_94])])).

fof(f2380,plain,
    ( spl3_99
  <=> ! [X1,X2] : k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_99])])).

fof(f2406,plain,
    ( ! [X4,X5] : k5_xboole_0(X5,k5_xboole_0(X4,X5)) = X4
    | ~ spl3_2
    | ~ spl3_94
    | ~ spl3_99 ),
    inference(forward_demodulation,[],[f2386,f55])).

fof(f2386,plain,
    ( ! [X4,X5] : k5_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X5,k5_xboole_0(X4,X5))
    | ~ spl3_94
    | ~ spl3_99 ),
    inference(superposition,[],[f2381,f2189])).

fof(f2189,plain,
    ( ! [X4,X5] : k1_xboole_0 = k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,X5)))
    | ~ spl3_94 ),
    inference(avatar_component_clause,[],[f2188])).

fof(f2381,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2
    | ~ spl3_99 ),
    inference(avatar_component_clause,[],[f2380])).

fof(f2382,plain,
    ( spl3_99
    | ~ spl3_2
    | ~ spl3_44
    | ~ spl3_74
    | ~ spl3_82
    | ~ spl3_95 ),
    inference(avatar_split_clause,[],[f2331,f2192,f1651,f1531,f495,f54,f2380])).

fof(f495,plain,
    ( spl3_44
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f1651,plain,
    ( spl3_82
  <=> ! [X1] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).

fof(f2331,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2
    | ~ spl3_2
    | ~ spl3_44
    | ~ spl3_74
    | ~ spl3_82
    | ~ spl3_95 ),
    inference(forward_demodulation,[],[f2325,f2321])).

fof(f2325,plain,
    ( ! [X2,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(X1,k5_xboole_0(X1,X2))
    | ~ spl3_2
    | ~ spl3_44
    | ~ spl3_74
    | ~ spl3_82
    | ~ spl3_95 ),
    inference(backward_demodulation,[],[f1665,f2321])).

fof(f1665,plain,
    ( ! [X2,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2))
    | ~ spl3_44
    | ~ spl3_82 ),
    inference(superposition,[],[f496,f1652])).

fof(f1652,plain,
    ( ! [X1] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1)
    | ~ spl3_82 ),
    inference(avatar_component_clause,[],[f1651])).

fof(f496,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f495])).

fof(f2194,plain,
    ( spl3_95
    | ~ spl3_44
    | ~ spl3_74 ),
    inference(avatar_split_clause,[],[f1590,f1531,f495,f2192])).

fof(f1590,plain,
    ( ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))
    | ~ spl3_44
    | ~ spl3_74 ),
    inference(superposition,[],[f496,f1532])).

fof(f2190,plain,
    ( spl3_94
    | ~ spl3_44
    | ~ spl3_74 ),
    inference(avatar_split_clause,[],[f1589,f1531,f495,f2188])).

fof(f1589,plain,
    ( ! [X4,X5] : k1_xboole_0 = k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,X5)))
    | ~ spl3_44
    | ~ spl3_74 ),
    inference(superposition,[],[f1532,f496])).

fof(f2134,plain,
    ( spl3_93
    | ~ spl3_2
    | ~ spl3_56
    | ~ spl3_92 ),
    inference(avatar_split_clause,[],[f2120,f1947,f809,f54,f2132])).

fof(f1947,plain,
    ( spl3_92
  <=> ! [X12] : k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X12,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).

fof(f2120,plain,
    ( ! [X34] : sK2 = k4_xboole_0(sK2,k4_xboole_0(X34,sK1))
    | ~ spl3_2
    | ~ spl3_56
    | ~ spl3_92 ),
    inference(forward_demodulation,[],[f2071,f55])).

fof(f2071,plain,
    ( ! [X34] : k5_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k4_xboole_0(X34,sK1))
    | ~ spl3_56
    | ~ spl3_92 ),
    inference(superposition,[],[f810,f1948])).

fof(f1948,plain,
    ( ! [X12] : k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X12,sK1)))
    | ~ spl3_92 ),
    inference(avatar_component_clause,[],[f1947])).

fof(f1949,plain,
    ( spl3_92
    | ~ spl3_26
    | ~ spl3_77 ),
    inference(avatar_split_clause,[],[f1784,f1606,f230,f1947])).

fof(f230,plain,
    ( spl3_26
  <=> ! [X4] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,X4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f1784,plain,
    ( ! [X12] : k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X12,sK1)))
    | ~ spl3_26
    | ~ spl3_77 ),
    inference(superposition,[],[f1607,f231])).

fof(f231,plain,
    ( ! [X4] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,X4),sK1)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f230])).

fof(f1705,plain,
    ( spl3_89
    | ~ spl3_3
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f1085,f924,f58,f1703])).

fof(f58,plain,
    ( spl3_3
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1085,plain,
    ( ! [X2,X3] : r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)
    | ~ spl3_3
    | ~ spl3_57 ),
    inference(superposition,[],[f59,f925])).

fof(f59,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f1653,plain,
    ( spl3_82
    | ~ spl3_58
    | ~ spl3_74 ),
    inference(avatar_split_clause,[],[f1588,f1531,f934,f1651])).

fof(f934,plain,
    ( spl3_58
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f1588,plain,
    ( ! [X1] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1)
    | ~ spl3_58
    | ~ spl3_74 ),
    inference(superposition,[],[f1532,f935])).

fof(f935,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f934])).

fof(f1608,plain,(
    spl3_77 ),
    inference(avatar_split_clause,[],[f44,f1606])).

fof(f1533,plain,
    ( spl3_74
    | ~ spl3_2
    | ~ spl3_56
    | ~ spl3_70 ),
    inference(avatar_split_clause,[],[f1393,f1327,f809,f54,f1531])).

fof(f1327,plain,
    ( spl3_70
  <=> ! [X23] : k1_xboole_0 = k4_xboole_0(X23,k4_xboole_0(X23,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f1393,plain,
    ( ! [X18] : k1_xboole_0 = k5_xboole_0(X18,X18)
    | ~ spl3_2
    | ~ spl3_56
    | ~ spl3_70 ),
    inference(forward_demodulation,[],[f1352,f1385])).

fof(f1385,plain,
    ( ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2
    | ~ spl3_2
    | ~ spl3_56
    | ~ spl3_70 ),
    inference(forward_demodulation,[],[f1340,f55])).

fof(f1340,plain,
    ( ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0)
    | ~ spl3_56
    | ~ spl3_70 ),
    inference(superposition,[],[f810,f1328])).

fof(f1328,plain,
    ( ! [X23] : k1_xboole_0 = k4_xboole_0(X23,k4_xboole_0(X23,k1_xboole_0))
    | ~ spl3_70 ),
    inference(avatar_component_clause,[],[f1327])).

fof(f1352,plain,
    ( ! [X18] : k1_xboole_0 = k5_xboole_0(X18,k4_xboole_0(X18,k1_xboole_0))
    | ~ spl3_56
    | ~ spl3_70 ),
    inference(superposition,[],[f810,f1328])).

fof(f1529,plain,
    ( spl3_73
    | ~ spl3_2
    | ~ spl3_56
    | ~ spl3_70 ),
    inference(avatar_split_clause,[],[f1385,f1327,f809,f54,f1527])).

fof(f1444,plain,
    ( spl3_72
    | ~ spl3_2
    | ~ spl3_56
    | ~ spl3_70 ),
    inference(avatar_split_clause,[],[f1386,f1327,f809,f54,f1442])).

fof(f1386,plain,
    ( ! [X23] : k1_xboole_0 = k4_xboole_0(X23,X23)
    | ~ spl3_2
    | ~ spl3_56
    | ~ spl3_70 ),
    inference(backward_demodulation,[],[f1328,f1385])).

fof(f1329,plain,
    ( spl3_70
    | ~ spl3_10
    | ~ spl3_39
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f1183,f924,f434,f100,f1327])).

fof(f100,plain,
    ( spl3_10
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f434,plain,
    ( spl3_39
  <=> ! [X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f1183,plain,
    ( ! [X23] : k1_xboole_0 = k4_xboole_0(X23,k4_xboole_0(X23,k1_xboole_0))
    | ~ spl3_10
    | ~ spl3_39
    | ~ spl3_57 ),
    inference(forward_demodulation,[],[f1067,f102])).

fof(f102,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f1067,plain,
    ( ! [X23] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X23,k4_xboole_0(X23,k1_xboole_0))
    | ~ spl3_39
    | ~ spl3_57 ),
    inference(superposition,[],[f925,f435])).

fof(f435,plain,
    ( ! [X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f434])).

fof(f936,plain,
    ( spl3_58
    | ~ spl3_2
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f927,f495,f54,f934])).

fof(f927,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))
    | ~ spl3_2
    | ~ spl3_44 ),
    inference(superposition,[],[f496,f55])).

fof(f926,plain,(
    spl3_57 ),
    inference(avatar_split_clause,[],[f42,f924])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f28,f31,f31])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f811,plain,(
    spl3_56 ),
    inference(avatar_split_clause,[],[f39,f809])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f552,plain,
    ( spl3_47
    | ~ spl3_11
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f523,f499,f108,f550])).

fof(f523,plain,
    ( ! [X14,X13] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X14))
    | ~ spl3_11
    | ~ spl3_45 ),
    inference(superposition,[],[f109,f500])).

fof(f501,plain,
    ( spl3_45
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f328,f204,f108,f58,f499])).

fof(f328,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f316,f109])).

fof(f316,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0))
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(resolution,[],[f205,f59])).

fof(f497,plain,(
    spl3_44 ),
    inference(avatar_split_clause,[],[f35,f495])).

fof(f35,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f436,plain,
    ( spl3_39
    | ~ spl3_5
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f406,f400,f66,f434])).

fof(f66,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f400,plain,
    ( spl3_38
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f406,plain,
    ( ! [X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)
    | ~ spl3_5
    | ~ spl3_38 ),
    inference(resolution,[],[f401,f67])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f401,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f400])).

fof(f402,plain,
    ( spl3_38
    | ~ spl3_11
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f394,f376,f108,f400])).

fof(f376,plain,
    ( spl3_37
  <=> ! [X1,X3,X2] : r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f394,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl3_11
    | ~ spl3_37 ),
    inference(superposition,[],[f377,f109])).

fof(f377,plain,
    ( ! [X2,X3,X1] : r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f376])).

fof(f378,plain,
    ( spl3_37
    | ~ spl3_3
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f186,f182,f58,f376])).

fof(f182,plain,
    ( spl3_20
  <=> ! [X1,X3,X2] :
        ( ~ r1_tarski(X1,X2)
        | r1_tarski(k4_xboole_0(X1,X3),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f186,plain,
    ( ! [X2,X3,X1] : r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1)
    | ~ spl3_3
    | ~ spl3_20 ),
    inference(resolution,[],[f183,f59])).

fof(f183,plain,
    ( ! [X2,X3,X1] :
        ( ~ r1_tarski(X1,X2)
        | r1_tarski(k4_xboole_0(X1,X3),X2) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f182])).

fof(f232,plain,
    ( spl3_26
    | ~ spl3_5
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f197,f192,f66,f230])).

fof(f192,plain,
    ( spl3_21
  <=> ! [X0] : r1_tarski(k4_xboole_0(sK2,X0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f197,plain,
    ( ! [X4] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,X4),sK1)
    | ~ spl3_5
    | ~ spl3_21 ),
    inference(resolution,[],[f193,f67])).

fof(f193,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK2,X0),sK1)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f192])).

fof(f206,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f43,f204])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f194,plain,
    ( spl3_21
    | ~ spl3_1
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f185,f182,f49,f192])).

fof(f49,plain,
    ( spl3_1
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f185,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK2,X0),sK1)
    | ~ spl3_1
    | ~ spl3_20 ),
    inference(resolution,[],[f183,f51])).

fof(f51,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f184,plain,
    ( spl3_20
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f146,f119,f58,f182])).

fof(f119,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f146,plain,
    ( ! [X2,X3,X1] :
        ( ~ r1_tarski(X1,X2)
        | r1_tarski(k4_xboole_0(X1,X3),X2) )
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(resolution,[],[f120,f59])).

fof(f120,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f38,f119])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f110,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f70,f66,f58,f108])).

fof(f70,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f67,f59])).

fof(f103,plain,
    ( spl3_10
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f98,f94,f66,f100])).

fof(f94,plain,
    ( spl3_9
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f98,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(resolution,[],[f96,f67])).

fof(f96,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f94])).

fof(f97,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f91,f86,f58,f94])).

fof(f86,plain,
    ( spl3_8
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f91,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(superposition,[],[f59,f88])).

fof(f88,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f89,plain,
    ( spl3_8
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f84,f80,f66,f86])).

fof(f80,plain,
    ( spl3_7
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f84,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(resolution,[],[f82,f67])).

fof(f82,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f83,plain,
    ( spl3_7
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f77,f72,f58,f80])).

fof(f72,plain,
    ( spl3_6
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f77,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(superposition,[],[f59,f74])).

fof(f74,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f75,plain,
    ( spl3_6
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f69,f66,f49,f72])).

fof(f69,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK1)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(resolution,[],[f67,f51])).

fof(f68,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f34,f66])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f60,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f56,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f25,f54])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f52,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f23,f49])).

fof(f23,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:41:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (12600)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (12599)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (12610)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (12607)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (12602)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (12606)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (12608)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.50  % (12609)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.50  % (12612)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (12598)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (12601)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (12596)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.51  % (12597)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.51  % (12603)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.51  % (12595)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.52  % (12611)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.52  % (12605)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.52  % (12604)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 5.14/1.03  % (12599)Time limit reached!
% 5.14/1.03  % (12599)------------------------------
% 5.14/1.03  % (12599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.14/1.03  % (12599)Termination reason: Time limit
% 5.14/1.03  
% 5.14/1.03  % (12599)Memory used [KB]: 16247
% 5.14/1.03  % (12599)Time elapsed: 0.611 s
% 5.14/1.03  % (12599)------------------------------
% 5.14/1.03  % (12599)------------------------------
% 11.28/1.78  % (12602)Refutation found. Thanks to Tanya!
% 11.28/1.78  % SZS status Theorem for theBenchmark
% 11.28/1.79  % SZS output start Proof for theBenchmark
% 11.28/1.79  fof(f23208,plain,(
% 11.28/1.79    $false),
% 11.28/1.79    inference(avatar_sat_refutation,[],[f52,f56,f60,f68,f75,f83,f89,f97,f103,f110,f121,f184,f194,f206,f232,f378,f402,f436,f497,f501,f552,f811,f926,f936,f1329,f1444,f1529,f1533,f1608,f1653,f1705,f1949,f2134,f2190,f2194,f2382,f2418,f2455,f2631,f3412,f5753,f6627,f6994,f8189,f8250,f13300,f14949,f17765,f22025,f22070,f22976])).
% 11.28/1.79  fof(f22976,plain,(
% 11.28/1.79    ~spl3_11 | ~spl3_45 | ~spl3_57 | ~spl3_77 | ~spl3_123 | ~spl3_164 | ~spl3_212 | ~spl3_257 | spl3_268),
% 11.28/1.79    inference(avatar_contradiction_clause,[],[f22975])).
% 11.28/1.79  fof(f22975,plain,(
% 11.28/1.79    $false | (~spl3_11 | ~spl3_45 | ~spl3_57 | ~spl3_77 | ~spl3_123 | ~spl3_164 | ~spl3_212 | ~spl3_257 | spl3_268)),
% 11.28/1.79    inference(subsumption_resolution,[],[f22069,f22974])).
% 11.28/1.79  fof(f22974,plain,(
% 11.28/1.79    ( ! [X46] : (k4_xboole_0(X46,sK2) = k5_xboole_0(k4_xboole_0(X46,sK1),k4_xboole_0(X46,k4_xboole_0(X46,k4_xboole_0(sK1,sK2))))) ) | (~spl3_11 | ~spl3_45 | ~spl3_57 | ~spl3_77 | ~spl3_123 | ~spl3_164 | ~spl3_212 | ~spl3_257)),
% 11.28/1.79    inference(forward_demodulation,[],[f22973,f500])).
% 11.28/1.79  fof(f500,plain,(
% 11.28/1.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ) | ~spl3_45),
% 11.28/1.79    inference(avatar_component_clause,[],[f499])).
% 11.28/1.79  fof(f499,plain,(
% 11.28/1.79    spl3_45 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 11.28/1.79  fof(f22973,plain,(
% 11.28/1.79    ( ! [X46] : (k4_xboole_0(X46,sK2) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X46,sK1),k1_xboole_0),k4_xboole_0(X46,k4_xboole_0(X46,k4_xboole_0(sK1,sK2))))) ) | (~spl3_11 | ~spl3_45 | ~spl3_57 | ~spl3_77 | ~spl3_123 | ~spl3_164 | ~spl3_212 | ~spl3_257)),
% 11.28/1.79    inference(forward_demodulation,[],[f22796,f15816])).
% 11.28/1.79  fof(f15816,plain,(
% 11.28/1.79    ( ! [X14,X15,X13] : (k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X15)) = k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X15,X14)))) ) | (~spl3_11 | ~spl3_45 | ~spl3_57 | ~spl3_77 | ~spl3_123 | ~spl3_212)),
% 11.28/1.79    inference(backward_demodulation,[],[f4102,f15815])).
% 11.28/1.79  fof(f15815,plain,(
% 11.28/1.79    ( ! [X10,X11,X9] : (k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(k4_xboole_0(X10,X11),X9)) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X9,X11)))) ) | (~spl3_57 | ~spl3_77 | ~spl3_212)),
% 11.28/1.79    inference(forward_demodulation,[],[f15345,f1607])).
% 11.28/1.79  fof(f1607,plain,(
% 11.28/1.79    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ) | ~spl3_77),
% 11.28/1.79    inference(avatar_component_clause,[],[f1606])).
% 11.28/1.79  fof(f1606,plain,(
% 11.28/1.79    spl3_77 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).
% 11.28/1.79  fof(f15345,plain,(
% 11.28/1.79    ( ! [X10,X11,X9] : (k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(k4_xboole_0(X10,X11),X9)) = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),X11)) ) | (~spl3_57 | ~spl3_212)),
% 11.28/1.79    inference(superposition,[],[f13299,f925])).
% 11.28/1.79  fof(f925,plain,(
% 11.28/1.79    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl3_57),
% 11.28/1.79    inference(avatar_component_clause,[],[f924])).
% 11.28/1.79  fof(f924,plain,(
% 11.28/1.79    spl3_57 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 11.28/1.79  fof(f13299,plain,(
% 11.28/1.79    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) ) | ~spl3_212),
% 11.28/1.79    inference(avatar_component_clause,[],[f13298])).
% 11.28/1.79  fof(f13298,plain,(
% 11.28/1.79    spl3_212 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_212])])).
% 11.28/1.79  fof(f4102,plain,(
% 11.28/1.79    ( ! [X14,X15,X13] : (k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X15)) = k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),X15))) ) | (~spl3_11 | ~spl3_45 | ~spl3_77 | ~spl3_123)),
% 11.28/1.79    inference(forward_demodulation,[],[f4101,f1850])).
% 11.28/1.79  fof(f1850,plain,(
% 11.28/1.79    ( ! [X12,X10,X11] : (k4_xboole_0(k4_xboole_0(X10,X11),X12) = k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X10,X12)))) ) | (~spl3_11 | ~spl3_45 | ~spl3_77)),
% 11.28/1.79    inference(forward_demodulation,[],[f1756,f500])).
% 11.28/1.79  fof(f1756,plain,(
% 11.28/1.79    ( ! [X12,X10,X11] : (k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X10,X12))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),k1_xboole_0),X12)) ) | (~spl3_11 | ~spl3_77)),
% 11.28/1.79    inference(superposition,[],[f1607,f109])).
% 11.28/1.79  fof(f109,plain,(
% 11.28/1.79    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) ) | ~spl3_11),
% 11.28/1.79    inference(avatar_component_clause,[],[f108])).
% 11.28/1.79  fof(f108,plain,(
% 11.28/1.79    spl3_11 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 11.28/1.79  fof(f4101,plain,(
% 11.28/1.79    ( ! [X14,X15,X13] : (k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,k4_xboole_0(X13,X15)))) = k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),X15))) ) | (~spl3_11 | ~spl3_45 | ~spl3_77 | ~spl3_123)),
% 11.28/1.79    inference(forward_demodulation,[],[f4100,f500])).
% 11.28/1.79  fof(f4100,plain,(
% 11.28/1.79    ( ! [X14,X15,X13] : (k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,k4_xboole_0(X13,X15)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X13,X14),k1_xboole_0),k4_xboole_0(k4_xboole_0(X13,X14),X15))) ) | (~spl3_11 | ~spl3_45 | ~spl3_77 | ~spl3_123)),
% 11.28/1.79    inference(forward_demodulation,[],[f3945,f1850])).
% 11.28/1.79  fof(f3945,plain,(
% 11.28/1.79    ( ! [X14,X15,X13] : (k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,k4_xboole_0(X13,X15)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X13,X14),k1_xboole_0),k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X15))))) ) | (~spl3_11 | ~spl3_123)),
% 11.28/1.79    inference(superposition,[],[f3411,f109])).
% 11.28/1.79  fof(f3411,plain,(
% 11.28/1.79    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))) ) | ~spl3_123),
% 11.28/1.79    inference(avatar_component_clause,[],[f3410])).
% 11.28/1.79  fof(f3410,plain,(
% 11.28/1.79    spl3_123 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_123])])).
% 11.28/1.79  fof(f22796,plain,(
% 11.28/1.79    ( ! [X46] : (k4_xboole_0(X46,sK2) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X46,sK1),k1_xboole_0),k4_xboole_0(k4_xboole_0(X46,sK2),k4_xboole_0(X46,sK1)))) ) | (~spl3_164 | ~spl3_257)),
% 11.28/1.79    inference(superposition,[],[f22024,f8249])).
% 11.28/1.79  fof(f8249,plain,(
% 11.28/1.79    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,sK1),k4_xboole_0(X3,sK2))) ) | ~spl3_164),
% 11.28/1.79    inference(avatar_component_clause,[],[f8248])).
% 11.28/1.79  fof(f8248,plain,(
% 11.28/1.79    spl3_164 <=> ! [X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,sK1),k4_xboole_0(X3,sK2))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_164])])).
% 11.28/1.79  fof(f22024,plain,(
% 11.28/1.79    ( ! [X6,X7] : (k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X6) ) | ~spl3_257),
% 11.28/1.79    inference(avatar_component_clause,[],[f22023])).
% 11.28/1.79  fof(f22023,plain,(
% 11.28/1.79    spl3_257 <=> ! [X7,X6] : k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X6),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_257])])).
% 11.28/1.79  fof(f22069,plain,(
% 11.28/1.79    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) | spl3_268),
% 11.28/1.79    inference(avatar_component_clause,[],[f22067])).
% 11.28/1.79  fof(f22067,plain,(
% 11.28/1.79    spl3_268 <=> k4_xboole_0(sK0,sK2) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_268])])).
% 11.28/1.79  fof(f22070,plain,(
% 11.28/1.79    ~spl3_268 | ~spl3_11 | ~spl3_45 | ~spl3_57 | ~spl3_73 | ~spl3_77 | spl3_101 | ~spl3_114 | ~spl3_123 | ~spl3_228),
% 11.28/1.79    inference(avatar_split_clause,[],[f20968,f17763,f3410,f2629,f2452,f1606,f1527,f924,f499,f108,f22067])).
% 11.28/1.79  fof(f1527,plain,(
% 11.28/1.79    spl3_73 <=> ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).
% 11.28/1.79  fof(f2452,plain,(
% 11.28/1.79    spl3_101 <=> k4_xboole_0(sK0,sK2) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1)))))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_101])])).
% 11.28/1.79  fof(f2629,plain,(
% 11.28/1.79    spl3_114 <=> ! [X7,X6] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6)),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_114])])).
% 11.28/1.79  fof(f17763,plain,(
% 11.28/1.79    spl3_228 <=> ! [X22,X23,X24] : k4_xboole_0(X24,k4_xboole_0(X24,k4_xboole_0(X22,k4_xboole_0(X22,X23)))) = k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,k4_xboole_0(X22,X24))))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_228])])).
% 11.28/1.79  fof(f20968,plain,(
% 11.28/1.79    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) | (~spl3_11 | ~spl3_45 | ~spl3_57 | ~spl3_73 | ~spl3_77 | spl3_101 | ~spl3_114 | ~spl3_123 | ~spl3_228)),
% 11.28/1.79    inference(backward_demodulation,[],[f2454,f20967])).
% 11.28/1.79  fof(f20967,plain,(
% 11.28/1.79    ( ! [X21,X22,X20] : (k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(X21,X22))) = k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k4_xboole_0(X21,X22),k4_xboole_0(X20,X21))))) ) | (~spl3_11 | ~spl3_45 | ~spl3_57 | ~spl3_73 | ~spl3_77 | ~spl3_114 | ~spl3_123 | ~spl3_228)),
% 11.28/1.79    inference(forward_demodulation,[],[f20966,f1176])).
% 11.28/1.79  fof(f1176,plain,(
% 11.28/1.79    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X4,X5)))) ) | (~spl3_11 | ~spl3_45 | ~spl3_57)),
% 11.28/1.79    inference(forward_demodulation,[],[f1060,f500])).
% 11.28/1.79  fof(f1060,plain,(
% 11.28/1.79    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k4_xboole_0(k4_xboole_0(X4,X5),k1_xboole_0)) ) | (~spl3_11 | ~spl3_57)),
% 11.28/1.79    inference(superposition,[],[f925,f109])).
% 11.28/1.79  fof(f20966,plain,(
% 11.28/1.79    ( ! [X21,X22,X20] : (k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(X21,X22))) = k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k4_xboole_0(X21,X22),k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(X20,X21))))))) ) | (~spl3_73 | ~spl3_77 | ~spl3_114 | ~spl3_123 | ~spl3_228)),
% 11.28/1.79    inference(forward_demodulation,[],[f20233,f2763])).
% 11.28/1.79  fof(f2763,plain,(
% 11.28/1.79    ( ! [X101,X102,X100] : (k4_xboole_0(X100,k4_xboole_0(X100,k4_xboole_0(X101,X102))) = k4_xboole_0(k4_xboole_0(X100,k4_xboole_0(X100,X101)),k4_xboole_0(X100,k4_xboole_0(X100,k4_xboole_0(X101,k4_xboole_0(X101,X102)))))) ) | (~spl3_73 | ~spl3_77 | ~spl3_114)),
% 11.28/1.79    inference(forward_demodulation,[],[f2762,f1607])).
% 11.28/1.79  fof(f2762,plain,(
% 11.28/1.79    ( ! [X101,X102,X100] : (k4_xboole_0(k4_xboole_0(X100,k4_xboole_0(X100,X101)),k4_xboole_0(k4_xboole_0(X100,k4_xboole_0(X100,X101)),k4_xboole_0(X101,X102))) = k4_xboole_0(X100,k4_xboole_0(X100,k4_xboole_0(X101,X102)))) ) | (~spl3_73 | ~spl3_77 | ~spl3_114)),
% 11.28/1.79    inference(forward_demodulation,[],[f2761,f1528])).
% 11.28/1.79  fof(f1528,plain,(
% 11.28/1.79    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) ) | ~spl3_73),
% 11.28/1.79    inference(avatar_component_clause,[],[f1527])).
% 11.28/1.79  fof(f2761,plain,(
% 11.28/1.79    ( ! [X101,X102,X100] : (k4_xboole_0(k4_xboole_0(X100,k4_xboole_0(X100,X101)),k4_xboole_0(k4_xboole_0(X100,k4_xboole_0(X100,X101)),k4_xboole_0(X101,X102))) = k4_xboole_0(X100,k4_xboole_0(X100,k4_xboole_0(k4_xboole_0(X101,k1_xboole_0),X102)))) ) | (~spl3_77 | ~spl3_114)),
% 11.28/1.79    inference(forward_demodulation,[],[f2760,f1607])).
% 11.28/1.79  fof(f2760,plain,(
% 11.28/1.79    ( ! [X101,X102,X100] : (k4_xboole_0(k4_xboole_0(X100,k4_xboole_0(X100,X101)),k4_xboole_0(k4_xboole_0(X100,k4_xboole_0(X100,X101)),k4_xboole_0(X101,X102))) = k4_xboole_0(k4_xboole_0(X100,k4_xboole_0(X100,k4_xboole_0(X101,k1_xboole_0))),X102)) ) | (~spl3_77 | ~spl3_114)),
% 11.28/1.79    inference(forward_demodulation,[],[f2708,f1607])).
% 11.28/1.79  fof(f2708,plain,(
% 11.28/1.79    ( ! [X101,X102,X100] : (k4_xboole_0(k4_xboole_0(X100,k4_xboole_0(X100,X101)),k4_xboole_0(k4_xboole_0(X100,k4_xboole_0(X100,X101)),k4_xboole_0(X101,X102))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X100,k4_xboole_0(X100,X101)),k1_xboole_0),X102)) ) | (~spl3_77 | ~spl3_114)),
% 11.28/1.79    inference(superposition,[],[f1607,f2630])).
% 11.28/1.79  fof(f2630,plain,(
% 11.28/1.79    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6)) ) | ~spl3_114),
% 11.28/1.79    inference(avatar_component_clause,[],[f2629])).
% 11.28/1.79  fof(f20233,plain,(
% 11.28/1.79    ( ! [X21,X22,X20] : (k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(k4_xboole_0(X21,X22),k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(X20,X21)))))) = k4_xboole_0(k4_xboole_0(X20,k4_xboole_0(X20,X21)),k4_xboole_0(X20,k4_xboole_0(X20,k4_xboole_0(X21,k4_xboole_0(X21,X22)))))) ) | (~spl3_123 | ~spl3_228)),
% 11.28/1.79    inference(superposition,[],[f17764,f3411])).
% 11.28/1.79  fof(f17764,plain,(
% 11.28/1.79    ( ! [X24,X23,X22] : (k4_xboole_0(X24,k4_xboole_0(X24,k4_xboole_0(X22,k4_xboole_0(X22,X23)))) = k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,k4_xboole_0(X22,X24))))) ) | ~spl3_228),
% 11.28/1.79    inference(avatar_component_clause,[],[f17763])).
% 11.28/1.79  fof(f2454,plain,(
% 11.28/1.79    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1))))) | spl3_101),
% 11.28/1.79    inference(avatar_component_clause,[],[f2452])).
% 11.28/1.79  fof(f22025,plain,(
% 11.28/1.79    spl3_257 | ~spl3_100 | ~spl3_139),
% 11.28/1.79    inference(avatar_split_clause,[],[f6345,f5751,f2416,f22023])).
% 11.28/1.79  fof(f2416,plain,(
% 11.28/1.79    spl3_100 <=> ! [X5,X4] : k5_xboole_0(X5,k5_xboole_0(X4,X5)) = X4),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_100])])).
% 11.28/1.79  fof(f5751,plain,(
% 11.28/1.79    spl3_139 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_139])])).
% 11.28/1.79  fof(f6345,plain,(
% 11.28/1.79    ( ! [X6,X7] : (k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X6) ) | (~spl3_100 | ~spl3_139)),
% 11.28/1.79    inference(superposition,[],[f2417,f5752])).
% 11.28/1.79  fof(f5752,plain,(
% 11.28/1.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | ~spl3_139),
% 11.28/1.79    inference(avatar_component_clause,[],[f5751])).
% 11.28/1.79  fof(f2417,plain,(
% 11.28/1.79    ( ! [X4,X5] : (k5_xboole_0(X5,k5_xboole_0(X4,X5)) = X4) ) | ~spl3_100),
% 11.28/1.79    inference(avatar_component_clause,[],[f2416])).
% 11.28/1.79  fof(f17765,plain,(
% 11.28/1.79    spl3_228 | ~spl3_56 | ~spl3_57 | ~spl3_77 | ~spl3_212 | ~spl3_214),
% 11.28/1.79    inference(avatar_split_clause,[],[f16131,f14947,f13298,f1606,f924,f809,f17763])).
% 11.28/1.79  fof(f809,plain,(
% 11.28/1.79    spl3_56 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 11.28/1.79  fof(f14947,plain,(
% 11.28/1.79    spl3_214 <=> ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_214])])).
% 11.28/1.79  fof(f16131,plain,(
% 11.28/1.79    ( ! [X24,X23,X22] : (k4_xboole_0(X24,k4_xboole_0(X24,k4_xboole_0(X22,k4_xboole_0(X22,X23)))) = k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,k4_xboole_0(X22,X24))))) ) | (~spl3_56 | ~spl3_57 | ~spl3_77 | ~spl3_212 | ~spl3_214)),
% 11.28/1.79    inference(backward_demodulation,[],[f1884,f16128])).
% 11.28/1.79  fof(f16128,plain,(
% 11.28/1.79    ( ! [X215,X213,X214] : (k4_xboole_0(X213,k4_xboole_0(X214,X215)) = k4_xboole_0(X213,k4_xboole_0(X214,k4_xboole_0(X214,k4_xboole_0(X213,X215))))) ) | (~spl3_56 | ~spl3_77 | ~spl3_212 | ~spl3_214)),
% 11.28/1.79    inference(forward_demodulation,[],[f16127,f16061])).
% 11.28/1.79  fof(f16061,plain,(
% 11.28/1.79    ( ! [X28,X26,X27] : (k4_xboole_0(X26,k4_xboole_0(X27,X28)) = k5_xboole_0(X26,k4_xboole_0(X27,k4_xboole_0(X27,k4_xboole_0(X26,X28))))) ) | (~spl3_56 | ~spl3_77 | ~spl3_212)),
% 11.28/1.79    inference(forward_demodulation,[],[f15425,f1607])).
% 11.28/1.79  fof(f15425,plain,(
% 11.28/1.79    ( ! [X28,X26,X27] : (k4_xboole_0(X26,k4_xboole_0(X27,X28)) = k5_xboole_0(X26,k4_xboole_0(k4_xboole_0(X27,k4_xboole_0(X27,X26)),X28))) ) | (~spl3_56 | ~spl3_212)),
% 11.28/1.79    inference(superposition,[],[f810,f13299])).
% 11.28/1.79  fof(f810,plain,(
% 11.28/1.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl3_56),
% 11.28/1.79    inference(avatar_component_clause,[],[f809])).
% 11.28/1.79  fof(f16127,plain,(
% 11.28/1.79    ( ! [X215,X213,X214] : (k4_xboole_0(X213,k4_xboole_0(X214,k4_xboole_0(X214,k4_xboole_0(X213,X215)))) = k5_xboole_0(X213,k4_xboole_0(X214,k4_xboole_0(X214,k4_xboole_0(X213,X215))))) ) | (~spl3_77 | ~spl3_212 | ~spl3_214)),
% 11.28/1.79    inference(forward_demodulation,[],[f15476,f1607])).
% 11.28/1.79  fof(f15476,plain,(
% 11.28/1.79    ( ! [X215,X213,X214] : (k4_xboole_0(X213,k4_xboole_0(k4_xboole_0(X214,k4_xboole_0(X214,X213)),X215)) = k5_xboole_0(X213,k4_xboole_0(k4_xboole_0(X214,k4_xboole_0(X214,X213)),X215))) ) | (~spl3_212 | ~spl3_214)),
% 11.28/1.79    inference(superposition,[],[f14948,f13299])).
% 11.28/1.79  fof(f14948,plain,(
% 11.28/1.79    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) ) | ~spl3_214),
% 11.28/1.79    inference(avatar_component_clause,[],[f14947])).
% 11.28/1.79  fof(f1884,plain,(
% 11.28/1.79    ( ! [X24,X23,X22] : (k4_xboole_0(X24,k4_xboole_0(X24,k4_xboole_0(X22,k4_xboole_0(X22,X23)))) = k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,X24))))))) ) | (~spl3_57 | ~spl3_77)),
% 11.28/1.79    inference(forward_demodulation,[],[f1788,f1607])).
% 11.28/1.79  fof(f1788,plain,(
% 11.28/1.79    ( ! [X24,X23,X22] : (k4_xboole_0(X24,k4_xboole_0(X24,k4_xboole_0(X22,k4_xboole_0(X22,X23)))) = k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X23)),X24))))) ) | (~spl3_57 | ~spl3_77)),
% 11.28/1.79    inference(superposition,[],[f1607,f925])).
% 11.28/1.79  fof(f14949,plain,(
% 11.28/1.79    spl3_214 | ~spl3_2 | ~spl3_56 | ~spl3_74 | ~spl3_95),
% 11.28/1.79    inference(avatar_split_clause,[],[f2333,f2192,f1531,f809,f54,f14947])).
% 11.28/1.79  fof(f54,plain,(
% 11.28/1.79    spl3_2 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 11.28/1.79  fof(f1531,plain,(
% 11.28/1.79    spl3_74 <=> ! [X18] : k1_xboole_0 = k5_xboole_0(X18,X18)),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).
% 11.28/1.79  fof(f2192,plain,(
% 11.28/1.79    spl3_95 <=> ! [X1,X0] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_95])])).
% 11.28/1.79  fof(f2333,plain,(
% 11.28/1.79    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) ) | (~spl3_2 | ~spl3_56 | ~spl3_74 | ~spl3_95)),
% 11.28/1.79    inference(forward_demodulation,[],[f2292,f2321])).
% 11.28/1.79  fof(f2321,plain,(
% 11.28/1.79    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl3_2 | ~spl3_74 | ~spl3_95)),
% 11.28/1.79    inference(forward_demodulation,[],[f2291,f55])).
% 11.28/1.79  fof(f55,plain,(
% 11.28/1.79    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_2),
% 11.28/1.79    inference(avatar_component_clause,[],[f54])).
% 11.28/1.79  fof(f2291,plain,(
% 11.28/1.79    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) ) | (~spl3_74 | ~spl3_95)),
% 11.28/1.79    inference(superposition,[],[f2193,f1532])).
% 11.28/1.79  fof(f1532,plain,(
% 11.28/1.79    ( ! [X18] : (k1_xboole_0 = k5_xboole_0(X18,X18)) ) | ~spl3_74),
% 11.28/1.79    inference(avatar_component_clause,[],[f1531])).
% 11.28/1.79  fof(f2193,plain,(
% 11.28/1.79    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) ) | ~spl3_95),
% 11.28/1.79    inference(avatar_component_clause,[],[f2192])).
% 11.28/1.79  fof(f2292,plain,(
% 11.28/1.79    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) ) | (~spl3_56 | ~spl3_95)),
% 11.28/1.79    inference(superposition,[],[f2193,f810])).
% 11.28/1.79  fof(f13300,plain,(
% 11.28/1.79    spl3_212 | ~spl3_57 | ~spl3_77),
% 11.28/1.79    inference(avatar_split_clause,[],[f1774,f1606,f924,f13298])).
% 11.28/1.79  fof(f1774,plain,(
% 11.28/1.79    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) ) | (~spl3_57 | ~spl3_77)),
% 11.28/1.79    inference(superposition,[],[f1607,f925])).
% 11.28/1.79  fof(f8250,plain,(
% 11.28/1.79    spl3_164 | ~spl3_23 | ~spl3_45 | ~spl3_47 | ~spl3_163),
% 11.28/1.79    inference(avatar_split_clause,[],[f8218,f8187,f550,f499,f204,f8248])).
% 11.28/1.79  fof(f204,plain,(
% 11.28/1.79    spl3_23 <=> ! [X1,X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 11.28/1.79  fof(f550,plain,(
% 11.28/1.79    spl3_47 <=> ! [X13,X14] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X14))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 11.28/1.79  fof(f8187,plain,(
% 11.28/1.79    spl3_163 <=> ! [X43] : r1_tarski(k4_xboole_0(k4_xboole_0(X43,sK1),k4_xboole_0(X43,sK2)),k1_xboole_0)),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_163])])).
% 11.28/1.79  fof(f8218,plain,(
% 11.28/1.79    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,sK1),k4_xboole_0(X3,sK2))) ) | (~spl3_23 | ~spl3_45 | ~spl3_47 | ~spl3_163)),
% 11.28/1.79    inference(forward_demodulation,[],[f8217,f551])).
% 11.28/1.79  fof(f551,plain,(
% 11.28/1.79    ( ! [X14,X13] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X14))) ) | ~spl3_47),
% 11.28/1.79    inference(avatar_component_clause,[],[f550])).
% 11.28/1.79  fof(f8217,plain,(
% 11.28/1.79    ( ! [X3] : (k4_xboole_0(k4_xboole_0(X3,sK1),k4_xboole_0(X3,sK2)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,sK1),k4_xboole_0(X3,sK2)),k4_xboole_0(k4_xboole_0(X3,sK1),k4_xboole_0(X3,sK2)))) ) | (~spl3_23 | ~spl3_45 | ~spl3_163)),
% 11.28/1.79    inference(forward_demodulation,[],[f8191,f500])).
% 11.28/1.79  fof(f8191,plain,(
% 11.28/1.79    ( ! [X3] : (k4_xboole_0(k4_xboole_0(X3,sK1),k4_xboole_0(X3,sK2)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,sK1),k4_xboole_0(X3,sK2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,sK1),k4_xboole_0(X3,sK2)),k1_xboole_0))) ) | (~spl3_23 | ~spl3_163)),
% 11.28/1.79    inference(resolution,[],[f8188,f205])).
% 11.28/1.79  fof(f205,plain,(
% 11.28/1.79    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) ) | ~spl3_23),
% 11.28/1.79    inference(avatar_component_clause,[],[f204])).
% 11.28/1.79  fof(f8188,plain,(
% 11.28/1.79    ( ! [X43] : (r1_tarski(k4_xboole_0(k4_xboole_0(X43,sK1),k4_xboole_0(X43,sK2)),k1_xboole_0)) ) | ~spl3_163),
% 11.28/1.79    inference(avatar_component_clause,[],[f8187])).
% 11.28/1.79  fof(f8189,plain,(
% 11.28/1.79    spl3_163 | ~spl3_11 | ~spl3_45 | ~spl3_72 | ~spl3_77 | ~spl3_93 | ~spl3_123 | ~spl3_159),
% 11.28/1.79    inference(avatar_split_clause,[],[f8173,f6992,f3410,f2132,f1606,f1442,f499,f108,f8187])).
% 11.28/1.79  fof(f1442,plain,(
% 11.28/1.79    spl3_72 <=> ! [X23] : k1_xboole_0 = k4_xboole_0(X23,X23)),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 11.28/1.79  fof(f2132,plain,(
% 11.28/1.79    spl3_93 <=> ! [X34] : sK2 = k4_xboole_0(sK2,k4_xboole_0(X34,sK1))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).
% 11.28/1.79  fof(f6992,plain,(
% 11.28/1.79    spl3_159 <=> ! [X55,X56] : r1_tarski(k4_xboole_0(X55,k4_xboole_0(X55,X56)),k4_xboole_0(X56,k4_xboole_0(X56,X55)))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_159])])).
% 11.28/1.79  fof(f8173,plain,(
% 11.28/1.79    ( ! [X43] : (r1_tarski(k4_xboole_0(k4_xboole_0(X43,sK1),k4_xboole_0(X43,sK2)),k1_xboole_0)) ) | (~spl3_11 | ~spl3_45 | ~spl3_72 | ~spl3_77 | ~spl3_93 | ~spl3_123 | ~spl3_159)),
% 11.28/1.79    inference(forward_demodulation,[],[f8172,f4102])).
% 11.28/1.79  fof(f8172,plain,(
% 11.28/1.79    ( ! [X43] : (r1_tarski(k4_xboole_0(k4_xboole_0(X43,sK1),k4_xboole_0(k4_xboole_0(X43,sK1),sK2)),k1_xboole_0)) ) | (~spl3_72 | ~spl3_93 | ~spl3_159)),
% 11.28/1.79    inference(forward_demodulation,[],[f8016,f1443])).
% 11.28/1.79  fof(f1443,plain,(
% 11.28/1.79    ( ! [X23] : (k1_xboole_0 = k4_xboole_0(X23,X23)) ) | ~spl3_72),
% 11.28/1.79    inference(avatar_component_clause,[],[f1442])).
% 11.28/1.79  fof(f8016,plain,(
% 11.28/1.79    ( ! [X43] : (r1_tarski(k4_xboole_0(k4_xboole_0(X43,sK1),k4_xboole_0(k4_xboole_0(X43,sK1),sK2)),k4_xboole_0(sK2,sK2))) ) | (~spl3_93 | ~spl3_159)),
% 11.28/1.79    inference(superposition,[],[f6993,f2133])).
% 11.28/1.79  fof(f2133,plain,(
% 11.28/1.79    ( ! [X34] : (sK2 = k4_xboole_0(sK2,k4_xboole_0(X34,sK1))) ) | ~spl3_93),
% 11.28/1.79    inference(avatar_component_clause,[],[f2132])).
% 11.28/1.79  fof(f6993,plain,(
% 11.28/1.79    ( ! [X56,X55] : (r1_tarski(k4_xboole_0(X55,k4_xboole_0(X55,X56)),k4_xboole_0(X56,k4_xboole_0(X56,X55)))) ) | ~spl3_159),
% 11.28/1.79    inference(avatar_component_clause,[],[f6992])).
% 11.28/1.79  fof(f6994,plain,(
% 11.28/1.79    spl3_159 | ~spl3_89 | ~spl3_147),
% 11.28/1.79    inference(avatar_split_clause,[],[f6696,f6625,f1703,f6992])).
% 11.28/1.79  fof(f1703,plain,(
% 11.28/1.79    spl3_89 <=> ! [X3,X2] : r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_89])])).
% 11.28/1.79  fof(f6625,plain,(
% 11.28/1.79    spl3_147 <=> ! [X15,X14] : k4_xboole_0(X15,X14) = k4_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,X15)))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_147])])).
% 11.28/1.79  fof(f6696,plain,(
% 11.28/1.79    ( ! [X56,X55] : (r1_tarski(k4_xboole_0(X55,k4_xboole_0(X55,X56)),k4_xboole_0(X56,k4_xboole_0(X56,X55)))) ) | (~spl3_89 | ~spl3_147)),
% 11.28/1.79    inference(superposition,[],[f1704,f6626])).
% 11.28/1.79  fof(f6626,plain,(
% 11.28/1.79    ( ! [X14,X15] : (k4_xboole_0(X15,X14) = k4_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,X15)))) ) | ~spl3_147),
% 11.28/1.79    inference(avatar_component_clause,[],[f6625])).
% 11.28/1.79  fof(f1704,plain,(
% 11.28/1.79    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)) ) | ~spl3_89),
% 11.28/1.79    inference(avatar_component_clause,[],[f1703])).
% 11.28/1.79  fof(f6627,plain,(
% 11.28/1.79    spl3_147 | ~spl3_73 | ~spl3_77 | ~spl3_114 | ~spl3_139),
% 11.28/1.79    inference(avatar_split_clause,[],[f6363,f5751,f2629,f1606,f1527,f6625])).
% 11.28/1.79  fof(f6363,plain,(
% 11.28/1.79    ( ! [X14,X15] : (k4_xboole_0(X15,X14) = k4_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,X15)))) ) | (~spl3_73 | ~spl3_77 | ~spl3_114 | ~spl3_139)),
% 11.28/1.79    inference(forward_demodulation,[],[f6362,f5752])).
% 11.28/1.79  fof(f6362,plain,(
% 11.28/1.79    ( ! [X14,X15] : (k4_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k5_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,X15)))) ) | (~spl3_73 | ~spl3_77 | ~spl3_114 | ~spl3_139)),
% 11.28/1.79    inference(forward_demodulation,[],[f6361,f1528])).
% 11.28/1.79  fof(f6361,plain,(
% 11.28/1.79    ( ! [X14,X15] : (k4_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k5_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,k1_xboole_0))))) ) | (~spl3_77 | ~spl3_114 | ~spl3_139)),
% 11.28/1.79    inference(forward_demodulation,[],[f6311,f1607])).
% 11.28/1.79  fof(f6311,plain,(
% 11.28/1.79    ( ! [X14,X15] : (k4_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k5_xboole_0(X15,k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X15)),k1_xboole_0))) ) | (~spl3_114 | ~spl3_139)),
% 11.28/1.79    inference(superposition,[],[f5752,f2630])).
% 11.28/1.79  fof(f5753,plain,(
% 11.28/1.79    spl3_139 | ~spl3_56 | ~spl3_57),
% 11.28/1.79    inference(avatar_split_clause,[],[f1084,f924,f809,f5751])).
% 11.28/1.79  fof(f1084,plain,(
% 11.28/1.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | (~spl3_56 | ~spl3_57)),
% 11.28/1.79    inference(superposition,[],[f810,f925])).
% 11.28/1.79  fof(f3412,plain,(
% 11.28/1.79    spl3_123),
% 11.28/1.79    inference(avatar_split_clause,[],[f47,f3410])).
% 11.28/1.79  fof(f47,plain,(
% 11.28/1.79    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))) )),
% 11.28/1.79    inference(forward_demodulation,[],[f45,f44])).
% 11.28/1.79  fof(f44,plain,(
% 11.28/1.79    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 11.28/1.79    inference(definition_unfolding,[],[f36,f31,f31])).
% 11.28/1.79  fof(f31,plain,(
% 11.28/1.79    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.28/1.79    inference(cnf_transformation,[],[f9])).
% 11.28/1.79  fof(f9,axiom,(
% 11.28/1.79    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.28/1.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 11.28/1.79  fof(f36,plain,(
% 11.28/1.79    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 11.28/1.79    inference(cnf_transformation,[],[f10])).
% 11.28/1.79  fof(f10,axiom,(
% 11.28/1.79    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 11.28/1.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 11.28/1.79  fof(f45,plain,(
% 11.28/1.79    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 11.28/1.79    inference(definition_unfolding,[],[f37,f31,f31,f31,f31])).
% 11.28/1.79  fof(f37,plain,(
% 11.28/1.79    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 11.28/1.79    inference(cnf_transformation,[],[f4])).
% 11.28/1.79  fof(f4,axiom,(
% 11.28/1.79    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 11.28/1.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 11.28/1.79  fof(f2631,plain,(
% 11.28/1.79    spl3_114 | ~spl3_11 | ~spl3_57),
% 11.28/1.79    inference(avatar_split_clause,[],[f1087,f924,f108,f2629])).
% 11.28/1.79  fof(f1087,plain,(
% 11.28/1.79    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6)) ) | (~spl3_11 | ~spl3_57)),
% 11.28/1.79    inference(superposition,[],[f109,f925])).
% 11.28/1.79  fof(f2455,plain,(
% 11.28/1.79    ~spl3_101),
% 11.28/1.79    inference(avatar_split_clause,[],[f46,f2452])).
% 11.28/1.79  fof(f46,plain,(
% 11.28/1.79    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK1)))))),
% 11.28/1.79    inference(backward_demodulation,[],[f40,f44])).
% 11.28/1.79  fof(f40,plain,(
% 11.28/1.79    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK1)))),
% 11.28/1.79    inference(definition_unfolding,[],[f24,f29,f31])).
% 11.28/1.79  fof(f29,plain,(
% 11.28/1.79    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.28/1.79    inference(cnf_transformation,[],[f13])).
% 11.28/1.79  fof(f13,axiom,(
% 11.28/1.79    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.28/1.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 11.28/1.79  fof(f24,plain,(
% 11.28/1.79    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 11.28/1.79    inference(cnf_transformation,[],[f21])).
% 11.28/1.79  fof(f21,plain,(
% 11.28/1.79    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1)),
% 11.28/1.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f20])).
% 11.28/1.79  fof(f20,plain,(
% 11.28/1.79    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1)) => (k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1))),
% 11.28/1.79    introduced(choice_axiom,[])).
% 11.28/1.79  fof(f16,plain,(
% 11.28/1.79    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1))),
% 11.28/1.79    inference(ennf_transformation,[],[f15])).
% 11.28/1.79  fof(f15,negated_conjecture,(
% 11.28/1.79    ~! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 11.28/1.79    inference(negated_conjecture,[],[f14])).
% 11.28/1.79  fof(f14,conjecture,(
% 11.28/1.79    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 11.28/1.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).
% 11.28/1.79  fof(f2418,plain,(
% 11.28/1.79    spl3_100 | ~spl3_2 | ~spl3_94 | ~spl3_99),
% 11.28/1.79    inference(avatar_split_clause,[],[f2406,f2380,f2188,f54,f2416])).
% 11.28/1.79  fof(f2188,plain,(
% 11.28/1.79    spl3_94 <=> ! [X5,X4] : k1_xboole_0 = k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,X5)))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_94])])).
% 11.28/1.79  fof(f2380,plain,(
% 11.28/1.79    spl3_99 <=> ! [X1,X2] : k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_99])])).
% 11.28/1.79  fof(f2406,plain,(
% 11.28/1.79    ( ! [X4,X5] : (k5_xboole_0(X5,k5_xboole_0(X4,X5)) = X4) ) | (~spl3_2 | ~spl3_94 | ~spl3_99)),
% 11.28/1.79    inference(forward_demodulation,[],[f2386,f55])).
% 11.28/1.79  fof(f2386,plain,(
% 11.28/1.79    ( ! [X4,X5] : (k5_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X5,k5_xboole_0(X4,X5))) ) | (~spl3_94 | ~spl3_99)),
% 11.28/1.79    inference(superposition,[],[f2381,f2189])).
% 11.28/1.79  fof(f2189,plain,(
% 11.28/1.79    ( ! [X4,X5] : (k1_xboole_0 = k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,X5)))) ) | ~spl3_94),
% 11.28/1.79    inference(avatar_component_clause,[],[f2188])).
% 11.28/1.79  fof(f2381,plain,(
% 11.28/1.79    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2) ) | ~spl3_99),
% 11.28/1.79    inference(avatar_component_clause,[],[f2380])).
% 11.28/1.79  fof(f2382,plain,(
% 11.28/1.79    spl3_99 | ~spl3_2 | ~spl3_44 | ~spl3_74 | ~spl3_82 | ~spl3_95),
% 11.28/1.79    inference(avatar_split_clause,[],[f2331,f2192,f1651,f1531,f495,f54,f2380])).
% 11.28/1.79  fof(f495,plain,(
% 11.28/1.79    spl3_44 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 11.28/1.79  fof(f1651,plain,(
% 11.28/1.79    spl3_82 <=> ! [X1] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1)),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).
% 11.28/1.79  fof(f2331,plain,(
% 11.28/1.79    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2) ) | (~spl3_2 | ~spl3_44 | ~spl3_74 | ~spl3_82 | ~spl3_95)),
% 11.28/1.79    inference(forward_demodulation,[],[f2325,f2321])).
% 11.28/1.79  fof(f2325,plain,(
% 11.28/1.79    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(X1,k5_xboole_0(X1,X2))) ) | (~spl3_2 | ~spl3_44 | ~spl3_74 | ~spl3_82 | ~spl3_95)),
% 11.28/1.79    inference(backward_demodulation,[],[f1665,f2321])).
% 11.28/1.79  fof(f1665,plain,(
% 11.28/1.79    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2))) ) | (~spl3_44 | ~spl3_82)),
% 11.28/1.79    inference(superposition,[],[f496,f1652])).
% 11.28/1.79  fof(f1652,plain,(
% 11.28/1.79    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1)) ) | ~spl3_82),
% 11.28/1.79    inference(avatar_component_clause,[],[f1651])).
% 11.28/1.79  fof(f496,plain,(
% 11.28/1.79    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl3_44),
% 11.28/1.79    inference(avatar_component_clause,[],[f495])).
% 11.28/1.79  fof(f2194,plain,(
% 11.28/1.79    spl3_95 | ~spl3_44 | ~spl3_74),
% 11.28/1.79    inference(avatar_split_clause,[],[f1590,f1531,f495,f2192])).
% 11.28/1.79  fof(f1590,plain,(
% 11.28/1.79    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) ) | (~spl3_44 | ~spl3_74)),
% 11.28/1.79    inference(superposition,[],[f496,f1532])).
% 11.28/1.79  fof(f2190,plain,(
% 11.28/1.79    spl3_94 | ~spl3_44 | ~spl3_74),
% 11.28/1.79    inference(avatar_split_clause,[],[f1589,f1531,f495,f2188])).
% 11.28/1.79  fof(f1589,plain,(
% 11.28/1.79    ( ! [X4,X5] : (k1_xboole_0 = k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,X5)))) ) | (~spl3_44 | ~spl3_74)),
% 11.28/1.79    inference(superposition,[],[f1532,f496])).
% 11.28/1.79  fof(f2134,plain,(
% 11.28/1.79    spl3_93 | ~spl3_2 | ~spl3_56 | ~spl3_92),
% 11.28/1.79    inference(avatar_split_clause,[],[f2120,f1947,f809,f54,f2132])).
% 11.28/1.79  fof(f1947,plain,(
% 11.28/1.79    spl3_92 <=> ! [X12] : k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X12,sK1)))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).
% 11.28/1.79  fof(f2120,plain,(
% 11.28/1.79    ( ! [X34] : (sK2 = k4_xboole_0(sK2,k4_xboole_0(X34,sK1))) ) | (~spl3_2 | ~spl3_56 | ~spl3_92)),
% 11.28/1.79    inference(forward_demodulation,[],[f2071,f55])).
% 11.28/1.79  fof(f2071,plain,(
% 11.28/1.79    ( ! [X34] : (k5_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k4_xboole_0(X34,sK1))) ) | (~spl3_56 | ~spl3_92)),
% 11.28/1.79    inference(superposition,[],[f810,f1948])).
% 11.28/1.79  fof(f1948,plain,(
% 11.28/1.79    ( ! [X12] : (k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X12,sK1)))) ) | ~spl3_92),
% 11.28/1.79    inference(avatar_component_clause,[],[f1947])).
% 11.28/1.79  fof(f1949,plain,(
% 11.28/1.79    spl3_92 | ~spl3_26 | ~spl3_77),
% 11.28/1.79    inference(avatar_split_clause,[],[f1784,f1606,f230,f1947])).
% 11.28/1.79  fof(f230,plain,(
% 11.28/1.79    spl3_26 <=> ! [X4] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,X4),sK1)),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 11.28/1.79  fof(f1784,plain,(
% 11.28/1.79    ( ! [X12] : (k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X12,sK1)))) ) | (~spl3_26 | ~spl3_77)),
% 11.28/1.79    inference(superposition,[],[f1607,f231])).
% 11.28/1.79  fof(f231,plain,(
% 11.28/1.79    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,X4),sK1)) ) | ~spl3_26),
% 11.28/1.79    inference(avatar_component_clause,[],[f230])).
% 11.28/1.79  fof(f1705,plain,(
% 11.28/1.79    spl3_89 | ~spl3_3 | ~spl3_57),
% 11.28/1.79    inference(avatar_split_clause,[],[f1085,f924,f58,f1703])).
% 11.28/1.79  fof(f58,plain,(
% 11.28/1.79    spl3_3 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 11.28/1.79  fof(f1085,plain,(
% 11.28/1.79    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)) ) | (~spl3_3 | ~spl3_57)),
% 11.28/1.79    inference(superposition,[],[f59,f925])).
% 11.28/1.79  fof(f59,plain,(
% 11.28/1.79    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_3),
% 11.28/1.79    inference(avatar_component_clause,[],[f58])).
% 11.28/1.79  fof(f1653,plain,(
% 11.28/1.79    spl3_82 | ~spl3_58 | ~spl3_74),
% 11.28/1.79    inference(avatar_split_clause,[],[f1588,f1531,f934,f1651])).
% 11.28/1.79  fof(f934,plain,(
% 11.28/1.79    spl3_58 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 11.28/1.79  fof(f1588,plain,(
% 11.28/1.79    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1)) ) | (~spl3_58 | ~spl3_74)),
% 11.28/1.79    inference(superposition,[],[f1532,f935])).
% 11.28/1.79  fof(f935,plain,(
% 11.28/1.79    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) ) | ~spl3_58),
% 11.28/1.79    inference(avatar_component_clause,[],[f934])).
% 11.28/1.79  fof(f1608,plain,(
% 11.28/1.79    spl3_77),
% 11.28/1.79    inference(avatar_split_clause,[],[f44,f1606])).
% 11.28/1.79  fof(f1533,plain,(
% 11.28/1.79    spl3_74 | ~spl3_2 | ~spl3_56 | ~spl3_70),
% 11.28/1.79    inference(avatar_split_clause,[],[f1393,f1327,f809,f54,f1531])).
% 11.28/1.79  fof(f1327,plain,(
% 11.28/1.79    spl3_70 <=> ! [X23] : k1_xboole_0 = k4_xboole_0(X23,k4_xboole_0(X23,k1_xboole_0))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 11.28/1.79  fof(f1393,plain,(
% 11.28/1.79    ( ! [X18] : (k1_xboole_0 = k5_xboole_0(X18,X18)) ) | (~spl3_2 | ~spl3_56 | ~spl3_70)),
% 11.28/1.79    inference(forward_demodulation,[],[f1352,f1385])).
% 11.28/1.79  fof(f1385,plain,(
% 11.28/1.79    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) ) | (~spl3_2 | ~spl3_56 | ~spl3_70)),
% 11.28/1.79    inference(forward_demodulation,[],[f1340,f55])).
% 11.28/1.79  fof(f1340,plain,(
% 11.28/1.79    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0)) ) | (~spl3_56 | ~spl3_70)),
% 11.28/1.79    inference(superposition,[],[f810,f1328])).
% 11.28/1.79  fof(f1328,plain,(
% 11.28/1.79    ( ! [X23] : (k1_xboole_0 = k4_xboole_0(X23,k4_xboole_0(X23,k1_xboole_0))) ) | ~spl3_70),
% 11.28/1.79    inference(avatar_component_clause,[],[f1327])).
% 11.28/1.79  fof(f1352,plain,(
% 11.28/1.79    ( ! [X18] : (k1_xboole_0 = k5_xboole_0(X18,k4_xboole_0(X18,k1_xboole_0))) ) | (~spl3_56 | ~spl3_70)),
% 11.28/1.79    inference(superposition,[],[f810,f1328])).
% 11.28/1.79  fof(f1529,plain,(
% 11.28/1.79    spl3_73 | ~spl3_2 | ~spl3_56 | ~spl3_70),
% 11.28/1.79    inference(avatar_split_clause,[],[f1385,f1327,f809,f54,f1527])).
% 11.28/1.79  fof(f1444,plain,(
% 11.28/1.79    spl3_72 | ~spl3_2 | ~spl3_56 | ~spl3_70),
% 11.28/1.79    inference(avatar_split_clause,[],[f1386,f1327,f809,f54,f1442])).
% 11.28/1.79  fof(f1386,plain,(
% 11.28/1.79    ( ! [X23] : (k1_xboole_0 = k4_xboole_0(X23,X23)) ) | (~spl3_2 | ~spl3_56 | ~spl3_70)),
% 11.28/1.79    inference(backward_demodulation,[],[f1328,f1385])).
% 11.28/1.79  fof(f1329,plain,(
% 11.28/1.79    spl3_70 | ~spl3_10 | ~spl3_39 | ~spl3_57),
% 11.28/1.79    inference(avatar_split_clause,[],[f1183,f924,f434,f100,f1327])).
% 11.28/1.79  fof(f100,plain,(
% 11.28/1.79    spl3_10 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 11.28/1.79  fof(f434,plain,(
% 11.28/1.79    spl3_39 <=> ! [X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 11.28/1.79  fof(f1183,plain,(
% 11.28/1.79    ( ! [X23] : (k1_xboole_0 = k4_xboole_0(X23,k4_xboole_0(X23,k1_xboole_0))) ) | (~spl3_10 | ~spl3_39 | ~spl3_57)),
% 11.28/1.79    inference(forward_demodulation,[],[f1067,f102])).
% 11.28/1.79  fof(f102,plain,(
% 11.28/1.79    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_10),
% 11.28/1.79    inference(avatar_component_clause,[],[f100])).
% 11.28/1.79  fof(f1067,plain,(
% 11.28/1.79    ( ! [X23] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X23,k4_xboole_0(X23,k1_xboole_0))) ) | (~spl3_39 | ~spl3_57)),
% 11.28/1.79    inference(superposition,[],[f925,f435])).
% 11.28/1.79  fof(f435,plain,(
% 11.28/1.79    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)) ) | ~spl3_39),
% 11.28/1.79    inference(avatar_component_clause,[],[f434])).
% 11.28/1.79  fof(f936,plain,(
% 11.28/1.79    spl3_58 | ~spl3_2 | ~spl3_44),
% 11.28/1.79    inference(avatar_split_clause,[],[f927,f495,f54,f934])).
% 11.28/1.79  fof(f927,plain,(
% 11.28/1.79    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) ) | (~spl3_2 | ~spl3_44)),
% 11.28/1.79    inference(superposition,[],[f496,f55])).
% 11.28/1.79  fof(f926,plain,(
% 11.28/1.79    spl3_57),
% 11.28/1.79    inference(avatar_split_clause,[],[f42,f924])).
% 11.28/1.79  fof(f42,plain,(
% 11.28/1.79    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.28/1.79    inference(definition_unfolding,[],[f28,f31,f31])).
% 11.28/1.79  fof(f28,plain,(
% 11.28/1.79    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.28/1.79    inference(cnf_transformation,[],[f1])).
% 11.28/1.79  fof(f1,axiom,(
% 11.28/1.79    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.28/1.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 11.28/1.79  fof(f811,plain,(
% 11.28/1.79    spl3_56),
% 11.28/1.79    inference(avatar_split_clause,[],[f39,f809])).
% 11.28/1.79  fof(f39,plain,(
% 11.28/1.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.28/1.79    inference(definition_unfolding,[],[f30,f31])).
% 11.28/1.79  fof(f30,plain,(
% 11.28/1.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.28/1.79    inference(cnf_transformation,[],[f3])).
% 11.28/1.79  fof(f3,axiom,(
% 11.28/1.79    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.28/1.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 11.28/1.79  fof(f552,plain,(
% 11.28/1.79    spl3_47 | ~spl3_11 | ~spl3_45),
% 11.28/1.79    inference(avatar_split_clause,[],[f523,f499,f108,f550])).
% 11.28/1.79  fof(f523,plain,(
% 11.28/1.79    ( ! [X14,X13] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X14))) ) | (~spl3_11 | ~spl3_45)),
% 11.28/1.79    inference(superposition,[],[f109,f500])).
% 11.28/1.79  fof(f501,plain,(
% 11.28/1.79    spl3_45 | ~spl3_3 | ~spl3_11 | ~spl3_23),
% 11.28/1.79    inference(avatar_split_clause,[],[f328,f204,f108,f58,f499])).
% 11.28/1.79  fof(f328,plain,(
% 11.28/1.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ) | (~spl3_3 | ~spl3_11 | ~spl3_23)),
% 11.28/1.79    inference(forward_demodulation,[],[f316,f109])).
% 11.28/1.79  fof(f316,plain,(
% 11.28/1.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0))) ) | (~spl3_3 | ~spl3_23)),
% 11.28/1.79    inference(resolution,[],[f205,f59])).
% 11.28/1.79  fof(f497,plain,(
% 11.28/1.79    spl3_44),
% 11.28/1.79    inference(avatar_split_clause,[],[f35,f495])).
% 11.28/1.79  fof(f35,plain,(
% 11.28/1.79    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 11.28/1.79    inference(cnf_transformation,[],[f12])).
% 11.28/1.79  fof(f12,axiom,(
% 11.28/1.79    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 11.28/1.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 11.28/1.79  fof(f436,plain,(
% 11.28/1.79    spl3_39 | ~spl3_5 | ~spl3_38),
% 11.28/1.79    inference(avatar_split_clause,[],[f406,f400,f66,f434])).
% 11.28/1.79  fof(f66,plain,(
% 11.28/1.79    spl3_5 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 11.28/1.79  fof(f400,plain,(
% 11.28/1.79    spl3_38 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 11.28/1.79  fof(f406,plain,(
% 11.28/1.79    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)) ) | (~spl3_5 | ~spl3_38)),
% 11.28/1.79    inference(resolution,[],[f401,f67])).
% 11.28/1.79  fof(f67,plain,(
% 11.28/1.79    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_5),
% 11.28/1.79    inference(avatar_component_clause,[],[f66])).
% 11.28/1.79  fof(f401,plain,(
% 11.28/1.79    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl3_38),
% 11.28/1.79    inference(avatar_component_clause,[],[f400])).
% 11.28/1.79  fof(f402,plain,(
% 11.28/1.79    spl3_38 | ~spl3_11 | ~spl3_37),
% 11.28/1.79    inference(avatar_split_clause,[],[f394,f376,f108,f400])).
% 11.28/1.79  fof(f376,plain,(
% 11.28/1.79    spl3_37 <=> ! [X1,X3,X2] : r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1)),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 11.28/1.79  fof(f394,plain,(
% 11.28/1.79    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (~spl3_11 | ~spl3_37)),
% 11.28/1.79    inference(superposition,[],[f377,f109])).
% 11.28/1.79  fof(f377,plain,(
% 11.28/1.79    ( ! [X2,X3,X1] : (r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1)) ) | ~spl3_37),
% 11.28/1.79    inference(avatar_component_clause,[],[f376])).
% 11.28/1.79  fof(f378,plain,(
% 11.28/1.79    spl3_37 | ~spl3_3 | ~spl3_20),
% 11.28/1.79    inference(avatar_split_clause,[],[f186,f182,f58,f376])).
% 11.28/1.79  fof(f182,plain,(
% 11.28/1.79    spl3_20 <=> ! [X1,X3,X2] : (~r1_tarski(X1,X2) | r1_tarski(k4_xboole_0(X1,X3),X2))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 11.28/1.79  fof(f186,plain,(
% 11.28/1.79    ( ! [X2,X3,X1] : (r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1)) ) | (~spl3_3 | ~spl3_20)),
% 11.28/1.79    inference(resolution,[],[f183,f59])).
% 11.28/1.79  fof(f183,plain,(
% 11.28/1.79    ( ! [X2,X3,X1] : (~r1_tarski(X1,X2) | r1_tarski(k4_xboole_0(X1,X3),X2)) ) | ~spl3_20),
% 11.28/1.79    inference(avatar_component_clause,[],[f182])).
% 11.28/1.79  fof(f232,plain,(
% 11.28/1.79    spl3_26 | ~spl3_5 | ~spl3_21),
% 11.28/1.79    inference(avatar_split_clause,[],[f197,f192,f66,f230])).
% 11.28/1.79  fof(f192,plain,(
% 11.28/1.79    spl3_21 <=> ! [X0] : r1_tarski(k4_xboole_0(sK2,X0),sK1)),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 11.28/1.79  fof(f197,plain,(
% 11.28/1.79    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,X4),sK1)) ) | (~spl3_5 | ~spl3_21)),
% 11.28/1.79    inference(resolution,[],[f193,f67])).
% 11.28/1.79  fof(f193,plain,(
% 11.28/1.79    ( ! [X0] : (r1_tarski(k4_xboole_0(sK2,X0),sK1)) ) | ~spl3_21),
% 11.28/1.79    inference(avatar_component_clause,[],[f192])).
% 11.28/1.79  fof(f206,plain,(
% 11.28/1.79    spl3_23),
% 11.28/1.79    inference(avatar_split_clause,[],[f43,f204])).
% 11.28/1.79  fof(f43,plain,(
% 11.28/1.79    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 11.28/1.79    inference(definition_unfolding,[],[f32,f31])).
% 11.28/1.79  fof(f32,plain,(
% 11.28/1.79    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.28/1.79    inference(cnf_transformation,[],[f17])).
% 11.28/1.79  fof(f17,plain,(
% 11.28/1.79    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.28/1.79    inference(ennf_transformation,[],[f7])).
% 11.28/1.79  fof(f7,axiom,(
% 11.28/1.79    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.28/1.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 11.28/1.79  fof(f194,plain,(
% 11.28/1.79    spl3_21 | ~spl3_1 | ~spl3_20),
% 11.28/1.79    inference(avatar_split_clause,[],[f185,f182,f49,f192])).
% 11.28/1.79  fof(f49,plain,(
% 11.28/1.79    spl3_1 <=> r1_tarski(sK2,sK1)),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 11.28/1.79  fof(f185,plain,(
% 11.28/1.79    ( ! [X0] : (r1_tarski(k4_xboole_0(sK2,X0),sK1)) ) | (~spl3_1 | ~spl3_20)),
% 11.28/1.79    inference(resolution,[],[f183,f51])).
% 11.28/1.79  fof(f51,plain,(
% 11.28/1.79    r1_tarski(sK2,sK1) | ~spl3_1),
% 11.28/1.79    inference(avatar_component_clause,[],[f49])).
% 11.28/1.79  fof(f184,plain,(
% 11.28/1.79    spl3_20 | ~spl3_3 | ~spl3_12),
% 11.28/1.79    inference(avatar_split_clause,[],[f146,f119,f58,f182])).
% 11.28/1.79  fof(f119,plain,(
% 11.28/1.79    spl3_12 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 11.28/1.79  fof(f146,plain,(
% 11.28/1.79    ( ! [X2,X3,X1] : (~r1_tarski(X1,X2) | r1_tarski(k4_xboole_0(X1,X3),X2)) ) | (~spl3_3 | ~spl3_12)),
% 11.28/1.79    inference(resolution,[],[f120,f59])).
% 11.28/1.79  fof(f120,plain,(
% 11.28/1.79    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) ) | ~spl3_12),
% 11.28/1.79    inference(avatar_component_clause,[],[f119])).
% 11.28/1.79  fof(f121,plain,(
% 11.28/1.79    spl3_12),
% 11.28/1.79    inference(avatar_split_clause,[],[f38,f119])).
% 11.28/1.79  fof(f38,plain,(
% 11.28/1.79    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.28/1.79    inference(cnf_transformation,[],[f19])).
% 11.28/1.79  fof(f19,plain,(
% 11.28/1.79    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.28/1.79    inference(flattening,[],[f18])).
% 11.28/1.79  fof(f18,plain,(
% 11.28/1.79    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.28/1.79    inference(ennf_transformation,[],[f6])).
% 11.28/1.79  fof(f6,axiom,(
% 11.28/1.79    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.28/1.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 11.28/1.79  fof(f110,plain,(
% 11.28/1.79    spl3_11 | ~spl3_3 | ~spl3_5),
% 11.28/1.79    inference(avatar_split_clause,[],[f70,f66,f58,f108])).
% 11.28/1.79  fof(f70,plain,(
% 11.28/1.79    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) ) | (~spl3_3 | ~spl3_5)),
% 11.28/1.79    inference(resolution,[],[f67,f59])).
% 11.28/1.79  fof(f103,plain,(
% 11.28/1.79    spl3_10 | ~spl3_5 | ~spl3_9),
% 11.28/1.79    inference(avatar_split_clause,[],[f98,f94,f66,f100])).
% 11.28/1.79  fof(f94,plain,(
% 11.28/1.79    spl3_9 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 11.28/1.79  fof(f98,plain,(
% 11.28/1.79    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl3_5 | ~spl3_9)),
% 11.28/1.79    inference(resolution,[],[f96,f67])).
% 11.28/1.79  fof(f96,plain,(
% 11.28/1.79    r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl3_9),
% 11.28/1.79    inference(avatar_component_clause,[],[f94])).
% 11.28/1.79  fof(f97,plain,(
% 11.28/1.79    spl3_9 | ~spl3_3 | ~spl3_8),
% 11.28/1.79    inference(avatar_split_clause,[],[f91,f86,f58,f94])).
% 11.28/1.79  fof(f86,plain,(
% 11.28/1.79    spl3_8 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 11.28/1.79  fof(f91,plain,(
% 11.28/1.79    r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl3_3 | ~spl3_8)),
% 11.28/1.79    inference(superposition,[],[f59,f88])).
% 11.28/1.79  fof(f88,plain,(
% 11.28/1.79    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) | ~spl3_8),
% 11.28/1.79    inference(avatar_component_clause,[],[f86])).
% 11.28/1.79  fof(f89,plain,(
% 11.28/1.79    spl3_8 | ~spl3_5 | ~spl3_7),
% 11.28/1.79    inference(avatar_split_clause,[],[f84,f80,f66,f86])).
% 11.28/1.79  fof(f80,plain,(
% 11.28/1.79    spl3_7 <=> r1_tarski(k1_xboole_0,sK2)),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 11.28/1.79  fof(f84,plain,(
% 11.28/1.79    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) | (~spl3_5 | ~spl3_7)),
% 11.28/1.79    inference(resolution,[],[f82,f67])).
% 11.28/1.79  fof(f82,plain,(
% 11.28/1.79    r1_tarski(k1_xboole_0,sK2) | ~spl3_7),
% 11.28/1.79    inference(avatar_component_clause,[],[f80])).
% 11.28/1.79  fof(f83,plain,(
% 11.28/1.79    spl3_7 | ~spl3_3 | ~spl3_6),
% 11.28/1.79    inference(avatar_split_clause,[],[f77,f72,f58,f80])).
% 11.28/1.79  fof(f72,plain,(
% 11.28/1.79    spl3_6 <=> k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 11.28/1.79    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 11.28/1.79  fof(f77,plain,(
% 11.28/1.79    r1_tarski(k1_xboole_0,sK2) | (~spl3_3 | ~spl3_6)),
% 11.28/1.79    inference(superposition,[],[f59,f74])).
% 11.28/1.79  fof(f74,plain,(
% 11.28/1.79    k1_xboole_0 = k4_xboole_0(sK2,sK1) | ~spl3_6),
% 11.28/1.79    inference(avatar_component_clause,[],[f72])).
% 11.28/1.79  fof(f75,plain,(
% 11.28/1.79    spl3_6 | ~spl3_1 | ~spl3_5),
% 11.28/1.79    inference(avatar_split_clause,[],[f69,f66,f49,f72])).
% 11.28/1.79  fof(f69,plain,(
% 11.28/1.79    k1_xboole_0 = k4_xboole_0(sK2,sK1) | (~spl3_1 | ~spl3_5)),
% 11.28/1.79    inference(resolution,[],[f67,f51])).
% 11.28/1.79  fof(f68,plain,(
% 11.28/1.79    spl3_5),
% 11.28/1.79    inference(avatar_split_clause,[],[f34,f66])).
% 11.28/1.79  fof(f34,plain,(
% 11.28/1.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 11.28/1.79    inference(cnf_transformation,[],[f22])).
% 11.28/1.79  fof(f22,plain,(
% 11.28/1.79    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 11.28/1.79    inference(nnf_transformation,[],[f2])).
% 11.28/1.79  fof(f2,axiom,(
% 11.28/1.79    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 11.28/1.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 11.28/1.79  fof(f60,plain,(
% 11.28/1.79    spl3_3),
% 11.28/1.79    inference(avatar_split_clause,[],[f26,f58])).
% 11.28/1.79  fof(f26,plain,(
% 11.28/1.79    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.28/1.79    inference(cnf_transformation,[],[f8])).
% 11.28/1.79  fof(f8,axiom,(
% 11.28/1.79    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.28/1.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 11.28/1.79  fof(f56,plain,(
% 11.28/1.79    spl3_2),
% 11.28/1.79    inference(avatar_split_clause,[],[f25,f54])).
% 11.28/1.79  fof(f25,plain,(
% 11.28/1.79    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.28/1.79    inference(cnf_transformation,[],[f11])).
% 11.28/1.79  fof(f11,axiom,(
% 11.28/1.79    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 11.28/1.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 11.28/1.79  fof(f52,plain,(
% 11.28/1.79    spl3_1),
% 11.28/1.79    inference(avatar_split_clause,[],[f23,f49])).
% 11.28/1.79  fof(f23,plain,(
% 11.28/1.79    r1_tarski(sK2,sK1)),
% 11.28/1.79    inference(cnf_transformation,[],[f21])).
% 11.28/1.79  % SZS output end Proof for theBenchmark
% 11.28/1.79  % (12602)------------------------------
% 11.28/1.79  % (12602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.28/1.79  % (12602)Termination reason: Refutation
% 11.28/1.79  
% 11.28/1.79  % (12602)Memory used [KB]: 29167
% 11.28/1.79  % (12602)Time elapsed: 1.325 s
% 11.28/1.79  % (12602)------------------------------
% 11.28/1.79  % (12602)------------------------------
% 11.28/1.80  % (12592)Success in time 1.438 s
%------------------------------------------------------------------------------
