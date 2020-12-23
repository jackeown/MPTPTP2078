%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:10 EST 2020

% Result     : Theorem 7.60s
% Output     : Refutation 7.60s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 252 expanded)
%              Number of leaves         :   43 ( 134 expanded)
%              Depth                    :    6
%              Number of atoms          :  306 ( 518 expanded)
%              Number of equality atoms :  112 ( 218 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26354,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f37,f47,f60,f64,f68,f80,f88,f92,f104,f108,f121,f132,f136,f146,f172,f199,f215,f248,f266,f312,f560,f584,f904,f1119,f1977,f2245,f2685,f3587,f7001,f25180,f26258,f26353])).

fof(f26353,plain,
    ( spl6_83
    | ~ spl6_302
    | ~ spl6_316 ),
    inference(avatar_contradiction_clause,[],[f26352])).

fof(f26352,plain,
    ( $false
    | spl6_83
    | ~ spl6_302
    | ~ spl6_316 ),
    inference(subsumption_resolution,[],[f1976,f26327])).

fof(f26327,plain,
    ( ! [X39,X37,X41,X38,X36,X40] : k4_enumset1(X36,X37,X38,X41,X40,X39) = k4_enumset1(X36,X37,X39,X40,X38,X41)
    | ~ spl6_302
    | ~ spl6_316 ),
    inference(superposition,[],[f26257,f25179])).

fof(f25179,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X0,X1,X4,X3,X2))
    | ~ spl6_302 ),
    inference(avatar_component_clause,[],[f25178])).

fof(f25178,plain,
    ( spl6_302
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X0,X1,X4,X3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_302])])).

fof(f26257,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X0,X3,X1,X2,X4))
    | ~ spl6_316 ),
    inference(avatar_component_clause,[],[f26256])).

fof(f26256,plain,
    ( spl6_316
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X0,X3,X1,X2,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_316])])).

fof(f1976,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK0,sK1,sK5,sK4,sK2,sK3)
    | spl6_83 ),
    inference(avatar_component_clause,[],[f1974])).

fof(f1974,plain,
    ( spl6_83
  <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) = k4_enumset1(sK0,sK1,sK5,sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).

fof(f26258,plain,
    ( spl6_316
    | ~ spl6_12
    | ~ spl6_174 ),
    inference(avatar_split_clause,[],[f7040,f6999,f102,f26256])).

fof(f102,plain,
    ( spl6_12
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f6999,plain,
    ( spl6_174
  <=> ! [X9,X5,X7,X8,X6] : k3_enumset1(X6,X7,X8,X9,X5) = k3_enumset1(X6,X9,X7,X8,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_174])])).

fof(f7040,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X0,X3,X1,X2,X4))
    | ~ spl6_12
    | ~ spl6_174 ),
    inference(superposition,[],[f103,f7000])).

fof(f7000,plain,
    ( ! [X6,X8,X7,X5,X9] : k3_enumset1(X6,X7,X8,X9,X5) = k3_enumset1(X6,X9,X7,X8,X5)
    | ~ spl6_174 ),
    inference(avatar_component_clause,[],[f6999])).

fof(f103,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f102])).

fof(f25180,plain,
    ( spl6_302
    | ~ spl6_12
    | ~ spl6_128 ),
    inference(avatar_split_clause,[],[f3940,f3585,f102,f25178])).

fof(f3585,plain,
    ( spl6_128
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X4,X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_128])])).

fof(f3940,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X0,X1,X4,X3,X2))
    | ~ spl6_12
    | ~ spl6_128 ),
    inference(superposition,[],[f103,f3586])).

fof(f3586,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X4,X3,X2)
    | ~ spl6_128 ),
    inference(avatar_component_clause,[],[f3585])).

fof(f7001,plain,
    ( spl6_174
    | ~ spl6_20
    | ~ spl6_111 ),
    inference(avatar_split_clause,[],[f2690,f2683,f170,f6999])).

fof(f170,plain,
    ( spl6_20
  <=> ! [X9,X5,X7,X8,X6] : k3_enumset1(X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X9),k2_enumset1(X5,X6,X7,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f2683,plain,
    ( spl6_111
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X2,X3,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).

fof(f2690,plain,
    ( ! [X6,X8,X7,X5,X9] : k3_enumset1(X6,X7,X8,X9,X5) = k3_enumset1(X6,X9,X7,X8,X5)
    | ~ spl6_20
    | ~ spl6_111 ),
    inference(superposition,[],[f2684,f171])).

fof(f171,plain,
    ( ! [X6,X8,X7,X5,X9] : k3_enumset1(X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X9),k2_enumset1(X5,X6,X7,X8))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f170])).

fof(f2684,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X2,X3,X1))
    | ~ spl6_111 ),
    inference(avatar_component_clause,[],[f2683])).

fof(f3587,plain,
    ( spl6_128
    | ~ spl6_10
    | ~ spl6_97 ),
    inference(avatar_split_clause,[],[f2256,f2243,f86,f3585])).

fof(f86,plain,
    ( spl6_10
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f2243,plain,
    ( spl6_97
  <=> ! [X5,X7,X8,X4,X6] : k3_enumset1(X7,X8,X4,X5,X6) = k2_xboole_0(k2_tarski(X7,X8),k1_enumset1(X6,X5,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).

fof(f2256,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X4,X3,X2)
    | ~ spl6_10
    | ~ spl6_97 ),
    inference(superposition,[],[f2244,f87])).

fof(f87,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f86])).

fof(f2244,plain,
    ( ! [X6,X4,X8,X7,X5] : k3_enumset1(X7,X8,X4,X5,X6) = k2_xboole_0(k2_tarski(X7,X8),k1_enumset1(X6,X5,X4))
    | ~ spl6_97 ),
    inference(avatar_component_clause,[],[f2243])).

fof(f2685,plain,
    ( spl6_111
    | ~ spl6_20
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f907,f902,f170,f2683])).

fof(f902,plain,
    ( spl6_52
  <=> ! [X5,X7,X4,X6] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X7,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f907,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X2,X3,X1))
    | ~ spl6_20
    | ~ spl6_52 ),
    inference(superposition,[],[f171,f903])).

fof(f903,plain,
    ( ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X7,X5)
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f902])).

fof(f2245,plain,
    ( spl6_97
    | ~ spl6_10
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f330,f264,f86,f2243])).

fof(f264,plain,
    ( spl6_29
  <=> ! [X3,X5,X4] : k1_enumset1(X4,X5,X3) = k1_enumset1(X3,X5,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f330,plain,
    ( ! [X6,X4,X8,X7,X5] : k3_enumset1(X7,X8,X4,X5,X6) = k2_xboole_0(k2_tarski(X7,X8),k1_enumset1(X6,X5,X4))
    | ~ spl6_10
    | ~ spl6_29 ),
    inference(superposition,[],[f87,f265])).

fof(f265,plain,
    ( ! [X4,X5,X3] : k1_enumset1(X4,X5,X3) = k1_enumset1(X3,X5,X4)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f264])).

fof(f1977,plain,
    ( ~ spl6_83
    | spl6_15
    | ~ spl6_63 ),
    inference(avatar_split_clause,[],[f1141,f1117,f129,f1974])).

fof(f129,plain,
    ( spl6_15
  <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) = k4_enumset1(sK5,sK0,sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f1117,plain,
    ( spl6_63
  <=> ! [X9,X11,X7,X8,X10,X6] : k4_enumset1(X7,X8,X6,X9,X10,X11) = k4_enumset1(X6,X7,X8,X10,X11,X9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f1141,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK0,sK1,sK5,sK4,sK2,sK3)
    | spl6_15
    | ~ spl6_63 ),
    inference(superposition,[],[f131,f1118])).

fof(f1118,plain,
    ( ! [X6,X10,X8,X7,X11,X9] : k4_enumset1(X7,X8,X6,X9,X10,X11) = k4_enumset1(X6,X7,X8,X10,X11,X9)
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f1117])).

fof(f131,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK5,sK0,sK1,sK2,sK3,sK4)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f129])).

fof(f1119,plain,
    ( spl6_63
    | ~ spl6_43
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f597,f582,f558,f1117])).

fof(f558,plain,
    ( spl6_43
  <=> ! [X9,X11,X13,X10,X12,X14] : k4_enumset1(X9,X10,X11,X12,X13,X14) = k2_xboole_0(k1_enumset1(X11,X9,X10),k1_enumset1(X12,X13,X14)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f582,plain,
    ( spl6_44
  <=> ! [X16,X18,X20,X15,X17,X19] : k4_enumset1(X18,X19,X20,X15,X16,X17) = k2_xboole_0(k1_enumset1(X18,X19,X20),k1_enumset1(X17,X15,X16)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f597,plain,
    ( ! [X6,X10,X8,X7,X11,X9] : k4_enumset1(X7,X8,X6,X9,X10,X11) = k4_enumset1(X6,X7,X8,X10,X11,X9)
    | ~ spl6_43
    | ~ spl6_44 ),
    inference(superposition,[],[f583,f559])).

fof(f559,plain,
    ( ! [X14,X12,X10,X13,X11,X9] : k4_enumset1(X9,X10,X11,X12,X13,X14) = k2_xboole_0(k1_enumset1(X11,X9,X10),k1_enumset1(X12,X13,X14))
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f558])).

fof(f583,plain,
    ( ! [X19,X17,X15,X20,X18,X16] : k4_enumset1(X18,X19,X20,X15,X16,X17) = k2_xboole_0(k1_enumset1(X18,X19,X20),k1_enumset1(X17,X15,X16))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f582])).

fof(f904,plain,
    ( spl6_52
    | ~ spl6_9
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f315,f310,f78,f902])).

fof(f78,plain,
    ( spl6_9
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f310,plain,
    ( spl6_32
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X3,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X2,X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f315,plain,
    ( ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X7,X5)
    | ~ spl6_9
    | ~ spl6_32 ),
    inference(superposition,[],[f311,f79])).

fof(f79,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f78])).

fof(f311,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X3,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X2,X0,X1))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f310])).

fof(f584,plain,
    ( spl6_44
    | ~ spl6_13
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f221,f213,f106,f582])).

fof(f106,plain,
    ( spl6_13
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f213,plain,
    ( spl6_24
  <=> ! [X3,X5,X4] : k1_enumset1(X3,X4,X5) = k1_enumset1(X5,X3,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f221,plain,
    ( ! [X19,X17,X15,X20,X18,X16] : k4_enumset1(X18,X19,X20,X15,X16,X17) = k2_xboole_0(k1_enumset1(X18,X19,X20),k1_enumset1(X17,X15,X16))
    | ~ spl6_13
    | ~ spl6_24 ),
    inference(superposition,[],[f107,f214])).

fof(f214,plain,
    ( ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k1_enumset1(X5,X3,X4)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f213])).

fof(f107,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f106])).

fof(f560,plain,
    ( spl6_43
    | ~ spl6_13
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f220,f213,f106,f558])).

fof(f220,plain,
    ( ! [X14,X12,X10,X13,X11,X9] : k4_enumset1(X9,X10,X11,X12,X13,X14) = k2_xboole_0(k1_enumset1(X11,X9,X10),k1_enumset1(X12,X13,X14))
    | ~ spl6_13
    | ~ spl6_24 ),
    inference(superposition,[],[f107,f214])).

fof(f312,plain,
    ( spl6_32
    | ~ spl6_9
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f218,f213,f78,f310])).

fof(f218,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X3,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X2,X0,X1))
    | ~ spl6_9
    | ~ spl6_24 ),
    inference(superposition,[],[f79,f214])).

fof(f266,plain,
    ( spl6_29
    | ~ spl6_17
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f251,f246,f144,f264])).

fof(f144,plain,
    ( spl6_17
  <=> ! [X3,X5,X4] : k1_enumset1(X3,X4,X5) = k2_xboole_0(k1_tarski(X5),k2_tarski(X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f246,plain,
    ( spl6_27
  <=> ! [X1,X0,X2] : k1_enumset1(X2,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f251,plain,
    ( ! [X4,X5,X3] : k1_enumset1(X4,X5,X3) = k1_enumset1(X3,X5,X4)
    | ~ spl6_17
    | ~ spl6_27 ),
    inference(superposition,[],[f247,f145])).

fof(f145,plain,
    ( ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k2_xboole_0(k1_tarski(X5),k2_tarski(X3,X4))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f144])).

fof(f247,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X2,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X1,X0))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f246])).

fof(f248,plain,
    ( spl6_27
    | ~ spl6_7
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f200,f197,f62,f246])).

fof(f62,plain,
    ( spl6_7
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f197,plain,
    ( spl6_23
  <=> ! [X3,X2] : k2_tarski(X2,X3) = k2_tarski(X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f200,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X2,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X1,X0))
    | ~ spl6_7
    | ~ spl6_23 ),
    inference(superposition,[],[f63,f198])).

fof(f198,plain,
    ( ! [X2,X3] : k2_tarski(X2,X3) = k2_tarski(X3,X2)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f197])).

fof(f63,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f215,plain,
    ( spl6_24
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f137,f134,f66,f213])).

fof(f66,plain,
    ( spl6_8
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f134,plain,
    ( spl6_16
  <=> ! [X3,X5,X4] : k1_enumset1(X3,X4,X5) = k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f137,plain,
    ( ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k1_enumset1(X5,X3,X4)
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(superposition,[],[f135,f67])).

fof(f67,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f135,plain,
    ( ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f134])).

fof(f199,plain,
    ( spl6_23
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f122,f119,f45,f197])).

fof(f45,plain,
    ( spl6_4
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f119,plain,
    ( spl6_14
  <=> ! [X3,X2] : k2_xboole_0(k1_tarski(X3),k1_tarski(X2)) = k2_tarski(X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f122,plain,
    ( ! [X2,X3] : k2_tarski(X2,X3) = k2_tarski(X3,X2)
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(superposition,[],[f120,f46])).

fof(f46,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f120,plain,
    ( ! [X2,X3] : k2_xboole_0(k1_tarski(X3),k1_tarski(X2)) = k2_tarski(X2,X3)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f172,plain,
    ( spl6_20
    | ~ spl6_2
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f97,f90,f35,f170])).

fof(f35,plain,
    ( spl6_2
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f90,plain,
    ( spl6_11
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f97,plain,
    ( ! [X6,X8,X7,X5,X9] : k3_enumset1(X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X9),k2_enumset1(X5,X6,X7,X8))
    | ~ spl6_2
    | ~ spl6_11 ),
    inference(superposition,[],[f91,f36])).

fof(f36,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f91,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f90])).

fof(f146,plain,
    ( spl6_17
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f73,f66,f35,f144])).

fof(f73,plain,
    ( ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k2_xboole_0(k1_tarski(X5),k2_tarski(X3,X4))
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(superposition,[],[f67,f36])).

fof(f136,plain,
    ( spl6_16
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f69,f62,f35,f134])).

fof(f69,plain,
    ( ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3))
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(superposition,[],[f63,f36])).

fof(f132,plain,
    ( ~ spl6_15
    | spl6_6
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f111,f102,f57,f129])).

fof(f57,plain,
    ( spl6_6
  <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) = k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f111,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK5,sK0,sK1,sK2,sK3,sK4)
    | spl6_6
    | ~ spl6_12 ),
    inference(superposition,[],[f59,f103])).

fof(f59,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK0,sK1,sK2,sK3,sK4))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f121,plain,
    ( spl6_14
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f52,f45,f35,f119])).

fof(f52,plain,
    ( ! [X2,X3] : k2_xboole_0(k1_tarski(X3),k1_tarski(X2)) = k2_tarski(X2,X3)
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(superposition,[],[f46,f36])).

fof(f108,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f28,f106])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(f104,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f27,f102])).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f92,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f26,f90])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f88,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f25,f86])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(f80,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f24,f78])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f68,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f23,f66])).

fof(f23,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f64,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f22,f62])).

fof(f22,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f60,plain,
    ( ~ spl6_6
    | spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f38,f35,f30,f57])).

fof(f30,plain,
    ( spl6_1
  <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) = k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f38,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK0,sK1,sK2,sK3,sK4))
    | spl6_1
    | ~ spl6_2 ),
    inference(superposition,[],[f32,f36])).

fof(f32,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f47,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f37,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f18,f35])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f33,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:20:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (23062)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (23068)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (23063)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (23060)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (23073)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (23071)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (23065)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (23067)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (23070)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (23070)Refutation not found, incomplete strategy% (23070)------------------------------
% 0.21/0.49  % (23070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (23070)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (23070)Memory used [KB]: 10618
% 0.21/0.49  % (23070)Time elapsed: 0.070 s
% 0.21/0.49  % (23070)------------------------------
% 0.21/0.49  % (23070)------------------------------
% 0.21/0.49  % (23074)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (23069)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (23059)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (23064)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (23066)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (23076)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (23061)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (23072)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (23075)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 5.28/1.03  % (23063)Time limit reached!
% 5.28/1.03  % (23063)------------------------------
% 5.28/1.03  % (23063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.28/1.03  % (23063)Termination reason: Time limit
% 5.28/1.03  
% 5.28/1.03  % (23063)Memory used [KB]: 9083
% 5.28/1.03  % (23063)Time elapsed: 0.621 s
% 5.28/1.03  % (23063)------------------------------
% 5.28/1.03  % (23063)------------------------------
% 7.60/1.32  % (23064)Refutation found. Thanks to Tanya!
% 7.60/1.32  % SZS status Theorem for theBenchmark
% 7.60/1.32  % SZS output start Proof for theBenchmark
% 7.60/1.32  fof(f26354,plain,(
% 7.60/1.32    $false),
% 7.60/1.32    inference(avatar_sat_refutation,[],[f33,f37,f47,f60,f64,f68,f80,f88,f92,f104,f108,f121,f132,f136,f146,f172,f199,f215,f248,f266,f312,f560,f584,f904,f1119,f1977,f2245,f2685,f3587,f7001,f25180,f26258,f26353])).
% 7.60/1.32  fof(f26353,plain,(
% 7.60/1.32    spl6_83 | ~spl6_302 | ~spl6_316),
% 7.60/1.32    inference(avatar_contradiction_clause,[],[f26352])).
% 7.60/1.32  fof(f26352,plain,(
% 7.60/1.32    $false | (spl6_83 | ~spl6_302 | ~spl6_316)),
% 7.60/1.32    inference(subsumption_resolution,[],[f1976,f26327])).
% 7.60/1.32  fof(f26327,plain,(
% 7.60/1.32    ( ! [X39,X37,X41,X38,X36,X40] : (k4_enumset1(X36,X37,X38,X41,X40,X39) = k4_enumset1(X36,X37,X39,X40,X38,X41)) ) | (~spl6_302 | ~spl6_316)),
% 7.60/1.32    inference(superposition,[],[f26257,f25179])).
% 7.60/1.32  fof(f25179,plain,(
% 7.60/1.32    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X0,X1,X4,X3,X2))) ) | ~spl6_302),
% 7.60/1.32    inference(avatar_component_clause,[],[f25178])).
% 7.60/1.32  fof(f25178,plain,(
% 7.60/1.32    spl6_302 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X0,X1,X4,X3,X2))),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_302])])).
% 7.60/1.32  fof(f26257,plain,(
% 7.60/1.32    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X0,X3,X1,X2,X4))) ) | ~spl6_316),
% 7.60/1.32    inference(avatar_component_clause,[],[f26256])).
% 7.60/1.32  fof(f26256,plain,(
% 7.60/1.32    spl6_316 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X0,X3,X1,X2,X4))),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_316])])).
% 7.60/1.32  fof(f1976,plain,(
% 7.60/1.32    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK0,sK1,sK5,sK4,sK2,sK3) | spl6_83),
% 7.60/1.32    inference(avatar_component_clause,[],[f1974])).
% 7.60/1.32  fof(f1974,plain,(
% 7.60/1.32    spl6_83 <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) = k4_enumset1(sK0,sK1,sK5,sK4,sK2,sK3)),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).
% 7.60/1.32  fof(f26258,plain,(
% 7.60/1.32    spl6_316 | ~spl6_12 | ~spl6_174),
% 7.60/1.32    inference(avatar_split_clause,[],[f7040,f6999,f102,f26256])).
% 7.60/1.32  fof(f102,plain,(
% 7.60/1.32    spl6_12 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 7.60/1.32  fof(f6999,plain,(
% 7.60/1.32    spl6_174 <=> ! [X9,X5,X7,X8,X6] : k3_enumset1(X6,X7,X8,X9,X5) = k3_enumset1(X6,X9,X7,X8,X5)),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_174])])).
% 7.60/1.32  fof(f7040,plain,(
% 7.60/1.32    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X0,X3,X1,X2,X4))) ) | (~spl6_12 | ~spl6_174)),
% 7.60/1.32    inference(superposition,[],[f103,f7000])).
% 7.60/1.32  fof(f7000,plain,(
% 7.60/1.32    ( ! [X6,X8,X7,X5,X9] : (k3_enumset1(X6,X7,X8,X9,X5) = k3_enumset1(X6,X9,X7,X8,X5)) ) | ~spl6_174),
% 7.60/1.32    inference(avatar_component_clause,[],[f6999])).
% 7.60/1.32  fof(f103,plain,(
% 7.60/1.32    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) ) | ~spl6_12),
% 7.60/1.32    inference(avatar_component_clause,[],[f102])).
% 7.60/1.32  fof(f25180,plain,(
% 7.60/1.32    spl6_302 | ~spl6_12 | ~spl6_128),
% 7.60/1.32    inference(avatar_split_clause,[],[f3940,f3585,f102,f25178])).
% 7.60/1.32  fof(f3585,plain,(
% 7.60/1.32    spl6_128 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X4,X3,X2)),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_128])])).
% 7.60/1.32  fof(f3940,plain,(
% 7.60/1.32    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X0,X1,X4,X3,X2))) ) | (~spl6_12 | ~spl6_128)),
% 7.60/1.32    inference(superposition,[],[f103,f3586])).
% 7.60/1.32  fof(f3586,plain,(
% 7.60/1.32    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X4,X3,X2)) ) | ~spl6_128),
% 7.60/1.32    inference(avatar_component_clause,[],[f3585])).
% 7.60/1.32  fof(f7001,plain,(
% 7.60/1.32    spl6_174 | ~spl6_20 | ~spl6_111),
% 7.60/1.32    inference(avatar_split_clause,[],[f2690,f2683,f170,f6999])).
% 7.60/1.32  fof(f170,plain,(
% 7.60/1.32    spl6_20 <=> ! [X9,X5,X7,X8,X6] : k3_enumset1(X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X9),k2_enumset1(X5,X6,X7,X8))),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 7.60/1.32  fof(f2683,plain,(
% 7.60/1.32    spl6_111 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X2,X3,X1))),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).
% 7.60/1.32  fof(f2690,plain,(
% 7.60/1.32    ( ! [X6,X8,X7,X5,X9] : (k3_enumset1(X6,X7,X8,X9,X5) = k3_enumset1(X6,X9,X7,X8,X5)) ) | (~spl6_20 | ~spl6_111)),
% 7.60/1.32    inference(superposition,[],[f2684,f171])).
% 7.60/1.32  fof(f171,plain,(
% 7.60/1.32    ( ! [X6,X8,X7,X5,X9] : (k3_enumset1(X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X9),k2_enumset1(X5,X6,X7,X8))) ) | ~spl6_20),
% 7.60/1.32    inference(avatar_component_clause,[],[f170])).
% 7.60/1.32  fof(f2684,plain,(
% 7.60/1.32    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X2,X3,X1))) ) | ~spl6_111),
% 7.60/1.32    inference(avatar_component_clause,[],[f2683])).
% 7.60/1.32  fof(f3587,plain,(
% 7.60/1.32    spl6_128 | ~spl6_10 | ~spl6_97),
% 7.60/1.32    inference(avatar_split_clause,[],[f2256,f2243,f86,f3585])).
% 7.60/1.32  fof(f86,plain,(
% 7.60/1.32    spl6_10 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 7.60/1.32  fof(f2243,plain,(
% 7.60/1.32    spl6_97 <=> ! [X5,X7,X8,X4,X6] : k3_enumset1(X7,X8,X4,X5,X6) = k2_xboole_0(k2_tarski(X7,X8),k1_enumset1(X6,X5,X4))),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).
% 7.60/1.32  fof(f2256,plain,(
% 7.60/1.32    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X4,X3,X2)) ) | (~spl6_10 | ~spl6_97)),
% 7.60/1.32    inference(superposition,[],[f2244,f87])).
% 7.60/1.32  fof(f87,plain,(
% 7.60/1.32    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) ) | ~spl6_10),
% 7.60/1.32    inference(avatar_component_clause,[],[f86])).
% 7.60/1.32  fof(f2244,plain,(
% 7.60/1.32    ( ! [X6,X4,X8,X7,X5] : (k3_enumset1(X7,X8,X4,X5,X6) = k2_xboole_0(k2_tarski(X7,X8),k1_enumset1(X6,X5,X4))) ) | ~spl6_97),
% 7.60/1.32    inference(avatar_component_clause,[],[f2243])).
% 7.60/1.32  fof(f2685,plain,(
% 7.60/1.32    spl6_111 | ~spl6_20 | ~spl6_52),
% 7.60/1.32    inference(avatar_split_clause,[],[f907,f902,f170,f2683])).
% 7.60/1.32  fof(f902,plain,(
% 7.60/1.32    spl6_52 <=> ! [X5,X7,X4,X6] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X7,X5)),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 7.60/1.32  fof(f907,plain,(
% 7.60/1.32    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X2,X3,X1))) ) | (~spl6_20 | ~spl6_52)),
% 7.60/1.32    inference(superposition,[],[f171,f903])).
% 7.60/1.32  fof(f903,plain,(
% 7.60/1.32    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X7,X5)) ) | ~spl6_52),
% 7.60/1.32    inference(avatar_component_clause,[],[f902])).
% 7.60/1.32  fof(f2245,plain,(
% 7.60/1.32    spl6_97 | ~spl6_10 | ~spl6_29),
% 7.60/1.32    inference(avatar_split_clause,[],[f330,f264,f86,f2243])).
% 7.60/1.32  fof(f264,plain,(
% 7.60/1.32    spl6_29 <=> ! [X3,X5,X4] : k1_enumset1(X4,X5,X3) = k1_enumset1(X3,X5,X4)),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 7.60/1.32  fof(f330,plain,(
% 7.60/1.32    ( ! [X6,X4,X8,X7,X5] : (k3_enumset1(X7,X8,X4,X5,X6) = k2_xboole_0(k2_tarski(X7,X8),k1_enumset1(X6,X5,X4))) ) | (~spl6_10 | ~spl6_29)),
% 7.60/1.32    inference(superposition,[],[f87,f265])).
% 7.60/1.32  fof(f265,plain,(
% 7.60/1.32    ( ! [X4,X5,X3] : (k1_enumset1(X4,X5,X3) = k1_enumset1(X3,X5,X4)) ) | ~spl6_29),
% 7.60/1.32    inference(avatar_component_clause,[],[f264])).
% 7.60/1.32  fof(f1977,plain,(
% 7.60/1.32    ~spl6_83 | spl6_15 | ~spl6_63),
% 7.60/1.32    inference(avatar_split_clause,[],[f1141,f1117,f129,f1974])).
% 7.60/1.32  fof(f129,plain,(
% 7.60/1.32    spl6_15 <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) = k4_enumset1(sK5,sK0,sK1,sK2,sK3,sK4)),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 7.60/1.32  fof(f1117,plain,(
% 7.60/1.32    spl6_63 <=> ! [X9,X11,X7,X8,X10,X6] : k4_enumset1(X7,X8,X6,X9,X10,X11) = k4_enumset1(X6,X7,X8,X10,X11,X9)),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).
% 7.60/1.32  fof(f1141,plain,(
% 7.60/1.32    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK0,sK1,sK5,sK4,sK2,sK3) | (spl6_15 | ~spl6_63)),
% 7.60/1.32    inference(superposition,[],[f131,f1118])).
% 7.60/1.32  fof(f1118,plain,(
% 7.60/1.32    ( ! [X6,X10,X8,X7,X11,X9] : (k4_enumset1(X7,X8,X6,X9,X10,X11) = k4_enumset1(X6,X7,X8,X10,X11,X9)) ) | ~spl6_63),
% 7.60/1.32    inference(avatar_component_clause,[],[f1117])).
% 7.60/1.32  fof(f131,plain,(
% 7.60/1.32    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK5,sK0,sK1,sK2,sK3,sK4) | spl6_15),
% 7.60/1.32    inference(avatar_component_clause,[],[f129])).
% 7.60/1.32  fof(f1119,plain,(
% 7.60/1.32    spl6_63 | ~spl6_43 | ~spl6_44),
% 7.60/1.32    inference(avatar_split_clause,[],[f597,f582,f558,f1117])).
% 7.60/1.32  fof(f558,plain,(
% 7.60/1.32    spl6_43 <=> ! [X9,X11,X13,X10,X12,X14] : k4_enumset1(X9,X10,X11,X12,X13,X14) = k2_xboole_0(k1_enumset1(X11,X9,X10),k1_enumset1(X12,X13,X14))),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 7.60/1.32  fof(f582,plain,(
% 7.60/1.32    spl6_44 <=> ! [X16,X18,X20,X15,X17,X19] : k4_enumset1(X18,X19,X20,X15,X16,X17) = k2_xboole_0(k1_enumset1(X18,X19,X20),k1_enumset1(X17,X15,X16))),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 7.60/1.32  fof(f597,plain,(
% 7.60/1.32    ( ! [X6,X10,X8,X7,X11,X9] : (k4_enumset1(X7,X8,X6,X9,X10,X11) = k4_enumset1(X6,X7,X8,X10,X11,X9)) ) | (~spl6_43 | ~spl6_44)),
% 7.60/1.32    inference(superposition,[],[f583,f559])).
% 7.60/1.32  fof(f559,plain,(
% 7.60/1.32    ( ! [X14,X12,X10,X13,X11,X9] : (k4_enumset1(X9,X10,X11,X12,X13,X14) = k2_xboole_0(k1_enumset1(X11,X9,X10),k1_enumset1(X12,X13,X14))) ) | ~spl6_43),
% 7.60/1.32    inference(avatar_component_clause,[],[f558])).
% 7.60/1.32  fof(f583,plain,(
% 7.60/1.32    ( ! [X19,X17,X15,X20,X18,X16] : (k4_enumset1(X18,X19,X20,X15,X16,X17) = k2_xboole_0(k1_enumset1(X18,X19,X20),k1_enumset1(X17,X15,X16))) ) | ~spl6_44),
% 7.60/1.32    inference(avatar_component_clause,[],[f582])).
% 7.60/1.32  fof(f904,plain,(
% 7.60/1.32    spl6_52 | ~spl6_9 | ~spl6_32),
% 7.60/1.32    inference(avatar_split_clause,[],[f315,f310,f78,f902])).
% 7.60/1.32  fof(f78,plain,(
% 7.60/1.32    spl6_9 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 7.60/1.32  fof(f310,plain,(
% 7.60/1.32    spl6_32 <=> ! [X1,X3,X0,X2] : k2_enumset1(X3,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X2,X0,X1))),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 7.60/1.32  fof(f315,plain,(
% 7.60/1.32    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X7,X5)) ) | (~spl6_9 | ~spl6_32)),
% 7.60/1.32    inference(superposition,[],[f311,f79])).
% 7.60/1.32  fof(f79,plain,(
% 7.60/1.32    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) ) | ~spl6_9),
% 7.60/1.32    inference(avatar_component_clause,[],[f78])).
% 7.60/1.32  fof(f311,plain,(
% 7.60/1.32    ( ! [X2,X0,X3,X1] : (k2_enumset1(X3,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X2,X0,X1))) ) | ~spl6_32),
% 7.60/1.32    inference(avatar_component_clause,[],[f310])).
% 7.60/1.32  fof(f584,plain,(
% 7.60/1.32    spl6_44 | ~spl6_13 | ~spl6_24),
% 7.60/1.32    inference(avatar_split_clause,[],[f221,f213,f106,f582])).
% 7.60/1.32  fof(f106,plain,(
% 7.60/1.32    spl6_13 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 7.60/1.32  fof(f213,plain,(
% 7.60/1.32    spl6_24 <=> ! [X3,X5,X4] : k1_enumset1(X3,X4,X5) = k1_enumset1(X5,X3,X4)),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 7.60/1.32  fof(f221,plain,(
% 7.60/1.32    ( ! [X19,X17,X15,X20,X18,X16] : (k4_enumset1(X18,X19,X20,X15,X16,X17) = k2_xboole_0(k1_enumset1(X18,X19,X20),k1_enumset1(X17,X15,X16))) ) | (~spl6_13 | ~spl6_24)),
% 7.60/1.32    inference(superposition,[],[f107,f214])).
% 7.60/1.32  fof(f214,plain,(
% 7.60/1.32    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k1_enumset1(X5,X3,X4)) ) | ~spl6_24),
% 7.60/1.32    inference(avatar_component_clause,[],[f213])).
% 7.60/1.32  fof(f107,plain,(
% 7.60/1.32    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) ) | ~spl6_13),
% 7.60/1.32    inference(avatar_component_clause,[],[f106])).
% 7.60/1.32  fof(f560,plain,(
% 7.60/1.32    spl6_43 | ~spl6_13 | ~spl6_24),
% 7.60/1.32    inference(avatar_split_clause,[],[f220,f213,f106,f558])).
% 7.60/1.32  fof(f220,plain,(
% 7.60/1.32    ( ! [X14,X12,X10,X13,X11,X9] : (k4_enumset1(X9,X10,X11,X12,X13,X14) = k2_xboole_0(k1_enumset1(X11,X9,X10),k1_enumset1(X12,X13,X14))) ) | (~spl6_13 | ~spl6_24)),
% 7.60/1.32    inference(superposition,[],[f107,f214])).
% 7.60/1.32  fof(f312,plain,(
% 7.60/1.32    spl6_32 | ~spl6_9 | ~spl6_24),
% 7.60/1.32    inference(avatar_split_clause,[],[f218,f213,f78,f310])).
% 7.60/1.32  fof(f218,plain,(
% 7.60/1.32    ( ! [X2,X0,X3,X1] : (k2_enumset1(X3,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X2,X0,X1))) ) | (~spl6_9 | ~spl6_24)),
% 7.60/1.32    inference(superposition,[],[f79,f214])).
% 7.60/1.32  fof(f266,plain,(
% 7.60/1.32    spl6_29 | ~spl6_17 | ~spl6_27),
% 7.60/1.32    inference(avatar_split_clause,[],[f251,f246,f144,f264])).
% 7.60/1.32  fof(f144,plain,(
% 7.60/1.32    spl6_17 <=> ! [X3,X5,X4] : k1_enumset1(X3,X4,X5) = k2_xboole_0(k1_tarski(X5),k2_tarski(X3,X4))),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 7.60/1.32  fof(f246,plain,(
% 7.60/1.32    spl6_27 <=> ! [X1,X0,X2] : k1_enumset1(X2,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X1,X0))),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 7.60/1.32  fof(f251,plain,(
% 7.60/1.32    ( ! [X4,X5,X3] : (k1_enumset1(X4,X5,X3) = k1_enumset1(X3,X5,X4)) ) | (~spl6_17 | ~spl6_27)),
% 7.60/1.32    inference(superposition,[],[f247,f145])).
% 7.60/1.32  fof(f145,plain,(
% 7.60/1.32    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k2_xboole_0(k1_tarski(X5),k2_tarski(X3,X4))) ) | ~spl6_17),
% 7.60/1.32    inference(avatar_component_clause,[],[f144])).
% 7.60/1.32  fof(f247,plain,(
% 7.60/1.32    ( ! [X2,X0,X1] : (k1_enumset1(X2,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X1,X0))) ) | ~spl6_27),
% 7.60/1.32    inference(avatar_component_clause,[],[f246])).
% 7.60/1.32  fof(f248,plain,(
% 7.60/1.32    spl6_27 | ~spl6_7 | ~spl6_23),
% 7.60/1.32    inference(avatar_split_clause,[],[f200,f197,f62,f246])).
% 7.60/1.32  fof(f62,plain,(
% 7.60/1.32    spl6_7 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 7.60/1.32  fof(f197,plain,(
% 7.60/1.32    spl6_23 <=> ! [X3,X2] : k2_tarski(X2,X3) = k2_tarski(X3,X2)),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 7.60/1.32  fof(f200,plain,(
% 7.60/1.32    ( ! [X2,X0,X1] : (k1_enumset1(X2,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X1,X0))) ) | (~spl6_7 | ~spl6_23)),
% 7.60/1.32    inference(superposition,[],[f63,f198])).
% 7.60/1.32  fof(f198,plain,(
% 7.60/1.32    ( ! [X2,X3] : (k2_tarski(X2,X3) = k2_tarski(X3,X2)) ) | ~spl6_23),
% 7.60/1.32    inference(avatar_component_clause,[],[f197])).
% 7.60/1.32  fof(f63,plain,(
% 7.60/1.32    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) ) | ~spl6_7),
% 7.60/1.32    inference(avatar_component_clause,[],[f62])).
% 7.60/1.32  fof(f215,plain,(
% 7.60/1.32    spl6_24 | ~spl6_8 | ~spl6_16),
% 7.60/1.32    inference(avatar_split_clause,[],[f137,f134,f66,f213])).
% 7.60/1.32  fof(f66,plain,(
% 7.60/1.32    spl6_8 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 7.60/1.32  fof(f134,plain,(
% 7.60/1.32    spl6_16 <=> ! [X3,X5,X4] : k1_enumset1(X3,X4,X5) = k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3))),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 7.60/1.32  fof(f137,plain,(
% 7.60/1.32    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k1_enumset1(X5,X3,X4)) ) | (~spl6_8 | ~spl6_16)),
% 7.60/1.32    inference(superposition,[],[f135,f67])).
% 7.60/1.32  fof(f67,plain,(
% 7.60/1.32    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) ) | ~spl6_8),
% 7.60/1.32    inference(avatar_component_clause,[],[f66])).
% 7.60/1.32  fof(f135,plain,(
% 7.60/1.32    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3))) ) | ~spl6_16),
% 7.60/1.32    inference(avatar_component_clause,[],[f134])).
% 7.60/1.32  fof(f199,plain,(
% 7.60/1.32    spl6_23 | ~spl6_4 | ~spl6_14),
% 7.60/1.32    inference(avatar_split_clause,[],[f122,f119,f45,f197])).
% 7.60/1.32  fof(f45,plain,(
% 7.60/1.32    spl6_4 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 7.60/1.32  fof(f119,plain,(
% 7.60/1.32    spl6_14 <=> ! [X3,X2] : k2_xboole_0(k1_tarski(X3),k1_tarski(X2)) = k2_tarski(X2,X3)),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 7.60/1.32  fof(f122,plain,(
% 7.60/1.32    ( ! [X2,X3] : (k2_tarski(X2,X3) = k2_tarski(X3,X2)) ) | (~spl6_4 | ~spl6_14)),
% 7.60/1.32    inference(superposition,[],[f120,f46])).
% 7.60/1.32  fof(f46,plain,(
% 7.60/1.32    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ) | ~spl6_4),
% 7.60/1.32    inference(avatar_component_clause,[],[f45])).
% 7.60/1.32  fof(f120,plain,(
% 7.60/1.32    ( ! [X2,X3] : (k2_xboole_0(k1_tarski(X3),k1_tarski(X2)) = k2_tarski(X2,X3)) ) | ~spl6_14),
% 7.60/1.32    inference(avatar_component_clause,[],[f119])).
% 7.60/1.32  fof(f172,plain,(
% 7.60/1.32    spl6_20 | ~spl6_2 | ~spl6_11),
% 7.60/1.32    inference(avatar_split_clause,[],[f97,f90,f35,f170])).
% 7.60/1.32  fof(f35,plain,(
% 7.60/1.32    spl6_2 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 7.60/1.32  fof(f90,plain,(
% 7.60/1.32    spl6_11 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 7.60/1.32  fof(f97,plain,(
% 7.60/1.32    ( ! [X6,X8,X7,X5,X9] : (k3_enumset1(X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X9),k2_enumset1(X5,X6,X7,X8))) ) | (~spl6_2 | ~spl6_11)),
% 7.60/1.32    inference(superposition,[],[f91,f36])).
% 7.60/1.32  fof(f36,plain,(
% 7.60/1.32    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl6_2),
% 7.60/1.32    inference(avatar_component_clause,[],[f35])).
% 7.60/1.32  fof(f91,plain,(
% 7.60/1.32    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) ) | ~spl6_11),
% 7.60/1.32    inference(avatar_component_clause,[],[f90])).
% 7.60/1.32  fof(f146,plain,(
% 7.60/1.32    spl6_17 | ~spl6_2 | ~spl6_8),
% 7.60/1.32    inference(avatar_split_clause,[],[f73,f66,f35,f144])).
% 7.60/1.32  fof(f73,plain,(
% 7.60/1.32    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k2_xboole_0(k1_tarski(X5),k2_tarski(X3,X4))) ) | (~spl6_2 | ~spl6_8)),
% 7.60/1.32    inference(superposition,[],[f67,f36])).
% 7.60/1.32  fof(f136,plain,(
% 7.60/1.32    spl6_16 | ~spl6_2 | ~spl6_7),
% 7.60/1.32    inference(avatar_split_clause,[],[f69,f62,f35,f134])).
% 7.60/1.32  fof(f69,plain,(
% 7.60/1.32    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3))) ) | (~spl6_2 | ~spl6_7)),
% 7.60/1.32    inference(superposition,[],[f63,f36])).
% 7.60/1.32  fof(f132,plain,(
% 7.60/1.32    ~spl6_15 | spl6_6 | ~spl6_12),
% 7.60/1.32    inference(avatar_split_clause,[],[f111,f102,f57,f129])).
% 7.60/1.32  fof(f57,plain,(
% 7.60/1.32    spl6_6 <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) = k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK0,sK1,sK2,sK3,sK4))),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 7.60/1.32  fof(f111,plain,(
% 7.60/1.32    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK5,sK0,sK1,sK2,sK3,sK4) | (spl6_6 | ~spl6_12)),
% 7.60/1.32    inference(superposition,[],[f59,f103])).
% 7.60/1.32  fof(f59,plain,(
% 7.60/1.32    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) | spl6_6),
% 7.60/1.32    inference(avatar_component_clause,[],[f57])).
% 7.60/1.32  fof(f121,plain,(
% 7.60/1.32    spl6_14 | ~spl6_2 | ~spl6_4),
% 7.60/1.32    inference(avatar_split_clause,[],[f52,f45,f35,f119])).
% 7.60/1.32  fof(f52,plain,(
% 7.60/1.32    ( ! [X2,X3] : (k2_xboole_0(k1_tarski(X3),k1_tarski(X2)) = k2_tarski(X2,X3)) ) | (~spl6_2 | ~spl6_4)),
% 7.60/1.32    inference(superposition,[],[f46,f36])).
% 7.60/1.32  fof(f108,plain,(
% 7.60/1.32    spl6_13),
% 7.60/1.32    inference(avatar_split_clause,[],[f28,f106])).
% 7.60/1.32  fof(f28,plain,(
% 7.60/1.32    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 7.60/1.32    inference(cnf_transformation,[],[f4])).
% 7.60/1.32  fof(f4,axiom,(
% 7.60/1.32    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 7.60/1.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).
% 7.60/1.32  fof(f104,plain,(
% 7.60/1.32    spl6_12),
% 7.60/1.32    inference(avatar_split_clause,[],[f27,f102])).
% 7.60/1.32  fof(f27,plain,(
% 7.60/1.32    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 7.60/1.32    inference(cnf_transformation,[],[f11])).
% 7.60/1.32  fof(f11,axiom,(
% 7.60/1.32    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 7.60/1.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 7.60/1.32  fof(f92,plain,(
% 7.60/1.32    spl6_11),
% 7.60/1.32    inference(avatar_split_clause,[],[f26,f90])).
% 7.60/1.32  fof(f26,plain,(
% 7.60/1.32    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 7.60/1.32    inference(cnf_transformation,[],[f10])).
% 7.60/1.32  fof(f10,axiom,(
% 7.60/1.32    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 7.60/1.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 7.60/1.32  fof(f88,plain,(
% 7.60/1.32    spl6_10),
% 7.60/1.32    inference(avatar_split_clause,[],[f25,f86])).
% 7.60/1.32  fof(f25,plain,(
% 7.60/1.32    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 7.60/1.32    inference(cnf_transformation,[],[f9])).
% 7.60/1.32  fof(f9,axiom,(
% 7.60/1.32    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 7.60/1.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 7.60/1.32  fof(f80,plain,(
% 7.60/1.32    spl6_9),
% 7.60/1.32    inference(avatar_split_clause,[],[f24,f78])).
% 7.60/1.32  fof(f24,plain,(
% 7.60/1.32    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 7.60/1.32    inference(cnf_transformation,[],[f8])).
% 7.60/1.32  fof(f8,axiom,(
% 7.60/1.32    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 7.60/1.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 7.60/1.32  fof(f68,plain,(
% 7.60/1.32    spl6_8),
% 7.60/1.32    inference(avatar_split_clause,[],[f23,f66])).
% 7.60/1.32  fof(f23,plain,(
% 7.60/1.32    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 7.60/1.32    inference(cnf_transformation,[],[f7])).
% 7.60/1.32  fof(f7,axiom,(
% 7.60/1.32    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 7.60/1.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 7.60/1.32  fof(f64,plain,(
% 7.60/1.32    spl6_7),
% 7.60/1.32    inference(avatar_split_clause,[],[f22,f62])).
% 7.60/1.32  fof(f22,plain,(
% 7.60/1.32    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 7.60/1.32    inference(cnf_transformation,[],[f6])).
% 7.60/1.32  fof(f6,axiom,(
% 7.60/1.32    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 7.60/1.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 7.60/1.32  fof(f60,plain,(
% 7.60/1.32    ~spl6_6 | spl6_1 | ~spl6_2),
% 7.60/1.32    inference(avatar_split_clause,[],[f38,f35,f30,f57])).
% 7.60/1.32  fof(f30,plain,(
% 7.60/1.32    spl6_1 <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) = k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5))),
% 7.60/1.32    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 7.60/1.32  fof(f38,plain,(
% 7.60/1.32    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) | (spl6_1 | ~spl6_2)),
% 7.60/1.32    inference(superposition,[],[f32,f36])).
% 7.60/1.32  fof(f32,plain,(
% 7.60/1.32    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) | spl6_1),
% 7.60/1.32    inference(avatar_component_clause,[],[f30])).
% 7.60/1.32  fof(f47,plain,(
% 7.60/1.32    spl6_4),
% 7.60/1.32    inference(avatar_split_clause,[],[f20,f45])).
% 7.60/1.32  fof(f20,plain,(
% 7.60/1.32    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 7.60/1.32    inference(cnf_transformation,[],[f5])).
% 7.60/1.32  fof(f5,axiom,(
% 7.60/1.32    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 7.60/1.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 7.60/1.32  fof(f37,plain,(
% 7.60/1.32    spl6_2),
% 7.60/1.32    inference(avatar_split_clause,[],[f18,f35])).
% 7.60/1.32  fof(f18,plain,(
% 7.60/1.32    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.60/1.32    inference(cnf_transformation,[],[f1])).
% 7.60/1.32  fof(f1,axiom,(
% 7.60/1.32    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.60/1.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 7.60/1.32  fof(f33,plain,(
% 7.60/1.32    ~spl6_1),
% 7.60/1.32    inference(avatar_split_clause,[],[f17,f30])).
% 7.60/1.32  fof(f17,plain,(
% 7.60/1.32    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5))),
% 7.60/1.32    inference(cnf_transformation,[],[f16])).
% 7.60/1.32  fof(f16,plain,(
% 7.60/1.32    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5))),
% 7.60/1.32    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f14,f15])).
% 7.60/1.32  fof(f15,plain,(
% 7.60/1.32    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5))),
% 7.60/1.32    introduced(choice_axiom,[])).
% 7.60/1.32  fof(f14,plain,(
% 7.60/1.32    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 7.60/1.32    inference(ennf_transformation,[],[f13])).
% 7.60/1.32  fof(f13,negated_conjecture,(
% 7.60/1.32    ~! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 7.60/1.32    inference(negated_conjecture,[],[f12])).
% 7.60/1.32  fof(f12,conjecture,(
% 7.60/1.32    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 7.60/1.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).
% 7.60/1.32  % SZS output end Proof for theBenchmark
% 7.60/1.32  % (23064)------------------------------
% 7.60/1.32  % (23064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.60/1.32  % (23064)Termination reason: Refutation
% 7.60/1.32  
% 7.60/1.32  % (23064)Memory used [KB]: 17142
% 7.60/1.32  % (23064)Time elapsed: 0.873 s
% 7.60/1.32  % (23064)------------------------------
% 7.60/1.32  % (23064)------------------------------
% 7.60/1.33  % (23058)Success in time 0.963 s
%------------------------------------------------------------------------------
