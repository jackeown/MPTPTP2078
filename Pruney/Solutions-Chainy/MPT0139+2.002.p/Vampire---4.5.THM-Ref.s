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
% DateTime   : Thu Dec  3 12:33:11 EST 2020

% Result     : Theorem 4.13s
% Output     : Refutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 237 expanded)
%              Number of leaves         :   38 ( 125 expanded)
%              Depth                    :    6
%              Number of atoms          :  285 ( 493 expanded)
%              Number of equality atoms :  102 ( 206 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6083,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f33,f47,f51,f68,f72,f84,f88,f101,f121,f136,f146,f155,f165,f179,f189,f220,f238,f292,f416,f450,f474,f595,f978,f998,f1126,f2541,f5928,f5999,f6082])).

fof(f6082,plain,
    ( ~ spl6_57
    | spl6_74
    | ~ spl6_93
    | ~ spl6_94 ),
    inference(avatar_contradiction_clause,[],[f6081])).

fof(f6081,plain,
    ( $false
    | ~ spl6_57
    | spl6_74
    | ~ spl6_93
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f5968,f6066])).

fof(f6066,plain,
    ( ! [X6,X10,X8,X7,X11,X9] : k4_enumset1(X6,X9,X10,X11,X7,X8) = k4_enumset1(X6,X10,X7,X8,X9,X11)
    | ~ spl6_57
    | ~ spl6_94 ),
    inference(superposition,[],[f5998,f1125])).

fof(f1125,plain,
    ( ! [X21,X19,X17,X20,X18,X16] : k4_enumset1(X21,X16,X17,X18,X19,X20) = k2_xboole_0(k1_tarski(X21),k3_enumset1(X19,X20,X16,X17,X18))
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f1124])).

fof(f1124,plain,
    ( spl6_57
  <=> ! [X16,X18,X20,X17,X19,X21] : k4_enumset1(X21,X16,X17,X18,X19,X20) = k2_xboole_0(k1_tarski(X21),k3_enumset1(X19,X20,X16,X17,X18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f5998,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X1,X2,X3,X0,X4))
    | ~ spl6_94 ),
    inference(avatar_component_clause,[],[f5997])).

fof(f5997,plain,
    ( spl6_94
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X1,X2,X3,X0,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).

fof(f5968,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK0,sK2,sK4,sK5,sK1,sK3)
    | spl6_74
    | ~ spl6_93 ),
    inference(superposition,[],[f2540,f5927])).

fof(f5927,plain,
    ( ! [X28,X26,X24,X29,X27,X25] : k4_enumset1(X27,X28,X29,X24,X25,X26) = k4_enumset1(X24,X28,X29,X25,X26,X27)
    | ~ spl6_93 ),
    inference(avatar_component_clause,[],[f5926])).

fof(f5926,plain,
    ( spl6_93
  <=> ! [X25,X27,X29,X24,X26,X28] : k4_enumset1(X27,X28,X29,X24,X25,X26) = k4_enumset1(X24,X28,X29,X25,X26,X27) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).

fof(f2540,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK3,sK2,sK4,sK0,sK5,sK1)
    | spl6_74 ),
    inference(avatar_component_clause,[],[f2538])).

fof(f2538,plain,
    ( spl6_74
  <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) = k4_enumset1(sK3,sK2,sK4,sK0,sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f5999,plain,
    ( spl6_94
    | ~ spl6_10
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f383,f290,f82,f5997])).

fof(f82,plain,
    ( spl6_10
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f290,plain,
    ( spl6_29
  <=> ! [X9,X5,X7,X8,X6] : k3_enumset1(X6,X7,X8,X9,X5) = k3_enumset1(X7,X8,X9,X6,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f383,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X1,X2,X3,X0,X4))
    | ~ spl6_10
    | ~ spl6_29 ),
    inference(superposition,[],[f83,f291])).

fof(f291,plain,
    ( ! [X6,X8,X7,X5,X9] : k3_enumset1(X6,X7,X8,X9,X5) = k3_enumset1(X7,X8,X9,X6,X5)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f290])).

fof(f83,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f82])).

fof(f5928,plain,
    ( spl6_93
    | ~ spl6_21
    | ~ spl6_53 ),
    inference(avatar_split_clause,[],[f1007,f996,f187,f5926])).

fof(f187,plain,
    ( spl6_21
  <=> ! [X9,X11,X7,X8,X10,X6] : k4_enumset1(X6,X7,X8,X9,X10,X11) = k4_enumset1(X9,X10,X11,X6,X7,X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f996,plain,
    ( spl6_53
  <=> ! [X9,X11,X7,X8,X10,X6] : k4_enumset1(X11,X10,X6,X7,X8,X9) = k4_enumset1(X11,X7,X8,X9,X10,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f1007,plain,
    ( ! [X28,X26,X24,X29,X27,X25] : k4_enumset1(X27,X28,X29,X24,X25,X26) = k4_enumset1(X24,X28,X29,X25,X26,X27)
    | ~ spl6_21
    | ~ spl6_53 ),
    inference(superposition,[],[f997,f188])).

fof(f188,plain,
    ( ! [X6,X10,X8,X7,X11,X9] : k4_enumset1(X6,X7,X8,X9,X10,X11) = k4_enumset1(X9,X10,X11,X6,X7,X8)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f187])).

fof(f997,plain,
    ( ! [X6,X10,X8,X7,X11,X9] : k4_enumset1(X11,X10,X6,X7,X8,X9) = k4_enumset1(X11,X7,X8,X9,X10,X6)
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f996])).

fof(f2541,plain,
    ( ~ spl6_74
    | spl6_42
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f992,f976,f592,f2538])).

fof(f592,plain,
    ( spl6_42
  <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) = k4_enumset1(sK3,sK4,sK0,sK5,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f976,plain,
    ( spl6_52
  <=> ! [X9,X11,X7,X8,X10,X6] : k4_enumset1(X11,X6,X7,X8,X9,X10) = k4_enumset1(X11,X7,X8,X9,X10,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f992,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK3,sK2,sK4,sK0,sK5,sK1)
    | spl6_42
    | ~ spl6_52 ),
    inference(superposition,[],[f594,f977])).

fof(f977,plain,
    ( ! [X6,X10,X8,X7,X11,X9] : k4_enumset1(X11,X6,X7,X8,X9,X10) = k4_enumset1(X11,X7,X8,X9,X10,X6)
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f976])).

fof(f594,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK3,sK4,sK0,sK5,sK1,sK2)
    | spl6_42 ),
    inference(avatar_component_clause,[],[f592])).

fof(f1126,plain,
    ( spl6_57
    | ~ spl6_10
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f234,f218,f82,f1124])).

fof(f218,plain,
    ( spl6_24
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X4,X0,X1,X2,X3) = k3_enumset1(X1,X2,X3,X4,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f234,plain,
    ( ! [X21,X19,X17,X20,X18,X16] : k4_enumset1(X21,X16,X17,X18,X19,X20) = k2_xboole_0(k1_tarski(X21),k3_enumset1(X19,X20,X16,X17,X18))
    | ~ spl6_10
    | ~ spl6_24 ),
    inference(superposition,[],[f83,f219])).

fof(f219,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X4,X0,X1,X2,X3) = k3_enumset1(X1,X2,X3,X4,X0)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f218])).

fof(f998,plain,
    ( spl6_53
    | ~ spl6_34
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f457,f448,f414,f996])).

fof(f414,plain,
    ( spl6_34
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X4,X0,X1,X2,X3),k1_tarski(X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f448,plain,
    ( spl6_36
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X0),k1_tarski(X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f457,plain,
    ( ! [X6,X10,X8,X7,X11,X9] : k4_enumset1(X11,X10,X6,X7,X8,X9) = k4_enumset1(X11,X7,X8,X9,X10,X6)
    | ~ spl6_34
    | ~ spl6_36 ),
    inference(superposition,[],[f449,f415])).

fof(f415,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X4,X0,X1,X2,X3),k1_tarski(X5))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f414])).

fof(f449,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X0),k1_tarski(X5))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f448])).

fof(f978,plain,
    ( spl6_52
    | ~ spl6_17
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f423,f414,f144,f976])).

fof(f144,plain,
    ( spl6_17
  <=> ! [X9,X11,X7,X8,X10,X6] : k2_xboole_0(k3_enumset1(X7,X8,X9,X10,X11),k1_tarski(X6)) = k4_enumset1(X6,X7,X8,X9,X10,X11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f423,plain,
    ( ! [X6,X10,X8,X7,X11,X9] : k4_enumset1(X11,X6,X7,X8,X9,X10) = k4_enumset1(X11,X7,X8,X9,X10,X6)
    | ~ spl6_17
    | ~ spl6_34 ),
    inference(superposition,[],[f415,f145])).

fof(f145,plain,
    ( ! [X6,X10,X8,X7,X11,X9] : k2_xboole_0(k3_enumset1(X7,X8,X9,X10,X11),k1_tarski(X6)) = k4_enumset1(X6,X7,X8,X9,X10,X11)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f144])).

fof(f595,plain,
    ( ~ spl6_42
    | ~ spl6_21
    | spl6_38 ),
    inference(avatar_split_clause,[],[f490,f471,f187,f592])).

fof(f471,plain,
    ( spl6_38
  <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) = k4_enumset1(sK5,sK1,sK2,sK3,sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f490,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK3,sK4,sK0,sK5,sK1,sK2)
    | ~ spl6_21
    | spl6_38 ),
    inference(superposition,[],[f473,f188])).

fof(f473,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK5,sK1,sK2,sK3,sK4,sK0)
    | spl6_38 ),
    inference(avatar_component_clause,[],[f471])).

fof(f474,plain,
    ( ~ spl6_38
    | spl6_1
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f426,f414,f26,f471])).

fof(f26,plain,
    ( spl6_1
  <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) = k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f426,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK5,sK1,sK2,sK3,sK4,sK0)
    | spl6_1
    | ~ spl6_34 ),
    inference(superposition,[],[f28,f415])).

fof(f28,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f450,plain,
    ( spl6_36
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f184,f177,f144,f448])).

fof(f177,plain,
    ( spl6_20
  <=> ! [X9,X5,X7,X8,X6] : k3_enumset1(X5,X6,X7,X8,X9) = k3_enumset1(X9,X5,X6,X7,X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f184,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X0),k1_tarski(X5))
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(superposition,[],[f145,f178])).

fof(f178,plain,
    ( ! [X6,X8,X7,X5,X9] : k3_enumset1(X5,X6,X7,X8,X9) = k3_enumset1(X9,X5,X6,X7,X8)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f177])).

fof(f416,plain,
    ( spl6_34
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f182,f177,f144,f414])).

fof(f182,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X4,X0,X1,X2,X3),k1_tarski(X5))
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(superposition,[],[f145,f178])).

fof(f292,plain,
    ( spl6_29
    | ~ spl6_16
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f243,f236,f134,f290])).

fof(f134,plain,
    ( spl6_16
  <=> ! [X9,X5,X7,X8,X6] : k3_enumset1(X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X9),k2_enumset1(X5,X6,X7,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f236,plain,
    ( spl6_25
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X3,X0,X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f243,plain,
    ( ! [X6,X8,X7,X5,X9] : k3_enumset1(X6,X7,X8,X9,X5) = k3_enumset1(X7,X8,X9,X6,X5)
    | ~ spl6_16
    | ~ spl6_25 ),
    inference(superposition,[],[f237,f135])).

fof(f135,plain,
    ( ! [X6,X8,X7,X5,X9] : k3_enumset1(X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X9),k2_enumset1(X5,X6,X7,X8))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f134])).

fof(f237,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X3,X0,X1,X2))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f236])).

fof(f238,plain,
    ( spl6_25
    | ~ spl6_16
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f168,f163,f134,f236])).

fof(f163,plain,
    ( spl6_19
  <=> ! [X5,X7,X4,X6] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f168,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X3,X0,X1,X2))
    | ~ spl6_16
    | ~ spl6_19 ),
    inference(superposition,[],[f135,f164])).

fof(f164,plain,
    ( ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f163])).

fof(f220,plain,
    ( spl6_24
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f180,f177,f218])).

fof(f180,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X4,X0,X1,X2,X3) = k3_enumset1(X1,X2,X3,X4,X0)
    | ~ spl6_20 ),
    inference(superposition,[],[f178,f178])).

fof(f189,plain,
    ( spl6_21
    | ~ spl6_11
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f156,f153,f86,f187])).

fof(f86,plain,
    ( spl6_11
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f153,plain,
    ( spl6_18
  <=> ! [X9,X11,X7,X8,X10,X6] : k4_enumset1(X6,X7,X8,X9,X10,X11) = k2_xboole_0(k1_enumset1(X9,X10,X11),k1_enumset1(X6,X7,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f156,plain,
    ( ! [X6,X10,X8,X7,X11,X9] : k4_enumset1(X6,X7,X8,X9,X10,X11) = k4_enumset1(X9,X10,X11,X6,X7,X8)
    | ~ spl6_11
    | ~ spl6_18 ),
    inference(superposition,[],[f154,f87])).

fof(f87,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f86])).

fof(f154,plain,
    ( ! [X6,X10,X8,X7,X11,X9] : k4_enumset1(X6,X7,X8,X9,X10,X11) = k2_xboole_0(k1_enumset1(X9,X10,X11),k1_enumset1(X6,X7,X8))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f153])).

fof(f179,plain,
    ( spl6_20
    | ~ spl6_9
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f122,f119,f70,f177])).

fof(f70,plain,
    ( spl6_9
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f119,plain,
    ( spl6_14
  <=> ! [X9,X5,X7,X8,X6] : k2_xboole_0(k2_enumset1(X6,X7,X8,X9),k1_tarski(X5)) = k3_enumset1(X5,X6,X7,X8,X9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f122,plain,
    ( ! [X6,X8,X7,X5,X9] : k3_enumset1(X5,X6,X7,X8,X9) = k3_enumset1(X9,X5,X6,X7,X8)
    | ~ spl6_9
    | ~ spl6_14 ),
    inference(superposition,[],[f120,f71])).

fof(f71,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f120,plain,
    ( ! [X6,X8,X7,X5,X9] : k2_xboole_0(k2_enumset1(X6,X7,X8,X9),k1_tarski(X5)) = k3_enumset1(X5,X6,X7,X8,X9)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f165,plain,
    ( spl6_19
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f102,f99,f49,f163])).

fof(f49,plain,
    ( spl6_6
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f99,plain,
    ( spl6_12
  <=> ! [X5,X7,X4,X6] : k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f102,plain,
    ( ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6)
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(superposition,[],[f100,f50])).

fof(f50,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f100,plain,
    ( ! [X6,X4,X7,X5] : k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f99])).

fof(f155,plain,
    ( spl6_18
    | ~ spl6_2
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f94,f86,f31,f153])).

fof(f31,plain,
    ( spl6_2
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f94,plain,
    ( ! [X6,X10,X8,X7,X11,X9] : k4_enumset1(X6,X7,X8,X9,X10,X11) = k2_xboole_0(k1_enumset1(X9,X10,X11),k1_enumset1(X6,X7,X8))
    | ~ spl6_2
    | ~ spl6_11 ),
    inference(superposition,[],[f87,f32])).

fof(f32,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f146,plain,
    ( spl6_17
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f89,f82,f31,f144])).

fof(f89,plain,
    ( ! [X6,X10,X8,X7,X11,X9] : k2_xboole_0(k3_enumset1(X7,X8,X9,X10,X11),k1_tarski(X6)) = k4_enumset1(X6,X7,X8,X9,X10,X11)
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(superposition,[],[f83,f32])).

fof(f136,plain,
    ( spl6_16
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f77,f70,f31,f134])).

fof(f77,plain,
    ( ! [X6,X8,X7,X5,X9] : k3_enumset1(X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X9),k2_enumset1(X5,X6,X7,X8))
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(superposition,[],[f71,f32])).

fof(f121,plain,
    ( spl6_14
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f73,f66,f31,f119])).

fof(f66,plain,
    ( spl6_8
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f73,plain,
    ( ! [X6,X8,X7,X5,X9] : k2_xboole_0(k2_enumset1(X6,X7,X8,X9),k1_tarski(X5)) = k3_enumset1(X5,X6,X7,X8,X9)
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(superposition,[],[f67,f32])).

fof(f67,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f101,plain,
    ( spl6_12
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f57,f45,f31,f99])).

fof(f45,plain,
    ( spl6_5
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f57,plain,
    ( ! [X6,X4,X7,X5] : k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7)
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(superposition,[],[f46,f32])).

fof(f46,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f88,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f24,f86])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

fof(f84,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f23,f82])).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(f72,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f22,f70])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(f68,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f21,f66])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f51,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f20,f49])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f47,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f33,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f16,f31])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f29,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f15,f26])).

fof(f15,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:53:37 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.45  % (12991)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (12990)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (12992)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (13005)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (13000)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (12997)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (13004)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (12994)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (12996)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (13003)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (12999)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (12993)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.51  % (13001)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (13001)Refutation not found, incomplete strategy% (13001)------------------------------
% 0.22/0.51  % (13001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13001)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (13001)Memory used [KB]: 10618
% 0.22/0.51  % (13001)Time elapsed: 0.075 s
% 0.22/0.51  % (13001)------------------------------
% 0.22/0.51  % (13001)------------------------------
% 0.22/0.51  % (12995)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.51  % (12998)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.52  % (13002)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.53  % (13007)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.53  % (13006)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 4.13/0.91  % (12995)Refutation found. Thanks to Tanya!
% 4.13/0.91  % SZS status Theorem for theBenchmark
% 4.13/0.91  % SZS output start Proof for theBenchmark
% 4.13/0.91  fof(f6083,plain,(
% 4.13/0.91    $false),
% 4.13/0.91    inference(avatar_sat_refutation,[],[f29,f33,f47,f51,f68,f72,f84,f88,f101,f121,f136,f146,f155,f165,f179,f189,f220,f238,f292,f416,f450,f474,f595,f978,f998,f1126,f2541,f5928,f5999,f6082])).
% 4.13/0.91  fof(f6082,plain,(
% 4.13/0.91    ~spl6_57 | spl6_74 | ~spl6_93 | ~spl6_94),
% 4.13/0.91    inference(avatar_contradiction_clause,[],[f6081])).
% 4.13/0.91  fof(f6081,plain,(
% 4.13/0.91    $false | (~spl6_57 | spl6_74 | ~spl6_93 | ~spl6_94)),
% 4.13/0.91    inference(subsumption_resolution,[],[f5968,f6066])).
% 4.13/0.91  fof(f6066,plain,(
% 4.13/0.91    ( ! [X6,X10,X8,X7,X11,X9] : (k4_enumset1(X6,X9,X10,X11,X7,X8) = k4_enumset1(X6,X10,X7,X8,X9,X11)) ) | (~spl6_57 | ~spl6_94)),
% 4.13/0.91    inference(superposition,[],[f5998,f1125])).
% 4.13/0.91  fof(f1125,plain,(
% 4.13/0.91    ( ! [X21,X19,X17,X20,X18,X16] : (k4_enumset1(X21,X16,X17,X18,X19,X20) = k2_xboole_0(k1_tarski(X21),k3_enumset1(X19,X20,X16,X17,X18))) ) | ~spl6_57),
% 4.13/0.91    inference(avatar_component_clause,[],[f1124])).
% 4.13/0.91  fof(f1124,plain,(
% 4.13/0.91    spl6_57 <=> ! [X16,X18,X20,X17,X19,X21] : k4_enumset1(X21,X16,X17,X18,X19,X20) = k2_xboole_0(k1_tarski(X21),k3_enumset1(X19,X20,X16,X17,X18))),
% 4.13/0.91    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).
% 4.13/0.91  fof(f5998,plain,(
% 4.13/0.91    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X1,X2,X3,X0,X4))) ) | ~spl6_94),
% 4.13/0.91    inference(avatar_component_clause,[],[f5997])).
% 4.13/0.91  fof(f5997,plain,(
% 4.13/0.91    spl6_94 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X1,X2,X3,X0,X4))),
% 4.13/0.91    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).
% 4.13/0.91  fof(f5968,plain,(
% 4.13/0.91    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK0,sK2,sK4,sK5,sK1,sK3) | (spl6_74 | ~spl6_93)),
% 4.13/0.91    inference(superposition,[],[f2540,f5927])).
% 4.13/0.91  fof(f5927,plain,(
% 4.13/0.91    ( ! [X28,X26,X24,X29,X27,X25] : (k4_enumset1(X27,X28,X29,X24,X25,X26) = k4_enumset1(X24,X28,X29,X25,X26,X27)) ) | ~spl6_93),
% 4.13/0.91    inference(avatar_component_clause,[],[f5926])).
% 4.13/0.91  fof(f5926,plain,(
% 4.13/0.91    spl6_93 <=> ! [X25,X27,X29,X24,X26,X28] : k4_enumset1(X27,X28,X29,X24,X25,X26) = k4_enumset1(X24,X28,X29,X25,X26,X27)),
% 4.13/0.91    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).
% 4.13/0.91  fof(f2540,plain,(
% 4.13/0.91    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK3,sK2,sK4,sK0,sK5,sK1) | spl6_74),
% 4.13/0.91    inference(avatar_component_clause,[],[f2538])).
% 4.13/0.91  fof(f2538,plain,(
% 4.13/0.91    spl6_74 <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) = k4_enumset1(sK3,sK2,sK4,sK0,sK5,sK1)),
% 4.13/0.91    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).
% 4.13/0.91  fof(f5999,plain,(
% 4.13/0.91    spl6_94 | ~spl6_10 | ~spl6_29),
% 4.13/0.91    inference(avatar_split_clause,[],[f383,f290,f82,f5997])).
% 4.13/0.91  fof(f82,plain,(
% 4.13/0.91    spl6_10 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 4.13/0.91    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 4.13/0.91  fof(f290,plain,(
% 4.13/0.91    spl6_29 <=> ! [X9,X5,X7,X8,X6] : k3_enumset1(X6,X7,X8,X9,X5) = k3_enumset1(X7,X8,X9,X6,X5)),
% 4.13/0.91    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 4.13/0.91  fof(f383,plain,(
% 4.13/0.91    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X1,X2,X3,X0,X4))) ) | (~spl6_10 | ~spl6_29)),
% 4.13/0.91    inference(superposition,[],[f83,f291])).
% 4.13/0.91  fof(f291,plain,(
% 4.13/0.91    ( ! [X6,X8,X7,X5,X9] : (k3_enumset1(X6,X7,X8,X9,X5) = k3_enumset1(X7,X8,X9,X6,X5)) ) | ~spl6_29),
% 4.13/0.91    inference(avatar_component_clause,[],[f290])).
% 4.13/0.91  fof(f83,plain,(
% 4.13/0.91    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) ) | ~spl6_10),
% 4.13/0.91    inference(avatar_component_clause,[],[f82])).
% 4.13/0.91  fof(f5928,plain,(
% 4.13/0.91    spl6_93 | ~spl6_21 | ~spl6_53),
% 4.13/0.91    inference(avatar_split_clause,[],[f1007,f996,f187,f5926])).
% 4.13/0.91  fof(f187,plain,(
% 4.13/0.91    spl6_21 <=> ! [X9,X11,X7,X8,X10,X6] : k4_enumset1(X6,X7,X8,X9,X10,X11) = k4_enumset1(X9,X10,X11,X6,X7,X8)),
% 4.13/0.91    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 4.13/0.91  fof(f996,plain,(
% 4.13/0.91    spl6_53 <=> ! [X9,X11,X7,X8,X10,X6] : k4_enumset1(X11,X10,X6,X7,X8,X9) = k4_enumset1(X11,X7,X8,X9,X10,X6)),
% 4.13/0.91    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 4.13/0.91  fof(f1007,plain,(
% 4.13/0.91    ( ! [X28,X26,X24,X29,X27,X25] : (k4_enumset1(X27,X28,X29,X24,X25,X26) = k4_enumset1(X24,X28,X29,X25,X26,X27)) ) | (~spl6_21 | ~spl6_53)),
% 4.13/0.91    inference(superposition,[],[f997,f188])).
% 4.13/0.91  fof(f188,plain,(
% 4.13/0.91    ( ! [X6,X10,X8,X7,X11,X9] : (k4_enumset1(X6,X7,X8,X9,X10,X11) = k4_enumset1(X9,X10,X11,X6,X7,X8)) ) | ~spl6_21),
% 4.13/0.91    inference(avatar_component_clause,[],[f187])).
% 4.13/0.91  fof(f997,plain,(
% 4.13/0.91    ( ! [X6,X10,X8,X7,X11,X9] : (k4_enumset1(X11,X10,X6,X7,X8,X9) = k4_enumset1(X11,X7,X8,X9,X10,X6)) ) | ~spl6_53),
% 4.13/0.91    inference(avatar_component_clause,[],[f996])).
% 4.13/0.91  fof(f2541,plain,(
% 4.13/0.91    ~spl6_74 | spl6_42 | ~spl6_52),
% 4.13/0.91    inference(avatar_split_clause,[],[f992,f976,f592,f2538])).
% 4.13/0.91  fof(f592,plain,(
% 4.13/0.91    spl6_42 <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) = k4_enumset1(sK3,sK4,sK0,sK5,sK1,sK2)),
% 4.13/0.91    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 4.13/0.91  fof(f976,plain,(
% 4.13/0.91    spl6_52 <=> ! [X9,X11,X7,X8,X10,X6] : k4_enumset1(X11,X6,X7,X8,X9,X10) = k4_enumset1(X11,X7,X8,X9,X10,X6)),
% 4.13/0.91    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 4.13/0.91  fof(f992,plain,(
% 4.13/0.91    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK3,sK2,sK4,sK0,sK5,sK1) | (spl6_42 | ~spl6_52)),
% 4.13/0.91    inference(superposition,[],[f594,f977])).
% 4.13/0.91  fof(f977,plain,(
% 4.13/0.91    ( ! [X6,X10,X8,X7,X11,X9] : (k4_enumset1(X11,X6,X7,X8,X9,X10) = k4_enumset1(X11,X7,X8,X9,X10,X6)) ) | ~spl6_52),
% 4.13/0.91    inference(avatar_component_clause,[],[f976])).
% 4.13/0.91  fof(f594,plain,(
% 4.13/0.91    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK3,sK4,sK0,sK5,sK1,sK2) | spl6_42),
% 4.13/0.91    inference(avatar_component_clause,[],[f592])).
% 4.13/0.91  fof(f1126,plain,(
% 4.13/0.91    spl6_57 | ~spl6_10 | ~spl6_24),
% 4.13/0.91    inference(avatar_split_clause,[],[f234,f218,f82,f1124])).
% 4.13/0.91  fof(f218,plain,(
% 4.13/0.91    spl6_24 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X4,X0,X1,X2,X3) = k3_enumset1(X1,X2,X3,X4,X0)),
% 4.13/0.91    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 4.13/0.91  fof(f234,plain,(
% 4.13/0.91    ( ! [X21,X19,X17,X20,X18,X16] : (k4_enumset1(X21,X16,X17,X18,X19,X20) = k2_xboole_0(k1_tarski(X21),k3_enumset1(X19,X20,X16,X17,X18))) ) | (~spl6_10 | ~spl6_24)),
% 4.13/0.91    inference(superposition,[],[f83,f219])).
% 4.13/0.91  fof(f219,plain,(
% 4.13/0.91    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X4,X0,X1,X2,X3) = k3_enumset1(X1,X2,X3,X4,X0)) ) | ~spl6_24),
% 4.13/0.91    inference(avatar_component_clause,[],[f218])).
% 4.13/0.91  fof(f998,plain,(
% 4.13/0.91    spl6_53 | ~spl6_34 | ~spl6_36),
% 4.13/0.91    inference(avatar_split_clause,[],[f457,f448,f414,f996])).
% 4.13/0.91  fof(f414,plain,(
% 4.13/0.91    spl6_34 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X4,X0,X1,X2,X3),k1_tarski(X5))),
% 4.13/0.91    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 4.13/0.91  fof(f448,plain,(
% 4.13/0.91    spl6_36 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X0),k1_tarski(X5))),
% 4.13/0.91    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 4.13/0.91  fof(f457,plain,(
% 4.13/0.91    ( ! [X6,X10,X8,X7,X11,X9] : (k4_enumset1(X11,X10,X6,X7,X8,X9) = k4_enumset1(X11,X7,X8,X9,X10,X6)) ) | (~spl6_34 | ~spl6_36)),
% 4.13/0.91    inference(superposition,[],[f449,f415])).
% 4.13/0.91  fof(f415,plain,(
% 4.13/0.91    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X4,X0,X1,X2,X3),k1_tarski(X5))) ) | ~spl6_34),
% 4.13/0.91    inference(avatar_component_clause,[],[f414])).
% 4.13/0.91  fof(f449,plain,(
% 4.13/0.91    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X0),k1_tarski(X5))) ) | ~spl6_36),
% 4.13/0.91    inference(avatar_component_clause,[],[f448])).
% 4.13/0.91  fof(f978,plain,(
% 4.13/0.91    spl6_52 | ~spl6_17 | ~spl6_34),
% 4.13/0.91    inference(avatar_split_clause,[],[f423,f414,f144,f976])).
% 4.13/0.91  fof(f144,plain,(
% 4.13/0.91    spl6_17 <=> ! [X9,X11,X7,X8,X10,X6] : k2_xboole_0(k3_enumset1(X7,X8,X9,X10,X11),k1_tarski(X6)) = k4_enumset1(X6,X7,X8,X9,X10,X11)),
% 4.13/0.91    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 4.13/0.91  fof(f423,plain,(
% 4.13/0.91    ( ! [X6,X10,X8,X7,X11,X9] : (k4_enumset1(X11,X6,X7,X8,X9,X10) = k4_enumset1(X11,X7,X8,X9,X10,X6)) ) | (~spl6_17 | ~spl6_34)),
% 4.13/0.91    inference(superposition,[],[f415,f145])).
% 4.13/0.91  fof(f145,plain,(
% 4.13/0.91    ( ! [X6,X10,X8,X7,X11,X9] : (k2_xboole_0(k3_enumset1(X7,X8,X9,X10,X11),k1_tarski(X6)) = k4_enumset1(X6,X7,X8,X9,X10,X11)) ) | ~spl6_17),
% 4.13/0.91    inference(avatar_component_clause,[],[f144])).
% 4.13/0.91  fof(f595,plain,(
% 4.13/0.91    ~spl6_42 | ~spl6_21 | spl6_38),
% 4.13/0.91    inference(avatar_split_clause,[],[f490,f471,f187,f592])).
% 4.13/0.91  fof(f471,plain,(
% 4.13/0.91    spl6_38 <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) = k4_enumset1(sK5,sK1,sK2,sK3,sK4,sK0)),
% 4.13/0.91    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 4.13/0.91  fof(f490,plain,(
% 4.13/0.91    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK3,sK4,sK0,sK5,sK1,sK2) | (~spl6_21 | spl6_38)),
% 4.13/0.91    inference(superposition,[],[f473,f188])).
% 4.13/0.91  fof(f473,plain,(
% 4.13/0.91    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK5,sK1,sK2,sK3,sK4,sK0) | spl6_38),
% 4.13/0.91    inference(avatar_component_clause,[],[f471])).
% 4.13/0.91  fof(f474,plain,(
% 4.13/0.91    ~spl6_38 | spl6_1 | ~spl6_34),
% 4.13/0.91    inference(avatar_split_clause,[],[f426,f414,f26,f471])).
% 4.13/0.91  fof(f26,plain,(
% 4.13/0.91    spl6_1 <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) = k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5))),
% 4.13/0.91    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 4.13/0.91  fof(f426,plain,(
% 4.13/0.91    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK5,sK1,sK2,sK3,sK4,sK0) | (spl6_1 | ~spl6_34)),
% 4.13/0.91    inference(superposition,[],[f28,f415])).
% 4.13/0.91  fof(f28,plain,(
% 4.13/0.91    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) | spl6_1),
% 4.13/0.91    inference(avatar_component_clause,[],[f26])).
% 4.13/0.91  fof(f450,plain,(
% 4.13/0.91    spl6_36 | ~spl6_17 | ~spl6_20),
% 4.13/0.91    inference(avatar_split_clause,[],[f184,f177,f144,f448])).
% 4.13/0.91  fof(f177,plain,(
% 4.13/0.91    spl6_20 <=> ! [X9,X5,X7,X8,X6] : k3_enumset1(X5,X6,X7,X8,X9) = k3_enumset1(X9,X5,X6,X7,X8)),
% 4.13/0.91    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 4.13/0.91  fof(f184,plain,(
% 4.13/0.91    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X0),k1_tarski(X5))) ) | (~spl6_17 | ~spl6_20)),
% 4.13/0.91    inference(superposition,[],[f145,f178])).
% 4.13/0.91  fof(f178,plain,(
% 4.13/0.91    ( ! [X6,X8,X7,X5,X9] : (k3_enumset1(X5,X6,X7,X8,X9) = k3_enumset1(X9,X5,X6,X7,X8)) ) | ~spl6_20),
% 4.13/0.91    inference(avatar_component_clause,[],[f177])).
% 4.13/0.91  fof(f416,plain,(
% 4.13/0.91    spl6_34 | ~spl6_17 | ~spl6_20),
% 4.13/0.91    inference(avatar_split_clause,[],[f182,f177,f144,f414])).
% 4.13/0.91  fof(f182,plain,(
% 4.13/0.91    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X5,X0,X1,X2,X3,X4) = k2_xboole_0(k3_enumset1(X4,X0,X1,X2,X3),k1_tarski(X5))) ) | (~spl6_17 | ~spl6_20)),
% 4.13/0.91    inference(superposition,[],[f145,f178])).
% 4.13/0.91  fof(f292,plain,(
% 4.13/0.91    spl6_29 | ~spl6_16 | ~spl6_25),
% 4.13/0.91    inference(avatar_split_clause,[],[f243,f236,f134,f290])).
% 4.13/0.91  fof(f134,plain,(
% 4.13/0.91    spl6_16 <=> ! [X9,X5,X7,X8,X6] : k3_enumset1(X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X9),k2_enumset1(X5,X6,X7,X8))),
% 4.13/0.91    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 4.13/0.91  fof(f236,plain,(
% 4.13/0.91    spl6_25 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X3,X0,X1,X2))),
% 4.13/0.91    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 4.13/0.91  fof(f243,plain,(
% 4.13/0.91    ( ! [X6,X8,X7,X5,X9] : (k3_enumset1(X6,X7,X8,X9,X5) = k3_enumset1(X7,X8,X9,X6,X5)) ) | (~spl6_16 | ~spl6_25)),
% 4.13/0.91    inference(superposition,[],[f237,f135])).
% 4.13/0.91  fof(f135,plain,(
% 4.13/0.91    ( ! [X6,X8,X7,X5,X9] : (k3_enumset1(X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X9),k2_enumset1(X5,X6,X7,X8))) ) | ~spl6_16),
% 4.13/0.91    inference(avatar_component_clause,[],[f134])).
% 4.13/0.91  fof(f237,plain,(
% 4.13/0.91    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X3,X0,X1,X2))) ) | ~spl6_25),
% 4.13/0.91    inference(avatar_component_clause,[],[f236])).
% 4.13/0.91  fof(f238,plain,(
% 4.13/0.91    spl6_25 | ~spl6_16 | ~spl6_19),
% 4.13/0.91    inference(avatar_split_clause,[],[f168,f163,f134,f236])).
% 4.13/0.91  fof(f163,plain,(
% 4.13/0.91    spl6_19 <=> ! [X5,X7,X4,X6] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6)),
% 4.13/0.91    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 4.13/0.91  fof(f168,plain,(
% 4.13/0.91    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X3,X0,X1,X2))) ) | (~spl6_16 | ~spl6_19)),
% 4.13/0.91    inference(superposition,[],[f135,f164])).
% 4.13/0.91  fof(f164,plain,(
% 4.13/0.91    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6)) ) | ~spl6_19),
% 4.13/0.91    inference(avatar_component_clause,[],[f163])).
% 4.13/0.91  fof(f220,plain,(
% 4.13/0.91    spl6_24 | ~spl6_20),
% 4.13/0.91    inference(avatar_split_clause,[],[f180,f177,f218])).
% 4.13/0.91  fof(f180,plain,(
% 4.13/0.91    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X4,X0,X1,X2,X3) = k3_enumset1(X1,X2,X3,X4,X0)) ) | ~spl6_20),
% 4.13/0.91    inference(superposition,[],[f178,f178])).
% 4.13/0.91  fof(f189,plain,(
% 4.13/0.91    spl6_21 | ~spl6_11 | ~spl6_18),
% 4.13/0.91    inference(avatar_split_clause,[],[f156,f153,f86,f187])).
% 4.36/0.91  fof(f86,plain,(
% 4.36/0.91    spl6_11 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 4.36/0.91    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 4.36/0.91  fof(f153,plain,(
% 4.36/0.91    spl6_18 <=> ! [X9,X11,X7,X8,X10,X6] : k4_enumset1(X6,X7,X8,X9,X10,X11) = k2_xboole_0(k1_enumset1(X9,X10,X11),k1_enumset1(X6,X7,X8))),
% 4.36/0.91    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 4.36/0.92  fof(f156,plain,(
% 4.36/0.92    ( ! [X6,X10,X8,X7,X11,X9] : (k4_enumset1(X6,X7,X8,X9,X10,X11) = k4_enumset1(X9,X10,X11,X6,X7,X8)) ) | (~spl6_11 | ~spl6_18)),
% 4.36/0.92    inference(superposition,[],[f154,f87])).
% 4.36/0.92  fof(f87,plain,(
% 4.36/0.92    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) ) | ~spl6_11),
% 4.36/0.92    inference(avatar_component_clause,[],[f86])).
% 4.50/0.93  fof(f154,plain,(
% 4.50/0.93    ( ! [X6,X10,X8,X7,X11,X9] : (k4_enumset1(X6,X7,X8,X9,X10,X11) = k2_xboole_0(k1_enumset1(X9,X10,X11),k1_enumset1(X6,X7,X8))) ) | ~spl6_18),
% 4.50/0.93    inference(avatar_component_clause,[],[f153])).
% 4.50/0.93  fof(f179,plain,(
% 4.50/0.93    spl6_20 | ~spl6_9 | ~spl6_14),
% 4.50/0.93    inference(avatar_split_clause,[],[f122,f119,f70,f177])).
% 4.50/0.93  fof(f70,plain,(
% 4.50/0.93    spl6_9 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 4.50/0.93    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 4.50/0.93  fof(f119,plain,(
% 4.50/0.93    spl6_14 <=> ! [X9,X5,X7,X8,X6] : k2_xboole_0(k2_enumset1(X6,X7,X8,X9),k1_tarski(X5)) = k3_enumset1(X5,X6,X7,X8,X9)),
% 4.50/0.93    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 4.50/0.93  fof(f122,plain,(
% 4.50/0.93    ( ! [X6,X8,X7,X5,X9] : (k3_enumset1(X5,X6,X7,X8,X9) = k3_enumset1(X9,X5,X6,X7,X8)) ) | (~spl6_9 | ~spl6_14)),
% 4.50/0.93    inference(superposition,[],[f120,f71])).
% 4.50/0.93  fof(f71,plain,(
% 4.50/0.93    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) ) | ~spl6_9),
% 4.50/0.93    inference(avatar_component_clause,[],[f70])).
% 4.50/0.93  fof(f120,plain,(
% 4.50/0.93    ( ! [X6,X8,X7,X5,X9] : (k2_xboole_0(k2_enumset1(X6,X7,X8,X9),k1_tarski(X5)) = k3_enumset1(X5,X6,X7,X8,X9)) ) | ~spl6_14),
% 4.50/0.93    inference(avatar_component_clause,[],[f119])).
% 4.50/0.93  fof(f165,plain,(
% 4.50/0.93    spl6_19 | ~spl6_6 | ~spl6_12),
% 4.50/0.93    inference(avatar_split_clause,[],[f102,f99,f49,f163])).
% 4.50/0.93  fof(f49,plain,(
% 4.50/0.93    spl6_6 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 4.50/0.93    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 4.50/0.93  fof(f99,plain,(
% 4.50/0.93    spl6_12 <=> ! [X5,X7,X4,X6] : k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7)),
% 4.50/0.93    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 4.50/0.93  fof(f102,plain,(
% 4.50/0.93    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6)) ) | (~spl6_6 | ~spl6_12)),
% 4.50/0.93    inference(superposition,[],[f100,f50])).
% 4.50/0.93  fof(f50,plain,(
% 4.50/0.93    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) ) | ~spl6_6),
% 4.50/0.93    inference(avatar_component_clause,[],[f49])).
% 4.50/0.93  fof(f100,plain,(
% 4.50/0.93    ( ! [X6,X4,X7,X5] : (k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7)) ) | ~spl6_12),
% 4.50/0.93    inference(avatar_component_clause,[],[f99])).
% 4.50/0.93  fof(f155,plain,(
% 4.50/0.93    spl6_18 | ~spl6_2 | ~spl6_11),
% 4.50/0.93    inference(avatar_split_clause,[],[f94,f86,f31,f153])).
% 4.50/0.93  fof(f31,plain,(
% 4.50/0.93    spl6_2 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.50/0.93    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 4.50/0.93  fof(f94,plain,(
% 4.50/0.93    ( ! [X6,X10,X8,X7,X11,X9] : (k4_enumset1(X6,X7,X8,X9,X10,X11) = k2_xboole_0(k1_enumset1(X9,X10,X11),k1_enumset1(X6,X7,X8))) ) | (~spl6_2 | ~spl6_11)),
% 4.50/0.93    inference(superposition,[],[f87,f32])).
% 4.50/0.93  fof(f32,plain,(
% 4.50/0.93    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl6_2),
% 4.50/0.93    inference(avatar_component_clause,[],[f31])).
% 4.50/0.93  fof(f146,plain,(
% 4.50/0.93    spl6_17 | ~spl6_2 | ~spl6_10),
% 4.50/0.93    inference(avatar_split_clause,[],[f89,f82,f31,f144])).
% 4.50/0.93  fof(f89,plain,(
% 4.50/0.93    ( ! [X6,X10,X8,X7,X11,X9] : (k2_xboole_0(k3_enumset1(X7,X8,X9,X10,X11),k1_tarski(X6)) = k4_enumset1(X6,X7,X8,X9,X10,X11)) ) | (~spl6_2 | ~spl6_10)),
% 4.50/0.93    inference(superposition,[],[f83,f32])).
% 4.50/0.93  fof(f136,plain,(
% 4.50/0.93    spl6_16 | ~spl6_2 | ~spl6_9),
% 4.50/0.93    inference(avatar_split_clause,[],[f77,f70,f31,f134])).
% 4.50/0.93  fof(f77,plain,(
% 4.50/0.93    ( ! [X6,X8,X7,X5,X9] : (k3_enumset1(X5,X6,X7,X8,X9) = k2_xboole_0(k1_tarski(X9),k2_enumset1(X5,X6,X7,X8))) ) | (~spl6_2 | ~spl6_9)),
% 4.50/0.93    inference(superposition,[],[f71,f32])).
% 4.50/0.93  fof(f121,plain,(
% 4.50/0.93    spl6_14 | ~spl6_2 | ~spl6_8),
% 4.50/0.93    inference(avatar_split_clause,[],[f73,f66,f31,f119])).
% 4.50/0.93  fof(f66,plain,(
% 4.50/0.93    spl6_8 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 4.50/0.93    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 4.50/0.93  fof(f73,plain,(
% 4.50/0.93    ( ! [X6,X8,X7,X5,X9] : (k2_xboole_0(k2_enumset1(X6,X7,X8,X9),k1_tarski(X5)) = k3_enumset1(X5,X6,X7,X8,X9)) ) | (~spl6_2 | ~spl6_8)),
% 4.50/0.93    inference(superposition,[],[f67,f32])).
% 4.50/0.93  fof(f67,plain,(
% 4.50/0.93    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) ) | ~spl6_8),
% 4.50/0.93    inference(avatar_component_clause,[],[f66])).
% 4.50/0.93  fof(f101,plain,(
% 4.50/0.93    spl6_12 | ~spl6_2 | ~spl6_5),
% 4.50/0.93    inference(avatar_split_clause,[],[f57,f45,f31,f99])).
% 4.50/0.93  fof(f45,plain,(
% 4.50/0.93    spl6_5 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 4.50/0.93    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 4.50/0.93  fof(f57,plain,(
% 4.50/0.93    ( ! [X6,X4,X7,X5] : (k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7)) ) | (~spl6_2 | ~spl6_5)),
% 4.50/0.93    inference(superposition,[],[f46,f32])).
% 4.50/0.93  fof(f46,plain,(
% 4.50/0.93    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) ) | ~spl6_5),
% 4.50/0.93    inference(avatar_component_clause,[],[f45])).
% 4.50/0.93  fof(f88,plain,(
% 4.50/0.93    spl6_11),
% 4.50/0.93    inference(avatar_split_clause,[],[f24,f86])).
% 4.50/0.93  fof(f24,plain,(
% 4.50/0.93    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 4.50/0.93    inference(cnf_transformation,[],[f4])).
% 4.50/0.93  fof(f4,axiom,(
% 4.50/0.93    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 4.50/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).
% 4.50/0.93  fof(f84,plain,(
% 4.50/0.93    spl6_10),
% 4.50/0.93    inference(avatar_split_clause,[],[f23,f82])).
% 4.50/0.93  fof(f23,plain,(
% 4.50/0.93    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 4.50/0.93    inference(cnf_transformation,[],[f9])).
% 4.50/0.93  fof(f9,axiom,(
% 4.50/0.93    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 4.50/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).
% 4.50/0.93  fof(f72,plain,(
% 4.50/0.93    spl6_9),
% 4.50/0.93    inference(avatar_split_clause,[],[f22,f70])).
% 4.50/0.93  fof(f22,plain,(
% 4.50/0.93    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 4.50/0.93    inference(cnf_transformation,[],[f8])).
% 4.50/0.93  fof(f8,axiom,(
% 4.50/0.93    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 4.50/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).
% 4.50/0.93  fof(f68,plain,(
% 4.50/0.93    spl6_8),
% 4.50/0.93    inference(avatar_split_clause,[],[f21,f66])).
% 4.50/0.93  fof(f21,plain,(
% 4.50/0.93    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 4.50/0.93    inference(cnf_transformation,[],[f7])).
% 4.50/0.93  fof(f7,axiom,(
% 4.50/0.93    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 4.50/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 4.50/0.93  fof(f51,plain,(
% 4.50/0.93    spl6_6),
% 4.50/0.93    inference(avatar_split_clause,[],[f20,f49])).
% 4.50/0.93  fof(f20,plain,(
% 4.50/0.93    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 4.50/0.93    inference(cnf_transformation,[],[f6])).
% 4.50/0.93  fof(f6,axiom,(
% 4.50/0.93    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 4.50/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 4.50/0.93  fof(f47,plain,(
% 4.50/0.93    spl6_5),
% 4.50/0.93    inference(avatar_split_clause,[],[f19,f45])).
% 4.50/0.93  fof(f19,plain,(
% 4.50/0.93    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 4.50/0.93    inference(cnf_transformation,[],[f5])).
% 4.50/0.93  fof(f5,axiom,(
% 4.50/0.93    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 4.50/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 4.50/0.93  fof(f33,plain,(
% 4.50/0.93    spl6_2),
% 4.50/0.93    inference(avatar_split_clause,[],[f16,f31])).
% 4.50/0.93  fof(f16,plain,(
% 4.50/0.93    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.50/0.93    inference(cnf_transformation,[],[f1])).
% 4.50/0.93  fof(f1,axiom,(
% 4.50/0.93    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.50/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 4.50/0.93  fof(f29,plain,(
% 4.50/0.93    ~spl6_1),
% 4.50/0.93    inference(avatar_split_clause,[],[f15,f26])).
% 4.50/0.93  fof(f15,plain,(
% 4.50/0.93    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5))),
% 4.50/0.93    inference(cnf_transformation,[],[f14])).
% 4.50/0.93  fof(f14,plain,(
% 4.50/0.93    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5))),
% 4.50/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f13])).
% 4.50/0.93  fof(f13,plain,(
% 4.50/0.93    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5))),
% 4.50/0.93    introduced(choice_axiom,[])).
% 4.50/0.93  fof(f12,plain,(
% 4.50/0.93    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 4.50/0.93    inference(ennf_transformation,[],[f11])).
% 4.50/0.93  fof(f11,negated_conjecture,(
% 4.50/0.93    ~! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 4.50/0.93    inference(negated_conjecture,[],[f10])).
% 4.50/0.93  fof(f10,conjecture,(
% 4.50/0.93    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 4.50/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
% 4.50/0.93  % SZS output end Proof for theBenchmark
% 4.50/0.93  % (12995)------------------------------
% 4.50/0.93  % (12995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/0.93  % (12995)Termination reason: Refutation
% 4.50/0.93  
% 4.50/0.93  % (12995)Memory used [KB]: 11385
% 4.50/0.93  % (12995)Time elapsed: 0.486 s
% 4.50/0.93  % (12995)------------------------------
% 4.50/0.93  % (12995)------------------------------
% 4.50/0.93  % (12989)Success in time 0.564 s
%------------------------------------------------------------------------------
