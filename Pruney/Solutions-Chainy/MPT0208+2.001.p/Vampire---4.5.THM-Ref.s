%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:41 EST 2020

% Result     : Theorem 1.90s
% Output     : Refutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 178 expanded)
%              Number of leaves         :   33 (  92 expanded)
%              Depth                    :    6
%              Number of atoms          :  228 ( 364 expanded)
%              Number of equality atoms :   86 ( 154 expanded)
%              Maximal formula depth    :   12 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4458,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f49,f57,f61,f85,f90,f106,f110,f127,f131,f135,f156,f213,f293,f307,f355,f473,f501,f812,f908,f4262,f4394,f4457])).

fof(f4457,plain,
    ( spl9_62
    | ~ spl9_158
    | ~ spl9_161 ),
    inference(avatar_contradiction_clause,[],[f4456])).

fof(f4456,plain,
    ( $false
    | spl9_62
    | ~ spl9_158
    | ~ spl9_161 ),
    inference(subsumption_resolution,[],[f907,f4424])).

fof(f4424,plain,
    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : k7_enumset1(X17,X13,X14,X15,X16,X9,X10,X11,X12) = k7_enumset1(X17,X12,X13,X14,X15,X16,X9,X10,X11)
    | ~ spl9_158
    | ~ spl9_161 ),
    inference(superposition,[],[f4393,f4261])).

fof(f4261,plain,
    ( ! [X14,X21,X19,X17,X15,X13,X20,X18,X16] : k7_enumset1(X21,X13,X14,X15,X16,X17,X18,X19,X20) = k2_xboole_0(k6_enumset1(X17,X18,X19,X20,X13,X14,X15,X16),k1_tarski(X21))
    | ~ spl9_158 ),
    inference(avatar_component_clause,[],[f4260])).

fof(f4260,plain,
    ( spl9_158
  <=> ! [X16,X18,X20,X13,X15,X17,X19,X21,X14] : k7_enumset1(X21,X13,X14,X15,X16,X17,X18,X19,X20) = k2_xboole_0(k6_enumset1(X17,X18,X19,X20,X13,X14,X15,X16),k1_tarski(X21)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_158])])).

fof(f4393,plain,
    ( ! [X30,X37,X35,X33,X31,X29,X36,X34,X32] : k7_enumset1(X37,X29,X30,X31,X32,X33,X34,X35,X36) = k2_xboole_0(k6_enumset1(X34,X35,X36,X29,X30,X31,X32,X33),k1_tarski(X37))
    | ~ spl9_161 ),
    inference(avatar_component_clause,[],[f4392])).

fof(f4392,plain,
    ( spl9_161
  <=> ! [X32,X34,X36,X29,X31,X33,X35,X37,X30] : k7_enumset1(X37,X29,X30,X31,X32,X33,X34,X35,X36) = k2_xboole_0(k6_enumset1(X34,X35,X36,X29,X30,X31,X32,X33),k1_tarski(X37)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_161])])).

fof(f907,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK0,sK8,sK1,sK2,sK3,sK4,sK5,sK6,sK7)
    | spl9_62 ),
    inference(avatar_component_clause,[],[f905])).

fof(f905,plain,
    ( spl9_62
  <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k7_enumset1(sK0,sK8,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f4394,plain,
    ( spl9_161
    | ~ spl9_32
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f520,f499,f291,f4392])).

fof(f291,plain,
    ( spl9_32
  <=> ! [X16,X9,X11,X13,X15,X17,X10,X12,X14] : k2_xboole_0(k6_enumset1(X10,X11,X12,X13,X14,X15,X16,X17),k1_tarski(X9)) = k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f499,plain,
    ( spl9_46
  <=> ! [X9,X11,X13,X15,X8,X10,X12,X14] : k6_enumset1(X12,X13,X14,X15,X8,X9,X10,X11) = k6_enumset1(X9,X10,X11,X12,X13,X14,X15,X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f520,plain,
    ( ! [X30,X37,X35,X33,X31,X29,X36,X34,X32] : k7_enumset1(X37,X29,X30,X31,X32,X33,X34,X35,X36) = k2_xboole_0(k6_enumset1(X34,X35,X36,X29,X30,X31,X32,X33),k1_tarski(X37))
    | ~ spl9_32
    | ~ spl9_46 ),
    inference(superposition,[],[f292,f500])).

fof(f500,plain,
    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] : k6_enumset1(X12,X13,X14,X15,X8,X9,X10,X11) = k6_enumset1(X9,X10,X11,X12,X13,X14,X15,X8)
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f499])).

fof(f292,plain,
    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : k2_xboole_0(k6_enumset1(X10,X11,X12,X13,X14,X15,X16,X17),k1_tarski(X9)) = k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17)
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f291])).

fof(f4262,plain,
    ( spl9_158
    | ~ spl9_32
    | ~ spl9_45 ),
    inference(avatar_split_clause,[],[f484,f471,f291,f4260])).

fof(f471,plain,
    ( spl9_45
  <=> ! [X9,X11,X13,X15,X8,X10,X12,X14] : k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15) = k6_enumset1(X12,X13,X14,X15,X8,X9,X10,X11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).

fof(f484,plain,
    ( ! [X14,X21,X19,X17,X15,X13,X20,X18,X16] : k7_enumset1(X21,X13,X14,X15,X16,X17,X18,X19,X20) = k2_xboole_0(k6_enumset1(X17,X18,X19,X20,X13,X14,X15,X16),k1_tarski(X21))
    | ~ spl9_32
    | ~ spl9_45 ),
    inference(superposition,[],[f292,f472])).

fof(f472,plain,
    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] : k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15) = k6_enumset1(X12,X13,X14,X15,X8,X9,X10,X11)
    | ~ spl9_45 ),
    inference(avatar_component_clause,[],[f471])).

fof(f908,plain,
    ( ~ spl9_62
    | spl9_20
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f821,f810,f153,f905])).

fof(f153,plain,
    ( spl9_20
  <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k7_enumset1(sK8,sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f810,plain,
    ( spl9_58
  <=> ! [X16,X9,X11,X13,X15,X17,X10,X12,X14] : k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) = k7_enumset1(X10,X9,X11,X12,X13,X14,X15,X16,X17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).

fof(f821,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK0,sK8,sK1,sK2,sK3,sK4,sK5,sK6,sK7)
    | spl9_20
    | ~ spl9_58 ),
    inference(superposition,[],[f155,f811])).

fof(f811,plain,
    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) = k7_enumset1(X10,X9,X11,X12,X13,X14,X15,X16,X17)
    | ~ spl9_58 ),
    inference(avatar_component_clause,[],[f810])).

fof(f155,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK8,sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)
    | spl9_20 ),
    inference(avatar_component_clause,[],[f153])).

fof(f812,plain,
    ( spl9_58
    | ~ spl9_18
    | ~ spl9_33 ),
    inference(avatar_split_clause,[],[f321,f305,f129,f810])).

fof(f129,plain,
    ( spl9_18
  <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f305,plain,
    ( spl9_33
  <=> ! [X16,X9,X11,X13,X15,X8,X10,X12,X14] : k7_enumset1(X8,X9,X10,X11,X12,X13,X14,X15,X16) = k2_xboole_0(k2_tarski(X9,X8),k5_enumset1(X10,X11,X12,X13,X14,X15,X16)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f321,plain,
    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) = k7_enumset1(X10,X9,X11,X12,X13,X14,X15,X16,X17)
    | ~ spl9_18
    | ~ spl9_33 ),
    inference(superposition,[],[f306,f130])).

fof(f130,plain,
    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f129])).

fof(f306,plain,
    ( ! [X14,X12,X10,X8,X15,X13,X11,X9,X16] : k7_enumset1(X8,X9,X10,X11,X12,X13,X14,X15,X16) = k2_xboole_0(k2_tarski(X9,X8),k5_enumset1(X10,X11,X12,X13,X14,X15,X16))
    | ~ spl9_33 ),
    inference(avatar_component_clause,[],[f305])).

fof(f501,plain,
    ( spl9_46
    | ~ spl9_25
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f358,f353,f211,f499])).

fof(f211,plain,
    ( spl9_25
  <=> ! [X9,X11,X13,X15,X8,X10,X12,X14] : k2_xboole_0(k2_enumset1(X12,X13,X14,X15),k2_enumset1(X8,X9,X10,X11)) = k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f353,plain,
    ( spl9_36
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f358,plain,
    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] : k6_enumset1(X12,X13,X14,X15,X8,X9,X10,X11) = k6_enumset1(X9,X10,X11,X12,X13,X14,X15,X8)
    | ~ spl9_25
    | ~ spl9_36 ),
    inference(superposition,[],[f354,f212])).

fof(f212,plain,
    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] : k2_xboole_0(k2_enumset1(X12,X13,X14,X15),k2_enumset1(X8,X9,X10,X11)) = k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15)
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f211])).

fof(f354,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f353])).

fof(f473,plain,
    ( spl9_45
    | ~ spl9_15
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f216,f211,f104,f471])).

fof(f104,plain,
    ( spl9_15
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f216,plain,
    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] : k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15) = k6_enumset1(X12,X13,X14,X15,X8,X9,X10,X11)
    | ~ spl9_15
    | ~ spl9_25 ),
    inference(superposition,[],[f212,f105])).

fof(f105,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f104])).

fof(f355,plain,
    ( spl9_36
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f163,f133,f129,f108,f83,f59,f47,f353])).

fof(f47,plain,
    ( spl9_2
  <=> ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f59,plain,
    ( spl9_5
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f83,plain,
    ( spl9_10
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f108,plain,
    ( spl9_16
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f133,plain,
    ( spl9_19
  <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f163,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_19 ),
    inference(forward_demodulation,[],[f157,f151])).

fof(f151,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(forward_demodulation,[],[f143,f119])).

fof(f119,plain,
    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] : k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15) = k2_xboole_0(k1_tarski(X15),k5_enumset1(X8,X9,X10,X11,X12,X13,X14))
    | ~ spl9_5
    | ~ spl9_16 ),
    inference(superposition,[],[f109,f60])).

fof(f60,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f109,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f108])).

fof(f143,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))
    | ~ spl9_2
    | ~ spl9_18 ),
    inference(superposition,[],[f130,f48])).

fof(f48,plain,
    ( ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f157,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)
    | ~ spl9_10
    | ~ spl9_19 ),
    inference(superposition,[],[f134,f84])).

fof(f84,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f83])).

fof(f134,plain,
    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f133])).

fof(f307,plain,
    ( spl9_33
    | ~ spl9_4
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f144,f129,f55,f305])).

fof(f55,plain,
    ( spl9_4
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f144,plain,
    ( ! [X14,X12,X10,X8,X15,X13,X11,X9,X16] : k7_enumset1(X8,X9,X10,X11,X12,X13,X14,X15,X16) = k2_xboole_0(k2_tarski(X9,X8),k5_enumset1(X10,X11,X12,X13,X14,X15,X16))
    | ~ spl9_4
    | ~ spl9_18 ),
    inference(superposition,[],[f130,f56])).

fof(f56,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f293,plain,
    ( spl9_32
    | ~ spl9_5
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f137,f125,f59,f291])).

fof(f125,plain,
    ( spl9_17
  <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f137,plain,
    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : k2_xboole_0(k6_enumset1(X10,X11,X12,X13,X14,X15,X16,X17),k1_tarski(X9)) = k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17)
    | ~ spl9_5
    | ~ spl9_17 ),
    inference(superposition,[],[f126,f60])).

fof(f126,plain,
    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f125])).

fof(f213,plain,
    ( spl9_25
    | ~ spl9_5
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f113,f104,f59,f211])).

fof(f113,plain,
    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] : k2_xboole_0(k2_enumset1(X12,X13,X14,X15),k2_enumset1(X8,X9,X10,X11)) = k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15)
    | ~ spl9_5
    | ~ spl9_15 ),
    inference(superposition,[],[f105,f60])).

fof(f156,plain,
    ( ~ spl9_20
    | spl9_11
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f139,f125,f87,f153])).

fof(f87,plain,
    ( spl9_11
  <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k2_xboole_0(k1_tarski(sK8),k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f139,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK8,sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)
    | spl9_11
    | ~ spl9_17 ),
    inference(superposition,[],[f89,f126])).

fof(f89,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK8),k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7))
    | spl9_11 ),
    inference(avatar_component_clause,[],[f87])).

fof(f135,plain,(
    spl9_19 ),
    inference(avatar_split_clause,[],[f40,f133])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

fof(f131,plain,(
    spl9_18 ),
    inference(avatar_split_clause,[],[f39,f129])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_enumset1)).

fof(f127,plain,(
    spl9_17 ),
    inference(avatar_split_clause,[],[f38,f125])).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).

fof(f110,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f37,f108])).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(f106,plain,(
    spl9_15 ),
    inference(avatar_split_clause,[],[f36,f104])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(f90,plain,
    ( ~ spl9_11
    | spl9_1
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f66,f59,f42,f87])).

fof(f42,plain,
    ( spl9_1
  <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f66,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK8),k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7))
    | spl9_1
    | ~ spl9_5 ),
    inference(superposition,[],[f44,f60])).

fof(f44,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f85,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f32,f83])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f61,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f27,f59])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f57,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f26,f55])).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f49,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f24,f47])).

fof(f24,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f23,f42])).

fof(f23,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:42:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.40  % (32725)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.45  % (32714)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.46  % (32723)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.46  % (32715)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.46  % (32724)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.47  % (32726)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.47  % (32713)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.47  % (32718)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.47  % (32717)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.48  % (32720)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.48  % (32724)Refutation not found, incomplete strategy% (32724)------------------------------
% 0.19/0.48  % (32724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (32724)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.48  
% 0.19/0.48  % (32724)Memory used [KB]: 10618
% 0.19/0.48  % (32724)Time elapsed: 0.063 s
% 0.19/0.48  % (32724)------------------------------
% 0.19/0.48  % (32724)------------------------------
% 0.19/0.48  % (32721)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.49  % (32730)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.50  % (32719)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.50  % (32716)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.50  % (32727)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.50  % (32722)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.52  % (32728)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.52  % (32729)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.90/0.59  % (32718)Refutation found. Thanks to Tanya!
% 1.90/0.59  % SZS status Theorem for theBenchmark
% 1.90/0.59  % SZS output start Proof for theBenchmark
% 1.90/0.60  fof(f4458,plain,(
% 1.90/0.60    $false),
% 1.90/0.60    inference(avatar_sat_refutation,[],[f45,f49,f57,f61,f85,f90,f106,f110,f127,f131,f135,f156,f213,f293,f307,f355,f473,f501,f812,f908,f4262,f4394,f4457])).
% 1.90/0.60  fof(f4457,plain,(
% 1.90/0.60    spl9_62 | ~spl9_158 | ~spl9_161),
% 1.90/0.60    inference(avatar_contradiction_clause,[],[f4456])).
% 1.90/0.60  fof(f4456,plain,(
% 1.90/0.60    $false | (spl9_62 | ~spl9_158 | ~spl9_161)),
% 1.90/0.60    inference(subsumption_resolution,[],[f907,f4424])).
% 1.90/0.60  fof(f4424,plain,(
% 1.90/0.60    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : (k7_enumset1(X17,X13,X14,X15,X16,X9,X10,X11,X12) = k7_enumset1(X17,X12,X13,X14,X15,X16,X9,X10,X11)) ) | (~spl9_158 | ~spl9_161)),
% 1.90/0.60    inference(superposition,[],[f4393,f4261])).
% 1.90/0.60  fof(f4261,plain,(
% 1.90/0.60    ( ! [X14,X21,X19,X17,X15,X13,X20,X18,X16] : (k7_enumset1(X21,X13,X14,X15,X16,X17,X18,X19,X20) = k2_xboole_0(k6_enumset1(X17,X18,X19,X20,X13,X14,X15,X16),k1_tarski(X21))) ) | ~spl9_158),
% 1.90/0.60    inference(avatar_component_clause,[],[f4260])).
% 1.90/0.60  fof(f4260,plain,(
% 1.90/0.60    spl9_158 <=> ! [X16,X18,X20,X13,X15,X17,X19,X21,X14] : k7_enumset1(X21,X13,X14,X15,X16,X17,X18,X19,X20) = k2_xboole_0(k6_enumset1(X17,X18,X19,X20,X13,X14,X15,X16),k1_tarski(X21))),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_158])])).
% 1.90/0.60  fof(f4393,plain,(
% 1.90/0.60    ( ! [X30,X37,X35,X33,X31,X29,X36,X34,X32] : (k7_enumset1(X37,X29,X30,X31,X32,X33,X34,X35,X36) = k2_xboole_0(k6_enumset1(X34,X35,X36,X29,X30,X31,X32,X33),k1_tarski(X37))) ) | ~spl9_161),
% 1.90/0.60    inference(avatar_component_clause,[],[f4392])).
% 1.90/0.60  fof(f4392,plain,(
% 1.90/0.60    spl9_161 <=> ! [X32,X34,X36,X29,X31,X33,X35,X37,X30] : k7_enumset1(X37,X29,X30,X31,X32,X33,X34,X35,X36) = k2_xboole_0(k6_enumset1(X34,X35,X36,X29,X30,X31,X32,X33),k1_tarski(X37))),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_161])])).
% 1.90/0.60  fof(f907,plain,(
% 1.90/0.60    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK0,sK8,sK1,sK2,sK3,sK4,sK5,sK6,sK7) | spl9_62),
% 1.90/0.60    inference(avatar_component_clause,[],[f905])).
% 1.90/0.60  fof(f905,plain,(
% 1.90/0.60    spl9_62 <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k7_enumset1(sK0,sK8,sK1,sK2,sK3,sK4,sK5,sK6,sK7)),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).
% 1.90/0.60  fof(f4394,plain,(
% 1.90/0.60    spl9_161 | ~spl9_32 | ~spl9_46),
% 1.90/0.60    inference(avatar_split_clause,[],[f520,f499,f291,f4392])).
% 1.90/0.60  fof(f291,plain,(
% 1.90/0.60    spl9_32 <=> ! [X16,X9,X11,X13,X15,X17,X10,X12,X14] : k2_xboole_0(k6_enumset1(X10,X11,X12,X13,X14,X15,X16,X17),k1_tarski(X9)) = k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17)),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 1.90/0.60  fof(f499,plain,(
% 1.90/0.60    spl9_46 <=> ! [X9,X11,X13,X15,X8,X10,X12,X14] : k6_enumset1(X12,X13,X14,X15,X8,X9,X10,X11) = k6_enumset1(X9,X10,X11,X12,X13,X14,X15,X8)),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).
% 1.90/0.60  fof(f520,plain,(
% 1.90/0.60    ( ! [X30,X37,X35,X33,X31,X29,X36,X34,X32] : (k7_enumset1(X37,X29,X30,X31,X32,X33,X34,X35,X36) = k2_xboole_0(k6_enumset1(X34,X35,X36,X29,X30,X31,X32,X33),k1_tarski(X37))) ) | (~spl9_32 | ~spl9_46)),
% 1.90/0.60    inference(superposition,[],[f292,f500])).
% 1.90/0.60  fof(f500,plain,(
% 1.90/0.60    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] : (k6_enumset1(X12,X13,X14,X15,X8,X9,X10,X11) = k6_enumset1(X9,X10,X11,X12,X13,X14,X15,X8)) ) | ~spl9_46),
% 1.90/0.60    inference(avatar_component_clause,[],[f499])).
% 1.90/0.60  fof(f292,plain,(
% 1.90/0.60    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : (k2_xboole_0(k6_enumset1(X10,X11,X12,X13,X14,X15,X16,X17),k1_tarski(X9)) = k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17)) ) | ~spl9_32),
% 1.90/0.60    inference(avatar_component_clause,[],[f291])).
% 1.90/0.60  fof(f4262,plain,(
% 1.90/0.60    spl9_158 | ~spl9_32 | ~spl9_45),
% 1.90/0.60    inference(avatar_split_clause,[],[f484,f471,f291,f4260])).
% 1.90/0.60  fof(f471,plain,(
% 1.90/0.60    spl9_45 <=> ! [X9,X11,X13,X15,X8,X10,X12,X14] : k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15) = k6_enumset1(X12,X13,X14,X15,X8,X9,X10,X11)),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).
% 1.90/0.60  fof(f484,plain,(
% 1.90/0.60    ( ! [X14,X21,X19,X17,X15,X13,X20,X18,X16] : (k7_enumset1(X21,X13,X14,X15,X16,X17,X18,X19,X20) = k2_xboole_0(k6_enumset1(X17,X18,X19,X20,X13,X14,X15,X16),k1_tarski(X21))) ) | (~spl9_32 | ~spl9_45)),
% 1.90/0.60    inference(superposition,[],[f292,f472])).
% 1.90/0.60  fof(f472,plain,(
% 1.90/0.60    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] : (k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15) = k6_enumset1(X12,X13,X14,X15,X8,X9,X10,X11)) ) | ~spl9_45),
% 1.90/0.60    inference(avatar_component_clause,[],[f471])).
% 1.90/0.60  fof(f908,plain,(
% 1.90/0.60    ~spl9_62 | spl9_20 | ~spl9_58),
% 1.90/0.60    inference(avatar_split_clause,[],[f821,f810,f153,f905])).
% 1.90/0.60  fof(f153,plain,(
% 1.90/0.60    spl9_20 <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k7_enumset1(sK8,sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 1.90/0.60  fof(f810,plain,(
% 1.90/0.60    spl9_58 <=> ! [X16,X9,X11,X13,X15,X17,X10,X12,X14] : k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) = k7_enumset1(X10,X9,X11,X12,X13,X14,X15,X16,X17)),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).
% 1.90/0.60  fof(f821,plain,(
% 1.90/0.60    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK0,sK8,sK1,sK2,sK3,sK4,sK5,sK6,sK7) | (spl9_20 | ~spl9_58)),
% 1.90/0.60    inference(superposition,[],[f155,f811])).
% 1.90/0.60  fof(f811,plain,(
% 1.90/0.60    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : (k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) = k7_enumset1(X10,X9,X11,X12,X13,X14,X15,X16,X17)) ) | ~spl9_58),
% 1.90/0.60    inference(avatar_component_clause,[],[f810])).
% 1.90/0.60  fof(f155,plain,(
% 1.90/0.60    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK8,sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) | spl9_20),
% 1.90/0.60    inference(avatar_component_clause,[],[f153])).
% 1.90/0.60  fof(f812,plain,(
% 1.90/0.60    spl9_58 | ~spl9_18 | ~spl9_33),
% 1.90/0.60    inference(avatar_split_clause,[],[f321,f305,f129,f810])).
% 1.90/0.60  fof(f129,plain,(
% 1.90/0.60    spl9_18 <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 1.90/0.60  fof(f305,plain,(
% 1.90/0.60    spl9_33 <=> ! [X16,X9,X11,X13,X15,X8,X10,X12,X14] : k7_enumset1(X8,X9,X10,X11,X12,X13,X14,X15,X16) = k2_xboole_0(k2_tarski(X9,X8),k5_enumset1(X10,X11,X12,X13,X14,X15,X16))),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).
% 1.90/0.60  fof(f321,plain,(
% 1.90/0.60    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : (k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) = k7_enumset1(X10,X9,X11,X12,X13,X14,X15,X16,X17)) ) | (~spl9_18 | ~spl9_33)),
% 1.90/0.60    inference(superposition,[],[f306,f130])).
% 1.90/0.60  fof(f130,plain,(
% 1.90/0.60    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) ) | ~spl9_18),
% 1.90/0.60    inference(avatar_component_clause,[],[f129])).
% 1.90/0.60  fof(f306,plain,(
% 1.90/0.60    ( ! [X14,X12,X10,X8,X15,X13,X11,X9,X16] : (k7_enumset1(X8,X9,X10,X11,X12,X13,X14,X15,X16) = k2_xboole_0(k2_tarski(X9,X8),k5_enumset1(X10,X11,X12,X13,X14,X15,X16))) ) | ~spl9_33),
% 1.90/0.60    inference(avatar_component_clause,[],[f305])).
% 1.90/0.60  fof(f501,plain,(
% 1.90/0.60    spl9_46 | ~spl9_25 | ~spl9_36),
% 1.90/0.60    inference(avatar_split_clause,[],[f358,f353,f211,f499])).
% 1.90/0.60  fof(f211,plain,(
% 1.90/0.60    spl9_25 <=> ! [X9,X11,X13,X15,X8,X10,X12,X14] : k2_xboole_0(k2_enumset1(X12,X13,X14,X15),k2_enumset1(X8,X9,X10,X11)) = k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15)),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 1.90/0.60  fof(f353,plain,(
% 1.90/0.60    spl9_36 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).
% 1.90/0.60  fof(f358,plain,(
% 1.90/0.60    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] : (k6_enumset1(X12,X13,X14,X15,X8,X9,X10,X11) = k6_enumset1(X9,X10,X11,X12,X13,X14,X15,X8)) ) | (~spl9_25 | ~spl9_36)),
% 1.90/0.60    inference(superposition,[],[f354,f212])).
% 1.90/0.60  fof(f212,plain,(
% 1.90/0.60    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] : (k2_xboole_0(k2_enumset1(X12,X13,X14,X15),k2_enumset1(X8,X9,X10,X11)) = k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15)) ) | ~spl9_25),
% 1.90/0.60    inference(avatar_component_clause,[],[f211])).
% 1.90/0.60  fof(f354,plain,(
% 1.90/0.60    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)) ) | ~spl9_36),
% 1.90/0.60    inference(avatar_component_clause,[],[f353])).
% 1.90/0.60  fof(f473,plain,(
% 1.90/0.60    spl9_45 | ~spl9_15 | ~spl9_25),
% 1.90/0.60    inference(avatar_split_clause,[],[f216,f211,f104,f471])).
% 1.90/0.60  fof(f104,plain,(
% 1.90/0.60    spl9_15 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 1.90/0.60  fof(f216,plain,(
% 1.90/0.60    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] : (k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15) = k6_enumset1(X12,X13,X14,X15,X8,X9,X10,X11)) ) | (~spl9_15 | ~spl9_25)),
% 1.90/0.60    inference(superposition,[],[f212,f105])).
% 1.90/0.60  fof(f105,plain,(
% 1.90/0.60    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) ) | ~spl9_15),
% 1.90/0.60    inference(avatar_component_clause,[],[f104])).
% 1.90/0.60  fof(f355,plain,(
% 1.90/0.60    spl9_36 | ~spl9_2 | ~spl9_5 | ~spl9_10 | ~spl9_16 | ~spl9_18 | ~spl9_19),
% 1.90/0.60    inference(avatar_split_clause,[],[f163,f133,f129,f108,f83,f59,f47,f353])).
% 1.90/0.60  fof(f47,plain,(
% 1.90/0.60    spl9_2 <=> ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.90/0.60  fof(f59,plain,(
% 1.90/0.60    spl9_5 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.90/0.60  fof(f83,plain,(
% 1.90/0.60    spl9_10 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 1.90/0.60  fof(f108,plain,(
% 1.90/0.60    spl9_16 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 1.90/0.60  fof(f133,plain,(
% 1.90/0.60    spl9_19 <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 1.90/0.60  fof(f163,plain,(
% 1.90/0.60    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)) ) | (~spl9_2 | ~spl9_5 | ~spl9_10 | ~spl9_16 | ~spl9_18 | ~spl9_19)),
% 1.90/0.60    inference(forward_demodulation,[],[f157,f151])).
% 1.90/0.60  fof(f151,plain,(
% 1.90/0.60    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)) ) | (~spl9_2 | ~spl9_5 | ~spl9_16 | ~spl9_18)),
% 1.90/0.60    inference(forward_demodulation,[],[f143,f119])).
% 1.90/0.60  fof(f119,plain,(
% 1.90/0.60    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] : (k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15) = k2_xboole_0(k1_tarski(X15),k5_enumset1(X8,X9,X10,X11,X12,X13,X14))) ) | (~spl9_5 | ~spl9_16)),
% 1.90/0.60    inference(superposition,[],[f109,f60])).
% 1.90/0.60  fof(f60,plain,(
% 1.90/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl9_5),
% 1.90/0.60    inference(avatar_component_clause,[],[f59])).
% 1.90/0.60  fof(f109,plain,(
% 1.90/0.60    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) ) | ~spl9_16),
% 1.90/0.60    inference(avatar_component_clause,[],[f108])).
% 1.90/0.60  fof(f143,plain,(
% 1.90/0.60    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) ) | (~spl9_2 | ~spl9_18)),
% 1.90/0.60    inference(superposition,[],[f130,f48])).
% 1.90/0.60  fof(f48,plain,(
% 1.90/0.60    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) ) | ~spl9_2),
% 1.90/0.60    inference(avatar_component_clause,[],[f47])).
% 1.90/0.60  fof(f157,plain,(
% 1.90/0.60    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)) ) | (~spl9_10 | ~spl9_19)),
% 1.90/0.60    inference(superposition,[],[f134,f84])).
% 1.90/0.60  fof(f84,plain,(
% 1.90/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) ) | ~spl9_10),
% 1.90/0.60    inference(avatar_component_clause,[],[f83])).
% 1.90/0.60  fof(f134,plain,(
% 1.90/0.60    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) ) | ~spl9_19),
% 1.90/0.60    inference(avatar_component_clause,[],[f133])).
% 1.90/0.60  fof(f307,plain,(
% 1.90/0.60    spl9_33 | ~spl9_4 | ~spl9_18),
% 1.90/0.60    inference(avatar_split_clause,[],[f144,f129,f55,f305])).
% 1.90/0.60  fof(f55,plain,(
% 1.90/0.60    spl9_4 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.90/0.60  fof(f144,plain,(
% 1.90/0.60    ( ! [X14,X12,X10,X8,X15,X13,X11,X9,X16] : (k7_enumset1(X8,X9,X10,X11,X12,X13,X14,X15,X16) = k2_xboole_0(k2_tarski(X9,X8),k5_enumset1(X10,X11,X12,X13,X14,X15,X16))) ) | (~spl9_4 | ~spl9_18)),
% 1.90/0.60    inference(superposition,[],[f130,f56])).
% 1.90/0.60  fof(f56,plain,(
% 1.90/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl9_4),
% 1.90/0.60    inference(avatar_component_clause,[],[f55])).
% 1.90/0.60  fof(f293,plain,(
% 1.90/0.60    spl9_32 | ~spl9_5 | ~spl9_17),
% 1.90/0.60    inference(avatar_split_clause,[],[f137,f125,f59,f291])).
% 1.90/0.60  fof(f125,plain,(
% 1.90/0.60    spl9_17 <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 1.90/0.60  fof(f137,plain,(
% 1.90/0.60    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : (k2_xboole_0(k6_enumset1(X10,X11,X12,X13,X14,X15,X16,X17),k1_tarski(X9)) = k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17)) ) | (~spl9_5 | ~spl9_17)),
% 1.90/0.60    inference(superposition,[],[f126,f60])).
% 1.90/0.60  fof(f126,plain,(
% 1.90/0.60    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))) ) | ~spl9_17),
% 1.90/0.60    inference(avatar_component_clause,[],[f125])).
% 1.90/0.60  fof(f213,plain,(
% 1.90/0.60    spl9_25 | ~spl9_5 | ~spl9_15),
% 1.90/0.60    inference(avatar_split_clause,[],[f113,f104,f59,f211])).
% 1.90/0.60  fof(f113,plain,(
% 1.90/0.60    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] : (k2_xboole_0(k2_enumset1(X12,X13,X14,X15),k2_enumset1(X8,X9,X10,X11)) = k6_enumset1(X8,X9,X10,X11,X12,X13,X14,X15)) ) | (~spl9_5 | ~spl9_15)),
% 1.90/0.60    inference(superposition,[],[f105,f60])).
% 1.90/0.60  fof(f156,plain,(
% 1.90/0.60    ~spl9_20 | spl9_11 | ~spl9_17),
% 1.90/0.60    inference(avatar_split_clause,[],[f139,f125,f87,f153])).
% 1.90/0.60  fof(f87,plain,(
% 1.90/0.60    spl9_11 <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k2_xboole_0(k1_tarski(sK8),k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7))),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 1.90/0.60  fof(f139,plain,(
% 1.90/0.60    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK8,sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) | (spl9_11 | ~spl9_17)),
% 1.90/0.60    inference(superposition,[],[f89,f126])).
% 1.90/0.60  fof(f89,plain,(
% 1.90/0.60    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK8),k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)) | spl9_11),
% 1.90/0.60    inference(avatar_component_clause,[],[f87])).
% 1.90/0.60  fof(f135,plain,(
% 1.90/0.60    spl9_19),
% 1.90/0.60    inference(avatar_split_clause,[],[f40,f133])).
% 1.90/0.60  fof(f40,plain,(
% 1.90/0.60    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 1.90/0.60    inference(cnf_transformation,[],[f9])).
% 1.90/0.60  fof(f9,axiom,(
% 1.90/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 1.90/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).
% 1.90/0.60  fof(f131,plain,(
% 1.90/0.60    spl9_18),
% 1.90/0.60    inference(avatar_split_clause,[],[f39,f129])).
% 1.90/0.60  fof(f39,plain,(
% 1.90/0.60    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) )),
% 1.90/0.60    inference(cnf_transformation,[],[f8])).
% 1.90/0.60  fof(f8,axiom,(
% 1.90/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),
% 1.90/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_enumset1)).
% 1.90/0.60  fof(f127,plain,(
% 1.90/0.60    spl9_17),
% 1.90/0.60    inference(avatar_split_clause,[],[f38,f125])).
% 1.90/0.60  fof(f38,plain,(
% 1.90/0.60    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))) )),
% 1.90/0.60    inference(cnf_transformation,[],[f7])).
% 1.90/0.60  fof(f7,axiom,(
% 1.90/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))),
% 1.90/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).
% 1.90/0.60  fof(f110,plain,(
% 1.90/0.60    spl9_16),
% 1.90/0.60    inference(avatar_split_clause,[],[f37,f108])).
% 1.90/0.60  fof(f37,plain,(
% 1.90/0.60    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 1.90/0.60    inference(cnf_transformation,[],[f10])).
% 1.90/0.60  fof(f10,axiom,(
% 1.90/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 1.90/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).
% 1.90/0.60  fof(f106,plain,(
% 1.90/0.60    spl9_15),
% 1.90/0.60    inference(avatar_split_clause,[],[f36,f104])).
% 1.90/0.60  fof(f36,plain,(
% 1.90/0.60    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 1.90/0.60    inference(cnf_transformation,[],[f6])).
% 1.90/0.60  fof(f6,axiom,(
% 1.90/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 1.90/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).
% 1.90/0.60  fof(f90,plain,(
% 1.90/0.60    ~spl9_11 | spl9_1 | ~spl9_5),
% 1.90/0.60    inference(avatar_split_clause,[],[f66,f59,f42,f87])).
% 1.90/0.60  fof(f42,plain,(
% 1.90/0.60    spl9_1 <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))),
% 1.90/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.90/0.60  fof(f66,plain,(
% 1.90/0.60    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK8),k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)) | (spl9_1 | ~spl9_5)),
% 1.90/0.60    inference(superposition,[],[f44,f60])).
% 1.90/0.60  fof(f44,plain,(
% 1.90/0.60    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) | spl9_1),
% 1.90/0.60    inference(avatar_component_clause,[],[f42])).
% 1.90/0.60  fof(f85,plain,(
% 1.90/0.60    spl9_10),
% 1.90/0.60    inference(avatar_split_clause,[],[f32,f83])).
% 1.90/0.60  fof(f32,plain,(
% 1.90/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.90/0.60    inference(cnf_transformation,[],[f14])).
% 1.90/0.60  fof(f14,axiom,(
% 1.90/0.60    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.90/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.90/0.60  fof(f61,plain,(
% 1.90/0.60    spl9_5),
% 1.90/0.60    inference(avatar_split_clause,[],[f27,f59])).
% 1.90/0.60  fof(f27,plain,(
% 1.90/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.90/0.60    inference(cnf_transformation,[],[f1])).
% 1.90/0.60  fof(f1,axiom,(
% 1.90/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.90/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.90/0.60  fof(f57,plain,(
% 1.90/0.60    spl9_4),
% 1.90/0.60    inference(avatar_split_clause,[],[f26,f55])).
% 1.90/0.60  fof(f26,plain,(
% 1.90/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.90/0.60    inference(cnf_transformation,[],[f5])).
% 1.90/0.60  fof(f5,axiom,(
% 1.90/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.90/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.90/0.60  fof(f49,plain,(
% 1.90/0.60    spl9_2),
% 1.90/0.60    inference(avatar_split_clause,[],[f24,f47])).
% 1.90/0.60  fof(f24,plain,(
% 1.90/0.60    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.90/0.60    inference(cnf_transformation,[],[f11])).
% 1.90/0.60  fof(f11,axiom,(
% 1.90/0.60    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.90/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.90/0.60  fof(f45,plain,(
% 1.90/0.60    ~spl9_1),
% 1.90/0.60    inference(avatar_split_clause,[],[f23,f42])).
% 1.90/0.60  fof(f23,plain,(
% 1.90/0.60    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))),
% 1.90/0.60    inference(cnf_transformation,[],[f22])).
% 1.90/0.60  fof(f22,plain,(
% 1.90/0.60    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))),
% 1.90/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f20,f21])).
% 1.90/0.60  fof(f21,plain,(
% 1.90/0.60    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))),
% 1.90/0.60    introduced(choice_axiom,[])).
% 1.90/0.60  fof(f20,plain,(
% 1.90/0.60    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 1.90/0.60    inference(ennf_transformation,[],[f19])).
% 1.90/0.60  fof(f19,negated_conjecture,(
% 1.90/0.60    ~! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 1.90/0.60    inference(negated_conjecture,[],[f18])).
% 1.90/0.60  fof(f18,conjecture,(
% 1.90/0.60    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 1.90/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).
% 1.90/0.60  % SZS output end Proof for theBenchmark
% 1.90/0.60  % (32718)------------------------------
% 1.90/0.60  % (32718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.60  % (32718)Termination reason: Refutation
% 1.90/0.60  
% 1.90/0.60  % (32718)Memory used [KB]: 10874
% 1.90/0.60  % (32718)Time elapsed: 0.197 s
% 1.90/0.60  % (32718)------------------------------
% 1.90/0.60  % (32718)------------------------------
% 1.90/0.60  % (32712)Success in time 0.25 s
%------------------------------------------------------------------------------
