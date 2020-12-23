%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 150 expanded)
%              Number of leaves         :   31 (  76 expanded)
%              Depth                    :    6
%              Number of atoms          :  198 ( 298 expanded)
%              Number of equality atoms :   79 ( 129 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1068,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f35,f39,f43,f47,f51,f55,f59,f65,f69,f73,f77,f100,f111,f121,f144,f224,f470,f1060,f1067])).

fof(f1067,plain,
    ( spl4_1
    | ~ spl4_37
    | ~ spl4_59 ),
    inference(avatar_contradiction_clause,[],[f1066])).

fof(f1066,plain,
    ( $false
    | spl4_1
    | ~ spl4_37
    | ~ spl4_59 ),
    inference(subsumption_resolution,[],[f30,f1064])).

fof(f1064,plain,
    ( ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X5,X7)
    | ~ spl4_37
    | ~ spl4_59 ),
    inference(superposition,[],[f1059,f469])).

fof(f469,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f468])).

fof(f468,plain,
    ( spl4_37
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f1059,plain,
    ( ! [X6,X4,X5,X3] : k2_enumset1(X6,X3,X4,X5) = k2_xboole_0(k1_tarski(X6),k1_enumset1(X4,X3,X5))
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f1058])).

fof(f1058,plain,
    ( spl4_59
  <=> ! [X3,X5,X4,X6] : k2_enumset1(X6,X3,X4,X5) = k2_xboole_0(k1_tarski(X6),k1_enumset1(X4,X3,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f30,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK2,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1060,plain,
    ( spl4_59
    | ~ spl4_20
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f472,f468,f142,f1058])).

fof(f142,plain,
    ( spl4_20
  <=> ! [X3,X5,X4] : k1_enumset1(X3,X4,X5) = k1_enumset1(X4,X3,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f472,plain,
    ( ! [X6,X4,X5,X3] : k2_enumset1(X6,X3,X4,X5) = k2_xboole_0(k1_tarski(X6),k1_enumset1(X4,X3,X5))
    | ~ spl4_20
    | ~ spl4_37 ),
    inference(superposition,[],[f469,f143])).

fof(f143,plain,
    ( ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k1_enumset1(X4,X3,X5)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f142])).

fof(f470,plain,
    ( spl4_37
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f231,f222,f49,f33,f468])).

fof(f33,plain,
    ( spl4_2
  <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f49,plain,
    ( spl4_6
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f222,plain,
    ( spl4_25
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f231,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f225,f50])).

fof(f50,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f225,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))
    | ~ spl4_2
    | ~ spl4_25 ),
    inference(superposition,[],[f223,f34])).

fof(f34,plain,
    ( ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f223,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f222])).

fof(f224,plain,
    ( spl4_25
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f124,f119,f57,f41,f222])).

fof(f41,plain,
    ( spl4_4
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f57,plain,
    ( spl4_8
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f119,plain,
    ( spl4_17
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f124,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f122,f58])).

fof(f58,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f122,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))
    | ~ spl4_4
    | ~ spl4_17 ),
    inference(superposition,[],[f120,f42])).

fof(f42,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f120,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f119])).

fof(f144,plain,
    ( spl4_20
    | ~ spl4_11
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f115,f109,f71,f142])).

fof(f71,plain,
    ( spl4_11
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f109,plain,
    ( spl4_16
  <=> ! [X3,X2,X4] : k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f115,plain,
    ( ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k1_enumset1(X4,X3,X5)
    | ~ spl4_11
    | ~ spl4_16 ),
    inference(superposition,[],[f110,f72])).

fof(f72,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f71])).

fof(f110,plain,
    ( ! [X4,X2,X3] : k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f109])).

fof(f121,plain,
    ( spl4_17
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f103,f98,f63,f45,f119])).

fof(f45,plain,
    ( spl4_5
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f63,plain,
    ( spl4_9
  <=> ! [X1,X3,X5,X0,X2,X4] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f98,plain,
    ( spl4_14
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f103,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f101,f64])).

fof(f64,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f101,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(superposition,[],[f99,f46])).

fof(f46,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f99,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f98])).

fof(f111,plain,
    ( spl4_16
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f82,f71,f37,f109])).

fof(f37,plain,
    ( spl4_3
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f82,plain,
    ( ! [X4,X2,X3] : k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4))
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(superposition,[],[f72,f38])).

fof(f38,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f100,plain,
    ( spl4_14
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f80,f75,f67,f49,f98])).

fof(f67,plain,
    ( spl4_10
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f75,plain,
    ( spl4_12
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f80,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f78,f68])).

fof(f68,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f78,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(superposition,[],[f76,f50])).

fof(f76,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f75])).

fof(f77,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f26,f75])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

fof(f73,plain,
    ( spl4_11
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f61,f53,f45,f41,f71])).

fof(f53,plain,
    ( spl4_7
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f61,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f60,f46])).

fof(f60,plain,
    ( ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(superposition,[],[f54,f42])).

fof(f54,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f69,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f25,f67])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f65,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f24,f63])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f59,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f23,f57])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f55,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f22,f53])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f51,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f47,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f19,f41])).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f18,f37])).

fof(f18,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f35,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f17,f33])).

fof(f17,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f16,f28])).

fof(f16,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:02:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (24284)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.45  % (24273)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (24272)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (24279)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (24277)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.46  % (24276)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (24283)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (24275)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (24282)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (24282)Refutation not found, incomplete strategy% (24282)------------------------------
% 0.20/0.48  % (24282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (24282)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (24282)Memory used [KB]: 10490
% 0.20/0.48  % (24282)Time elapsed: 0.061 s
% 0.20/0.48  % (24282)------------------------------
% 0.20/0.48  % (24282)------------------------------
% 0.20/0.48  % (24288)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  % (24278)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (24287)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.49  % (24280)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (24285)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (24274)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.49  % (24286)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (24271)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.51  % (24281)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.52  % (24276)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f1068,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f31,f35,f39,f43,f47,f51,f55,f59,f65,f69,f73,f77,f100,f111,f121,f144,f224,f470,f1060,f1067])).
% 0.20/0.52  fof(f1067,plain,(
% 0.20/0.52    spl4_1 | ~spl4_37 | ~spl4_59),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f1066])).
% 0.20/0.52  fof(f1066,plain,(
% 0.20/0.52    $false | (spl4_1 | ~spl4_37 | ~spl4_59)),
% 0.20/0.52    inference(subsumption_resolution,[],[f30,f1064])).
% 0.20/0.52  fof(f1064,plain,(
% 0.20/0.52    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X5,X7)) ) | (~spl4_37 | ~spl4_59)),
% 0.20/0.52    inference(superposition,[],[f1059,f469])).
% 0.20/0.52  fof(f469,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) ) | ~spl4_37),
% 0.20/0.52    inference(avatar_component_clause,[],[f468])).
% 0.20/0.52  fof(f468,plain,(
% 0.20/0.52    spl4_37 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.20/0.52  fof(f1059,plain,(
% 0.20/0.52    ( ! [X6,X4,X5,X3] : (k2_enumset1(X6,X3,X4,X5) = k2_xboole_0(k1_tarski(X6),k1_enumset1(X4,X3,X5))) ) | ~spl4_59),
% 0.20/0.52    inference(avatar_component_clause,[],[f1058])).
% 0.20/0.52  fof(f1058,plain,(
% 0.20/0.52    spl4_59 <=> ! [X3,X5,X4,X6] : k2_enumset1(X6,X3,X4,X5) = k2_xboole_0(k1_tarski(X6),k1_enumset1(X4,X3,X5))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) | spl4_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK0,sK2,sK1,sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.52  fof(f1060,plain,(
% 0.20/0.52    spl4_59 | ~spl4_20 | ~spl4_37),
% 0.20/0.52    inference(avatar_split_clause,[],[f472,f468,f142,f1058])).
% 0.20/0.52  fof(f142,plain,(
% 0.20/0.52    spl4_20 <=> ! [X3,X5,X4] : k1_enumset1(X3,X4,X5) = k1_enumset1(X4,X3,X5)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.52  fof(f472,plain,(
% 0.20/0.52    ( ! [X6,X4,X5,X3] : (k2_enumset1(X6,X3,X4,X5) = k2_xboole_0(k1_tarski(X6),k1_enumset1(X4,X3,X5))) ) | (~spl4_20 | ~spl4_37)),
% 0.20/0.52    inference(superposition,[],[f469,f143])).
% 0.20/0.52  fof(f143,plain,(
% 0.20/0.52    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k1_enumset1(X4,X3,X5)) ) | ~spl4_20),
% 0.20/0.52    inference(avatar_component_clause,[],[f142])).
% 0.20/0.52  fof(f470,plain,(
% 0.20/0.52    spl4_37 | ~spl4_2 | ~spl4_6 | ~spl4_25),
% 0.20/0.52    inference(avatar_split_clause,[],[f231,f222,f49,f33,f468])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    spl4_2 <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    spl4_6 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.52  fof(f222,plain,(
% 0.20/0.52    spl4_25 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.52  fof(f231,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) ) | (~spl4_2 | ~spl4_6 | ~spl4_25)),
% 0.20/0.52    inference(forward_demodulation,[],[f225,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) ) | ~spl4_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f49])).
% 0.20/0.52  fof(f225,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) ) | (~spl4_2 | ~spl4_25)),
% 0.20/0.52    inference(superposition,[],[f223,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) ) | ~spl4_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f33])).
% 0.20/0.52  fof(f223,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) ) | ~spl4_25),
% 0.20/0.52    inference(avatar_component_clause,[],[f222])).
% 0.20/0.52  fof(f224,plain,(
% 0.20/0.52    spl4_25 | ~spl4_4 | ~spl4_8 | ~spl4_17),
% 0.20/0.52    inference(avatar_split_clause,[],[f124,f119,f57,f41,f222])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    spl4_4 <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    spl4_8 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    spl4_17 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) ) | (~spl4_4 | ~spl4_8 | ~spl4_17)),
% 0.20/0.52    inference(forward_demodulation,[],[f122,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) ) | ~spl4_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f57])).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) ) | (~spl4_4 | ~spl4_17)),
% 0.20/0.52    inference(superposition,[],[f120,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) ) | ~spl4_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f41])).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) ) | ~spl4_17),
% 0.20/0.52    inference(avatar_component_clause,[],[f119])).
% 0.20/0.52  fof(f144,plain,(
% 0.20/0.52    spl4_20 | ~spl4_11 | ~spl4_16),
% 0.20/0.52    inference(avatar_split_clause,[],[f115,f109,f71,f142])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    spl4_11 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.52  fof(f109,plain,(
% 0.20/0.52    spl4_16 <=> ! [X3,X2,X4] : k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k1_enumset1(X4,X3,X5)) ) | (~spl4_11 | ~spl4_16)),
% 0.20/0.52    inference(superposition,[],[f110,f72])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) ) | ~spl4_11),
% 0.20/0.52    inference(avatar_component_clause,[],[f71])).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    ( ! [X4,X2,X3] : (k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4))) ) | ~spl4_16),
% 0.20/0.52    inference(avatar_component_clause,[],[f109])).
% 0.20/0.52  fof(f121,plain,(
% 0.20/0.52    spl4_17 | ~spl4_5 | ~spl4_9 | ~spl4_14),
% 0.20/0.52    inference(avatar_split_clause,[],[f103,f98,f63,f45,f119])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    spl4_5 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    spl4_9 <=> ! [X1,X3,X5,X0,X2,X4] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    spl4_14 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) ) | (~spl4_5 | ~spl4_9 | ~spl4_14)),
% 0.20/0.52    inference(forward_demodulation,[],[f101,f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) ) | ~spl4_9),
% 0.20/0.52    inference(avatar_component_clause,[],[f63])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) ) | (~spl4_5 | ~spl4_14)),
% 0.20/0.52    inference(superposition,[],[f99,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) ) | ~spl4_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f45])).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) ) | ~spl4_14),
% 0.20/0.52    inference(avatar_component_clause,[],[f98])).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    spl4_16 | ~spl4_3 | ~spl4_11),
% 0.20/0.52    inference(avatar_split_clause,[],[f82,f71,f37,f109])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    spl4_3 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    ( ! [X4,X2,X3] : (k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4))) ) | (~spl4_3 | ~spl4_11)),
% 0.20/0.52    inference(superposition,[],[f72,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl4_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f37])).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    spl4_14 | ~spl4_6 | ~spl4_10 | ~spl4_12),
% 0.20/0.52    inference(avatar_split_clause,[],[f80,f75,f67,f49,f98])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    spl4_10 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    spl4_12 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) ) | (~spl4_6 | ~spl4_10 | ~spl4_12)),
% 0.20/0.52    inference(forward_demodulation,[],[f78,f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) ) | ~spl4_10),
% 0.20/0.52    inference(avatar_component_clause,[],[f67])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) ) | (~spl4_6 | ~spl4_12)),
% 0.20/0.52    inference(superposition,[],[f76,f50])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) ) | ~spl4_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f75])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    spl4_12),
% 0.20/0.52    inference(avatar_split_clause,[],[f26,f75])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    spl4_11 | ~spl4_4 | ~spl4_5 | ~spl4_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f61,f53,f45,f41,f71])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    spl4_7 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) ) | (~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.20/0.52    inference(forward_demodulation,[],[f60,f46])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) ) | (~spl4_4 | ~spl4_7)),
% 0.20/0.52    inference(superposition,[],[f54,f42])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) ) | ~spl4_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f53])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    spl4_10),
% 0.20/0.52    inference(avatar_split_clause,[],[f25,f67])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    spl4_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f24,f63])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    spl4_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f23,f57])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    spl4_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f22,f53])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    spl4_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f21,f49])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    spl4_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f20,f45])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    spl4_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f19,f41])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    spl4_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f18,f37])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    spl4_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f17,f33])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ~spl4_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f16,f28])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3)),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 0.20/0.52    inference(negated_conjecture,[],[f11])).
% 0.20/0.52  fof(f11,conjecture,(
% 0.20/0.52    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (24276)------------------------------
% 0.20/0.52  % (24276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24276)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (24276)Memory used [KB]: 6908
% 0.20/0.52  % (24276)Time elapsed: 0.102 s
% 0.20/0.52  % (24276)------------------------------
% 0.20/0.52  % (24276)------------------------------
% 0.20/0.53  % (24270)Success in time 0.173 s
%------------------------------------------------------------------------------
