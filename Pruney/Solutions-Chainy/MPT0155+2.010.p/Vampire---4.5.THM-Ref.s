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
% DateTime   : Thu Dec  3 12:33:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 142 expanded)
%              Number of leaves         :   23 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  207 ( 321 expanded)
%              Number of equality atoms :   69 ( 126 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f586,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f43,f51,f65,f83,f89,f100,f104,f144,f185,f276,f282,f506,f548,f584])).

fof(f584,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_22
    | ~ spl3_26
    | ~ spl3_40
    | ~ spl3_44 ),
    inference(avatar_contradiction_clause,[],[f583])).

fof(f583,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_22
    | ~ spl3_26
    | ~ spl3_40
    | ~ spl3_44 ),
    inference(subsumption_resolution,[],[f38,f582])).

fof(f582,plain,
    ( ! [X19,X20,X18] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_22
    | ~ spl3_26
    | ~ spl3_40
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f581,f570])).

fof(f570,plain,
    ( ! [X19,X17,X18] : k2_xboole_0(k2_tarski(X17,X18),k2_tarski(X18,X19)) = k1_enumset1(X17,X18,X19)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_40
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f569,f64])).

fof(f64,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f569,plain,
    ( ! [X19,X17,X18] : k2_xboole_0(k2_tarski(X17,X18),k2_tarski(X18,X19)) = k2_xboole_0(k1_tarski(X17),k2_tarski(X18,X19))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_40
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f568,f42])).

fof(f42,plain,
    ( ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_2
  <=> ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f568,plain,
    ( ! [X19,X17,X18] : k2_xboole_0(k2_tarski(X17,X17),k2_tarski(X18,X19)) = k2_xboole_0(k2_tarski(X17,X18),k2_tarski(X18,X19))
    | ~ spl3_4
    | ~ spl3_40
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f552,f50])).

fof(f50,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_4
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f552,plain,
    ( ! [X19,X17,X18] : k2_xboole_0(k2_tarski(X17,X17),k2_tarski(X18,X19)) = k2_xboole_0(k1_enumset1(X17,X17,X18),k2_tarski(X18,X19))
    | ~ spl3_40
    | ~ spl3_44 ),
    inference(superposition,[],[f547,f505])).

fof(f505,plain,
    ( ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k4_enumset1(X0,X0,X1,X2,X2,X3)
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f504])).

fof(f504,plain,
    ( spl3_40
  <=> ! [X1,X3,X0,X2] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k4_enumset1(X0,X0,X1,X2,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f547,plain,
    ( ! [X6,X10,X8,X7,X9] : k4_enumset1(X6,X7,X7,X8,X9,X10) = k2_xboole_0(k1_enumset1(X6,X7,X8),k2_tarski(X9,X10))
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f546])).

fof(f546,plain,
    ( spl3_44
  <=> ! [X9,X7,X8,X10,X6] : k4_enumset1(X6,X7,X7,X8,X9,X10) = k2_xboole_0(k1_enumset1(X6,X7,X8),k2_tarski(X9,X10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f581,plain,
    ( ! [X19,X20,X18] : k2_enumset1(X18,X18,X19,X20) = k2_xboole_0(k2_tarski(X18,X19),k2_tarski(X19,X20))
    | ~ spl3_4
    | ~ spl3_22
    | ~ spl3_26
    | ~ spl3_40
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f580,f50])).

fof(f580,plain,
    ( ! [X19,X20,X18] : k2_xboole_0(k1_enumset1(X18,X18,X19),k2_tarski(X19,X20)) = k2_enumset1(X18,X18,X19,X20)
    | ~ spl3_4
    | ~ spl3_22
    | ~ spl3_26
    | ~ spl3_40
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f562,f565])).

fof(f565,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl3_4
    | ~ spl3_22
    | ~ spl3_26
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f564,f184])).

fof(f184,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl3_22
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f564,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl3_4
    | ~ spl3_26
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f549,f50])).

fof(f549,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X1),k2_tarski(X2,X3))
    | ~ spl3_26
    | ~ spl3_44 ),
    inference(superposition,[],[f547,f275])).

fof(f275,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl3_26
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f562,plain,
    ( ! [X19,X20,X18] : k2_xboole_0(k1_enumset1(X18,X18,X19),k2_tarski(X19,X20)) = k2_xboole_0(k2_tarski(X18,X18),k2_tarski(X19,X20))
    | ~ spl3_40
    | ~ spl3_44 ),
    inference(superposition,[],[f505,f547])).

fof(f38,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f548,plain,
    ( spl3_44
    | ~ spl3_13
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f146,f142,f102,f546])).

fof(f102,plain,
    ( spl3_13
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f142,plain,
    ( spl3_18
  <=> ! [X1,X0,X2] : k2_enumset1(X2,X0,X0,X1) = k1_enumset1(X2,X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f146,plain,
    ( ! [X6,X10,X8,X7,X9] : k4_enumset1(X6,X7,X7,X8,X9,X10) = k2_xboole_0(k1_enumset1(X6,X7,X8),k2_tarski(X9,X10))
    | ~ spl3_13
    | ~ spl3_18 ),
    inference(superposition,[],[f103,f143])).

fof(f143,plain,
    ( ! [X2,X0,X1] : k2_enumset1(X2,X0,X0,X1) = k1_enumset1(X2,X0,X1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f142])).

fof(f103,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f102])).

fof(f506,plain,
    ( spl3_40
    | ~ spl3_4
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f284,f280,f49,f504])).

fof(f280,plain,
    ( spl3_27
  <=> ! [X1,X3,X0,X2,X4] : k4_enumset1(X2,X3,X4,X0,X0,X1) = k2_xboole_0(k1_enumset1(X2,X3,X4),k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f284,plain,
    ( ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k4_enumset1(X0,X0,X1,X2,X2,X3)
    | ~ spl3_4
    | ~ spl3_27 ),
    inference(superposition,[],[f281,f50])).

fof(f281,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X2,X3,X4,X0,X0,X1) = k2_xboole_0(k1_enumset1(X2,X3,X4),k2_tarski(X0,X1))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f280])).

fof(f282,plain,
    ( spl3_27
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f110,f98,f49,f280])).

fof(f98,plain,
    ( spl3_12
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f110,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X2,X3,X4,X0,X0,X1) = k2_xboole_0(k1_enumset1(X2,X3,X4),k2_tarski(X0,X1))
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(superposition,[],[f99,f50])).

fof(f99,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f98])).

fof(f276,plain,
    ( spl3_26
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f111,f98,f87,f49,f274])).

fof(f87,plain,
    ( spl3_10
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f111,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f109,f88])).

fof(f88,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f87])).

fof(f109,plain,
    ( ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k4_enumset1(X0,X0,X1,X2,X3,X4)
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(superposition,[],[f99,f50])).

fof(f185,plain,
    ( spl3_22
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f96,f87,f81,f41,f183])).

fof(f81,plain,
    ( spl3_9
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f96,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f94,f82])).

fof(f82,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f81])).

fof(f94,plain,
    ( ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k3_enumset1(X0,X0,X1,X2,X3)
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(superposition,[],[f88,f42])).

fof(f144,plain,
    ( spl3_18
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f85,f81,f63,f49,f142])).

fof(f85,plain,
    ( ! [X2,X0,X1] : k2_enumset1(X2,X0,X0,X1) = k1_enumset1(X2,X0,X1)
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f84,f64])).

fof(f84,plain,
    ( ! [X2,X0,X1] : k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(superposition,[],[f82,f50])).

fof(f104,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f31,f102])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

fof(f100,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f30,f98])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

fof(f89,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f29,f87])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(f83,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f28,f81])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f65,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f26,f63])).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f51,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f23,f49])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f20,f36])).

fof(f20,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:13:33 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (30275)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.44  % (30276)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.44  % (30276)Refutation not found, incomplete strategy% (30276)------------------------------
% 0.21/0.44  % (30276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (30276)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.44  
% 0.21/0.44  % (30276)Memory used [KB]: 10490
% 0.21/0.44  % (30276)Time elapsed: 0.003 s
% 0.21/0.44  % (30276)------------------------------
% 0.21/0.44  % (30276)------------------------------
% 0.21/0.47  % (30269)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (30278)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (30277)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (30270)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (30266)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (30273)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (30279)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (30272)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (30267)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (30265)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (30271)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (30280)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (30270)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f586,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f39,f43,f51,f65,f83,f89,f100,f104,f144,f185,f276,f282,f506,f548,f584])).
% 0.21/0.50  fof(f584,plain,(
% 0.21/0.50    spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_7 | ~spl3_22 | ~spl3_26 | ~spl3_40 | ~spl3_44),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f583])).
% 0.21/0.50  fof(f583,plain,(
% 0.21/0.50    $false | (spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_7 | ~spl3_22 | ~spl3_26 | ~spl3_40 | ~spl3_44)),
% 0.21/0.50    inference(subsumption_resolution,[],[f38,f582])).
% 0.21/0.50  fof(f582,plain,(
% 0.21/0.50    ( ! [X19,X20,X18] : (k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20)) ) | (~spl3_2 | ~spl3_4 | ~spl3_7 | ~spl3_22 | ~spl3_26 | ~spl3_40 | ~spl3_44)),
% 0.21/0.50    inference(forward_demodulation,[],[f581,f570])).
% 0.21/0.50  fof(f570,plain,(
% 0.21/0.50    ( ! [X19,X17,X18] : (k2_xboole_0(k2_tarski(X17,X18),k2_tarski(X18,X19)) = k1_enumset1(X17,X18,X19)) ) | (~spl3_2 | ~spl3_4 | ~spl3_7 | ~spl3_40 | ~spl3_44)),
% 0.21/0.50    inference(forward_demodulation,[],[f569,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) ) | ~spl3_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    spl3_7 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.50  fof(f569,plain,(
% 0.21/0.50    ( ! [X19,X17,X18] : (k2_xboole_0(k2_tarski(X17,X18),k2_tarski(X18,X19)) = k2_xboole_0(k1_tarski(X17),k2_tarski(X18,X19))) ) | (~spl3_2 | ~spl3_4 | ~spl3_40 | ~spl3_44)),
% 0.21/0.50    inference(forward_demodulation,[],[f568,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) ) | ~spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    spl3_2 <=> ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.50  fof(f568,plain,(
% 0.21/0.50    ( ! [X19,X17,X18] : (k2_xboole_0(k2_tarski(X17,X17),k2_tarski(X18,X19)) = k2_xboole_0(k2_tarski(X17,X18),k2_tarski(X18,X19))) ) | (~spl3_4 | ~spl3_40 | ~spl3_44)),
% 0.21/0.50    inference(forward_demodulation,[],[f552,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) ) | ~spl3_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    spl3_4 <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.50  fof(f552,plain,(
% 0.21/0.50    ( ! [X19,X17,X18] : (k2_xboole_0(k2_tarski(X17,X17),k2_tarski(X18,X19)) = k2_xboole_0(k1_enumset1(X17,X17,X18),k2_tarski(X18,X19))) ) | (~spl3_40 | ~spl3_44)),
% 0.21/0.50    inference(superposition,[],[f547,f505])).
% 0.21/0.50  fof(f505,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k4_enumset1(X0,X0,X1,X2,X2,X3)) ) | ~spl3_40),
% 0.21/0.50    inference(avatar_component_clause,[],[f504])).
% 0.21/0.50  fof(f504,plain,(
% 0.21/0.50    spl3_40 <=> ! [X1,X3,X0,X2] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k4_enumset1(X0,X0,X1,X2,X2,X3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.21/0.50  fof(f547,plain,(
% 0.21/0.50    ( ! [X6,X10,X8,X7,X9] : (k4_enumset1(X6,X7,X7,X8,X9,X10) = k2_xboole_0(k1_enumset1(X6,X7,X8),k2_tarski(X9,X10))) ) | ~spl3_44),
% 0.21/0.50    inference(avatar_component_clause,[],[f546])).
% 0.21/0.50  fof(f546,plain,(
% 0.21/0.50    spl3_44 <=> ! [X9,X7,X8,X10,X6] : k4_enumset1(X6,X7,X7,X8,X9,X10) = k2_xboole_0(k1_enumset1(X6,X7,X8),k2_tarski(X9,X10))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.21/0.50  fof(f581,plain,(
% 0.21/0.50    ( ! [X19,X20,X18] : (k2_enumset1(X18,X18,X19,X20) = k2_xboole_0(k2_tarski(X18,X19),k2_tarski(X19,X20))) ) | (~spl3_4 | ~spl3_22 | ~spl3_26 | ~spl3_40 | ~spl3_44)),
% 0.21/0.50    inference(forward_demodulation,[],[f580,f50])).
% 0.21/0.50  fof(f580,plain,(
% 0.21/0.50    ( ! [X19,X20,X18] : (k2_xboole_0(k1_enumset1(X18,X18,X19),k2_tarski(X19,X20)) = k2_enumset1(X18,X18,X19,X20)) ) | (~spl3_4 | ~spl3_22 | ~spl3_26 | ~spl3_40 | ~spl3_44)),
% 0.21/0.50    inference(forward_demodulation,[],[f562,f565])).
% 0.21/0.50  fof(f565,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | (~spl3_4 | ~spl3_22 | ~spl3_26 | ~spl3_44)),
% 0.21/0.50    inference(forward_demodulation,[],[f564,f184])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) ) | ~spl3_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f183])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    spl3_22 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.50  fof(f564,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | (~spl3_4 | ~spl3_26 | ~spl3_44)),
% 0.21/0.50    inference(forward_demodulation,[],[f549,f50])).
% 0.21/0.50  fof(f549,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X1),k2_tarski(X2,X3))) ) | (~spl3_26 | ~spl3_44)),
% 0.21/0.50    inference(superposition,[],[f547,f275])).
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) ) | ~spl3_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f274])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    spl3_26 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.50  fof(f562,plain,(
% 0.21/0.50    ( ! [X19,X20,X18] : (k2_xboole_0(k1_enumset1(X18,X18,X19),k2_tarski(X19,X20)) = k2_xboole_0(k2_tarski(X18,X18),k2_tarski(X19,X20))) ) | (~spl3_40 | ~spl3_44)),
% 0.21/0.50    inference(superposition,[],[f505,f547])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) | spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    spl3_1 <=> k1_enumset1(sK0,sK1,sK2) = k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f548,plain,(
% 0.21/0.50    spl3_44 | ~spl3_13 | ~spl3_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f146,f142,f102,f546])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl3_13 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    spl3_18 <=> ! [X1,X0,X2] : k2_enumset1(X2,X0,X0,X1) = k1_enumset1(X2,X0,X1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    ( ! [X6,X10,X8,X7,X9] : (k4_enumset1(X6,X7,X7,X8,X9,X10) = k2_xboole_0(k1_enumset1(X6,X7,X8),k2_tarski(X9,X10))) ) | (~spl3_13 | ~spl3_18)),
% 0.21/0.50    inference(superposition,[],[f103,f143])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X2,X0,X0,X1) = k1_enumset1(X2,X0,X1)) ) | ~spl3_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f142])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) ) | ~spl3_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f102])).
% 0.21/0.50  fof(f506,plain,(
% 0.21/0.50    spl3_40 | ~spl3_4 | ~spl3_27),
% 0.21/0.50    inference(avatar_split_clause,[],[f284,f280,f49,f504])).
% 0.21/0.50  fof(f280,plain,(
% 0.21/0.50    spl3_27 <=> ! [X1,X3,X0,X2,X4] : k4_enumset1(X2,X3,X4,X0,X0,X1) = k2_xboole_0(k1_enumset1(X2,X3,X4),k2_tarski(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.50  fof(f284,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k4_enumset1(X0,X0,X1,X2,X2,X3)) ) | (~spl3_4 | ~spl3_27)),
% 0.21/0.50    inference(superposition,[],[f281,f50])).
% 0.21/0.50  fof(f281,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X2,X3,X4,X0,X0,X1) = k2_xboole_0(k1_enumset1(X2,X3,X4),k2_tarski(X0,X1))) ) | ~spl3_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f280])).
% 0.21/0.50  fof(f282,plain,(
% 0.21/0.50    spl3_27 | ~spl3_4 | ~spl3_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f110,f98,f49,f280])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl3_12 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X2,X3,X4,X0,X0,X1) = k2_xboole_0(k1_enumset1(X2,X3,X4),k2_tarski(X0,X1))) ) | (~spl3_4 | ~spl3_12)),
% 0.21/0.50    inference(superposition,[],[f99,f50])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) ) | ~spl3_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f98])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    spl3_26 | ~spl3_4 | ~spl3_10 | ~spl3_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f111,f98,f87,f49,f274])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    spl3_10 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) ) | (~spl3_4 | ~spl3_10 | ~spl3_12)),
% 0.21/0.50    inference(forward_demodulation,[],[f109,f88])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) ) | ~spl3_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f87])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k4_enumset1(X0,X0,X1,X2,X3,X4)) ) | (~spl3_4 | ~spl3_12)),
% 0.21/0.50    inference(superposition,[],[f99,f50])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    spl3_22 | ~spl3_2 | ~spl3_9 | ~spl3_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f96,f87,f81,f41,f183])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    spl3_9 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) ) | (~spl3_2 | ~spl3_9 | ~spl3_10)),
% 0.21/0.50    inference(forward_demodulation,[],[f94,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) ) | ~spl3_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f81])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k3_enumset1(X0,X0,X1,X2,X3)) ) | (~spl3_2 | ~spl3_10)),
% 0.21/0.50    inference(superposition,[],[f88,f42])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    spl3_18 | ~spl3_4 | ~spl3_7 | ~spl3_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f85,f81,f63,f49,f142])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X2,X0,X0,X1) = k1_enumset1(X2,X0,X1)) ) | (~spl3_4 | ~spl3_7 | ~spl3_9)),
% 0.21/0.50    inference(forward_demodulation,[],[f84,f64])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))) ) | (~spl3_4 | ~spl3_9)),
% 0.21/0.50    inference(superposition,[],[f82,f50])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    spl3_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f31,f102])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl3_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f30,f98])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    spl3_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f29,f87])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    spl3_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f28,f81])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f26,f63])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    spl3_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f23,f49])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f21,f41])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ~spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f20,f36])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.50    inference(negated_conjecture,[],[f15])).
% 0.21/0.50  fof(f15,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (30270)------------------------------
% 0.21/0.50  % (30270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30270)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (30270)Memory used [KB]: 6652
% 0.21/0.50  % (30270)Time elapsed: 0.035 s
% 0.21/0.50  % (30270)------------------------------
% 0.21/0.50  % (30270)------------------------------
% 0.21/0.50  % (30264)Success in time 0.141 s
%------------------------------------------------------------------------------
