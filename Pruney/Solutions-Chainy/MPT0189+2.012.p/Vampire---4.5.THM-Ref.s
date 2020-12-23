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
% DateTime   : Thu Dec  3 12:34:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 142 expanded)
%              Number of leaves         :   25 (  66 expanded)
%              Depth                    :    6
%              Number of atoms          :  147 ( 245 expanded)
%              Number of equality atoms :   69 ( 128 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f539,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f70,f136,f140,f144,f174,f186,f254,f262,f362,f382,f446,f538])).

fof(f538,plain,
    ( spl4_1
    | ~ spl4_21
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f537])).

fof(f537,plain,
    ( $false
    | spl4_1
    | ~ spl4_21
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f65,f475])).

fof(f475,plain,
    ( ! [X35,X33,X34,X32] : k2_enumset1(X34,X35,X32,X33) = k2_enumset1(X35,X34,X32,X33)
    | ~ spl4_21
    | ~ spl4_22 ),
    inference(superposition,[],[f445,f381])).

fof(f381,plain,
    ( ! [X17,X15,X18,X16] : k2_enumset1(X15,X16,X17,X18) = k2_enumset1(X17,X18,X15,X16)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f380])).

fof(f380,plain,
    ( spl4_21
  <=> ! [X16,X18,X15,X17] : k2_enumset1(X15,X16,X17,X18) = k2_enumset1(X17,X18,X15,X16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f445,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X3,X2) = k2_enumset1(X2,X3,X0,X1)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f444])).

fof(f444,plain,
    ( spl4_22
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X3,X2) = k2_enumset1(X2,X3,X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f65,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f446,plain,
    ( spl4_22
    | ~ spl4_2
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f383,f380,f68,f444])).

fof(f68,plain,
    ( spl4_2
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f383,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X3,X2) = k2_enumset1(X2,X3,X0,X1)
    | ~ spl4_2
    | ~ spl4_21 ),
    inference(superposition,[],[f381,f69])).

fof(f69,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f382,plain,
    ( spl4_21
    | ~ spl4_17
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f370,f360,f260,f380])).

fof(f260,plain,
    ( spl4_17
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X1,X0,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f360,plain,
    ( spl4_18
  <=> ! [X1,X3,X0,X2] : k6_enumset1(X0,X0,X0,X0,X1,X0,X2,X3) = k2_enumset1(X2,X3,X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f370,plain,
    ( ! [X17,X15,X18,X16] : k2_enumset1(X15,X16,X17,X18) = k2_enumset1(X17,X18,X15,X16)
    | ~ spl4_17
    | ~ spl4_18 ),
    inference(superposition,[],[f361,f261])).

fof(f261,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X1,X0,X2,X3)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f260])).

fof(f361,plain,
    ( ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X0,X2,X3) = k2_enumset1(X2,X3,X0,X1)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f360])).

fof(f362,plain,
    ( spl4_18
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f347,f184,f172,f134,f360])).

fof(f134,plain,
    ( spl4_6
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f172,plain,
    ( spl4_11
  <=> ! [X1,X3,X0,X2,X4] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k2_enumset1(X0,X0,X2,X1),k5_xboole_0(k2_enumset1(X3,X3,X3,X4),k3_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X2,X1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f184,plain,
    ( spl4_14
  <=> ! [X9,X5,X7,X8,X6] : k6_enumset1(X5,X5,X5,X5,X6,X7,X8,X9) = k5_xboole_0(k2_enumset1(X8,X8,X8,X9),k5_xboole_0(k2_enumset1(X5,X5,X6,X7),k3_xboole_0(k2_enumset1(X5,X5,X6,X7),k2_enumset1(X8,X8,X8,X9)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f347,plain,
    ( ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X0,X2,X3) = k2_enumset1(X2,X3,X0,X1)
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f331,f135])).

fof(f135,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f331,plain,
    ( ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X0,X2,X3) = k6_enumset1(X2,X2,X2,X2,X2,X3,X0,X1)
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(superposition,[],[f185,f173])).

fof(f173,plain,
    ( ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k2_enumset1(X0,X0,X2,X1),k5_xboole_0(k2_enumset1(X3,X3,X3,X4),k3_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X2,X1))))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f172])).

fof(f185,plain,
    ( ! [X6,X8,X7,X5,X9] : k6_enumset1(X5,X5,X5,X5,X6,X7,X8,X9) = k5_xboole_0(k2_enumset1(X8,X8,X8,X9),k5_xboole_0(k2_enumset1(X5,X5,X6,X7),k3_xboole_0(k2_enumset1(X5,X5,X6,X7),k2_enumset1(X8,X8,X8,X9))))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f184])).

fof(f262,plain,
    ( spl4_17
    | ~ spl4_6
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f255,f252,f134,f260])).

fof(f252,plain,
    ( spl4_16
  <=> ! [X9,X5,X7,X8,X6] : k6_enumset1(X5,X5,X5,X5,X6,X7,X8,X9) = k6_enumset1(X5,X5,X5,X5,X7,X6,X8,X9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f255,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X1,X0,X2,X3)
    | ~ spl4_6
    | ~ spl4_16 ),
    inference(superposition,[],[f253,f135])).

fof(f253,plain,
    ( ! [X6,X8,X7,X5,X9] : k6_enumset1(X5,X5,X5,X5,X6,X7,X8,X9) = k6_enumset1(X5,X5,X5,X5,X7,X6,X8,X9)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f252])).

fof(f254,plain,
    ( spl4_16
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f241,f172,f142,f252])).

fof(f142,plain,
    ( spl4_8
  <=> ! [X1,X3,X0,X2,X4] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k5_xboole_0(k2_enumset1(X3,X3,X3,X4),k3_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f241,plain,
    ( ! [X6,X8,X7,X5,X9] : k6_enumset1(X5,X5,X5,X5,X6,X7,X8,X9) = k6_enumset1(X5,X5,X5,X5,X7,X6,X8,X9)
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(superposition,[],[f173,f143])).

fof(f143,plain,
    ( ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k5_xboole_0(k2_enumset1(X3,X3,X3,X4),k3_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f142])).

fof(f186,plain,
    ( spl4_14
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f159,f142,f138,f184])).

fof(f138,plain,
    ( spl4_7
  <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f159,plain,
    ( ! [X6,X8,X7,X5,X9] : k6_enumset1(X5,X5,X5,X5,X6,X7,X8,X9) = k5_xboole_0(k2_enumset1(X8,X8,X8,X9),k5_xboole_0(k2_enumset1(X5,X5,X6,X7),k3_xboole_0(k2_enumset1(X5,X5,X6,X7),k2_enumset1(X8,X8,X8,X9))))
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(superposition,[],[f143,f139])).

fof(f139,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f138])).

fof(f174,plain,
    ( spl4_11
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f151,f142,f68,f172])).

fof(f151,plain,
    ( ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k2_enumset1(X0,X0,X2,X1),k5_xboole_0(k2_enumset1(X3,X3,X3,X4),k3_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X2,X1))))
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(superposition,[],[f143,f69])).

fof(f144,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f55,f142])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k5_xboole_0(k2_enumset1(X3,X3,X3,X4),k3_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2)))) ),
    inference(definition_unfolding,[],[f37,f51,f47,f32,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f32])).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f36,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

fof(f140,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f54,f138])).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f47,f47])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f136,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f52,f134])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f35,f51])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f70,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f33,f68])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

fof(f66,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f26,f63])).

fof(f26,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:31:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (3778)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (3783)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (3777)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (3779)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (3780)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (3791)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (3785)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (3792)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.50  % (3786)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (3790)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (3784)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.51  % (3787)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.51  % (3782)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.51  % (3789)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.51  % (3781)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (3793)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.52  % (3788)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.52  % (3788)Refutation not found, incomplete strategy% (3788)------------------------------
% 0.22/0.52  % (3788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (3788)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (3788)Memory used [KB]: 10618
% 0.22/0.52  % (3788)Time elapsed: 0.099 s
% 0.22/0.52  % (3788)------------------------------
% 0.22/0.52  % (3788)------------------------------
% 0.22/0.53  % (3794)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.53  % (3784)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f539,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f66,f70,f136,f140,f144,f174,f186,f254,f262,f362,f382,f446,f538])).
% 0.22/0.54  fof(f538,plain,(
% 0.22/0.54    spl4_1 | ~spl4_21 | ~spl4_22),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f537])).
% 0.22/0.54  fof(f537,plain,(
% 0.22/0.54    $false | (spl4_1 | ~spl4_21 | ~spl4_22)),
% 0.22/0.54    inference(subsumption_resolution,[],[f65,f475])).
% 0.22/0.54  fof(f475,plain,(
% 0.22/0.54    ( ! [X35,X33,X34,X32] : (k2_enumset1(X34,X35,X32,X33) = k2_enumset1(X35,X34,X32,X33)) ) | (~spl4_21 | ~spl4_22)),
% 0.22/0.54    inference(superposition,[],[f445,f381])).
% 0.22/0.54  fof(f381,plain,(
% 0.22/0.54    ( ! [X17,X15,X18,X16] : (k2_enumset1(X15,X16,X17,X18) = k2_enumset1(X17,X18,X15,X16)) ) | ~spl4_21),
% 0.22/0.54    inference(avatar_component_clause,[],[f380])).
% 0.22/0.54  fof(f380,plain,(
% 0.22/0.54    spl4_21 <=> ! [X16,X18,X15,X17] : k2_enumset1(X15,X16,X17,X18) = k2_enumset1(X17,X18,X15,X16)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.54  fof(f445,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X3,X2) = k2_enumset1(X2,X3,X0,X1)) ) | ~spl4_22),
% 0.22/0.54    inference(avatar_component_clause,[],[f444])).
% 0.22/0.54  fof(f444,plain,(
% 0.22/0.54    spl4_22 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X3,X2) = k2_enumset1(X2,X3,X0,X1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) | spl4_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK0,sK2,sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.54  fof(f446,plain,(
% 0.22/0.54    spl4_22 | ~spl4_2 | ~spl4_21),
% 0.22/0.54    inference(avatar_split_clause,[],[f383,f380,f68,f444])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    spl4_2 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.54  fof(f383,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X3,X2) = k2_enumset1(X2,X3,X0,X1)) ) | (~spl4_2 | ~spl4_21)),
% 0.22/0.54    inference(superposition,[],[f381,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) ) | ~spl4_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f68])).
% 0.22/0.54  fof(f382,plain,(
% 0.22/0.54    spl4_21 | ~spl4_17 | ~spl4_18),
% 0.22/0.54    inference(avatar_split_clause,[],[f370,f360,f260,f380])).
% 0.22/0.54  fof(f260,plain,(
% 0.22/0.54    spl4_17 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X1,X0,X2,X3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.54  fof(f360,plain,(
% 0.22/0.54    spl4_18 <=> ! [X1,X3,X0,X2] : k6_enumset1(X0,X0,X0,X0,X1,X0,X2,X3) = k2_enumset1(X2,X3,X0,X1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.54  fof(f370,plain,(
% 0.22/0.54    ( ! [X17,X15,X18,X16] : (k2_enumset1(X15,X16,X17,X18) = k2_enumset1(X17,X18,X15,X16)) ) | (~spl4_17 | ~spl4_18)),
% 0.22/0.54    inference(superposition,[],[f361,f261])).
% 0.22/0.54  fof(f261,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X1,X0,X2,X3)) ) | ~spl4_17),
% 0.22/0.54    inference(avatar_component_clause,[],[f260])).
% 0.22/0.54  fof(f361,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X0,X2,X3) = k2_enumset1(X2,X3,X0,X1)) ) | ~spl4_18),
% 0.22/0.54    inference(avatar_component_clause,[],[f360])).
% 0.22/0.54  fof(f362,plain,(
% 0.22/0.54    spl4_18 | ~spl4_6 | ~spl4_11 | ~spl4_14),
% 0.22/0.54    inference(avatar_split_clause,[],[f347,f184,f172,f134,f360])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    spl4_6 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    spl4_11 <=> ! [X1,X3,X0,X2,X4] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k2_enumset1(X0,X0,X2,X1),k5_xboole_0(k2_enumset1(X3,X3,X3,X4),k3_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X2,X1))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.54  fof(f184,plain,(
% 0.22/0.54    spl4_14 <=> ! [X9,X5,X7,X8,X6] : k6_enumset1(X5,X5,X5,X5,X6,X7,X8,X9) = k5_xboole_0(k2_enumset1(X8,X8,X8,X9),k5_xboole_0(k2_enumset1(X5,X5,X6,X7),k3_xboole_0(k2_enumset1(X5,X5,X6,X7),k2_enumset1(X8,X8,X8,X9))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.54  fof(f347,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X0,X2,X3) = k2_enumset1(X2,X3,X0,X1)) ) | (~spl4_6 | ~spl4_11 | ~spl4_14)),
% 0.22/0.54    inference(forward_demodulation,[],[f331,f135])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) ) | ~spl4_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f134])).
% 0.22/0.54  fof(f331,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X0,X2,X3) = k6_enumset1(X2,X2,X2,X2,X2,X3,X0,X1)) ) | (~spl4_11 | ~spl4_14)),
% 0.22/0.54    inference(superposition,[],[f185,f173])).
% 0.22/0.54  fof(f173,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k2_enumset1(X0,X0,X2,X1),k5_xboole_0(k2_enumset1(X3,X3,X3,X4),k3_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X2,X1))))) ) | ~spl4_11),
% 0.22/0.54    inference(avatar_component_clause,[],[f172])).
% 0.22/0.54  fof(f185,plain,(
% 0.22/0.54    ( ! [X6,X8,X7,X5,X9] : (k6_enumset1(X5,X5,X5,X5,X6,X7,X8,X9) = k5_xboole_0(k2_enumset1(X8,X8,X8,X9),k5_xboole_0(k2_enumset1(X5,X5,X6,X7),k3_xboole_0(k2_enumset1(X5,X5,X6,X7),k2_enumset1(X8,X8,X8,X9))))) ) | ~spl4_14),
% 0.22/0.54    inference(avatar_component_clause,[],[f184])).
% 0.22/0.54  fof(f262,plain,(
% 0.22/0.54    spl4_17 | ~spl4_6 | ~spl4_16),
% 0.22/0.54    inference(avatar_split_clause,[],[f255,f252,f134,f260])).
% 0.22/0.54  fof(f252,plain,(
% 0.22/0.54    spl4_16 <=> ! [X9,X5,X7,X8,X6] : k6_enumset1(X5,X5,X5,X5,X6,X7,X8,X9) = k6_enumset1(X5,X5,X5,X5,X7,X6,X8,X9)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.54  fof(f255,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X1,X0,X2,X3)) ) | (~spl4_6 | ~spl4_16)),
% 0.22/0.54    inference(superposition,[],[f253,f135])).
% 0.22/0.54  fof(f253,plain,(
% 0.22/0.54    ( ! [X6,X8,X7,X5,X9] : (k6_enumset1(X5,X5,X5,X5,X6,X7,X8,X9) = k6_enumset1(X5,X5,X5,X5,X7,X6,X8,X9)) ) | ~spl4_16),
% 0.22/0.54    inference(avatar_component_clause,[],[f252])).
% 0.22/0.54  fof(f254,plain,(
% 0.22/0.54    spl4_16 | ~spl4_8 | ~spl4_11),
% 0.22/0.54    inference(avatar_split_clause,[],[f241,f172,f142,f252])).
% 0.22/0.54  fof(f142,plain,(
% 0.22/0.54    spl4_8 <=> ! [X1,X3,X0,X2,X4] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k5_xboole_0(k2_enumset1(X3,X3,X3,X4),k3_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.54  fof(f241,plain,(
% 0.22/0.54    ( ! [X6,X8,X7,X5,X9] : (k6_enumset1(X5,X5,X5,X5,X6,X7,X8,X9) = k6_enumset1(X5,X5,X5,X5,X7,X6,X8,X9)) ) | (~spl4_8 | ~spl4_11)),
% 0.22/0.54    inference(superposition,[],[f173,f143])).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k5_xboole_0(k2_enumset1(X3,X3,X3,X4),k3_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))))) ) | ~spl4_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f142])).
% 0.22/0.54  fof(f186,plain,(
% 0.22/0.54    spl4_14 | ~spl4_7 | ~spl4_8),
% 0.22/0.54    inference(avatar_split_clause,[],[f159,f142,f138,f184])).
% 0.22/0.54  fof(f138,plain,(
% 0.22/0.54    spl4_7 <=> ! [X1,X0] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.54  fof(f159,plain,(
% 0.22/0.54    ( ! [X6,X8,X7,X5,X9] : (k6_enumset1(X5,X5,X5,X5,X6,X7,X8,X9) = k5_xboole_0(k2_enumset1(X8,X8,X8,X9),k5_xboole_0(k2_enumset1(X5,X5,X6,X7),k3_xboole_0(k2_enumset1(X5,X5,X6,X7),k2_enumset1(X8,X8,X8,X9))))) ) | (~spl4_7 | ~spl4_8)),
% 0.22/0.54    inference(superposition,[],[f143,f139])).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ) | ~spl4_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f138])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    spl4_11 | ~spl4_2 | ~spl4_8),
% 0.22/0.54    inference(avatar_split_clause,[],[f151,f142,f68,f172])).
% 0.22/0.54  fof(f151,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k2_enumset1(X0,X0,X2,X1),k5_xboole_0(k2_enumset1(X3,X3,X3,X4),k3_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X2,X1))))) ) | (~spl4_2 | ~spl4_8)),
% 0.22/0.54    inference(superposition,[],[f143,f69])).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    spl4_8),
% 0.22/0.54    inference(avatar_split_clause,[],[f55,f142])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k5_xboole_0(k2_enumset1(X3,X3,X3,X4),k3_xboole_0(k2_enumset1(X3,X3,X3,X4),k2_enumset1(X0,X0,X1,X2))))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f37,f51,f47,f32,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f29,f32])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f31,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f36,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f38,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).
% 0.22/0.54  fof(f140,plain,(
% 0.22/0.54    spl4_7),
% 0.22/0.54    inference(avatar_split_clause,[],[f54,f138])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f28,f47,f47])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    spl4_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f52,f134])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f35,f51])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    spl4_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f33,f68])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ~spl4_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f26,f63])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 0.22/0.54    inference(ennf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 0.22/0.54    inference(negated_conjecture,[],[f21])).
% 0.22/0.54  fof(f21,conjecture,(
% 0.22/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (3784)------------------------------
% 0.22/0.54  % (3784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (3784)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (3784)Memory used [KB]: 6652
% 0.22/0.54  % (3784)Time elapsed: 0.069 s
% 0.22/0.54  % (3784)------------------------------
% 0.22/0.54  % (3784)------------------------------
% 0.22/0.54  % (3776)Success in time 0.174 s
%------------------------------------------------------------------------------
