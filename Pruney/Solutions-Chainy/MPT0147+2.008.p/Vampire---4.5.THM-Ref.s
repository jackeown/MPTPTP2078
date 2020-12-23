%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   68 (  97 expanded)
%              Number of leaves         :   21 (  47 expanded)
%              Depth                    :    6
%              Number of atoms          :  133 ( 191 expanded)
%              Number of equality atoms :   54 (  83 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f392,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f33,f41,f49,f64,f69,f74,f79,f95,f137,f259,f368,f383])).

fof(f383,plain,
    ( spl8_1
    | ~ spl8_10
    | ~ spl8_25
    | ~ spl8_28 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | spl8_1
    | ~ spl8_10
    | ~ spl8_25
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f28,f381])).

fof(f381,plain,
    ( ! [X14,X19,X17,X15,X13,X20,X18,X16] : k2_xboole_0(k2_tarski(X19,X20),k4_enumset1(X13,X14,X15,X16,X17,X18)) = k6_enumset1(X19,X20,X13,X14,X15,X16,X17,X18)
    | ~ spl8_10
    | ~ spl8_25
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f371,f78])).

fof(f78,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl8_10
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f371,plain,
    ( ! [X14,X19,X17,X15,X13,X20,X18,X16] : k2_xboole_0(k2_enumset1(X19,X20,X13,X14),k2_enumset1(X15,X16,X17,X18)) = k2_xboole_0(k2_tarski(X19,X20),k4_enumset1(X13,X14,X15,X16,X17,X18))
    | ~ spl8_25
    | ~ spl8_28 ),
    inference(superposition,[],[f367,f258])).

fof(f258,plain,
    ( ! [X6,X4,X8,X7,X5,X9] : k2_xboole_0(k2_tarski(X9,X4),k2_enumset1(X5,X6,X7,X8)) = k4_enumset1(X9,X4,X5,X6,X7,X8)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl8_25
  <=> ! [X9,X5,X7,X8,X4,X6] : k2_xboole_0(k2_tarski(X9,X4),k2_enumset1(X5,X6,X7,X8)) = k4_enumset1(X9,X4,X5,X6,X7,X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f367,plain,
    ( ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X4,X0),k2_xboole_0(k2_tarski(X1,X2),X3)) = k2_xboole_0(k2_enumset1(X4,X0,X1,X2),X3)
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f366])).

fof(f366,plain,
    ( spl8_28
  <=> ! [X1,X3,X0,X2,X4] : k2_xboole_0(k2_tarski(X4,X0),k2_xboole_0(k2_tarski(X1,X2),X3)) = k2_xboole_0(k2_enumset1(X4,X0,X1,X2),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f28,plain,
    ( k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl8_1
  <=> k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) = k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f368,plain,
    ( spl8_28
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f140,f135,f93,f62,f47,f366])).

fof(f47,plain,
    ( spl8_6
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f62,plain,
    ( spl8_7
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f93,plain,
    ( spl8_12
  <=> ! [X1,X0,X2] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f135,plain,
    ( spl8_14
  <=> ! [X3,X5,X4,X6] : k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f140,plain,
    ( ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X4,X0),k2_xboole_0(k2_tarski(X1,X2),X3)) = k2_xboole_0(k2_enumset1(X4,X0,X1,X2),X3)
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_14 ),
    inference(forward_demodulation,[],[f138,f65])).

fof(f65,plain,
    ( ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_enumset1(X1,X2,X3),X4)) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),X4)
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(superposition,[],[f48,f63])).

fof(f63,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f48,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f138,plain,
    ( ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X4,X0),k2_xboole_0(k2_tarski(X1,X2),X3)) = k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_enumset1(X0,X1,X2),X3))
    | ~ spl8_12
    | ~ spl8_14 ),
    inference(superposition,[],[f94,f136])).

fof(f136,plain,
    ( ! [X6,X4,X5,X3] : k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f135])).

fof(f94,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f93])).

fof(f259,plain,
    ( spl8_25
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f104,f93,f72,f67,f257])).

fof(f67,plain,
    ( spl8_8
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f72,plain,
    ( spl8_9
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f104,plain,
    ( ! [X6,X4,X8,X7,X5,X9] : k2_xboole_0(k2_tarski(X9,X4),k2_enumset1(X5,X6,X7,X8)) = k4_enumset1(X9,X4,X5,X6,X7,X8)
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f97,f73])).

fof(f73,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f72])).

fof(f97,plain,
    ( ! [X6,X4,X8,X7,X5,X9] : k2_xboole_0(k2_tarski(X9,X4),k2_enumset1(X5,X6,X7,X8)) = k2_xboole_0(k1_tarski(X9),k3_enumset1(X4,X5,X6,X7,X8))
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(superposition,[],[f94,f68])).

fof(f68,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f137,plain,
    ( spl8_14
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f57,f47,f39,f135])).

fof(f39,plain,
    ( spl8_4
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f57,plain,
    ( ! [X6,X4,X5,X3] : k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(superposition,[],[f48,f40])).

fof(f40,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f95,plain,
    ( spl8_12
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f56,f47,f31,f93])).

fof(f31,plain,
    ( spl8_2
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f56,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(superposition,[],[f48,f32])).

fof(f32,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f79,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f24,f77])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

fof(f74,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f23,f72])).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f69,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f22,f67])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(f64,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f21,f62])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f49,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f20,f47])).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f41,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f33,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f16,f31])).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f29,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f15,f26])).

fof(f15,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:16:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.43  % (13919)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.46  % (13919)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f392,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f29,f33,f41,f49,f64,f69,f74,f79,f95,f137,f259,f368,f383])).
% 0.22/0.46  fof(f383,plain,(
% 0.22/0.46    spl8_1 | ~spl8_10 | ~spl8_25 | ~spl8_28),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f382])).
% 0.22/0.46  fof(f382,plain,(
% 0.22/0.46    $false | (spl8_1 | ~spl8_10 | ~spl8_25 | ~spl8_28)),
% 0.22/0.46    inference(subsumption_resolution,[],[f28,f381])).
% 0.22/0.46  fof(f381,plain,(
% 0.22/0.46    ( ! [X14,X19,X17,X15,X13,X20,X18,X16] : (k2_xboole_0(k2_tarski(X19,X20),k4_enumset1(X13,X14,X15,X16,X17,X18)) = k6_enumset1(X19,X20,X13,X14,X15,X16,X17,X18)) ) | (~spl8_10 | ~spl8_25 | ~spl8_28)),
% 0.22/0.46    inference(forward_demodulation,[],[f371,f78])).
% 0.22/0.46  fof(f78,plain,(
% 0.22/0.46    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) ) | ~spl8_10),
% 0.22/0.46    inference(avatar_component_clause,[],[f77])).
% 0.22/0.46  fof(f77,plain,(
% 0.22/0.46    spl8_10 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.22/0.46  fof(f371,plain,(
% 0.22/0.46    ( ! [X14,X19,X17,X15,X13,X20,X18,X16] : (k2_xboole_0(k2_enumset1(X19,X20,X13,X14),k2_enumset1(X15,X16,X17,X18)) = k2_xboole_0(k2_tarski(X19,X20),k4_enumset1(X13,X14,X15,X16,X17,X18))) ) | (~spl8_25 | ~spl8_28)),
% 0.22/0.46    inference(superposition,[],[f367,f258])).
% 0.22/0.46  fof(f258,plain,(
% 0.22/0.46    ( ! [X6,X4,X8,X7,X5,X9] : (k2_xboole_0(k2_tarski(X9,X4),k2_enumset1(X5,X6,X7,X8)) = k4_enumset1(X9,X4,X5,X6,X7,X8)) ) | ~spl8_25),
% 0.22/0.46    inference(avatar_component_clause,[],[f257])).
% 0.22/0.46  fof(f257,plain,(
% 0.22/0.46    spl8_25 <=> ! [X9,X5,X7,X8,X4,X6] : k2_xboole_0(k2_tarski(X9,X4),k2_enumset1(X5,X6,X7,X8)) = k4_enumset1(X9,X4,X5,X6,X7,X8)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.22/0.46  fof(f367,plain,(
% 0.22/0.46    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X4,X0),k2_xboole_0(k2_tarski(X1,X2),X3)) = k2_xboole_0(k2_enumset1(X4,X0,X1,X2),X3)) ) | ~spl8_28),
% 0.22/0.46    inference(avatar_component_clause,[],[f366])).
% 0.22/0.46  fof(f366,plain,(
% 0.22/0.46    spl8_28 <=> ! [X1,X3,X0,X2,X4] : k2_xboole_0(k2_tarski(X4,X0),k2_xboole_0(k2_tarski(X1,X2),X3)) = k2_xboole_0(k2_enumset1(X4,X0,X1,X2),X3)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) | spl8_1),
% 0.22/0.46    inference(avatar_component_clause,[],[f26])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    spl8_1 <=> k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) = k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.46  fof(f368,plain,(
% 0.22/0.46    spl8_28 | ~spl8_6 | ~spl8_7 | ~spl8_12 | ~spl8_14),
% 0.22/0.46    inference(avatar_split_clause,[],[f140,f135,f93,f62,f47,f366])).
% 0.22/0.46  fof(f47,plain,(
% 0.22/0.46    spl8_6 <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.46  fof(f62,plain,(
% 0.22/0.46    spl8_7 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.22/0.46  fof(f93,plain,(
% 0.22/0.46    spl8_12 <=> ! [X1,X0,X2] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.22/0.46  fof(f135,plain,(
% 0.22/0.46    spl8_14 <=> ! [X3,X5,X4,X6] : k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.22/0.46  fof(f140,plain,(
% 0.22/0.46    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X4,X0),k2_xboole_0(k2_tarski(X1,X2),X3)) = k2_xboole_0(k2_enumset1(X4,X0,X1,X2),X3)) ) | (~spl8_6 | ~spl8_7 | ~spl8_12 | ~spl8_14)),
% 0.22/0.46    inference(forward_demodulation,[],[f138,f65])).
% 0.22/0.46  fof(f65,plain,(
% 0.22/0.46    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_enumset1(X1,X2,X3),X4)) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),X4)) ) | (~spl8_6 | ~spl8_7)),
% 0.22/0.46    inference(superposition,[],[f48,f63])).
% 0.22/0.46  fof(f63,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) ) | ~spl8_7),
% 0.22/0.46    inference(avatar_component_clause,[],[f62])).
% 0.22/0.46  fof(f48,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl8_6),
% 0.22/0.46    inference(avatar_component_clause,[],[f47])).
% 0.22/0.46  fof(f138,plain,(
% 0.22/0.46    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X4,X0),k2_xboole_0(k2_tarski(X1,X2),X3)) = k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_enumset1(X0,X1,X2),X3))) ) | (~spl8_12 | ~spl8_14)),
% 0.22/0.46    inference(superposition,[],[f94,f136])).
% 0.22/0.46  fof(f136,plain,(
% 0.22/0.46    ( ! [X6,X4,X5,X3] : (k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) ) | ~spl8_14),
% 0.22/0.46    inference(avatar_component_clause,[],[f135])).
% 0.22/0.46  fof(f94,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)) ) | ~spl8_12),
% 0.22/0.46    inference(avatar_component_clause,[],[f93])).
% 0.22/0.46  fof(f259,plain,(
% 0.22/0.46    spl8_25 | ~spl8_8 | ~spl8_9 | ~spl8_12),
% 0.22/0.46    inference(avatar_split_clause,[],[f104,f93,f72,f67,f257])).
% 0.22/0.46  fof(f67,plain,(
% 0.22/0.46    spl8_8 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.22/0.46  fof(f72,plain,(
% 0.22/0.46    spl8_9 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.22/0.46  fof(f104,plain,(
% 0.22/0.46    ( ! [X6,X4,X8,X7,X5,X9] : (k2_xboole_0(k2_tarski(X9,X4),k2_enumset1(X5,X6,X7,X8)) = k4_enumset1(X9,X4,X5,X6,X7,X8)) ) | (~spl8_8 | ~spl8_9 | ~spl8_12)),
% 0.22/0.46    inference(forward_demodulation,[],[f97,f73])).
% 0.22/0.46  fof(f73,plain,(
% 0.22/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) ) | ~spl8_9),
% 0.22/0.46    inference(avatar_component_clause,[],[f72])).
% 0.22/0.46  fof(f97,plain,(
% 0.22/0.46    ( ! [X6,X4,X8,X7,X5,X9] : (k2_xboole_0(k2_tarski(X9,X4),k2_enumset1(X5,X6,X7,X8)) = k2_xboole_0(k1_tarski(X9),k3_enumset1(X4,X5,X6,X7,X8))) ) | (~spl8_8 | ~spl8_12)),
% 0.22/0.46    inference(superposition,[],[f94,f68])).
% 0.22/0.46  fof(f68,plain,(
% 0.22/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) ) | ~spl8_8),
% 0.22/0.46    inference(avatar_component_clause,[],[f67])).
% 0.22/0.46  fof(f137,plain,(
% 0.22/0.46    spl8_14 | ~spl8_4 | ~spl8_6),
% 0.22/0.46    inference(avatar_split_clause,[],[f57,f47,f39,f135])).
% 0.22/0.46  fof(f39,plain,(
% 0.22/0.46    spl8_4 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.46  fof(f57,plain,(
% 0.22/0.46    ( ! [X6,X4,X5,X3] : (k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) ) | (~spl8_4 | ~spl8_6)),
% 0.22/0.46    inference(superposition,[],[f48,f40])).
% 0.22/0.46  fof(f40,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) ) | ~spl8_4),
% 0.22/0.46    inference(avatar_component_clause,[],[f39])).
% 0.22/0.46  fof(f95,plain,(
% 0.22/0.46    spl8_12 | ~spl8_2 | ~spl8_6),
% 0.22/0.46    inference(avatar_split_clause,[],[f56,f47,f31,f93])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    spl8_2 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.46  fof(f56,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)) ) | (~spl8_2 | ~spl8_6)),
% 0.22/0.46    inference(superposition,[],[f48,f32])).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ) | ~spl8_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f31])).
% 0.22/0.46  fof(f79,plain,(
% 0.22/0.46    spl8_10),
% 0.22/0.46    inference(avatar_split_clause,[],[f24,f77])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).
% 0.22/0.46  fof(f74,plain,(
% 0.22/0.46    spl8_9),
% 0.22/0.46    inference(avatar_split_clause,[],[f23,f72])).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f9])).
% 0.22/0.46  fof(f9,axiom,(
% 0.22/0.46    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 0.22/0.46  fof(f69,plain,(
% 0.22/0.46    spl8_8),
% 0.22/0.46    inference(avatar_split_clause,[],[f22,f67])).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,axiom,(
% 0.22/0.46    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
% 0.22/0.46  fof(f64,plain,(
% 0.22/0.46    spl8_7),
% 0.22/0.46    inference(avatar_split_clause,[],[f21,f62])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,axiom,(
% 0.22/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.22/0.46  fof(f49,plain,(
% 0.22/0.46    spl8_6),
% 0.22/0.46    inference(avatar_split_clause,[],[f20,f47])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.46  fof(f41,plain,(
% 0.22/0.46    spl8_4),
% 0.22/0.46    inference(avatar_split_clause,[],[f18,f39])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    spl8_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f16,f31])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    ~spl8_1),
% 0.22/0.46    inference(avatar_split_clause,[],[f15,f26])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.22/0.46    inference(cnf_transformation,[],[f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f12,f13])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.22/0.46    inference(ennf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,negated_conjecture,(
% 0.22/0.46    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.22/0.46    inference(negated_conjecture,[],[f10])).
% 0.22/0.46  fof(f10,conjecture,(
% 0.22/0.46    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (13919)------------------------------
% 0.22/0.46  % (13919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (13919)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (13919)Memory used [KB]: 6524
% 0.22/0.46  % (13919)Time elapsed: 0.044 s
% 0.22/0.46  % (13919)------------------------------
% 0.22/0.46  % (13919)------------------------------
% 0.22/0.46  % (13913)Success in time 0.092 s
%------------------------------------------------------------------------------
