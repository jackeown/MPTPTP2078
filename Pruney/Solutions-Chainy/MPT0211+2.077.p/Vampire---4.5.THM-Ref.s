%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 553 expanded)
%              Number of leaves         :   19 ( 201 expanded)
%              Depth                    :   14
%              Number of atoms          :   96 ( 584 expanded)
%              Number of equality atoms :   66 ( 547 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f857,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f152,f832,f839,f856])).

fof(f856,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f845])).

fof(f845,plain,
    ( $false
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f93,f838])).

fof(f838,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f836])).

fof(f836,plain,
    ( spl3_5
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f93,plain,(
    ! [X14,X12,X15,X13] : k5_enumset1(X12,X12,X12,X12,X14,X15,X13) = k5_enumset1(X12,X12,X12,X12,X15,X14,X13) ),
    inference(superposition,[],[f48,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X2,X3,X1) ),
    inference(definition_unfolding,[],[f30,f41,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f34,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X3,X2,X1) ),
    inference(definition_unfolding,[],[f31,f41,f41])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(f839,plain,
    ( ~ spl3_5
    | spl3_4 ),
    inference(avatar_split_clause,[],[f833,f829,f836])).

fof(f829,plain,
    ( spl3_4
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f833,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2)
    | spl3_4 ),
    inference(superposition,[],[f831,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X5),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X5),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) ),
    inference(definition_unfolding,[],[f38,f37,f39,f41,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f28,f41])).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

fof(f831,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f829])).

fof(f832,plain,
    ( ~ spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f827,f149,f829])).

fof(f149,plain,
    ( spl3_2
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f827,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_2 ),
    inference(forward_demodulation,[],[f826,f271])).

fof(f271,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X1,X2,X3,X4,X4) ),
    inference(superposition,[],[f52,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X4),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X4),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) ),
    inference(definition_unfolding,[],[f36,f40,f39,f41,f44])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f43])).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(f826,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_2 ),
    inference(forward_demodulation,[],[f825,f271])).

fof(f825,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_2 ),
    inference(forward_demodulation,[],[f725,f271])).

fof(f725,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1))))
    | spl3_2 ),
    inference(backward_demodulation,[],[f151,f271])).

fof(f151,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f149])).

fof(f152,plain,
    ( ~ spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f147,f54,f149])).

fof(f54,plain,
    ( spl3_1
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f147,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f146,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X1,X1,X1,X1,X3,X2,X0) ),
    inference(definition_unfolding,[],[f32,f41,f41])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

fof(f146,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK0,sK2,sK2),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK0,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f145,f47])).

fof(f145,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK0,sK2),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f144,f47])).

fof(f144,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f143,f49])).

fof(f143,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f142,f47])).

fof(f142,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f56,f47])).

fof(f56,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f57,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f45,f54])).

fof(f45,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) ),
    inference(definition_unfolding,[],[f22,f42,f39,f43,f43])).

fof(f22,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:37 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.41  % (9379)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.43  % (9374)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.44  % (9382)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.44  % (9376)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.45  % (9377)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.45  % (9386)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.45  % (9382)Refutation not found, incomplete strategy% (9382)------------------------------
% 0.21/0.45  % (9382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (9382)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (9382)Memory used [KB]: 10618
% 0.21/0.45  % (9382)Time elapsed: 0.058 s
% 0.21/0.45  % (9382)------------------------------
% 0.21/0.45  % (9382)------------------------------
% 0.21/0.45  % (9371)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.45  % (9384)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.45  % (9378)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.45  % (9375)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.45  % (9373)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.45  % (9385)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (9372)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (9381)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (9387)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (9380)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (9383)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (9388)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (9377)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f857,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f57,f152,f832,f839,f856])).
% 0.21/0.53  fof(f856,plain,(
% 0.21/0.53    spl3_5),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f845])).
% 0.21/0.53  fof(f845,plain,(
% 0.21/0.53    $false | spl3_5),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f93,f838])).
% 0.21/0.53  fof(f838,plain,(
% 0.21/0.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2) | spl3_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f836])).
% 0.21/0.53  fof(f836,plain,(
% 0.21/0.53    spl3_5 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ( ! [X14,X12,X15,X13] : (k5_enumset1(X12,X12,X12,X12,X14,X15,X13) = k5_enumset1(X12,X12,X12,X12,X15,X14,X13)) )),
% 0.21/0.53    inference(superposition,[],[f48,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X2,X3,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f30,f41,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f34,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f35,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X3,X2,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f31,f41,f41])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).
% 0.21/0.53  fof(f839,plain,(
% 0.21/0.53    ~spl3_5 | spl3_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f833,f829,f836])).
% 0.21/0.53  fof(f829,plain,(
% 0.21/0.53    spl3_4 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.53  fof(f833,plain,(
% 0.21/0.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2) | spl3_4),
% 0.21/0.53    inference(superposition,[],[f831,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X5),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X5),k5_enumset1(X0,X0,X0,X0,X1,X2,X3))))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f38,f37,f39,f41,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f24,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f28,f41])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f26,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).
% 0.21/0.53  fof(f831,plain,(
% 0.21/0.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f829])).
% 0.21/0.53  fof(f832,plain,(
% 0.21/0.53    ~spl3_4 | spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f827,f149,f829])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    spl3_2 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.53  fof(f827,plain,(
% 0.21/0.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_2),
% 0.21/0.53    inference(forward_demodulation,[],[f826,f271])).
% 0.21/0.53  fof(f271,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X1,X2,X3,X4,X4)) )),
% 0.21/0.53    inference(superposition,[],[f52,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X4),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X4),k5_enumset1(X0,X0,X0,X0,X1,X2,X3))))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f36,f40,f39,f41,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f23,f43])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).
% 0.21/0.53  fof(f826,plain,(
% 0.21/0.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_2),
% 0.21/0.53    inference(forward_demodulation,[],[f825,f271])).
% 0.21/0.53  fof(f825,plain,(
% 0.21/0.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_2),
% 0.21/0.53    inference(forward_demodulation,[],[f725,f271])).
% 0.21/0.53  fof(f725,plain,(
% 0.21/0.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1)))) | spl3_2),
% 0.21/0.53    inference(backward_demodulation,[],[f151,f271])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f149])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    ~spl3_2 | spl3_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f147,f54,f149])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    spl3_1 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 0.21/0.53    inference(forward_demodulation,[],[f146,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X1,X1,X1,X1,X3,X2,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f32,f41,f41])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK0,sK2,sK2),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK0,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 0.21/0.53    inference(forward_demodulation,[],[f145,f47])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK0,sK2),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 0.21/0.53    inference(forward_demodulation,[],[f144,f47])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 0.21/0.53    inference(forward_demodulation,[],[f143,f49])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1)))) | spl3_1),
% 0.21/0.53    inference(forward_demodulation,[],[f142,f47])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1)))) | spl3_1),
% 0.21/0.53    inference(forward_demodulation,[],[f56,f47])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) | spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f54])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ~spl3_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f45,f54])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0))))),
% 0.21/0.53    inference(definition_unfolding,[],[f22,f42,f39,f43,f43])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.53    inference(negated_conjecture,[],[f17])).
% 0.21/0.53  fof(f17,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (9377)------------------------------
% 0.21/0.53  % (9377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (9377)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (9377)Memory used [KB]: 6780
% 0.21/0.53  % (9377)Time elapsed: 0.106 s
% 0.21/0.53  % (9377)------------------------------
% 0.21/0.53  % (9377)------------------------------
% 0.21/0.53  % (9370)Success in time 0.173 s
%------------------------------------------------------------------------------
