%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 513 expanded)
%              Number of leaves         :   19 ( 187 expanded)
%              Depth                    :   14
%              Number of atoms          :   92 ( 542 expanded)
%              Number of equality atoms :   64 ( 507 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f667,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f154,f642,f650,f666])).

fof(f666,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f661])).

fof(f661,plain,
    ( $false
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f107,f649])).

fof(f649,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f647])).

fof(f647,plain,
    ( spl3_5
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f107,plain,(
    ! [X14,X12,X15,X13] : k5_enumset1(X13,X13,X13,X13,X15,X14,X12) = k5_enumset1(X15,X15,X15,X15,X14,X13,X12) ),
    inference(superposition,[],[f54,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X1,X1,X1,X1,X3,X2,X0) ),
    inference(definition_unfolding,[],[f33,f45,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f35,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f34,f45,f45])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(f650,plain,
    ( ~ spl3_5
    | spl3_4 ),
    inference(avatar_split_clause,[],[f643,f639,f647])).

fof(f639,plain,
    ( spl3_4
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f643,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2)
    | spl3_4 ),
    inference(superposition,[],[f641,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X5),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X5),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) ),
    inference(definition_unfolding,[],[f40,f38,f43,f45,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f30,f45])).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

fof(f641,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f639])).

fof(f642,plain,
    ( ~ spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f637,f151,f639])).

fof(f151,plain,
    ( spl3_2
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f637,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_2 ),
    inference(forward_demodulation,[],[f636,f245])).

fof(f245,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X1,X2,X3,X4,X4) ),
    inference(superposition,[],[f57,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X4),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X4),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) ),
    inference(definition_unfolding,[],[f37,f44,f43,f45,f49])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f48])).

fof(f25,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(f636,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_2 ),
    inference(forward_demodulation,[],[f635,f245])).

fof(f635,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_2 ),
    inference(forward_demodulation,[],[f549,f245])).

fof(f549,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1))))
    | spl3_2 ),
    inference(backward_demodulation,[],[f153,f245])).

fof(f153,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f151])).

fof(f154,plain,
    ( ~ spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f149,f60,f151])).

fof(f60,plain,
    ( spl3_1
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f149,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f148,f53])).

fof(f148,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK0,sK2,sK2),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK0,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f147,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X3,X2,X1) ),
    inference(definition_unfolding,[],[f32,f45,f45])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(f147,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f146,f53])).

fof(f146,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f62,f52])).

fof(f62,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f63,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f50,f60])).

fof(f50,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) ),
    inference(definition_unfolding,[],[f24,f46,f43,f48,f48])).

fof(f24,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:12 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.41  % (7275)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.41  % (7275)Refutation not found, incomplete strategy% (7275)------------------------------
% 0.19/0.41  % (7275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.41  % (7275)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.41  
% 0.19/0.41  % (7275)Memory used [KB]: 10618
% 0.19/0.41  % (7275)Time elapsed: 0.004 s
% 0.19/0.41  % (7275)------------------------------
% 0.19/0.41  % (7275)------------------------------
% 0.20/0.44  % (7278)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.45  % (7266)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (7265)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (7264)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (7281)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.47  % (7277)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (7273)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (7276)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (7267)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (7269)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (7268)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (7274)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (7270)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (7272)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.50  % (7271)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.51  % (7280)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.52  % (7279)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.54  % (7270)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f667,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f63,f154,f642,f650,f666])).
% 0.20/0.54  fof(f666,plain,(
% 0.20/0.54    spl3_5),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f661])).
% 0.20/0.54  fof(f661,plain,(
% 0.20/0.54    $false | spl3_5),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f107,f649])).
% 0.20/0.54  fof(f649,plain,(
% 0.20/0.54    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2) | spl3_5),
% 0.20/0.54    inference(avatar_component_clause,[],[f647])).
% 0.20/0.54  fof(f647,plain,(
% 0.20/0.54    spl3_5 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.54  fof(f107,plain,(
% 0.20/0.54    ( ! [X14,X12,X15,X13] : (k5_enumset1(X13,X13,X13,X13,X15,X14,X12) = k5_enumset1(X15,X15,X15,X15,X14,X13,X12)) )),
% 0.20/0.54    inference(superposition,[],[f54,f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X1,X1,X1,X1,X3,X2,X0)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f33,f45,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f35,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f36,f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f34,f45,f45])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).
% 0.20/0.54  fof(f650,plain,(
% 0.20/0.54    ~spl3_5 | spl3_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f643,f639,f647])).
% 0.20/0.54  fof(f639,plain,(
% 0.20/0.54    spl3_4 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.54  fof(f643,plain,(
% 0.20/0.54    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2) | spl3_4),
% 0.20/0.54    inference(superposition,[],[f641,f57])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X5),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X5),k5_enumset1(X0,X0,X0,X0,X1,X2,X3))))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f40,f38,f43,f45,f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f26,f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f30,f45])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,axiom,(
% 0.20/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f28,f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).
% 0.20/0.54  fof(f641,plain,(
% 0.20/0.54    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_4),
% 0.20/0.54    inference(avatar_component_clause,[],[f639])).
% 0.20/0.54  fof(f642,plain,(
% 0.20/0.54    ~spl3_4 | spl3_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f637,f151,f639])).
% 0.20/0.54  fof(f151,plain,(
% 0.20/0.54    spl3_2 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1))))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.54  fof(f637,plain,(
% 0.20/0.54    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_2),
% 0.20/0.54    inference(forward_demodulation,[],[f636,f245])).
% 0.20/0.54  fof(f245,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X1,X2,X3,X4,X4)) )),
% 0.20/0.54    inference(superposition,[],[f57,f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X4),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X4),k5_enumset1(X0,X0,X0,X0,X1,X2,X3))))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f37,f44,f43,f45,f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f25,f48])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).
% 0.20/0.54  fof(f636,plain,(
% 0.20/0.54    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_2),
% 0.20/0.54    inference(forward_demodulation,[],[f635,f245])).
% 0.20/0.54  fof(f635,plain,(
% 0.20/0.54    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_2),
% 0.20/0.54    inference(forward_demodulation,[],[f549,f245])).
% 0.20/0.54  fof(f549,plain,(
% 0.20/0.54    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1)))) | spl3_2),
% 0.20/0.54    inference(backward_demodulation,[],[f153,f245])).
% 0.20/0.54  fof(f153,plain,(
% 0.20/0.54    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f151])).
% 0.20/0.54  fof(f154,plain,(
% 0.20/0.54    ~spl3_2 | spl3_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f149,f60,f151])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    spl3_1 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0))))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.54  fof(f149,plain,(
% 0.20/0.54    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 0.20/0.54    inference(forward_demodulation,[],[f148,f53])).
% 0.20/0.54  fof(f148,plain,(
% 0.20/0.54    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK0,sK2,sK2),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK0,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 0.20/0.54    inference(forward_demodulation,[],[f147,f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X3,X2,X1)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f32,f45,f45])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).
% 0.20/0.54  fof(f147,plain,(
% 0.20/0.54    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 0.20/0.54    inference(forward_demodulation,[],[f146,f53])).
% 0.20/0.54  fof(f146,plain,(
% 0.20/0.54    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1)))) | spl3_1),
% 0.20/0.54    inference(forward_demodulation,[],[f62,f52])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) | spl3_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f60])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    ~spl3_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f50,f60])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0))))),
% 0.20/0.54    inference(definition_unfolding,[],[f24,f46,f43,f48,f48])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.20/0.54    inference(negated_conjecture,[],[f19])).
% 0.20/0.54  fof(f19,conjecture,(
% 0.20/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (7270)------------------------------
% 0.20/0.54  % (7270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (7270)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (7270)Memory used [KB]: 7036
% 0.20/0.54  % (7270)Time elapsed: 0.098 s
% 0.20/0.54  % (7270)------------------------------
% 0.20/0.54  % (7270)------------------------------
% 0.20/0.56  % (7263)Success in time 0.204 s
%------------------------------------------------------------------------------
