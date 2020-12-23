%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:50 EST 2020

% Result     : Theorem 2.07s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 537 expanded)
%              Number of leaves         :   19 ( 195 expanded)
%              Depth                    :   14
%              Number of atoms          :   92 ( 566 expanded)
%              Number of equality atoms :   64 ( 531 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1455,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f198,f1430,f1438,f1454])).

fof(f1454,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f1449])).

fof(f1449,plain,
    ( $false
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f175,f1437])).

fof(f1437,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f1435])).

fof(f1435,plain,
    ( spl3_5
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f175,plain,(
    ! [X14,X12,X15,X13] : k5_enumset1(X13,X13,X13,X13,X15,X14,X12) = k5_enumset1(X15,X15,X15,X15,X14,X13,X12) ),
    inference(superposition,[],[f56,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X1,X1,X1,X1,X3,X2,X0) ),
    inference(definition_unfolding,[],[f35,f47,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f37,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f36,f47,f47])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(f1438,plain,
    ( ~ spl3_5
    | spl3_4 ),
    inference(avatar_split_clause,[],[f1431,f1427,f1435])).

fof(f1427,plain,
    ( spl3_4
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1431,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2)
    | spl3_4 ),
    inference(superposition,[],[f1429,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X5),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X5),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) ),
    inference(definition_unfolding,[],[f42,f40,f45,f47,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f32,f47])).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

fof(f1429,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f1427])).

fof(f1430,plain,
    ( ~ spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f1425,f195,f1427])).

fof(f195,plain,
    ( spl3_2
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1425,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_2 ),
    inference(forward_demodulation,[],[f1424,f331])).

fof(f331,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X1,X2,X3,X3) ),
    inference(superposition,[],[f59,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X3),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X3),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) ),
    inference(definition_unfolding,[],[f38,f47,f45,f48,f51])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f50])).

fof(f26,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f1424,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_2 ),
    inference(forward_demodulation,[],[f1423,f331])).

fof(f1423,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_2 ),
    inference(forward_demodulation,[],[f1339,f331])).

fof(f1339,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1))))
    | spl3_2 ),
    inference(backward_demodulation,[],[f197,f331])).

fof(f197,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f195])).

fof(f198,plain,
    ( ~ spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f193,f62,f195])).

fof(f62,plain,
    ( spl3_1
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f193,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f192,f55])).

fof(f192,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK0,sK2,sK2),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK0,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f191,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X3,X2,X1) ),
    inference(definition_unfolding,[],[f34,f47,f47])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(f191,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f190,f55])).

fof(f190,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f64,f54])).

fof(f64,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f65,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f52,f62])).

fof(f52,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) ),
    inference(definition_unfolding,[],[f25,f48,f45,f50,f50])).

fof(f25,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:24:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (13750)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (13743)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (13744)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (13746)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (13751)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (13751)Refutation not found, incomplete strategy% (13751)------------------------------
% 0.21/0.48  % (13751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (13751)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (13751)Memory used [KB]: 10618
% 0.21/0.48  % (13751)Time elapsed: 0.061 s
% 0.21/0.48  % (13751)------------------------------
% 0.21/0.48  % (13751)------------------------------
% 0.21/0.49  % (13753)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (13752)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (13754)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (13749)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (13757)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (13745)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (13741)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.51  % (13742)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (13747)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (13740)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.52  % (13748)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (13756)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.25/0.53  % (13755)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 2.07/0.65  % (13746)Refutation found. Thanks to Tanya!
% 2.07/0.65  % SZS status Theorem for theBenchmark
% 2.07/0.65  % SZS output start Proof for theBenchmark
% 2.07/0.65  fof(f1455,plain,(
% 2.07/0.65    $false),
% 2.07/0.65    inference(avatar_sat_refutation,[],[f65,f198,f1430,f1438,f1454])).
% 2.07/0.65  fof(f1454,plain,(
% 2.07/0.65    spl3_5),
% 2.07/0.65    inference(avatar_contradiction_clause,[],[f1449])).
% 2.07/0.65  fof(f1449,plain,(
% 2.07/0.65    $false | spl3_5),
% 2.07/0.65    inference(unit_resulting_resolution,[],[f175,f1437])).
% 2.07/0.65  fof(f1437,plain,(
% 2.07/0.65    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2) | spl3_5),
% 2.07/0.65    inference(avatar_component_clause,[],[f1435])).
% 2.07/0.65  fof(f1435,plain,(
% 2.07/0.65    spl3_5 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2)),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.07/0.65  fof(f175,plain,(
% 2.07/0.65    ( ! [X14,X12,X15,X13] : (k5_enumset1(X13,X13,X13,X13,X15,X14,X12) = k5_enumset1(X15,X15,X15,X15,X14,X13,X12)) )),
% 2.07/0.65    inference(superposition,[],[f56,f55])).
% 2.07/0.65  fof(f55,plain,(
% 2.07/0.65    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X1,X1,X1,X1,X3,X2,X0)) )),
% 2.07/0.65    inference(definition_unfolding,[],[f35,f47,f47])).
% 2.07/0.65  fof(f47,plain,(
% 2.07/0.65    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 2.07/0.65    inference(definition_unfolding,[],[f37,f46])).
% 2.07/0.65  fof(f46,plain,(
% 2.07/0.65    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 2.07/0.65    inference(definition_unfolding,[],[f39,f40])).
% 2.07/0.65  fof(f40,plain,(
% 2.07/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.07/0.65    inference(cnf_transformation,[],[f19])).
% 2.07/0.65  fof(f19,axiom,(
% 2.07/0.65    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.07/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.07/0.65  fof(f39,plain,(
% 2.07/0.65    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.07/0.65    inference(cnf_transformation,[],[f18])).
% 2.07/0.65  fof(f18,axiom,(
% 2.07/0.65    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.07/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.07/0.65  fof(f37,plain,(
% 2.07/0.65    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.07/0.65    inference(cnf_transformation,[],[f17])).
% 2.07/0.65  fof(f17,axiom,(
% 2.07/0.65    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.07/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.07/0.65  fof(f35,plain,(
% 2.07/0.65    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 2.07/0.65    inference(cnf_transformation,[],[f7])).
% 2.07/0.65  fof(f7,axiom,(
% 2.07/0.65    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 2.07/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).
% 2.07/0.65  fof(f56,plain,(
% 2.07/0.65    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0)) )),
% 2.07/0.65    inference(definition_unfolding,[],[f36,f47,f47])).
% 2.07/0.65  fof(f36,plain,(
% 2.07/0.65    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 2.07/0.65    inference(cnf_transformation,[],[f8])).
% 2.07/0.65  fof(f8,axiom,(
% 2.07/0.65    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 2.07/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).
% 2.07/0.65  fof(f1438,plain,(
% 2.07/0.65    ~spl3_5 | spl3_4),
% 2.07/0.65    inference(avatar_split_clause,[],[f1431,f1427,f1435])).
% 2.07/0.65  fof(f1427,plain,(
% 2.07/0.65    spl3_4 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.07/0.65  fof(f1431,plain,(
% 2.07/0.65    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2) | spl3_4),
% 2.07/0.65    inference(superposition,[],[f1429,f59])).
% 2.07/0.65  fof(f59,plain,(
% 2.07/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X5),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X5),k5_enumset1(X0,X0,X0,X0,X1,X2,X3))))) )),
% 2.07/0.65    inference(definition_unfolding,[],[f42,f40,f45,f47,f50])).
% 2.07/0.65  fof(f50,plain,(
% 2.07/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 2.07/0.65    inference(definition_unfolding,[],[f28,f48])).
% 2.07/0.65  fof(f48,plain,(
% 2.07/0.65    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 2.07/0.65    inference(definition_unfolding,[],[f32,f47])).
% 2.07/0.65  fof(f32,plain,(
% 2.07/0.65    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.07/0.65    inference(cnf_transformation,[],[f16])).
% 2.07/0.65  fof(f16,axiom,(
% 2.07/0.65    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.07/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.07/0.65  fof(f28,plain,(
% 2.07/0.65    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.07/0.65    inference(cnf_transformation,[],[f15])).
% 2.07/0.65  fof(f15,axiom,(
% 2.07/0.65    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.07/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.07/0.65  fof(f45,plain,(
% 2.07/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.07/0.65    inference(definition_unfolding,[],[f30,f29])).
% 2.07/0.65  fof(f29,plain,(
% 2.07/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.07/0.65    inference(cnf_transformation,[],[f2])).
% 2.07/0.65  fof(f2,axiom,(
% 2.07/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.07/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.07/0.65  fof(f30,plain,(
% 2.07/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.07/0.65    inference(cnf_transformation,[],[f5])).
% 2.07/0.65  fof(f5,axiom,(
% 2.07/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.07/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.07/0.65  fof(f42,plain,(
% 2.07/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 2.07/0.65    inference(cnf_transformation,[],[f13])).
% 2.07/0.65  fof(f13,axiom,(
% 2.07/0.65    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 2.07/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).
% 2.07/0.65  fof(f1429,plain,(
% 2.07/0.65    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_4),
% 2.07/0.65    inference(avatar_component_clause,[],[f1427])).
% 2.07/0.65  fof(f1430,plain,(
% 2.07/0.65    ~spl3_4 | spl3_2),
% 2.07/0.65    inference(avatar_split_clause,[],[f1425,f195,f1427])).
% 2.07/0.65  fof(f195,plain,(
% 2.07/0.65    spl3_2 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1))))),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.07/0.65  fof(f1425,plain,(
% 2.07/0.65    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_2),
% 2.07/0.65    inference(forward_demodulation,[],[f1424,f331])).
% 2.07/0.65  fof(f331,plain,(
% 2.07/0.65    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X1,X2,X3,X3)) )),
% 2.07/0.65    inference(superposition,[],[f59,f57])).
% 2.07/0.65  fof(f57,plain,(
% 2.07/0.65    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X3),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X3),k5_enumset1(X0,X0,X0,X0,X0,X1,X2))))) )),
% 2.07/0.65    inference(definition_unfolding,[],[f38,f47,f45,f48,f51])).
% 2.07/0.65  fof(f51,plain,(
% 2.07/0.65    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 2.07/0.65    inference(definition_unfolding,[],[f26,f50])).
% 2.07/0.65  fof(f26,plain,(
% 2.07/0.65    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.07/0.65    inference(cnf_transformation,[],[f14])).
% 2.07/0.65  fof(f14,axiom,(
% 2.07/0.65    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.07/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.07/0.65  fof(f38,plain,(
% 2.07/0.65    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 2.07/0.65    inference(cnf_transformation,[],[f11])).
% 2.07/0.65  fof(f11,axiom,(
% 2.07/0.65    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 2.07/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 2.07/0.65  fof(f1424,plain,(
% 2.07/0.65    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_2),
% 2.07/0.65    inference(forward_demodulation,[],[f1423,f331])).
% 2.07/0.65  fof(f1423,plain,(
% 2.07/0.65    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_2),
% 2.07/0.65    inference(forward_demodulation,[],[f1339,f331])).
% 2.07/0.65  fof(f1339,plain,(
% 2.07/0.65    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1)))) | spl3_2),
% 2.07/0.65    inference(backward_demodulation,[],[f197,f331])).
% 2.07/0.65  fof(f197,plain,(
% 2.07/0.65    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_2),
% 2.07/0.65    inference(avatar_component_clause,[],[f195])).
% 2.07/0.65  fof(f198,plain,(
% 2.07/0.65    ~spl3_2 | spl3_1),
% 2.07/0.65    inference(avatar_split_clause,[],[f193,f62,f195])).
% 2.07/0.65  fof(f62,plain,(
% 2.07/0.65    spl3_1 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0))))),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.07/0.65  fof(f193,plain,(
% 2.07/0.65    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 2.07/0.65    inference(forward_demodulation,[],[f192,f55])).
% 2.07/0.65  fof(f192,plain,(
% 2.07/0.65    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK0,sK2,sK2),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK0,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 2.07/0.65    inference(forward_demodulation,[],[f191,f54])).
% 2.07/0.65  fof(f54,plain,(
% 2.07/0.65    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X3,X2,X1)) )),
% 2.07/0.65    inference(definition_unfolding,[],[f34,f47,f47])).
% 2.07/0.65  fof(f34,plain,(
% 2.07/0.65    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 2.07/0.65    inference(cnf_transformation,[],[f6])).
% 2.07/0.65  fof(f6,axiom,(
% 2.07/0.65    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 2.07/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).
% 2.07/0.65  fof(f191,plain,(
% 2.07/0.65    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 2.07/0.65    inference(forward_demodulation,[],[f190,f55])).
% 2.07/0.65  fof(f190,plain,(
% 2.07/0.65    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1)))) | spl3_1),
% 2.07/0.65    inference(forward_demodulation,[],[f64,f54])).
% 2.07/0.65  fof(f64,plain,(
% 2.07/0.65    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) | spl3_1),
% 2.07/0.65    inference(avatar_component_clause,[],[f62])).
% 2.07/0.65  fof(f65,plain,(
% 2.07/0.65    ~spl3_1),
% 2.07/0.65    inference(avatar_split_clause,[],[f52,f62])).
% 2.07/0.65  fof(f52,plain,(
% 2.07/0.65    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0))))),
% 2.07/0.65    inference(definition_unfolding,[],[f25,f48,f45,f50,f50])).
% 2.07/0.65  fof(f25,plain,(
% 2.07/0.65    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 2.07/0.65    inference(cnf_transformation,[],[f24])).
% 2.07/0.65  fof(f24,plain,(
% 2.07/0.65    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 2.07/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).
% 2.07/0.65  fof(f23,plain,(
% 2.07/0.65    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 2.07/0.65    introduced(choice_axiom,[])).
% 2.07/0.65  fof(f22,plain,(
% 2.07/0.65    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 2.07/0.65    inference(ennf_transformation,[],[f21])).
% 2.07/0.65  fof(f21,negated_conjecture,(
% 2.07/0.65    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 2.07/0.65    inference(negated_conjecture,[],[f20])).
% 2.07/0.65  fof(f20,conjecture,(
% 2.07/0.65    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 2.07/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
% 2.07/0.65  % SZS output end Proof for theBenchmark
% 2.07/0.65  % (13746)------------------------------
% 2.07/0.65  % (13746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.65  % (13746)Termination reason: Refutation
% 2.07/0.65  
% 2.07/0.65  % (13746)Memory used [KB]: 8315
% 2.07/0.65  % (13746)Time elapsed: 0.216 s
% 2.07/0.65  % (13746)------------------------------
% 2.07/0.65  % (13746)------------------------------
% 2.07/0.65  % (13739)Success in time 0.272 s
%------------------------------------------------------------------------------
