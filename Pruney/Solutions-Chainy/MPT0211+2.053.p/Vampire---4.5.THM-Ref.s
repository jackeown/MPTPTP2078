%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 392 expanded)
%              Number of leaves         :   18 ( 145 expanded)
%              Depth                    :   13
%              Number of atoms          :   89 ( 421 expanded)
%              Number of equality atoms :   61 ( 386 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1310,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f216,f1285,f1292,f1309])).

fof(f1309,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f1298])).

fof(f1298,plain,
    ( $false
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f188,f1291])).

fof(f1291,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK1,sK0,sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f1289])).

fof(f1289,plain,
    ( spl3_5
  <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k4_enumset1(sK0,sK0,sK0,sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f188,plain,(
    ! [X19,X17,X18,X16] : k4_enumset1(X17,X17,X17,X19,X18,X16) = k4_enumset1(X19,X19,X19,X18,X17,X16) ),
    inference(superposition,[],[f53,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X1,X1,X1,X3,X2,X0) ),
    inference(definition_unfolding,[],[f34,f42,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f35,f42,f42])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(f1292,plain,
    ( ~ spl3_5
    | spl3_4 ),
    inference(avatar_split_clause,[],[f1286,f1282,f1289])).

fof(f1282,plain,
    ( spl3_4
  <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1286,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK1,sK0,sK2)
    | spl3_4 ),
    inference(superposition,[],[f1284,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k4_enumset1(X0,X0,X0,X1,X2,X3)))) ),
    inference(definition_unfolding,[],[f39,f41,f42,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f30,f42])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

fof(f1284,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f1282])).

fof(f1285,plain,
    ( ~ spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f1280,f213,f1282])).

fof(f213,plain,
    ( spl3_2
  <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1280,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_2 ),
    inference(forward_demodulation,[],[f1279,f329])).

fof(f329,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4) ),
    inference(superposition,[],[f54,f47])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X4),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X4),k4_enumset1(X0,X0,X0,X1,X2,X3)))) ),
    inference(definition_unfolding,[],[f38,f37,f41,f42,f46])).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f45])).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f1279,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_2 ),
    inference(forward_demodulation,[],[f1278,f329])).

fof(f1278,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_2 ),
    inference(forward_demodulation,[],[f1198,f329])).

fof(f1198,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK1))))
    | spl3_2 ),
    inference(backward_demodulation,[],[f215,f329])).

fof(f215,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f213])).

fof(f216,plain,
    ( ~ spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f211,f56,f213])).

fof(f56,plain,
    ( spl3_1
  <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f211,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f210,f52])).

fof(f210,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK0,sK2,sK2),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK0,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f209,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X3,X2,X1) ),
    inference(definition_unfolding,[],[f32,f42,f42])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

fof(f209,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f208,f52])).

fof(f208,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK0,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK0,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f58,f50])).

fof(f58,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f59,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f48,f56])).

fof(f48,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0)))) ),
    inference(definition_unfolding,[],[f23,f43,f41,f45,f45])).

fof(f23,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:42:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (14749)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (14748)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (14747)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (14753)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (14754)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (14754)Refutation not found, incomplete strategy% (14754)------------------------------
% 0.21/0.48  % (14754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (14754)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (14754)Memory used [KB]: 10618
% 0.21/0.48  % (14754)Time elapsed: 0.052 s
% 0.21/0.48  % (14754)------------------------------
% 0.21/0.48  % (14754)------------------------------
% 0.21/0.48  % (14744)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (14746)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (14757)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (14743)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (14756)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (14745)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (14759)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (14752)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (14755)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (14758)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (14750)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.52  % (14751)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.53  % (14760)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.54  % (14749)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f1310,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f59,f216,f1285,f1292,f1309])).
% 0.21/0.54  fof(f1309,plain,(
% 0.21/0.54    spl3_5),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f1298])).
% 0.21/0.54  fof(f1298,plain,(
% 0.21/0.54    $false | spl3_5),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f188,f1291])).
% 0.21/0.54  fof(f1291,plain,(
% 0.21/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK1,sK0,sK2) | spl3_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f1289])).
% 0.21/0.54  fof(f1289,plain,(
% 0.21/0.54    spl3_5 <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k4_enumset1(sK0,sK0,sK0,sK1,sK0,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.54  fof(f188,plain,(
% 0.21/0.54    ( ! [X19,X17,X18,X16] : (k4_enumset1(X17,X17,X17,X19,X18,X16) = k4_enumset1(X19,X19,X19,X18,X17,X16)) )),
% 0.21/0.54    inference(superposition,[],[f53,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X1,X1,X1,X3,X2,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f34,f42,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f36,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X2,X1,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f35,f42,f42])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
% 0.21/0.54  fof(f1292,plain,(
% 0.21/0.54    ~spl3_5 | spl3_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f1286,f1282,f1289])).
% 0.21/0.54  fof(f1282,plain,(
% 0.21/0.54    spl3_4 <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.54  fof(f1286,plain,(
% 0.21/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK1,sK0,sK2) | spl3_4),
% 0.21/0.54    inference(superposition,[],[f1284,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k4_enumset1(X0,X0,X0,X1,X2,X3))))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f39,f41,f42,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f26,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f30,f42])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f28,f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).
% 0.21/0.54  fof(f1284,plain,(
% 0.21/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f1282])).
% 0.21/0.54  fof(f1285,plain,(
% 0.21/0.54    ~spl3_4 | spl3_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f1280,f213,f1282])).
% 0.21/0.54  fof(f213,plain,(
% 0.21/0.54    spl3_2 <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.54  fof(f1280,plain,(
% 0.21/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_2),
% 0.21/0.54    inference(forward_demodulation,[],[f1279,f329])).
% 0.21/0.54  fof(f329,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)) )),
% 0.21/0.54    inference(superposition,[],[f54,f47])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X4),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X4),k4_enumset1(X0,X0,X0,X1,X2,X3))))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f38,f37,f41,f42,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f24,f45])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 1.45/0.54  fof(f11,axiom,(
% 1.45/0.54    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 1.45/0.54  fof(f1279,plain,(
% 1.45/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_2),
% 1.45/0.54    inference(forward_demodulation,[],[f1278,f329])).
% 1.45/0.54  fof(f1278,plain,(
% 1.45/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_2),
% 1.45/0.54    inference(forward_demodulation,[],[f1198,f329])).
% 1.45/0.54  fof(f1198,plain,(
% 1.45/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK1)))) | spl3_2),
% 1.45/0.54    inference(backward_demodulation,[],[f215,f329])).
% 1.45/0.54  fof(f215,plain,(
% 1.45/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_2),
% 1.45/0.54    inference(avatar_component_clause,[],[f213])).
% 1.45/0.54  fof(f216,plain,(
% 1.45/0.54    ~spl3_2 | spl3_1),
% 1.45/0.54    inference(avatar_split_clause,[],[f211,f56,f213])).
% 1.45/0.54  fof(f56,plain,(
% 1.45/0.54    spl3_1 <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0))))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.45/0.54  fof(f211,plain,(
% 1.45/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 1.45/0.54    inference(forward_demodulation,[],[f210,f52])).
% 1.45/0.54  fof(f210,plain,(
% 1.45/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK0,sK2,sK2),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK0,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 1.45/0.54    inference(forward_demodulation,[],[f209,f50])).
% 1.45/0.54  fof(f50,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X3,X2,X1)) )),
% 1.45/0.54    inference(definition_unfolding,[],[f32,f42,f42])).
% 1.45/0.54  fof(f32,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f6])).
% 1.45/0.54  fof(f6,axiom,(
% 1.45/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).
% 1.45/0.54  fof(f209,plain,(
% 1.45/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 1.45/0.54    inference(forward_demodulation,[],[f208,f52])).
% 1.45/0.54  fof(f208,plain,(
% 1.45/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK0,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK0,sK1,sK1)))) | spl3_1),
% 1.45/0.54    inference(forward_demodulation,[],[f58,f50])).
% 1.45/0.54  fof(f58,plain,(
% 1.45/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0)))) | spl3_1),
% 1.45/0.54    inference(avatar_component_clause,[],[f56])).
% 1.45/0.54  fof(f59,plain,(
% 1.45/0.54    ~spl3_1),
% 1.45/0.54    inference(avatar_split_clause,[],[f48,f56])).
% 1.45/0.54  fof(f48,plain,(
% 1.45/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0))))),
% 1.45/0.54    inference(definition_unfolding,[],[f23,f43,f41,f45,f45])).
% 1.45/0.54  fof(f23,plain,(
% 1.45/0.54    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.45/0.54    inference(cnf_transformation,[],[f22])).
% 1.45/0.54  fof(f22,plain,(
% 1.45/0.54    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.45/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).
% 1.45/0.54  fof(f21,plain,(
% 1.45/0.54    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.45/0.54    introduced(choice_axiom,[])).
% 1.45/0.54  fof(f20,plain,(
% 1.45/0.54    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.45/0.54    inference(ennf_transformation,[],[f19])).
% 1.45/0.54  fof(f19,negated_conjecture,(
% 1.45/0.54    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.45/0.54    inference(negated_conjecture,[],[f18])).
% 1.45/0.54  fof(f18,conjecture,(
% 1.45/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 1.45/0.54  % SZS output end Proof for theBenchmark
% 1.45/0.54  % (14749)------------------------------
% 1.45/0.54  % (14749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.54  % (14749)Termination reason: Refutation
% 1.45/0.54  
% 1.45/0.54  % (14749)Memory used [KB]: 7419
% 1.45/0.54  % (14749)Time elapsed: 0.100 s
% 1.45/0.54  % (14749)------------------------------
% 1.45/0.54  % (14749)------------------------------
% 1.45/0.54  % (14742)Success in time 0.18 s
%------------------------------------------------------------------------------
