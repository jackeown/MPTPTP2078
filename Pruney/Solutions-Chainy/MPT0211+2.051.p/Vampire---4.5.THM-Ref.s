%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:49 EST 2020

% Result     : Theorem 2.25s
% Output     : Refutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 493 expanded)
%              Number of leaves         :   18 ( 180 expanded)
%              Depth                    :   14
%              Number of atoms          :   88 ( 522 expanded)
%              Number of equality atoms :   60 ( 487 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1616,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f216,f1591,f1598,f1615])).

fof(f1615,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f1604])).

fof(f1604,plain,
    ( $false
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f49,f1597])).

fof(f1597,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f1595])).

fof(f1595,plain,
    ( spl3_5
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X2,X1,X3) ),
    inference(definition_unfolding,[],[f32,f43,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f37,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

fof(f1598,plain,
    ( ~ spl3_5
    | spl3_4 ),
    inference(avatar_split_clause,[],[f1592,f1588,f1595])).

fof(f1588,plain,
    ( spl3_4
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1592,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2)
    | spl3_4 ),
    inference(superposition,[],[f1590,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X5),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X5),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) ),
    inference(definition_unfolding,[],[f40,f39,f41,f43,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f30,f43])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

fof(f1590,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f1588])).

fof(f1591,plain,
    ( ~ spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f1586,f213,f1588])).

fof(f213,plain,
    ( spl3_2
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1586,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_2 ),
    inference(forward_demodulation,[],[f1585,f327])).

fof(f327,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X1,X2,X3,X4,X4) ),
    inference(superposition,[],[f54,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X4),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X4),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) ),
    inference(definition_unfolding,[],[f38,f42,f41,f43,f46])).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f45])).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f1585,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_2 ),
    inference(forward_demodulation,[],[f1584,f327])).

fof(f1584,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_2 ),
    inference(forward_demodulation,[],[f1496,f327])).

fof(f1496,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1))))
    | spl3_2 ),
    inference(backward_demodulation,[],[f215,f327])).

fof(f215,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f213])).

fof(f216,plain,
    ( ~ spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f211,f56,f213])).

fof(f56,plain,
    ( spl3_1
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f211,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f210,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X1,X1,X1,X1,X3,X2,X0) ),
    inference(definition_unfolding,[],[f33,f43,f43])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

fof(f210,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK0,sK2,sK2),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK0,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f209,f50])).

fof(f209,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f208,f50])).

fof(f208,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f58,f50])).

fof(f58,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f59,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f47,f56])).

fof(f47,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) ),
    inference(definition_unfolding,[],[f23,f44,f41,f45,f45])).

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
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:53:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (10216)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (10209)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (10221)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (10210)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (10213)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.53  % (10219)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.53  % (10219)Refutation not found, incomplete strategy% (10219)------------------------------
% 0.21/0.53  % (10219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10219)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (10219)Memory used [KB]: 10618
% 0.21/0.53  % (10219)Time elapsed: 0.087 s
% 0.21/0.53  % (10219)------------------------------
% 0.21/0.53  % (10219)------------------------------
% 0.21/0.53  % (10217)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.53  % (10225)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.53  % (10208)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.54  % (10218)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.54  % (10211)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.54  % (10212)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.55  % (10214)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (10220)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.56  % (10223)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.57  % (10222)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.57  % (10215)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.67/0.59  % (10224)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 2.25/0.72  % (10214)Refutation found. Thanks to Tanya!
% 2.25/0.72  % SZS status Theorem for theBenchmark
% 2.25/0.72  % SZS output start Proof for theBenchmark
% 2.25/0.72  fof(f1616,plain,(
% 2.25/0.72    $false),
% 2.25/0.72    inference(avatar_sat_refutation,[],[f59,f216,f1591,f1598,f1615])).
% 2.25/0.72  fof(f1615,plain,(
% 2.25/0.72    spl3_5),
% 2.25/0.72    inference(avatar_contradiction_clause,[],[f1604])).
% 2.25/0.72  fof(f1604,plain,(
% 2.25/0.72    $false | spl3_5),
% 2.25/0.72    inference(unit_resulting_resolution,[],[f49,f1597])).
% 2.25/0.72  fof(f1597,plain,(
% 2.25/0.72    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2) | spl3_5),
% 2.25/0.72    inference(avatar_component_clause,[],[f1595])).
% 2.25/0.72  fof(f1595,plain,(
% 2.25/0.72    spl3_5 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2)),
% 2.25/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.25/0.72  fof(f49,plain,(
% 2.25/0.72    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X2,X1,X3)) )),
% 2.25/0.72    inference(definition_unfolding,[],[f32,f43,f43])).
% 2.25/0.72  fof(f43,plain,(
% 2.25/0.72    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 2.25/0.72    inference(definition_unfolding,[],[f36,f42])).
% 2.25/0.72  fof(f42,plain,(
% 2.25/0.72    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 2.25/0.72    inference(definition_unfolding,[],[f37,f39])).
% 2.25/0.72  fof(f39,plain,(
% 2.25/0.72    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.25/0.72    inference(cnf_transformation,[],[f17])).
% 2.25/0.72  fof(f17,axiom,(
% 2.25/0.72    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.25/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.25/0.72  fof(f37,plain,(
% 2.25/0.72    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.25/0.72    inference(cnf_transformation,[],[f16])).
% 2.25/0.72  fof(f16,axiom,(
% 2.25/0.72    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.25/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.25/0.72  fof(f36,plain,(
% 2.25/0.72    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.25/0.72    inference(cnf_transformation,[],[f15])).
% 2.25/0.72  fof(f15,axiom,(
% 2.25/0.72    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.25/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.25/0.72  fof(f32,plain,(
% 2.25/0.72    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)) )),
% 2.25/0.72    inference(cnf_transformation,[],[f6])).
% 2.25/0.72  fof(f6,axiom,(
% 2.25/0.72    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 2.25/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).
% 2.25/0.72  fof(f1598,plain,(
% 2.25/0.72    ~spl3_5 | spl3_4),
% 2.25/0.72    inference(avatar_split_clause,[],[f1592,f1588,f1595])).
% 2.25/0.72  fof(f1588,plain,(
% 2.25/0.72    spl3_4 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 2.25/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.25/0.72  fof(f1592,plain,(
% 2.25/0.72    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK0,sK2) | spl3_4),
% 2.25/0.72    inference(superposition,[],[f1590,f54])).
% 2.25/0.72  fof(f54,plain,(
% 2.25/0.72    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X5),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X5),k5_enumset1(X0,X0,X0,X0,X1,X2,X3))))) )),
% 2.25/0.72    inference(definition_unfolding,[],[f40,f39,f41,f43,f45])).
% 2.25/0.72  fof(f45,plain,(
% 2.25/0.72    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 2.25/0.72    inference(definition_unfolding,[],[f26,f44])).
% 2.25/0.72  fof(f44,plain,(
% 2.25/0.72    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 2.25/0.72    inference(definition_unfolding,[],[f30,f43])).
% 2.25/0.72  fof(f30,plain,(
% 2.25/0.72    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.25/0.72    inference(cnf_transformation,[],[f14])).
% 2.25/0.72  fof(f14,axiom,(
% 2.25/0.72    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.25/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.25/0.72  fof(f26,plain,(
% 2.25/0.72    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.25/0.72    inference(cnf_transformation,[],[f13])).
% 2.25/0.72  fof(f13,axiom,(
% 2.25/0.72    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.25/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.25/0.72  fof(f41,plain,(
% 2.25/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.25/0.72    inference(definition_unfolding,[],[f28,f27])).
% 2.25/0.72  fof(f27,plain,(
% 2.25/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.25/0.72    inference(cnf_transformation,[],[f2])).
% 2.25/0.72  fof(f2,axiom,(
% 2.25/0.72    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.25/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.25/0.72  fof(f28,plain,(
% 2.25/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.25/0.72    inference(cnf_transformation,[],[f5])).
% 2.25/0.72  fof(f5,axiom,(
% 2.25/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.25/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.25/0.72  fof(f40,plain,(
% 2.25/0.72    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 2.25/0.72    inference(cnf_transformation,[],[f11])).
% 2.25/0.72  fof(f11,axiom,(
% 2.25/0.72    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 2.25/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).
% 2.25/0.72  fof(f1590,plain,(
% 2.25/0.72    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_4),
% 2.25/0.72    inference(avatar_component_clause,[],[f1588])).
% 2.25/0.72  fof(f1591,plain,(
% 2.25/0.72    ~spl3_4 | spl3_2),
% 2.25/0.72    inference(avatar_split_clause,[],[f1586,f213,f1588])).
% 2.25/0.72  fof(f213,plain,(
% 2.25/0.72    spl3_2 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1))))),
% 2.25/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.25/0.72  fof(f1586,plain,(
% 2.25/0.72    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_2),
% 2.25/0.72    inference(forward_demodulation,[],[f1585,f327])).
% 2.25/0.72  fof(f327,plain,(
% 2.25/0.72    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X1,X2,X3,X4,X4)) )),
% 2.25/0.72    inference(superposition,[],[f54,f53])).
% 2.25/0.72  fof(f53,plain,(
% 2.25/0.72    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X4),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X4),k5_enumset1(X0,X0,X0,X0,X1,X2,X3))))) )),
% 2.25/0.72    inference(definition_unfolding,[],[f38,f42,f41,f43,f46])).
% 2.25/0.72  fof(f46,plain,(
% 2.25/0.72    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 2.25/0.72    inference(definition_unfolding,[],[f24,f45])).
% 2.25/0.72  fof(f24,plain,(
% 2.25/0.72    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.25/0.72    inference(cnf_transformation,[],[f12])).
% 2.25/0.72  fof(f12,axiom,(
% 2.25/0.72    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.25/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.25/0.72  fof(f38,plain,(
% 2.25/0.72    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 2.25/0.72    inference(cnf_transformation,[],[f10])).
% 2.25/0.72  fof(f10,axiom,(
% 2.25/0.72    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 2.25/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 2.25/0.72  fof(f1585,plain,(
% 2.25/0.72    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_2),
% 2.25/0.72    inference(forward_demodulation,[],[f1584,f327])).
% 2.25/0.72  fof(f1584,plain,(
% 2.25/0.72    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_2),
% 2.25/0.72    inference(forward_demodulation,[],[f1496,f327])).
% 2.25/0.72  fof(f1496,plain,(
% 2.25/0.72    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1)))) | spl3_2),
% 2.25/0.72    inference(backward_demodulation,[],[f215,f327])).
% 2.25/0.72  fof(f215,plain,(
% 2.25/0.72    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_2),
% 2.25/0.72    inference(avatar_component_clause,[],[f213])).
% 2.25/0.72  fof(f216,plain,(
% 2.25/0.72    ~spl3_2 | spl3_1),
% 2.25/0.72    inference(avatar_split_clause,[],[f211,f56,f213])).
% 2.25/0.72  fof(f56,plain,(
% 2.25/0.72    spl3_1 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0))))),
% 2.25/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.25/0.72  fof(f211,plain,(
% 2.25/0.72    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 2.25/0.72    inference(forward_demodulation,[],[f210,f50])).
% 2.25/0.72  fof(f50,plain,(
% 2.25/0.72    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X1,X1,X1,X1,X3,X2,X0)) )),
% 2.25/0.72    inference(definition_unfolding,[],[f33,f43,f43])).
% 2.25/0.72  fof(f33,plain,(
% 2.25/0.72    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 2.25/0.72    inference(cnf_transformation,[],[f8])).
% 2.25/0.72  fof(f8,axiom,(
% 2.25/0.72    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 2.25/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).
% 2.25/0.72  fof(f210,plain,(
% 2.25/0.72    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK0,sK2,sK2),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK0,sK2,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 2.25/0.72    inference(forward_demodulation,[],[f209,f50])).
% 2.25/0.72  fof(f209,plain,(
% 2.25/0.72    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 2.25/0.72    inference(forward_demodulation,[],[f208,f50])).
% 2.25/0.72  fof(f208,plain,(
% 2.25/0.72    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK0,sK1,sK1)))) | spl3_1),
% 2.25/0.72    inference(forward_demodulation,[],[f58,f50])).
% 2.25/0.72  fof(f58,plain,(
% 2.25/0.72    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) | spl3_1),
% 2.25/0.72    inference(avatar_component_clause,[],[f56])).
% 2.25/0.72  fof(f59,plain,(
% 2.25/0.72    ~spl3_1),
% 2.25/0.72    inference(avatar_split_clause,[],[f47,f56])).
% 2.25/0.72  fof(f47,plain,(
% 2.25/0.72    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0))))),
% 2.25/0.72    inference(definition_unfolding,[],[f23,f44,f41,f45,f45])).
% 2.25/0.72  fof(f23,plain,(
% 2.25/0.72    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 2.25/0.72    inference(cnf_transformation,[],[f22])).
% 2.25/0.72  fof(f22,plain,(
% 2.25/0.72    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 2.25/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).
% 2.25/0.72  fof(f21,plain,(
% 2.25/0.72    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 2.25/0.72    introduced(choice_axiom,[])).
% 2.25/0.72  fof(f20,plain,(
% 2.25/0.72    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 2.25/0.72    inference(ennf_transformation,[],[f19])).
% 2.25/0.72  fof(f19,negated_conjecture,(
% 2.25/0.72    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 2.25/0.72    inference(negated_conjecture,[],[f18])).
% 2.25/0.72  fof(f18,conjecture,(
% 2.25/0.72    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 2.25/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 2.25/0.72  % SZS output end Proof for theBenchmark
% 2.25/0.72  % (10214)------------------------------
% 2.25/0.72  % (10214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.25/0.72  % (10214)Termination reason: Refutation
% 2.25/0.72  
% 2.25/0.72  % (10214)Memory used [KB]: 8059
% 2.25/0.72  % (10214)Time elapsed: 0.266 s
% 2.25/0.72  % (10214)------------------------------
% 2.25/0.72  % (10214)------------------------------
% 2.25/0.73  % (10207)Success in time 0.362 s
%------------------------------------------------------------------------------
