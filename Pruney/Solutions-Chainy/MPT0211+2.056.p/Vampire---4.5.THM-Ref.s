%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
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
fof(f1225,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f189,f1206,f1213,f1224])).

fof(f1224,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f1219])).

fof(f1219,plain,
    ( $false
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f166,f1212])).

fof(f1212,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK1,sK0,sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f1210])).

fof(f1210,plain,
    ( spl3_5
  <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k4_enumset1(sK0,sK0,sK0,sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f166,plain,(
    ! [X14,X12,X15,X13] : k4_enumset1(X13,X13,X13,X15,X14,X12) = k4_enumset1(X15,X15,X15,X14,X13,X12) ),
    inference(superposition,[],[f50,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X1,X1,X1,X3,X2,X0) ),
    inference(definition_unfolding,[],[f32,f40,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f33,f40,f40])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(f1213,plain,
    ( ~ spl3_5
    | spl3_4 ),
    inference(avatar_split_clause,[],[f1207,f1203,f1210])).

fof(f1203,plain,
    ( spl3_4
  <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1207,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK1,sK0,sK2)
    | spl3_4 ),
    inference(superposition,[],[f1205,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k4_enumset1(X0,X0,X0,X1,X2,X3)))) ),
    inference(definition_unfolding,[],[f37,f39,f40,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f25,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f29,f40])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

fof(f1205,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f1203])).

fof(f1206,plain,
    ( ~ spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f1201,f186,f1203])).

fof(f186,plain,
    ( spl3_2
  <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1201,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_2 ),
    inference(forward_demodulation,[],[f1200,f220])).

fof(f220,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4) ),
    inference(superposition,[],[f51,f45])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X4),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X4),k4_enumset1(X0,X0,X0,X1,X2,X3)))) ),
    inference(definition_unfolding,[],[f36,f35,f39,f40,f43])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f42])).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f1200,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_2 ),
    inference(forward_demodulation,[],[f1199,f220])).

fof(f1199,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_2 ),
    inference(forward_demodulation,[],[f1127,f220])).

fof(f1127,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK1))))
    | spl3_2 ),
    inference(backward_demodulation,[],[f188,f220])).

fof(f188,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f186])).

fof(f189,plain,
    ( ~ spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f184,f53,f186])).

fof(f53,plain,
    ( spl3_1
  <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f184,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f183,f49])).

fof(f183,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK0,sK2,sK2),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK0,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f182,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X3,X2,X1) ),
    inference(definition_unfolding,[],[f31,f40,f40])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

fof(f182,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f181,f49])).

fof(f181,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK0,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK0,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f55,f48])).

fof(f55,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f56,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f46,f53])).

fof(f46,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0)))) ),
    inference(definition_unfolding,[],[f22,f41,f39,f42,f42])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:07:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (7021)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.46  % (7009)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (7012)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (7017)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (7006)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (7005)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (7008)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (7007)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (7015)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (7011)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (7004)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (7018)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (7010)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (7015)Refutation not found, incomplete strategy% (7015)------------------------------
% 0.21/0.49  % (7015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7015)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7015)Memory used [KB]: 10618
% 0.21/0.49  % (7015)Time elapsed: 0.081 s
% 0.21/0.49  % (7015)------------------------------
% 0.21/0.49  % (7015)------------------------------
% 0.21/0.50  % (7014)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (7016)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (7013)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.52  % (7019)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.52  % (7020)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.58  % (7010)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f1225,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(avatar_sat_refutation,[],[f56,f189,f1206,f1213,f1224])).
% 0.21/0.58  fof(f1224,plain,(
% 0.21/0.58    spl3_5),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f1219])).
% 0.21/0.58  fof(f1219,plain,(
% 0.21/0.58    $false | spl3_5),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f166,f1212])).
% 0.21/0.58  fof(f1212,plain,(
% 0.21/0.58    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK1,sK0,sK2) | spl3_5),
% 0.21/0.58    inference(avatar_component_clause,[],[f1210])).
% 0.21/0.58  fof(f1210,plain,(
% 0.21/0.58    spl3_5 <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k4_enumset1(sK0,sK0,sK0,sK1,sK0,sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.58  fof(f166,plain,(
% 0.21/0.58    ( ! [X14,X12,X15,X13] : (k4_enumset1(X13,X13,X13,X15,X14,X12) = k4_enumset1(X15,X15,X15,X14,X13,X12)) )),
% 0.21/0.58    inference(superposition,[],[f50,f49])).
% 0.21/0.58  fof(f49,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X1,X1,X1,X3,X2,X0)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f32,f40,f40])).
% 0.21/0.58  fof(f40,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f34,f35])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f16])).
% 0.21/0.58  fof(f16,axiom,(
% 0.21/0.58    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,axiom,(
% 0.21/0.58    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X2,X1,X0)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f33,f40,f40])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
% 0.21/0.58  fof(f1213,plain,(
% 0.21/0.58    ~spl3_5 | spl3_4),
% 0.21/0.58    inference(avatar_split_clause,[],[f1207,f1203,f1210])).
% 0.21/0.58  fof(f1203,plain,(
% 0.21/0.58    spl3_4 <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.58  fof(f1207,plain,(
% 0.21/0.58    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK1,sK0,sK2) | spl3_4),
% 0.21/0.58    inference(superposition,[],[f1205,f45])).
% 0.21/0.58  fof(f45,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k4_enumset1(X0,X0,X0,X1,X2,X3))))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f37,f39,f40,f42])).
% 0.21/0.58  fof(f42,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f25,f41])).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f29,f40])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f14])).
% 0.21/0.58  fof(f14,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f27,f26])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f10])).
% 0.21/0.58  fof(f10,axiom,(
% 0.21/0.58    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).
% 0.21/0.58  fof(f1205,plain,(
% 0.21/0.58    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_4),
% 0.21/0.58    inference(avatar_component_clause,[],[f1203])).
% 0.21/0.58  fof(f1206,plain,(
% 0.21/0.58    ~spl3_4 | spl3_2),
% 0.21/0.58    inference(avatar_split_clause,[],[f1201,f186,f1203])).
% 0.21/0.58  fof(f186,plain,(
% 0.21/0.58    spl3_2 <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1))))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.58  fof(f1201,plain,(
% 0.21/0.58    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_2),
% 0.21/0.58    inference(forward_demodulation,[],[f1200,f220])).
% 0.21/0.58  fof(f220,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)) )),
% 0.21/0.58    inference(superposition,[],[f51,f45])).
% 0.21/0.58  fof(f51,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X4),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X4),k4_enumset1(X0,X0,X0,X1,X2,X3))))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f36,f35,f39,f40,f43])).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f23,f42])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,axiom,(
% 0.21/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 0.21/0.58  fof(f1200,plain,(
% 0.21/0.58    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_2),
% 0.21/0.58    inference(forward_demodulation,[],[f1199,f220])).
% 0.21/0.58  fof(f1199,plain,(
% 0.21/0.58    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_2),
% 0.21/0.58    inference(forward_demodulation,[],[f1127,f220])).
% 0.21/0.58  fof(f1127,plain,(
% 0.21/0.58    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK1)))) | spl3_2),
% 0.21/0.58    inference(backward_demodulation,[],[f188,f220])).
% 0.21/0.58  fof(f188,plain,(
% 0.21/0.58    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_2),
% 0.21/0.58    inference(avatar_component_clause,[],[f186])).
% 0.21/0.58  fof(f189,plain,(
% 0.21/0.58    ~spl3_2 | spl3_1),
% 0.21/0.58    inference(avatar_split_clause,[],[f184,f53,f186])).
% 0.21/0.58  fof(f53,plain,(
% 0.21/0.58    spl3_1 <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0))))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.58  fof(f184,plain,(
% 0.21/0.58    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 0.21/0.58    inference(forward_demodulation,[],[f183,f49])).
% 0.21/0.58  fof(f183,plain,(
% 0.21/0.58    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK0,sK2,sK2),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK0,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 0.21/0.58    inference(forward_demodulation,[],[f182,f48])).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X3,X2,X1)) )),
% 0.21/0.58    inference(definition_unfolding,[],[f31,f40,f40])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,axiom,(
% 0.21/0.58    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).
% 0.21/0.58  fof(f182,plain,(
% 0.21/0.58    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 0.21/0.58    inference(forward_demodulation,[],[f181,f49])).
% 0.21/0.58  fof(f181,plain,(
% 0.21/0.58    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK0,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK0,sK1,sK1)))) | spl3_1),
% 0.21/0.58    inference(forward_demodulation,[],[f55,f48])).
% 0.21/0.58  fof(f55,plain,(
% 0.21/0.58    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0)))) | spl3_1),
% 0.21/0.58    inference(avatar_component_clause,[],[f53])).
% 0.21/0.58  fof(f56,plain,(
% 0.21/0.58    ~spl3_1),
% 0.21/0.58    inference(avatar_split_clause,[],[f46,f53])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0))))),
% 0.21/0.58    inference(definition_unfolding,[],[f22,f41,f39,f42,f42])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.58    inference(cnf_transformation,[],[f21])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).
% 0.21/0.58  fof(f20,plain,(
% 0.21/0.58    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f19,plain,(
% 0.21/0.58    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f18])).
% 0.21/0.58  fof(f18,negated_conjecture,(
% 0.21/0.58    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.58    inference(negated_conjecture,[],[f17])).
% 0.21/0.58  fof(f17,conjecture,(
% 0.21/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (7010)------------------------------
% 0.21/0.58  % (7010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (7010)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (7010)Memory used [KB]: 7291
% 0.21/0.58  % (7010)Time elapsed: 0.147 s
% 0.21/0.58  % (7010)------------------------------
% 0.21/0.58  % (7010)------------------------------
% 0.21/0.59  % (7003)Success in time 0.226 s
%------------------------------------------------------------------------------
