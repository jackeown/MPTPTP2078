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

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 444 expanded)
%              Number of leaves         :   18 ( 163 expanded)
%              Depth                    :   13
%              Number of atoms          :   93 ( 475 expanded)
%              Number of equality atoms :   63 ( 438 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1587,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f217,f1562,f1569,f1586])).

fof(f1586,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f1575])).

fof(f1575,plain,
    ( $false
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f170,f1568])).

fof(f1568,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK1,sK0,sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f1566])).

fof(f1566,plain,
    ( spl3_5
  <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k4_enumset1(sK0,sK0,sK0,sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f170,plain,(
    ! [X23,X21,X22,X20] : k4_enumset1(X20,X20,X20,X22,X23,X21) = k4_enumset1(X20,X20,X20,X23,X22,X21) ),
    inference(superposition,[],[f49,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X2,X3,X1) ),
    inference(definition_unfolding,[],[f31,f40,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X3,X2,X1) ),
    inference(definition_unfolding,[],[f33,f40,f40])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

fof(f1569,plain,
    ( ~ spl3_5
    | spl3_4 ),
    inference(avatar_split_clause,[],[f1563,f1559,f1566])).

fof(f1559,plain,
    ( spl3_4
  <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1563,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK1,sK0,sK2)
    | spl3_4 ),
    inference(superposition,[],[f1561,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k4_enumset1(X0,X0,X0,X1,X2,X3)))) ),
    inference(definition_unfolding,[],[f38,f39,f40,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f25,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f29,f40])).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
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

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

fof(f1561,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f1559])).

fof(f1562,plain,
    ( ~ spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f1557,f214,f1559])).

fof(f214,plain,
    ( spl3_2
  <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1557,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_2 ),
    inference(forward_demodulation,[],[f1556,f330])).

fof(f330,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X1,X2,X3,X3) ),
    inference(superposition,[],[f51,f44])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k5_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X3),k3_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X3),k4_enumset1(X0,X0,X0,X0,X1,X2)))) ),
    inference(definition_unfolding,[],[f36,f40,f39,f41,f43])).

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
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f1556,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_2 ),
    inference(forward_demodulation,[],[f1555,f330])).

fof(f1555,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_2 ),
    inference(forward_demodulation,[],[f1455,f330])).

fof(f1455,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK1))))
    | spl3_2 ),
    inference(backward_demodulation,[],[f216,f330])).

fof(f216,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f214])).

fof(f217,plain,
    ( ~ spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f212,f53,f214])).

fof(f53,plain,
    ( spl3_1
  <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f212,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f211,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X1,X1,X1,X3,X2,X0) ),
    inference(definition_unfolding,[],[f32,f40,f40])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

fof(f211,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK0,sK2,sK2),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK0,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f210,f47])).

fof(f210,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK0,sK2),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f209,f47])).

fof(f209,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f208,f48])).

fof(f208,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK0,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK0,sK1,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f207,f47])).

fof(f207,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK0,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK0,sK1))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f55,f47])).

fof(f55,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f56,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f45,f53])).

fof(f45,plain,(
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
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (22322)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.45  % (22314)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (22308)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (22317)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (22312)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (22316)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (22320)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (22309)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (22313)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (22307)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (22311)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (22319)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.50  % (22315)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.50  % (22318)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.50  % (22318)Refutation not found, incomplete strategy% (22318)------------------------------
% 0.20/0.50  % (22318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (22318)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (22318)Memory used [KB]: 10618
% 0.20/0.50  % (22318)Time elapsed: 0.080 s
% 0.20/0.50  % (22318)------------------------------
% 0.20/0.50  % (22318)------------------------------
% 0.20/0.51  % (22323)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.51  % (22321)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.51  % (22310)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.52  % (22324)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.60/0.61  % (22313)Refutation found. Thanks to Tanya!
% 1.60/0.61  % SZS status Theorem for theBenchmark
% 1.60/0.61  % SZS output start Proof for theBenchmark
% 1.60/0.61  fof(f1587,plain,(
% 1.60/0.61    $false),
% 1.60/0.61    inference(avatar_sat_refutation,[],[f56,f217,f1562,f1569,f1586])).
% 1.60/0.61  fof(f1586,plain,(
% 1.60/0.61    spl3_5),
% 1.60/0.61    inference(avatar_contradiction_clause,[],[f1575])).
% 1.60/0.61  fof(f1575,plain,(
% 1.60/0.61    $false | spl3_5),
% 1.60/0.61    inference(unit_resulting_resolution,[],[f170,f1568])).
% 1.60/0.61  fof(f1568,plain,(
% 1.60/0.61    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK1,sK0,sK2) | spl3_5),
% 1.60/0.61    inference(avatar_component_clause,[],[f1566])).
% 1.60/0.61  fof(f1566,plain,(
% 1.60/0.61    spl3_5 <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k4_enumset1(sK0,sK0,sK0,sK1,sK0,sK2)),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.60/0.61  fof(f170,plain,(
% 1.60/0.61    ( ! [X23,X21,X22,X20] : (k4_enumset1(X20,X20,X20,X22,X23,X21) = k4_enumset1(X20,X20,X20,X23,X22,X21)) )),
% 1.60/0.61    inference(superposition,[],[f49,f47])).
% 1.60/0.61  fof(f47,plain,(
% 1.60/0.61    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X2,X3,X1)) )),
% 1.60/0.61    inference(definition_unfolding,[],[f31,f40,f40])).
% 1.60/0.61  fof(f40,plain,(
% 1.60/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.60/0.61    inference(definition_unfolding,[],[f35,f37])).
% 1.60/0.61  fof(f37,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f16])).
% 1.60/0.61  fof(f16,axiom,(
% 1.60/0.61    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.60/0.61  fof(f35,plain,(
% 1.60/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f15])).
% 1.60/0.61  fof(f15,axiom,(
% 1.60/0.61    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.60/0.61  fof(f31,plain,(
% 1.60/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f6])).
% 1.60/0.61  fof(f6,axiom,(
% 1.60/0.61    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).
% 1.60/0.61  fof(f49,plain,(
% 1.60/0.61    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X3,X2,X1)) )),
% 1.60/0.61    inference(definition_unfolding,[],[f33,f40,f40])).
% 1.60/0.61  fof(f33,plain,(
% 1.60/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f7])).
% 1.60/0.61  fof(f7,axiom,(
% 1.60/0.61    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).
% 1.60/0.61  fof(f1569,plain,(
% 1.60/0.61    ~spl3_5 | spl3_4),
% 1.60/0.61    inference(avatar_split_clause,[],[f1563,f1559,f1566])).
% 1.60/0.61  fof(f1559,plain,(
% 1.60/0.61    spl3_4 <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.60/0.61  fof(f1563,plain,(
% 1.60/0.61    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK1,sK0,sK2) | spl3_4),
% 1.60/0.61    inference(superposition,[],[f1561,f44])).
% 1.60/0.61  fof(f44,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k4_enumset1(X0,X0,X0,X1,X2,X3))))) )),
% 1.60/0.61    inference(definition_unfolding,[],[f38,f39,f40,f42])).
% 1.60/0.61  fof(f42,plain,(
% 1.60/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.60/0.61    inference(definition_unfolding,[],[f25,f41])).
% 1.60/0.61  fof(f41,plain,(
% 1.60/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.60/0.61    inference(definition_unfolding,[],[f29,f40])).
% 1.60/0.61  fof(f29,plain,(
% 1.60/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f14])).
% 1.60/0.61  fof(f14,axiom,(
% 1.60/0.61    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.60/0.61  fof(f25,plain,(
% 1.60/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f13])).
% 1.60/0.61  fof(f13,axiom,(
% 1.60/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.60/0.61  fof(f39,plain,(
% 1.60/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.60/0.61    inference(definition_unfolding,[],[f27,f26])).
% 1.60/0.61  fof(f26,plain,(
% 1.60/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.60/0.61    inference(cnf_transformation,[],[f2])).
% 1.60/0.61  fof(f2,axiom,(
% 1.60/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.60/0.61  fof(f27,plain,(
% 1.60/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.60/0.61    inference(cnf_transformation,[],[f5])).
% 1.60/0.61  fof(f5,axiom,(
% 1.60/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.60/0.61  fof(f38,plain,(
% 1.60/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 1.60/0.61    inference(cnf_transformation,[],[f11])).
% 1.60/0.61  fof(f11,axiom,(
% 1.60/0.61    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).
% 1.60/0.61  fof(f1561,plain,(
% 1.60/0.61    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_4),
% 1.60/0.61    inference(avatar_component_clause,[],[f1559])).
% 1.60/0.61  fof(f1562,plain,(
% 1.60/0.61    ~spl3_4 | spl3_2),
% 1.60/0.61    inference(avatar_split_clause,[],[f1557,f214,f1559])).
% 1.60/0.61  fof(f214,plain,(
% 1.60/0.61    spl3_2 <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1))))),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.60/0.61  fof(f1557,plain,(
% 1.60/0.61    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_2),
% 1.60/0.61    inference(forward_demodulation,[],[f1556,f330])).
% 1.60/0.61  fof(f330,plain,(
% 1.60/0.61    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X1,X2,X3,X3)) )),
% 1.60/0.61    inference(superposition,[],[f51,f44])).
% 1.60/0.61  fof(f51,plain,(
% 1.60/0.61    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k5_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X3),k3_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X3),k4_enumset1(X0,X0,X0,X0,X1,X2))))) )),
% 1.60/0.61    inference(definition_unfolding,[],[f36,f40,f39,f41,f43])).
% 1.60/0.61  fof(f43,plain,(
% 1.60/0.61    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.60/0.61    inference(definition_unfolding,[],[f23,f42])).
% 1.60/0.61  fof(f23,plain,(
% 1.60/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f12])).
% 1.60/0.61  fof(f12,axiom,(
% 1.60/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.60/0.61  fof(f36,plain,(
% 1.60/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.60/0.61    inference(cnf_transformation,[],[f10])).
% 1.60/0.61  fof(f10,axiom,(
% 1.60/0.61    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 1.60/0.61  fof(f1556,plain,(
% 1.60/0.61    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_2),
% 1.60/0.61    inference(forward_demodulation,[],[f1555,f330])).
% 1.60/0.61  fof(f1555,plain,(
% 1.60/0.61    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_2),
% 1.60/0.61    inference(forward_demodulation,[],[f1455,f330])).
% 1.60/0.61  fof(f1455,plain,(
% 1.60/0.61    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK1)))) | spl3_2),
% 1.60/0.61    inference(backward_demodulation,[],[f216,f330])).
% 1.60/0.61  fof(f216,plain,(
% 1.60/0.61    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_2),
% 1.60/0.61    inference(avatar_component_clause,[],[f214])).
% 1.60/0.61  fof(f217,plain,(
% 1.60/0.61    ~spl3_2 | spl3_1),
% 1.60/0.61    inference(avatar_split_clause,[],[f212,f53,f214])).
% 1.60/0.61  fof(f53,plain,(
% 1.60/0.61    spl3_1 <=> k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0))))),
% 1.60/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.60/0.61  fof(f212,plain,(
% 1.60/0.61    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 1.60/0.61    inference(forward_demodulation,[],[f211,f48])).
% 1.60/0.61  fof(f48,plain,(
% 1.60/0.61    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X1,X1,X1,X3,X2,X0)) )),
% 1.60/0.61    inference(definition_unfolding,[],[f32,f40,f40])).
% 1.60/0.61  fof(f32,plain,(
% 1.60/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 1.60/0.61    inference(cnf_transformation,[],[f8])).
% 1.60/0.61  fof(f8,axiom,(
% 1.60/0.61    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).
% 1.60/0.61  fof(f211,plain,(
% 1.60/0.61    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK0,sK2,sK2),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK0,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 1.60/0.61    inference(forward_demodulation,[],[f210,f47])).
% 1.60/0.61  fof(f210,plain,(
% 1.60/0.61    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK0,sK2),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 1.60/0.61    inference(forward_demodulation,[],[f209,f47])).
% 1.60/0.61  fof(f209,plain,(
% 1.60/0.61    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1)))) | spl3_1),
% 1.60/0.61    inference(forward_demodulation,[],[f208,f48])).
% 1.60/0.61  fof(f208,plain,(
% 1.60/0.61    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK0,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK0,sK1,sK1)))) | spl3_1),
% 1.60/0.61    inference(forward_demodulation,[],[f207,f47])).
% 1.60/0.61  fof(f207,plain,(
% 1.60/0.61    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK0,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK0,sK1)))) | spl3_1),
% 1.60/0.61    inference(forward_demodulation,[],[f55,f47])).
% 1.60/0.61  fof(f55,plain,(
% 1.60/0.61    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0)))) | spl3_1),
% 1.60/0.61    inference(avatar_component_clause,[],[f53])).
% 1.60/0.61  fof(f56,plain,(
% 1.60/0.61    ~spl3_1),
% 1.60/0.61    inference(avatar_split_clause,[],[f45,f53])).
% 1.60/0.61  fof(f45,plain,(
% 1.60/0.61    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0))))),
% 1.60/0.61    inference(definition_unfolding,[],[f22,f41,f39,f42,f42])).
% 1.60/0.61  fof(f22,plain,(
% 1.60/0.61    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.60/0.61    inference(cnf_transformation,[],[f21])).
% 1.60/0.61  fof(f21,plain,(
% 1.60/0.61    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.60/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).
% 1.60/0.61  fof(f20,plain,(
% 1.60/0.61    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.60/0.61    introduced(choice_axiom,[])).
% 1.60/0.61  fof(f19,plain,(
% 1.60/0.61    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.60/0.61    inference(ennf_transformation,[],[f18])).
% 1.60/0.61  fof(f18,negated_conjecture,(
% 1.60/0.61    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.60/0.61    inference(negated_conjecture,[],[f17])).
% 1.60/0.61  fof(f17,conjecture,(
% 1.60/0.61    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.60/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 1.60/0.61  % SZS output end Proof for theBenchmark
% 1.60/0.61  % (22313)------------------------------
% 1.60/0.61  % (22313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.61  % (22313)Termination reason: Refutation
% 1.60/0.61  
% 1.60/0.61  % (22313)Memory used [KB]: 7547
% 1.60/0.61  % (22313)Time elapsed: 0.180 s
% 1.60/0.61  % (22313)------------------------------
% 1.60/0.61  % (22313)------------------------------
% 1.60/0.61  % (22306)Success in time 0.255 s
%------------------------------------------------------------------------------
