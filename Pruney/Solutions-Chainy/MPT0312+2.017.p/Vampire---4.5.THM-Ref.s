%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 340 expanded)
%              Number of leaves         :   26 ( 120 expanded)
%              Depth                    :   18
%              Number of atoms          :  161 ( 447 expanded)
%              Number of equality atoms :   86 ( 323 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f259,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f80,f120,f121,f167,f223,f257])).

fof(f257,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | spl4_11 ),
    inference(trivial_inequality_removal,[],[f240])).

fof(f240,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2)
    | spl4_11 ),
    inference(backward_demodulation,[],[f222,f226])).

fof(f226,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f103,f37])).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f103,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f89,f81])).

fof(f81,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f37,f34])).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f89,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f45,f32])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f45,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f222,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,sK3)))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl4_11
  <=> k2_zfmisc_1(sK0,sK2) = k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f223,plain,
    ( ~ spl4_11
    | spl4_1
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f218,f164,f111,f67,f220])).

fof(f67,plain,
    ( spl4_1
  <=> k2_zfmisc_1(sK0,sK2) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f111,plain,
    ( spl4_4
  <=> sK1 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f164,plain,
    ( spl4_8
  <=> sK3 = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f218,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,sK3)))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f217,f34])).

fof(f217,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(sK3,k5_xboole_0(sK2,sK3)))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f216,f32])).

fof(f216,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK3,k5_xboole_0(sK2,sK3)))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f215,f113])).

fof(f113,plain,
    ( sK1 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f215,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k5_xboole_0(sK3,k5_xboole_0(sK2,sK3)))
    | spl4_1
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f197,f166])).

fof(f166,plain,
    ( sK3 = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f164])).

fof(f197,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k5_xboole_0(sK3,k5_xboole_0(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)))))
    | spl4_1 ),
    inference(superposition,[],[f69,f184])).

fof(f184,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))) ),
    inference(forward_demodulation,[],[f183,f45])).

fof(f183,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))) ),
    inference(forward_demodulation,[],[f65,f45])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),k5_xboole_0(k5_xboole_0(X2,X3),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) ),
    inference(definition_unfolding,[],[f47,f57,f57,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f42,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f69,plain,
    ( k2_zfmisc_1(sK0,sK2) != k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f167,plain,
    ( spl4_8
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f162,f116,f164])).

fof(f116,plain,
    ( spl4_5
  <=> sK3 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f162,plain,
    ( sK3 = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f161,f60])).

fof(f60,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f33,f56])).

fof(f33,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f161,plain,
    ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k1_xboole_0))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f160,f32])).

fof(f160,plain,
    ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(sK2,sK2)))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f159,f34])).

fof(f159,plain,
    ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(sK2,k5_xboole_0(sK2,k1_xboole_0))))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f135,f32])).

fof(f135,plain,
    ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK3,sK3)))))
    | ~ spl4_5 ),
    inference(superposition,[],[f130,f118])).

fof(f118,plain,
    ( sK3 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f116])).

fof(f130,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))))) ),
    inference(forward_demodulation,[],[f63,f45])).

fof(f63,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))) ),
    inference(definition_unfolding,[],[f41,f56,f56,f58])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f40,f57])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f121,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f109,f77,f111])).

fof(f77,plain,
    ( spl4_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f109,plain,
    ( sK1 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl4_3 ),
    inference(resolution,[],[f64,f79])).

fof(f79,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f43,f56])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f120,plain,
    ( spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f108,f72,f116])).

fof(f72,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f108,plain,
    ( sK3 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl4_2 ),
    inference(resolution,[],[f64,f74])).

fof(f74,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f80,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f29,f77])).

fof(f29,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_zfmisc_1)).

fof(f75,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f30,f72])).

fof(f30,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f59,f67])).

fof(f59,plain,(
    k2_zfmisc_1(sK0,sK2) != k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))) ),
    inference(definition_unfolding,[],[f31,f57])).

fof(f31,plain,(
    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:09:08 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (20071)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (20070)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (20075)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (20083)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (20073)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (20079)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (20075)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (20078)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.52  % (20077)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (20086)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.52  % (20085)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (20084)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.53  % (20074)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f259,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f70,f75,f80,f120,f121,f167,f223,f257])).
% 0.21/0.53  fof(f257,plain,(
% 0.21/0.53    spl4_11),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f256])).
% 0.21/0.53  fof(f256,plain,(
% 0.21/0.53    $false | spl4_11),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f240])).
% 0.21/0.53  fof(f240,plain,(
% 0.21/0.53    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2) | spl4_11),
% 0.21/0.53    inference(backward_demodulation,[],[f222,f226])).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 0.21/0.53    inference(superposition,[],[f103,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.21/0.53    inference(forward_demodulation,[],[f89,f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.21/0.53    inference(superposition,[],[f37,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(superposition,[],[f45,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.53  fof(f222,plain,(
% 0.21/0.53    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,sK3))) | spl4_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f220])).
% 0.21/0.53  fof(f220,plain,(
% 0.21/0.53    spl4_11 <=> k2_zfmisc_1(sK0,sK2) = k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,sK3)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.53  fof(f223,plain,(
% 0.21/0.53    ~spl4_11 | spl4_1 | ~spl4_4 | ~spl4_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f218,f164,f111,f67,f220])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    spl4_1 <=> k2_zfmisc_1(sK0,sK2) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    spl4_4 <=> sK1 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.53  fof(f164,plain,(
% 0.21/0.53    spl4_8 <=> sK3 = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,sK3))) | (spl4_1 | ~spl4_4 | ~spl4_8)),
% 0.21/0.53    inference(forward_demodulation,[],[f217,f34])).
% 0.21/0.53  fof(f217,plain,(
% 0.21/0.53    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(sK3,k5_xboole_0(sK2,sK3))) | (spl4_1 | ~spl4_4 | ~spl4_8)),
% 0.21/0.53    inference(forward_demodulation,[],[f216,f32])).
% 0.21/0.53  fof(f216,plain,(
% 0.21/0.53    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK3,k5_xboole_0(sK2,sK3))) | (spl4_1 | ~spl4_4 | ~spl4_8)),
% 0.21/0.53    inference(forward_demodulation,[],[f215,f113])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    sK1 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl4_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f111])).
% 0.21/0.53  fof(f215,plain,(
% 0.21/0.53    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k5_xboole_0(sK3,k5_xboole_0(sK2,sK3))) | (spl4_1 | ~spl4_8)),
% 0.21/0.53    inference(forward_demodulation,[],[f197,f166])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    sK3 = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) | ~spl4_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f164])).
% 0.21/0.53  fof(f197,plain,(
% 0.21/0.53    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k5_xboole_0(sK3,k5_xboole_0(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2))))) | spl4_1),
% 0.21/0.53    inference(superposition,[],[f69,f184])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f183,f45])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f65,f45])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),k5_xboole_0(k5_xboole_0(X2,X3),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f47,f57,f57,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f42,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f38,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f39,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f44,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f46,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f48,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f49,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    k2_zfmisc_1(sK0,sK2) != k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))) | spl4_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f67])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    spl4_8 | ~spl4_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f162,f116,f164])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    spl4_5 <=> sK3 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    sK3 = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) | ~spl4_5),
% 0.21/0.53    inference(forward_demodulation,[],[f161,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f33,f56])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k1_xboole_0)) | ~spl4_5),
% 0.21/0.53    inference(forward_demodulation,[],[f160,f32])).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(sK2,sK2))) | ~spl4_5),
% 0.21/0.53    inference(forward_demodulation,[],[f159,f34])).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(sK2,k5_xboole_0(sK2,k1_xboole_0)))) | ~spl4_5),
% 0.21/0.53    inference(forward_demodulation,[],[f135,f32])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK3,sK3))))) | ~spl4_5),
% 0.21/0.53    inference(superposition,[],[f130,f118])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    sK3 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | ~spl4_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f116])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f63,f45])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f41,f56,f56,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f40,f57])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    spl4_4 | ~spl4_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f109,f77,f111])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    spl4_3 <=> r1_tarski(sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    sK1 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl4_3),
% 0.21/0.53    inference(resolution,[],[f64,f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    r1_tarski(sK0,sK1) | ~spl4_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f77])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1) )),
% 0.21/0.53    inference(definition_unfolding,[],[f43,f56])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    spl4_5 | ~spl4_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f108,f72,f116])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    spl4_2 <=> r1_tarski(sK2,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    sK3 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | ~spl4_2),
% 0.21/0.53    inference(resolution,[],[f64,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    r1_tarski(sK2,sK3) | ~spl4_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f72])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    spl4_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f29,f77])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    r1_tarski(sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))),
% 0.21/0.53    inference(negated_conjecture,[],[f20])).
% 0.21/0.53  fof(f20,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_zfmisc_1)).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    spl4_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f30,f72])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    r1_tarski(sK2,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ~spl4_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f59,f67])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    k2_zfmisc_1(sK0,sK2) != k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))))),
% 0.21/0.53    inference(definition_unfolding,[],[f31,f57])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (20075)------------------------------
% 0.21/0.53  % (20075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20075)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (20075)Memory used [KB]: 6396
% 0.21/0.53  % (20075)Time elapsed: 0.081 s
% 0.21/0.53  % (20075)------------------------------
% 0.21/0.53  % (20075)------------------------------
% 0.21/0.53  % (20068)Success in time 0.164 s
%------------------------------------------------------------------------------
