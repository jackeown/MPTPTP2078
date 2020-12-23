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
% DateTime   : Thu Dec  3 12:40:36 EST 2020

% Result     : Theorem 3.31s
% Output     : Refutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :  192 (2149 expanded)
%              Number of leaves         :   42 ( 746 expanded)
%              Depth                    :   18
%              Number of atoms          :  339 (2384 expanded)
%              Number of equality atoms :  153 (2094 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f831,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f102,f125,f214,f220,f268,f732,f739,f743,f747,f749,f751,f757,f760,f766,f768,f772,f777,f792,f796,f798,f801,f816,f821,f825,f829])).

fof(f829,plain,
    ( spl2_19
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f805,f790,f770,f827])).

fof(f827,plain,
    ( spl2_19
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f770,plain,
    ( spl2_13
  <=> r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f790,plain,
    ( spl2_15
  <=> k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f805,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(backward_demodulation,[],[f771,f791])).

fof(f791,plain,
    ( k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f790])).

fof(f771,plain,
    ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f770])).

fof(f825,plain,
    ( spl2_18
    | ~ spl2_5
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f823,f790,f218,f819])).

fof(f819,plain,
    ( spl2_18
  <=> k1_xboole_0 = k5_xboole_0(sK0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f218,plain,
    ( spl2_5
  <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f823,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)))
    | ~ spl2_5
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f822,f80])).

fof(f80,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f42,f70,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f61,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f62,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f822,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0)))
    | ~ spl2_5
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f804,f104])).

fof(f104,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f103,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f103,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f79,f78])).

fof(f78,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f40,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f70])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f79,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f41,f72])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f49,f71])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f804,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0))))
    | ~ spl2_5
    | ~ spl2_15 ),
    inference(backward_demodulation,[],[f767,f791])).

fof(f767,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f218])).

fof(f821,plain,
    ( ~ spl2_18
    | spl2_6
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f817,f790,f266,f819])).

fof(f266,plain,
    ( spl2_6
  <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f817,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)))
    | spl2_6
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f803,f80])).

fof(f803,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0)))
    | spl2_6
    | ~ spl2_15 ),
    inference(backward_demodulation,[],[f765,f791])).

fof(f765,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f266])).

fof(f816,plain,
    ( ~ spl2_17
    | spl2_4
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f812,f790,f212,f814])).

fof(f814,plain,
    ( spl2_17
  <=> sK0 = k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f212,plain,
    ( spl2_4
  <=> sK0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f812,plain,
    ( sK0 != k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)))
    | spl2_4
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f802,f80])).

fof(f802,plain,
    ( sK0 != k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0)))
    | spl2_4
    | ~ spl2_15 ),
    inference(backward_demodulation,[],[f213,f791])).

fof(f213,plain,
    ( sK0 != k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f212])).

fof(f801,plain,
    ( spl2_16
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f800,f775,f794])).

fof(f794,plain,
    ( spl2_16
  <=> sK0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f775,plain,
    ( spl2_14
  <=> sK0 = k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f800,plain,
    ( sK0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f787,f104])).

fof(f787,plain,
    ( k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) = k5_xboole_0(k1_xboole_0,sK0)
    | ~ spl2_14 ),
    inference(superposition,[],[f361,f776])).

fof(f776,plain,
    ( sK0 = k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f775])).

fof(f361,plain,(
    ! [X35,X36] : k5_xboole_0(X36,X35) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X35,X36)) ),
    inference(superposition,[],[f142,f104])).

fof(f142,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8)) ),
    inference(superposition,[],[f60,f43])).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f60,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f798,plain,
    ( spl2_15
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f797,f775,f790])).

fof(f797,plain,
    ( k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f785,f37])).

fof(f785,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(sK0,sK0)
    | ~ spl2_14 ),
    inference(superposition,[],[f174,f776])).

fof(f174,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f156,f156])).

fof(f156,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f148,f43])).

fof(f148,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f134,f104])).

fof(f134,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f60,f37])).

fof(f796,plain,
    ( spl2_16
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f783,f775,f794])).

fof(f783,plain,
    ( sK0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)
    | ~ spl2_14 ),
    inference(superposition,[],[f156,f776])).

fof(f792,plain,
    ( spl2_15
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f788,f775,f790])).

fof(f788,plain,
    ( k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f782,f37])).

fof(f782,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(sK0,sK0)
    | ~ spl2_14 ),
    inference(superposition,[],[f148,f776])).

fof(f777,plain,
    ( spl2_14
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f773,f218,f123,f775])).

fof(f123,plain,
    ( spl2_3
  <=> sK0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f773,plain,
    ( sK0 = k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f759,f767])).

fof(f759,plain,
    ( sK0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f123])).

fof(f772,plain,
    ( spl2_13
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f763,f97,f770])).

fof(f97,plain,
    ( spl2_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f763,plain,
    ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f98,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f53,f74])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f70])).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f98,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f768,plain,
    ( spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f762,f97,f218])).

fof(f762,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))
    | ~ spl2_2 ),
    inference(resolution,[],[f98,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(X1,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) ) ),
    inference(backward_demodulation,[],[f83,f60])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ) ),
    inference(definition_unfolding,[],[f50,f74,f72,f74])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f766,plain,
    ( ~ spl2_6
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f764,f97,f266])).

fof(f764,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f761,f80])).

fof(f761,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k5_xboole_0(sK0,k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)))
    | ~ spl2_2 ),
    inference(resolution,[],[f98,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(X1,k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) ) ),
    inference(backward_demodulation,[],[f120,f148])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(X1,k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)))))
      | ~ r2_hidden(X0,X1) ) ),
    inference(backward_demodulation,[],[f88,f60])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)))) ) ),
    inference(definition_unfolding,[],[f56,f74,f73,f74])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f48,f72])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f760,plain,
    ( spl2_3
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f758,f94,f123])).

fof(f94,plain,
    ( spl2_1
  <=> sK0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f758,plain,
    ( sK0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f100,f60])).

fof(f100,plain,
    ( sK0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f757,plain,
    ( spl2_12
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f753,f266,f755])).

fof(f755,plain,
    ( spl2_12
  <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f753,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK0)
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f726,f104])).

fof(f726,plain,
    ( k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK0) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl2_6 ),
    inference(superposition,[],[f361,f267])).

fof(f267,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f266])).

fof(f751,plain,
    ( spl2_10
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f750,f266,f741])).

fof(f741,plain,
    ( spl2_10
  <=> k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f750,plain,
    ( k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f724,f43])).

fof(f724,plain,
    ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)
    | ~ spl2_6 ),
    inference(superposition,[],[f174,f267])).

fof(f749,plain,
    ( spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f723,f266,f212])).

fof(f723,plain,
    ( sK0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | ~ spl2_6 ),
    inference(superposition,[],[f173,f267])).

fof(f173,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    inference(superposition,[],[f156,f148])).

fof(f747,plain,
    ( spl2_11
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f722,f266,f745])).

fof(f745,plain,
    ( spl2_11
  <=> sK0 = k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f722,plain,
    ( sK0 = k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl2_6 ),
    inference(superposition,[],[f156,f267])).

fof(f743,plain,
    ( spl2_10
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f721,f266,f741])).

fof(f721,plain,
    ( k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | ~ spl2_6 ),
    inference(superposition,[],[f148,f267])).

fof(f739,plain,
    ( spl2_8
    | ~ spl2_9
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f716,f266,f737,f734])).

fof(f734,plain,
    ( spl2_8
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f737,plain,
    ( spl2_9
  <=> r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f716,plain,
    ( ~ r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k1_xboole_0 = sK0
    | ~ spl2_6 ),
    inference(superposition,[],[f192,f267])).

fof(f192,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X5,k5_xboole_0(X5,k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4))))
      | k1_xboole_0 = X5 ) ),
    inference(superposition,[],[f150,f80])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))
      | k1_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f114,f148])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))))
      | k1_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f84,f60])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f51,f73])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f732,plain,
    ( spl2_7
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f728,f266,f730])).

fof(f730,plain,
    ( spl2_7
  <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f728,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f727,f80])).

fof(f727,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0))
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f715,f37])).

fof(f715,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | ~ spl2_6 ),
    inference(superposition,[],[f194,f267])).

fof(f194,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))) = X0 ),
    inference(superposition,[],[f116,f80])).

fof(f116,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) = X0 ),
    inference(backward_demodulation,[],[f81,f60])).

fof(f81,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = X0 ),
    inference(definition_unfolding,[],[f44,f71,f72])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f268,plain,
    ( spl2_6
    | spl2_2 ),
    inference(avatar_split_clause,[],[f264,f97,f266])).

fof(f264,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | spl2_2 ),
    inference(forward_demodulation,[],[f260,f80])).

fof(f260,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(sK0,k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)))
    | spl2_2 ),
    inference(resolution,[],[f152,f101])).

fof(f101,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f152,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(X1,k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) ) ),
    inference(backward_demodulation,[],[f119,f148])).

fof(f119,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(X1,k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)))))
      | r2_hidden(X0,X1) ) ),
    inference(backward_demodulation,[],[f89,f60])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)))) ) ),
    inference(definition_unfolding,[],[f55,f74,f73,f74])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f220,plain,
    ( ~ spl2_5
    | spl2_2 ),
    inference(avatar_split_clause,[],[f215,f97,f218])).

fof(f215,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))
    | spl2_2 ),
    inference(resolution,[],[f117,f101])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(X0,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) ) ),
    inference(backward_demodulation,[],[f85,f60])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k5_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f52,f74,f72,f74])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1))
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

fof(f214,plain,
    ( ~ spl2_4
    | spl2_3 ),
    inference(avatar_split_clause,[],[f210,f123,f212])).

fof(f210,plain,
    ( sK0 != k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | spl2_3 ),
    inference(superposition,[],[f124,f148])).

fof(f124,plain,
    ( sK0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f123])).

fof(f125,plain,
    ( ~ spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f121,f94,f123])).

fof(f121,plain,
    ( sK0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))))
    | spl2_1 ),
    inference(forward_demodulation,[],[f95,f60])).

fof(f95,plain,
    ( sK0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f102,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f77,f97,f94])).

fof(f77,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) ),
    inference(definition_unfolding,[],[f35,f73,f74])).

fof(f35,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f99,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f76,f97,f94])).

fof(f76,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) ),
    inference(definition_unfolding,[],[f36,f73,f74])).

fof(f36,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:26:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (23798)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (23790)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (23798)Refutation not found, incomplete strategy% (23798)------------------------------
% 0.22/0.51  % (23798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (23782)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (23798)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (23798)Memory used [KB]: 1791
% 0.22/0.51  % (23798)Time elapsed: 0.065 s
% 0.22/0.51  % (23798)------------------------------
% 0.22/0.51  % (23798)------------------------------
% 0.22/0.51  % (23797)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (23781)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (23787)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (23788)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (23786)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (23775)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (23793)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (23789)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (23800)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (23799)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (23779)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (23796)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (23797)Refutation not found, incomplete strategy% (23797)------------------------------
% 0.22/0.54  % (23797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23776)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (23797)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (23797)Memory used [KB]: 10874
% 0.22/0.54  % (23797)Time elapsed: 0.123 s
% 0.22/0.54  % (23797)------------------------------
% 0.22/0.54  % (23797)------------------------------
% 0.22/0.54  % (23780)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (23778)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (23801)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (23783)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (23777)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (23792)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (23792)Refutation not found, incomplete strategy% (23792)------------------------------
% 0.22/0.55  % (23792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23792)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (23792)Memory used [KB]: 10618
% 0.22/0.55  % (23792)Time elapsed: 0.139 s
% 0.22/0.55  % (23792)------------------------------
% 0.22/0.55  % (23792)------------------------------
% 0.22/0.55  % (23785)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (23784)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (23795)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (23804)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (23795)Refutation not found, incomplete strategy% (23795)------------------------------
% 0.22/0.55  % (23795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23795)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (23795)Memory used [KB]: 10746
% 0.22/0.55  % (23795)Time elapsed: 0.150 s
% 0.22/0.55  % (23795)------------------------------
% 0.22/0.55  % (23795)------------------------------
% 0.22/0.55  % (23802)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (23791)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (23803)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.56  % (23794)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.04/0.66  % (23843)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.04/0.66  % (23826)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.04/0.67  % (23849)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.74/0.73  % (23858)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 3.31/0.81  % (23780)Time limit reached!
% 3.31/0.81  % (23780)------------------------------
% 3.31/0.81  % (23780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.31/0.81  % (23780)Termination reason: Time limit
% 3.31/0.81  
% 3.31/0.81  % (23780)Memory used [KB]: 10490
% 3.31/0.81  % (23780)Time elapsed: 0.408 s
% 3.31/0.81  % (23780)------------------------------
% 3.31/0.81  % (23780)------------------------------
% 3.31/0.84  % (23803)Refutation found. Thanks to Tanya!
% 3.31/0.84  % SZS status Theorem for theBenchmark
% 3.31/0.85  % SZS output start Proof for theBenchmark
% 3.31/0.85  fof(f831,plain,(
% 3.31/0.85    $false),
% 3.31/0.85    inference(avatar_sat_refutation,[],[f99,f102,f125,f214,f220,f268,f732,f739,f743,f747,f749,f751,f757,f760,f766,f768,f772,f777,f792,f796,f798,f801,f816,f821,f825,f829])).
% 3.31/0.85  fof(f829,plain,(
% 3.31/0.85    spl2_19 | ~spl2_13 | ~spl2_15),
% 3.31/0.85    inference(avatar_split_clause,[],[f805,f790,f770,f827])).
% 3.31/0.85  fof(f827,plain,(
% 3.31/0.85    spl2_19 <=> r1_tarski(k1_xboole_0,sK0)),
% 3.31/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 3.31/0.85  fof(f770,plain,(
% 3.31/0.85    spl2_13 <=> r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)),
% 3.31/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 3.31/0.85  fof(f790,plain,(
% 3.31/0.85    spl2_15 <=> k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 3.31/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 3.31/0.85  fof(f805,plain,(
% 3.31/0.85    r1_tarski(k1_xboole_0,sK0) | (~spl2_13 | ~spl2_15)),
% 3.31/0.85    inference(backward_demodulation,[],[f771,f791])).
% 3.31/0.85  fof(f791,plain,(
% 3.31/0.85    k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl2_15),
% 3.31/0.85    inference(avatar_component_clause,[],[f790])).
% 3.31/0.85  fof(f771,plain,(
% 3.31/0.85    r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) | ~spl2_13),
% 3.31/0.85    inference(avatar_component_clause,[],[f770])).
% 3.31/0.85  fof(f825,plain,(
% 3.31/0.85    spl2_18 | ~spl2_5 | ~spl2_15),
% 3.31/0.85    inference(avatar_split_clause,[],[f823,f790,f218,f819])).
% 3.31/0.85  fof(f819,plain,(
% 3.31/0.85    spl2_18 <=> k1_xboole_0 = k5_xboole_0(sK0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)))),
% 3.31/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 3.31/0.85  fof(f218,plain,(
% 3.31/0.85    spl2_5 <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))),
% 3.31/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 3.31/0.85  fof(f823,plain,(
% 3.31/0.85    k1_xboole_0 = k5_xboole_0(sK0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0))) | (~spl2_5 | ~spl2_15)),
% 3.31/0.85    inference(forward_demodulation,[],[f822,f80])).
% 3.31/0.85  fof(f80,plain,(
% 3.31/0.85    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 3.31/0.85    inference(definition_unfolding,[],[f42,f70,f70])).
% 3.31/0.85  fof(f70,plain,(
% 3.31/0.85    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.31/0.85    inference(definition_unfolding,[],[f46,f69])).
% 3.31/0.85  fof(f69,plain,(
% 3.31/0.85    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.31/0.85    inference(definition_unfolding,[],[f59,f68])).
% 3.31/0.85  fof(f68,plain,(
% 3.31/0.85    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.31/0.85    inference(definition_unfolding,[],[f61,f67])).
% 3.31/0.85  fof(f67,plain,(
% 3.31/0.85    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.31/0.85    inference(definition_unfolding,[],[f62,f66])).
% 3.31/0.85  fof(f66,plain,(
% 3.31/0.85    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.31/0.85    inference(definition_unfolding,[],[f63,f64])).
% 3.31/0.85  fof(f64,plain,(
% 3.31/0.85    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.31/0.85    inference(cnf_transformation,[],[f20])).
% 3.31/0.85  fof(f20,axiom,(
% 3.31/0.85    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 3.31/0.85  fof(f63,plain,(
% 3.31/0.85    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.31/0.85    inference(cnf_transformation,[],[f19])).
% 3.31/0.85  fof(f19,axiom,(
% 3.31/0.85    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 3.31/0.85  fof(f62,plain,(
% 3.31/0.85    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.31/0.85    inference(cnf_transformation,[],[f18])).
% 3.31/0.85  fof(f18,axiom,(
% 3.31/0.85    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 3.31/0.85  fof(f61,plain,(
% 3.31/0.85    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.31/0.85    inference(cnf_transformation,[],[f17])).
% 3.31/0.85  fof(f17,axiom,(
% 3.31/0.85    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 3.31/0.85  fof(f59,plain,(
% 3.31/0.85    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.31/0.85    inference(cnf_transformation,[],[f16])).
% 3.31/0.85  fof(f16,axiom,(
% 3.31/0.85    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 3.31/0.85  fof(f46,plain,(
% 3.31/0.85    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.31/0.85    inference(cnf_transformation,[],[f15])).
% 3.31/0.85  fof(f15,axiom,(
% 3.31/0.85    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.31/0.85  fof(f42,plain,(
% 3.31/0.85    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.31/0.85    inference(cnf_transformation,[],[f12])).
% 3.31/0.85  fof(f12,axiom,(
% 3.31/0.85    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.31/0.85  fof(f822,plain,(
% 3.31/0.85    k1_xboole_0 = k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0))) | (~spl2_5 | ~spl2_15)),
% 3.31/0.85    inference(forward_demodulation,[],[f804,f104])).
% 3.31/0.85  fof(f104,plain,(
% 3.31/0.85    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 3.31/0.85    inference(forward_demodulation,[],[f103,f37])).
% 3.31/0.85  fof(f37,plain,(
% 3.31/0.85    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.31/0.85    inference(cnf_transformation,[],[f10])).
% 3.31/0.85  fof(f10,axiom,(
% 3.31/0.85    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 3.31/0.85  fof(f103,plain,(
% 3.31/0.85    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 3.31/0.85    inference(forward_demodulation,[],[f79,f78])).
% 3.31/0.85  fof(f78,plain,(
% 3.31/0.85    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 3.31/0.85    inference(definition_unfolding,[],[f40,f71])).
% 3.31/0.85  fof(f71,plain,(
% 3.31/0.85    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.31/0.85    inference(definition_unfolding,[],[f45,f70])).
% 3.31/0.85  fof(f45,plain,(
% 3.31/0.85    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.31/0.85    inference(cnf_transformation,[],[f25])).
% 3.31/0.85  fof(f25,axiom,(
% 3.31/0.85    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.31/0.85  fof(f40,plain,(
% 3.31/0.85    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 3.31/0.85    inference(cnf_transformation,[],[f29])).
% 3.31/0.85  fof(f29,plain,(
% 3.31/0.85    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 3.31/0.85    inference(rectify,[],[f2])).
% 3.31/0.85  fof(f2,axiom,(
% 3.31/0.85    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 3.31/0.85  fof(f79,plain,(
% 3.31/0.85    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 3.31/0.85    inference(definition_unfolding,[],[f41,f72])).
% 3.31/0.85  fof(f72,plain,(
% 3.31/0.85    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.31/0.85    inference(definition_unfolding,[],[f49,f71])).
% 3.31/0.85  fof(f49,plain,(
% 3.31/0.85    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 3.31/0.85    inference(cnf_transformation,[],[f11])).
% 3.31/0.85  fof(f11,axiom,(
% 3.31/0.85    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 3.31/0.85  fof(f41,plain,(
% 3.31/0.85    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.31/0.85    inference(cnf_transformation,[],[f30])).
% 3.31/0.85  fof(f30,plain,(
% 3.31/0.85    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.31/0.85    inference(rectify,[],[f3])).
% 3.31/0.85  fof(f3,axiom,(
% 3.31/0.85    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 3.31/0.85  fof(f804,plain,(
% 3.31/0.85    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0)))) | (~spl2_5 | ~spl2_15)),
% 3.31/0.85    inference(backward_demodulation,[],[f767,f791])).
% 3.31/0.85  fof(f767,plain,(
% 3.31/0.85    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) | ~spl2_5),
% 3.31/0.85    inference(avatar_component_clause,[],[f218])).
% 3.31/0.85  fof(f821,plain,(
% 3.31/0.85    ~spl2_18 | spl2_6 | ~spl2_15),
% 3.31/0.85    inference(avatar_split_clause,[],[f817,f790,f266,f819])).
% 3.31/0.85  fof(f266,plain,(
% 3.31/0.85    spl2_6 <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 3.31/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 3.31/0.85  fof(f817,plain,(
% 3.31/0.85    k1_xboole_0 != k5_xboole_0(sK0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0))) | (spl2_6 | ~spl2_15)),
% 3.31/0.85    inference(forward_demodulation,[],[f803,f80])).
% 3.31/0.85  fof(f803,plain,(
% 3.31/0.85    k1_xboole_0 != k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0))) | (spl2_6 | ~spl2_15)),
% 3.31/0.85    inference(backward_demodulation,[],[f765,f791])).
% 3.31/0.85  fof(f765,plain,(
% 3.31/0.85    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | spl2_6),
% 3.31/0.85    inference(avatar_component_clause,[],[f266])).
% 3.31/0.85  fof(f816,plain,(
% 3.31/0.85    ~spl2_17 | spl2_4 | ~spl2_15),
% 3.31/0.85    inference(avatar_split_clause,[],[f812,f790,f212,f814])).
% 3.31/0.85  fof(f814,plain,(
% 3.31/0.85    spl2_17 <=> sK0 = k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0)))),
% 3.31/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 3.31/0.85  fof(f212,plain,(
% 3.31/0.85    spl2_4 <=> sK0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 3.31/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 3.31/0.85  fof(f812,plain,(
% 3.31/0.85    sK0 != k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK0))) | (spl2_4 | ~spl2_15)),
% 3.31/0.85    inference(forward_demodulation,[],[f802,f80])).
% 3.31/0.85  fof(f802,plain,(
% 3.31/0.85    sK0 != k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0))) | (spl2_4 | ~spl2_15)),
% 3.31/0.85    inference(backward_demodulation,[],[f213,f791])).
% 3.31/0.85  fof(f213,plain,(
% 3.31/0.85    sK0 != k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | spl2_4),
% 3.31/0.85    inference(avatar_component_clause,[],[f212])).
% 3.31/0.85  fof(f801,plain,(
% 3.31/0.85    spl2_16 | ~spl2_14),
% 3.31/0.85    inference(avatar_split_clause,[],[f800,f775,f794])).
% 3.31/0.85  fof(f794,plain,(
% 3.31/0.85    spl2_16 <=> sK0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)),
% 3.31/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 3.31/0.85  fof(f775,plain,(
% 3.31/0.85    spl2_14 <=> sK0 = k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 3.31/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 3.31/0.85  fof(f800,plain,(
% 3.31/0.85    sK0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) | ~spl2_14),
% 3.31/0.85    inference(forward_demodulation,[],[f787,f104])).
% 3.31/0.85  fof(f787,plain,(
% 3.31/0.85    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) = k5_xboole_0(k1_xboole_0,sK0) | ~spl2_14),
% 3.31/0.85    inference(superposition,[],[f361,f776])).
% 3.31/0.85  fof(f776,plain,(
% 3.31/0.85    sK0 = k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl2_14),
% 3.31/0.85    inference(avatar_component_clause,[],[f775])).
% 3.31/0.85  fof(f361,plain,(
% 3.31/0.85    ( ! [X35,X36] : (k5_xboole_0(X36,X35) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X35,X36))) )),
% 3.31/0.85    inference(superposition,[],[f142,f104])).
% 3.31/0.85  fof(f142,plain,(
% 3.31/0.85    ( ! [X8,X7,X9] : (k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8))) )),
% 3.31/0.85    inference(superposition,[],[f60,f43])).
% 3.31/0.85  fof(f43,plain,(
% 3.31/0.85    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.31/0.85    inference(cnf_transformation,[],[f1])).
% 3.31/0.85  fof(f1,axiom,(
% 3.31/0.85    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 3.31/0.85  fof(f60,plain,(
% 3.31/0.85    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 3.31/0.85    inference(cnf_transformation,[],[f9])).
% 3.31/0.85  fof(f9,axiom,(
% 3.31/0.85    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 3.31/0.85  fof(f798,plain,(
% 3.31/0.85    spl2_15 | ~spl2_14),
% 3.31/0.85    inference(avatar_split_clause,[],[f797,f775,f790])).
% 3.31/0.85  fof(f797,plain,(
% 3.31/0.85    k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl2_14),
% 3.31/0.85    inference(forward_demodulation,[],[f785,f37])).
% 3.31/0.85  fof(f785,plain,(
% 3.31/0.85    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(sK0,sK0) | ~spl2_14),
% 3.31/0.85    inference(superposition,[],[f174,f776])).
% 3.31/0.85  fof(f174,plain,(
% 3.31/0.85    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 3.31/0.85    inference(superposition,[],[f156,f156])).
% 3.31/0.85  fof(f156,plain,(
% 3.31/0.85    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 3.31/0.85    inference(superposition,[],[f148,f43])).
% 3.31/0.85  fof(f148,plain,(
% 3.31/0.85    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 3.31/0.85    inference(forward_demodulation,[],[f134,f104])).
% 3.31/0.85  fof(f134,plain,(
% 3.31/0.85    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 3.31/0.85    inference(superposition,[],[f60,f37])).
% 3.31/0.85  fof(f796,plain,(
% 3.31/0.85    spl2_16 | ~spl2_14),
% 3.31/0.85    inference(avatar_split_clause,[],[f783,f775,f794])).
% 3.31/0.85  fof(f783,plain,(
% 3.31/0.85    sK0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) | ~spl2_14),
% 3.31/0.85    inference(superposition,[],[f156,f776])).
% 3.31/0.85  fof(f792,plain,(
% 3.31/0.85    spl2_15 | ~spl2_14),
% 3.31/0.85    inference(avatar_split_clause,[],[f788,f775,f790])).
% 3.31/0.85  fof(f788,plain,(
% 3.31/0.85    k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl2_14),
% 3.31/0.85    inference(forward_demodulation,[],[f782,f37])).
% 3.31/0.85  fof(f782,plain,(
% 3.31/0.85    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(sK0,sK0) | ~spl2_14),
% 3.31/0.85    inference(superposition,[],[f148,f776])).
% 3.31/0.85  fof(f777,plain,(
% 3.31/0.85    spl2_14 | ~spl2_3 | ~spl2_5),
% 3.31/0.85    inference(avatar_split_clause,[],[f773,f218,f123,f775])).
% 3.31/0.85  fof(f123,plain,(
% 3.31/0.85    spl2_3 <=> sK0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))))),
% 3.31/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 3.31/0.85  fof(f773,plain,(
% 3.31/0.85    sK0 = k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | (~spl2_3 | ~spl2_5)),
% 3.31/0.85    inference(backward_demodulation,[],[f759,f767])).
% 3.31/0.85  fof(f759,plain,(
% 3.31/0.85    sK0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))) | ~spl2_3),
% 3.31/0.85    inference(avatar_component_clause,[],[f123])).
% 3.31/0.85  fof(f772,plain,(
% 3.31/0.85    spl2_13 | ~spl2_2),
% 3.31/0.85    inference(avatar_split_clause,[],[f763,f97,f770])).
% 3.31/0.85  fof(f97,plain,(
% 3.31/0.85    spl2_2 <=> r2_hidden(sK1,sK0)),
% 3.31/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 3.31/0.85  fof(f763,plain,(
% 3.31/0.85    r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) | ~spl2_2),
% 3.31/0.85    inference(resolution,[],[f98,f87])).
% 3.31/0.85  fof(f87,plain,(
% 3.31/0.85    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 3.31/0.85    inference(definition_unfolding,[],[f53,f74])).
% 3.31/0.85  fof(f74,plain,(
% 3.31/0.85    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.31/0.85    inference(definition_unfolding,[],[f39,f70])).
% 3.31/0.85  fof(f39,plain,(
% 3.31/0.85    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.31/0.85    inference(cnf_transformation,[],[f14])).
% 3.31/0.85  fof(f14,axiom,(
% 3.31/0.85    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 3.31/0.85  fof(f53,plain,(
% 3.31/0.85    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 3.31/0.85    inference(cnf_transformation,[],[f21])).
% 3.31/0.85  fof(f21,axiom,(
% 3.31/0.85    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 3.31/0.85  fof(f98,plain,(
% 3.31/0.85    r2_hidden(sK1,sK0) | ~spl2_2),
% 3.31/0.85    inference(avatar_component_clause,[],[f97])).
% 3.31/0.85  fof(f768,plain,(
% 3.31/0.85    spl2_5 | ~spl2_2),
% 3.31/0.85    inference(avatar_split_clause,[],[f762,f97,f218])).
% 3.31/0.85  fof(f762,plain,(
% 3.31/0.85    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) | ~spl2_2),
% 3.31/0.85    inference(resolution,[],[f98,f118])).
% 3.31/0.85  fof(f118,plain,(
% 3.31/0.85    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(X1,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))))) )),
% 3.31/0.85    inference(backward_demodulation,[],[f83,f60])).
% 3.31/0.85  fof(f83,plain,(
% 3.31/0.85    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) )),
% 3.31/0.85    inference(definition_unfolding,[],[f50,f74,f72,f74])).
% 3.31/0.85  fof(f50,plain,(
% 3.31/0.85    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))) )),
% 3.31/0.85    inference(cnf_transformation,[],[f32])).
% 3.31/0.85  fof(f32,plain,(
% 3.31/0.85    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 3.31/0.85    inference(ennf_transformation,[],[f23])).
% 3.31/0.85  fof(f23,axiom,(
% 3.31/0.85    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 3.31/0.85  fof(f766,plain,(
% 3.31/0.85    ~spl2_6 | ~spl2_2),
% 3.31/0.85    inference(avatar_split_clause,[],[f764,f97,f266])).
% 3.31/0.85  fof(f764,plain,(
% 3.31/0.85    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | ~spl2_2),
% 3.31/0.85    inference(forward_demodulation,[],[f761,f80])).
% 3.31/0.85  fof(f761,plain,(
% 3.31/0.85    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k5_xboole_0(sK0,k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0))) | ~spl2_2),
% 3.31/0.85    inference(resolution,[],[f98,f151])).
% 3.31/0.85  fof(f151,plain,(
% 3.31/0.85    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(X1,k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)))) )),
% 3.31/0.85    inference(backward_demodulation,[],[f120,f148])).
% 3.31/0.85  fof(f120,plain,(
% 3.31/0.85    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(X1,k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))))) | ~r2_hidden(X0,X1)) )),
% 3.31/0.85    inference(backward_demodulation,[],[f88,f60])).
% 3.31/0.85  fof(f88,plain,(
% 3.31/0.85    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))))) )),
% 3.31/0.85    inference(definition_unfolding,[],[f56,f74,f73,f74])).
% 3.31/0.85  fof(f73,plain,(
% 3.31/0.85    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 3.31/0.85    inference(definition_unfolding,[],[f48,f72])).
% 3.31/0.85  fof(f48,plain,(
% 3.31/0.85    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.31/0.85    inference(cnf_transformation,[],[f4])).
% 3.31/0.85  fof(f4,axiom,(
% 3.31/0.85    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.31/0.85  fof(f56,plain,(
% 3.31/0.85    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) )),
% 3.31/0.85    inference(cnf_transformation,[],[f24])).
% 3.31/0.85  fof(f24,axiom,(
% 3.31/0.85    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 3.31/0.85  fof(f760,plain,(
% 3.31/0.85    spl2_3 | ~spl2_1),
% 3.31/0.85    inference(avatar_split_clause,[],[f758,f94,f123])).
% 3.31/0.85  fof(f94,plain,(
% 3.31/0.85    spl2_1 <=> sK0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))),
% 3.31/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 3.31/0.85  fof(f758,plain,(
% 3.31/0.85    sK0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))) | ~spl2_1),
% 3.31/0.85    inference(forward_demodulation,[],[f100,f60])).
% 3.31/0.85  fof(f100,plain,(
% 3.31/0.85    sK0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) | ~spl2_1),
% 3.31/0.85    inference(avatar_component_clause,[],[f94])).
% 3.31/0.85  fof(f757,plain,(
% 3.31/0.85    spl2_12 | ~spl2_6),
% 3.31/0.85    inference(avatar_split_clause,[],[f753,f266,f755])).
% 3.31/0.85  fof(f755,plain,(
% 3.31/0.85    spl2_12 <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK0)),
% 3.31/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 3.31/0.85  fof(f753,plain,(
% 3.31/0.85    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK0) | ~spl2_6),
% 3.31/0.85    inference(forward_demodulation,[],[f726,f104])).
% 3.31/0.85  fof(f726,plain,(
% 3.31/0.85    k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK0) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl2_6),
% 3.31/0.85    inference(superposition,[],[f361,f267])).
% 3.31/0.85  fof(f267,plain,(
% 3.31/0.85    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | ~spl2_6),
% 3.31/0.85    inference(avatar_component_clause,[],[f266])).
% 3.31/0.85  fof(f751,plain,(
% 3.31/0.85    spl2_10 | ~spl2_6),
% 3.31/0.85    inference(avatar_split_clause,[],[f750,f266,f741])).
% 3.31/0.85  fof(f741,plain,(
% 3.31/0.85    spl2_10 <=> k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 3.31/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 3.31/0.85  fof(f750,plain,(
% 3.31/0.85    k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | ~spl2_6),
% 3.31/0.85    inference(forward_demodulation,[],[f724,f43])).
% 3.31/0.85  fof(f724,plain,(
% 3.31/0.85    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) | ~spl2_6),
% 3.31/0.85    inference(superposition,[],[f174,f267])).
% 3.31/0.85  fof(f749,plain,(
% 3.31/0.85    spl2_4 | ~spl2_6),
% 3.31/0.85    inference(avatar_split_clause,[],[f723,f266,f212])).
% 3.31/0.85  fof(f723,plain,(
% 3.31/0.85    sK0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | ~spl2_6),
% 3.31/0.85    inference(superposition,[],[f173,f267])).
% 3.31/0.85  fof(f173,plain,(
% 3.31/0.85    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) )),
% 3.31/0.85    inference(superposition,[],[f156,f148])).
% 3.31/0.85  fof(f747,plain,(
% 3.31/0.85    spl2_11 | ~spl2_6),
% 3.31/0.85    inference(avatar_split_clause,[],[f722,f266,f745])).
% 3.31/0.85  fof(f745,plain,(
% 3.31/0.85    spl2_11 <=> sK0 = k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 3.31/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 3.31/0.85  fof(f722,plain,(
% 3.31/0.85    sK0 = k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl2_6),
% 3.31/0.85    inference(superposition,[],[f156,f267])).
% 3.31/0.85  fof(f743,plain,(
% 3.31/0.85    spl2_10 | ~spl2_6),
% 3.31/0.85    inference(avatar_split_clause,[],[f721,f266,f741])).
% 3.31/0.85  fof(f721,plain,(
% 3.31/0.85    k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | ~spl2_6),
% 3.31/0.85    inference(superposition,[],[f148,f267])).
% 3.31/0.85  fof(f739,plain,(
% 3.31/0.85    spl2_8 | ~spl2_9 | ~spl2_6),
% 3.31/0.85    inference(avatar_split_clause,[],[f716,f266,f737,f734])).
% 3.31/0.85  fof(f734,plain,(
% 3.31/0.85    spl2_8 <=> k1_xboole_0 = sK0),
% 3.31/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 3.31/0.85  fof(f737,plain,(
% 3.31/0.85    spl2_9 <=> r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 3.31/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 3.31/0.85  fof(f716,plain,(
% 3.31/0.85    ~r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | k1_xboole_0 = sK0 | ~spl2_6),
% 3.31/0.85    inference(superposition,[],[f192,f267])).
% 3.31/0.85  fof(f192,plain,(
% 3.31/0.85    ( ! [X4,X5] : (~r1_tarski(X5,k5_xboole_0(X5,k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4)))) | k1_xboole_0 = X5) )),
% 3.31/0.85    inference(superposition,[],[f150,f80])).
% 3.31/0.85  fof(f150,plain,(
% 3.31/0.85    ( ! [X0,X1] : (~r1_tarski(X0,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) | k1_xboole_0 = X0) )),
% 3.31/0.85    inference(backward_demodulation,[],[f114,f148])).
% 3.31/0.85  fof(f114,plain,(
% 3.31/0.85    ( ! [X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))) | k1_xboole_0 = X0) )),
% 3.31/0.85    inference(backward_demodulation,[],[f84,f60])).
% 3.31/0.85  fof(f84,plain,(
% 3.31/0.85    ( ! [X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) | k1_xboole_0 = X0) )),
% 3.31/0.85    inference(definition_unfolding,[],[f51,f73])).
% 3.31/0.85  fof(f51,plain,(
% 3.31/0.85    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 3.31/0.85    inference(cnf_transformation,[],[f33])).
% 3.31/0.85  fof(f33,plain,(
% 3.31/0.85    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 3.31/0.85    inference(ennf_transformation,[],[f6])).
% 3.31/0.85  fof(f6,axiom,(
% 3.31/0.85    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 3.31/0.85  fof(f732,plain,(
% 3.31/0.85    spl2_7 | ~spl2_6),
% 3.31/0.85    inference(avatar_split_clause,[],[f728,f266,f730])).
% 3.31/0.85  fof(f730,plain,(
% 3.31/0.85    spl2_7 <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 3.31/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 3.31/0.85  fof(f728,plain,(
% 3.31/0.85    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | ~spl2_6),
% 3.31/0.85    inference(forward_demodulation,[],[f727,f80])).
% 3.31/0.85  fof(f727,plain,(
% 3.31/0.85    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)) | ~spl2_6),
% 3.31/0.85    inference(forward_demodulation,[],[f715,f37])).
% 3.31/0.85  fof(f715,plain,(
% 3.31/0.85    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | ~spl2_6),
% 3.31/0.85    inference(superposition,[],[f194,f267])).
% 3.31/0.85  fof(f194,plain,(
% 3.31/0.85    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))) = X0) )),
% 3.31/0.85    inference(superposition,[],[f116,f80])).
% 3.31/0.85  fof(f116,plain,(
% 3.31/0.85    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) = X0) )),
% 3.31/0.85    inference(backward_demodulation,[],[f81,f60])).
% 3.31/0.85  fof(f81,plain,(
% 3.31/0.85    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = X0) )),
% 3.31/0.85    inference(definition_unfolding,[],[f44,f71,f72])).
% 3.31/0.85  fof(f44,plain,(
% 3.31/0.85    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.31/0.85    inference(cnf_transformation,[],[f5])).
% 3.31/0.85  fof(f5,axiom,(
% 3.31/0.85    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 3.31/0.85  fof(f268,plain,(
% 3.31/0.85    spl2_6 | spl2_2),
% 3.31/0.85    inference(avatar_split_clause,[],[f264,f97,f266])).
% 3.31/0.85  fof(f264,plain,(
% 3.31/0.85    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | spl2_2),
% 3.31/0.85    inference(forward_demodulation,[],[f260,f80])).
% 3.31/0.85  fof(f260,plain,(
% 3.31/0.85    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(sK0,k3_tarski(k6_enumset1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0))) | spl2_2),
% 3.31/0.85    inference(resolution,[],[f152,f101])).
% 3.31/0.85  fof(f101,plain,(
% 3.31/0.85    ~r2_hidden(sK1,sK0) | spl2_2),
% 3.31/0.85    inference(avatar_component_clause,[],[f97])).
% 3.31/0.85  fof(f152,plain,(
% 3.31/0.85    ( ! [X0,X1] : (r2_hidden(X0,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(X1,k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)))) )),
% 3.31/0.85    inference(backward_demodulation,[],[f119,f148])).
% 3.31/0.85  fof(f119,plain,(
% 3.31/0.85    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(X1,k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))))) | r2_hidden(X0,X1)) )),
% 3.31/0.85    inference(backward_demodulation,[],[f89,f60])).
% 3.31/0.85  fof(f89,plain,(
% 3.31/0.85    ( ! [X0,X1] : (r2_hidden(X0,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))))) )),
% 3.31/0.85    inference(definition_unfolding,[],[f55,f74,f73,f74])).
% 3.31/0.85  fof(f55,plain,(
% 3.31/0.85    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 3.31/0.85    inference(cnf_transformation,[],[f24])).
% 3.31/0.85  fof(f220,plain,(
% 3.31/0.85    ~spl2_5 | spl2_2),
% 3.31/0.85    inference(avatar_split_clause,[],[f215,f97,f218])).
% 3.31/0.85  fof(f215,plain,(
% 3.31/0.85    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) | spl2_2),
% 3.31/0.85    inference(resolution,[],[f117,f101])).
% 3.31/0.85  fof(f117,plain,(
% 3.31/0.85    ( ! [X0,X1] : (r2_hidden(X1,X0) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(X0,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))))) )),
% 3.31/0.85    inference(backward_demodulation,[],[f85,f60])).
% 3.31/0.85  fof(f85,plain,(
% 3.31/0.85    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k5_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) | r2_hidden(X1,X0)) )),
% 3.31/0.85    inference(definition_unfolding,[],[f52,f74,f72,f74])).
% 3.31/0.85  fof(f52,plain,(
% 3.31/0.85    ( ! [X0,X1] : (k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) | r2_hidden(X1,X0)) )),
% 3.31/0.85    inference(cnf_transformation,[],[f34])).
% 3.31/0.85  fof(f34,plain,(
% 3.31/0.85    ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)))),
% 3.31/0.85    inference(ennf_transformation,[],[f22])).
% 3.31/0.85  fof(f22,axiom,(
% 3.31/0.85    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).
% 3.31/0.85  fof(f214,plain,(
% 3.31/0.85    ~spl2_4 | spl2_3),
% 3.31/0.85    inference(avatar_split_clause,[],[f210,f123,f212])).
% 3.31/0.85  fof(f210,plain,(
% 3.31/0.85    sK0 != k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | spl2_3),
% 3.31/0.85    inference(superposition,[],[f124,f148])).
% 3.31/0.85  fof(f124,plain,(
% 3.31/0.85    sK0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))) | spl2_3),
% 3.31/0.85    inference(avatar_component_clause,[],[f123])).
% 3.31/0.85  fof(f125,plain,(
% 3.31/0.85    ~spl2_3 | spl2_1),
% 3.31/0.85    inference(avatar_split_clause,[],[f121,f94,f123])).
% 3.31/0.85  fof(f121,plain,(
% 3.31/0.85    sK0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))) | spl2_1),
% 3.31/0.85    inference(forward_demodulation,[],[f95,f60])).
% 3.31/0.85  fof(f95,plain,(
% 3.31/0.85    sK0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) | spl2_1),
% 3.31/0.85    inference(avatar_component_clause,[],[f94])).
% 3.31/0.85  fof(f102,plain,(
% 3.31/0.85    spl2_1 | ~spl2_2),
% 3.31/0.85    inference(avatar_split_clause,[],[f77,f97,f94])).
% 3.31/0.85  fof(f77,plain,(
% 3.31/0.85    ~r2_hidden(sK1,sK0) | sK0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))),
% 3.31/0.85    inference(definition_unfolding,[],[f35,f73,f74])).
% 3.31/0.85  fof(f35,plain,(
% 3.31/0.85    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 3.31/0.85    inference(cnf_transformation,[],[f31])).
% 3.31/0.85  fof(f31,plain,(
% 3.31/0.85    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 3.31/0.85    inference(ennf_transformation,[],[f28])).
% 3.31/0.85  fof(f28,negated_conjecture,(
% 3.31/0.85    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.31/0.85    inference(negated_conjecture,[],[f27])).
% 3.31/0.85  fof(f27,conjecture,(
% 3.31/0.85    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.31/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 3.31/0.85  fof(f99,plain,(
% 3.31/0.85    ~spl2_1 | spl2_2),
% 3.31/0.85    inference(avatar_split_clause,[],[f76,f97,f94])).
% 3.31/0.85  fof(f76,plain,(
% 3.31/0.85    r2_hidden(sK1,sK0) | sK0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))),
% 3.31/0.85    inference(definition_unfolding,[],[f36,f73,f74])).
% 3.31/0.85  fof(f36,plain,(
% 3.31/0.85    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 3.31/0.85    inference(cnf_transformation,[],[f31])).
% 3.31/0.85  % SZS output end Proof for theBenchmark
% 3.31/0.85  % (23803)------------------------------
% 3.31/0.85  % (23803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.31/0.85  % (23803)Termination reason: Refutation
% 3.31/0.85  
% 3.31/0.85  % (23803)Memory used [KB]: 7419
% 3.31/0.85  % (23803)Time elapsed: 0.400 s
% 3.31/0.85  % (23803)------------------------------
% 3.31/0.85  % (23803)------------------------------
% 3.31/0.86  % (23774)Success in time 0.488 s
%------------------------------------------------------------------------------
