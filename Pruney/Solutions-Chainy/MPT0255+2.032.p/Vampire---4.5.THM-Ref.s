%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 183 expanded)
%              Number of leaves         :   31 (  93 expanded)
%              Depth                    :    6
%              Number of atoms          :  231 ( 381 expanded)
%              Number of equality atoms :   85 ( 160 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f328,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f38,f42,f46,f50,f54,f58,f63,f77,f91,f98,f102,f117,f153,f163,f226,f233,f244,f284,f307,f325])).

fof(f325,plain,
    ( ~ spl3_4
    | ~ spl3_14
    | ~ spl3_17
    | ~ spl3_36 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_14
    | ~ spl3_17
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f320,f323])).

fof(f323,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_14
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f312,f41])).

fof(f41,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_4
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f312,plain,
    ( k3_tarski(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_14
    | ~ spl3_36 ),
    inference(superposition,[],[f90,f306])).

fof(f306,plain,
    ( k1_xboole_0 = k1_tarski(k1_xboole_0)
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl3_36
  <=> k1_xboole_0 = k1_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f90,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_14
  <=> ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f320,plain,
    ( k1_xboole_0 != k3_tarski(k1_xboole_0)
    | ~ spl3_17
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f311,f306])).

fof(f311,plain,
    ( k1_xboole_0 != k3_tarski(k1_tarski(k1_xboole_0))
    | ~ spl3_17
    | ~ spl3_36 ),
    inference(superposition,[],[f116,f306])).

fof(f116,plain,
    ( ! [X1] : k1_xboole_0 != k3_tarski(k1_tarski(k1_tarski(X1)))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_17
  <=> ! [X1] : k1_xboole_0 != k3_tarski(k1_tarski(k1_tarski(X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f307,plain,
    ( spl3_36
    | ~ spl3_5
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f285,f281,f44,f304])).

fof(f44,plain,
    ( spl3_5
  <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f281,plain,
    ( spl3_33
  <=> k1_xboole_0 = k2_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f285,plain,
    ( k1_xboole_0 = k1_tarski(k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_33 ),
    inference(superposition,[],[f283,f45])).

fof(f45,plain,
    ( ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f283,plain,
    ( k1_xboole_0 = k2_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f281])).

fof(f284,plain,
    ( spl3_33
    | ~ spl3_3
    | ~ spl3_15
    | ~ spl3_29
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f258,f241,f230,f95,f36,f281])).

fof(f36,plain,
    ( spl3_3
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f95,plain,
    ( spl3_15
  <=> k1_xboole_0 = k2_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f230,plain,
    ( spl3_29
  <=> k1_xboole_0 = k4_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f241,plain,
    ( spl3_31
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f258,plain,
    ( k1_xboole_0 = k2_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_15
    | ~ spl3_29
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f247,f234])).

fof(f234,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(superposition,[],[f232,f37])).

fof(f37,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f232,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f230])).

fof(f247,plain,
    ( k1_xboole_0 = k2_tarski(sK0,k1_xboole_0)
    | ~ spl3_15
    | ~ spl3_31 ),
    inference(superposition,[],[f97,f243])).

fof(f243,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f241])).

fof(f97,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f95])).

fof(f244,plain,
    ( spl3_31
    | ~ spl3_3
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f227,f223,f36,f241])).

fof(f223,plain,
    ( spl3_28
  <=> k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f227,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_3
    | ~ spl3_28 ),
    inference(superposition,[],[f225,f37])).

fof(f225,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f223])).

fof(f233,plain,
    ( spl3_29
    | ~ spl3_7
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f164,f160,f52,f230])).

fof(f52,plain,
    ( spl3_7
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f160,plain,
    ( spl3_22
  <=> k1_xboole_0 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f164,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_7
    | ~ spl3_22 ),
    inference(superposition,[],[f53,f162])).

fof(f162,plain,
    ( k1_xboole_0 = k2_xboole_0(sK0,sK1)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f160])).

fof(f53,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f226,plain,
    ( spl3_28
    | ~ spl3_7
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f158,f150,f52,f223])).

fof(f150,plain,
    ( spl3_21
  <=> k1_xboole_0 = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f158,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_7
    | ~ spl3_21 ),
    inference(superposition,[],[f53,f152])).

fof(f152,plain,
    ( k1_xboole_0 = k2_xboole_0(sK1,sK0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f150])).

fof(f163,plain,
    ( spl3_22
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f113,f95,f61,f31,f160])).

fof(f31,plain,
    ( spl3_2
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f61,plain,
    ( spl3_9
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f113,plain,
    ( k1_xboole_0 = k2_xboole_0(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f111,f33])).

fof(f33,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f111,plain,
    ( k3_tarski(k1_xboole_0) = k2_xboole_0(sK0,sK1)
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(superposition,[],[f62,f97])).

fof(f62,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f153,plain,
    ( spl3_21
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f112,f100,f95,f31,f150])).

fof(f100,plain,
    ( spl3_16
  <=> ! [X1,X2] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f112,plain,
    ( k1_xboole_0 = k2_xboole_0(sK1,sK0)
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f110,f33])).

fof(f110,plain,
    ( k3_tarski(k1_xboole_0) = k2_xboole_0(sK1,sK0)
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(superposition,[],[f101,f97])).

fof(f101,plain,
    ( ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f100])).

fof(f117,plain,
    ( spl3_17
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f93,f89,f48,f115])).

fof(f48,plain,
    ( spl3_6
  <=> ! [X1,X0] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f93,plain,
    ( ! [X1] : k1_xboole_0 != k3_tarski(k1_tarski(k1_tarski(X1)))
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(superposition,[],[f49,f90])).

fof(f49,plain,
    ( ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f102,plain,
    ( spl3_16
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f71,f61,f56,f100])).

fof(f56,plain,
    ( spl3_8
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f71,plain,
    ( ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(superposition,[],[f62,f57])).

fof(f57,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f56])).

fof(f98,plain,
    ( spl3_15
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f78,f74,f36,f95])).

fof(f74,plain,
    ( spl3_11
  <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f78,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(superposition,[],[f76,f37])).

fof(f76,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f91,plain,
    ( spl3_14
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f70,f61,f44,f89])).

fof(f70,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(superposition,[],[f62,f45])).

fof(f77,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f68,f52,f26,f74])).

fof(f26,plain,
    ( spl3_1
  <=> k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f68,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(superposition,[],[f53,f28])).

fof(f28,plain,
    ( k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f63,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f23,f61])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f58,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f22,f56])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f54,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f21,f52])).

fof(f21,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f50,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f20,f48])).

fof(f20,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f46,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f19,f44])).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f38,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f17,f36])).

fof(f17,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f34,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f31])).

fof(f16,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f29,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f15,f26])).

fof(f15,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:37:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (3326)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.43  % (3326)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f328,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f29,f34,f38,f42,f46,f50,f54,f58,f63,f77,f91,f98,f102,f117,f153,f163,f226,f233,f244,f284,f307,f325])).
% 0.22/0.43  fof(f325,plain,(
% 0.22/0.43    ~spl3_4 | ~spl3_14 | ~spl3_17 | ~spl3_36),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f324])).
% 0.22/0.43  fof(f324,plain,(
% 0.22/0.43    $false | (~spl3_4 | ~spl3_14 | ~spl3_17 | ~spl3_36)),
% 0.22/0.43    inference(subsumption_resolution,[],[f320,f323])).
% 0.22/0.43  fof(f323,plain,(
% 0.22/0.43    k1_xboole_0 = k3_tarski(k1_xboole_0) | (~spl3_4 | ~spl3_14 | ~spl3_36)),
% 0.22/0.43    inference(forward_demodulation,[],[f312,f41])).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f40])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    spl3_4 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.43  fof(f312,plain,(
% 0.22/0.43    k3_tarski(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl3_14 | ~spl3_36)),
% 0.22/0.43    inference(superposition,[],[f90,f306])).
% 0.22/0.43  fof(f306,plain,(
% 0.22/0.43    k1_xboole_0 = k1_tarski(k1_xboole_0) | ~spl3_36),
% 0.22/0.43    inference(avatar_component_clause,[],[f304])).
% 0.22/0.43  fof(f304,plain,(
% 0.22/0.43    spl3_36 <=> k1_xboole_0 = k1_tarski(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.43  fof(f90,plain,(
% 0.22/0.43    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))) ) | ~spl3_14),
% 0.22/0.43    inference(avatar_component_clause,[],[f89])).
% 0.22/0.43  fof(f89,plain,(
% 0.22/0.43    spl3_14 <=> ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.43  fof(f320,plain,(
% 0.22/0.43    k1_xboole_0 != k3_tarski(k1_xboole_0) | (~spl3_17 | ~spl3_36)),
% 0.22/0.43    inference(forward_demodulation,[],[f311,f306])).
% 0.22/0.43  fof(f311,plain,(
% 0.22/0.43    k1_xboole_0 != k3_tarski(k1_tarski(k1_xboole_0)) | (~spl3_17 | ~spl3_36)),
% 0.22/0.43    inference(superposition,[],[f116,f306])).
% 0.22/0.43  fof(f116,plain,(
% 0.22/0.43    ( ! [X1] : (k1_xboole_0 != k3_tarski(k1_tarski(k1_tarski(X1)))) ) | ~spl3_17),
% 0.22/0.43    inference(avatar_component_clause,[],[f115])).
% 0.22/0.43  fof(f115,plain,(
% 0.22/0.43    spl3_17 <=> ! [X1] : k1_xboole_0 != k3_tarski(k1_tarski(k1_tarski(X1)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.43  fof(f307,plain,(
% 0.22/0.43    spl3_36 | ~spl3_5 | ~spl3_33),
% 0.22/0.43    inference(avatar_split_clause,[],[f285,f281,f44,f304])).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    spl3_5 <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.43  fof(f281,plain,(
% 0.22/0.43    spl3_33 <=> k1_xboole_0 = k2_tarski(k1_xboole_0,k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.43  fof(f285,plain,(
% 0.22/0.43    k1_xboole_0 = k1_tarski(k1_xboole_0) | (~spl3_5 | ~spl3_33)),
% 0.22/0.43    inference(superposition,[],[f283,f45])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) ) | ~spl3_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f44])).
% 0.22/0.43  fof(f283,plain,(
% 0.22/0.43    k1_xboole_0 = k2_tarski(k1_xboole_0,k1_xboole_0) | ~spl3_33),
% 0.22/0.43    inference(avatar_component_clause,[],[f281])).
% 0.22/0.43  fof(f284,plain,(
% 0.22/0.43    spl3_33 | ~spl3_3 | ~spl3_15 | ~spl3_29 | ~spl3_31),
% 0.22/0.43    inference(avatar_split_clause,[],[f258,f241,f230,f95,f36,f281])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    spl3_3 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.43  fof(f95,plain,(
% 0.22/0.43    spl3_15 <=> k1_xboole_0 = k2_tarski(sK0,sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.43  fof(f230,plain,(
% 0.22/0.43    spl3_29 <=> k1_xboole_0 = k4_xboole_0(sK0,k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.43  fof(f241,plain,(
% 0.22/0.43    spl3_31 <=> k1_xboole_0 = sK1),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.22/0.43  fof(f258,plain,(
% 0.22/0.43    k1_xboole_0 = k2_tarski(k1_xboole_0,k1_xboole_0) | (~spl3_3 | ~spl3_15 | ~spl3_29 | ~spl3_31)),
% 0.22/0.43    inference(forward_demodulation,[],[f247,f234])).
% 0.22/0.43  fof(f234,plain,(
% 0.22/0.43    k1_xboole_0 = sK0 | (~spl3_3 | ~spl3_29)),
% 0.22/0.43    inference(superposition,[],[f232,f37])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f36])).
% 0.22/0.43  fof(f232,plain,(
% 0.22/0.43    k1_xboole_0 = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_29),
% 0.22/0.43    inference(avatar_component_clause,[],[f230])).
% 0.22/0.43  fof(f247,plain,(
% 0.22/0.43    k1_xboole_0 = k2_tarski(sK0,k1_xboole_0) | (~spl3_15 | ~spl3_31)),
% 0.22/0.43    inference(superposition,[],[f97,f243])).
% 0.22/0.43  fof(f243,plain,(
% 0.22/0.43    k1_xboole_0 = sK1 | ~spl3_31),
% 0.22/0.43    inference(avatar_component_clause,[],[f241])).
% 0.22/0.43  fof(f97,plain,(
% 0.22/0.43    k1_xboole_0 = k2_tarski(sK0,sK1) | ~spl3_15),
% 0.22/0.43    inference(avatar_component_clause,[],[f95])).
% 0.22/0.43  fof(f244,plain,(
% 0.22/0.43    spl3_31 | ~spl3_3 | ~spl3_28),
% 0.22/0.43    inference(avatar_split_clause,[],[f227,f223,f36,f241])).
% 0.22/0.43  fof(f223,plain,(
% 0.22/0.43    spl3_28 <=> k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.43  fof(f227,plain,(
% 0.22/0.43    k1_xboole_0 = sK1 | (~spl3_3 | ~spl3_28)),
% 0.22/0.43    inference(superposition,[],[f225,f37])).
% 0.22/0.43  fof(f225,plain,(
% 0.22/0.43    k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0) | ~spl3_28),
% 0.22/0.43    inference(avatar_component_clause,[],[f223])).
% 0.22/0.43  fof(f233,plain,(
% 0.22/0.43    spl3_29 | ~spl3_7 | ~spl3_22),
% 0.22/0.43    inference(avatar_split_clause,[],[f164,f160,f52,f230])).
% 0.22/0.43  fof(f52,plain,(
% 0.22/0.43    spl3_7 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.43  fof(f160,plain,(
% 0.22/0.43    spl3_22 <=> k1_xboole_0 = k2_xboole_0(sK0,sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.43  fof(f164,plain,(
% 0.22/0.43    k1_xboole_0 = k4_xboole_0(sK0,k1_xboole_0) | (~spl3_7 | ~spl3_22)),
% 0.22/0.43    inference(superposition,[],[f53,f162])).
% 0.22/0.43  fof(f162,plain,(
% 0.22/0.43    k1_xboole_0 = k2_xboole_0(sK0,sK1) | ~spl3_22),
% 0.22/0.43    inference(avatar_component_clause,[],[f160])).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) ) | ~spl3_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f52])).
% 0.22/0.43  fof(f226,plain,(
% 0.22/0.43    spl3_28 | ~spl3_7 | ~spl3_21),
% 0.22/0.43    inference(avatar_split_clause,[],[f158,f150,f52,f223])).
% 0.22/0.43  fof(f150,plain,(
% 0.22/0.43    spl3_21 <=> k1_xboole_0 = k2_xboole_0(sK1,sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.43  fof(f158,plain,(
% 0.22/0.43    k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0) | (~spl3_7 | ~spl3_21)),
% 0.22/0.43    inference(superposition,[],[f53,f152])).
% 0.22/0.43  fof(f152,plain,(
% 0.22/0.43    k1_xboole_0 = k2_xboole_0(sK1,sK0) | ~spl3_21),
% 0.22/0.43    inference(avatar_component_clause,[],[f150])).
% 0.22/0.43  fof(f163,plain,(
% 0.22/0.43    spl3_22 | ~spl3_2 | ~spl3_9 | ~spl3_15),
% 0.22/0.43    inference(avatar_split_clause,[],[f113,f95,f61,f31,f160])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    spl3_2 <=> k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.43  fof(f61,plain,(
% 0.22/0.43    spl3_9 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.43  fof(f113,plain,(
% 0.22/0.43    k1_xboole_0 = k2_xboole_0(sK0,sK1) | (~spl3_2 | ~spl3_9 | ~spl3_15)),
% 0.22/0.43    inference(forward_demodulation,[],[f111,f33])).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    k1_xboole_0 = k3_tarski(k1_xboole_0) | ~spl3_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f31])).
% 0.22/0.43  fof(f111,plain,(
% 0.22/0.43    k3_tarski(k1_xboole_0) = k2_xboole_0(sK0,sK1) | (~spl3_9 | ~spl3_15)),
% 0.22/0.43    inference(superposition,[],[f62,f97])).
% 0.22/0.43  fof(f62,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) ) | ~spl3_9),
% 0.22/0.43    inference(avatar_component_clause,[],[f61])).
% 0.22/0.43  fof(f153,plain,(
% 0.22/0.43    spl3_21 | ~spl3_2 | ~spl3_15 | ~spl3_16),
% 0.22/0.43    inference(avatar_split_clause,[],[f112,f100,f95,f31,f150])).
% 0.22/0.43  fof(f100,plain,(
% 0.22/0.43    spl3_16 <=> ! [X1,X2] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.43  fof(f112,plain,(
% 0.22/0.43    k1_xboole_0 = k2_xboole_0(sK1,sK0) | (~spl3_2 | ~spl3_15 | ~spl3_16)),
% 0.22/0.43    inference(forward_demodulation,[],[f110,f33])).
% 0.22/0.43  fof(f110,plain,(
% 0.22/0.43    k3_tarski(k1_xboole_0) = k2_xboole_0(sK1,sK0) | (~spl3_15 | ~spl3_16)),
% 0.22/0.43    inference(superposition,[],[f101,f97])).
% 0.22/0.43  fof(f101,plain,(
% 0.22/0.43    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) ) | ~spl3_16),
% 0.22/0.43    inference(avatar_component_clause,[],[f100])).
% 0.22/0.43  fof(f117,plain,(
% 0.22/0.43    spl3_17 | ~spl3_6 | ~spl3_14),
% 0.22/0.43    inference(avatar_split_clause,[],[f93,f89,f48,f115])).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    spl3_6 <=> ! [X1,X0] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.43  fof(f93,plain,(
% 0.22/0.43    ( ! [X1] : (k1_xboole_0 != k3_tarski(k1_tarski(k1_tarski(X1)))) ) | (~spl3_6 | ~spl3_14)),
% 0.22/0.43    inference(superposition,[],[f49,f90])).
% 0.22/0.43  fof(f49,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) ) | ~spl3_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f48])).
% 0.22/0.43  fof(f102,plain,(
% 0.22/0.43    spl3_16 | ~spl3_8 | ~spl3_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f71,f61,f56,f100])).
% 0.22/0.43  fof(f56,plain,(
% 0.22/0.43    spl3_8 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.43  fof(f71,plain,(
% 0.22/0.43    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) ) | (~spl3_8 | ~spl3_9)),
% 0.22/0.43    inference(superposition,[],[f62,f57])).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl3_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f56])).
% 0.22/0.43  fof(f98,plain,(
% 0.22/0.43    spl3_15 | ~spl3_3 | ~spl3_11),
% 0.22/0.43    inference(avatar_split_clause,[],[f78,f74,f36,f95])).
% 0.22/0.43  fof(f74,plain,(
% 0.22/0.43    spl3_11 <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.43  fof(f78,plain,(
% 0.22/0.43    k1_xboole_0 = k2_tarski(sK0,sK1) | (~spl3_3 | ~spl3_11)),
% 0.22/0.43    inference(superposition,[],[f76,f37])).
% 0.22/0.43  fof(f76,plain,(
% 0.22/0.43    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) | ~spl3_11),
% 0.22/0.43    inference(avatar_component_clause,[],[f74])).
% 0.22/0.43  fof(f91,plain,(
% 0.22/0.43    spl3_14 | ~spl3_5 | ~spl3_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f70,f61,f44,f89])).
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))) ) | (~spl3_5 | ~spl3_9)),
% 0.22/0.43    inference(superposition,[],[f62,f45])).
% 0.22/0.43  fof(f77,plain,(
% 0.22/0.43    spl3_11 | ~spl3_1 | ~spl3_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f68,f52,f26,f74])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    spl3_1 <=> k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.43  fof(f68,plain,(
% 0.22/0.43    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) | (~spl3_1 | ~spl3_7)),
% 0.22/0.43    inference(superposition,[],[f53,f28])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl3_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f26])).
% 0.22/0.43  fof(f63,plain,(
% 0.22/0.43    spl3_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f23,f61])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,axiom,(
% 0.22/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    spl3_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f22,f56])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.43  fof(f54,plain,(
% 0.22/0.43    spl3_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f21,f52])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    spl3_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f20,f48])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,axiom,(
% 0.22/0.43    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    spl3_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f19,f44])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    spl3_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f18,f40])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    spl3_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f17,f36])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    spl3_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f16,f31])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,axiom,(
% 0.22/0.43    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    spl3_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f15,f26])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.22/0.43    inference(cnf_transformation,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.22/0.43    inference(ennf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.22/0.43    inference(negated_conjecture,[],[f10])).
% 0.22/0.43  fof(f10,conjecture,(
% 0.22/0.43    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (3326)------------------------------
% 0.22/0.43  % (3326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (3326)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (3326)Memory used [KB]: 6268
% 0.22/0.43  % (3326)Time elapsed: 0.029 s
% 0.22/0.43  % (3326)------------------------------
% 0.22/0.43  % (3326)------------------------------
% 0.22/0.43  % (3316)Success in time 0.065 s
%------------------------------------------------------------------------------
