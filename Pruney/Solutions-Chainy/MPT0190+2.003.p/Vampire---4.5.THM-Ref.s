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
% DateTime   : Thu Dec  3 12:34:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 183 expanded)
%              Number of leaves         :   30 (  93 expanded)
%              Depth                    :    6
%              Number of atoms          :  225 ( 386 expanded)
%              Number of equality atoms :   82 ( 161 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2341,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f35,f43,f47,f51,f55,f59,f71,f75,f79,f101,f111,f121,f162,f170,f293,f657,f1393,f1476,f2268,f2324])).

fof(f2324,plain,
    ( ~ spl4_7
    | spl4_66
    | ~ spl4_81 ),
    inference(avatar_contradiction_clause,[],[f2323])).

fof(f2323,plain,
    ( $false
    | ~ spl4_7
    | spl4_66
    | ~ spl4_81 ),
    inference(subsumption_resolution,[],[f1475,f2271])).

fof(f2271,plain,
    ( ! [X12,X10,X13,X11] : k2_enumset1(X10,X11,X12,X13) = k2_enumset1(X11,X10,X12,X13)
    | ~ spl4_7
    | ~ spl4_81 ),
    inference(superposition,[],[f2267,f54])).

fof(f54,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl4_7
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f2267,plain,
    ( ! [X14,X12,X13,X11] : k3_enumset1(X11,X11,X12,X13,X14) = k2_enumset1(X12,X11,X13,X14)
    | ~ spl4_81 ),
    inference(avatar_component_clause,[],[f2266])).

fof(f2266,plain,
    ( spl4_81
  <=> ! [X11,X13,X12,X14] : k3_enumset1(X11,X11,X12,X13,X14) = k2_enumset1(X12,X11,X13,X14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).

fof(f1475,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)
    | spl4_66 ),
    inference(avatar_component_clause,[],[f1473])).

fof(f1473,plain,
    ( spl4_66
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f2268,plain,
    ( spl4_81
    | ~ spl4_7
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f310,f291,f109,f73,f53,f2266])).

fof(f73,plain,
    ( spl4_11
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f109,plain,
    ( spl4_15
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f291,plain,
    ( spl4_27
  <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f310,plain,
    ( ! [X14,X12,X13,X11] : k3_enumset1(X11,X11,X12,X13,X14) = k2_enumset1(X12,X11,X13,X14)
    | ~ spl4_7
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f301,f150])).

fof(f150,plain,
    ( ! [X14,X12,X13,X11] : k2_xboole_0(k2_tarski(X11,X12),k2_tarski(X13,X14)) = k2_enumset1(X11,X12,X13,X14)
    | ~ spl4_7
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f144,f54])).

fof(f144,plain,
    ( ! [X14,X12,X13,X11] : k3_enumset1(X11,X11,X12,X13,X14) = k2_xboole_0(k2_tarski(X11,X12),k2_tarski(X13,X14))
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(superposition,[],[f74,f110])).

fof(f110,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f109])).

fof(f74,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f73])).

fof(f301,plain,
    ( ! [X14,X12,X13,X11] : k3_enumset1(X11,X11,X12,X13,X14) = k2_xboole_0(k2_tarski(X12,X11),k2_tarski(X13,X14))
    | ~ spl4_11
    | ~ spl4_27 ),
    inference(superposition,[],[f74,f292])).

fof(f292,plain,
    ( ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X1,X0)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f291])).

fof(f1476,plain,
    ( ~ spl4_66
    | spl4_1
    | ~ spl4_65 ),
    inference(avatar_split_clause,[],[f1432,f1391,f28,f1473])).

fof(f28,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1391,plain,
    ( spl4_65
  <=> ! [X18,X20,X17,X19] : k2_enumset1(X17,X18,X19,X20) = k2_enumset1(X17,X18,X20,X19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f1432,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)
    | spl4_1
    | ~ spl4_65 ),
    inference(superposition,[],[f30,f1392])).

fof(f1392,plain,
    ( ! [X19,X17,X20,X18] : k2_enumset1(X17,X18,X19,X20) = k2_enumset1(X17,X18,X20,X19)
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f1391])).

fof(f30,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK3,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f1393,plain,
    ( spl4_65
    | ~ spl4_14
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f663,f655,f99,f1391])).

fof(f99,plain,
    ( spl4_14
  <=> ! [X1,X3,X0,X2] : k3_enumset1(X1,X2,X3,X0,X0) = k2_enumset1(X1,X2,X3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f655,plain,
    ( spl4_44
  <=> ! [X22,X21,X23,X24] : k3_enumset1(X23,X24,X22,X21,X21) = k2_enumset1(X23,X24,X21,X22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f663,plain,
    ( ! [X19,X17,X20,X18] : k2_enumset1(X17,X18,X19,X20) = k2_enumset1(X17,X18,X20,X19)
    | ~ spl4_14
    | ~ spl4_44 ),
    inference(superposition,[],[f656,f100])).

fof(f100,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X1,X2,X3,X0,X0) = k2_enumset1(X1,X2,X3,X0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f99])).

fof(f656,plain,
    ( ! [X24,X23,X21,X22] : k3_enumset1(X23,X24,X22,X21,X21) = k2_enumset1(X23,X24,X21,X22)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f655])).

fof(f657,plain,
    ( spl4_44
    | ~ spl4_7
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f153,f119,f109,f73,f53,f655])).

fof(f119,plain,
    ( spl4_17
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X3,X4,X0,X1,X2) = k2_xboole_0(k2_tarski(X3,X4),k1_enumset1(X2,X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f153,plain,
    ( ! [X24,X23,X21,X22] : k3_enumset1(X23,X24,X22,X21,X21) = k2_enumset1(X23,X24,X21,X22)
    | ~ spl4_7
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f147,f150])).

fof(f147,plain,
    ( ! [X24,X23,X21,X22] : k3_enumset1(X23,X24,X22,X21,X21) = k2_xboole_0(k2_tarski(X23,X24),k2_tarski(X21,X22))
    | ~ spl4_15
    | ~ spl4_17 ),
    inference(superposition,[],[f120,f110])).

fof(f120,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X3,X4,X0,X1,X2) = k2_xboole_0(k2_tarski(X3,X4),k1_enumset1(X2,X1,X0))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f119])).

fof(f293,plain,
    ( spl4_27
    | ~ spl4_6
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f179,f168,f160,f49,f291])).

fof(f49,plain,
    ( spl4_6
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f160,plain,
    ( spl4_20
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f168,plain,
    ( spl4_21
  <=> ! [X1,X3,X2] : k1_enumset1(X1,X2,X3) = k2_enumset1(X1,X2,X3,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f179,plain,
    ( ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X1,X0)
    | ~ spl4_6
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f171,f161])).

fof(f161,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f160])).

fof(f171,plain,
    ( ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X0,X1,X1)
    | ~ spl4_6
    | ~ spl4_21 ),
    inference(superposition,[],[f169,f50])).

fof(f50,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f169,plain,
    ( ! [X2,X3,X1] : k1_enumset1(X1,X2,X3) = k2_enumset1(X1,X2,X3,X3)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f168])).

fof(f170,plain,
    ( spl4_21
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f106,f99,f53,f49,f168])).

fof(f106,plain,
    ( ! [X2,X3,X1] : k1_enumset1(X1,X2,X3) = k2_enumset1(X1,X2,X3,X3)
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f103,f50])).

fof(f103,plain,
    ( ! [X2,X3,X1] : k2_enumset1(X1,X2,X3,X3) = k2_enumset1(X1,X1,X2,X3)
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(superposition,[],[f100,f54])).

fof(f162,plain,
    ( spl4_20
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f138,f109,f41,f160])).

fof(f41,plain,
    ( spl4_4
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f138,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(superposition,[],[f110,f42])).

fof(f42,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f121,plain,
    ( spl4_17
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f81,f69,f41,f119])).

fof(f69,plain,
    ( spl4_10
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f81,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X3,X4,X0,X1,X2) = k2_xboole_0(k2_tarski(X3,X4),k1_enumset1(X2,X1,X0))
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(superposition,[],[f70,f42])).

fof(f70,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f69])).

fof(f111,plain,
    ( spl4_15
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f88,f77,f49,f109])).

fof(f77,plain,
    ( spl4_12
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f88,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(superposition,[],[f78,f50])).

fof(f78,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f77])).

fof(f101,plain,
    ( spl4_14
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f87,f73,f57,f33,f99])).

fof(f33,plain,
    ( spl4_2
  <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f57,plain,
    ( spl4_8
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f87,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X1,X2,X3,X0,X0) = k2_enumset1(X1,X2,X3,X0)
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f86,f58])).

fof(f58,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f86,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X1,X2,X3,X0,X0) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(superposition,[],[f74,f34])).

fof(f34,plain,
    ( ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f79,plain,
    ( spl4_12
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f60,f53,f45,f77])).

fof(f45,plain,
    ( spl4_5
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f60,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(superposition,[],[f54,f46])).

fof(f46,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f75,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f26,f73])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

fof(f71,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f25,f69])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(f59,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f23,f57])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f55,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f22,f53])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f51,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_enumset1)).

fof(f43,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f20,f41])).

fof(f20,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

fof(f35,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f17,f33])).

fof(f17,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f16,f28])).

fof(f16,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK3,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X3,X2)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK3,sK2) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X3,X2) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X3,X2) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:17:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (15729)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (15738)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (15732)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (15724)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (15731)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (15725)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (15733)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (15737)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (15730)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (15728)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (15726)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (15736)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.50  % (15727)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (15740)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (15739)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (15741)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (15734)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.52  % (15735)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.52  % (15735)Refutation not found, incomplete strategy% (15735)------------------------------
% 0.22/0.52  % (15735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15735)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (15735)Memory used [KB]: 10490
% 0.22/0.52  % (15735)Time elapsed: 0.092 s
% 0.22/0.52  % (15735)------------------------------
% 0.22/0.52  % (15735)------------------------------
% 0.22/0.54  % (15729)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f2341,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f31,f35,f43,f47,f51,f55,f59,f71,f75,f79,f101,f111,f121,f162,f170,f293,f657,f1393,f1476,f2268,f2324])).
% 0.22/0.54  fof(f2324,plain,(
% 0.22/0.54    ~spl4_7 | spl4_66 | ~spl4_81),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f2323])).
% 0.22/0.54  fof(f2323,plain,(
% 0.22/0.54    $false | (~spl4_7 | spl4_66 | ~spl4_81)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1475,f2271])).
% 0.22/0.54  fof(f2271,plain,(
% 0.22/0.54    ( ! [X12,X10,X13,X11] : (k2_enumset1(X10,X11,X12,X13) = k2_enumset1(X11,X10,X12,X13)) ) | (~spl4_7 | ~spl4_81)),
% 0.22/0.54    inference(superposition,[],[f2267,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) ) | ~spl4_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    spl4_7 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.54  fof(f2267,plain,(
% 0.22/0.54    ( ! [X14,X12,X13,X11] : (k3_enumset1(X11,X11,X12,X13,X14) = k2_enumset1(X12,X11,X13,X14)) ) | ~spl4_81),
% 0.22/0.54    inference(avatar_component_clause,[],[f2266])).
% 0.22/0.54  fof(f2266,plain,(
% 0.22/0.54    spl4_81 <=> ! [X11,X13,X12,X14] : k3_enumset1(X11,X11,X12,X13,X14) = k2_enumset1(X12,X11,X13,X14)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).
% 0.22/0.54  fof(f1475,plain,(
% 0.22/0.54    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) | spl4_66),
% 0.22/0.54    inference(avatar_component_clause,[],[f1473])).
% 0.22/0.54  fof(f1473,plain,(
% 0.22/0.54    spl4_66 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK0,sK2,sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 0.22/0.54  fof(f2268,plain,(
% 0.22/0.54    spl4_81 | ~spl4_7 | ~spl4_11 | ~spl4_15 | ~spl4_27),
% 0.22/0.54    inference(avatar_split_clause,[],[f310,f291,f109,f73,f53,f2266])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    spl4_11 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    spl4_15 <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.54  fof(f291,plain,(
% 0.22/0.54    spl4_27 <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.22/0.54  fof(f310,plain,(
% 0.22/0.54    ( ! [X14,X12,X13,X11] : (k3_enumset1(X11,X11,X12,X13,X14) = k2_enumset1(X12,X11,X13,X14)) ) | (~spl4_7 | ~spl4_11 | ~spl4_15 | ~spl4_27)),
% 0.22/0.54    inference(forward_demodulation,[],[f301,f150])).
% 0.22/0.54  fof(f150,plain,(
% 0.22/0.54    ( ! [X14,X12,X13,X11] : (k2_xboole_0(k2_tarski(X11,X12),k2_tarski(X13,X14)) = k2_enumset1(X11,X12,X13,X14)) ) | (~spl4_7 | ~spl4_11 | ~spl4_15)),
% 0.22/0.54    inference(forward_demodulation,[],[f144,f54])).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    ( ! [X14,X12,X13,X11] : (k3_enumset1(X11,X11,X12,X13,X14) = k2_xboole_0(k2_tarski(X11,X12),k2_tarski(X13,X14))) ) | (~spl4_11 | ~spl4_15)),
% 0.22/0.54    inference(superposition,[],[f74,f110])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) ) | ~spl4_15),
% 0.22/0.54    inference(avatar_component_clause,[],[f109])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) ) | ~spl4_11),
% 0.22/0.54    inference(avatar_component_clause,[],[f73])).
% 0.22/0.54  fof(f301,plain,(
% 0.22/0.54    ( ! [X14,X12,X13,X11] : (k3_enumset1(X11,X11,X12,X13,X14) = k2_xboole_0(k2_tarski(X12,X11),k2_tarski(X13,X14))) ) | (~spl4_11 | ~spl4_27)),
% 0.22/0.54    inference(superposition,[],[f74,f292])).
% 0.22/0.54  fof(f292,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X1,X0)) ) | ~spl4_27),
% 0.22/0.54    inference(avatar_component_clause,[],[f291])).
% 0.22/0.54  fof(f1476,plain,(
% 0.22/0.54    ~spl4_66 | spl4_1 | ~spl4_65),
% 0.22/0.54    inference(avatar_split_clause,[],[f1432,f1391,f28,f1473])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK0,sK3,sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.54  fof(f1391,plain,(
% 0.22/0.54    spl4_65 <=> ! [X18,X20,X17,X19] : k2_enumset1(X17,X18,X19,X20) = k2_enumset1(X17,X18,X20,X19)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 0.22/0.54  fof(f1432,plain,(
% 0.22/0.54    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) | (spl4_1 | ~spl4_65)),
% 0.22/0.54    inference(superposition,[],[f30,f1392])).
% 0.22/0.54  fof(f1392,plain,(
% 0.22/0.54    ( ! [X19,X17,X20,X18] : (k2_enumset1(X17,X18,X19,X20) = k2_enumset1(X17,X18,X20,X19)) ) | ~spl4_65),
% 0.22/0.54    inference(avatar_component_clause,[],[f1391])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK3,sK2) | spl4_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f28])).
% 0.22/0.54  fof(f1393,plain,(
% 0.22/0.54    spl4_65 | ~spl4_14 | ~spl4_44),
% 0.22/0.54    inference(avatar_split_clause,[],[f663,f655,f99,f1391])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    spl4_14 <=> ! [X1,X3,X0,X2] : k3_enumset1(X1,X2,X3,X0,X0) = k2_enumset1(X1,X2,X3,X0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.54  fof(f655,plain,(
% 0.22/0.54    spl4_44 <=> ! [X22,X21,X23,X24] : k3_enumset1(X23,X24,X22,X21,X21) = k2_enumset1(X23,X24,X21,X22)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.22/0.54  fof(f663,plain,(
% 0.22/0.54    ( ! [X19,X17,X20,X18] : (k2_enumset1(X17,X18,X19,X20) = k2_enumset1(X17,X18,X20,X19)) ) | (~spl4_14 | ~spl4_44)),
% 0.22/0.54    inference(superposition,[],[f656,f100])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X1,X2,X3,X0,X0) = k2_enumset1(X1,X2,X3,X0)) ) | ~spl4_14),
% 0.22/0.54    inference(avatar_component_clause,[],[f99])).
% 1.50/0.56  fof(f656,plain,(
% 1.50/0.56    ( ! [X24,X23,X21,X22] : (k3_enumset1(X23,X24,X22,X21,X21) = k2_enumset1(X23,X24,X21,X22)) ) | ~spl4_44),
% 1.50/0.56    inference(avatar_component_clause,[],[f655])).
% 1.50/0.56  fof(f657,plain,(
% 1.50/0.56    spl4_44 | ~spl4_7 | ~spl4_11 | ~spl4_15 | ~spl4_17),
% 1.50/0.56    inference(avatar_split_clause,[],[f153,f119,f109,f73,f53,f655])).
% 1.50/0.56  fof(f119,plain,(
% 1.50/0.56    spl4_17 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X3,X4,X0,X1,X2) = k2_xboole_0(k2_tarski(X3,X4),k1_enumset1(X2,X1,X0))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.50/0.56  fof(f153,plain,(
% 1.50/0.56    ( ! [X24,X23,X21,X22] : (k3_enumset1(X23,X24,X22,X21,X21) = k2_enumset1(X23,X24,X21,X22)) ) | (~spl4_7 | ~spl4_11 | ~spl4_15 | ~spl4_17)),
% 1.50/0.56    inference(forward_demodulation,[],[f147,f150])).
% 1.50/0.56  fof(f147,plain,(
% 1.50/0.56    ( ! [X24,X23,X21,X22] : (k3_enumset1(X23,X24,X22,X21,X21) = k2_xboole_0(k2_tarski(X23,X24),k2_tarski(X21,X22))) ) | (~spl4_15 | ~spl4_17)),
% 1.50/0.56    inference(superposition,[],[f120,f110])).
% 1.50/0.56  fof(f120,plain,(
% 1.50/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X3,X4,X0,X1,X2) = k2_xboole_0(k2_tarski(X3,X4),k1_enumset1(X2,X1,X0))) ) | ~spl4_17),
% 1.50/0.56    inference(avatar_component_clause,[],[f119])).
% 1.50/0.56  fof(f293,plain,(
% 1.50/0.56    spl4_27 | ~spl4_6 | ~spl4_20 | ~spl4_21),
% 1.50/0.56    inference(avatar_split_clause,[],[f179,f168,f160,f49,f291])).
% 1.50/0.56  fof(f49,plain,(
% 1.50/0.56    spl4_6 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.50/0.56  fof(f160,plain,(
% 1.50/0.56    spl4_20 <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.50/0.56  fof(f168,plain,(
% 1.50/0.56    spl4_21 <=> ! [X1,X3,X2] : k1_enumset1(X1,X2,X3) = k2_enumset1(X1,X2,X3,X3)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.50/0.56  fof(f179,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X1,X0)) ) | (~spl4_6 | ~spl4_20 | ~spl4_21)),
% 1.50/0.56    inference(forward_demodulation,[],[f171,f161])).
% 1.50/0.56  fof(f161,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)) ) | ~spl4_20),
% 1.50/0.56    inference(avatar_component_clause,[],[f160])).
% 1.50/0.56  fof(f171,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X0,X1,X1)) ) | (~spl4_6 | ~spl4_21)),
% 1.50/0.56    inference(superposition,[],[f169,f50])).
% 1.50/0.56  fof(f50,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) ) | ~spl4_6),
% 1.50/0.56    inference(avatar_component_clause,[],[f49])).
% 1.50/0.56  fof(f169,plain,(
% 1.50/0.56    ( ! [X2,X3,X1] : (k1_enumset1(X1,X2,X3) = k2_enumset1(X1,X2,X3,X3)) ) | ~spl4_21),
% 1.50/0.56    inference(avatar_component_clause,[],[f168])).
% 1.50/0.56  fof(f170,plain,(
% 1.50/0.56    spl4_21 | ~spl4_6 | ~spl4_7 | ~spl4_14),
% 1.50/0.56    inference(avatar_split_clause,[],[f106,f99,f53,f49,f168])).
% 1.50/0.56  fof(f106,plain,(
% 1.50/0.56    ( ! [X2,X3,X1] : (k1_enumset1(X1,X2,X3) = k2_enumset1(X1,X2,X3,X3)) ) | (~spl4_6 | ~spl4_7 | ~spl4_14)),
% 1.50/0.56    inference(forward_demodulation,[],[f103,f50])).
% 1.50/0.56  fof(f103,plain,(
% 1.50/0.56    ( ! [X2,X3,X1] : (k2_enumset1(X1,X2,X3,X3) = k2_enumset1(X1,X1,X2,X3)) ) | (~spl4_7 | ~spl4_14)),
% 1.50/0.56    inference(superposition,[],[f100,f54])).
% 1.50/0.56  fof(f162,plain,(
% 1.50/0.56    spl4_20 | ~spl4_4 | ~spl4_15),
% 1.50/0.56    inference(avatar_split_clause,[],[f138,f109,f41,f160])).
% 1.50/0.56  fof(f41,plain,(
% 1.50/0.56    spl4_4 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.50/0.56  fof(f138,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)) ) | (~spl4_4 | ~spl4_15)),
% 1.50/0.56    inference(superposition,[],[f110,f42])).
% 1.50/0.56  fof(f42,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) ) | ~spl4_4),
% 1.50/0.56    inference(avatar_component_clause,[],[f41])).
% 1.50/0.56  fof(f121,plain,(
% 1.50/0.56    spl4_17 | ~spl4_4 | ~spl4_10),
% 1.50/0.56    inference(avatar_split_clause,[],[f81,f69,f41,f119])).
% 1.50/0.56  fof(f69,plain,(
% 1.50/0.56    spl4_10 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.50/0.56  fof(f81,plain,(
% 1.50/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X3,X4,X0,X1,X2) = k2_xboole_0(k2_tarski(X3,X4),k1_enumset1(X2,X1,X0))) ) | (~spl4_4 | ~spl4_10)),
% 1.50/0.56    inference(superposition,[],[f70,f42])).
% 1.50/0.56  fof(f70,plain,(
% 1.50/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) ) | ~spl4_10),
% 1.50/0.56    inference(avatar_component_clause,[],[f69])).
% 1.50/0.56  fof(f111,plain,(
% 1.50/0.56    spl4_15 | ~spl4_6 | ~spl4_12),
% 1.50/0.56    inference(avatar_split_clause,[],[f88,f77,f49,f109])).
% 1.50/0.56  fof(f77,plain,(
% 1.50/0.56    spl4_12 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.50/0.56  fof(f88,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) ) | (~spl4_6 | ~spl4_12)),
% 1.50/0.56    inference(superposition,[],[f78,f50])).
% 1.50/0.56  fof(f78,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) ) | ~spl4_12),
% 1.50/0.56    inference(avatar_component_clause,[],[f77])).
% 1.50/0.56  fof(f101,plain,(
% 1.50/0.56    spl4_14 | ~spl4_2 | ~spl4_8 | ~spl4_11),
% 1.50/0.56    inference(avatar_split_clause,[],[f87,f73,f57,f33,f99])).
% 1.50/0.56  fof(f33,plain,(
% 1.50/0.56    spl4_2 <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.50/0.56  fof(f57,plain,(
% 1.50/0.56    spl4_8 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.50/0.56  fof(f87,plain,(
% 1.50/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X1,X2,X3,X0,X0) = k2_enumset1(X1,X2,X3,X0)) ) | (~spl4_2 | ~spl4_8 | ~spl4_11)),
% 1.50/0.56    inference(forward_demodulation,[],[f86,f58])).
% 1.50/0.56  fof(f58,plain,(
% 1.50/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) ) | ~spl4_8),
% 1.50/0.56    inference(avatar_component_clause,[],[f57])).
% 1.50/0.56  fof(f86,plain,(
% 1.50/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X1,X2,X3,X0,X0) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))) ) | (~spl4_2 | ~spl4_11)),
% 1.50/0.56    inference(superposition,[],[f74,f34])).
% 1.50/0.56  fof(f34,plain,(
% 1.50/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) ) | ~spl4_2),
% 1.50/0.56    inference(avatar_component_clause,[],[f33])).
% 1.50/0.56  fof(f79,plain,(
% 1.50/0.56    spl4_12 | ~spl4_5 | ~spl4_7),
% 1.50/0.56    inference(avatar_split_clause,[],[f60,f53,f45,f77])).
% 1.50/0.56  fof(f45,plain,(
% 1.50/0.56    spl4_5 <=> ! [X1,X0] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.50/0.56  fof(f60,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) ) | (~spl4_5 | ~spl4_7)),
% 1.50/0.56    inference(superposition,[],[f54,f46])).
% 1.50/0.56  fof(f46,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) ) | ~spl4_5),
% 1.50/0.56    inference(avatar_component_clause,[],[f45])).
% 1.50/0.56  fof(f75,plain,(
% 1.50/0.56    spl4_11),
% 1.50/0.56    inference(avatar_split_clause,[],[f26,f73])).
% 1.50/0.56  fof(f26,plain,(
% 1.50/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f2])).
% 1.50/0.56  fof(f2,axiom,(
% 1.50/0.56    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).
% 1.50/0.56  fof(f71,plain,(
% 1.50/0.56    spl4_10),
% 1.50/0.56    inference(avatar_split_clause,[],[f25,f69])).
% 1.50/0.56  fof(f25,plain,(
% 1.50/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f5])).
% 1.50/0.56  fof(f5,axiom,(
% 1.50/0.56    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 1.50/0.56  fof(f59,plain,(
% 1.50/0.56    spl4_8),
% 1.50/0.56    inference(avatar_split_clause,[],[f23,f57])).
% 1.50/0.56  fof(f23,plain,(
% 1.50/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f4])).
% 1.50/0.56  fof(f4,axiom,(
% 1.50/0.56    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 1.50/0.56  fof(f55,plain,(
% 1.50/0.56    spl4_7),
% 1.50/0.56    inference(avatar_split_clause,[],[f22,f53])).
% 1.50/0.56  fof(f22,plain,(
% 1.50/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f8])).
% 1.50/0.56  fof(f8,axiom,(
% 1.50/0.56    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.50/0.56  fof(f51,plain,(
% 1.50/0.56    spl4_6),
% 1.50/0.56    inference(avatar_split_clause,[],[f21,f49])).
% 1.50/0.56  fof(f21,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f7])).
% 1.50/0.56  fof(f7,axiom,(
% 1.50/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.50/0.56  fof(f47,plain,(
% 1.50/0.56    spl4_5),
% 1.50/0.56    inference(avatar_split_clause,[],[f19,f45])).
% 1.50/0.56  fof(f19,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f10])).
% 1.50/0.56  fof(f10,axiom,(
% 1.50/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_enumset1)).
% 1.50/0.56  fof(f43,plain,(
% 1.50/0.56    spl4_4),
% 1.50/0.56    inference(avatar_split_clause,[],[f20,f41])).
% 1.50/0.56  fof(f20,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f3])).
% 1.50/0.56  fof(f3,axiom,(
% 1.50/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).
% 1.50/0.56  fof(f35,plain,(
% 1.50/0.56    spl4_2),
% 1.50/0.56    inference(avatar_split_clause,[],[f17,f33])).
% 1.50/0.56  fof(f17,plain,(
% 1.50/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f6])).
% 1.50/0.56  fof(f6,axiom,(
% 1.50/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.50/0.56  fof(f31,plain,(
% 1.50/0.56    ~spl4_1),
% 1.50/0.56    inference(avatar_split_clause,[],[f16,f28])).
% 1.50/0.56  fof(f16,plain,(
% 1.50/0.56    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK3,sK2)),
% 1.50/0.56    inference(cnf_transformation,[],[f15])).
% 1.50/0.56  fof(f15,plain,(
% 1.50/0.56    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK3,sK2)),
% 1.50/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f14])).
% 1.50/0.56  fof(f14,plain,(
% 1.50/0.56    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X3,X2) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK3,sK2)),
% 1.50/0.56    introduced(choice_axiom,[])).
% 1.50/0.56  fof(f13,plain,(
% 1.50/0.56    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X3,X2)),
% 1.50/0.56    inference(ennf_transformation,[],[f12])).
% 1.50/0.56  fof(f12,negated_conjecture,(
% 1.50/0.56    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X3,X2)),
% 1.50/0.56    inference(negated_conjecture,[],[f11])).
% 1.50/0.56  fof(f11,conjecture,(
% 1.50/0.56    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X3,X2)),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_enumset1)).
% 1.50/0.56  % SZS output end Proof for theBenchmark
% 1.50/0.56  % (15729)------------------------------
% 1.50/0.56  % (15729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (15729)Termination reason: Refutation
% 1.50/0.56  
% 1.50/0.56  % (15729)Memory used [KB]: 7547
% 1.50/0.56  % (15729)Time elapsed: 0.124 s
% 1.50/0.56  % (15729)------------------------------
% 1.50/0.56  % (15729)------------------------------
% 1.50/0.56  % (15723)Success in time 0.196 s
%------------------------------------------------------------------------------
