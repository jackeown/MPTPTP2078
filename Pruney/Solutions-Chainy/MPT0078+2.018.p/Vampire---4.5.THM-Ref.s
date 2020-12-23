%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 244 expanded)
%              Number of leaves         :   26 ( 105 expanded)
%              Depth                    :    9
%              Number of atoms          :  264 ( 506 expanded)
%              Number of equality atoms :   95 ( 230 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f552,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f40,f47,f52,f61,f78,f83,f93,f98,f113,f118,f177,f213,f227,f378,f529,f549])).

fof(f549,plain,
    ( spl3_3
    | ~ spl3_16
    | ~ spl3_29
    | ~ spl3_31 ),
    inference(avatar_contradiction_clause,[],[f548])).

fof(f548,plain,
    ( $false
    | spl3_3
    | ~ spl3_16
    | ~ spl3_29
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f547,f39])).

fof(f39,plain,
    ( sK0 != sK2
    | spl3_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_3
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f547,plain,
    ( sK0 = sK2
    | ~ spl3_16
    | ~ spl3_29
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f546,f176])).

fof(f176,plain,
    ( sK0 = k2_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl3_16
  <=> sK0 = k2_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f546,plain,
    ( sK2 = k2_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_29
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f540,f377])).

fof(f377,plain,
    ( sK2 = k2_xboole_0(sK0,sK2)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl3_29
  <=> sK2 = k2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f540,plain,
    ( k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK2)
    | ~ spl3_31 ),
    inference(superposition,[],[f20,f528])).

fof(f528,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK0)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f526])).

fof(f526,plain,
    ( spl3_31
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f529,plain,
    ( spl3_31
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f367,f115,f90,f44,f526])).

fof(f44,plain,
    ( spl3_4
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f90,plain,
    ( spl3_10
  <=> sK2 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f115,plain,
    ( spl3_13
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f367,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK0)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f366,f117])).

fof(f117,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f115])).

fof(f366,plain,
    ( k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,sK0)
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f357,f150])).

fof(f150,plain,
    ( ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k2_xboole_0(X0,sK1))
    | ~ spl3_10 ),
    inference(superposition,[],[f104,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f104,plain,
    ( ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK2,X0)
    | ~ spl3_10 ),
    inference(superposition,[],[f25,f92])).

fof(f92,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f90])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f357,plain,
    ( k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(superposition,[],[f150,f46])).

fof(f46,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f378,plain,
    ( spl3_29
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_13
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f277,f224,f210,f115,f95,f44,f375])).

fof(f95,plain,
    ( spl3_11
  <=> sK2 = k2_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f210,plain,
    ( spl3_20
  <=> k4_xboole_0(sK0,sK2) = k4_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f224,plain,
    ( spl3_23
  <=> k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f277,plain,
    ( sK2 = k2_xboole_0(sK0,sK2)
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_13
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f276,f97])).

fof(f97,plain,
    ( sK2 = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f95])).

fof(f276,plain,
    ( k2_xboole_0(k1_xboole_0,sK2) = k2_xboole_0(sK0,sK2)
    | ~ spl3_4
    | ~ spl3_13
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f272,f18])).

fof(f272,plain,
    ( k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK0,sK2)
    | ~ spl3_4
    | ~ spl3_13
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(backward_demodulation,[],[f233,f270])).

fof(f270,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)
    | ~ spl3_4
    | ~ spl3_13
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f260,f226])).

fof(f226,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f224])).

fof(f260,plain,
    ( k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(superposition,[],[f127,f46])).

fof(f127,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(sK2,X0))
    | ~ spl3_13 ),
    inference(superposition,[],[f25,f117])).

fof(f233,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(k1_xboole_0,sK1)) = k2_xboole_0(sK0,sK2)
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f230,f18])).

fof(f230,plain,
    ( k2_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k4_xboole_0(k1_xboole_0,sK1))
    | ~ spl3_20 ),
    inference(superposition,[],[f20,f212])).

fof(f212,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(k1_xboole_0,sK1)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f210])).

fof(f227,plain,
    ( spl3_23
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f157,f115,f90,f80,f224])).

fof(f80,plain,
    ( spl3_8
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f157,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f149,f117])).

fof(f149,plain,
    ( k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(superposition,[],[f104,f82])).

fof(f82,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f213,plain,
    ( spl3_20
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f143,f110,f80,f75,f210])).

fof(f75,plain,
    ( spl3_7
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f110,plain,
    ( spl3_12
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f143,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(k1_xboole_0,sK1)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f135,f119])).

fof(f119,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK0,X0)) = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl3_12 ),
    inference(superposition,[],[f25,f112])).

fof(f112,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f110])).

fof(f135,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(superposition,[],[f99,f82])).

fof(f99,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)
    | ~ spl3_7 ),
    inference(superposition,[],[f25,f77])).

fof(f77,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f177,plain,
    ( spl3_16
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f126,f110,f174])).

fof(f126,plain,
    ( sK0 = k2_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f120,f125])).

fof(f125,plain,
    ( sK0 = k3_xboole_0(sK0,sK0)
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f122,f17])).

fof(f17,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f122,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK0)
    | ~ spl3_12 ),
    inference(superposition,[],[f19,f112])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f120,plain,
    ( sK0 = k2_xboole_0(k3_xboole_0(sK0,sK0),k1_xboole_0)
    | ~ spl3_12 ),
    inference(superposition,[],[f22,f112])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f118,plain,
    ( spl3_13
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f108,f90,f58,f115])).

fof(f58,plain,
    ( spl3_6
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f108,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK2)
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f106,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f106,plain,
    ( k3_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2)
    | ~ spl3_10 ),
    inference(superposition,[],[f19,f92])).

fof(f113,plain,
    ( spl3_12
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f103,f75,f49,f110])).

fof(f49,plain,
    ( spl3_5
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f103,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f101,f51])).

fof(f51,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f101,plain,
    ( k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK0)
    | ~ spl3_7 ),
    inference(superposition,[],[f19,f77])).

fof(f98,plain,
    ( spl3_11
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f73,f58,f95])).

fof(f73,plain,
    ( sK2 = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f69,f72])).

fof(f72,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f70,f17])).

fof(f70,plain,
    ( k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,k1_xboole_0)
    | ~ spl3_6 ),
    inference(superposition,[],[f21,f60])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f69,plain,
    ( sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1))
    | ~ spl3_6 ),
    inference(superposition,[],[f22,f60])).

fof(f93,plain,
    ( spl3_10
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f72,f58,f90])).

fof(f83,plain,
    ( spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f53,f44,f80])).

fof(f53,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2)
    | ~ spl3_4 ),
    inference(superposition,[],[f46,f18])).

fof(f78,plain,
    ( spl3_7
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f66,f49,f75])).

fof(f66,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f64,f17])).

fof(f64,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_5 ),
    inference(superposition,[],[f21,f51])).

fof(f61,plain,
    ( spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f42,f32,f58])).

fof(f32,plain,
    ( spl3_2
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f42,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f34,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f34,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f52,plain,
    ( spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f41,f27,f49])).

fof(f27,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f41,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f29,f24])).

fof(f29,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f47,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f13,f44])).

fof(f13,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f40,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f16,f37])).

fof(f16,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f15,f32])).

fof(f15,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f30,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f14,f27])).

fof(f14,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:18:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (410)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (399)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (427)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (418)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (403)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (398)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (400)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (426)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (407)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (402)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (413)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (413)Refutation not found, incomplete strategy% (413)------------------------------
% 0.21/0.55  % (413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (413)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (413)Memory used [KB]: 6140
% 0.21/0.55  % (413)Time elapsed: 0.001 s
% 0.21/0.55  % (413)------------------------------
% 0.21/0.55  % (413)------------------------------
% 0.21/0.55  % (422)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (428)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (412)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (408)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (420)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (408)Refutation not found, incomplete strategy% (408)------------------------------
% 0.21/0.55  % (408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (408)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (408)Memory used [KB]: 10618
% 0.21/0.55  % (408)Time elapsed: 0.130 s
% 0.21/0.55  % (408)------------------------------
% 0.21/0.55  % (408)------------------------------
% 0.21/0.55  % (405)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (417)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (401)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (423)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (404)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (418)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (414)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (419)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (421)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (420)Refutation not found, incomplete strategy% (420)------------------------------
% 0.21/0.56  % (420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (420)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (420)Memory used [KB]: 10618
% 0.21/0.56  % (420)Time elapsed: 0.066 s
% 0.21/0.56  % (420)------------------------------
% 0.21/0.56  % (420)------------------------------
% 0.21/0.56  % (415)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (409)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (411)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (415)Refutation not found, incomplete strategy% (415)------------------------------
% 0.21/0.56  % (415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (415)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (415)Memory used [KB]: 10618
% 0.21/0.56  % (415)Time elapsed: 0.149 s
% 0.21/0.56  % (415)------------------------------
% 0.21/0.56  % (415)------------------------------
% 0.21/0.56  % (424)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (406)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f552,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f30,f35,f40,f47,f52,f61,f78,f83,f93,f98,f113,f118,f177,f213,f227,f378,f529,f549])).
% 0.21/0.57  fof(f549,plain,(
% 0.21/0.57    spl3_3 | ~spl3_16 | ~spl3_29 | ~spl3_31),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f548])).
% 0.21/0.57  fof(f548,plain,(
% 0.21/0.57    $false | (spl3_3 | ~spl3_16 | ~spl3_29 | ~spl3_31)),
% 0.21/0.57    inference(subsumption_resolution,[],[f547,f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    sK0 != sK2 | spl3_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    spl3_3 <=> sK0 = sK2),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.57  fof(f547,plain,(
% 0.21/0.57    sK0 = sK2 | (~spl3_16 | ~spl3_29 | ~spl3_31)),
% 0.21/0.57    inference(forward_demodulation,[],[f546,f176])).
% 0.21/0.57  fof(f176,plain,(
% 0.21/0.57    sK0 = k2_xboole_0(sK0,k1_xboole_0) | ~spl3_16),
% 0.21/0.57    inference(avatar_component_clause,[],[f174])).
% 0.21/0.57  fof(f174,plain,(
% 0.21/0.57    spl3_16 <=> sK0 = k2_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.57  fof(f546,plain,(
% 0.21/0.57    sK2 = k2_xboole_0(sK0,k1_xboole_0) | (~spl3_29 | ~spl3_31)),
% 0.21/0.57    inference(forward_demodulation,[],[f540,f377])).
% 0.21/0.57  fof(f377,plain,(
% 0.21/0.57    sK2 = k2_xboole_0(sK0,sK2) | ~spl3_29),
% 0.21/0.57    inference(avatar_component_clause,[],[f375])).
% 0.21/0.57  fof(f375,plain,(
% 0.21/0.57    spl3_29 <=> sK2 = k2_xboole_0(sK0,sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.57  fof(f540,plain,(
% 0.21/0.57    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK2) | ~spl3_31),
% 0.21/0.57    inference(superposition,[],[f20,f528])).
% 0.21/0.57  fof(f528,plain,(
% 0.21/0.57    k1_xboole_0 = k4_xboole_0(sK2,sK0) | ~spl3_31),
% 0.21/0.57    inference(avatar_component_clause,[],[f526])).
% 0.21/0.57  fof(f526,plain,(
% 0.21/0.57    spl3_31 <=> k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.57  fof(f529,plain,(
% 0.21/0.57    spl3_31 | ~spl3_4 | ~spl3_10 | ~spl3_13),
% 0.21/0.57    inference(avatar_split_clause,[],[f367,f115,f90,f44,f526])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    spl3_4 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.57  fof(f90,plain,(
% 0.21/0.57    spl3_10 <=> sK2 = k4_xboole_0(sK2,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.57  fof(f115,plain,(
% 0.21/0.57    spl3_13 <=> k1_xboole_0 = k4_xboole_0(sK2,sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.57  fof(f367,plain,(
% 0.21/0.57    k1_xboole_0 = k4_xboole_0(sK2,sK0) | (~spl3_4 | ~spl3_10 | ~spl3_13)),
% 0.21/0.57    inference(forward_demodulation,[],[f366,f117])).
% 0.21/0.57  fof(f117,plain,(
% 0.21/0.57    k1_xboole_0 = k4_xboole_0(sK2,sK2) | ~spl3_13),
% 0.21/0.57    inference(avatar_component_clause,[],[f115])).
% 0.21/0.57  fof(f366,plain,(
% 0.21/0.57    k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,sK0) | (~spl3_4 | ~spl3_10)),
% 0.21/0.57    inference(forward_demodulation,[],[f357,f150])).
% 0.21/0.57  fof(f150,plain,(
% 0.21/0.57    ( ! [X0] : (k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k2_xboole_0(X0,sK1))) ) | ~spl3_10),
% 0.21/0.57    inference(superposition,[],[f104,f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.57  fof(f104,plain,(
% 0.21/0.57    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK2,X0)) ) | ~spl3_10),
% 0.21/0.57    inference(superposition,[],[f25,f92])).
% 0.21/0.57  fof(f92,plain,(
% 0.21/0.57    sK2 = k4_xboole_0(sK2,sK1) | ~spl3_10),
% 0.21/0.57    inference(avatar_component_clause,[],[f90])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.57  fof(f357,plain,(
% 0.21/0.57    k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | (~spl3_4 | ~spl3_10)),
% 0.21/0.57    inference(superposition,[],[f150,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) | ~spl3_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f44])).
% 0.21/0.57  fof(f378,plain,(
% 0.21/0.57    spl3_29 | ~spl3_4 | ~spl3_11 | ~spl3_13 | ~spl3_20 | ~spl3_23),
% 0.21/0.57    inference(avatar_split_clause,[],[f277,f224,f210,f115,f95,f44,f375])).
% 0.21/0.57  fof(f95,plain,(
% 0.21/0.57    spl3_11 <=> sK2 = k2_xboole_0(k1_xboole_0,sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.57  fof(f210,plain,(
% 0.21/0.57    spl3_20 <=> k4_xboole_0(sK0,sK2) = k4_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.57  fof(f224,plain,(
% 0.21/0.57    spl3_23 <=> k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.57  fof(f277,plain,(
% 0.21/0.57    sK2 = k2_xboole_0(sK0,sK2) | (~spl3_4 | ~spl3_11 | ~spl3_13 | ~spl3_20 | ~spl3_23)),
% 0.21/0.57    inference(forward_demodulation,[],[f276,f97])).
% 0.21/0.57  fof(f97,plain,(
% 0.21/0.57    sK2 = k2_xboole_0(k1_xboole_0,sK2) | ~spl3_11),
% 0.21/0.57    inference(avatar_component_clause,[],[f95])).
% 0.21/0.57  fof(f276,plain,(
% 0.21/0.57    k2_xboole_0(k1_xboole_0,sK2) = k2_xboole_0(sK0,sK2) | (~spl3_4 | ~spl3_13 | ~spl3_20 | ~spl3_23)),
% 0.21/0.57    inference(forward_demodulation,[],[f272,f18])).
% 0.21/0.57  fof(f272,plain,(
% 0.21/0.57    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK0,sK2) | (~spl3_4 | ~spl3_13 | ~spl3_20 | ~spl3_23)),
% 0.21/0.57    inference(backward_demodulation,[],[f233,f270])).
% 0.21/0.57  fof(f270,plain,(
% 0.21/0.57    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) | (~spl3_4 | ~spl3_13 | ~spl3_23)),
% 0.21/0.57    inference(forward_demodulation,[],[f260,f226])).
% 0.21/0.57  fof(f226,plain,(
% 0.21/0.57    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | ~spl3_23),
% 0.21/0.57    inference(avatar_component_clause,[],[f224])).
% 0.21/0.57  fof(f260,plain,(
% 0.21/0.57    k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | (~spl3_4 | ~spl3_13)),
% 0.21/0.57    inference(superposition,[],[f127,f46])).
% 0.21/0.57  fof(f127,plain,(
% 0.21/0.57    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(sK2,X0))) ) | ~spl3_13),
% 0.21/0.57    inference(superposition,[],[f25,f117])).
% 0.21/0.57  fof(f233,plain,(
% 0.21/0.57    k2_xboole_0(sK2,k4_xboole_0(k1_xboole_0,sK1)) = k2_xboole_0(sK0,sK2) | ~spl3_20),
% 0.21/0.57    inference(forward_demodulation,[],[f230,f18])).
% 0.21/0.57  fof(f230,plain,(
% 0.21/0.57    k2_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k4_xboole_0(k1_xboole_0,sK1)) | ~spl3_20),
% 0.21/0.57    inference(superposition,[],[f20,f212])).
% 0.21/0.57  fof(f212,plain,(
% 0.21/0.57    k4_xboole_0(sK0,sK2) = k4_xboole_0(k1_xboole_0,sK1) | ~spl3_20),
% 0.21/0.57    inference(avatar_component_clause,[],[f210])).
% 0.21/0.57  fof(f227,plain,(
% 0.21/0.57    spl3_23 | ~spl3_8 | ~spl3_10 | ~spl3_13),
% 0.21/0.57    inference(avatar_split_clause,[],[f157,f115,f90,f80,f224])).
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    spl3_8 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.57  fof(f157,plain,(
% 0.21/0.57    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | (~spl3_8 | ~spl3_10 | ~spl3_13)),
% 0.21/0.57    inference(forward_demodulation,[],[f149,f117])).
% 0.21/0.57  fof(f149,plain,(
% 0.21/0.57    k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | (~spl3_8 | ~spl3_10)),
% 0.21/0.57    inference(superposition,[],[f104,f82])).
% 0.21/0.57  fof(f82,plain,(
% 0.21/0.57    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2) | ~spl3_8),
% 0.21/0.57    inference(avatar_component_clause,[],[f80])).
% 0.21/0.57  fof(f213,plain,(
% 0.21/0.57    spl3_20 | ~spl3_7 | ~spl3_8 | ~spl3_12),
% 0.21/0.57    inference(avatar_split_clause,[],[f143,f110,f80,f75,f210])).
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    spl3_7 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.57  fof(f110,plain,(
% 0.21/0.57    spl3_12 <=> k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.57  fof(f143,plain,(
% 0.21/0.57    k4_xboole_0(sK0,sK2) = k4_xboole_0(k1_xboole_0,sK1) | (~spl3_7 | ~spl3_8 | ~spl3_12)),
% 0.21/0.57    inference(forward_demodulation,[],[f135,f119])).
% 0.21/0.57  fof(f119,plain,(
% 0.21/0.57    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK0,X0)) = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl3_12),
% 0.21/0.57    inference(superposition,[],[f25,f112])).
% 0.21/0.57  fof(f112,plain,(
% 0.21/0.57    k1_xboole_0 = k4_xboole_0(sK0,sK0) | ~spl3_12),
% 0.21/0.57    inference(avatar_component_clause,[],[f110])).
% 0.21/0.57  fof(f135,plain,(
% 0.21/0.57    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) | (~spl3_7 | ~spl3_8)),
% 0.21/0.57    inference(superposition,[],[f99,f82])).
% 0.21/0.57  fof(f99,plain,(
% 0.21/0.57    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)) ) | ~spl3_7),
% 0.21/0.57    inference(superposition,[],[f25,f77])).
% 0.21/0.57  fof(f77,plain,(
% 0.21/0.57    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_7),
% 0.21/0.57    inference(avatar_component_clause,[],[f75])).
% 0.21/0.57  fof(f177,plain,(
% 0.21/0.57    spl3_16 | ~spl3_12),
% 0.21/0.57    inference(avatar_split_clause,[],[f126,f110,f174])).
% 0.21/0.57  fof(f126,plain,(
% 0.21/0.57    sK0 = k2_xboole_0(sK0,k1_xboole_0) | ~spl3_12),
% 0.21/0.57    inference(backward_demodulation,[],[f120,f125])).
% 0.21/0.57  fof(f125,plain,(
% 0.21/0.57    sK0 = k3_xboole_0(sK0,sK0) | ~spl3_12),
% 0.21/0.57    inference(forward_demodulation,[],[f122,f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.57  fof(f122,plain,(
% 0.21/0.57    k4_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK0) | ~spl3_12),
% 0.21/0.57    inference(superposition,[],[f19,f112])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.57  fof(f120,plain,(
% 0.21/0.57    sK0 = k2_xboole_0(k3_xboole_0(sK0,sK0),k1_xboole_0) | ~spl3_12),
% 0.21/0.57    inference(superposition,[],[f22,f112])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.57  fof(f118,plain,(
% 0.21/0.57    spl3_13 | ~spl3_6 | ~spl3_10),
% 0.21/0.57    inference(avatar_split_clause,[],[f108,f90,f58,f115])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    spl3_6 <=> k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.57  fof(f108,plain,(
% 0.21/0.57    k1_xboole_0 = k4_xboole_0(sK2,sK2) | (~spl3_6 | ~spl3_10)),
% 0.21/0.57    inference(forward_demodulation,[],[f106,f60])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    k1_xboole_0 = k3_xboole_0(sK2,sK1) | ~spl3_6),
% 0.21/0.57    inference(avatar_component_clause,[],[f58])).
% 0.21/0.57  fof(f106,plain,(
% 0.21/0.57    k3_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2) | ~spl3_10),
% 0.21/0.57    inference(superposition,[],[f19,f92])).
% 0.21/0.57  fof(f113,plain,(
% 0.21/0.57    spl3_12 | ~spl3_5 | ~spl3_7),
% 0.21/0.57    inference(avatar_split_clause,[],[f103,f75,f49,f110])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    spl3_5 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.57  fof(f103,plain,(
% 0.21/0.57    k1_xboole_0 = k4_xboole_0(sK0,sK0) | (~spl3_5 | ~spl3_7)),
% 0.21/0.57    inference(forward_demodulation,[],[f101,f51])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl3_5),
% 0.21/0.57    inference(avatar_component_clause,[],[f49])).
% 0.21/0.57  fof(f101,plain,(
% 0.21/0.57    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK0) | ~spl3_7),
% 0.21/0.57    inference(superposition,[],[f19,f77])).
% 0.21/0.57  fof(f98,plain,(
% 0.21/0.57    spl3_11 | ~spl3_6),
% 0.21/0.57    inference(avatar_split_clause,[],[f73,f58,f95])).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    sK2 = k2_xboole_0(k1_xboole_0,sK2) | ~spl3_6),
% 0.21/0.57    inference(backward_demodulation,[],[f69,f72])).
% 0.21/0.57  fof(f72,plain,(
% 0.21/0.57    sK2 = k4_xboole_0(sK2,sK1) | ~spl3_6),
% 0.21/0.57    inference(forward_demodulation,[],[f70,f17])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,k1_xboole_0) | ~spl3_6),
% 0.21/0.57    inference(superposition,[],[f21,f60])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) | ~spl3_6),
% 0.21/0.57    inference(superposition,[],[f22,f60])).
% 0.21/0.57  fof(f93,plain,(
% 0.21/0.57    spl3_10 | ~spl3_6),
% 0.21/0.57    inference(avatar_split_clause,[],[f72,f58,f90])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    spl3_8 | ~spl3_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f53,f44,f80])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2) | ~spl3_4),
% 0.21/0.57    inference(superposition,[],[f46,f18])).
% 0.21/0.57  fof(f78,plain,(
% 0.21/0.57    spl3_7 | ~spl3_5),
% 0.21/0.57    inference(avatar_split_clause,[],[f66,f49,f75])).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_5),
% 0.21/0.57    inference(forward_demodulation,[],[f64,f17])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_5),
% 0.21/0.57    inference(superposition,[],[f21,f51])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    spl3_6 | ~spl3_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f42,f32,f58])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    spl3_2 <=> r1_xboole_0(sK2,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    k1_xboole_0 = k3_xboole_0(sK2,sK1) | ~spl3_2),
% 0.21/0.57    inference(resolution,[],[f34,f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    r1_xboole_0(sK2,sK1) | ~spl3_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f32])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    spl3_5 | ~spl3_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f41,f27,f49])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl3_1),
% 0.21/0.57    inference(resolution,[],[f29,f24])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f27])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    spl3_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f13,f44])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 0.21/0.57    inference(flattening,[],[f11])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 0.21/0.57    inference(negated_conjecture,[],[f9])).
% 0.21/0.57  fof(f9,conjecture,(
% 0.21/0.57    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ~spl3_3),
% 0.21/0.57    inference(avatar_split_clause,[],[f16,f37])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    sK0 != sK2),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    spl3_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f15,f32])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    r1_xboole_0(sK2,sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    spl3_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f14,f27])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    r1_xboole_0(sK0,sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (418)------------------------------
% 0.21/0.57  % (418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (418)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (418)Memory used [KB]: 11129
% 0.21/0.57  % (418)Time elapsed: 0.133 s
% 0.21/0.57  % (418)------------------------------
% 0.21/0.57  % (418)------------------------------
% 0.21/0.57  % (393)Success in time 0.205 s
%------------------------------------------------------------------------------
