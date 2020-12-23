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
% DateTime   : Thu Dec  3 12:34:52 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 165 expanded)
%              Number of leaves         :   30 (  83 expanded)
%              Depth                    :    6
%              Number of atoms          :  208 ( 341 expanded)
%              Number of equality atoms :   79 ( 144 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1385,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f43,f55,f63,f67,f109,f113,f117,f121,f125,f148,f202,f229,f282,f416,f532,f793,f1337,f1342,f1380])).

fof(f1380,plain,
    ( spl3_1
    | ~ spl3_43
    | ~ spl3_69
    | ~ spl3_70 ),
    inference(avatar_contradiction_clause,[],[f1379])).

fof(f1379,plain,
    ( $false
    | spl3_1
    | ~ spl3_43
    | ~ spl3_69
    | ~ spl3_70 ),
    inference(subsumption_resolution,[],[f1338,f1343])).

fof(f1343,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X0,X2,X0)
    | ~ spl3_43
    | ~ spl3_70 ),
    inference(superposition,[],[f1341,f792])).

fof(f792,plain,
    ( ! [X21,X22,X20] : k1_enumset1(X20,X21,X22) = k3_enumset1(X20,X21,X21,X22,X20)
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f791])).

fof(f791,plain,
    ( spl3_43
  <=> ! [X20,X22,X21] : k1_enumset1(X20,X21,X22) = k3_enumset1(X20,X21,X21,X22,X20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f1341,plain,
    ( ! [X47,X45,X46,X44] : k3_enumset1(X44,X45,X45,X46,X47) = k2_enumset1(X45,X44,X46,X47)
    | ~ spl3_70 ),
    inference(avatar_component_clause,[],[f1340])).

fof(f1340,plain,
    ( spl3_70
  <=> ! [X44,X46,X45,X47] : k3_enumset1(X44,X45,X45,X46,X47) = k2_enumset1(X45,X44,X46,X47) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f1338,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0)
    | spl3_1
    | ~ spl3_69 ),
    inference(superposition,[],[f38,f1336])).

fof(f1336,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl3_69 ),
    inference(avatar_component_clause,[],[f1335])).

fof(f1335,plain,
    ( spl3_69
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f38,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1342,plain,
    ( spl3_70
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f545,f530,f115,f107,f41,f1340])).

fof(f41,plain,
    ( spl3_2
  <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f107,plain,
    ( spl3_9
  <=> ! [X1,X3,X0,X2] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f115,plain,
    ( spl3_11
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f530,plain,
    ( spl3_34
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f545,plain,
    ( ! [X47,X45,X46,X44] : k3_enumset1(X44,X45,X45,X46,X47) = k2_enumset1(X45,X44,X46,X47)
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f542,f544])).

fof(f544,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f533,f108])).

fof(f108,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f533,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
    | ~ spl3_2
    | ~ spl3_34 ),
    inference(superposition,[],[f531,f42])).

fof(f42,plain,
    ( ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f531,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f530])).

fof(f542,plain,
    ( ! [X47,X45,X46,X44] : k3_enumset1(X44,X45,X45,X46,X47) = k2_xboole_0(k2_tarski(X45,X44),k2_tarski(X46,X47))
    | ~ spl3_11
    | ~ spl3_34 ),
    inference(superposition,[],[f531,f116])).

fof(f116,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f115])).

fof(f1337,plain,
    ( spl3_69
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f544,f530,f107,f41,f1335])).

fof(f793,plain,
    ( spl3_43
    | ~ spl3_26
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f440,f414,f280,f791])).

fof(f280,plain,
    ( spl3_26
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f414,plain,
    ( spl3_30
  <=> ! [X25,X23,X24,X26] : k3_enumset1(X26,X23,X23,X24,X25) = k2_xboole_0(k1_tarski(X26),k1_enumset1(X25,X23,X24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f440,plain,
    ( ! [X21,X22,X20] : k1_enumset1(X20,X21,X22) = k3_enumset1(X20,X21,X21,X22,X20)
    | ~ spl3_26
    | ~ spl3_30 ),
    inference(superposition,[],[f415,f281])).

fof(f281,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f280])).

fof(f415,plain,
    ( ! [X26,X24,X23,X25] : k3_enumset1(X26,X23,X23,X24,X25) = k2_xboole_0(k1_tarski(X26),k1_enumset1(X25,X23,X24))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f414])).

fof(f532,plain,
    ( spl3_34
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f231,f227,f111,f65,f530])).

fof(f65,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f111,plain,
    ( spl3_10
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f227,plain,
    ( spl3_21
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f231,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f230,f112])).

fof(f112,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f230,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))
    | ~ spl3_8
    | ~ spl3_21 ),
    inference(superposition,[],[f228,f66])).

fof(f66,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f228,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f227])).

fof(f416,plain,
    ( spl3_30
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f210,f200,f61,f414])).

fof(f61,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f200,plain,
    ( spl3_19
  <=> ! [X1,X3,X0,X2] : k3_enumset1(X3,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f210,plain,
    ( ! [X26,X24,X23,X25] : k3_enumset1(X26,X23,X23,X24,X25) = k2_xboole_0(k1_tarski(X26),k1_enumset1(X25,X23,X24))
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(superposition,[],[f201,f62])).

fof(f62,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f201,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X3,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f200])).

fof(f282,plain,
    ( spl3_26
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f218,f200,f107,f65,f280])).

fof(f218,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2))
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f203,f66])).

fof(f203,plain,
    ( ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2))
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(superposition,[],[f201,f108])).

fof(f229,plain,
    ( spl3_21
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f150,f146,f123,f107,f227])).

fof(f123,plain,
    ( spl3_13
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f146,plain,
    ( spl3_16
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f150,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f149,f124])).

fof(f124,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f123])).

fof(f149,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))
    | ~ spl3_9
    | ~ spl3_16 ),
    inference(superposition,[],[f147,f108])).

fof(f147,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f146])).

fof(f202,plain,
    ( spl3_19
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f126,f119,f65,f200])).

fof(f119,plain,
    ( spl3_12
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f126,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X3,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(superposition,[],[f120,f66])).

fof(f120,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f148,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f34,f146])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

fof(f125,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f31,f123])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f121,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f30,f119])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f117,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f68,f53,f41,f115])).

fof(f53,plain,
    ( spl3_5
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f68,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(superposition,[],[f54,f42])).

fof(f54,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f113,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f29,f111])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f109,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f28,f107])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f67,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f27,f65])).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f63,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f26,f61])).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

fof(f55,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f24,f53])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

fof(f43,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f20,f36])).

fof(f20,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:53:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (18276)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (18273)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (18275)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (18278)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (18275)Refutation not found, incomplete strategy% (18275)------------------------------
% 0.21/0.47  % (18275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (18275)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (18275)Memory used [KB]: 10618
% 0.21/0.47  % (18275)Time elapsed: 0.062 s
% 0.21/0.47  % (18275)------------------------------
% 0.21/0.47  % (18275)------------------------------
% 0.21/0.47  % (18266)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (18268)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (18269)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (18270)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (18277)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (18264)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (18265)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (18274)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (18279)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (18271)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (18267)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (18272)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (18281)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.52  % (18280)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.49/0.55  % (18269)Refutation found. Thanks to Tanya!
% 1.49/0.55  % SZS status Theorem for theBenchmark
% 1.49/0.55  % SZS output start Proof for theBenchmark
% 1.49/0.55  fof(f1385,plain,(
% 1.49/0.55    $false),
% 1.49/0.55    inference(avatar_sat_refutation,[],[f39,f43,f55,f63,f67,f109,f113,f117,f121,f125,f148,f202,f229,f282,f416,f532,f793,f1337,f1342,f1380])).
% 1.49/0.55  fof(f1380,plain,(
% 1.49/0.55    spl3_1 | ~spl3_43 | ~spl3_69 | ~spl3_70),
% 1.49/0.55    inference(avatar_contradiction_clause,[],[f1379])).
% 1.49/0.55  fof(f1379,plain,(
% 1.49/0.55    $false | (spl3_1 | ~spl3_43 | ~spl3_69 | ~spl3_70)),
% 1.49/0.55    inference(subsumption_resolution,[],[f1338,f1343])).
% 1.49/0.55  fof(f1343,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X0,X2,X0)) ) | (~spl3_43 | ~spl3_70)),
% 1.49/0.55    inference(superposition,[],[f1341,f792])).
% 1.49/0.55  fof(f792,plain,(
% 1.49/0.55    ( ! [X21,X22,X20] : (k1_enumset1(X20,X21,X22) = k3_enumset1(X20,X21,X21,X22,X20)) ) | ~spl3_43),
% 1.49/0.55    inference(avatar_component_clause,[],[f791])).
% 1.49/0.55  fof(f791,plain,(
% 1.49/0.55    spl3_43 <=> ! [X20,X22,X21] : k1_enumset1(X20,X21,X22) = k3_enumset1(X20,X21,X21,X22,X20)),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 1.49/0.55  fof(f1341,plain,(
% 1.49/0.55    ( ! [X47,X45,X46,X44] : (k3_enumset1(X44,X45,X45,X46,X47) = k2_enumset1(X45,X44,X46,X47)) ) | ~spl3_70),
% 1.49/0.55    inference(avatar_component_clause,[],[f1340])).
% 1.49/0.55  fof(f1340,plain,(
% 1.49/0.55    spl3_70 <=> ! [X44,X46,X45,X47] : k3_enumset1(X44,X45,X45,X46,X47) = k2_enumset1(X45,X44,X46,X47)),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 1.49/0.55  fof(f1338,plain,(
% 1.49/0.55    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK1,sK0,sK2,sK0) | (spl3_1 | ~spl3_69)),
% 1.49/0.55    inference(superposition,[],[f38,f1336])).
% 1.49/0.55  fof(f1336,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | ~spl3_69),
% 1.49/0.55    inference(avatar_component_clause,[],[f1335])).
% 1.49/0.55  fof(f1335,plain,(
% 1.49/0.55    spl3_69 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 1.49/0.55  fof(f38,plain,(
% 1.49/0.55    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) | spl3_1),
% 1.49/0.55    inference(avatar_component_clause,[],[f36])).
% 1.49/0.55  fof(f36,plain,(
% 1.49/0.55    spl3_1 <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.49/0.55  fof(f1342,plain,(
% 1.49/0.55    spl3_70 | ~spl3_2 | ~spl3_9 | ~spl3_11 | ~spl3_34),
% 1.49/0.55    inference(avatar_split_clause,[],[f545,f530,f115,f107,f41,f1340])).
% 1.49/0.55  fof(f41,plain,(
% 1.49/0.55    spl3_2 <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.49/0.55  fof(f107,plain,(
% 1.49/0.55    spl3_9 <=> ! [X1,X3,X0,X2] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.49/0.55  fof(f115,plain,(
% 1.49/0.55    spl3_11 <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.49/0.55  fof(f530,plain,(
% 1.49/0.55    spl3_34 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 1.49/0.55  fof(f545,plain,(
% 1.49/0.55    ( ! [X47,X45,X46,X44] : (k3_enumset1(X44,X45,X45,X46,X47) = k2_enumset1(X45,X44,X46,X47)) ) | (~spl3_2 | ~spl3_9 | ~spl3_11 | ~spl3_34)),
% 1.49/0.55    inference(forward_demodulation,[],[f542,f544])).
% 1.49/0.55  fof(f544,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | (~spl3_2 | ~spl3_9 | ~spl3_34)),
% 1.49/0.55    inference(forward_demodulation,[],[f533,f108])).
% 1.49/0.55  fof(f108,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) ) | ~spl3_9),
% 1.49/0.55    inference(avatar_component_clause,[],[f107])).
% 1.49/0.55  fof(f533,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ) | (~spl3_2 | ~spl3_34)),
% 1.49/0.55    inference(superposition,[],[f531,f42])).
% 1.49/0.55  fof(f42,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) ) | ~spl3_2),
% 1.49/0.55    inference(avatar_component_clause,[],[f41])).
% 1.49/0.55  fof(f531,plain,(
% 1.49/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) ) | ~spl3_34),
% 1.49/0.55    inference(avatar_component_clause,[],[f530])).
% 1.49/0.55  fof(f542,plain,(
% 1.49/0.55    ( ! [X47,X45,X46,X44] : (k3_enumset1(X44,X45,X45,X46,X47) = k2_xboole_0(k2_tarski(X45,X44),k2_tarski(X46,X47))) ) | (~spl3_11 | ~spl3_34)),
% 1.49/0.55    inference(superposition,[],[f531,f116])).
% 1.49/0.55  fof(f116,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)) ) | ~spl3_11),
% 1.49/0.55    inference(avatar_component_clause,[],[f115])).
% 1.49/0.55  fof(f1337,plain,(
% 1.49/0.55    spl3_69 | ~spl3_2 | ~spl3_9 | ~spl3_34),
% 1.49/0.55    inference(avatar_split_clause,[],[f544,f530,f107,f41,f1335])).
% 1.49/0.55  fof(f793,plain,(
% 1.49/0.55    spl3_43 | ~spl3_26 | ~spl3_30),
% 1.49/0.55    inference(avatar_split_clause,[],[f440,f414,f280,f791])).
% 1.49/0.55  fof(f280,plain,(
% 1.49/0.55    spl3_26 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2))),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 1.49/0.55  fof(f414,plain,(
% 1.49/0.55    spl3_30 <=> ! [X25,X23,X24,X26] : k3_enumset1(X26,X23,X23,X24,X25) = k2_xboole_0(k1_tarski(X26),k1_enumset1(X25,X23,X24))),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 1.49/0.55  fof(f440,plain,(
% 1.49/0.55    ( ! [X21,X22,X20] : (k1_enumset1(X20,X21,X22) = k3_enumset1(X20,X21,X21,X22,X20)) ) | (~spl3_26 | ~spl3_30)),
% 1.49/0.55    inference(superposition,[],[f415,f281])).
% 1.49/0.55  fof(f281,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2))) ) | ~spl3_26),
% 1.49/0.55    inference(avatar_component_clause,[],[f280])).
% 1.49/0.55  fof(f415,plain,(
% 1.49/0.55    ( ! [X26,X24,X23,X25] : (k3_enumset1(X26,X23,X23,X24,X25) = k2_xboole_0(k1_tarski(X26),k1_enumset1(X25,X23,X24))) ) | ~spl3_30),
% 1.49/0.55    inference(avatar_component_clause,[],[f414])).
% 1.49/0.55  fof(f532,plain,(
% 1.49/0.55    spl3_34 | ~spl3_8 | ~spl3_10 | ~spl3_21),
% 1.49/0.55    inference(avatar_split_clause,[],[f231,f227,f111,f65,f530])).
% 1.49/0.55  fof(f65,plain,(
% 1.49/0.55    spl3_8 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.49/0.55  fof(f111,plain,(
% 1.49/0.55    spl3_10 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.49/0.55  fof(f227,plain,(
% 1.49/0.55    spl3_21 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.49/0.55  fof(f231,plain,(
% 1.49/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) ) | (~spl3_8 | ~spl3_10 | ~spl3_21)),
% 1.49/0.55    inference(forward_demodulation,[],[f230,f112])).
% 1.49/0.55  fof(f112,plain,(
% 1.49/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) ) | ~spl3_10),
% 1.49/0.55    inference(avatar_component_clause,[],[f111])).
% 1.49/0.55  fof(f230,plain,(
% 1.49/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) ) | (~spl3_8 | ~spl3_21)),
% 1.49/0.55    inference(superposition,[],[f228,f66])).
% 1.49/0.55  fof(f66,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) ) | ~spl3_8),
% 1.49/0.55    inference(avatar_component_clause,[],[f65])).
% 1.49/0.55  fof(f228,plain,(
% 1.49/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) ) | ~spl3_21),
% 1.49/0.55    inference(avatar_component_clause,[],[f227])).
% 1.49/0.55  fof(f416,plain,(
% 1.49/0.55    spl3_30 | ~spl3_7 | ~spl3_19),
% 1.49/0.55    inference(avatar_split_clause,[],[f210,f200,f61,f414])).
% 1.49/0.55  fof(f61,plain,(
% 1.49/0.55    spl3_7 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.49/0.55  fof(f200,plain,(
% 1.49/0.55    spl3_19 <=> ! [X1,X3,X0,X2] : k3_enumset1(X3,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.49/0.55  fof(f210,plain,(
% 1.49/0.55    ( ! [X26,X24,X23,X25] : (k3_enumset1(X26,X23,X23,X24,X25) = k2_xboole_0(k1_tarski(X26),k1_enumset1(X25,X23,X24))) ) | (~spl3_7 | ~spl3_19)),
% 1.49/0.55    inference(superposition,[],[f201,f62])).
% 1.49/0.55  fof(f62,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) ) | ~spl3_7),
% 1.49/0.55    inference(avatar_component_clause,[],[f61])).
% 1.49/0.55  fof(f201,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X3,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))) ) | ~spl3_19),
% 1.49/0.55    inference(avatar_component_clause,[],[f200])).
% 1.49/0.55  fof(f282,plain,(
% 1.49/0.55    spl3_26 | ~spl3_8 | ~spl3_9 | ~spl3_19),
% 1.49/0.55    inference(avatar_split_clause,[],[f218,f200,f107,f65,f280])).
% 1.49/0.55  fof(f218,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2))) ) | (~spl3_8 | ~spl3_9 | ~spl3_19)),
% 1.49/0.55    inference(forward_demodulation,[],[f203,f66])).
% 1.49/0.55  fof(f203,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2))) ) | (~spl3_9 | ~spl3_19)),
% 1.49/0.55    inference(superposition,[],[f201,f108])).
% 1.49/0.55  fof(f229,plain,(
% 1.49/0.55    spl3_21 | ~spl3_9 | ~spl3_13 | ~spl3_16),
% 1.49/0.55    inference(avatar_split_clause,[],[f150,f146,f123,f107,f227])).
% 1.49/0.55  fof(f123,plain,(
% 1.49/0.55    spl3_13 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.49/0.55  fof(f146,plain,(
% 1.49/0.55    spl3_16 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.49/0.55  fof(f150,plain,(
% 1.49/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) ) | (~spl3_9 | ~spl3_13 | ~spl3_16)),
% 1.49/0.55    inference(forward_demodulation,[],[f149,f124])).
% 1.49/0.55  fof(f124,plain,(
% 1.49/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) ) | ~spl3_13),
% 1.49/0.55    inference(avatar_component_clause,[],[f123])).
% 1.49/0.55  fof(f149,plain,(
% 1.49/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) ) | (~spl3_9 | ~spl3_16)),
% 1.49/0.55    inference(superposition,[],[f147,f108])).
% 1.49/0.55  fof(f147,plain,(
% 1.49/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) ) | ~spl3_16),
% 1.49/0.55    inference(avatar_component_clause,[],[f146])).
% 1.49/0.55  fof(f202,plain,(
% 1.49/0.55    spl3_19 | ~spl3_8 | ~spl3_12),
% 1.49/0.55    inference(avatar_split_clause,[],[f126,f119,f65,f200])).
% 1.49/0.55  fof(f119,plain,(
% 1.49/0.55    spl3_12 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.49/0.55  fof(f126,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X3,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))) ) | (~spl3_8 | ~spl3_12)),
% 1.49/0.55    inference(superposition,[],[f120,f66])).
% 1.49/0.55  fof(f120,plain,(
% 1.49/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) ) | ~spl3_12),
% 1.49/0.55    inference(avatar_component_clause,[],[f119])).
% 1.49/0.55  fof(f148,plain,(
% 1.49/0.55    spl3_16),
% 1.49/0.55    inference(avatar_split_clause,[],[f34,f146])).
% 1.49/0.55  fof(f34,plain,(
% 1.49/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f7])).
% 1.49/0.55  fof(f7,axiom,(
% 1.49/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).
% 1.49/0.55  fof(f125,plain,(
% 1.49/0.55    spl3_13),
% 1.49/0.55    inference(avatar_split_clause,[],[f31,f123])).
% 1.49/0.55  fof(f31,plain,(
% 1.49/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f12])).
% 1.49/0.55  fof(f12,axiom,(
% 1.49/0.55    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.49/0.55  fof(f121,plain,(
% 1.49/0.55    spl3_12),
% 1.49/0.55    inference(avatar_split_clause,[],[f30,f119])).
% 1.49/0.55  fof(f30,plain,(
% 1.49/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f5])).
% 1.49/0.55  fof(f5,axiom,(
% 1.49/0.55    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 1.49/0.55  fof(f117,plain,(
% 1.49/0.55    spl3_11 | ~spl3_2 | ~spl3_5),
% 1.49/0.55    inference(avatar_split_clause,[],[f68,f53,f41,f115])).
% 1.49/0.55  fof(f53,plain,(
% 1.49/0.55    spl3_5 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.49/0.55  fof(f68,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)) ) | (~spl3_2 | ~spl3_5)),
% 1.49/0.55    inference(superposition,[],[f54,f42])).
% 1.49/0.55  fof(f54,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) ) | ~spl3_5),
% 1.49/0.55    inference(avatar_component_clause,[],[f53])).
% 1.49/0.55  fof(f113,plain,(
% 1.49/0.55    spl3_10),
% 1.49/0.55    inference(avatar_split_clause,[],[f29,f111])).
% 1.49/0.55  fof(f29,plain,(
% 1.49/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f11])).
% 1.49/0.55  fof(f11,axiom,(
% 1.49/0.55    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.49/0.55  fof(f109,plain,(
% 1.49/0.55    spl3_9),
% 1.49/0.55    inference(avatar_split_clause,[],[f28,f107])).
% 1.49/0.55  fof(f28,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f10])).
% 1.49/0.55  fof(f10,axiom,(
% 1.49/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.49/0.55  fof(f67,plain,(
% 1.49/0.55    spl3_8),
% 1.49/0.55    inference(avatar_split_clause,[],[f27,f65])).
% 1.49/0.55  fof(f27,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f9])).
% 1.49/0.55  fof(f9,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.49/0.55  fof(f63,plain,(
% 1.49/0.55    spl3_7),
% 1.49/0.55    inference(avatar_split_clause,[],[f26,f61])).
% 1.49/0.55  fof(f26,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f3])).
% 1.49/0.55  fof(f3,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).
% 1.49/0.55  fof(f55,plain,(
% 1.49/0.55    spl3_5),
% 1.49/0.55    inference(avatar_split_clause,[],[f24,f53])).
% 1.49/0.55  fof(f24,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f4])).
% 1.49/0.55  fof(f4,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).
% 1.49/0.55  fof(f43,plain,(
% 1.49/0.55    spl3_2),
% 1.49/0.55    inference(avatar_split_clause,[],[f21,f41])).
% 1.49/0.55  fof(f21,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f8])).
% 1.49/0.55  fof(f8,axiom,(
% 1.49/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.49/0.55  fof(f39,plain,(
% 1.49/0.55    ~spl3_1),
% 1.49/0.55    inference(avatar_split_clause,[],[f20,f36])).
% 1.49/0.55  fof(f20,plain,(
% 1.49/0.55    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.49/0.55    inference(cnf_transformation,[],[f19])).
% 1.49/0.55  fof(f19,plain,(
% 1.49/0.55    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.49/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).
% 1.49/0.55  fof(f18,plain,(
% 1.49/0.55    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f17,plain,(
% 1.49/0.55    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.49/0.55    inference(ennf_transformation,[],[f16])).
% 1.49/0.55  fof(f16,negated_conjecture,(
% 1.49/0.55    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.49/0.55    inference(negated_conjecture,[],[f15])).
% 1.49/0.55  fof(f15,conjecture,(
% 1.49/0.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
% 1.49/0.55  % SZS output end Proof for theBenchmark
% 1.49/0.55  % (18269)------------------------------
% 1.49/0.55  % (18269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (18269)Termination reason: Refutation
% 1.49/0.55  
% 1.49/0.55  % (18269)Memory used [KB]: 7164
% 1.49/0.55  % (18269)Time elapsed: 0.124 s
% 1.49/0.55  % (18269)------------------------------
% 1.49/0.55  % (18269)------------------------------
% 1.49/0.55  % (18263)Success in time 0.19 s
%------------------------------------------------------------------------------
