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
% DateTime   : Thu Dec  3 12:33:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 120 expanded)
%              Number of leaves         :   21 (  58 expanded)
%              Depth                    :    7
%              Number of atoms          :  159 ( 254 expanded)
%              Number of equality atoms :   58 ( 105 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f227,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f27,f31,f35,f44,f49,f54,f59,f72,f80,f84,f133,f176,f225])).

fof(f225,plain,
    ( spl7_1
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_16
    | ~ spl7_21 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl7_1
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_16
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f22,f223])).

fof(f223,plain,
    ( ! [X6,X12,X10,X8,X7,X11,X9] : k2_xboole_0(k2_tarski(X10,X11),k3_enumset1(X12,X6,X7,X8,X9)) = k5_enumset1(X10,X11,X12,X6,X7,X8,X9)
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_16
    | ~ spl7_21 ),
    inference(forward_demodulation,[],[f222,f53])).

fof(f53,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl7_7
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f222,plain,
    ( ! [X6,X12,X10,X8,X7,X11,X9] : k2_xboole_0(k2_enumset1(X10,X11,X12,X6),k1_enumset1(X7,X8,X9)) = k2_xboole_0(k2_tarski(X10,X11),k3_enumset1(X12,X6,X7,X8,X9))
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_16
    | ~ spl7_21 ),
    inference(forward_demodulation,[],[f218,f137])).

fof(f137,plain,
    ( ! [X24,X23,X21,X19,X25,X22,X20] : k2_xboole_0(k1_enumset1(X24,X25,X19),k2_enumset1(X20,X21,X22,X23)) = k2_xboole_0(k2_tarski(X24,X25),k3_enumset1(X19,X20,X21,X22,X23))
    | ~ spl7_6
    | ~ spl7_16 ),
    inference(superposition,[],[f132,f48])).

fof(f48,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl7_6
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f132,plain,
    ( ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_enumset1(X3,X0,X1),X2)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl7_16
  <=> ! [X1,X3,X0,X2] : k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_enumset1(X3,X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f218,plain,
    ( ! [X6,X12,X10,X8,X7,X11,X9] : k2_xboole_0(k2_enumset1(X10,X11,X12,X6),k1_enumset1(X7,X8,X9)) = k2_xboole_0(k1_enumset1(X10,X11,X12),k2_enumset1(X6,X7,X8,X9))
    | ~ spl7_10
    | ~ spl7_21 ),
    inference(superposition,[],[f79,f175])).

fof(f175,plain,
    ( ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) = k2_enumset1(X3,X0,X1,X2)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl7_21
  <=> ! [X1,X3,X0,X2] : k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) = k2_enumset1(X3,X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f79,plain,
    ( ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_tarski(X3),X4)) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),X4)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl7_10
  <=> ! [X1,X3,X0,X2,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_tarski(X3),X4)) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f22,plain,
    ( k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl7_1
  <=> k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) = k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f176,plain,
    ( spl7_21
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f117,f82,f70,f42,f174])).

fof(f42,plain,
    ( spl7_5
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f70,plain,
    ( spl7_9
  <=> ! [X3,X5,X4,X6] : k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f82,plain,
    ( spl7_11
  <=> ! [X16,X15,X14] : k2_xboole_0(k2_tarski(X16,X14),k1_tarski(X15)) = k1_enumset1(X16,X14,X15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f117,plain,
    ( ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) = k2_enumset1(X3,X0,X1,X2)
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f115,f43])).

fof(f43,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f115,plain,
    ( ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X3,X0,X1),k1_tarski(X2)) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(superposition,[],[f71,f83])).

fof(f83,plain,
    ( ! [X14,X15,X16] : k2_xboole_0(k2_tarski(X16,X14),k1_tarski(X15)) = k1_enumset1(X16,X14,X15)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f82])).

fof(f71,plain,
    ( ! [X6,X4,X5,X3] : k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f133,plain,
    ( spl7_16
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f65,f57,f33,f29,f131])).

fof(f29,plain,
    ( spl7_3
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f33,plain,
    ( spl7_4
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f57,plain,
    ( spl7_8
  <=> ! [X1,X0,X2] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f65,plain,
    ( ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_enumset1(X3,X0,X1),X2)
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f60,f37])).

fof(f37,plain,
    ( ! [X6,X4,X5,X3] : k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(superposition,[],[f34,f30])).

fof(f30,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f34,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f33])).

fof(f60,plain,
    ( ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X0,X1),X2))
    | ~ spl7_8 ),
    inference(superposition,[],[f58,f58])).

fof(f58,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f84,plain,
    ( spl7_11
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f66,f57,f29,f25,f82])).

fof(f25,plain,
    ( spl7_2
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f66,plain,
    ( ! [X14,X15,X16] : k2_xboole_0(k2_tarski(X16,X14),k1_tarski(X15)) = k1_enumset1(X16,X14,X15)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f63,f30])).

fof(f63,plain,
    ( ! [X14,X15,X16] : k2_xboole_0(k2_tarski(X16,X14),k1_tarski(X15)) = k2_xboole_0(k1_tarski(X16),k2_tarski(X14,X15))
    | ~ spl7_2
    | ~ spl7_8 ),
    inference(superposition,[],[f58,f26])).

fof(f26,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f80,plain,
    ( spl7_10
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f45,f42,f33,f78])).

fof(f45,plain,
    ( ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_tarski(X3),X4)) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),X4)
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(superposition,[],[f34,f43])).

fof(f72,plain,
    ( spl7_9
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f37,f33,f29,f70])).

fof(f59,plain,
    ( spl7_8
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f36,f33,f25,f57])).

fof(f36,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(superposition,[],[f34,f26])).

fof(f54,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f18,f52])).

fof(f18,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

fof(f49,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f17,f47])).

fof(f17,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(f44,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f16,f42])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f35,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f15,f33])).

fof(f15,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f31,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f14,f29])).

fof(f14,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f27,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f13,f25])).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f23,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f12,f20])).

fof(f12,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:15:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (24781)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.44  % (24781)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f227,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f23,f27,f31,f35,f44,f49,f54,f59,f72,f80,f84,f133,f176,f225])).
% 0.21/0.44  fof(f225,plain,(
% 0.21/0.44    spl7_1 | ~spl7_6 | ~spl7_7 | ~spl7_10 | ~spl7_16 | ~spl7_21),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f224])).
% 0.21/0.44  fof(f224,plain,(
% 0.21/0.44    $false | (spl7_1 | ~spl7_6 | ~spl7_7 | ~spl7_10 | ~spl7_16 | ~spl7_21)),
% 0.21/0.44    inference(subsumption_resolution,[],[f22,f223])).
% 0.21/0.44  fof(f223,plain,(
% 0.21/0.44    ( ! [X6,X12,X10,X8,X7,X11,X9] : (k2_xboole_0(k2_tarski(X10,X11),k3_enumset1(X12,X6,X7,X8,X9)) = k5_enumset1(X10,X11,X12,X6,X7,X8,X9)) ) | (~spl7_6 | ~spl7_7 | ~spl7_10 | ~spl7_16 | ~spl7_21)),
% 0.21/0.44    inference(forward_demodulation,[],[f222,f53])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) ) | ~spl7_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f52])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    spl7_7 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.44  fof(f222,plain,(
% 0.21/0.44    ( ! [X6,X12,X10,X8,X7,X11,X9] : (k2_xboole_0(k2_enumset1(X10,X11,X12,X6),k1_enumset1(X7,X8,X9)) = k2_xboole_0(k2_tarski(X10,X11),k3_enumset1(X12,X6,X7,X8,X9))) ) | (~spl7_6 | ~spl7_10 | ~spl7_16 | ~spl7_21)),
% 0.21/0.44    inference(forward_demodulation,[],[f218,f137])).
% 0.21/0.44  fof(f137,plain,(
% 0.21/0.44    ( ! [X24,X23,X21,X19,X25,X22,X20] : (k2_xboole_0(k1_enumset1(X24,X25,X19),k2_enumset1(X20,X21,X22,X23)) = k2_xboole_0(k2_tarski(X24,X25),k3_enumset1(X19,X20,X21,X22,X23))) ) | (~spl7_6 | ~spl7_16)),
% 0.21/0.44    inference(superposition,[],[f132,f48])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) ) | ~spl7_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f47])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    spl7_6 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.44  fof(f132,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_enumset1(X3,X0,X1),X2)) ) | ~spl7_16),
% 0.21/0.44    inference(avatar_component_clause,[],[f131])).
% 0.21/0.44  fof(f131,plain,(
% 0.21/0.44    spl7_16 <=> ! [X1,X3,X0,X2] : k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_enumset1(X3,X0,X1),X2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.44  fof(f218,plain,(
% 0.21/0.44    ( ! [X6,X12,X10,X8,X7,X11,X9] : (k2_xboole_0(k2_enumset1(X10,X11,X12,X6),k1_enumset1(X7,X8,X9)) = k2_xboole_0(k1_enumset1(X10,X11,X12),k2_enumset1(X6,X7,X8,X9))) ) | (~spl7_10 | ~spl7_21)),
% 0.21/0.44    inference(superposition,[],[f79,f175])).
% 0.21/0.44  fof(f175,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) = k2_enumset1(X3,X0,X1,X2)) ) | ~spl7_21),
% 0.21/0.44    inference(avatar_component_clause,[],[f174])).
% 0.21/0.44  fof(f174,plain,(
% 0.21/0.44    spl7_21 <=> ! [X1,X3,X0,X2] : k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) = k2_enumset1(X3,X0,X1,X2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_tarski(X3),X4)) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),X4)) ) | ~spl7_10),
% 0.21/0.44    inference(avatar_component_clause,[],[f78])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    spl7_10 <=> ! [X1,X3,X0,X2,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_tarski(X3),X4)) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),X4)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)) | spl7_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    spl7_1 <=> k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) = k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.44  fof(f176,plain,(
% 0.21/0.44    spl7_21 | ~spl7_5 | ~spl7_9 | ~spl7_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f117,f82,f70,f42,f174])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    spl7_5 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    spl7_9 <=> ! [X3,X5,X4,X6] : k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    spl7_11 <=> ! [X16,X15,X14] : k2_xboole_0(k2_tarski(X16,X14),k1_tarski(X15)) = k1_enumset1(X16,X14,X15)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.44  fof(f117,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) = k2_enumset1(X3,X0,X1,X2)) ) | (~spl7_5 | ~spl7_9 | ~spl7_11)),
% 0.21/0.44    inference(forward_demodulation,[],[f115,f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) ) | ~spl7_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f42])).
% 0.21/0.44  fof(f115,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X3,X0,X1),k1_tarski(X2)) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))) ) | (~spl7_9 | ~spl7_11)),
% 0.21/0.44    inference(superposition,[],[f71,f83])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    ( ! [X14,X15,X16] : (k2_xboole_0(k2_tarski(X16,X14),k1_tarski(X15)) = k1_enumset1(X16,X14,X15)) ) | ~spl7_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f82])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    ( ! [X6,X4,X5,X3] : (k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) ) | ~spl7_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f70])).
% 0.21/0.44  fof(f133,plain,(
% 0.21/0.44    spl7_16 | ~spl7_3 | ~spl7_4 | ~spl7_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f65,f57,f33,f29,f131])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    spl7_3 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    spl7_4 <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    spl7_8 <=> ! [X1,X0,X2] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_enumset1(X3,X0,X1),X2)) ) | (~spl7_3 | ~spl7_4 | ~spl7_8)),
% 0.21/0.44    inference(forward_demodulation,[],[f60,f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ( ! [X6,X4,X5,X3] : (k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) ) | (~spl7_3 | ~spl7_4)),
% 0.21/0.44    inference(superposition,[],[f34,f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) ) | ~spl7_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f29])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl7_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f33])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X0,X1),X2))) ) | ~spl7_8),
% 0.21/0.44    inference(superposition,[],[f58,f58])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)) ) | ~spl7_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f57])).
% 0.21/0.44  fof(f84,plain,(
% 0.21/0.44    spl7_11 | ~spl7_2 | ~spl7_3 | ~spl7_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f66,f57,f29,f25,f82])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    spl7_2 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    ( ! [X14,X15,X16] : (k2_xboole_0(k2_tarski(X16,X14),k1_tarski(X15)) = k1_enumset1(X16,X14,X15)) ) | (~spl7_2 | ~spl7_3 | ~spl7_8)),
% 0.21/0.44    inference(forward_demodulation,[],[f63,f30])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    ( ! [X14,X15,X16] : (k2_xboole_0(k2_tarski(X16,X14),k1_tarski(X15)) = k2_xboole_0(k1_tarski(X16),k2_tarski(X14,X15))) ) | (~spl7_2 | ~spl7_8)),
% 0.21/0.44    inference(superposition,[],[f58,f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ) | ~spl7_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f25])).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    spl7_10 | ~spl7_4 | ~spl7_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f45,f42,f33,f78])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_tarski(X3),X4)) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),X4)) ) | (~spl7_4 | ~spl7_5)),
% 0.21/0.44    inference(superposition,[],[f34,f43])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    spl7_9 | ~spl7_3 | ~spl7_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f37,f33,f29,f70])).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    spl7_8 | ~spl7_2 | ~spl7_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f36,f33,f25,f57])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)) ) | (~spl7_2 | ~spl7_4)),
% 0.21/0.44    inference(superposition,[],[f34,f26])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    spl7_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f18,f52])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    spl7_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f17,f47])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    spl7_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f16,f42])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    spl7_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f15,f33])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    spl7_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f14,f29])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    spl7_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f13,f25])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ~spl7_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f12,f20])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6))),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f9,f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 0.21/0.44    inference(negated_conjecture,[],[f7])).
% 0.21/0.44  fof(f7,conjecture,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (24781)------------------------------
% 0.21/0.44  % (24781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (24781)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (24781)Memory used [KB]: 6268
% 0.21/0.44  % (24781)Time elapsed: 0.010 s
% 0.21/0.44  % (24781)------------------------------
% 0.21/0.44  % (24781)------------------------------
% 0.21/0.44  % (24770)Success in time 0.083 s
%------------------------------------------------------------------------------
