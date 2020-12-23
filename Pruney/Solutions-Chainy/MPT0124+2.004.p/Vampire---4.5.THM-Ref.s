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
% DateTime   : Thu Dec  3 12:32:59 EST 2020

% Result     : Theorem 39.20s
% Output     : Refutation 39.20s
% Verified   : 
% Statistics : Number of formulae       :  207 (1175 expanded)
%              Number of leaves         :   25 ( 403 expanded)
%              Depth                    :   45
%              Number of atoms          :  346 (1348 expanded)
%              Number of equality atoms :  193 (1160 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :   11 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43227,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f103,f199,f223,f261,f416,f961,f6754,f43216,f43226])).

fof(f43226,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f43225])).

fof(f43225,plain,
    ( $false
    | spl3_13 ),
    inference(subsumption_resolution,[],[f43224,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f43224,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,sK2),sK0)
    | spl3_13 ),
    inference(forward_demodulation,[],[f43223,f78])).

fof(f78,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(forward_demodulation,[],[f66,f55])).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f28,f44])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f40,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f25,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f66,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f34,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f41,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f30,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(definition_unfolding,[],[f27,f32,f38])).

fof(f27,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f43223,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),sK0)
    | spl3_13 ),
    inference(forward_demodulation,[],[f43222,f15735])).

fof(f15735,plain,(
    ! [X43,X41,X44,X42] : k5_xboole_0(X43,k5_xboole_0(X41,k5_xboole_0(X42,X44))) = k5_xboole_0(X43,k5_xboole_0(X42,k5_xboole_0(X44,X41))) ),
    inference(forward_demodulation,[],[f15734,f34])).

fof(f15734,plain,(
    ! [X43,X41,X44,X42] : k5_xboole_0(X43,k5_xboole_0(k5_xboole_0(X41,X42),X44)) = k5_xboole_0(X43,k5_xboole_0(X42,k5_xboole_0(X44,X41))) ),
    inference(forward_demodulation,[],[f15733,f67])).

fof(f67,plain,(
    ! [X6,X4,X5] : k5_xboole_0(X4,k5_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,X4),X6) ),
    inference(superposition,[],[f34,f28])).

fof(f15733,plain,(
    ! [X43,X41,X44,X42] : k5_xboole_0(X43,k5_xboole_0(k5_xboole_0(X41,X42),X44)) = k5_xboole_0(k5_xboole_0(X42,X43),k5_xboole_0(X44,X41)) ),
    inference(forward_demodulation,[],[f15592,f34])).

fof(f15592,plain,(
    ! [X43,X41,X44,X42] : k5_xboole_0(k5_xboole_0(X42,X43),k5_xboole_0(X44,X41)) = k5_xboole_0(k5_xboole_0(X43,k5_xboole_0(X41,X42)),X44) ),
    inference(superposition,[],[f485,f72])).

fof(f72,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8)) ),
    inference(superposition,[],[f34,f28])).

fof(f485,plain,(
    ! [X12,X10,X11] : k5_xboole_0(X12,k5_xboole_0(X10,X11)) = k5_xboole_0(k5_xboole_0(X11,X12),X10) ),
    inference(superposition,[],[f72,f28])).

fof(f43222,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),sK0)
    | spl3_13 ),
    inference(forward_demodulation,[],[f43221,f14151])).

fof(f14151,plain,(
    ! [X132,X133,X131] : k5_xboole_0(X133,k5_xboole_0(X131,X132)) = k5_xboole_0(X133,k5_xboole_0(X132,X131)) ),
    inference(forward_demodulation,[],[f14083,f55])).

fof(f14083,plain,(
    ! [X132,X133,X131] : k5_xboole_0(X133,k5_xboole_0(X131,X132)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X133),k5_xboole_0(X132,X131)) ),
    inference(superposition,[],[f435,f501])).

fof(f501,plain,(
    ! [X37,X38] : k5_xboole_0(X38,X37) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X37,X38)) ),
    inference(superposition,[],[f72,f55])).

fof(f435,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X9,X10) = k5_xboole_0(k5_xboole_0(X8,X9),k5_xboole_0(X8,X10)) ),
    inference(superposition,[],[f67,f78])).

fof(f43221,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK2,sK1),sK1)),sK0)
    | spl3_13 ),
    inference(forward_demodulation,[],[f43220,f72])).

fof(f43220,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK2,sK1))),sK0)
    | spl3_13 ),
    inference(forward_demodulation,[],[f43219,f459])).

fof(f459,plain,(
    ! [X28,X26,X27,X25] : k5_xboole_0(X27,k5_xboole_0(X26,k5_xboole_0(X25,X28))) = k5_xboole_0(X27,k5_xboole_0(X25,k5_xboole_0(X26,X28))) ),
    inference(forward_demodulation,[],[f458,f34])).

fof(f458,plain,(
    ! [X28,X26,X27,X25] : k5_xboole_0(X27,k5_xboole_0(k5_xboole_0(X25,X26),X28)) = k5_xboole_0(X27,k5_xboole_0(X26,k5_xboole_0(X25,X28))) ),
    inference(forward_demodulation,[],[f440,f457])).

fof(f457,plain,(
    ! [X24,X23,X21,X22] : k5_xboole_0(k5_xboole_0(X22,k5_xboole_0(X21,X23)),X24) = k5_xboole_0(X23,k5_xboole_0(X21,k5_xboole_0(X22,X24))) ),
    inference(forward_demodulation,[],[f439,f34])).

fof(f439,plain,(
    ! [X24,X23,X21,X22] : k5_xboole_0(X23,k5_xboole_0(k5_xboole_0(X21,X22),X24)) = k5_xboole_0(k5_xboole_0(X22,k5_xboole_0(X21,X23)),X24) ),
    inference(superposition,[],[f67,f67])).

fof(f440,plain,(
    ! [X28,X26,X27,X25] : k5_xboole_0(X27,k5_xboole_0(k5_xboole_0(X25,X26),X28)) = k5_xboole_0(k5_xboole_0(X25,k5_xboole_0(X26,X27)),X28) ),
    inference(superposition,[],[f67,f34])).

fof(f43219,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))),sK0)
    | spl3_13 ),
    inference(forward_demodulation,[],[f43218,f72])).

fof(f43218,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)),sK0)
    | spl3_13 ),
    inference(forward_demodulation,[],[f43217,f72])).

fof(f43217,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)),sK0)
    | spl3_13 ),
    inference(superposition,[],[f43215,f1114])).

fof(f1114,plain,(
    ! [X4,X2,X3] : k3_xboole_0(k5_xboole_0(X4,X2),X3) = k5_xboole_0(k3_xboole_0(X3,X4),k3_xboole_0(X3,X2)) ),
    inference(superposition,[],[f123,f29])).

fof(f123,plain,(
    ! [X4,X2,X3] : k3_xboole_0(k5_xboole_0(X2,X4),X3) = k5_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(X4,X3)) ),
    inference(superposition,[],[f37,f29])).

fof(f37,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f43215,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f43213])).

fof(f43213,plain,
    ( spl3_13
  <=> k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) = k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f43216,plain,
    ( ~ spl3_13
    | ~ spl3_5
    | spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f42907,f6751,f958,f413,f258,f43213])).

fof(f258,plain,
    ( spl3_5
  <=> sK2 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f413,plain,
    ( spl3_6
  <=> k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) = k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f958,plain,
    ( spl3_7
  <=> k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f6751,plain,
    ( spl3_10
  <=> k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f42907,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | ~ spl3_5
    | spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f42906,f82])).

fof(f82,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f36,f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f42906,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))))
    | ~ spl3_5
    | spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f42905,f55])).

fof(f42905,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(k1_xboole_0,sK0),k5_xboole_0(sK1,sK2))))
    | ~ spl3_5
    | spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f42904,f2152])).

fof(f2152,plain,(
    ! [X12,X10,X11] : k3_xboole_0(X11,k3_xboole_0(k5_xboole_0(X11,X10),X12)) = k3_xboole_0(X11,k3_xboole_0(k5_xboole_0(X10,X11),X12)) ),
    inference(backward_demodulation,[],[f1003,f2151])).

fof(f2151,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X1,X2),X0) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X0))) ),
    inference(forward_demodulation,[],[f2150,f37])).

fof(f2150,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X0))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X2,X0)) ),
    inference(forward_demodulation,[],[f2083,f29])).

fof(f2083,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X2,X0)) = k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X0)),X0) ),
    inference(superposition,[],[f133,f26])).

fof(f133,plain,(
    ! [X14,X15,X13,X16] : k3_xboole_0(k5_xboole_0(X16,k3_xboole_0(X13,X14)),X15) = k5_xboole_0(k3_xboole_0(X16,X15),k3_xboole_0(X13,k3_xboole_0(X14,X15))) ),
    inference(superposition,[],[f37,f36])).

fof(f1003,plain,(
    ! [X12,X10,X11] : k3_xboole_0(X11,k3_xboole_0(k5_xboole_0(X11,X10),X12)) = k3_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,k3_xboole_0(X11,X12)))) ),
    inference(forward_demodulation,[],[f1002,f36])).

fof(f1002,plain,(
    ! [X12,X10,X11] : k3_xboole_0(k3_xboole_0(X11,k5_xboole_0(X11,X10)),X12) = k3_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,k3_xboole_0(X11,X12)))) ),
    inference(forward_demodulation,[],[f1001,f142])).

fof(f142,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f122,f29])).

fof(f122,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f37,f26])).

fof(f1001,plain,(
    ! [X12,X10,X11] : k3_xboole_0(k5_xboole_0(X11,k3_xboole_0(X10,X11)),X12) = k3_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,k3_xboole_0(X11,X12)))) ),
    inference(forward_demodulation,[],[f1000,f28])).

fof(f1000,plain,(
    ! [X12,X10,X11] : k3_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,k3_xboole_0(X11,X12)))) = k3_xboole_0(k5_xboole_0(k3_xboole_0(X10,X11),X11),X12) ),
    inference(forward_demodulation,[],[f999,f123])).

fof(f999,plain,(
    ! [X12,X10,X11] : k5_xboole_0(k3_xboole_0(X12,k3_xboole_0(X10,X11)),k3_xboole_0(X11,X12)) = k3_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,k3_xboole_0(X11,X12)))) ),
    inference(forward_demodulation,[],[f967,f36])).

fof(f967,plain,(
    ! [X12,X10,X11] : k5_xboole_0(k3_xboole_0(X12,k3_xboole_0(X10,X11)),k3_xboole_0(X11,X12)) = k3_xboole_0(k3_xboole_0(X11,X12),k5_xboole_0(X10,k3_xboole_0(X11,X12))) ),
    inference(superposition,[],[f146,f88])).

fof(f88,plain,(
    ! [X8,X7,X9] : k3_xboole_0(X7,k3_xboole_0(X8,X9)) = k3_xboole_0(X9,k3_xboole_0(X7,X8)) ),
    inference(superposition,[],[f36,f29])).

fof(f146,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(X1,X0),X0) = k3_xboole_0(X0,k5_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f128,f29])).

fof(f128,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(X1,X0),X0) = k3_xboole_0(k5_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f37,f26])).

fof(f42904,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(sK1,sK2))))
    | ~ spl3_5
    | spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f42903,f16984])).

fof(f16984,plain,(
    ! [X12,X10,X11] : k3_xboole_0(X11,k3_xboole_0(X12,X10)) = k3_xboole_0(X11,k3_xboole_0(X10,X12)) ),
    inference(superposition,[],[f569,f88])).

fof(f569,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,k3_xboole_0(X4,X5)) = k3_xboole_0(X4,k3_xboole_0(X3,X5)) ),
    inference(superposition,[],[f83,f36])).

fof(f83,plain,(
    ! [X6,X4,X5] : k3_xboole_0(X4,k3_xboole_0(X5,X6)) = k3_xboole_0(k3_xboole_0(X5,X4),X6) ),
    inference(superposition,[],[f36,f29])).

fof(f42903,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k1_xboole_0))))
    | ~ spl3_5
    | spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f42902,f45])).

fof(f42902,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)))))
    | ~ spl3_5
    | spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f42901,f72])).

fof(f42901,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))))
    | ~ spl3_5
    | spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f42900,f16984])).

fof(f42900,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2))))
    | ~ spl3_5
    | spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f42899,f17290])).

fof(f17290,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,X66),k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,X66)))
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f6022,f16975])).

fof(f16975,plain,
    ( ! [X105] : k3_xboole_0(X105,k5_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k3_xboole_0(X105,k5_xboole_0(sK1,sK2)))
    | ~ spl3_10 ),
    inference(superposition,[],[f569,f6753])).

fof(f6753,plain,
    ( k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f6751])).

fof(f6022,plain,
    ( ! [X66] : k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,X66),k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,X66)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6021,f34])).

fof(f6021,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,X66),k5_xboole_0(sK1,sK2)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6020,f88])).

fof(f6020,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,k5_xboole_0(sK1,X66)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6019,f305])).

fof(f305,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f170,f304])).

fof(f304,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f303,f29])).

fof(f303,plain,(
    ! [X0,X1] : k3_xboole_0(k5_xboole_0(X0,X1),X0) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f292,f129])).

fof(f129,plain,(
    ! [X4,X2,X3] : k3_xboole_0(k5_xboole_0(X4,X2),X3) = k5_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(X3,X2)) ),
    inference(superposition,[],[f37,f29])).

fof(f292,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f49,f82])).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) ),
    inference(backward_demodulation,[],[f43,f36])).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f35,f32,f32])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f170,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f153,f82])).

fof(f153,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f49,f26])).

fof(f6019,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,X66)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6018,f55])).

fof(f6018,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(k1_xboole_0,sK1),X66)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6017,f1421])).

fof(f1421,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k5_xboole_0(X3,X5),X4) = k3_xboole_0(k5_xboole_0(X5,X3),X4) ),
    inference(superposition,[],[f135,f37])).

fof(f135,plain,(
    ! [X6,X7,X5] : k3_xboole_0(k5_xboole_0(X5,X7),X6) = k5_xboole_0(k3_xboole_0(X7,X6),k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f37,f28])).

fof(f6017,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k1_xboole_0),X66)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6016,f24])).

fof(f6016,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0)),X66)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6015,f45])).

fof(f6015,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,k5_xboole_0(sK1,sK1))),X66)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6014,f426])).

fof(f426,plain,
    ( ! [X2] : k3_xboole_0(sK2,k5_xboole_0(X2,sK2)) = k3_xboole_0(sK2,k5_xboole_0(X2,sK1))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f425,f29])).

fof(f425,plain,
    ( ! [X2] : k3_xboole_0(k5_xboole_0(X2,sK1),sK2) = k3_xboole_0(sK2,k5_xboole_0(X2,sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f419,f146])).

fof(f419,plain,
    ( ! [X2] : k3_xboole_0(k5_xboole_0(X2,sK1),sK2) = k5_xboole_0(k3_xboole_0(X2,sK2),sK2)
    | ~ spl3_5 ),
    inference(superposition,[],[f37,f260])).

fof(f260,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f258])).

fof(f6014,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))),X66)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6013,f29])).

fof(f6013,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,sK2),sK2)),X66)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6012,f78])).

fof(f6012,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),sK2)))),X66)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6011,f72])).

fof(f6011,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK2),sK2),sK2))),X66)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6010,f28])).

fof(f6010,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK2),sK2),sK2),sK2)),X66)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6009,f72])).

fof(f6009,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK2),sK2),sK2))),X66)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6008,f459])).

fof(f6008,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK2),sK2),k5_xboole_0(sK1,sK2))),X66)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6007,f782])).

fof(f782,plain,(
    ! [X12,X10,X11] : k5_xboole_0(X10,k5_xboole_0(k3_xboole_0(X11,X10),X12)) = k5_xboole_0(X12,k3_xboole_0(X10,k5_xboole_0(X10,X11))) ),
    inference(superposition,[],[f72,f142])).

fof(f6007,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X66)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6006,f28])).

fof(f6006,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X66),sK1))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6005,f55])).

fof(f6005,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X66),sK1)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6004,f72])).

fof(f6004,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X66))))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6003,f78])).

fof(f6003,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X66))))))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6002,f72])).

fof(f6002,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X66)),sK2))))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6001,f28])).

fof(f6001,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X66)),sK2),sK2)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6000,f72])).

fof(f6000,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X66)),sK2))))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f5999,f459])).

fof(f5999,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X66)),k5_xboole_0(sK1,sK2))))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f5629,f72])).

fof(f5629,plain,
    ( ! [X66] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X66)))))
    | ~ spl3_7 ),
    inference(superposition,[],[f325,f960])).

fof(f960,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f958])).

fof(f325,plain,(
    ! [X10,X8,X9] : k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(X9,k5_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(k5_xboole_0(X8,k3_xboole_0(X9,k5_xboole_0(X9,X8))),X10))))) = k3_xboole_0(X8,k5_xboole_0(X8,X10)) ),
    inference(forward_demodulation,[],[f314,f305])).

fof(f314,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X8,k3_xboole_0(X8,X10)) = k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(X9,k5_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(k5_xboole_0(X8,k3_xboole_0(X9,k5_xboole_0(X9,X8))),X10))))) ),
    inference(backward_demodulation,[],[f173,f305])).

fof(f173,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X8,k3_xboole_0(X8,X10)) = k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(X9,k5_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X10))))) ),
    inference(forward_demodulation,[],[f172,f34])).

fof(f172,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X8,k3_xboole_0(X8,X10)) = k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(k5_xboole_0(X9,k3_xboole_0(X9,X8)),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X10)))) ),
    inference(forward_demodulation,[],[f171,f34])).

fof(f171,plain,(
    ! [X10,X8,X9] : k3_xboole_0(X8,k5_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X10))) = k5_xboole_0(X8,k3_xboole_0(X8,X10)) ),
    inference(forward_demodulation,[],[f156,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X2)) ),
    inference(superposition,[],[f36,f42])).

fof(f156,plain,(
    ! [X10,X8,X9] : k3_xboole_0(X8,k5_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X10))) = k5_xboole_0(X8,k3_xboole_0(X8,k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X10))) ),
    inference(superposition,[],[f49,f42])).

fof(f42899,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))))))
    | spl3_6 ),
    inference(forward_demodulation,[],[f42898,f806])).

fof(f806,plain,(
    ! [X12,X10,X11] : k5_xboole_0(X10,k5_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,X11)))) = k3_xboole_0(k5_xboole_0(X10,X11),k5_xboole_0(X10,k5_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f778,f34])).

fof(f778,plain,(
    ! [X12,X10,X11] : k5_xboole_0(X10,k5_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,X11)))) = k3_xboole_0(k5_xboole_0(X10,X11),k5_xboole_0(k5_xboole_0(X10,X11),X12)) ),
    inference(superposition,[],[f142,f34])).

fof(f42898,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2))))))
    | spl3_6 ),
    inference(forward_demodulation,[],[f42897,f14151])).

fof(f42897,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)),sK2))))
    | spl3_6 ),
    inference(forward_demodulation,[],[f42896,f72])).

fof(f42896,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2))))))
    | spl3_6 ),
    inference(forward_demodulation,[],[f42891,f29])).

fof(f42891,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)))),sK0))
    | spl3_6 ),
    inference(backward_demodulation,[],[f415,f42887])).

fof(f42887,plain,(
    ! [X109,X107,X110,X108] : k3_xboole_0(X109,k5_xboole_0(X108,k5_xboole_0(X107,k3_xboole_0(X109,X110)))) = k3_xboole_0(k5_xboole_0(X107,k5_xboole_0(X108,X110)),X109) ),
    inference(forward_demodulation,[],[f42428,f34])).

fof(f42428,plain,(
    ! [X109,X107,X110,X108] : k3_xboole_0(k5_xboole_0(k5_xboole_0(X107,X108),X110),X109) = k3_xboole_0(X109,k5_xboole_0(X108,k5_xboole_0(X107,k3_xboole_0(X109,X110)))) ),
    inference(superposition,[],[f1286,f67])).

fof(f1286,plain,(
    ! [X10,X8,X9] : k3_xboole_0(X8,k5_xboole_0(X10,k3_xboole_0(X8,X9))) = k3_xboole_0(k5_xboole_0(X10,X9),X8) ),
    inference(forward_demodulation,[],[f1285,f129])).

fof(f1285,plain,(
    ! [X10,X8,X9] : k5_xboole_0(k3_xboole_0(X10,X8),k3_xboole_0(X8,X9)) = k3_xboole_0(X8,k5_xboole_0(X10,k3_xboole_0(X8,X9))) ),
    inference(forward_demodulation,[],[f1234,f29])).

fof(f1234,plain,(
    ! [X10,X8,X9] : k5_xboole_0(k3_xboole_0(X10,X8),k3_xboole_0(X8,X9)) = k3_xboole_0(k5_xboole_0(X10,k3_xboole_0(X8,X9)),X8) ),
    inference(superposition,[],[f129,f82])).

fof(f415,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)))))))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f413])).

fof(f6754,plain,
    ( spl3_10
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f774,f100,f6751])).

fof(f100,plain,
    ( spl3_2
  <=> sK2 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f774,plain,
    ( k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(superposition,[],[f142,f102])).

fof(f102,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f961,plain,
    ( spl3_7
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f801,f258,f958])).

fof(f801,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f800,f45])).

fof(f800,plain,
    ( k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f773,f28])).

fof(f773,plain,
    ( k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k5_xboole_0(sK2,sK1))
    | ~ spl3_5 ),
    inference(superposition,[],[f142,f260])).

fof(f416,plain,
    ( ~ spl3_6
    | spl3_4 ),
    inference(avatar_split_clause,[],[f331,f220,f413])).

fof(f220,plain,
    ( spl3_4
  <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f331,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)))))))
    | spl3_4 ),
    inference(forward_demodulation,[],[f330,f305])).

fof(f330,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)))))))
    | spl3_4 ),
    inference(forward_demodulation,[],[f329,f88])).

fof(f329,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(k5_xboole_0(sK1,sK2),sK0))))))
    | spl3_4 ),
    inference(forward_demodulation,[],[f323,f88])).

fof(f323,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)))))))
    | spl3_4 ),
    inference(backward_demodulation,[],[f222,f305])).

fof(f222,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f220])).

fof(f261,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f200,f100,f258])).

fof(f200,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(superposition,[],[f102,f29])).

fof(f223,plain,
    ( ~ spl3_4
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f211,f196,f100,f220])).

fof(f196,plain,
    ( spl3_3
  <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f211,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))))
    | ~ spl3_2
    | spl3_3 ),
    inference(forward_demodulation,[],[f210,f29])).

fof(f210,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2))))))
    | ~ spl3_2
    | spl3_3 ),
    inference(backward_demodulation,[],[f198,f200])).

fof(f198,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f196])).

fof(f199,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f48,f196])).

fof(f48,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))))) ),
    inference(forward_demodulation,[],[f47,f29])).

fof(f47,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) ),
    inference(forward_demodulation,[],[f46,f34])).

fof(f46,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))) ),
    inference(backward_demodulation,[],[f39,f43])).

fof(f39,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))) ),
    inference(definition_unfolding,[],[f23,f32,f38,f32,f32])).

fof(f23,plain,(
    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    & r1_tarski(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
        & r1_tarski(X2,X1) )
   => ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).

fof(f103,plain,
    ( spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f63,f51,f100])).

fof(f51,plain,
    ( spl3_1
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f63,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f53,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f53,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f54,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f22,f51])).

fof(f22,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (19697)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (19695)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (19698)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (19699)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (19707)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (19702)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (19696)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (19700)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (19710)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (19712)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (19703)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (19701)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (19704)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (19708)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (19709)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (19711)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (19705)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (19706)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 5.19/1.01  % (19699)Time limit reached!
% 5.19/1.01  % (19699)------------------------------
% 5.19/1.01  % (19699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.19/1.01  % (19699)Termination reason: Time limit
% 5.19/1.01  
% 5.19/1.01  % (19699)Memory used [KB]: 15351
% 5.19/1.01  % (19699)Time elapsed: 0.602 s
% 5.19/1.01  % (19699)------------------------------
% 5.19/1.01  % (19699)------------------------------
% 12.15/1.94  % (19700)Time limit reached!
% 12.15/1.94  % (19700)------------------------------
% 12.15/1.94  % (19700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.15/1.95  % (19700)Termination reason: Time limit
% 12.15/1.95  
% 12.15/1.95  % (19700)Memory used [KB]: 29807
% 12.15/1.95  % (19700)Time elapsed: 1.519 s
% 12.15/1.95  % (19700)------------------------------
% 12.15/1.95  % (19700)------------------------------
% 12.15/1.96  % (19701)Time limit reached!
% 12.15/1.96  % (19701)------------------------------
% 12.15/1.96  % (19701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.15/1.96  % (19701)Termination reason: Time limit
% 12.15/1.96  
% 12.15/1.96  % (19701)Memory used [KB]: 41705
% 12.15/1.96  % (19701)Time elapsed: 1.514 s
% 12.15/1.96  % (19701)------------------------------
% 12.15/1.96  % (19701)------------------------------
% 14.70/2.26  % (19697)Time limit reached!
% 14.70/2.26  % (19697)------------------------------
% 14.70/2.26  % (19697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.70/2.26  % (19697)Termination reason: Time limit
% 14.70/2.26  
% 14.70/2.26  % (19697)Memory used [KB]: 49764
% 14.70/2.26  % (19697)Time elapsed: 1.808 s
% 14.70/2.26  % (19697)------------------------------
% 14.70/2.26  % (19697)------------------------------
% 17.98/2.64  % (19707)Time limit reached!
% 17.98/2.64  % (19707)------------------------------
% 17.98/2.64  % (19707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.98/2.64  % (19707)Termination reason: Time limit
% 17.98/2.64  % (19707)Termination phase: Saturation
% 17.98/2.64  
% 17.98/2.64  % (19707)Memory used [KB]: 46694
% 17.98/2.64  % (19707)Time elapsed: 2.200 s
% 17.98/2.64  % (19707)------------------------------
% 17.98/2.64  % (19707)------------------------------
% 39.20/5.28  % (19710)Refutation found. Thanks to Tanya!
% 39.20/5.28  % SZS status Theorem for theBenchmark
% 39.20/5.29  % SZS output start Proof for theBenchmark
% 39.20/5.29  fof(f43227,plain,(
% 39.20/5.29    $false),
% 39.20/5.29    inference(avatar_sat_refutation,[],[f54,f103,f199,f223,f261,f416,f961,f6754,f43216,f43226])).
% 39.20/5.29  fof(f43226,plain,(
% 39.20/5.29    spl3_13),
% 39.20/5.29    inference(avatar_contradiction_clause,[],[f43225])).
% 39.20/5.29  fof(f43225,plain,(
% 39.20/5.29    $false | spl3_13),
% 39.20/5.29    inference(subsumption_resolution,[],[f43224,f29])).
% 39.20/5.29  fof(f29,plain,(
% 39.20/5.29    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 39.20/5.29    inference(cnf_transformation,[],[f1])).
% 39.20/5.29  fof(f1,axiom,(
% 39.20/5.29    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 39.20/5.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 39.20/5.29  fof(f43224,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,sK2),sK0) | spl3_13),
% 39.20/5.29    inference(forward_demodulation,[],[f43223,f78])).
% 39.20/5.29  fof(f78,plain,(
% 39.20/5.29    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 39.20/5.29    inference(forward_demodulation,[],[f66,f55])).
% 39.20/5.29  fof(f55,plain,(
% 39.20/5.29    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 39.20/5.29    inference(superposition,[],[f28,f44])).
% 39.20/5.29  fof(f44,plain,(
% 39.20/5.29    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 39.20/5.29    inference(forward_demodulation,[],[f40,f24])).
% 39.20/5.29  fof(f24,plain,(
% 39.20/5.29    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 39.20/5.29    inference(cnf_transformation,[],[f9])).
% 39.20/5.29  fof(f9,axiom,(
% 39.20/5.29    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 39.20/5.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 39.20/5.29  fof(f40,plain,(
% 39.20/5.29    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 39.20/5.29    inference(definition_unfolding,[],[f25,f32])).
% 39.20/5.29  fof(f32,plain,(
% 39.20/5.29    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 39.20/5.29    inference(cnf_transformation,[],[f4])).
% 39.20/5.29  fof(f4,axiom,(
% 39.20/5.29    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 39.20/5.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 39.20/5.29  fof(f25,plain,(
% 39.20/5.29    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 39.20/5.29    inference(cnf_transformation,[],[f10])).
% 39.20/5.29  fof(f10,axiom,(
% 39.20/5.29    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 39.20/5.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 39.20/5.29  fof(f28,plain,(
% 39.20/5.29    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 39.20/5.29    inference(cnf_transformation,[],[f2])).
% 39.20/5.29  fof(f2,axiom,(
% 39.20/5.29    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 39.20/5.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 39.20/5.29  fof(f66,plain,(
% 39.20/5.29    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 39.20/5.29    inference(superposition,[],[f34,f45])).
% 39.20/5.29  fof(f45,plain,(
% 39.20/5.29    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 39.20/5.29    inference(backward_demodulation,[],[f41,f42])).
% 39.20/5.29  fof(f42,plain,(
% 39.20/5.29    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 39.20/5.29    inference(definition_unfolding,[],[f30,f38])).
% 39.20/5.29  fof(f38,plain,(
% 39.20/5.29    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 39.20/5.29    inference(definition_unfolding,[],[f31,f32])).
% 39.20/5.29  fof(f31,plain,(
% 39.20/5.29    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 39.20/5.29    inference(cnf_transformation,[],[f14])).
% 39.20/5.29  fof(f14,axiom,(
% 39.20/5.29    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 39.20/5.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 39.20/5.29  fof(f30,plain,(
% 39.20/5.29    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 39.20/5.29    inference(cnf_transformation,[],[f7])).
% 39.20/5.29  fof(f7,axiom,(
% 39.20/5.29    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 39.20/5.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 39.20/5.29  fof(f41,plain,(
% 39.20/5.29    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 39.20/5.29    inference(definition_unfolding,[],[f27,f32,f38])).
% 39.20/5.29  fof(f27,plain,(
% 39.20/5.29    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 39.20/5.29    inference(cnf_transformation,[],[f11])).
% 39.20/5.29  fof(f11,axiom,(
% 39.20/5.29    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 39.20/5.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 39.20/5.29  fof(f34,plain,(
% 39.20/5.29    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 39.20/5.29    inference(cnf_transformation,[],[f13])).
% 39.20/5.29  fof(f13,axiom,(
% 39.20/5.29    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 39.20/5.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 39.20/5.29  fof(f43223,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),sK0) | spl3_13),
% 39.20/5.29    inference(forward_demodulation,[],[f43222,f15735])).
% 39.20/5.29  fof(f15735,plain,(
% 39.20/5.29    ( ! [X43,X41,X44,X42] : (k5_xboole_0(X43,k5_xboole_0(X41,k5_xboole_0(X42,X44))) = k5_xboole_0(X43,k5_xboole_0(X42,k5_xboole_0(X44,X41)))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f15734,f34])).
% 39.20/5.29  fof(f15734,plain,(
% 39.20/5.29    ( ! [X43,X41,X44,X42] : (k5_xboole_0(X43,k5_xboole_0(k5_xboole_0(X41,X42),X44)) = k5_xboole_0(X43,k5_xboole_0(X42,k5_xboole_0(X44,X41)))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f15733,f67])).
% 39.20/5.29  fof(f67,plain,(
% 39.20/5.29    ( ! [X6,X4,X5] : (k5_xboole_0(X4,k5_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,X4),X6)) )),
% 39.20/5.29    inference(superposition,[],[f34,f28])).
% 39.20/5.29  fof(f15733,plain,(
% 39.20/5.29    ( ! [X43,X41,X44,X42] : (k5_xboole_0(X43,k5_xboole_0(k5_xboole_0(X41,X42),X44)) = k5_xboole_0(k5_xboole_0(X42,X43),k5_xboole_0(X44,X41))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f15592,f34])).
% 39.20/5.29  fof(f15592,plain,(
% 39.20/5.29    ( ! [X43,X41,X44,X42] : (k5_xboole_0(k5_xboole_0(X42,X43),k5_xboole_0(X44,X41)) = k5_xboole_0(k5_xboole_0(X43,k5_xboole_0(X41,X42)),X44)) )),
% 39.20/5.29    inference(superposition,[],[f485,f72])).
% 39.20/5.29  fof(f72,plain,(
% 39.20/5.29    ( ! [X8,X7,X9] : (k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8))) )),
% 39.20/5.29    inference(superposition,[],[f34,f28])).
% 39.20/5.29  fof(f485,plain,(
% 39.20/5.29    ( ! [X12,X10,X11] : (k5_xboole_0(X12,k5_xboole_0(X10,X11)) = k5_xboole_0(k5_xboole_0(X11,X12),X10)) )),
% 39.20/5.29    inference(superposition,[],[f72,f28])).
% 39.20/5.29  fof(f43222,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),sK0) | spl3_13),
% 39.20/5.29    inference(forward_demodulation,[],[f43221,f14151])).
% 39.20/5.29  fof(f14151,plain,(
% 39.20/5.29    ( ! [X132,X133,X131] : (k5_xboole_0(X133,k5_xboole_0(X131,X132)) = k5_xboole_0(X133,k5_xboole_0(X132,X131))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f14083,f55])).
% 39.20/5.29  fof(f14083,plain,(
% 39.20/5.29    ( ! [X132,X133,X131] : (k5_xboole_0(X133,k5_xboole_0(X131,X132)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X133),k5_xboole_0(X132,X131))) )),
% 39.20/5.29    inference(superposition,[],[f435,f501])).
% 39.20/5.29  fof(f501,plain,(
% 39.20/5.29    ( ! [X37,X38] : (k5_xboole_0(X38,X37) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X37,X38))) )),
% 39.20/5.29    inference(superposition,[],[f72,f55])).
% 39.20/5.29  fof(f435,plain,(
% 39.20/5.29    ( ! [X10,X8,X9] : (k5_xboole_0(X9,X10) = k5_xboole_0(k5_xboole_0(X8,X9),k5_xboole_0(X8,X10))) )),
% 39.20/5.29    inference(superposition,[],[f67,f78])).
% 39.20/5.29  fof(f43221,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK2,sK1),sK1)),sK0) | spl3_13),
% 39.20/5.29    inference(forward_demodulation,[],[f43220,f72])).
% 39.20/5.29  fof(f43220,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK2,sK1))),sK0) | spl3_13),
% 39.20/5.29    inference(forward_demodulation,[],[f43219,f459])).
% 39.20/5.29  fof(f459,plain,(
% 39.20/5.29    ( ! [X28,X26,X27,X25] : (k5_xboole_0(X27,k5_xboole_0(X26,k5_xboole_0(X25,X28))) = k5_xboole_0(X27,k5_xboole_0(X25,k5_xboole_0(X26,X28)))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f458,f34])).
% 39.20/5.29  fof(f458,plain,(
% 39.20/5.29    ( ! [X28,X26,X27,X25] : (k5_xboole_0(X27,k5_xboole_0(k5_xboole_0(X25,X26),X28)) = k5_xboole_0(X27,k5_xboole_0(X26,k5_xboole_0(X25,X28)))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f440,f457])).
% 39.20/5.29  fof(f457,plain,(
% 39.20/5.29    ( ! [X24,X23,X21,X22] : (k5_xboole_0(k5_xboole_0(X22,k5_xboole_0(X21,X23)),X24) = k5_xboole_0(X23,k5_xboole_0(X21,k5_xboole_0(X22,X24)))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f439,f34])).
% 39.20/5.29  fof(f439,plain,(
% 39.20/5.29    ( ! [X24,X23,X21,X22] : (k5_xboole_0(X23,k5_xboole_0(k5_xboole_0(X21,X22),X24)) = k5_xboole_0(k5_xboole_0(X22,k5_xboole_0(X21,X23)),X24)) )),
% 39.20/5.29    inference(superposition,[],[f67,f67])).
% 39.20/5.29  fof(f440,plain,(
% 39.20/5.29    ( ! [X28,X26,X27,X25] : (k5_xboole_0(X27,k5_xboole_0(k5_xboole_0(X25,X26),X28)) = k5_xboole_0(k5_xboole_0(X25,k5_xboole_0(X26,X27)),X28)) )),
% 39.20/5.29    inference(superposition,[],[f67,f34])).
% 39.20/5.29  fof(f43219,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))),sK0) | spl3_13),
% 39.20/5.29    inference(forward_demodulation,[],[f43218,f72])).
% 39.20/5.29  fof(f43218,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)),sK0) | spl3_13),
% 39.20/5.29    inference(forward_demodulation,[],[f43217,f72])).
% 39.20/5.29  fof(f43217,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)),sK0) | spl3_13),
% 39.20/5.29    inference(superposition,[],[f43215,f1114])).
% 39.20/5.29  fof(f1114,plain,(
% 39.20/5.29    ( ! [X4,X2,X3] : (k3_xboole_0(k5_xboole_0(X4,X2),X3) = k5_xboole_0(k3_xboole_0(X3,X4),k3_xboole_0(X3,X2))) )),
% 39.20/5.29    inference(superposition,[],[f123,f29])).
% 39.20/5.29  fof(f123,plain,(
% 39.20/5.29    ( ! [X4,X2,X3] : (k3_xboole_0(k5_xboole_0(X2,X4),X3) = k5_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(X4,X3))) )),
% 39.20/5.29    inference(superposition,[],[f37,f29])).
% 39.20/5.29  fof(f37,plain,(
% 39.20/5.29    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 39.20/5.29    inference(cnf_transformation,[],[f5])).
% 39.20/5.29  fof(f5,axiom,(
% 39.20/5.29    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 39.20/5.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 39.20/5.29  fof(f43215,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))) | spl3_13),
% 39.20/5.29    inference(avatar_component_clause,[],[f43213])).
% 39.20/5.29  fof(f43213,plain,(
% 39.20/5.29    spl3_13 <=> k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) = k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)))),
% 39.20/5.29    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 39.20/5.29  fof(f43216,plain,(
% 39.20/5.29    ~spl3_13 | ~spl3_5 | spl3_6 | ~spl3_7 | ~spl3_10),
% 39.20/5.29    inference(avatar_split_clause,[],[f42907,f6751,f958,f413,f258,f43213])).
% 39.20/5.29  fof(f258,plain,(
% 39.20/5.29    spl3_5 <=> sK2 = k3_xboole_0(sK1,sK2)),
% 39.20/5.29    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 39.20/5.29  fof(f413,plain,(
% 39.20/5.29    spl3_6 <=> k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) = k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)))))))),
% 39.20/5.29    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 39.20/5.29  fof(f958,plain,(
% 39.20/5.29    spl3_7 <=> k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))),
% 39.20/5.29    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 39.20/5.29  fof(f6751,plain,(
% 39.20/5.29    spl3_10 <=> k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))),
% 39.20/5.29    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 39.20/5.29  fof(f42907,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))) | (~spl3_5 | spl3_6 | ~spl3_7 | ~spl3_10)),
% 39.20/5.29    inference(forward_demodulation,[],[f42906,f82])).
% 39.20/5.29  fof(f82,plain,(
% 39.20/5.29    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 39.20/5.29    inference(superposition,[],[f36,f26])).
% 39.20/5.29  fof(f26,plain,(
% 39.20/5.29    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 39.20/5.29    inference(cnf_transformation,[],[f17])).
% 39.20/5.29  fof(f17,plain,(
% 39.20/5.29    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 39.20/5.29    inference(rectify,[],[f3])).
% 39.20/5.29  fof(f3,axiom,(
% 39.20/5.29    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 39.20/5.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 39.20/5.29  fof(f36,plain,(
% 39.20/5.29    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 39.20/5.29    inference(cnf_transformation,[],[f6])).
% 39.20/5.29  fof(f6,axiom,(
% 39.20/5.29    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 39.20/5.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 39.20/5.29  fof(f42906,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)))) | (~spl3_5 | spl3_6 | ~spl3_7 | ~spl3_10)),
% 39.20/5.29    inference(forward_demodulation,[],[f42905,f55])).
% 39.20/5.29  fof(f42905,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(k1_xboole_0,sK0),k5_xboole_0(sK1,sK2)))) | (~spl3_5 | spl3_6 | ~spl3_7 | ~spl3_10)),
% 39.20/5.29    inference(forward_demodulation,[],[f42904,f2152])).
% 39.20/5.29  fof(f2152,plain,(
% 39.20/5.29    ( ! [X12,X10,X11] : (k3_xboole_0(X11,k3_xboole_0(k5_xboole_0(X11,X10),X12)) = k3_xboole_0(X11,k3_xboole_0(k5_xboole_0(X10,X11),X12))) )),
% 39.20/5.29    inference(backward_demodulation,[],[f1003,f2151])).
% 39.20/5.29  fof(f2151,plain,(
% 39.20/5.29    ( ! [X2,X0,X1] : (k3_xboole_0(k5_xboole_0(X1,X2),X0) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X0)))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f2150,f37])).
% 39.20/5.29  fof(f2150,plain,(
% 39.20/5.29    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X0))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X2,X0))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f2083,f29])).
% 39.20/5.29  fof(f2083,plain,(
% 39.20/5.29    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X2,X0)) = k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X0)),X0)) )),
% 39.20/5.29    inference(superposition,[],[f133,f26])).
% 39.20/5.29  fof(f133,plain,(
% 39.20/5.29    ( ! [X14,X15,X13,X16] : (k3_xboole_0(k5_xboole_0(X16,k3_xboole_0(X13,X14)),X15) = k5_xboole_0(k3_xboole_0(X16,X15),k3_xboole_0(X13,k3_xboole_0(X14,X15)))) )),
% 39.20/5.29    inference(superposition,[],[f37,f36])).
% 39.20/5.29  fof(f1003,plain,(
% 39.20/5.29    ( ! [X12,X10,X11] : (k3_xboole_0(X11,k3_xboole_0(k5_xboole_0(X11,X10),X12)) = k3_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,k3_xboole_0(X11,X12))))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f1002,f36])).
% 39.20/5.29  fof(f1002,plain,(
% 39.20/5.29    ( ! [X12,X10,X11] : (k3_xboole_0(k3_xboole_0(X11,k5_xboole_0(X11,X10)),X12) = k3_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,k3_xboole_0(X11,X12))))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f1001,f142])).
% 39.20/5.29  fof(f142,plain,(
% 39.20/5.29    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f122,f29])).
% 39.20/5.29  fof(f122,plain,(
% 39.20/5.29    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0)) )),
% 39.20/5.29    inference(superposition,[],[f37,f26])).
% 39.20/5.29  fof(f1001,plain,(
% 39.20/5.29    ( ! [X12,X10,X11] : (k3_xboole_0(k5_xboole_0(X11,k3_xboole_0(X10,X11)),X12) = k3_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,k3_xboole_0(X11,X12))))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f1000,f28])).
% 39.20/5.29  fof(f1000,plain,(
% 39.20/5.29    ( ! [X12,X10,X11] : (k3_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,k3_xboole_0(X11,X12)))) = k3_xboole_0(k5_xboole_0(k3_xboole_0(X10,X11),X11),X12)) )),
% 39.20/5.29    inference(forward_demodulation,[],[f999,f123])).
% 39.20/5.29  fof(f999,plain,(
% 39.20/5.29    ( ! [X12,X10,X11] : (k5_xboole_0(k3_xboole_0(X12,k3_xboole_0(X10,X11)),k3_xboole_0(X11,X12)) = k3_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,k3_xboole_0(X11,X12))))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f967,f36])).
% 39.20/5.29  fof(f967,plain,(
% 39.20/5.29    ( ! [X12,X10,X11] : (k5_xboole_0(k3_xboole_0(X12,k3_xboole_0(X10,X11)),k3_xboole_0(X11,X12)) = k3_xboole_0(k3_xboole_0(X11,X12),k5_xboole_0(X10,k3_xboole_0(X11,X12)))) )),
% 39.20/5.29    inference(superposition,[],[f146,f88])).
% 39.20/5.29  fof(f88,plain,(
% 39.20/5.29    ( ! [X8,X7,X9] : (k3_xboole_0(X7,k3_xboole_0(X8,X9)) = k3_xboole_0(X9,k3_xboole_0(X7,X8))) )),
% 39.20/5.29    inference(superposition,[],[f36,f29])).
% 39.20/5.29  fof(f146,plain,(
% 39.20/5.29    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X1,X0),X0) = k3_xboole_0(X0,k5_xboole_0(X1,X0))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f128,f29])).
% 39.20/5.29  fof(f128,plain,(
% 39.20/5.29    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X1,X0),X0) = k3_xboole_0(k5_xboole_0(X1,X0),X0)) )),
% 39.20/5.29    inference(superposition,[],[f37,f26])).
% 39.20/5.29  fof(f42904,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(sK1,sK2)))) | (~spl3_5 | spl3_6 | ~spl3_7 | ~spl3_10)),
% 39.20/5.29    inference(forward_demodulation,[],[f42903,f16984])).
% 39.20/5.29  fof(f16984,plain,(
% 39.20/5.29    ( ! [X12,X10,X11] : (k3_xboole_0(X11,k3_xboole_0(X12,X10)) = k3_xboole_0(X11,k3_xboole_0(X10,X12))) )),
% 39.20/5.29    inference(superposition,[],[f569,f88])).
% 39.20/5.29  fof(f569,plain,(
% 39.20/5.29    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k3_xboole_0(X4,X5)) = k3_xboole_0(X4,k3_xboole_0(X3,X5))) )),
% 39.20/5.29    inference(superposition,[],[f83,f36])).
% 39.20/5.29  fof(f83,plain,(
% 39.20/5.29    ( ! [X6,X4,X5] : (k3_xboole_0(X4,k3_xboole_0(X5,X6)) = k3_xboole_0(k3_xboole_0(X5,X4),X6)) )),
% 39.20/5.29    inference(superposition,[],[f36,f29])).
% 39.20/5.29  fof(f42903,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k1_xboole_0)))) | (~spl3_5 | spl3_6 | ~spl3_7 | ~spl3_10)),
% 39.20/5.29    inference(forward_demodulation,[],[f42902,f45])).
% 39.20/5.29  fof(f42902,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))))) | (~spl3_5 | spl3_6 | ~spl3_7 | ~spl3_10)),
% 39.20/5.29    inference(forward_demodulation,[],[f42901,f72])).
% 39.20/5.29  fof(f42901,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))))) | (~spl3_5 | spl3_6 | ~spl3_7 | ~spl3_10)),
% 39.20/5.29    inference(forward_demodulation,[],[f42900,f16984])).
% 39.20/5.29  fof(f42900,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)))) | (~spl3_5 | spl3_6 | ~spl3_7 | ~spl3_10)),
% 39.20/5.29    inference(forward_demodulation,[],[f42899,f17290])).
% 39.20/5.29  fof(f17290,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,X66),k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,X66)))) ) | (~spl3_5 | ~spl3_7 | ~spl3_10)),
% 39.20/5.29    inference(backward_demodulation,[],[f6022,f16975])).
% 39.20/5.29  fof(f16975,plain,(
% 39.20/5.29    ( ! [X105] : (k3_xboole_0(X105,k5_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k3_xboole_0(X105,k5_xboole_0(sK1,sK2)))) ) | ~spl3_10),
% 39.20/5.29    inference(superposition,[],[f569,f6753])).
% 39.20/5.29  fof(f6753,plain,(
% 39.20/5.29    k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | ~spl3_10),
% 39.20/5.29    inference(avatar_component_clause,[],[f6751])).
% 39.20/5.29  fof(f6022,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,X66),k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,X66)))) ) | (~spl3_5 | ~spl3_7)),
% 39.20/5.29    inference(forward_demodulation,[],[f6021,f34])).
% 39.20/5.29  fof(f6021,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,X66),k5_xboole_0(sK1,sK2)))) ) | (~spl3_5 | ~spl3_7)),
% 39.20/5.29    inference(forward_demodulation,[],[f6020,f88])).
% 39.20/5.29  fof(f6020,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,k5_xboole_0(sK1,X66)))) ) | (~spl3_5 | ~spl3_7)),
% 39.20/5.29    inference(forward_demodulation,[],[f6019,f305])).
% 39.20/5.29  fof(f305,plain,(
% 39.20/5.29    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 39.20/5.29    inference(backward_demodulation,[],[f170,f304])).
% 39.20/5.29  fof(f304,plain,(
% 39.20/5.29    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f303,f29])).
% 39.20/5.29  fof(f303,plain,(
% 39.20/5.29    ( ! [X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X1),X0) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f292,f129])).
% 39.20/5.29  fof(f129,plain,(
% 39.20/5.29    ( ! [X4,X2,X3] : (k3_xboole_0(k5_xboole_0(X4,X2),X3) = k5_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(X3,X2))) )),
% 39.20/5.29    inference(superposition,[],[f37,f29])).
% 39.20/5.29  fof(f292,plain,(
% 39.20/5.29    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X1))) )),
% 39.20/5.29    inference(superposition,[],[f49,f82])).
% 39.20/5.29  fof(f49,plain,(
% 39.20/5.29    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))) )),
% 39.20/5.29    inference(backward_demodulation,[],[f43,f36])).
% 39.20/5.29  fof(f43,plain,(
% 39.20/5.29    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 39.20/5.29    inference(definition_unfolding,[],[f35,f32,f32])).
% 39.20/5.29  fof(f35,plain,(
% 39.20/5.29    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 39.20/5.29    inference(cnf_transformation,[],[f12])).
% 39.20/5.29  fof(f12,axiom,(
% 39.20/5.29    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 39.20/5.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 39.20/5.29  fof(f170,plain,(
% 39.20/5.29    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f153,f82])).
% 39.20/5.29  fof(f153,plain,(
% 39.20/5.29    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 39.20/5.29    inference(superposition,[],[f49,f26])).
% 39.20/5.29  fof(f6019,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,X66)))) ) | (~spl3_5 | ~spl3_7)),
% 39.20/5.29    inference(forward_demodulation,[],[f6018,f55])).
% 39.20/5.29  fof(f6018,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(k1_xboole_0,sK1),X66)))) ) | (~spl3_5 | ~spl3_7)),
% 39.20/5.29    inference(forward_demodulation,[],[f6017,f1421])).
% 39.20/5.29  fof(f1421,plain,(
% 39.20/5.29    ( ! [X4,X5,X3] : (k3_xboole_0(k5_xboole_0(X3,X5),X4) = k3_xboole_0(k5_xboole_0(X5,X3),X4)) )),
% 39.20/5.29    inference(superposition,[],[f135,f37])).
% 39.20/5.29  fof(f135,plain,(
% 39.20/5.29    ( ! [X6,X7,X5] : (k3_xboole_0(k5_xboole_0(X5,X7),X6) = k5_xboole_0(k3_xboole_0(X7,X6),k3_xboole_0(X5,X6))) )),
% 39.20/5.29    inference(superposition,[],[f37,f28])).
% 39.20/5.29  fof(f6017,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k1_xboole_0),X66)))) ) | (~spl3_5 | ~spl3_7)),
% 39.20/5.29    inference(forward_demodulation,[],[f6016,f24])).
% 39.20/5.29  fof(f6016,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0)),X66)))) ) | (~spl3_5 | ~spl3_7)),
% 39.20/5.29    inference(forward_demodulation,[],[f6015,f45])).
% 39.20/5.29  fof(f6015,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,k5_xboole_0(sK1,sK1))),X66)))) ) | (~spl3_5 | ~spl3_7)),
% 39.20/5.29    inference(forward_demodulation,[],[f6014,f426])).
% 39.20/5.29  fof(f426,plain,(
% 39.20/5.29    ( ! [X2] : (k3_xboole_0(sK2,k5_xboole_0(X2,sK2)) = k3_xboole_0(sK2,k5_xboole_0(X2,sK1))) ) | ~spl3_5),
% 39.20/5.29    inference(forward_demodulation,[],[f425,f29])).
% 39.20/5.29  fof(f425,plain,(
% 39.20/5.29    ( ! [X2] : (k3_xboole_0(k5_xboole_0(X2,sK1),sK2) = k3_xboole_0(sK2,k5_xboole_0(X2,sK2))) ) | ~spl3_5),
% 39.20/5.29    inference(forward_demodulation,[],[f419,f146])).
% 39.20/5.29  fof(f419,plain,(
% 39.20/5.29    ( ! [X2] : (k3_xboole_0(k5_xboole_0(X2,sK1),sK2) = k5_xboole_0(k3_xboole_0(X2,sK2),sK2)) ) | ~spl3_5),
% 39.20/5.29    inference(superposition,[],[f37,f260])).
% 39.20/5.29  fof(f260,plain,(
% 39.20/5.29    sK2 = k3_xboole_0(sK1,sK2) | ~spl3_5),
% 39.20/5.29    inference(avatar_component_clause,[],[f258])).
% 39.20/5.29  fof(f6014,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))),X66)))) ) | ~spl3_7),
% 39.20/5.29    inference(forward_demodulation,[],[f6013,f29])).
% 39.20/5.29  fof(f6013,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,sK2),sK2)),X66)))) ) | ~spl3_7),
% 39.20/5.29    inference(forward_demodulation,[],[f6012,f78])).
% 39.20/5.29  fof(f6012,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),sK2)))),X66)))) ) | ~spl3_7),
% 39.20/5.29    inference(forward_demodulation,[],[f6011,f72])).
% 39.20/5.29  fof(f6011,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK2),sK2),sK2))),X66)))) ) | ~spl3_7),
% 39.20/5.29    inference(forward_demodulation,[],[f6010,f28])).
% 39.20/5.29  fof(f6010,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK2),sK2),sK2),sK2)),X66)))) ) | ~spl3_7),
% 39.20/5.29    inference(forward_demodulation,[],[f6009,f72])).
% 39.20/5.29  fof(f6009,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK2),sK2),sK2))),X66)))) ) | ~spl3_7),
% 39.20/5.29    inference(forward_demodulation,[],[f6008,f459])).
% 39.20/5.29  fof(f6008,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK2),sK2),k5_xboole_0(sK1,sK2))),X66)))) ) | ~spl3_7),
% 39.20/5.29    inference(forward_demodulation,[],[f6007,f782])).
% 39.20/5.29  fof(f782,plain,(
% 39.20/5.29    ( ! [X12,X10,X11] : (k5_xboole_0(X10,k5_xboole_0(k3_xboole_0(X11,X10),X12)) = k5_xboole_0(X12,k3_xboole_0(X10,k5_xboole_0(X10,X11)))) )),
% 39.20/5.29    inference(superposition,[],[f72,f142])).
% 39.20/5.29  fof(f6007,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X66)))) ) | ~spl3_7),
% 39.20/5.29    inference(forward_demodulation,[],[f6006,f28])).
% 39.20/5.29  fof(f6006,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X66),sK1))) ) | ~spl3_7),
% 39.20/5.29    inference(forward_demodulation,[],[f6005,f55])).
% 39.20/5.29  fof(f6005,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X66),sK1)))) ) | ~spl3_7),
% 39.20/5.29    inference(forward_demodulation,[],[f6004,f72])).
% 39.20/5.29  fof(f6004,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X66))))) ) | ~spl3_7),
% 39.20/5.29    inference(forward_demodulation,[],[f6003,f78])).
% 39.20/5.29  fof(f6003,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X66))))))) ) | ~spl3_7),
% 39.20/5.29    inference(forward_demodulation,[],[f6002,f72])).
% 39.20/5.29  fof(f6002,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X66)),sK2))))) ) | ~spl3_7),
% 39.20/5.29    inference(forward_demodulation,[],[f6001,f28])).
% 39.20/5.29  fof(f6001,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X66)),sK2),sK2)))) ) | ~spl3_7),
% 39.20/5.29    inference(forward_demodulation,[],[f6000,f72])).
% 39.20/5.29  fof(f6000,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X66)),sK2))))) ) | ~spl3_7),
% 39.20/5.29    inference(forward_demodulation,[],[f5999,f459])).
% 39.20/5.29  fof(f5999,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X66)),k5_xboole_0(sK1,sK2))))) ) | ~spl3_7),
% 39.20/5.29    inference(forward_demodulation,[],[f5629,f72])).
% 39.20/5.29  fof(f5629,plain,(
% 39.20/5.29    ( ! [X66] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X66)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X66)))))) ) | ~spl3_7),
% 39.20/5.29    inference(superposition,[],[f325,f960])).
% 39.20/5.29  fof(f960,plain,(
% 39.20/5.29    k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) | ~spl3_7),
% 39.20/5.29    inference(avatar_component_clause,[],[f958])).
% 39.20/5.29  fof(f325,plain,(
% 39.20/5.29    ( ! [X10,X8,X9] : (k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(X9,k5_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(k5_xboole_0(X8,k3_xboole_0(X9,k5_xboole_0(X9,X8))),X10))))) = k3_xboole_0(X8,k5_xboole_0(X8,X10))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f314,f305])).
% 39.20/5.29  fof(f314,plain,(
% 39.20/5.29    ( ! [X10,X8,X9] : (k5_xboole_0(X8,k3_xboole_0(X8,X10)) = k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(X9,k5_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(k5_xboole_0(X8,k3_xboole_0(X9,k5_xboole_0(X9,X8))),X10)))))) )),
% 39.20/5.29    inference(backward_demodulation,[],[f173,f305])).
% 39.20/5.29  fof(f173,plain,(
% 39.20/5.29    ( ! [X10,X8,X9] : (k5_xboole_0(X8,k3_xboole_0(X8,X10)) = k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(X9,k5_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X10)))))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f172,f34])).
% 39.20/5.29  fof(f172,plain,(
% 39.20/5.29    ( ! [X10,X8,X9] : (k5_xboole_0(X8,k3_xboole_0(X8,X10)) = k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(k5_xboole_0(X9,k3_xboole_0(X9,X8)),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X10))))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f171,f34])).
% 39.20/5.29  fof(f171,plain,(
% 39.20/5.29    ( ! [X10,X8,X9] : (k3_xboole_0(X8,k5_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X10))) = k5_xboole_0(X8,k3_xboole_0(X8,X10))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f156,f113])).
% 39.20/5.29  fof(f113,plain,(
% 39.20/5.29    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X2))) )),
% 39.20/5.29    inference(superposition,[],[f36,f42])).
% 39.20/5.29  fof(f156,plain,(
% 39.20/5.29    ( ! [X10,X8,X9] : (k3_xboole_0(X8,k5_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X10))) = k5_xboole_0(X8,k3_xboole_0(X8,k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X10)))) )),
% 39.20/5.29    inference(superposition,[],[f49,f42])).
% 39.20/5.29  fof(f42899,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK0,sK1)))))) | spl3_6),
% 39.20/5.29    inference(forward_demodulation,[],[f42898,f806])).
% 39.20/5.29  fof(f806,plain,(
% 39.20/5.29    ( ! [X12,X10,X11] : (k5_xboole_0(X10,k5_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,X11)))) = k3_xboole_0(k5_xboole_0(X10,X11),k5_xboole_0(X10,k5_xboole_0(X11,X12)))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f778,f34])).
% 39.20/5.29  fof(f778,plain,(
% 39.20/5.29    ( ! [X12,X10,X11] : (k5_xboole_0(X10,k5_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,X11)))) = k3_xboole_0(k5_xboole_0(X10,X11),k5_xboole_0(k5_xboole_0(X10,X11),X12))) )),
% 39.20/5.29    inference(superposition,[],[f142,f34])).
% 39.20/5.29  fof(f42898,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)))))) | spl3_6),
% 39.20/5.29    inference(forward_demodulation,[],[f42897,f14151])).
% 39.20/5.29  fof(f42897,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)),sK2)))) | spl3_6),
% 39.20/5.29    inference(forward_demodulation,[],[f42896,f72])).
% 39.20/5.29  fof(f42896,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)))))) | spl3_6),
% 39.20/5.29    inference(forward_demodulation,[],[f42891,f29])).
% 39.20/5.29  fof(f42891,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)))),sK0)) | spl3_6),
% 39.20/5.29    inference(backward_demodulation,[],[f415,f42887])).
% 39.20/5.29  fof(f42887,plain,(
% 39.20/5.29    ( ! [X109,X107,X110,X108] : (k3_xboole_0(X109,k5_xboole_0(X108,k5_xboole_0(X107,k3_xboole_0(X109,X110)))) = k3_xboole_0(k5_xboole_0(X107,k5_xboole_0(X108,X110)),X109)) )),
% 39.20/5.29    inference(forward_demodulation,[],[f42428,f34])).
% 39.20/5.29  fof(f42428,plain,(
% 39.20/5.29    ( ! [X109,X107,X110,X108] : (k3_xboole_0(k5_xboole_0(k5_xboole_0(X107,X108),X110),X109) = k3_xboole_0(X109,k5_xboole_0(X108,k5_xboole_0(X107,k3_xboole_0(X109,X110))))) )),
% 39.20/5.29    inference(superposition,[],[f1286,f67])).
% 39.20/5.29  fof(f1286,plain,(
% 39.20/5.29    ( ! [X10,X8,X9] : (k3_xboole_0(X8,k5_xboole_0(X10,k3_xboole_0(X8,X9))) = k3_xboole_0(k5_xboole_0(X10,X9),X8)) )),
% 39.20/5.29    inference(forward_demodulation,[],[f1285,f129])).
% 39.20/5.29  fof(f1285,plain,(
% 39.20/5.29    ( ! [X10,X8,X9] : (k5_xboole_0(k3_xboole_0(X10,X8),k3_xboole_0(X8,X9)) = k3_xboole_0(X8,k5_xboole_0(X10,k3_xboole_0(X8,X9)))) )),
% 39.20/5.29    inference(forward_demodulation,[],[f1234,f29])).
% 39.20/5.29  fof(f1234,plain,(
% 39.20/5.29    ( ! [X10,X8,X9] : (k5_xboole_0(k3_xboole_0(X10,X8),k3_xboole_0(X8,X9)) = k3_xboole_0(k5_xboole_0(X10,k3_xboole_0(X8,X9)),X8)) )),
% 39.20/5.29    inference(superposition,[],[f129,f82])).
% 39.20/5.29  fof(f415,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2))))))) | spl3_6),
% 39.20/5.29    inference(avatar_component_clause,[],[f413])).
% 39.20/5.29  fof(f6754,plain,(
% 39.20/5.29    spl3_10 | ~spl3_2),
% 39.20/5.29    inference(avatar_split_clause,[],[f774,f100,f6751])).
% 39.20/5.29  fof(f100,plain,(
% 39.20/5.29    spl3_2 <=> sK2 = k3_xboole_0(sK2,sK1)),
% 39.20/5.29    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 39.20/5.29  fof(f774,plain,(
% 39.20/5.29    k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | ~spl3_2),
% 39.20/5.29    inference(superposition,[],[f142,f102])).
% 39.20/5.29  fof(f102,plain,(
% 39.20/5.29    sK2 = k3_xboole_0(sK2,sK1) | ~spl3_2),
% 39.20/5.29    inference(avatar_component_clause,[],[f100])).
% 39.20/5.29  fof(f961,plain,(
% 39.20/5.29    spl3_7 | ~spl3_5),
% 39.20/5.29    inference(avatar_split_clause,[],[f801,f258,f958])).
% 39.20/5.29  fof(f801,plain,(
% 39.20/5.29    k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) | ~spl3_5),
% 39.20/5.29    inference(forward_demodulation,[],[f800,f45])).
% 39.20/5.29  fof(f800,plain,(
% 39.20/5.29    k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) | ~spl3_5),
% 39.20/5.29    inference(forward_demodulation,[],[f773,f28])).
% 39.20/5.29  fof(f773,plain,(
% 39.20/5.29    k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k5_xboole_0(sK2,sK1)) | ~spl3_5),
% 39.20/5.29    inference(superposition,[],[f142,f260])).
% 39.20/5.29  fof(f416,plain,(
% 39.20/5.29    ~spl3_6 | spl3_4),
% 39.20/5.29    inference(avatar_split_clause,[],[f331,f220,f413])).
% 39.20/5.29  fof(f220,plain,(
% 39.20/5.29    spl3_4 <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))))),
% 39.20/5.29    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 39.20/5.29  fof(f331,plain,(
% 39.20/5.29    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2))))))) | spl3_4),
% 39.20/5.29    inference(forward_demodulation,[],[f330,f305])).
% 39.20/5.29  fof(f330,plain,(
% 39.20/5.29    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2))))))) | spl3_4),
% 39.20/5.29    inference(forward_demodulation,[],[f329,f88])).
% 39.20/5.29  fof(f329,plain,(
% 39.20/5.29    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(k5_xboole_0(sK1,sK2),sK0)))))) | spl3_4),
% 39.20/5.29    inference(forward_demodulation,[],[f323,f88])).
% 39.20/5.29  fof(f323,plain,(
% 39.20/5.29    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))))))) | spl3_4),
% 39.20/5.29    inference(backward_demodulation,[],[f222,f305])).
% 39.20/5.29  fof(f222,plain,(
% 39.20/5.29    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) | spl3_4),
% 39.20/5.29    inference(avatar_component_clause,[],[f220])).
% 39.20/5.29  fof(f261,plain,(
% 39.20/5.29    spl3_5 | ~spl3_2),
% 39.20/5.29    inference(avatar_split_clause,[],[f200,f100,f258])).
% 39.20/5.29  fof(f200,plain,(
% 39.20/5.29    sK2 = k3_xboole_0(sK1,sK2) | ~spl3_2),
% 39.20/5.29    inference(superposition,[],[f102,f29])).
% 39.20/5.29  fof(f223,plain,(
% 39.20/5.29    ~spl3_4 | ~spl3_2 | spl3_3),
% 39.20/5.29    inference(avatar_split_clause,[],[f211,f196,f100,f220])).
% 39.20/5.29  fof(f196,plain,(
% 39.20/5.29    spl3_3 <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))))),
% 39.20/5.29    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 39.20/5.29  fof(f211,plain,(
% 39.20/5.29    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) | (~spl3_2 | spl3_3)),
% 39.20/5.29    inference(forward_demodulation,[],[f210,f29])).
% 39.20/5.29  fof(f210,plain,(
% 39.20/5.29    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)))))) | (~spl3_2 | spl3_3)),
% 39.20/5.29    inference(backward_demodulation,[],[f198,f200])).
% 39.20/5.29  fof(f198,plain,(
% 39.20/5.29    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))))) | spl3_3),
% 39.20/5.29    inference(avatar_component_clause,[],[f196])).
% 39.20/5.29  fof(f199,plain,(
% 39.20/5.29    ~spl3_3),
% 39.20/5.29    inference(avatar_split_clause,[],[f48,f196])).
% 39.20/5.29  fof(f48,plain,(
% 39.20/5.29    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))))),
% 39.20/5.29    inference(forward_demodulation,[],[f47,f29])).
% 39.20/5.29  fof(f47,plain,(
% 39.20/5.29    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))))),
% 39.20/5.29    inference(forward_demodulation,[],[f46,f34])).
% 39.20/5.29  fof(f46,plain,(
% 39.20/5.29    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))),
% 39.20/5.29    inference(backward_demodulation,[],[f39,f43])).
% 39.20/5.29  fof(f39,plain,(
% 39.20/5.29    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))),
% 39.20/5.29    inference(definition_unfolding,[],[f23,f32,f38,f32,f32])).
% 39.20/5.29  fof(f23,plain,(
% 39.20/5.29    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 39.20/5.29    inference(cnf_transformation,[],[f21])).
% 39.20/5.29  fof(f21,plain,(
% 39.20/5.29    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1)),
% 39.20/5.29    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f20])).
% 39.20/5.29  fof(f20,plain,(
% 39.20/5.29    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1)) => (k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1))),
% 39.20/5.29    introduced(choice_axiom,[])).
% 39.20/5.29  fof(f18,plain,(
% 39.20/5.29    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1))),
% 39.20/5.29    inference(ennf_transformation,[],[f16])).
% 39.20/5.29  fof(f16,negated_conjecture,(
% 39.20/5.29    ~! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 39.20/5.29    inference(negated_conjecture,[],[f15])).
% 39.20/5.29  fof(f15,conjecture,(
% 39.20/5.29    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 39.20/5.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).
% 39.20/5.29  fof(f103,plain,(
% 39.20/5.29    spl3_2 | ~spl3_1),
% 39.20/5.29    inference(avatar_split_clause,[],[f63,f51,f100])).
% 39.20/5.29  fof(f51,plain,(
% 39.20/5.29    spl3_1 <=> r1_tarski(sK2,sK1)),
% 39.20/5.29    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 39.20/5.29  fof(f63,plain,(
% 39.20/5.29    sK2 = k3_xboole_0(sK2,sK1) | ~spl3_1),
% 39.20/5.29    inference(unit_resulting_resolution,[],[f53,f33])).
% 39.20/5.29  fof(f33,plain,(
% 39.20/5.29    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 39.20/5.29    inference(cnf_transformation,[],[f19])).
% 39.20/5.29  fof(f19,plain,(
% 39.20/5.29    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 39.20/5.29    inference(ennf_transformation,[],[f8])).
% 39.20/5.29  fof(f8,axiom,(
% 39.20/5.29    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 39.20/5.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 39.20/5.29  fof(f53,plain,(
% 39.20/5.29    r1_tarski(sK2,sK1) | ~spl3_1),
% 39.20/5.29    inference(avatar_component_clause,[],[f51])).
% 39.20/5.29  fof(f54,plain,(
% 39.20/5.29    spl3_1),
% 39.20/5.29    inference(avatar_split_clause,[],[f22,f51])).
% 39.20/5.29  fof(f22,plain,(
% 39.20/5.29    r1_tarski(sK2,sK1)),
% 39.20/5.29    inference(cnf_transformation,[],[f21])).
% 39.20/5.29  % SZS output end Proof for theBenchmark
% 39.20/5.29  % (19710)------------------------------
% 39.20/5.29  % (19710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 39.20/5.29  % (19710)Termination reason: Refutation
% 39.20/5.29  
% 39.20/5.29  % (19710)Memory used [KB]: 143792
% 39.20/5.29  % (19710)Time elapsed: 4.827 s
% 39.20/5.29  % (19710)------------------------------
% 39.20/5.29  % (19710)------------------------------
% 39.46/5.30  % (19690)Success in time 4.941 s
%------------------------------------------------------------------------------
