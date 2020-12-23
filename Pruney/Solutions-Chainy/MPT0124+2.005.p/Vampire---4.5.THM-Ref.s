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
% DateTime   : Thu Dec  3 12:32:59 EST 2020

% Result     : Theorem 46.13s
% Output     : Refutation 46.13s
% Verified   : 
% Statistics : Number of formulae       :  206 (1146 expanded)
%              Number of leaves         :   24 ( 394 expanded)
%              Depth                    :   46
%              Number of atoms          :  347 (1321 expanded)
%              Number of equality atoms :  192 (1131 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :   11 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44911,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f94,f182,f206,f257,f411,f955,f7429,f44900,f44910])).

fof(f44910,plain,(
    spl3_12 ),
    inference(avatar_contradiction_clause,[],[f44909])).

fof(f44909,plain,
    ( $false
    | spl3_12 ),
    inference(subsumption_resolution,[],[f44908,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f44908,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,sK2),sK0)
    | spl3_12 ),
    inference(forward_demodulation,[],[f44907,f75])).

fof(f75,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(forward_demodulation,[],[f62,f51])).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f25,f23])).

fof(f23,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f62,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f32,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f38,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f28,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(definition_unfolding,[],[f27,f30,f36])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f44907,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),sK0)
    | spl3_12 ),
    inference(forward_demodulation,[],[f44906,f16548])).

fof(f16548,plain,(
    ! [X43,X41,X44,X42] : k5_xboole_0(X43,k5_xboole_0(X41,k5_xboole_0(X42,X44))) = k5_xboole_0(X43,k5_xboole_0(X42,k5_xboole_0(X44,X41))) ),
    inference(forward_demodulation,[],[f16547,f32])).

fof(f16547,plain,(
    ! [X43,X41,X44,X42] : k5_xboole_0(X43,k5_xboole_0(k5_xboole_0(X41,X42),X44)) = k5_xboole_0(X43,k5_xboole_0(X42,k5_xboole_0(X44,X41))) ),
    inference(forward_demodulation,[],[f16546,f63])).

fof(f63,plain,(
    ! [X6,X4,X5] : k5_xboole_0(X4,k5_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,X4),X6) ),
    inference(superposition,[],[f32,f25])).

fof(f16546,plain,(
    ! [X43,X41,X44,X42] : k5_xboole_0(X43,k5_xboole_0(k5_xboole_0(X41,X42),X44)) = k5_xboole_0(k5_xboole_0(X42,X43),k5_xboole_0(X44,X41)) ),
    inference(forward_demodulation,[],[f16403,f32])).

fof(f16403,plain,(
    ! [X43,X41,X44,X42] : k5_xboole_0(k5_xboole_0(X42,X43),k5_xboole_0(X44,X41)) = k5_xboole_0(k5_xboole_0(X43,k5_xboole_0(X41,X42)),X44) ),
    inference(superposition,[],[f481,f69])).

fof(f69,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8)) ),
    inference(superposition,[],[f32,f25])).

fof(f481,plain,(
    ! [X12,X10,X11] : k5_xboole_0(X12,k5_xboole_0(X10,X11)) = k5_xboole_0(k5_xboole_0(X11,X12),X10) ),
    inference(superposition,[],[f69,f25])).

fof(f44906,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),sK0)
    | spl3_12 ),
    inference(forward_demodulation,[],[f44905,f14914])).

fof(f14914,plain,(
    ! [X132,X133,X131] : k5_xboole_0(X133,k5_xboole_0(X131,X132)) = k5_xboole_0(X133,k5_xboole_0(X132,X131)) ),
    inference(forward_demodulation,[],[f14844,f51])).

fof(f14844,plain,(
    ! [X132,X133,X131] : k5_xboole_0(X133,k5_xboole_0(X131,X132)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X133),k5_xboole_0(X132,X131)) ),
    inference(superposition,[],[f431,f497])).

fof(f497,plain,(
    ! [X37,X38] : k5_xboole_0(X38,X37) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X37,X38)) ),
    inference(superposition,[],[f69,f51])).

fof(f431,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X9,X10) = k5_xboole_0(k5_xboole_0(X8,X9),k5_xboole_0(X8,X10)) ),
    inference(superposition,[],[f63,f75])).

fof(f44905,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK2,sK1),sK1)),sK0)
    | spl3_12 ),
    inference(forward_demodulation,[],[f44904,f69])).

fof(f44904,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK2,sK1))),sK0)
    | spl3_12 ),
    inference(forward_demodulation,[],[f44903,f455])).

fof(f455,plain,(
    ! [X28,X26,X27,X25] : k5_xboole_0(X27,k5_xboole_0(X26,k5_xboole_0(X25,X28))) = k5_xboole_0(X27,k5_xboole_0(X25,k5_xboole_0(X26,X28))) ),
    inference(forward_demodulation,[],[f454,f32])).

fof(f454,plain,(
    ! [X28,X26,X27,X25] : k5_xboole_0(X27,k5_xboole_0(k5_xboole_0(X25,X26),X28)) = k5_xboole_0(X27,k5_xboole_0(X26,k5_xboole_0(X25,X28))) ),
    inference(forward_demodulation,[],[f436,f453])).

fof(f453,plain,(
    ! [X24,X23,X21,X22] : k5_xboole_0(k5_xboole_0(X22,k5_xboole_0(X21,X23)),X24) = k5_xboole_0(X23,k5_xboole_0(X21,k5_xboole_0(X22,X24))) ),
    inference(forward_demodulation,[],[f435,f32])).

fof(f435,plain,(
    ! [X24,X23,X21,X22] : k5_xboole_0(X23,k5_xboole_0(k5_xboole_0(X21,X22),X24)) = k5_xboole_0(k5_xboole_0(X22,k5_xboole_0(X21,X23)),X24) ),
    inference(superposition,[],[f63,f63])).

fof(f436,plain,(
    ! [X28,X26,X27,X25] : k5_xboole_0(X27,k5_xboole_0(k5_xboole_0(X25,X26),X28)) = k5_xboole_0(k5_xboole_0(X25,k5_xboole_0(X26,X27)),X28) ),
    inference(superposition,[],[f63,f32])).

fof(f44903,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))),sK0)
    | spl3_12 ),
    inference(forward_demodulation,[],[f44902,f69])).

fof(f44902,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)),sK0)
    | spl3_12 ),
    inference(forward_demodulation,[],[f44901,f69])).

fof(f44901,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)),sK0)
    | spl3_12 ),
    inference(superposition,[],[f44899,f1108])).

fof(f1108,plain,(
    ! [X4,X2,X3] : k3_xboole_0(k5_xboole_0(X4,X2),X3) = k5_xboole_0(k3_xboole_0(X3,X4),k3_xboole_0(X3,X2)) ),
    inference(superposition,[],[f115,f26])).

fof(f115,plain,(
    ! [X4,X2,X3] : k3_xboole_0(k5_xboole_0(X2,X4),X3) = k5_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(X4,X3)) ),
    inference(superposition,[],[f35,f26])).

fof(f35,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f44899,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f44897])).

fof(f44897,plain,
    ( spl3_12
  <=> k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) = k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f44900,plain,
    ( ~ spl3_12
    | ~ spl3_5
    | spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f44578,f7426,f952,f408,f254,f44897])).

fof(f254,plain,
    ( spl3_5
  <=> sK2 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f408,plain,
    ( spl3_6
  <=> k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) = k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f952,plain,
    ( spl3_7
  <=> k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f7426,plain,
    ( spl3_10
  <=> k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f44578,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | ~ spl3_5
    | spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f44577,f78])).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f34,f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f44577,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))))
    | ~ spl3_5
    | spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f44576,f51])).

fof(f44576,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(k1_xboole_0,sK0),k5_xboole_0(sK1,sK2))))
    | ~ spl3_5
    | spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f44575,f2153])).

fof(f2153,plain,(
    ! [X12,X10,X11] : k3_xboole_0(X11,k3_xboole_0(k5_xboole_0(X11,X10),X12)) = k3_xboole_0(X11,k3_xboole_0(k5_xboole_0(X10,X11),X12)) ),
    inference(backward_demodulation,[],[f997,f2152])).

fof(f2152,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X1,X2),X0) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X0))) ),
    inference(forward_demodulation,[],[f2151,f35])).

fof(f2151,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X0))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X2,X0)) ),
    inference(forward_demodulation,[],[f2084,f26])).

fof(f2084,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X2,X0)) = k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X0)),X0) ),
    inference(superposition,[],[f123,f24])).

fof(f123,plain,(
    ! [X14,X12,X13,X11] : k3_xboole_0(k5_xboole_0(X14,k3_xboole_0(X11,X12)),X13) = k5_xboole_0(k3_xboole_0(X14,X13),k3_xboole_0(X11,k3_xboole_0(X12,X13))) ),
    inference(superposition,[],[f35,f34])).

fof(f997,plain,(
    ! [X12,X10,X11] : k3_xboole_0(X11,k3_xboole_0(k5_xboole_0(X11,X10),X12)) = k3_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,k3_xboole_0(X11,X12)))) ),
    inference(forward_demodulation,[],[f996,f34])).

fof(f996,plain,(
    ! [X12,X10,X11] : k3_xboole_0(k3_xboole_0(X11,k5_xboole_0(X11,X10)),X12) = k3_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,k3_xboole_0(X11,X12)))) ),
    inference(forward_demodulation,[],[f995,f132])).

fof(f132,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f114,f26])).

fof(f114,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f35,f24])).

fof(f995,plain,(
    ! [X12,X10,X11] : k3_xboole_0(k5_xboole_0(X11,k3_xboole_0(X10,X11)),X12) = k3_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,k3_xboole_0(X11,X12)))) ),
    inference(forward_demodulation,[],[f994,f25])).

fof(f994,plain,(
    ! [X12,X10,X11] : k3_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,k3_xboole_0(X11,X12)))) = k3_xboole_0(k5_xboole_0(k3_xboole_0(X10,X11),X11),X12) ),
    inference(forward_demodulation,[],[f993,f115])).

fof(f993,plain,(
    ! [X12,X10,X11] : k5_xboole_0(k3_xboole_0(X12,k3_xboole_0(X10,X11)),k3_xboole_0(X11,X12)) = k3_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,k3_xboole_0(X11,X12)))) ),
    inference(forward_demodulation,[],[f961,f34])).

fof(f961,plain,(
    ! [X12,X10,X11] : k5_xboole_0(k3_xboole_0(X12,k3_xboole_0(X10,X11)),k3_xboole_0(X11,X12)) = k3_xboole_0(k3_xboole_0(X11,X12),k5_xboole_0(X10,k3_xboole_0(X11,X12))) ),
    inference(superposition,[],[f137,f83])).

fof(f83,plain,(
    ! [X6,X7,X5] : k3_xboole_0(X5,k3_xboole_0(X6,X7)) = k3_xboole_0(X7,k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f34,f26])).

fof(f137,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(X1,X0),X0) = k3_xboole_0(X0,k5_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f119,f26])).

fof(f119,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(X1,X0),X0) = k3_xboole_0(k5_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f35,f24])).

fof(f44575,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(sK1,sK2))))
    | ~ spl3_5
    | spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f44574,f17771])).

fof(f17771,plain,(
    ! [X14,X15,X16] : k3_xboole_0(X15,k3_xboole_0(X14,X16)) = k3_xboole_0(X15,k3_xboole_0(X16,X14)) ),
    inference(superposition,[],[f565,f83])).

fof(f565,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,k3_xboole_0(X4,X5)) = k3_xboole_0(X4,k3_xboole_0(X3,X5)) ),
    inference(superposition,[],[f79,f34])).

fof(f79,plain,(
    ! [X4,X2,X3] : k3_xboole_0(X2,k3_xboole_0(X3,X4)) = k3_xboole_0(k3_xboole_0(X3,X2),X4) ),
    inference(superposition,[],[f34,f26])).

fof(f44574,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k1_xboole_0))))
    | ~ spl3_5
    | spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f44573,f41])).

fof(f44573,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)))))
    | ~ spl3_5
    | spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f44572,f69])).

fof(f44572,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))))
    | ~ spl3_5
    | spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f44571,f17771])).

fof(f44571,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2))))
    | ~ spl3_5
    | spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f44570,f18088])).

fof(f18088,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,X76),k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,X76)))
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f6691,f17760])).

fof(f17760,plain,
    ( ! [X113] : k3_xboole_0(X113,k5_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k3_xboole_0(X113,k5_xboole_0(sK1,sK2)))
    | ~ spl3_10 ),
    inference(superposition,[],[f565,f7428])).

fof(f7428,plain,
    ( k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f7426])).

fof(f6691,plain,
    ( ! [X76] : k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,X76),k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,X76)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6690,f32])).

fof(f6690,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,X76),k5_xboole_0(sK1,sK2)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6689,f83])).

fof(f6689,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,k5_xboole_0(sK1,X76)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6688,f301])).

fof(f301,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f157,f300])).

fof(f300,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f299,f26])).

fof(f299,plain,(
    ! [X0,X1] : k3_xboole_0(k5_xboole_0(X0,X1),X0) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f288,f120])).

fof(f120,plain,(
    ! [X4,X2,X3] : k3_xboole_0(k5_xboole_0(X4,X2),X3) = k5_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(X3,X2)) ),
    inference(superposition,[],[f35,f26])).

fof(f288,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f45,f78])).

fof(f45,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) ),
    inference(backward_demodulation,[],[f40,f34])).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f33,f30,f30])).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f157,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f142,f78])).

fof(f142,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f45,f24])).

fof(f6688,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,X76)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6687,f51])).

fof(f6687,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(k1_xboole_0,sK1),X76)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6686,f1415])).

fof(f1415,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k5_xboole_0(X3,X5),X4) = k3_xboole_0(k5_xboole_0(X5,X3),X4) ),
    inference(superposition,[],[f125,f35])).

fof(f125,plain,(
    ! [X6,X7,X5] : k3_xboole_0(k5_xboole_0(X5,X7),X6) = k5_xboole_0(k3_xboole_0(X7,X6),k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f35,f25])).

fof(f6686,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k1_xboole_0),X76)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6685,f138])).

fof(f138,plain,(
    ! [X4] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X4) ),
    inference(forward_demodulation,[],[f124,f41])).

fof(f124,plain,(
    ! [X4,X3] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X3,X3),X4) ),
    inference(superposition,[],[f35,f41])).

fof(f6685,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)),X76)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6684,f26])).

fof(f6684,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0)),X76)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6683,f41])).

fof(f6683,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,k5_xboole_0(sK1,sK1))),X76)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6682,f421])).

fof(f421,plain,
    ( ! [X2] : k3_xboole_0(sK2,k5_xboole_0(X2,sK2)) = k3_xboole_0(sK2,k5_xboole_0(X2,sK1))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f420,f26])).

fof(f420,plain,
    ( ! [X2] : k3_xboole_0(k5_xboole_0(X2,sK1),sK2) = k3_xboole_0(sK2,k5_xboole_0(X2,sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f414,f137])).

fof(f414,plain,
    ( ! [X2] : k3_xboole_0(k5_xboole_0(X2,sK1),sK2) = k5_xboole_0(k3_xboole_0(X2,sK2),sK2)
    | ~ spl3_5 ),
    inference(superposition,[],[f35,f256])).

fof(f256,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f254])).

fof(f6682,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))),X76)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6681,f26])).

fof(f6681,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,sK2),sK2)),X76)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6680,f75])).

fof(f6680,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),sK2)))),X76)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6679,f69])).

fof(f6679,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK2),sK2),sK2))),X76)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6678,f25])).

fof(f6678,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK2),sK2),sK2),sK2)),X76)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6677,f69])).

fof(f6677,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK2),sK2),sK2))),X76)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6676,f455])).

fof(f6676,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK2),sK2),k5_xboole_0(sK1,sK2))),X76)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6675,f777])).

fof(f777,plain,(
    ! [X12,X10,X11] : k5_xboole_0(X10,k5_xboole_0(k3_xboole_0(X11,X10),X12)) = k5_xboole_0(X12,k3_xboole_0(X10,k5_xboole_0(X10,X11))) ),
    inference(superposition,[],[f69,f132])).

fof(f6675,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X76)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6674,f25])).

fof(f6674,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X76),sK1))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6673,f51])).

fof(f6673,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X76),sK1)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6672,f69])).

fof(f6672,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X76))))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6671,f75])).

fof(f6671,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X76))))))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6670,f69])).

fof(f6670,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X76)),sK2))))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6669,f25])).

fof(f6669,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X76)),sK2),sK2)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6668,f69])).

fof(f6668,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X76)),sK2))))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6667,f455])).

fof(f6667,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X76)),k5_xboole_0(sK1,sK2))))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f6288,f69])).

fof(f6288,plain,
    ( ! [X76] : k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X76)))))
    | ~ spl3_7 ),
    inference(superposition,[],[f321,f954])).

fof(f954,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f952])).

fof(f321,plain,(
    ! [X10,X8,X9] : k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(X9,k5_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(k5_xboole_0(X8,k3_xboole_0(X9,k5_xboole_0(X9,X8))),X10))))) = k3_xboole_0(X8,k5_xboole_0(X8,X10)) ),
    inference(forward_demodulation,[],[f310,f301])).

fof(f310,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X8,k3_xboole_0(X8,X10)) = k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(X9,k5_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(k5_xboole_0(X8,k3_xboole_0(X9,k5_xboole_0(X9,X8))),X10))))) ),
    inference(backward_demodulation,[],[f160,f301])).

fof(f160,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X8,k3_xboole_0(X8,X10)) = k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(X9,k5_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X10))))) ),
    inference(forward_demodulation,[],[f159,f32])).

fof(f159,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X8,k3_xboole_0(X8,X10)) = k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(k5_xboole_0(X9,k3_xboole_0(X9,X8)),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X10)))) ),
    inference(forward_demodulation,[],[f158,f32])).

fof(f158,plain,(
    ! [X10,X8,X9] : k3_xboole_0(X8,k5_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X10))) = k5_xboole_0(X8,k3_xboole_0(X8,X10)) ),
    inference(forward_demodulation,[],[f145,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X2)) ),
    inference(superposition,[],[f34,f39])).

fof(f145,plain,(
    ! [X10,X8,X9] : k3_xboole_0(X8,k5_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X10))) = k5_xboole_0(X8,k3_xboole_0(X8,k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X10))) ),
    inference(superposition,[],[f45,f39])).

fof(f44570,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))))))
    | spl3_6 ),
    inference(forward_demodulation,[],[f44569,f801])).

fof(f801,plain,(
    ! [X12,X10,X11] : k5_xboole_0(X10,k5_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,X11)))) = k3_xboole_0(k5_xboole_0(X10,X11),k5_xboole_0(X10,k5_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f773,f32])).

fof(f773,plain,(
    ! [X12,X10,X11] : k5_xboole_0(X10,k5_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,X11)))) = k3_xboole_0(k5_xboole_0(X10,X11),k5_xboole_0(k5_xboole_0(X10,X11),X12)) ),
    inference(superposition,[],[f132,f32])).

fof(f44569,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2))))))
    | spl3_6 ),
    inference(forward_demodulation,[],[f44568,f14914])).

fof(f44568,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)),sK2))))
    | spl3_6 ),
    inference(forward_demodulation,[],[f44567,f69])).

fof(f44567,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2))))))
    | spl3_6 ),
    inference(forward_demodulation,[],[f44562,f26])).

fof(f44562,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)))),sK0))
    | spl3_6 ),
    inference(backward_demodulation,[],[f410,f44558])).

fof(f44558,plain,(
    ! [X109,X107,X110,X108] : k3_xboole_0(X109,k5_xboole_0(X108,k5_xboole_0(X107,k3_xboole_0(X109,X110)))) = k3_xboole_0(k5_xboole_0(X107,k5_xboole_0(X108,X110)),X109) ),
    inference(forward_demodulation,[],[f44097,f32])).

fof(f44097,plain,(
    ! [X109,X107,X110,X108] : k3_xboole_0(k5_xboole_0(k5_xboole_0(X107,X108),X110),X109) = k3_xboole_0(X109,k5_xboole_0(X108,k5_xboole_0(X107,k3_xboole_0(X109,X110)))) ),
    inference(superposition,[],[f1280,f63])).

fof(f1280,plain,(
    ! [X10,X8,X9] : k3_xboole_0(X8,k5_xboole_0(X10,k3_xboole_0(X8,X9))) = k3_xboole_0(k5_xboole_0(X10,X9),X8) ),
    inference(forward_demodulation,[],[f1279,f120])).

fof(f1279,plain,(
    ! [X10,X8,X9] : k5_xboole_0(k3_xboole_0(X10,X8),k3_xboole_0(X8,X9)) = k3_xboole_0(X8,k5_xboole_0(X10,k3_xboole_0(X8,X9))) ),
    inference(forward_demodulation,[],[f1228,f26])).

fof(f1228,plain,(
    ! [X10,X8,X9] : k5_xboole_0(k3_xboole_0(X10,X8),k3_xboole_0(X8,X9)) = k3_xboole_0(k5_xboole_0(X10,k3_xboole_0(X8,X9)),X8) ),
    inference(superposition,[],[f120,f78])).

fof(f410,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)))))))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f408])).

fof(f7429,plain,
    ( spl3_10
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f769,f91,f7426])).

fof(f91,plain,
    ( spl3_2
  <=> sK2 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f769,plain,
    ( k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(superposition,[],[f132,f93])).

fof(f93,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f955,plain,
    ( spl3_7
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f796,f254,f952])).

fof(f796,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f795,f41])).

fof(f795,plain,
    ( k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f768,f25])).

fof(f768,plain,
    ( k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k5_xboole_0(sK2,sK1))
    | ~ spl3_5 ),
    inference(superposition,[],[f132,f256])).

fof(f411,plain,
    ( ~ spl3_6
    | spl3_4 ),
    inference(avatar_split_clause,[],[f327,f203,f408])).

fof(f203,plain,
    ( spl3_4
  <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f327,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)))))))
    | spl3_4 ),
    inference(forward_demodulation,[],[f326,f301])).

fof(f326,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)))))))
    | spl3_4 ),
    inference(forward_demodulation,[],[f325,f83])).

fof(f325,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(k5_xboole_0(sK1,sK2),sK0))))))
    | spl3_4 ),
    inference(forward_demodulation,[],[f319,f83])).

fof(f319,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)))))))
    | spl3_4 ),
    inference(backward_demodulation,[],[f205,f301])).

fof(f205,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f203])).

fof(f257,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f183,f91,f254])).

fof(f183,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(superposition,[],[f93,f26])).

fof(f206,plain,
    ( ~ spl3_4
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f194,f179,f91,f203])).

fof(f179,plain,
    ( spl3_3
  <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f194,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))))
    | ~ spl3_2
    | spl3_3 ),
    inference(forward_demodulation,[],[f193,f26])).

fof(f193,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2))))))
    | ~ spl3_2
    | spl3_3 ),
    inference(backward_demodulation,[],[f181,f183])).

fof(f181,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f179])).

fof(f182,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f44,f179])).

fof(f44,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))))) ),
    inference(forward_demodulation,[],[f43,f26])).

fof(f43,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) ),
    inference(forward_demodulation,[],[f42,f32])).

fof(f42,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))) ),
    inference(backward_demodulation,[],[f37,f40])).

fof(f37,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))) ),
    inference(definition_unfolding,[],[f22,f30,f36,f30,f30])).

fof(f22,plain,(
    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    & r1_tarski(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
        & r1_tarski(X2,X1) )
   => ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).

fof(f94,plain,
    ( spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f59,f47,f91])).

fof(f47,plain,
    ( spl3_1
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f59,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f49,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f49,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f50,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:31:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (7588)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.46  % (7589)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.47  % (7584)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (7585)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (7583)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (7591)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (7586)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (7592)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (7582)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (7596)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.50  % (7590)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (7587)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (7593)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.51  % (7581)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.51  % (7594)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.51  % (7597)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.51  % (7595)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.53  % (7598)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 4.87/1.02  % (7585)Time limit reached!
% 4.87/1.02  % (7585)------------------------------
% 4.87/1.02  % (7585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.87/1.02  % (7585)Termination reason: Time limit
% 4.87/1.02  % (7585)Termination phase: Saturation
% 4.87/1.02  
% 4.87/1.02  % (7585)Memory used [KB]: 16247
% 4.87/1.02  % (7585)Time elapsed: 0.600 s
% 4.87/1.02  % (7585)------------------------------
% 4.87/1.02  % (7585)------------------------------
% 12.49/1.93  % (7586)Time limit reached!
% 12.49/1.93  % (7586)------------------------------
% 12.49/1.93  % (7586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.49/1.93  % (7586)Termination reason: Time limit
% 12.49/1.93  % (7586)Termination phase: Saturation
% 12.49/1.93  
% 12.49/1.93  % (7586)Memory used [KB]: 28272
% 12.49/1.93  % (7586)Time elapsed: 1.500 s
% 12.49/1.93  % (7586)------------------------------
% 12.49/1.93  % (7586)------------------------------
% 12.89/2.00  % (7587)Time limit reached!
% 12.89/2.00  % (7587)------------------------------
% 12.89/2.00  % (7587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.89/2.00  % (7587)Termination reason: Time limit
% 12.89/2.00  % (7587)Termination phase: Saturation
% 12.89/2.00  
% 12.89/2.00  % (7587)Memory used [KB]: 39018
% 12.89/2.00  % (7587)Time elapsed: 1.500 s
% 12.89/2.00  % (7587)------------------------------
% 12.89/2.00  % (7587)------------------------------
% 14.33/2.22  % (7583)Time limit reached!
% 14.33/2.22  % (7583)------------------------------
% 14.33/2.22  % (7583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.33/2.22  % (7583)Termination reason: Time limit
% 14.33/2.22  % (7583)Termination phase: Saturation
% 14.33/2.22  
% 14.33/2.22  % (7583)Memory used [KB]: 39274
% 14.33/2.22  % (7583)Time elapsed: 1.800 s
% 14.33/2.22  % (7583)------------------------------
% 14.33/2.22  % (7583)------------------------------
% 18.25/2.65  % (7593)Time limit reached!
% 18.25/2.65  % (7593)------------------------------
% 18.25/2.65  % (7593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.25/2.65  % (7593)Termination reason: Time limit
% 18.25/2.65  % (7593)Termination phase: Saturation
% 18.25/2.65  
% 18.25/2.65  % (7593)Memory used [KB]: 44263
% 18.25/2.65  % (7593)Time elapsed: 2.200 s
% 18.25/2.65  % (7593)------------------------------
% 18.25/2.65  % (7593)------------------------------
% 46.13/6.16  % (7596)Refutation found. Thanks to Tanya!
% 46.13/6.16  % SZS status Theorem for theBenchmark
% 46.13/6.16  % SZS output start Proof for theBenchmark
% 46.13/6.16  fof(f44911,plain,(
% 46.13/6.16    $false),
% 46.13/6.16    inference(avatar_sat_refutation,[],[f50,f94,f182,f206,f257,f411,f955,f7429,f44900,f44910])).
% 46.13/6.16  fof(f44910,plain,(
% 46.13/6.16    spl3_12),
% 46.13/6.16    inference(avatar_contradiction_clause,[],[f44909])).
% 46.13/6.16  fof(f44909,plain,(
% 46.13/6.16    $false | spl3_12),
% 46.13/6.16    inference(subsumption_resolution,[],[f44908,f26])).
% 46.13/6.16  fof(f26,plain,(
% 46.13/6.16    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 46.13/6.16    inference(cnf_transformation,[],[f1])).
% 46.13/6.16  fof(f1,axiom,(
% 46.13/6.16    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 46.13/6.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 46.13/6.16  fof(f44908,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,sK2),sK0) | spl3_12),
% 46.13/6.16    inference(forward_demodulation,[],[f44907,f75])).
% 46.13/6.16  fof(f75,plain,(
% 46.13/6.16    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 46.13/6.16    inference(forward_demodulation,[],[f62,f51])).
% 46.13/6.16  fof(f51,plain,(
% 46.13/6.16    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 46.13/6.16    inference(superposition,[],[f25,f23])).
% 46.13/6.16  fof(f23,plain,(
% 46.13/6.16    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 46.13/6.16    inference(cnf_transformation,[],[f11])).
% 46.13/6.16  fof(f11,axiom,(
% 46.13/6.16    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 46.13/6.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 46.13/6.16  fof(f25,plain,(
% 46.13/6.16    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 46.13/6.16    inference(cnf_transformation,[],[f2])).
% 46.13/6.16  fof(f2,axiom,(
% 46.13/6.16    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 46.13/6.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 46.13/6.16  fof(f62,plain,(
% 46.13/6.16    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 46.13/6.16    inference(superposition,[],[f32,f41])).
% 46.13/6.16  fof(f41,plain,(
% 46.13/6.16    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 46.13/6.16    inference(backward_demodulation,[],[f38,f39])).
% 46.13/6.16  fof(f39,plain,(
% 46.13/6.16    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 46.13/6.16    inference(definition_unfolding,[],[f28,f36])).
% 46.13/6.16  fof(f36,plain,(
% 46.13/6.16    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 46.13/6.16    inference(definition_unfolding,[],[f29,f30])).
% 46.13/6.16  fof(f30,plain,(
% 46.13/6.16    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 46.13/6.16    inference(cnf_transformation,[],[f4])).
% 46.13/6.16  fof(f4,axiom,(
% 46.13/6.16    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 46.13/6.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 46.13/6.16  fof(f29,plain,(
% 46.13/6.16    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 46.13/6.16    inference(cnf_transformation,[],[f13])).
% 46.13/6.16  fof(f13,axiom,(
% 46.13/6.16    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 46.13/6.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 46.13/6.16  fof(f28,plain,(
% 46.13/6.16    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 46.13/6.16    inference(cnf_transformation,[],[f7])).
% 46.13/6.16  fof(f7,axiom,(
% 46.13/6.16    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 46.13/6.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 46.13/6.16  fof(f38,plain,(
% 46.13/6.16    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 46.13/6.16    inference(definition_unfolding,[],[f27,f30,f36])).
% 46.13/6.16  fof(f27,plain,(
% 46.13/6.16    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 46.13/6.16    inference(cnf_transformation,[],[f9])).
% 46.13/6.16  fof(f9,axiom,(
% 46.13/6.16    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 46.13/6.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 46.13/6.16  fof(f32,plain,(
% 46.13/6.16    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 46.13/6.16    inference(cnf_transformation,[],[f12])).
% 46.13/6.16  fof(f12,axiom,(
% 46.13/6.16    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 46.13/6.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 46.13/6.16  fof(f44907,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),sK0) | spl3_12),
% 46.13/6.16    inference(forward_demodulation,[],[f44906,f16548])).
% 46.13/6.16  fof(f16548,plain,(
% 46.13/6.16    ( ! [X43,X41,X44,X42] : (k5_xboole_0(X43,k5_xboole_0(X41,k5_xboole_0(X42,X44))) = k5_xboole_0(X43,k5_xboole_0(X42,k5_xboole_0(X44,X41)))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f16547,f32])).
% 46.13/6.16  fof(f16547,plain,(
% 46.13/6.16    ( ! [X43,X41,X44,X42] : (k5_xboole_0(X43,k5_xboole_0(k5_xboole_0(X41,X42),X44)) = k5_xboole_0(X43,k5_xboole_0(X42,k5_xboole_0(X44,X41)))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f16546,f63])).
% 46.13/6.16  fof(f63,plain,(
% 46.13/6.16    ( ! [X6,X4,X5] : (k5_xboole_0(X4,k5_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,X4),X6)) )),
% 46.13/6.16    inference(superposition,[],[f32,f25])).
% 46.13/6.16  fof(f16546,plain,(
% 46.13/6.16    ( ! [X43,X41,X44,X42] : (k5_xboole_0(X43,k5_xboole_0(k5_xboole_0(X41,X42),X44)) = k5_xboole_0(k5_xboole_0(X42,X43),k5_xboole_0(X44,X41))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f16403,f32])).
% 46.13/6.16  fof(f16403,plain,(
% 46.13/6.16    ( ! [X43,X41,X44,X42] : (k5_xboole_0(k5_xboole_0(X42,X43),k5_xboole_0(X44,X41)) = k5_xboole_0(k5_xboole_0(X43,k5_xboole_0(X41,X42)),X44)) )),
% 46.13/6.16    inference(superposition,[],[f481,f69])).
% 46.13/6.16  fof(f69,plain,(
% 46.13/6.16    ( ! [X8,X7,X9] : (k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8))) )),
% 46.13/6.16    inference(superposition,[],[f32,f25])).
% 46.13/6.16  fof(f481,plain,(
% 46.13/6.16    ( ! [X12,X10,X11] : (k5_xboole_0(X12,k5_xboole_0(X10,X11)) = k5_xboole_0(k5_xboole_0(X11,X12),X10)) )),
% 46.13/6.16    inference(superposition,[],[f69,f25])).
% 46.13/6.16  fof(f44906,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),sK0) | spl3_12),
% 46.13/6.16    inference(forward_demodulation,[],[f44905,f14914])).
% 46.13/6.16  fof(f14914,plain,(
% 46.13/6.16    ( ! [X132,X133,X131] : (k5_xboole_0(X133,k5_xboole_0(X131,X132)) = k5_xboole_0(X133,k5_xboole_0(X132,X131))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f14844,f51])).
% 46.13/6.16  fof(f14844,plain,(
% 46.13/6.16    ( ! [X132,X133,X131] : (k5_xboole_0(X133,k5_xboole_0(X131,X132)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X133),k5_xboole_0(X132,X131))) )),
% 46.13/6.16    inference(superposition,[],[f431,f497])).
% 46.13/6.16  fof(f497,plain,(
% 46.13/6.16    ( ! [X37,X38] : (k5_xboole_0(X38,X37) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X37,X38))) )),
% 46.13/6.16    inference(superposition,[],[f69,f51])).
% 46.13/6.16  fof(f431,plain,(
% 46.13/6.16    ( ! [X10,X8,X9] : (k5_xboole_0(X9,X10) = k5_xboole_0(k5_xboole_0(X8,X9),k5_xboole_0(X8,X10))) )),
% 46.13/6.16    inference(superposition,[],[f63,f75])).
% 46.13/6.16  fof(f44905,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK2,sK1),sK1)),sK0) | spl3_12),
% 46.13/6.16    inference(forward_demodulation,[],[f44904,f69])).
% 46.13/6.16  fof(f44904,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK2,sK1))),sK0) | spl3_12),
% 46.13/6.16    inference(forward_demodulation,[],[f44903,f455])).
% 46.13/6.16  fof(f455,plain,(
% 46.13/6.16    ( ! [X28,X26,X27,X25] : (k5_xboole_0(X27,k5_xboole_0(X26,k5_xboole_0(X25,X28))) = k5_xboole_0(X27,k5_xboole_0(X25,k5_xboole_0(X26,X28)))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f454,f32])).
% 46.13/6.16  fof(f454,plain,(
% 46.13/6.16    ( ! [X28,X26,X27,X25] : (k5_xboole_0(X27,k5_xboole_0(k5_xboole_0(X25,X26),X28)) = k5_xboole_0(X27,k5_xboole_0(X26,k5_xboole_0(X25,X28)))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f436,f453])).
% 46.13/6.16  fof(f453,plain,(
% 46.13/6.16    ( ! [X24,X23,X21,X22] : (k5_xboole_0(k5_xboole_0(X22,k5_xboole_0(X21,X23)),X24) = k5_xboole_0(X23,k5_xboole_0(X21,k5_xboole_0(X22,X24)))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f435,f32])).
% 46.13/6.16  fof(f435,plain,(
% 46.13/6.16    ( ! [X24,X23,X21,X22] : (k5_xboole_0(X23,k5_xboole_0(k5_xboole_0(X21,X22),X24)) = k5_xboole_0(k5_xboole_0(X22,k5_xboole_0(X21,X23)),X24)) )),
% 46.13/6.16    inference(superposition,[],[f63,f63])).
% 46.13/6.16  fof(f436,plain,(
% 46.13/6.16    ( ! [X28,X26,X27,X25] : (k5_xboole_0(X27,k5_xboole_0(k5_xboole_0(X25,X26),X28)) = k5_xboole_0(k5_xboole_0(X25,k5_xboole_0(X26,X27)),X28)) )),
% 46.13/6.16    inference(superposition,[],[f63,f32])).
% 46.13/6.16  fof(f44903,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))),sK0) | spl3_12),
% 46.13/6.16    inference(forward_demodulation,[],[f44902,f69])).
% 46.13/6.16  fof(f44902,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)),sK0) | spl3_12),
% 46.13/6.16    inference(forward_demodulation,[],[f44901,f69])).
% 46.13/6.16  fof(f44901,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)),sK0) | spl3_12),
% 46.13/6.16    inference(superposition,[],[f44899,f1108])).
% 46.13/6.16  fof(f1108,plain,(
% 46.13/6.16    ( ! [X4,X2,X3] : (k3_xboole_0(k5_xboole_0(X4,X2),X3) = k5_xboole_0(k3_xboole_0(X3,X4),k3_xboole_0(X3,X2))) )),
% 46.13/6.16    inference(superposition,[],[f115,f26])).
% 46.13/6.16  fof(f115,plain,(
% 46.13/6.16    ( ! [X4,X2,X3] : (k3_xboole_0(k5_xboole_0(X2,X4),X3) = k5_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(X4,X3))) )),
% 46.13/6.16    inference(superposition,[],[f35,f26])).
% 46.13/6.16  fof(f35,plain,(
% 46.13/6.16    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 46.13/6.16    inference(cnf_transformation,[],[f5])).
% 46.13/6.16  fof(f5,axiom,(
% 46.13/6.16    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 46.13/6.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 46.13/6.16  fof(f44899,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))) | spl3_12),
% 46.13/6.16    inference(avatar_component_clause,[],[f44897])).
% 46.13/6.16  fof(f44897,plain,(
% 46.13/6.16    spl3_12 <=> k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) = k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)))),
% 46.13/6.16    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 46.13/6.16  fof(f44900,plain,(
% 46.13/6.16    ~spl3_12 | ~spl3_5 | spl3_6 | ~spl3_7 | ~spl3_10),
% 46.13/6.16    inference(avatar_split_clause,[],[f44578,f7426,f952,f408,f254,f44897])).
% 46.13/6.16  fof(f254,plain,(
% 46.13/6.16    spl3_5 <=> sK2 = k3_xboole_0(sK1,sK2)),
% 46.13/6.16    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 46.13/6.16  fof(f408,plain,(
% 46.13/6.16    spl3_6 <=> k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) = k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)))))))),
% 46.13/6.16    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 46.13/6.16  fof(f952,plain,(
% 46.13/6.16    spl3_7 <=> k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))),
% 46.13/6.16    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 46.13/6.16  fof(f7426,plain,(
% 46.13/6.16    spl3_10 <=> k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))),
% 46.13/6.16    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 46.13/6.16  fof(f44578,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))) | (~spl3_5 | spl3_6 | ~spl3_7 | ~spl3_10)),
% 46.13/6.16    inference(forward_demodulation,[],[f44577,f78])).
% 46.13/6.16  fof(f78,plain,(
% 46.13/6.16    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 46.13/6.16    inference(superposition,[],[f34,f24])).
% 46.13/6.16  fof(f24,plain,(
% 46.13/6.16    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 46.13/6.16    inference(cnf_transformation,[],[f16])).
% 46.13/6.16  fof(f16,plain,(
% 46.13/6.16    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 46.13/6.16    inference(rectify,[],[f3])).
% 46.13/6.16  fof(f3,axiom,(
% 46.13/6.16    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 46.13/6.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 46.13/6.16  fof(f34,plain,(
% 46.13/6.16    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 46.13/6.16    inference(cnf_transformation,[],[f6])).
% 46.13/6.16  fof(f6,axiom,(
% 46.13/6.16    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 46.13/6.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 46.13/6.16  fof(f44577,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)))) | (~spl3_5 | spl3_6 | ~spl3_7 | ~spl3_10)),
% 46.13/6.16    inference(forward_demodulation,[],[f44576,f51])).
% 46.13/6.16  fof(f44576,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(k1_xboole_0,sK0),k5_xboole_0(sK1,sK2)))) | (~spl3_5 | spl3_6 | ~spl3_7 | ~spl3_10)),
% 46.13/6.16    inference(forward_demodulation,[],[f44575,f2153])).
% 46.13/6.16  fof(f2153,plain,(
% 46.13/6.16    ( ! [X12,X10,X11] : (k3_xboole_0(X11,k3_xboole_0(k5_xboole_0(X11,X10),X12)) = k3_xboole_0(X11,k3_xboole_0(k5_xboole_0(X10,X11),X12))) )),
% 46.13/6.16    inference(backward_demodulation,[],[f997,f2152])).
% 46.13/6.16  fof(f2152,plain,(
% 46.13/6.16    ( ! [X2,X0,X1] : (k3_xboole_0(k5_xboole_0(X1,X2),X0) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X0)))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f2151,f35])).
% 46.13/6.16  fof(f2151,plain,(
% 46.13/6.16    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X0))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X2,X0))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f2084,f26])).
% 46.13/6.16  fof(f2084,plain,(
% 46.13/6.16    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X2,X0)) = k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X0)),X0)) )),
% 46.13/6.16    inference(superposition,[],[f123,f24])).
% 46.13/6.16  fof(f123,plain,(
% 46.13/6.16    ( ! [X14,X12,X13,X11] : (k3_xboole_0(k5_xboole_0(X14,k3_xboole_0(X11,X12)),X13) = k5_xboole_0(k3_xboole_0(X14,X13),k3_xboole_0(X11,k3_xboole_0(X12,X13)))) )),
% 46.13/6.16    inference(superposition,[],[f35,f34])).
% 46.13/6.16  fof(f997,plain,(
% 46.13/6.16    ( ! [X12,X10,X11] : (k3_xboole_0(X11,k3_xboole_0(k5_xboole_0(X11,X10),X12)) = k3_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,k3_xboole_0(X11,X12))))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f996,f34])).
% 46.13/6.16  fof(f996,plain,(
% 46.13/6.16    ( ! [X12,X10,X11] : (k3_xboole_0(k3_xboole_0(X11,k5_xboole_0(X11,X10)),X12) = k3_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,k3_xboole_0(X11,X12))))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f995,f132])).
% 46.13/6.16  fof(f132,plain,(
% 46.13/6.16    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f114,f26])).
% 46.13/6.16  fof(f114,plain,(
% 46.13/6.16    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0)) )),
% 46.13/6.16    inference(superposition,[],[f35,f24])).
% 46.13/6.16  fof(f995,plain,(
% 46.13/6.16    ( ! [X12,X10,X11] : (k3_xboole_0(k5_xboole_0(X11,k3_xboole_0(X10,X11)),X12) = k3_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,k3_xboole_0(X11,X12))))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f994,f25])).
% 46.13/6.16  fof(f994,plain,(
% 46.13/6.16    ( ! [X12,X10,X11] : (k3_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,k3_xboole_0(X11,X12)))) = k3_xboole_0(k5_xboole_0(k3_xboole_0(X10,X11),X11),X12)) )),
% 46.13/6.16    inference(forward_demodulation,[],[f993,f115])).
% 46.13/6.16  fof(f993,plain,(
% 46.13/6.16    ( ! [X12,X10,X11] : (k5_xboole_0(k3_xboole_0(X12,k3_xboole_0(X10,X11)),k3_xboole_0(X11,X12)) = k3_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,k3_xboole_0(X11,X12))))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f961,f34])).
% 46.13/6.16  fof(f961,plain,(
% 46.13/6.16    ( ! [X12,X10,X11] : (k5_xboole_0(k3_xboole_0(X12,k3_xboole_0(X10,X11)),k3_xboole_0(X11,X12)) = k3_xboole_0(k3_xboole_0(X11,X12),k5_xboole_0(X10,k3_xboole_0(X11,X12)))) )),
% 46.13/6.16    inference(superposition,[],[f137,f83])).
% 46.13/6.16  fof(f83,plain,(
% 46.13/6.16    ( ! [X6,X7,X5] : (k3_xboole_0(X5,k3_xboole_0(X6,X7)) = k3_xboole_0(X7,k3_xboole_0(X5,X6))) )),
% 46.13/6.16    inference(superposition,[],[f34,f26])).
% 46.13/6.16  fof(f137,plain,(
% 46.13/6.16    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X1,X0),X0) = k3_xboole_0(X0,k5_xboole_0(X1,X0))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f119,f26])).
% 46.13/6.16  fof(f119,plain,(
% 46.13/6.16    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X1,X0),X0) = k3_xboole_0(k5_xboole_0(X1,X0),X0)) )),
% 46.13/6.16    inference(superposition,[],[f35,f24])).
% 46.13/6.16  fof(f44575,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(sK1,sK2)))) | (~spl3_5 | spl3_6 | ~spl3_7 | ~spl3_10)),
% 46.13/6.16    inference(forward_demodulation,[],[f44574,f17771])).
% 46.13/6.16  fof(f17771,plain,(
% 46.13/6.16    ( ! [X14,X15,X16] : (k3_xboole_0(X15,k3_xboole_0(X14,X16)) = k3_xboole_0(X15,k3_xboole_0(X16,X14))) )),
% 46.13/6.16    inference(superposition,[],[f565,f83])).
% 46.13/6.16  fof(f565,plain,(
% 46.13/6.16    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k3_xboole_0(X4,X5)) = k3_xboole_0(X4,k3_xboole_0(X3,X5))) )),
% 46.13/6.16    inference(superposition,[],[f79,f34])).
% 46.13/6.16  fof(f79,plain,(
% 46.13/6.16    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k3_xboole_0(X3,X4)) = k3_xboole_0(k3_xboole_0(X3,X2),X4)) )),
% 46.13/6.16    inference(superposition,[],[f34,f26])).
% 46.13/6.16  fof(f44574,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k1_xboole_0)))) | (~spl3_5 | spl3_6 | ~spl3_7 | ~spl3_10)),
% 46.13/6.16    inference(forward_demodulation,[],[f44573,f41])).
% 46.13/6.16  fof(f44573,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))))) | (~spl3_5 | spl3_6 | ~spl3_7 | ~spl3_10)),
% 46.13/6.16    inference(forward_demodulation,[],[f44572,f69])).
% 46.13/6.16  fof(f44572,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))))) | (~spl3_5 | spl3_6 | ~spl3_7 | ~spl3_10)),
% 46.13/6.16    inference(forward_demodulation,[],[f44571,f17771])).
% 46.13/6.16  fof(f44571,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)))) | (~spl3_5 | spl3_6 | ~spl3_7 | ~spl3_10)),
% 46.13/6.16    inference(forward_demodulation,[],[f44570,f18088])).
% 46.13/6.16  fof(f18088,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,X76),k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,X76)))) ) | (~spl3_5 | ~spl3_7 | ~spl3_10)),
% 46.13/6.16    inference(backward_demodulation,[],[f6691,f17760])).
% 46.13/6.16  fof(f17760,plain,(
% 46.13/6.16    ( ! [X113] : (k3_xboole_0(X113,k5_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k3_xboole_0(X113,k5_xboole_0(sK1,sK2)))) ) | ~spl3_10),
% 46.13/6.16    inference(superposition,[],[f565,f7428])).
% 46.13/6.16  fof(f7428,plain,(
% 46.13/6.16    k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | ~spl3_10),
% 46.13/6.16    inference(avatar_component_clause,[],[f7426])).
% 46.13/6.16  fof(f6691,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,X76),k5_xboole_0(sK1,sK2))) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,X76)))) ) | (~spl3_5 | ~spl3_7)),
% 46.13/6.16    inference(forward_demodulation,[],[f6690,f32])).
% 46.13/6.16  fof(f6690,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,X76),k5_xboole_0(sK1,sK2)))) ) | (~spl3_5 | ~spl3_7)),
% 46.13/6.16    inference(forward_demodulation,[],[f6689,f83])).
% 46.13/6.16  fof(f6689,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,k5_xboole_0(sK1,X76)))) ) | (~spl3_5 | ~spl3_7)),
% 46.13/6.16    inference(forward_demodulation,[],[f6688,f301])).
% 46.13/6.16  fof(f301,plain,(
% 46.13/6.16    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 46.13/6.16    inference(backward_demodulation,[],[f157,f300])).
% 46.13/6.16  fof(f300,plain,(
% 46.13/6.16    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f299,f26])).
% 46.13/6.16  fof(f299,plain,(
% 46.13/6.16    ( ! [X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X1),X0) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f288,f120])).
% 46.13/6.16  fof(f120,plain,(
% 46.13/6.16    ( ! [X4,X2,X3] : (k3_xboole_0(k5_xboole_0(X4,X2),X3) = k5_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(X3,X2))) )),
% 46.13/6.16    inference(superposition,[],[f35,f26])).
% 46.13/6.16  fof(f288,plain,(
% 46.13/6.16    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X1))) )),
% 46.13/6.16    inference(superposition,[],[f45,f78])).
% 46.13/6.16  fof(f45,plain,(
% 46.13/6.16    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))) )),
% 46.13/6.16    inference(backward_demodulation,[],[f40,f34])).
% 46.13/6.16  fof(f40,plain,(
% 46.13/6.16    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 46.13/6.16    inference(definition_unfolding,[],[f33,f30,f30])).
% 46.13/6.16  fof(f33,plain,(
% 46.13/6.16    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 46.13/6.16    inference(cnf_transformation,[],[f10])).
% 46.13/6.16  fof(f10,axiom,(
% 46.13/6.16    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 46.13/6.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 46.13/6.16  fof(f157,plain,(
% 46.13/6.16    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f142,f78])).
% 46.13/6.16  fof(f142,plain,(
% 46.13/6.16    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 46.13/6.16    inference(superposition,[],[f45,f24])).
% 46.13/6.16  fof(f6688,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,X76)))) ) | (~spl3_5 | ~spl3_7)),
% 46.13/6.16    inference(forward_demodulation,[],[f6687,f51])).
% 46.13/6.16  fof(f6687,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(k1_xboole_0,sK1),X76)))) ) | (~spl3_5 | ~spl3_7)),
% 46.13/6.16    inference(forward_demodulation,[],[f6686,f1415])).
% 46.13/6.16  fof(f1415,plain,(
% 46.13/6.16    ( ! [X4,X5,X3] : (k3_xboole_0(k5_xboole_0(X3,X5),X4) = k3_xboole_0(k5_xboole_0(X5,X3),X4)) )),
% 46.13/6.16    inference(superposition,[],[f125,f35])).
% 46.13/6.16  fof(f125,plain,(
% 46.13/6.16    ( ! [X6,X7,X5] : (k3_xboole_0(k5_xboole_0(X5,X7),X6) = k5_xboole_0(k3_xboole_0(X7,X6),k3_xboole_0(X5,X6))) )),
% 46.13/6.16    inference(superposition,[],[f35,f25])).
% 46.13/6.16  fof(f6686,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k1_xboole_0),X76)))) ) | (~spl3_5 | ~spl3_7)),
% 46.13/6.16    inference(forward_demodulation,[],[f6685,f138])).
% 46.13/6.16  fof(f138,plain,(
% 46.13/6.16    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X4)) )),
% 46.13/6.16    inference(forward_demodulation,[],[f124,f41])).
% 46.13/6.16  fof(f124,plain,(
% 46.13/6.16    ( ! [X4,X3] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X3,X3),X4)) )),
% 46.13/6.16    inference(superposition,[],[f35,f41])).
% 46.13/6.16  fof(f6685,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK2)),X76)))) ) | (~spl3_5 | ~spl3_7)),
% 46.13/6.16    inference(forward_demodulation,[],[f6684,f26])).
% 46.13/6.16  fof(f6684,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,k1_xboole_0)),X76)))) ) | (~spl3_5 | ~spl3_7)),
% 46.13/6.16    inference(forward_demodulation,[],[f6683,f41])).
% 46.13/6.16  fof(f6683,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,k5_xboole_0(sK1,sK1))),X76)))) ) | (~spl3_5 | ~spl3_7)),
% 46.13/6.16    inference(forward_demodulation,[],[f6682,f421])).
% 46.13/6.16  fof(f421,plain,(
% 46.13/6.16    ( ! [X2] : (k3_xboole_0(sK2,k5_xboole_0(X2,sK2)) = k3_xboole_0(sK2,k5_xboole_0(X2,sK1))) ) | ~spl3_5),
% 46.13/6.16    inference(forward_demodulation,[],[f420,f26])).
% 46.13/6.16  fof(f420,plain,(
% 46.13/6.16    ( ! [X2] : (k3_xboole_0(k5_xboole_0(X2,sK1),sK2) = k3_xboole_0(sK2,k5_xboole_0(X2,sK2))) ) | ~spl3_5),
% 46.13/6.16    inference(forward_demodulation,[],[f414,f137])).
% 46.13/6.16  fof(f414,plain,(
% 46.13/6.16    ( ! [X2] : (k3_xboole_0(k5_xboole_0(X2,sK1),sK2) = k5_xboole_0(k3_xboole_0(X2,sK2),sK2)) ) | ~spl3_5),
% 46.13/6.16    inference(superposition,[],[f35,f256])).
% 46.13/6.16  fof(f256,plain,(
% 46.13/6.16    sK2 = k3_xboole_0(sK1,sK2) | ~spl3_5),
% 46.13/6.16    inference(avatar_component_clause,[],[f254])).
% 46.13/6.16  fof(f6682,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))),X76)))) ) | ~spl3_7),
% 46.13/6.16    inference(forward_demodulation,[],[f6681,f26])).
% 46.13/6.16  fof(f6681,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,sK2),sK2)),X76)))) ) | ~spl3_7),
% 46.13/6.16    inference(forward_demodulation,[],[f6680,f75])).
% 46.13/6.16  fof(f6680,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),sK2)))),X76)))) ) | ~spl3_7),
% 46.13/6.16    inference(forward_demodulation,[],[f6679,f69])).
% 46.13/6.16  fof(f6679,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK2),sK2),sK2))),X76)))) ) | ~spl3_7),
% 46.13/6.16    inference(forward_demodulation,[],[f6678,f25])).
% 46.13/6.16  fof(f6678,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK2),sK2),sK2),sK2)),X76)))) ) | ~spl3_7),
% 46.13/6.16    inference(forward_demodulation,[],[f6677,f69])).
% 46.13/6.16  fof(f6677,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK2),sK2),sK2))),X76)))) ) | ~spl3_7),
% 46.13/6.16    inference(forward_demodulation,[],[f6676,f455])).
% 46.13/6.16  fof(f6676,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK2),sK2),k5_xboole_0(sK1,sK2))),X76)))) ) | ~spl3_7),
% 46.13/6.16    inference(forward_demodulation,[],[f6675,f777])).
% 46.13/6.16  fof(f777,plain,(
% 46.13/6.16    ( ! [X12,X10,X11] : (k5_xboole_0(X10,k5_xboole_0(k3_xboole_0(X11,X10),X12)) = k5_xboole_0(X12,k3_xboole_0(X10,k5_xboole_0(X10,X11)))) )),
% 46.13/6.16    inference(superposition,[],[f69,f132])).
% 46.13/6.16  fof(f6675,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X76)))) ) | ~spl3_7),
% 46.13/6.16    inference(forward_demodulation,[],[f6674,f25])).
% 46.13/6.16  fof(f6674,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X76),sK1))) ) | ~spl3_7),
% 46.13/6.16    inference(forward_demodulation,[],[f6673,f51])).
% 46.13/6.16  fof(f6673,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X76),sK1)))) ) | ~spl3_7),
% 46.13/6.16    inference(forward_demodulation,[],[f6672,f69])).
% 46.13/6.16  fof(f6672,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X76))))) ) | ~spl3_7),
% 46.13/6.16    inference(forward_demodulation,[],[f6671,f75])).
% 46.13/6.16  fof(f6671,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X76))))))) ) | ~spl3_7),
% 46.13/6.16    inference(forward_demodulation,[],[f6670,f69])).
% 46.13/6.16  fof(f6670,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X76)),sK2))))) ) | ~spl3_7),
% 46.13/6.16    inference(forward_demodulation,[],[f6669,f25])).
% 46.13/6.16  fof(f6669,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X76)),sK2),sK2)))) ) | ~spl3_7),
% 46.13/6.16    inference(forward_demodulation,[],[f6668,f69])).
% 46.13/6.16  fof(f6668,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X76)),sK2))))) ) | ~spl3_7),
% 46.13/6.16    inference(forward_demodulation,[],[f6667,f455])).
% 46.13/6.16  fof(f6667,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X76)),k5_xboole_0(sK1,sK2))))) ) | ~spl3_7),
% 46.13/6.16    inference(forward_demodulation,[],[f6288,f69])).
% 46.13/6.16  fof(f6288,plain,(
% 46.13/6.16    ( ! [X76] : (k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),X76)) = k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),X76)))))) ) | ~spl3_7),
% 46.13/6.16    inference(superposition,[],[f321,f954])).
% 46.13/6.16  fof(f954,plain,(
% 46.13/6.16    k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) | ~spl3_7),
% 46.13/6.16    inference(avatar_component_clause,[],[f952])).
% 46.13/6.16  fof(f321,plain,(
% 46.13/6.16    ( ! [X10,X8,X9] : (k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(X9,k5_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(k5_xboole_0(X8,k3_xboole_0(X9,k5_xboole_0(X9,X8))),X10))))) = k3_xboole_0(X8,k5_xboole_0(X8,X10))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f310,f301])).
% 46.13/6.16  fof(f310,plain,(
% 46.13/6.16    ( ! [X10,X8,X9] : (k5_xboole_0(X8,k3_xboole_0(X8,X10)) = k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(X9,k5_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(k5_xboole_0(X8,k3_xboole_0(X9,k5_xboole_0(X9,X8))),X10)))))) )),
% 46.13/6.16    inference(backward_demodulation,[],[f160,f301])).
% 46.13/6.16  fof(f160,plain,(
% 46.13/6.16    ( ! [X10,X8,X9] : (k5_xboole_0(X8,k3_xboole_0(X8,X10)) = k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(X9,k5_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X10)))))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f159,f32])).
% 46.13/6.16  fof(f159,plain,(
% 46.13/6.16    ( ! [X10,X8,X9] : (k5_xboole_0(X8,k3_xboole_0(X8,X10)) = k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(k5_xboole_0(X9,k3_xboole_0(X9,X8)),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X10))))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f158,f32])).
% 46.13/6.16  fof(f158,plain,(
% 46.13/6.16    ( ! [X10,X8,X9] : (k3_xboole_0(X8,k5_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X10))) = k5_xboole_0(X8,k3_xboole_0(X8,X10))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f145,f105])).
% 46.13/6.16  fof(f105,plain,(
% 46.13/6.16    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X2))) )),
% 46.13/6.16    inference(superposition,[],[f34,f39])).
% 46.13/6.16  fof(f145,plain,(
% 46.13/6.16    ( ! [X10,X8,X9] : (k3_xboole_0(X8,k5_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X10))) = k5_xboole_0(X8,k3_xboole_0(X8,k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X10)))) )),
% 46.13/6.16    inference(superposition,[],[f45,f39])).
% 46.13/6.16  fof(f44570,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK0,sK1)))))) | spl3_6),
% 46.13/6.16    inference(forward_demodulation,[],[f44569,f801])).
% 46.13/6.16  fof(f801,plain,(
% 46.13/6.16    ( ! [X12,X10,X11] : (k5_xboole_0(X10,k5_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,X11)))) = k3_xboole_0(k5_xboole_0(X10,X11),k5_xboole_0(X10,k5_xboole_0(X11,X12)))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f773,f32])).
% 46.13/6.16  fof(f773,plain,(
% 46.13/6.16    ( ! [X12,X10,X11] : (k5_xboole_0(X10,k5_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,X11)))) = k3_xboole_0(k5_xboole_0(X10,X11),k5_xboole_0(k5_xboole_0(X10,X11),X12))) )),
% 46.13/6.16    inference(superposition,[],[f132,f32])).
% 46.13/6.16  fof(f44569,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)))))) | spl3_6),
% 46.13/6.16    inference(forward_demodulation,[],[f44568,f14914])).
% 46.13/6.16  fof(f44568,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)),sK2)))) | spl3_6),
% 46.13/6.16    inference(forward_demodulation,[],[f44567,f69])).
% 46.13/6.16  fof(f44567,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)))))) | spl3_6),
% 46.13/6.16    inference(forward_demodulation,[],[f44562,f26])).
% 46.13/6.16  fof(f44562,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)))),sK0)) | spl3_6),
% 46.13/6.16    inference(backward_demodulation,[],[f410,f44558])).
% 46.13/6.16  fof(f44558,plain,(
% 46.13/6.16    ( ! [X109,X107,X110,X108] : (k3_xboole_0(X109,k5_xboole_0(X108,k5_xboole_0(X107,k3_xboole_0(X109,X110)))) = k3_xboole_0(k5_xboole_0(X107,k5_xboole_0(X108,X110)),X109)) )),
% 46.13/6.16    inference(forward_demodulation,[],[f44097,f32])).
% 46.13/6.16  fof(f44097,plain,(
% 46.13/6.16    ( ! [X109,X107,X110,X108] : (k3_xboole_0(k5_xboole_0(k5_xboole_0(X107,X108),X110),X109) = k3_xboole_0(X109,k5_xboole_0(X108,k5_xboole_0(X107,k3_xboole_0(X109,X110))))) )),
% 46.13/6.16    inference(superposition,[],[f1280,f63])).
% 46.13/6.16  fof(f1280,plain,(
% 46.13/6.16    ( ! [X10,X8,X9] : (k3_xboole_0(X8,k5_xboole_0(X10,k3_xboole_0(X8,X9))) = k3_xboole_0(k5_xboole_0(X10,X9),X8)) )),
% 46.13/6.16    inference(forward_demodulation,[],[f1279,f120])).
% 46.13/6.16  fof(f1279,plain,(
% 46.13/6.16    ( ! [X10,X8,X9] : (k5_xboole_0(k3_xboole_0(X10,X8),k3_xboole_0(X8,X9)) = k3_xboole_0(X8,k5_xboole_0(X10,k3_xboole_0(X8,X9)))) )),
% 46.13/6.16    inference(forward_demodulation,[],[f1228,f26])).
% 46.13/6.16  fof(f1228,plain,(
% 46.13/6.16    ( ! [X10,X8,X9] : (k5_xboole_0(k3_xboole_0(X10,X8),k3_xboole_0(X8,X9)) = k3_xboole_0(k5_xboole_0(X10,k3_xboole_0(X8,X9)),X8)) )),
% 46.13/6.16    inference(superposition,[],[f120,f78])).
% 46.13/6.16  fof(f410,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2))))))) | spl3_6),
% 46.13/6.16    inference(avatar_component_clause,[],[f408])).
% 46.13/6.16  fof(f7429,plain,(
% 46.13/6.16    spl3_10 | ~spl3_2),
% 46.13/6.16    inference(avatar_split_clause,[],[f769,f91,f7426])).
% 46.13/6.16  fof(f91,plain,(
% 46.13/6.16    spl3_2 <=> sK2 = k3_xboole_0(sK2,sK1)),
% 46.13/6.16    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 46.13/6.16  fof(f769,plain,(
% 46.13/6.16    k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | ~spl3_2),
% 46.13/6.16    inference(superposition,[],[f132,f93])).
% 46.13/6.16  fof(f93,plain,(
% 46.13/6.16    sK2 = k3_xboole_0(sK2,sK1) | ~spl3_2),
% 46.13/6.16    inference(avatar_component_clause,[],[f91])).
% 46.13/6.16  fof(f955,plain,(
% 46.13/6.16    spl3_7 | ~spl3_5),
% 46.13/6.16    inference(avatar_split_clause,[],[f796,f254,f952])).
% 46.13/6.16  fof(f796,plain,(
% 46.13/6.16    k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) | ~spl3_5),
% 46.13/6.16    inference(forward_demodulation,[],[f795,f41])).
% 46.13/6.16  fof(f795,plain,(
% 46.13/6.16    k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) | ~spl3_5),
% 46.13/6.16    inference(forward_demodulation,[],[f768,f25])).
% 46.13/6.16  fof(f768,plain,(
% 46.13/6.16    k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k5_xboole_0(sK2,sK1)) | ~spl3_5),
% 46.13/6.16    inference(superposition,[],[f132,f256])).
% 46.13/6.16  fof(f411,plain,(
% 46.13/6.16    ~spl3_6 | spl3_4),
% 46.13/6.16    inference(avatar_split_clause,[],[f327,f203,f408])).
% 46.13/6.16  fof(f203,plain,(
% 46.13/6.16    spl3_4 <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))))),
% 46.13/6.16    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 46.13/6.16  fof(f327,plain,(
% 46.13/6.16    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2))))))) | spl3_4),
% 46.13/6.16    inference(forward_demodulation,[],[f326,f301])).
% 46.13/6.16  fof(f326,plain,(
% 46.13/6.16    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2))))))) | spl3_4),
% 46.13/6.16    inference(forward_demodulation,[],[f325,f83])).
% 46.13/6.16  fof(f325,plain,(
% 46.13/6.16    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(k5_xboole_0(sK1,sK2),sK0)))))) | spl3_4),
% 46.13/6.16    inference(forward_demodulation,[],[f319,f83])).
% 46.13/6.16  fof(f319,plain,(
% 46.13/6.16    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))))))) | spl3_4),
% 46.13/6.16    inference(backward_demodulation,[],[f205,f301])).
% 46.13/6.16  fof(f205,plain,(
% 46.13/6.16    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) | spl3_4),
% 46.13/6.16    inference(avatar_component_clause,[],[f203])).
% 46.13/6.16  fof(f257,plain,(
% 46.13/6.16    spl3_5 | ~spl3_2),
% 46.13/6.16    inference(avatar_split_clause,[],[f183,f91,f254])).
% 46.13/6.16  fof(f183,plain,(
% 46.13/6.16    sK2 = k3_xboole_0(sK1,sK2) | ~spl3_2),
% 46.13/6.16    inference(superposition,[],[f93,f26])).
% 46.13/6.16  fof(f206,plain,(
% 46.13/6.16    ~spl3_4 | ~spl3_2 | spl3_3),
% 46.13/6.16    inference(avatar_split_clause,[],[f194,f179,f91,f203])).
% 46.13/6.16  fof(f179,plain,(
% 46.13/6.16    spl3_3 <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))))),
% 46.13/6.16    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 46.13/6.16  fof(f194,plain,(
% 46.13/6.16    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) | (~spl3_2 | spl3_3)),
% 46.13/6.16    inference(forward_demodulation,[],[f193,f26])).
% 46.13/6.16  fof(f193,plain,(
% 46.13/6.16    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)))))) | (~spl3_2 | spl3_3)),
% 46.13/6.16    inference(backward_demodulation,[],[f181,f183])).
% 46.13/6.16  fof(f181,plain,(
% 46.13/6.16    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))))) | spl3_3),
% 46.13/6.16    inference(avatar_component_clause,[],[f179])).
% 46.13/6.16  fof(f182,plain,(
% 46.13/6.16    ~spl3_3),
% 46.13/6.16    inference(avatar_split_clause,[],[f44,f179])).
% 46.13/6.16  fof(f44,plain,(
% 46.13/6.16    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))))),
% 46.13/6.16    inference(forward_demodulation,[],[f43,f26])).
% 46.13/6.16  fof(f43,plain,(
% 46.13/6.16    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))))),
% 46.13/6.16    inference(forward_demodulation,[],[f42,f32])).
% 46.13/6.16  fof(f42,plain,(
% 46.13/6.16    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))),
% 46.13/6.16    inference(backward_demodulation,[],[f37,f40])).
% 46.13/6.16  fof(f37,plain,(
% 46.13/6.16    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))),
% 46.13/6.16    inference(definition_unfolding,[],[f22,f30,f36,f30,f30])).
% 46.13/6.16  fof(f22,plain,(
% 46.13/6.16    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 46.13/6.16    inference(cnf_transformation,[],[f20])).
% 46.13/6.16  fof(f20,plain,(
% 46.13/6.16    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1)),
% 46.13/6.16    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19])).
% 46.13/6.16  fof(f19,plain,(
% 46.13/6.16    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1)) => (k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1))),
% 46.13/6.16    introduced(choice_axiom,[])).
% 46.13/6.16  fof(f17,plain,(
% 46.13/6.16    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1))),
% 46.13/6.16    inference(ennf_transformation,[],[f15])).
% 46.13/6.16  fof(f15,negated_conjecture,(
% 46.13/6.16    ~! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 46.13/6.16    inference(negated_conjecture,[],[f14])).
% 46.13/6.16  fof(f14,conjecture,(
% 46.13/6.16    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 46.13/6.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).
% 46.13/6.16  fof(f94,plain,(
% 46.13/6.16    spl3_2 | ~spl3_1),
% 46.13/6.16    inference(avatar_split_clause,[],[f59,f47,f91])).
% 46.13/6.16  fof(f47,plain,(
% 46.13/6.16    spl3_1 <=> r1_tarski(sK2,sK1)),
% 46.13/6.16    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 46.13/6.16  fof(f59,plain,(
% 46.13/6.16    sK2 = k3_xboole_0(sK2,sK1) | ~spl3_1),
% 46.13/6.16    inference(unit_resulting_resolution,[],[f49,f31])).
% 46.13/6.16  fof(f31,plain,(
% 46.13/6.16    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 46.13/6.16    inference(cnf_transformation,[],[f18])).
% 46.13/6.16  fof(f18,plain,(
% 46.13/6.16    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 46.13/6.16    inference(ennf_transformation,[],[f8])).
% 46.13/6.16  fof(f8,axiom,(
% 46.13/6.16    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 46.13/6.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 46.13/6.16  fof(f49,plain,(
% 46.13/6.16    r1_tarski(sK2,sK1) | ~spl3_1),
% 46.13/6.16    inference(avatar_component_clause,[],[f47])).
% 46.13/6.16  fof(f50,plain,(
% 46.13/6.16    spl3_1),
% 46.13/6.16    inference(avatar_split_clause,[],[f21,f47])).
% 46.13/6.16  fof(f21,plain,(
% 46.13/6.16    r1_tarski(sK2,sK1)),
% 46.13/6.16    inference(cnf_transformation,[],[f20])).
% 46.13/6.16  % SZS output end Proof for theBenchmark
% 46.13/6.16  % (7596)------------------------------
% 46.13/6.16  % (7596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 46.13/6.16  % (7596)Termination reason: Refutation
% 46.13/6.16  
% 46.13/6.16  % (7596)Memory used [KB]: 152875
% 46.13/6.16  % (7596)Time elapsed: 5.739 s
% 46.13/6.16  % (7596)------------------------------
% 46.13/6.16  % (7596)------------------------------
% 46.13/6.18  % (7580)Success in time 5.817 s
%------------------------------------------------------------------------------
