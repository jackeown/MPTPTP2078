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
% DateTime   : Thu Dec  3 12:31:54 EST 2020

% Result     : Theorem 11.23s
% Output     : Refutation 11.85s
% Verified   : 
% Statistics : Number of formulae       :  198 (31959 expanded)
%              Number of leaves         :   22 (10676 expanded)
%              Depth                    :   40
%              Number of atoms          :  267 (32084 expanded)
%              Number of equality atoms :  176 (31935 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24148,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f37,f54,f126,f127,f17721,f17726,f17821,f23977,f24094,f24117,f24119,f24128,f24133,f24138,f24139,f24145,f24146,f24147])).

fof(f24147,plain,
    ( ~ spl2_12
    | spl2_9 ),
    inference(avatar_split_clause,[],[f24126,f24114,f24142])).

fof(f24142,plain,
    ( spl2_12
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f24114,plain,
    ( spl2_9
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f24126,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | spl2_9 ),
    inference(superposition,[],[f24116,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f24116,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f24114])).

fof(f24146,plain,
    ( ~ spl2_12
    | spl2_9 ),
    inference(avatar_split_clause,[],[f24125,f24114,f24142])).

fof(f24125,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | spl2_9 ),
    inference(superposition,[],[f24116,f16])).

fof(f24145,plain,
    ( ~ spl2_12
    | spl2_9 ),
    inference(avatar_split_clause,[],[f24140,f24114,f24142])).

fof(f24140,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | spl2_9 ),
    inference(forward_demodulation,[],[f24124,f16])).

fof(f24124,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK1))
    | spl2_9 ),
    inference(superposition,[],[f24116,f18537])).

fof(f18537,plain,(
    ! [X19,X17,X18] : k2_xboole_0(X19,k2_xboole_0(X18,X17)) = k2_xboole_0(k2_xboole_0(X17,X18),X19) ),
    inference(forward_demodulation,[],[f18536,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f41,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f19,f20])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f18536,plain,(
    ! [X19,X17,X18] : k2_xboole_0(k2_xboole_0(X17,X18),X19) = k2_xboole_0(X19,k2_xboole_0(X18,k2_xboole_0(X17,X18))) ),
    inference(forward_demodulation,[],[f18395,f16])).

fof(f18395,plain,(
    ! [X19,X17,X18] : k2_xboole_0(k2_xboole_0(X17,X18),X19) = k2_xboole_0(X19,k2_xboole_0(k2_xboole_0(X17,X18),X18)) ),
    inference(superposition,[],[f18085,f2359])).

fof(f2359,plain,(
    ! [X23,X21,X22] : k2_xboole_0(k2_xboole_0(X21,X23),k2_xboole_0(X21,X22)) = k2_xboole_0(k2_xboole_0(X21,X23),X22) ),
    inference(forward_demodulation,[],[f2317,f19])).

fof(f2317,plain,(
    ! [X23,X21,X22] : k2_xboole_0(k2_xboole_0(X21,X23),k2_xboole_0(X21,X22)) = k2_xboole_0(k2_xboole_0(X21,X23),k4_xboole_0(X22,k2_xboole_0(X21,X23))) ),
    inference(superposition,[],[f19,f137])).

fof(f137,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,X5)) = k4_xboole_0(X4,k2_xboole_0(X3,X5)) ),
    inference(forward_demodulation,[],[f129,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f129,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,X5)) = k4_xboole_0(k4_xboole_0(X4,X3),X5) ),
    inference(superposition,[],[f24,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f20,f16])).

fof(f18085,plain,(
    ! [X10,X9] : k2_xboole_0(X10,X9) = k2_xboole_0(X9,k2_xboole_0(X10,X10)) ),
    inference(backward_demodulation,[],[f267,f18033])).

fof(f18033,plain,(
    ! [X26,X25] : k2_xboole_0(X26,X25) = k2_xboole_0(k4_xboole_0(X25,X26),k2_xboole_0(X25,k2_xboole_0(X26,X26))) ),
    inference(backward_demodulation,[],[f2945,f17876])).

fof(f17876,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(k2_xboole_0(X4,X4),X5) ),
    inference(superposition,[],[f16799,f2359])).

fof(f16799,plain,(
    ! [X12,X13] : k2_xboole_0(X12,X13) = k2_xboole_0(k2_xboole_0(X12,X12),k2_xboole_0(X12,X13)) ),
    inference(superposition,[],[f16512,f16])).

fof(f16512,plain,(
    ! [X24,X25] : k2_xboole_0(X24,X25) = k2_xboole_0(k2_xboole_0(X24,X25),k2_xboole_0(X24,X24)) ),
    inference(forward_demodulation,[],[f16315,f8174])).

fof(f8174,plain,(
    ! [X54,X55] : k2_xboole_0(X54,X55) = k2_xboole_0(k2_xboole_0(X54,X55),k4_xboole_0(X54,k4_xboole_0(X54,X54))) ),
    inference(forward_demodulation,[],[f8173,f48])).

fof(f48,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f46,f19])).

fof(f46,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(superposition,[],[f19,f38])).

fof(f8173,plain,(
    ! [X54,X55] : k2_xboole_0(X54,k2_xboole_0(X54,X55)) = k2_xboole_0(k2_xboole_0(X54,X55),k4_xboole_0(X54,k4_xboole_0(X54,X54))) ),
    inference(forward_demodulation,[],[f8172,f16])).

fof(f8172,plain,(
    ! [X54,X55] : k2_xboole_0(k2_xboole_0(X54,X55),X54) = k2_xboole_0(k2_xboole_0(X54,X55),k4_xboole_0(X54,k4_xboole_0(X54,X54))) ),
    inference(forward_demodulation,[],[f8067,f2359])).

fof(f8067,plain,(
    ! [X54,X55] : k2_xboole_0(k2_xboole_0(X54,X55),k4_xboole_0(X54,k4_xboole_0(X54,X54))) = k2_xboole_0(k2_xboole_0(X54,X55),k2_xboole_0(X54,X54)) ),
    inference(superposition,[],[f2188,f7826])).

fof(f7826,plain,(
    ! [X7] : k2_xboole_0(X7,X7) = k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X7)),X7) ),
    inference(forward_demodulation,[],[f7734,f190])).

fof(f190,plain,(
    ! [X17,X16] : k2_xboole_0(X17,X16) = k2_xboole_0(k4_xboole_0(X17,k4_xboole_0(X16,X17)),k2_xboole_0(X17,X16)) ),
    inference(forward_demodulation,[],[f172,f40])).

fof(f40,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) ),
    inference(superposition,[],[f20,f19])).

fof(f172,plain,(
    ! [X17,X16] : k2_xboole_0(X17,X16) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X17,X16),k4_xboole_0(X16,X17)),k2_xboole_0(X17,X16)) ),
    inference(superposition,[],[f62,f62])).

fof(f62,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f61,f19])).

fof(f61,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X5,X4)) = k2_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f57,f16])).

fof(f57,plain,(
    ! [X4,X5] : k2_xboole_0(k4_xboole_0(X5,X4),X4) = k2_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5)) ),
    inference(superposition,[],[f42,f19])).

fof(f7734,plain,(
    ! [X7] : k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X7)),X7) = k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X7)),k2_xboole_0(X7,X7)) ),
    inference(superposition,[],[f42,f7414])).

fof(f7414,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X1))) ),
    inference(forward_demodulation,[],[f7276,f42])).

fof(f7276,plain,(
    ! [X1] : k2_xboole_0(X1,k2_xboole_0(X1,X1)) = k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X1))) ),
    inference(superposition,[],[f356,f190])).

fof(f356,plain,(
    ! [X12,X13] : k2_xboole_0(X13,X12) = k2_xboole_0(X13,k2_xboole_0(X12,k2_xboole_0(X13,X13))) ),
    inference(forward_demodulation,[],[f348,f19])).

fof(f348,plain,(
    ! [X12,X13] : k2_xboole_0(X13,k2_xboole_0(X12,k2_xboole_0(X13,X13))) = k2_xboole_0(X13,k4_xboole_0(X12,X13)) ),
    inference(superposition,[],[f19,f152])).

fof(f152,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X1)),X1) ),
    inference(forward_demodulation,[],[f141,f132])).

fof(f132,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(X1,X1)) ),
    inference(superposition,[],[f24,f47])).

fof(f47,plain,(
    ! [X4,X5] : k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4) ),
    inference(forward_demodulation,[],[f45,f38])).

fof(f45,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X5,X4),X4) = k4_xboole_0(k2_xboole_0(X4,X5),X4) ),
    inference(superposition,[],[f38,f19])).

fof(f141,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X1)) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X1)),X1) ),
    inference(superposition,[],[f132,f20])).

fof(f2188,plain,(
    ! [X21,X22,X20] : k2_xboole_0(k2_xboole_0(X21,X22),k2_xboole_0(X20,X21)) = k2_xboole_0(k2_xboole_0(X21,X22),X20) ),
    inference(forward_demodulation,[],[f2144,f19])).

fof(f2144,plain,(
    ! [X21,X22,X20] : k2_xboole_0(k2_xboole_0(X21,X22),k2_xboole_0(X20,X21)) = k2_xboole_0(k2_xboole_0(X21,X22),k4_xboole_0(X20,k2_xboole_0(X21,X22))) ),
    inference(superposition,[],[f19,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f128,f24])).

fof(f128,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f24,f20])).

fof(f16315,plain,(
    ! [X24,X25] : k2_xboole_0(k2_xboole_0(X24,X25),k2_xboole_0(X24,X24)) = k2_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,k4_xboole_0(X24,X24))) ),
    inference(superposition,[],[f2359,f7414])).

fof(f2945,plain,(
    ! [X26,X25] : k2_xboole_0(k2_xboole_0(X26,X26),X25) = k2_xboole_0(k4_xboole_0(X25,X26),k2_xboole_0(X25,k2_xboole_0(X26,X26))) ),
    inference(superposition,[],[f2895,f132])).

fof(f2895,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f2894,f19])).

fof(f2894,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f2893,f16])).

fof(f2893,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(forward_demodulation,[],[f2846,f19])).

fof(f2846,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(superposition,[],[f19,f1355])).

fof(f1355,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f40,f16])).

fof(f267,plain,(
    ! [X10,X9] : k2_xboole_0(X9,k2_xboole_0(X10,X10)) = k2_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X9,k2_xboole_0(X10,X10))) ),
    inference(superposition,[],[f164,f132])).

fof(f164,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f62,f16])).

fof(f24139,plain,
    ( ~ spl2_11
    | spl2_9 ),
    inference(avatar_split_clause,[],[f24123,f24114,f24135])).

fof(f24135,plain,
    ( spl2_11
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f24123,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_9 ),
    inference(superposition,[],[f24116,f21554])).

fof(f21554,plain,(
    ! [X12,X13,X11] : k2_xboole_0(X11,k2_xboole_0(X12,X13)) = k2_xboole_0(X13,k2_xboole_0(X12,X11)) ),
    inference(superposition,[],[f21327,f18537])).

fof(f21327,plain,(
    ! [X52,X50,X51] : k2_xboole_0(k2_xboole_0(X51,X50),X52) = k2_xboole_0(X51,k2_xboole_0(X50,X52)) ),
    inference(forward_demodulation,[],[f21116,f21017])).

fof(f21017,plain,(
    ! [X74,X72,X73] : k2_xboole_0(X73,k2_xboole_0(X72,X74)) = k2_xboole_0(k2_xboole_0(X73,X72),k2_xboole_0(X73,k2_xboole_0(X72,X74))) ),
    inference(backward_demodulation,[],[f6747,f20920])).

fof(f20920,plain,(
    ! [X57,X58,X56] : k2_xboole_0(X58,k2_xboole_0(X56,X57)) = k2_xboole_0(k2_xboole_0(X56,X58),X57) ),
    inference(forward_demodulation,[],[f20919,f20650])).

fof(f20650,plain,(
    ! [X70,X71] : k2_xboole_0(X70,X71) = k2_xboole_0(k2_xboole_0(X71,X70),X71) ),
    inference(forward_demodulation,[],[f20649,f77])).

fof(f77,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f76,f48])).

fof(f76,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f74,f16])).

fof(f74,plain,(
    ! [X2,X1] : k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f42,f48])).

fof(f20649,plain,(
    ! [X70,X71] : k2_xboole_0(k2_xboole_0(X71,X70),X71) = k2_xboole_0(k2_xboole_0(X70,X71),k2_xboole_0(X70,X71)) ),
    inference(forward_demodulation,[],[f20522,f20037])).

fof(f20037,plain,(
    ! [X37,X35,X36] : k2_xboole_0(k2_xboole_0(X35,X36),X37) = k2_xboole_0(k4_xboole_0(X37,X35),k2_xboole_0(X36,X35)) ),
    inference(superposition,[],[f18537,f2010])).

fof(f2010,plain,(
    ! [X24,X23,X22] : k2_xboole_0(k2_xboole_0(X22,X23),k4_xboole_0(X24,X22)) = k2_xboole_0(k2_xboole_0(X22,X23),X24) ),
    inference(forward_demodulation,[],[f1950,f19])).

fof(f1950,plain,(
    ! [X24,X23,X22] : k2_xboole_0(k2_xboole_0(X22,X23),k4_xboole_0(X24,X22)) = k2_xboole_0(k2_xboole_0(X22,X23),k4_xboole_0(X24,k2_xboole_0(X22,X23))) ),
    inference(superposition,[],[f135,f48])).

fof(f135,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7))) ),
    inference(superposition,[],[f19,f24])).

fof(f20522,plain,(
    ! [X70,X71] : k2_xboole_0(k2_xboole_0(X70,X71),k2_xboole_0(X70,X71)) = k2_xboole_0(k4_xboole_0(X71,X71),k2_xboole_0(X70,X71)) ),
    inference(superposition,[],[f20027,f11618])).

fof(f11618,plain,(
    ! [X10,X9] : k2_xboole_0(X10,X9) = k2_xboole_0(k2_xboole_0(X10,X9),k4_xboole_0(X9,X9)) ),
    inference(superposition,[],[f9881,f16])).

fof(f9881,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X3,X3),k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f9692,f280])).

fof(f280,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f164,f16])).

fof(f9692,plain,(
    ! [X2,X3] : k2_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X3,X3),k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f9320,f20])).

fof(f9320,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k4_xboole_0(X8,X9)) = k2_xboole_0(k4_xboole_0(X9,X9),X8) ),
    inference(superposition,[],[f9144,f16])).

fof(f9144,plain,(
    ! [X26,X27] : k2_xboole_0(X26,k4_xboole_0(X27,X27)) = k2_xboole_0(X26,k4_xboole_0(X26,X27)) ),
    inference(forward_demodulation,[],[f9143,f132])).

fof(f9143,plain,(
    ! [X26,X27] : k2_xboole_0(X26,k4_xboole_0(X27,X27)) = k2_xboole_0(X26,k4_xboole_0(X26,k2_xboole_0(X27,X27))) ),
    inference(forward_demodulation,[],[f9142,f24])).

fof(f9142,plain,(
    ! [X26,X27] : k2_xboole_0(X26,k4_xboole_0(X27,X27)) = k2_xboole_0(X26,k4_xboole_0(k4_xboole_0(X26,X27),X27)) ),
    inference(forward_demodulation,[],[f9141,f135])).

fof(f9141,plain,(
    ! [X26,X27] : k2_xboole_0(X26,k4_xboole_0(k4_xboole_0(X26,X27),X27)) = k2_xboole_0(X26,k4_xboole_0(X27,k2_xboole_0(X27,X26))) ),
    inference(forward_demodulation,[],[f9001,f16])).

fof(f9001,plain,(
    ! [X26,X27] : k2_xboole_0(X26,k4_xboole_0(k4_xboole_0(X26,X27),X27)) = k2_xboole_0(k4_xboole_0(X27,k2_xboole_0(X27,X26)),X26) ),
    inference(superposition,[],[f1440,f191])).

fof(f191,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X4,X5),k2_xboole_0(X5,X4)) = k4_xboole_0(X5,k2_xboole_0(X5,X4)) ),
    inference(forward_demodulation,[],[f177,f75])).

fof(f75,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f20,f48])).

fof(f177,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X4,X5),k2_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X5,X4),k2_xboole_0(X5,X4)) ),
    inference(superposition,[],[f20,f62])).

fof(f1440,plain,(
    ! [X14,X12,X13] : k2_xboole_0(X14,k4_xboole_0(X12,X13)) = k2_xboole_0(k4_xboole_0(X12,k2_xboole_0(X13,X14)),X14) ),
    inference(superposition,[],[f1412,f24])).

fof(f1412,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(forward_demodulation,[],[f1411,f62])).

fof(f1411,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X1,X0),X0) = k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f1375,f19])).

fof(f1375,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f19,f40])).

fof(f20027,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,k2_xboole_0(X5,X4)) ),
    inference(superposition,[],[f18537,f89])).

fof(f89,plain,(
    ! [X12,X11] : k2_xboole_0(X12,X11) = k2_xboole_0(k2_xboole_0(X12,X11),X11) ),
    inference(forward_demodulation,[],[f87,f77])).

fof(f87,plain,(
    ! [X12,X11] : k2_xboole_0(k2_xboole_0(X12,X11),X11) = k2_xboole_0(k2_xboole_0(X12,X11),k2_xboole_0(X12,X11)) ),
    inference(superposition,[],[f42,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f48,f16])).

fof(f20919,plain,(
    ! [X57,X58,X56] : k2_xboole_0(k2_xboole_0(X56,X58),X57) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X56,X57),X58),k2_xboole_0(X56,X57)) ),
    inference(forward_demodulation,[],[f20782,f2359])).

fof(f20782,plain,(
    ! [X57,X58,X56] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X56,X57),X58),k2_xboole_0(X56,X57)) = k2_xboole_0(k2_xboole_0(X56,X58),k2_xboole_0(X56,X57)) ),
    inference(superposition,[],[f20650,f2359])).

fof(f6747,plain,(
    ! [X74,X72,X73] : k2_xboole_0(k2_xboole_0(X72,X73),X74) = k2_xboole_0(k2_xboole_0(X73,X72),k2_xboole_0(k2_xboole_0(X72,X73),X74)) ),
    inference(backward_demodulation,[],[f6744,f6746])).

fof(f6746,plain,(
    ! [X76,X77,X75] : k2_xboole_0(k2_xboole_0(X75,X76),X77) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X75,X76),X77),k4_xboole_0(X75,X76)) ),
    inference(forward_demodulation,[],[f6745,f48])).

fof(f6745,plain,(
    ! [X76,X77,X75] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X75,X76),X77),k4_xboole_0(X75,X76)) = k2_xboole_0(k2_xboole_0(X75,X76),k2_xboole_0(k2_xboole_0(X75,X76),X77)) ),
    inference(forward_demodulation,[],[f6603,f16])).

fof(f6603,plain,(
    ! [X76,X77,X75] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X75,X76),X77),k4_xboole_0(X75,X76)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X75,X76),X77),k2_xboole_0(X75,X76)) ),
    inference(superposition,[],[f2188,f164])).

fof(f6744,plain,(
    ! [X74,X72,X73] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X72,X73),X74),k4_xboole_0(X72,X73)) = k2_xboole_0(k2_xboole_0(X73,X72),k2_xboole_0(k2_xboole_0(X72,X73),X74)) ),
    inference(forward_demodulation,[],[f6602,f16])).

fof(f6602,plain,(
    ! [X74,X72,X73] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X72,X73),X74),k4_xboole_0(X72,X73)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X72,X73),X74),k2_xboole_0(X73,X72)) ),
    inference(superposition,[],[f2188,f2895])).

fof(f21116,plain,(
    ! [X52,X50,X51] : k2_xboole_0(k2_xboole_0(X51,X50),X52) = k2_xboole_0(k2_xboole_0(X51,X50),k2_xboole_0(X51,k2_xboole_0(X50,X52))) ),
    inference(backward_demodulation,[],[f16282,f20920])).

fof(f16282,plain,(
    ! [X52,X50,X51] : k2_xboole_0(k2_xboole_0(X51,X50),k2_xboole_0(k2_xboole_0(X50,X51),X52)) = k2_xboole_0(k2_xboole_0(X51,X50),X52) ),
    inference(superposition,[],[f2359,f3046])).

fof(f3046,plain,(
    ! [X12,X11] : k2_xboole_0(k2_xboole_0(X12,X11),X11) = k2_xboole_0(X11,X12) ),
    inference(forward_demodulation,[],[f2951,f242])).

fof(f242,plain,(
    ! [X14,X15] : k2_xboole_0(X15,X14) = k2_xboole_0(k4_xboole_0(X15,k2_xboole_0(X14,X15)),k2_xboole_0(X15,X14)) ),
    inference(forward_demodulation,[],[f220,f136])).

fof(f220,plain,(
    ! [X14,X15] : k2_xboole_0(X15,X14) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X15,X14),k2_xboole_0(X14,X15)),k2_xboole_0(X15,X14)) ),
    inference(superposition,[],[f62,f64])).

fof(f64,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(k2_xboole_0(X7,X6),k2_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f63,f42])).

fof(f63,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k2_xboole_0(X7,X6)) = k2_xboole_0(k2_xboole_0(X7,X6),k2_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f58,f16])).

fof(f58,plain,(
    ! [X6,X7] : k2_xboole_0(k2_xboole_0(X7,X6),X6) = k2_xboole_0(k2_xboole_0(X7,X6),k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f42,f42])).

fof(f2951,plain,(
    ! [X12,X11] : k2_xboole_0(k2_xboole_0(X12,X11),X11) = k2_xboole_0(k4_xboole_0(X11,k2_xboole_0(X12,X11)),k2_xboole_0(X11,X12)) ),
    inference(superposition,[],[f2895,f42])).

fof(f24138,plain,
    ( ~ spl2_11
    | spl2_9 ),
    inference(avatar_split_clause,[],[f24122,f24114,f24135])).

fof(f24122,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_9 ),
    inference(superposition,[],[f24116,f21554])).

fof(f24133,plain,
    ( ~ spl2_10
    | spl2_9 ),
    inference(avatar_split_clause,[],[f24120,f24114,f24130])).

fof(f24130,plain,
    ( spl2_10
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f24120,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK0)
    | spl2_9 ),
    inference(superposition,[],[f24116,f2895])).

fof(f24128,plain,(
    spl2_9 ),
    inference(avatar_contradiction_clause,[],[f24127])).

fof(f24127,plain,
    ( $false
    | spl2_9 ),
    inference(trivial_inequality_removal,[],[f24121])).

fof(f24121,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1)
    | spl2_9 ),
    inference(superposition,[],[f24116,f164])).

fof(f24119,plain,
    ( ~ spl2_9
    | spl2_8 ),
    inference(avatar_split_clause,[],[f24118,f23974,f24114])).

fof(f23974,plain,
    ( spl2_8
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f24118,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))
    | spl2_8 ),
    inference(forward_demodulation,[],[f24111,f19])).

fof(f24111,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | spl2_8 ),
    inference(superposition,[],[f23976,f21554])).

fof(f23976,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f23974])).

fof(f24117,plain,
    ( ~ spl2_9
    | spl2_8 ),
    inference(avatar_split_clause,[],[f24112,f23974,f24114])).

fof(f24112,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))
    | spl2_8 ),
    inference(forward_demodulation,[],[f24110,f19])).

fof(f24110,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | spl2_8 ),
    inference(superposition,[],[f23976,f21554])).

fof(f24094,plain,
    ( ~ spl2_8
    | spl2_7 ),
    inference(avatar_split_clause,[],[f24093,f17818,f23974])).

fof(f17818,plain,
    ( spl2_7
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f24093,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_7 ),
    inference(forward_demodulation,[],[f24092,f16])).

fof(f24092,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0))
    | spl2_7 ),
    inference(forward_demodulation,[],[f23753,f19])).

fof(f23753,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_7 ),
    inference(superposition,[],[f17820,f21554])).

fof(f17820,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f17818])).

fof(f23977,plain,
    ( ~ spl2_8
    | spl2_7 ),
    inference(avatar_split_clause,[],[f23972,f17818,f23974])).

fof(f23972,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_7 ),
    inference(forward_demodulation,[],[f23971,f16])).

fof(f23971,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0))
    | spl2_7 ),
    inference(forward_demodulation,[],[f23624,f19])).

fof(f23624,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_7 ),
    inference(superposition,[],[f17820,f21554])).

fof(f17821,plain,
    ( ~ spl2_7
    | spl2_6 ),
    inference(avatar_split_clause,[],[f17814,f17723,f17818])).

fof(f17723,plain,
    ( spl2_6
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f17814,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | spl2_6 ),
    inference(superposition,[],[f17725,f1412])).

fof(f17725,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f17723])).

fof(f17726,plain,
    ( ~ spl2_6
    | spl2_3 ),
    inference(avatar_split_clause,[],[f17716,f51,f17723])).

fof(f51,plain,
    ( spl2_3
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f17716,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_3 ),
    inference(backward_demodulation,[],[f53,f17517])).

fof(f17517,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,X3))) ),
    inference(superposition,[],[f389,f138])).

fof(f138,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k4_xboole_0(X6,X7),k2_xboole_0(X7,X8)) = k4_xboole_0(X6,k2_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f130,f24])).

fof(f130,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k4_xboole_0(X6,X7),k2_xboole_0(X7,X8)) = k4_xboole_0(k4_xboole_0(X6,X7),X8) ),
    inference(superposition,[],[f24,f47])).

fof(f389,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ),
    inference(resolution,[],[f26,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f17,f18,f21])).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f17,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f53,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f17721,plain,
    ( ~ spl2_5
    | spl2_4 ),
    inference(avatar_split_clause,[],[f17715,f123,f17718])).

fof(f17718,plain,
    ( spl2_5
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f123,plain,
    ( spl2_4
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f17715,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_4 ),
    inference(backward_demodulation,[],[f125,f17517])).

fof(f125,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f127,plain,
    ( ~ spl2_4
    | spl2_3 ),
    inference(avatar_split_clause,[],[f121,f51,f123])).

fof(f121,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_3 ),
    inference(superposition,[],[f53,f16])).

fof(f126,plain,
    ( ~ spl2_4
    | spl2_3 ),
    inference(avatar_split_clause,[],[f120,f51,f123])).

fof(f120,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_3 ),
    inference(superposition,[],[f53,f16])).

fof(f54,plain,
    ( ~ spl2_3
    | spl2_2 ),
    inference(avatar_split_clause,[],[f49,f34,f51])).

fof(f34,plain,
    ( spl2_2
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f49,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl2_2 ),
    inference(backward_demodulation,[],[f36,f48])).

fof(f36,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f37,plain,
    ( ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f32,f28,f34])).

fof(f28,plain,
    ( spl2_1
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f32,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))
    | spl2_1 ),
    inference(forward_demodulation,[],[f30,f24])).

fof(f30,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f31,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f25,f28])).

fof(f25,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f15,f21,f21,f18])).

fof(f15,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:40:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (9513)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (9526)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (9517)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (9518)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (9514)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (9516)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (9527)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (9524)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (9528)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (9522)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.52  % (9519)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (9523)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.52  % (9512)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.52  % (9522)Refutation not found, incomplete strategy% (9522)------------------------------
% 0.21/0.52  % (9522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9522)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9522)Memory used [KB]: 10490
% 0.21/0.52  % (9522)Time elapsed: 0.089 s
% 0.21/0.52  % (9522)------------------------------
% 0.21/0.52  % (9522)------------------------------
% 0.21/0.53  % (9521)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.53  % (9525)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.53  % (9511)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.54  % (9515)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 1.61/0.56  % (9520)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 5.35/1.04  % (9515)Time limit reached!
% 5.35/1.04  % (9515)------------------------------
% 5.35/1.04  % (9515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.35/1.04  % (9515)Termination reason: Time limit
% 5.35/1.04  % (9515)Termination phase: Saturation
% 5.35/1.04  
% 5.35/1.04  % (9515)Memory used [KB]: 13560
% 5.35/1.04  % (9515)Time elapsed: 0.600 s
% 5.35/1.04  % (9515)------------------------------
% 5.35/1.04  % (9515)------------------------------
% 11.23/1.84  % (9521)Refutation found. Thanks to Tanya!
% 11.23/1.84  % SZS status Theorem for theBenchmark
% 11.85/1.85  % SZS output start Proof for theBenchmark
% 11.85/1.85  fof(f24148,plain,(
% 11.85/1.85    $false),
% 11.85/1.85    inference(avatar_sat_refutation,[],[f31,f37,f54,f126,f127,f17721,f17726,f17821,f23977,f24094,f24117,f24119,f24128,f24133,f24138,f24139,f24145,f24146,f24147])).
% 11.85/1.85  fof(f24147,plain,(
% 11.85/1.85    ~spl2_12 | spl2_9),
% 11.85/1.85    inference(avatar_split_clause,[],[f24126,f24114,f24142])).
% 11.85/1.85  fof(f24142,plain,(
% 11.85/1.85    spl2_12 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 11.85/1.85    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 11.85/1.85  fof(f24114,plain,(
% 11.85/1.85    spl2_9 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 11.85/1.85    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 11.85/1.85  fof(f24126,plain,(
% 11.85/1.85    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | spl2_9),
% 11.85/1.85    inference(superposition,[],[f24116,f16])).
% 11.85/1.85  fof(f16,plain,(
% 11.85/1.85    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.85/1.85    inference(cnf_transformation,[],[f1])).
% 11.85/1.85  fof(f1,axiom,(
% 11.85/1.85    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.85/1.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 11.85/1.85  fof(f24116,plain,(
% 11.85/1.85    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) | spl2_9),
% 11.85/1.85    inference(avatar_component_clause,[],[f24114])).
% 11.85/1.85  fof(f24146,plain,(
% 11.85/1.85    ~spl2_12 | spl2_9),
% 11.85/1.85    inference(avatar_split_clause,[],[f24125,f24114,f24142])).
% 11.85/1.85  fof(f24125,plain,(
% 11.85/1.85    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | spl2_9),
% 11.85/1.85    inference(superposition,[],[f24116,f16])).
% 11.85/1.85  fof(f24145,plain,(
% 11.85/1.85    ~spl2_12 | spl2_9),
% 11.85/1.85    inference(avatar_split_clause,[],[f24140,f24114,f24142])).
% 11.85/1.85  fof(f24140,plain,(
% 11.85/1.85    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | spl2_9),
% 11.85/1.85    inference(forward_demodulation,[],[f24124,f16])).
% 11.85/1.85  fof(f24124,plain,(
% 11.85/1.85    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK1)) | spl2_9),
% 11.85/1.85    inference(superposition,[],[f24116,f18537])).
% 11.85/1.85  fof(f18537,plain,(
% 11.85/1.85    ( ! [X19,X17,X18] : (k2_xboole_0(X19,k2_xboole_0(X18,X17)) = k2_xboole_0(k2_xboole_0(X17,X18),X19)) )),
% 11.85/1.85    inference(forward_demodulation,[],[f18536,f42])).
% 11.85/1.85  fof(f42,plain,(
% 11.85/1.85    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) )),
% 11.85/1.85    inference(forward_demodulation,[],[f41,f19])).
% 11.85/1.85  fof(f19,plain,(
% 11.85/1.85    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.85/1.85    inference(cnf_transformation,[],[f4])).
% 11.85/1.85  fof(f4,axiom,(
% 11.85/1.85    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.85/1.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 11.85/1.85  fof(f41,plain,(
% 11.85/1.85    ( ! [X0,X1] : (k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 11.85/1.85    inference(superposition,[],[f19,f20])).
% 11.85/1.85  fof(f20,plain,(
% 11.85/1.85    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 11.85/1.85    inference(cnf_transformation,[],[f5])).
% 11.85/1.85  fof(f5,axiom,(
% 11.85/1.85    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 11.85/1.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 11.85/1.85  fof(f18536,plain,(
% 11.85/1.85    ( ! [X19,X17,X18] : (k2_xboole_0(k2_xboole_0(X17,X18),X19) = k2_xboole_0(X19,k2_xboole_0(X18,k2_xboole_0(X17,X18)))) )),
% 11.85/1.85    inference(forward_demodulation,[],[f18395,f16])).
% 11.85/1.85  fof(f18395,plain,(
% 11.85/1.85    ( ! [X19,X17,X18] : (k2_xboole_0(k2_xboole_0(X17,X18),X19) = k2_xboole_0(X19,k2_xboole_0(k2_xboole_0(X17,X18),X18))) )),
% 11.85/1.85    inference(superposition,[],[f18085,f2359])).
% 11.85/1.85  fof(f2359,plain,(
% 11.85/1.85    ( ! [X23,X21,X22] : (k2_xboole_0(k2_xboole_0(X21,X23),k2_xboole_0(X21,X22)) = k2_xboole_0(k2_xboole_0(X21,X23),X22)) )),
% 11.85/1.85    inference(forward_demodulation,[],[f2317,f19])).
% 11.85/1.85  fof(f2317,plain,(
% 11.85/1.85    ( ! [X23,X21,X22] : (k2_xboole_0(k2_xboole_0(X21,X23),k2_xboole_0(X21,X22)) = k2_xboole_0(k2_xboole_0(X21,X23),k4_xboole_0(X22,k2_xboole_0(X21,X23)))) )),
% 11.85/1.85    inference(superposition,[],[f19,f137])).
% 11.85/1.85  fof(f137,plain,(
% 11.85/1.85    ( ! [X4,X5,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,X5)) = k4_xboole_0(X4,k2_xboole_0(X3,X5))) )),
% 11.85/1.85    inference(forward_demodulation,[],[f129,f24])).
% 11.85/1.85  fof(f24,plain,(
% 11.85/1.85    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 11.85/1.85    inference(cnf_transformation,[],[f6])).
% 11.85/1.85  fof(f6,axiom,(
% 11.85/1.85    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 11.85/1.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 11.85/1.85  fof(f129,plain,(
% 11.85/1.85    ( ! [X4,X5,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,X5)) = k4_xboole_0(k4_xboole_0(X4,X3),X5)) )),
% 11.85/1.85    inference(superposition,[],[f24,f38])).
% 11.85/1.85  fof(f38,plain,(
% 11.85/1.85    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 11.85/1.85    inference(superposition,[],[f20,f16])).
% 11.85/1.85  fof(f18085,plain,(
% 11.85/1.85    ( ! [X10,X9] : (k2_xboole_0(X10,X9) = k2_xboole_0(X9,k2_xboole_0(X10,X10))) )),
% 11.85/1.85    inference(backward_demodulation,[],[f267,f18033])).
% 11.85/1.85  fof(f18033,plain,(
% 11.85/1.85    ( ! [X26,X25] : (k2_xboole_0(X26,X25) = k2_xboole_0(k4_xboole_0(X25,X26),k2_xboole_0(X25,k2_xboole_0(X26,X26)))) )),
% 11.85/1.85    inference(backward_demodulation,[],[f2945,f17876])).
% 11.85/1.85  fof(f17876,plain,(
% 11.85/1.85    ( ! [X4,X5] : (k2_xboole_0(X4,X5) = k2_xboole_0(k2_xboole_0(X4,X4),X5)) )),
% 11.85/1.85    inference(superposition,[],[f16799,f2359])).
% 11.85/1.85  fof(f16799,plain,(
% 11.85/1.85    ( ! [X12,X13] : (k2_xboole_0(X12,X13) = k2_xboole_0(k2_xboole_0(X12,X12),k2_xboole_0(X12,X13))) )),
% 11.85/1.85    inference(superposition,[],[f16512,f16])).
% 11.85/1.85  fof(f16512,plain,(
% 11.85/1.85    ( ! [X24,X25] : (k2_xboole_0(X24,X25) = k2_xboole_0(k2_xboole_0(X24,X25),k2_xboole_0(X24,X24))) )),
% 11.85/1.85    inference(forward_demodulation,[],[f16315,f8174])).
% 11.85/1.85  fof(f8174,plain,(
% 11.85/1.85    ( ! [X54,X55] : (k2_xboole_0(X54,X55) = k2_xboole_0(k2_xboole_0(X54,X55),k4_xboole_0(X54,k4_xboole_0(X54,X54)))) )),
% 11.85/1.85    inference(forward_demodulation,[],[f8173,f48])).
% 11.85/1.85  fof(f48,plain,(
% 11.85/1.85    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2))) )),
% 11.85/1.85    inference(forward_demodulation,[],[f46,f19])).
% 11.85/1.85  fof(f46,plain,(
% 11.85/1.85    ( ! [X2,X1] : (k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X2,X1))) )),
% 11.85/1.85    inference(superposition,[],[f19,f38])).
% 11.85/1.85  fof(f8173,plain,(
% 11.85/1.85    ( ! [X54,X55] : (k2_xboole_0(X54,k2_xboole_0(X54,X55)) = k2_xboole_0(k2_xboole_0(X54,X55),k4_xboole_0(X54,k4_xboole_0(X54,X54)))) )),
% 11.85/1.85    inference(forward_demodulation,[],[f8172,f16])).
% 11.85/1.85  fof(f8172,plain,(
% 11.85/1.85    ( ! [X54,X55] : (k2_xboole_0(k2_xboole_0(X54,X55),X54) = k2_xboole_0(k2_xboole_0(X54,X55),k4_xboole_0(X54,k4_xboole_0(X54,X54)))) )),
% 11.85/1.85    inference(forward_demodulation,[],[f8067,f2359])).
% 11.85/1.85  fof(f8067,plain,(
% 11.85/1.85    ( ! [X54,X55] : (k2_xboole_0(k2_xboole_0(X54,X55),k4_xboole_0(X54,k4_xboole_0(X54,X54))) = k2_xboole_0(k2_xboole_0(X54,X55),k2_xboole_0(X54,X54))) )),
% 11.85/1.85    inference(superposition,[],[f2188,f7826])).
% 11.85/1.85  fof(f7826,plain,(
% 11.85/1.85    ( ! [X7] : (k2_xboole_0(X7,X7) = k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X7)),X7)) )),
% 11.85/1.85    inference(forward_demodulation,[],[f7734,f190])).
% 11.85/1.85  fof(f190,plain,(
% 11.85/1.85    ( ! [X17,X16] : (k2_xboole_0(X17,X16) = k2_xboole_0(k4_xboole_0(X17,k4_xboole_0(X16,X17)),k2_xboole_0(X17,X16))) )),
% 11.85/1.85    inference(forward_demodulation,[],[f172,f40])).
% 11.85/1.85  fof(f40,plain,(
% 11.85/1.85    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4))) )),
% 11.85/1.85    inference(superposition,[],[f20,f19])).
% 11.85/1.85  fof(f172,plain,(
% 11.85/1.85    ( ! [X17,X16] : (k2_xboole_0(X17,X16) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X17,X16),k4_xboole_0(X16,X17)),k2_xboole_0(X17,X16))) )),
% 11.85/1.85    inference(superposition,[],[f62,f62])).
% 11.85/1.85  fof(f62,plain,(
% 11.85/1.85    ( ! [X4,X5] : (k2_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5))) )),
% 11.85/1.85    inference(forward_demodulation,[],[f61,f19])).
% 11.85/1.85  fof(f61,plain,(
% 11.85/1.85    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X5,X4)) = k2_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5))) )),
% 11.85/1.85    inference(forward_demodulation,[],[f57,f16])).
% 11.85/1.85  fof(f57,plain,(
% 11.85/1.85    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X5,X4),X4) = k2_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5))) )),
% 11.85/1.85    inference(superposition,[],[f42,f19])).
% 11.85/1.85  fof(f7734,plain,(
% 11.85/1.85    ( ! [X7] : (k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X7)),X7) = k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X7)),k2_xboole_0(X7,X7))) )),
% 11.85/1.85    inference(superposition,[],[f42,f7414])).
% 11.85/1.85  fof(f7414,plain,(
% 11.85/1.85    ( ! [X1] : (k2_xboole_0(X1,X1) = k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X1)))) )),
% 11.85/1.85    inference(forward_demodulation,[],[f7276,f42])).
% 11.85/1.85  fof(f7276,plain,(
% 11.85/1.85    ( ! [X1] : (k2_xboole_0(X1,k2_xboole_0(X1,X1)) = k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X1)))) )),
% 11.85/1.85    inference(superposition,[],[f356,f190])).
% 11.85/1.85  fof(f356,plain,(
% 11.85/1.85    ( ! [X12,X13] : (k2_xboole_0(X13,X12) = k2_xboole_0(X13,k2_xboole_0(X12,k2_xboole_0(X13,X13)))) )),
% 11.85/1.85    inference(forward_demodulation,[],[f348,f19])).
% 11.85/1.85  fof(f348,plain,(
% 11.85/1.85    ( ! [X12,X13] : (k2_xboole_0(X13,k2_xboole_0(X12,k2_xboole_0(X13,X13))) = k2_xboole_0(X13,k4_xboole_0(X12,X13))) )),
% 11.85/1.85    inference(superposition,[],[f19,f152])).
% 11.85/1.85  fof(f152,plain,(
% 11.85/1.85    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X1)),X1)) )),
% 11.85/1.85    inference(forward_demodulation,[],[f141,f132])).
% 11.85/1.85  fof(f132,plain,(
% 11.85/1.85    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(X1,X1))) )),
% 11.85/1.85    inference(superposition,[],[f24,f47])).
% 11.85/1.85  fof(f47,plain,(
% 11.85/1.85    ( ! [X4,X5] : (k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)) )),
% 11.85/1.85    inference(forward_demodulation,[],[f45,f38])).
% 11.85/1.85  fof(f45,plain,(
% 11.85/1.85    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X5,X4),X4) = k4_xboole_0(k2_xboole_0(X4,X5),X4)) )),
% 11.85/1.85    inference(superposition,[],[f38,f19])).
% 11.85/1.85  fof(f141,plain,(
% 11.85/1.85    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X1)) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X1)),X1)) )),
% 11.85/1.85    inference(superposition,[],[f132,f20])).
% 11.85/1.85  fof(f2188,plain,(
% 11.85/1.85    ( ! [X21,X22,X20] : (k2_xboole_0(k2_xboole_0(X21,X22),k2_xboole_0(X20,X21)) = k2_xboole_0(k2_xboole_0(X21,X22),X20)) )),
% 11.85/1.85    inference(forward_demodulation,[],[f2144,f19])).
% 11.85/1.85  fof(f2144,plain,(
% 11.85/1.85    ( ! [X21,X22,X20] : (k2_xboole_0(k2_xboole_0(X21,X22),k2_xboole_0(X20,X21)) = k2_xboole_0(k2_xboole_0(X21,X22),k4_xboole_0(X20,k2_xboole_0(X21,X22)))) )),
% 11.85/1.85    inference(superposition,[],[f19,f136])).
% 11.85/1.85  fof(f136,plain,(
% 11.85/1.85    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))) )),
% 11.85/1.85    inference(forward_demodulation,[],[f128,f24])).
% 11.85/1.85  fof(f128,plain,(
% 11.85/1.85    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))) )),
% 11.85/1.85    inference(superposition,[],[f24,f20])).
% 11.85/1.85  fof(f16315,plain,(
% 11.85/1.85    ( ! [X24,X25] : (k2_xboole_0(k2_xboole_0(X24,X25),k2_xboole_0(X24,X24)) = k2_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,k4_xboole_0(X24,X24)))) )),
% 11.85/1.85    inference(superposition,[],[f2359,f7414])).
% 11.85/1.85  fof(f2945,plain,(
% 11.85/1.85    ( ! [X26,X25] : (k2_xboole_0(k2_xboole_0(X26,X26),X25) = k2_xboole_0(k4_xboole_0(X25,X26),k2_xboole_0(X25,k2_xboole_0(X26,X26)))) )),
% 11.85/1.85    inference(superposition,[],[f2895,f132])).
% 11.85/1.85  fof(f2895,plain,(
% 11.85/1.85    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2))) )),
% 11.85/1.85    inference(forward_demodulation,[],[f2894,f19])).
% 11.85/1.85  fof(f2894,plain,(
% 11.85/1.85    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k4_xboole_0(X1,X2))) )),
% 11.85/1.85    inference(forward_demodulation,[],[f2893,f16])).
% 11.85/1.85  fof(f2893,plain,(
% 11.85/1.85    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),X2)) )),
% 11.85/1.85    inference(forward_demodulation,[],[f2846,f19])).
% 11.85/1.85  fof(f2846,plain,(
% 11.85/1.85    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X1,X2)))) )),
% 11.85/1.85    inference(superposition,[],[f19,f1355])).
% 11.85/1.85  fof(f1355,plain,(
% 11.85/1.85    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,X0))) )),
% 11.85/1.85    inference(superposition,[],[f40,f16])).
% 11.85/1.85  fof(f267,plain,(
% 11.85/1.85    ( ! [X10,X9] : (k2_xboole_0(X9,k2_xboole_0(X10,X10)) = k2_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X9,k2_xboole_0(X10,X10)))) )),
% 11.85/1.85    inference(superposition,[],[f164,f132])).
% 11.85/1.85  fof(f164,plain,(
% 11.85/1.85    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X1,X0))) )),
% 11.85/1.85    inference(superposition,[],[f62,f16])).
% 11.85/1.85  fof(f24139,plain,(
% 11.85/1.85    ~spl2_11 | spl2_9),
% 11.85/1.85    inference(avatar_split_clause,[],[f24123,f24114,f24135])).
% 11.85/1.85  fof(f24135,plain,(
% 11.85/1.85    spl2_11 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 11.85/1.85    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 11.85/1.85  fof(f24123,plain,(
% 11.85/1.85    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_9),
% 11.85/1.85    inference(superposition,[],[f24116,f21554])).
% 11.85/1.85  fof(f21554,plain,(
% 11.85/1.85    ( ! [X12,X13,X11] : (k2_xboole_0(X11,k2_xboole_0(X12,X13)) = k2_xboole_0(X13,k2_xboole_0(X12,X11))) )),
% 11.85/1.85    inference(superposition,[],[f21327,f18537])).
% 11.85/1.86  fof(f21327,plain,(
% 11.85/1.86    ( ! [X52,X50,X51] : (k2_xboole_0(k2_xboole_0(X51,X50),X52) = k2_xboole_0(X51,k2_xboole_0(X50,X52))) )),
% 11.85/1.86    inference(forward_demodulation,[],[f21116,f21017])).
% 11.85/1.86  fof(f21017,plain,(
% 11.85/1.86    ( ! [X74,X72,X73] : (k2_xboole_0(X73,k2_xboole_0(X72,X74)) = k2_xboole_0(k2_xboole_0(X73,X72),k2_xboole_0(X73,k2_xboole_0(X72,X74)))) )),
% 11.85/1.86    inference(backward_demodulation,[],[f6747,f20920])).
% 11.85/1.86  fof(f20920,plain,(
% 11.85/1.86    ( ! [X57,X58,X56] : (k2_xboole_0(X58,k2_xboole_0(X56,X57)) = k2_xboole_0(k2_xboole_0(X56,X58),X57)) )),
% 11.85/1.86    inference(forward_demodulation,[],[f20919,f20650])).
% 11.85/1.86  fof(f20650,plain,(
% 11.85/1.86    ( ! [X70,X71] : (k2_xboole_0(X70,X71) = k2_xboole_0(k2_xboole_0(X71,X70),X71)) )),
% 11.85/1.86    inference(forward_demodulation,[],[f20649,f77])).
% 11.85/1.86  fof(f77,plain,(
% 11.85/1.86    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2))) )),
% 11.85/1.86    inference(forward_demodulation,[],[f76,f48])).
% 11.85/1.86  fof(f76,plain,(
% 11.85/1.86    ( ! [X2,X1] : (k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2))) )),
% 11.85/1.86    inference(forward_demodulation,[],[f74,f16])).
% 11.85/1.86  fof(f74,plain,(
% 11.85/1.86    ( ! [X2,X1] : (k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2))) )),
% 11.85/1.86    inference(superposition,[],[f42,f48])).
% 11.85/1.86  fof(f20649,plain,(
% 11.85/1.86    ( ! [X70,X71] : (k2_xboole_0(k2_xboole_0(X71,X70),X71) = k2_xboole_0(k2_xboole_0(X70,X71),k2_xboole_0(X70,X71))) )),
% 11.85/1.86    inference(forward_demodulation,[],[f20522,f20037])).
% 11.85/1.86  fof(f20037,plain,(
% 11.85/1.86    ( ! [X37,X35,X36] : (k2_xboole_0(k2_xboole_0(X35,X36),X37) = k2_xboole_0(k4_xboole_0(X37,X35),k2_xboole_0(X36,X35))) )),
% 11.85/1.86    inference(superposition,[],[f18537,f2010])).
% 11.85/1.86  fof(f2010,plain,(
% 11.85/1.86    ( ! [X24,X23,X22] : (k2_xboole_0(k2_xboole_0(X22,X23),k4_xboole_0(X24,X22)) = k2_xboole_0(k2_xboole_0(X22,X23),X24)) )),
% 11.85/1.86    inference(forward_demodulation,[],[f1950,f19])).
% 11.85/1.86  fof(f1950,plain,(
% 11.85/1.86    ( ! [X24,X23,X22] : (k2_xboole_0(k2_xboole_0(X22,X23),k4_xboole_0(X24,X22)) = k2_xboole_0(k2_xboole_0(X22,X23),k4_xboole_0(X24,k2_xboole_0(X22,X23)))) )),
% 11.85/1.86    inference(superposition,[],[f135,f48])).
% 11.85/1.86  fof(f135,plain,(
% 11.85/1.86    ( ! [X6,X7,X5] : (k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))) )),
% 11.85/1.86    inference(superposition,[],[f19,f24])).
% 11.85/1.86  fof(f20522,plain,(
% 11.85/1.86    ( ! [X70,X71] : (k2_xboole_0(k2_xboole_0(X70,X71),k2_xboole_0(X70,X71)) = k2_xboole_0(k4_xboole_0(X71,X71),k2_xboole_0(X70,X71))) )),
% 11.85/1.86    inference(superposition,[],[f20027,f11618])).
% 11.85/1.86  fof(f11618,plain,(
% 11.85/1.86    ( ! [X10,X9] : (k2_xboole_0(X10,X9) = k2_xboole_0(k2_xboole_0(X10,X9),k4_xboole_0(X9,X9))) )),
% 11.85/1.86    inference(superposition,[],[f9881,f16])).
% 11.85/1.86  fof(f9881,plain,(
% 11.85/1.86    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X3,X3),k2_xboole_0(X2,X3))) )),
% 11.85/1.86    inference(forward_demodulation,[],[f9692,f280])).
% 11.85/1.86  fof(f280,plain,(
% 11.85/1.86    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X3,X4))) )),
% 11.85/1.86    inference(superposition,[],[f164,f16])).
% 11.85/1.86  fof(f9692,plain,(
% 11.85/1.86    ( ! [X2,X3] : (k2_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X3,X3),k2_xboole_0(X2,X3))) )),
% 11.85/1.86    inference(superposition,[],[f9320,f20])).
% 11.85/1.86  fof(f9320,plain,(
% 11.85/1.86    ( ! [X8,X9] : (k2_xboole_0(X8,k4_xboole_0(X8,X9)) = k2_xboole_0(k4_xboole_0(X9,X9),X8)) )),
% 11.85/1.86    inference(superposition,[],[f9144,f16])).
% 11.85/1.86  fof(f9144,plain,(
% 11.85/1.86    ( ! [X26,X27] : (k2_xboole_0(X26,k4_xboole_0(X27,X27)) = k2_xboole_0(X26,k4_xboole_0(X26,X27))) )),
% 11.85/1.86    inference(forward_demodulation,[],[f9143,f132])).
% 11.85/1.86  fof(f9143,plain,(
% 11.85/1.86    ( ! [X26,X27] : (k2_xboole_0(X26,k4_xboole_0(X27,X27)) = k2_xboole_0(X26,k4_xboole_0(X26,k2_xboole_0(X27,X27)))) )),
% 11.85/1.86    inference(forward_demodulation,[],[f9142,f24])).
% 11.85/1.86  fof(f9142,plain,(
% 11.85/1.86    ( ! [X26,X27] : (k2_xboole_0(X26,k4_xboole_0(X27,X27)) = k2_xboole_0(X26,k4_xboole_0(k4_xboole_0(X26,X27),X27))) )),
% 11.85/1.86    inference(forward_demodulation,[],[f9141,f135])).
% 11.85/1.86  fof(f9141,plain,(
% 11.85/1.86    ( ! [X26,X27] : (k2_xboole_0(X26,k4_xboole_0(k4_xboole_0(X26,X27),X27)) = k2_xboole_0(X26,k4_xboole_0(X27,k2_xboole_0(X27,X26)))) )),
% 11.85/1.86    inference(forward_demodulation,[],[f9001,f16])).
% 11.85/1.86  fof(f9001,plain,(
% 11.85/1.86    ( ! [X26,X27] : (k2_xboole_0(X26,k4_xboole_0(k4_xboole_0(X26,X27),X27)) = k2_xboole_0(k4_xboole_0(X27,k2_xboole_0(X27,X26)),X26)) )),
% 11.85/1.86    inference(superposition,[],[f1440,f191])).
% 11.85/1.86  fof(f191,plain,(
% 11.85/1.86    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),k2_xboole_0(X5,X4)) = k4_xboole_0(X5,k2_xboole_0(X5,X4))) )),
% 11.85/1.86    inference(forward_demodulation,[],[f177,f75])).
% 11.85/1.86  fof(f75,plain,(
% 11.85/1.86    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6))) )),
% 11.85/1.86    inference(superposition,[],[f20,f48])).
% 11.85/1.86  fof(f177,plain,(
% 11.85/1.86    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),k2_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X5,X4),k2_xboole_0(X5,X4))) )),
% 11.85/1.86    inference(superposition,[],[f20,f62])).
% 11.85/1.86  fof(f1440,plain,(
% 11.85/1.86    ( ! [X14,X12,X13] : (k2_xboole_0(X14,k4_xboole_0(X12,X13)) = k2_xboole_0(k4_xboole_0(X12,k2_xboole_0(X13,X14)),X14)) )),
% 11.85/1.86    inference(superposition,[],[f1412,f24])).
% 11.85/1.86  fof(f1412,plain,(
% 11.85/1.86    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 11.85/1.86    inference(forward_demodulation,[],[f1411,f62])).
% 11.85/1.86  fof(f1411,plain,(
% 11.85/1.86    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,X0),X0) = k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1))) )),
% 11.85/1.86    inference(forward_demodulation,[],[f1375,f19])).
% 11.85/1.86  fof(f1375,plain,(
% 11.85/1.86    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 11.85/1.86    inference(superposition,[],[f19,f40])).
% 11.85/1.86  fof(f20027,plain,(
% 11.85/1.86    ( ! [X4,X5] : (k2_xboole_0(X4,X5) = k2_xboole_0(X5,k2_xboole_0(X5,X4))) )),
% 11.85/1.86    inference(superposition,[],[f18537,f89])).
% 11.85/1.86  fof(f89,plain,(
% 11.85/1.86    ( ! [X12,X11] : (k2_xboole_0(X12,X11) = k2_xboole_0(k2_xboole_0(X12,X11),X11)) )),
% 11.85/1.86    inference(forward_demodulation,[],[f87,f77])).
% 11.85/1.86  fof(f87,plain,(
% 11.85/1.86    ( ! [X12,X11] : (k2_xboole_0(k2_xboole_0(X12,X11),X11) = k2_xboole_0(k2_xboole_0(X12,X11),k2_xboole_0(X12,X11))) )),
% 11.85/1.86    inference(superposition,[],[f42,f69])).
% 11.85/1.86  fof(f69,plain,(
% 11.85/1.86    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 11.85/1.86    inference(superposition,[],[f48,f16])).
% 11.85/1.86  fof(f20919,plain,(
% 11.85/1.86    ( ! [X57,X58,X56] : (k2_xboole_0(k2_xboole_0(X56,X58),X57) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X56,X57),X58),k2_xboole_0(X56,X57))) )),
% 11.85/1.86    inference(forward_demodulation,[],[f20782,f2359])).
% 11.85/1.86  fof(f20782,plain,(
% 11.85/1.86    ( ! [X57,X58,X56] : (k2_xboole_0(k2_xboole_0(k2_xboole_0(X56,X57),X58),k2_xboole_0(X56,X57)) = k2_xboole_0(k2_xboole_0(X56,X58),k2_xboole_0(X56,X57))) )),
% 11.85/1.86    inference(superposition,[],[f20650,f2359])).
% 11.85/1.86  fof(f6747,plain,(
% 11.85/1.86    ( ! [X74,X72,X73] : (k2_xboole_0(k2_xboole_0(X72,X73),X74) = k2_xboole_0(k2_xboole_0(X73,X72),k2_xboole_0(k2_xboole_0(X72,X73),X74))) )),
% 11.85/1.86    inference(backward_demodulation,[],[f6744,f6746])).
% 11.85/1.86  fof(f6746,plain,(
% 11.85/1.86    ( ! [X76,X77,X75] : (k2_xboole_0(k2_xboole_0(X75,X76),X77) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X75,X76),X77),k4_xboole_0(X75,X76))) )),
% 11.85/1.86    inference(forward_demodulation,[],[f6745,f48])).
% 11.85/1.86  fof(f6745,plain,(
% 11.85/1.86    ( ! [X76,X77,X75] : (k2_xboole_0(k2_xboole_0(k2_xboole_0(X75,X76),X77),k4_xboole_0(X75,X76)) = k2_xboole_0(k2_xboole_0(X75,X76),k2_xboole_0(k2_xboole_0(X75,X76),X77))) )),
% 11.85/1.86    inference(forward_demodulation,[],[f6603,f16])).
% 11.85/1.86  fof(f6603,plain,(
% 11.85/1.86    ( ! [X76,X77,X75] : (k2_xboole_0(k2_xboole_0(k2_xboole_0(X75,X76),X77),k4_xboole_0(X75,X76)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X75,X76),X77),k2_xboole_0(X75,X76))) )),
% 11.85/1.86    inference(superposition,[],[f2188,f164])).
% 11.85/1.86  fof(f6744,plain,(
% 11.85/1.86    ( ! [X74,X72,X73] : (k2_xboole_0(k2_xboole_0(k2_xboole_0(X72,X73),X74),k4_xboole_0(X72,X73)) = k2_xboole_0(k2_xboole_0(X73,X72),k2_xboole_0(k2_xboole_0(X72,X73),X74))) )),
% 11.85/1.86    inference(forward_demodulation,[],[f6602,f16])).
% 11.85/1.86  fof(f6602,plain,(
% 11.85/1.86    ( ! [X74,X72,X73] : (k2_xboole_0(k2_xboole_0(k2_xboole_0(X72,X73),X74),k4_xboole_0(X72,X73)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X72,X73),X74),k2_xboole_0(X73,X72))) )),
% 11.85/1.86    inference(superposition,[],[f2188,f2895])).
% 11.85/1.86  fof(f21116,plain,(
% 11.85/1.86    ( ! [X52,X50,X51] : (k2_xboole_0(k2_xboole_0(X51,X50),X52) = k2_xboole_0(k2_xboole_0(X51,X50),k2_xboole_0(X51,k2_xboole_0(X50,X52)))) )),
% 11.85/1.86    inference(backward_demodulation,[],[f16282,f20920])).
% 11.85/1.86  fof(f16282,plain,(
% 11.85/1.86    ( ! [X52,X50,X51] : (k2_xboole_0(k2_xboole_0(X51,X50),k2_xboole_0(k2_xboole_0(X50,X51),X52)) = k2_xboole_0(k2_xboole_0(X51,X50),X52)) )),
% 11.85/1.86    inference(superposition,[],[f2359,f3046])).
% 11.85/1.86  fof(f3046,plain,(
% 11.85/1.86    ( ! [X12,X11] : (k2_xboole_0(k2_xboole_0(X12,X11),X11) = k2_xboole_0(X11,X12)) )),
% 11.85/1.86    inference(forward_demodulation,[],[f2951,f242])).
% 11.85/1.86  fof(f242,plain,(
% 11.85/1.86    ( ! [X14,X15] : (k2_xboole_0(X15,X14) = k2_xboole_0(k4_xboole_0(X15,k2_xboole_0(X14,X15)),k2_xboole_0(X15,X14))) )),
% 11.85/1.86    inference(forward_demodulation,[],[f220,f136])).
% 11.85/1.86  fof(f220,plain,(
% 11.85/1.86    ( ! [X14,X15] : (k2_xboole_0(X15,X14) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X15,X14),k2_xboole_0(X14,X15)),k2_xboole_0(X15,X14))) )),
% 11.85/1.86    inference(superposition,[],[f62,f64])).
% 11.85/1.86  fof(f64,plain,(
% 11.85/1.86    ( ! [X6,X7] : (k2_xboole_0(X6,X7) = k2_xboole_0(k2_xboole_0(X7,X6),k2_xboole_0(X6,X7))) )),
% 11.85/1.86    inference(forward_demodulation,[],[f63,f42])).
% 11.85/1.86  fof(f63,plain,(
% 11.85/1.86    ( ! [X6,X7] : (k2_xboole_0(X6,k2_xboole_0(X7,X6)) = k2_xboole_0(k2_xboole_0(X7,X6),k2_xboole_0(X6,X7))) )),
% 11.85/1.86    inference(forward_demodulation,[],[f58,f16])).
% 11.85/1.86  fof(f58,plain,(
% 11.85/1.86    ( ! [X6,X7] : (k2_xboole_0(k2_xboole_0(X7,X6),X6) = k2_xboole_0(k2_xboole_0(X7,X6),k2_xboole_0(X6,X7))) )),
% 11.85/1.86    inference(superposition,[],[f42,f42])).
% 11.85/1.86  fof(f2951,plain,(
% 11.85/1.86    ( ! [X12,X11] : (k2_xboole_0(k2_xboole_0(X12,X11),X11) = k2_xboole_0(k4_xboole_0(X11,k2_xboole_0(X12,X11)),k2_xboole_0(X11,X12))) )),
% 11.85/1.86    inference(superposition,[],[f2895,f42])).
% 11.85/1.86  fof(f24138,plain,(
% 11.85/1.86    ~spl2_11 | spl2_9),
% 11.85/1.86    inference(avatar_split_clause,[],[f24122,f24114,f24135])).
% 11.85/1.86  fof(f24122,plain,(
% 11.85/1.86    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_9),
% 11.85/1.86    inference(superposition,[],[f24116,f21554])).
% 11.85/1.86  fof(f24133,plain,(
% 11.85/1.86    ~spl2_10 | spl2_9),
% 11.85/1.86    inference(avatar_split_clause,[],[f24120,f24114,f24130])).
% 11.85/1.86  fof(f24130,plain,(
% 11.85/1.86    spl2_10 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK0)),
% 11.85/1.86    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 11.85/1.86  fof(f24120,plain,(
% 11.85/1.86    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK0) | spl2_9),
% 11.85/1.86    inference(superposition,[],[f24116,f2895])).
% 11.85/1.86  fof(f24128,plain,(
% 11.85/1.86    spl2_9),
% 11.85/1.86    inference(avatar_contradiction_clause,[],[f24127])).
% 11.85/1.86  fof(f24127,plain,(
% 11.85/1.86    $false | spl2_9),
% 11.85/1.86    inference(trivial_inequality_removal,[],[f24121])).
% 11.85/1.86  fof(f24121,plain,(
% 11.85/1.86    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) | spl2_9),
% 11.85/1.86    inference(superposition,[],[f24116,f164])).
% 11.85/1.86  fof(f24119,plain,(
% 11.85/1.86    ~spl2_9 | spl2_8),
% 11.85/1.86    inference(avatar_split_clause,[],[f24118,f23974,f24114])).
% 11.85/1.86  fof(f23974,plain,(
% 11.85/1.86    spl2_8 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 11.85/1.86    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 11.85/1.86  fof(f24118,plain,(
% 11.85/1.86    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) | spl2_8),
% 11.85/1.86    inference(forward_demodulation,[],[f24111,f19])).
% 11.85/1.86  fof(f24111,plain,(
% 11.85/1.86    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))) | spl2_8),
% 11.85/1.86    inference(superposition,[],[f23976,f21554])).
% 11.85/1.86  fof(f23976,plain,(
% 11.85/1.86    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_8),
% 11.85/1.86    inference(avatar_component_clause,[],[f23974])).
% 11.85/1.86  fof(f24117,plain,(
% 11.85/1.86    ~spl2_9 | spl2_8),
% 11.85/1.86    inference(avatar_split_clause,[],[f24112,f23974,f24114])).
% 11.85/1.86  fof(f24112,plain,(
% 11.85/1.86    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) | spl2_8),
% 11.85/1.86    inference(forward_demodulation,[],[f24110,f19])).
% 11.85/1.86  fof(f24110,plain,(
% 11.85/1.86    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))) | spl2_8),
% 11.85/1.86    inference(superposition,[],[f23976,f21554])).
% 11.85/1.86  fof(f24094,plain,(
% 11.85/1.86    ~spl2_8 | spl2_7),
% 11.85/1.86    inference(avatar_split_clause,[],[f24093,f17818,f23974])).
% 11.85/1.86  fof(f17818,plain,(
% 11.85/1.86    spl2_7 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),
% 11.85/1.86    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 11.85/1.86  fof(f24093,plain,(
% 11.85/1.86    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_7),
% 11.85/1.86    inference(forward_demodulation,[],[f24092,f16])).
% 11.85/1.87  fof(f24092,plain,(
% 11.85/1.87    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) | spl2_7),
% 11.85/1.87    inference(forward_demodulation,[],[f23753,f19])).
% 11.85/1.87  fof(f23753,plain,(
% 11.85/1.87    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_7),
% 11.85/1.87    inference(superposition,[],[f17820,f21554])).
% 11.85/1.87  fof(f17820,plain,(
% 11.85/1.87    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | spl2_7),
% 11.85/1.87    inference(avatar_component_clause,[],[f17818])).
% 11.85/1.87  fof(f23977,plain,(
% 11.85/1.87    ~spl2_8 | spl2_7),
% 11.85/1.87    inference(avatar_split_clause,[],[f23972,f17818,f23974])).
% 11.85/1.87  fof(f23972,plain,(
% 11.85/1.87    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_7),
% 11.85/1.87    inference(forward_demodulation,[],[f23971,f16])).
% 11.85/1.87  fof(f23971,plain,(
% 11.85/1.87    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) | spl2_7),
% 11.85/1.87    inference(forward_demodulation,[],[f23624,f19])).
% 11.85/1.87  fof(f23624,plain,(
% 11.85/1.87    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_7),
% 11.85/1.87    inference(superposition,[],[f17820,f21554])).
% 11.85/1.87  fof(f17821,plain,(
% 11.85/1.87    ~spl2_7 | spl2_6),
% 11.85/1.87    inference(avatar_split_clause,[],[f17814,f17723,f17818])).
% 11.85/1.87  fof(f17723,plain,(
% 11.85/1.87    spl2_6 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 11.85/1.87    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 11.85/1.87  fof(f17814,plain,(
% 11.85/1.87    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | spl2_6),
% 11.85/1.87    inference(superposition,[],[f17725,f1412])).
% 11.85/1.87  fof(f17725,plain,(
% 11.85/1.87    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_6),
% 11.85/1.87    inference(avatar_component_clause,[],[f17723])).
% 11.85/1.87  fof(f17726,plain,(
% 11.85/1.87    ~spl2_6 | spl2_3),
% 11.85/1.87    inference(avatar_split_clause,[],[f17716,f51,f17723])).
% 11.85/1.87  fof(f51,plain,(
% 11.85/1.87    spl2_3 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 11.85/1.87    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 11.85/1.87  fof(f17716,plain,(
% 11.85/1.87    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_3),
% 11.85/1.87    inference(backward_demodulation,[],[f53,f17517])).
% 11.85/1.87  fof(f17517,plain,(
% 11.85/1.87    ( ! [X4,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,X3)))) )),
% 11.85/1.87    inference(superposition,[],[f389,f138])).
% 11.85/1.87  fof(f138,plain,(
% 11.85/1.87    ( ! [X6,X8,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),k2_xboole_0(X7,X8)) = k4_xboole_0(X6,k2_xboole_0(X7,X8))) )),
% 11.85/1.87    inference(forward_demodulation,[],[f130,f24])).
% 11.85/1.87  fof(f130,plain,(
% 11.85/1.87    ( ! [X6,X8,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),k2_xboole_0(X7,X8)) = k4_xboole_0(k4_xboole_0(X6,X7),X8)) )),
% 11.85/1.87    inference(superposition,[],[f24,f47])).
% 11.85/1.87  fof(f389,plain,(
% 11.85/1.87    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) )),
% 11.85/1.87    inference(resolution,[],[f26,f22])).
% 11.85/1.87  fof(f22,plain,(
% 11.85/1.87    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 11.85/1.87    inference(cnf_transformation,[],[f14])).
% 11.85/1.87  fof(f14,plain,(
% 11.85/1.87    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 11.85/1.87    inference(nnf_transformation,[],[f8])).
% 11.85/1.87  fof(f8,axiom,(
% 11.85/1.87    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 11.85/1.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 11.85/1.87  fof(f26,plain,(
% 11.85/1.87    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) )),
% 11.85/1.87    inference(definition_unfolding,[],[f17,f18,f21])).
% 11.85/1.87  fof(f21,plain,(
% 11.85/1.87    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 11.85/1.87    inference(cnf_transformation,[],[f2])).
% 11.85/1.87  fof(f2,axiom,(
% 11.85/1.87    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 11.85/1.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 11.85/1.87  fof(f18,plain,(
% 11.85/1.87    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.85/1.87    inference(cnf_transformation,[],[f7])).
% 11.85/1.87  fof(f7,axiom,(
% 11.85/1.87    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.85/1.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 11.85/1.87  fof(f17,plain,(
% 11.85/1.87    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 11.85/1.87    inference(cnf_transformation,[],[f3])).
% 11.85/1.87  fof(f3,axiom,(
% 11.85/1.87    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 11.85/1.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).
% 11.85/1.87  fof(f53,plain,(
% 11.85/1.87    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl2_3),
% 11.85/1.87    inference(avatar_component_clause,[],[f51])).
% 11.85/1.87  fof(f17721,plain,(
% 11.85/1.87    ~spl2_5 | spl2_4),
% 11.85/1.87    inference(avatar_split_clause,[],[f17715,f123,f17718])).
% 11.85/1.87  fof(f17718,plain,(
% 11.85/1.87    spl2_5 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 11.85/1.87    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 11.85/1.87  fof(f123,plain,(
% 11.85/1.87    spl2_4 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 11.85/1.87    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 11.85/1.87  fof(f17715,plain,(
% 11.85/1.87    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_4),
% 11.85/1.87    inference(backward_demodulation,[],[f125,f17517])).
% 11.85/1.87  fof(f125,plain,(
% 11.85/1.87    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_4),
% 11.85/1.87    inference(avatar_component_clause,[],[f123])).
% 11.85/1.87  fof(f127,plain,(
% 11.85/1.87    ~spl2_4 | spl2_3),
% 11.85/1.87    inference(avatar_split_clause,[],[f121,f51,f123])).
% 11.85/1.87  fof(f121,plain,(
% 11.85/1.87    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_3),
% 11.85/1.87    inference(superposition,[],[f53,f16])).
% 11.85/1.87  fof(f126,plain,(
% 11.85/1.87    ~spl2_4 | spl2_3),
% 11.85/1.87    inference(avatar_split_clause,[],[f120,f51,f123])).
% 11.85/1.87  fof(f120,plain,(
% 11.85/1.87    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_3),
% 11.85/1.87    inference(superposition,[],[f53,f16])).
% 11.85/1.87  fof(f54,plain,(
% 11.85/1.87    ~spl2_3 | spl2_2),
% 11.85/1.87    inference(avatar_split_clause,[],[f49,f34,f51])).
% 11.85/1.87  fof(f34,plain,(
% 11.85/1.87    spl2_2 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 11.85/1.87    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 11.85/1.87  fof(f49,plain,(
% 11.85/1.87    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl2_2),
% 11.85/1.87    inference(backward_demodulation,[],[f36,f48])).
% 11.85/1.87  fof(f36,plain,(
% 11.85/1.87    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) | spl2_2),
% 11.85/1.87    inference(avatar_component_clause,[],[f34])).
% 11.85/1.87  fof(f37,plain,(
% 11.85/1.87    ~spl2_2 | spl2_1),
% 11.85/1.87    inference(avatar_split_clause,[],[f32,f28,f34])).
% 11.85/1.87  fof(f28,plain,(
% 11.85/1.87    spl2_1 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 11.85/1.87    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 11.85/1.87  fof(f32,plain,(
% 11.85/1.87    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) | spl2_1),
% 11.85/1.87    inference(forward_demodulation,[],[f30,f24])).
% 11.85/1.87  fof(f30,plain,(
% 11.85/1.87    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl2_1),
% 11.85/1.87    inference(avatar_component_clause,[],[f28])).
% 11.85/1.87  fof(f31,plain,(
% 11.85/1.87    ~spl2_1),
% 11.85/1.87    inference(avatar_split_clause,[],[f25,f28])).
% 11.85/1.87  fof(f25,plain,(
% 11.85/1.87    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 11.85/1.87    inference(definition_unfolding,[],[f15,f21,f21,f18])).
% 11.85/1.87  fof(f15,plain,(
% 11.85/1.87    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 11.85/1.87    inference(cnf_transformation,[],[f13])).
% 11.85/1.87  fof(f13,plain,(
% 11.85/1.87    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 11.85/1.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 11.85/1.87  fof(f12,plain,(
% 11.85/1.87    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 11.85/1.87    introduced(choice_axiom,[])).
% 11.85/1.87  fof(f11,plain,(
% 11.85/1.87    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 11.85/1.87    inference(ennf_transformation,[],[f10])).
% 11.85/1.87  fof(f10,negated_conjecture,(
% 11.85/1.87    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 11.85/1.87    inference(negated_conjecture,[],[f9])).
% 11.85/1.87  fof(f9,conjecture,(
% 11.85/1.87    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 11.85/1.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 11.85/1.87  % SZS output end Proof for theBenchmark
% 11.85/1.87  % (9521)------------------------------
% 11.85/1.87  % (9521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.85/1.87  % (9521)Termination reason: Refutation
% 11.85/1.87  
% 11.85/1.87  % (9521)Memory used [KB]: 25330
% 11.85/1.87  % (9521)Time elapsed: 1.389 s
% 11.85/1.87  % (9521)------------------------------
% 11.85/1.87  % (9521)------------------------------
% 11.85/1.87  % (9510)Success in time 1.507 s
%------------------------------------------------------------------------------
