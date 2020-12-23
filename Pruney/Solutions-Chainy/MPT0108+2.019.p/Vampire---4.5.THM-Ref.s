%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:20 EST 2020

% Result     : Theorem 12.97s
% Output     : Refutation 12.97s
% Verified   : 
% Statistics : Number of formulae       :  121 (2081 expanded)
%              Number of leaves         :   15 ( 636 expanded)
%              Depth                    :   38
%              Number of atoms          :  127 (2088 expanded)
%              Number of equality atoms :  117 (2077 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57825,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f76,f57738])).

fof(f57738,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f57737])).

fof(f57737,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f57251,f21])).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f57251,plain,
    ( k5_xboole_0(sK0,sK1) != k5_xboole_0(sK1,sK0)
    | spl2_1 ),
    inference(superposition,[],[f40,f39819])).

fof(f39819,plain,(
    ! [X94,X95] : k5_xboole_0(X95,X94) = k4_xboole_0(k2_xboole_0(X94,X95),k3_xboole_0(X94,X95)) ),
    inference(forward_demodulation,[],[f39818,f927])).

fof(f927,plain,(
    ! [X4,X3] : k5_xboole_0(X3,X4) = k3_xboole_0(k5_xboole_0(X3,X4),k2_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f926,f174])).

fof(f174,plain,(
    ! [X2] : k2_xboole_0(k1_xboole_0,X2) = X2 ),
    inference(superposition,[],[f156,f52])).

fof(f52,plain,(
    ! [X3] : k4_xboole_0(X3,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f46,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f46,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f45,f21])).

fof(f45,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f43,f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f43,plain,(
    ! [X2] : k2_xboole_0(X2,X2) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f24,f32])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f23,f19])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f156,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f150,f45])).

fof(f150,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f25,f139])).

fof(f139,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f129,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f129,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f113,f45])).

fof(f113,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(superposition,[],[f109,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f109,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f108,f32])).

fof(f108,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f101,f52])).

fof(f101,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f25,f88])).

fof(f88,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f26,f32])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f926,plain,(
    ! [X4,X3] : k3_xboole_0(k5_xboole_0(X3,X4),k2_xboole_0(X4,X3)) = k2_xboole_0(k1_xboole_0,k5_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f894,f52])).

fof(f894,plain,(
    ! [X4,X3] : k3_xboole_0(k5_xboole_0(X3,X4),k2_xboole_0(X4,X3)) = k4_xboole_0(k5_xboole_0(X3,X4),k1_xboole_0) ),
    inference(superposition,[],[f26,f524])).

fof(f524,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f485,f21])).

fof(f485,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X4,X5),k2_xboole_0(X4,X5)) ),
    inference(superposition,[],[f23,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f39818,plain,(
    ! [X94,X95] : k4_xboole_0(k2_xboole_0(X94,X95),k3_xboole_0(X94,X95)) = k3_xboole_0(k5_xboole_0(X95,X94),k2_xboole_0(X94,X95)) ),
    inference(forward_demodulation,[],[f39817,f20])).

fof(f39817,plain,(
    ! [X94,X95] : k3_xboole_0(k2_xboole_0(X94,X95),k5_xboole_0(X95,X94)) = k4_xboole_0(k2_xboole_0(X94,X95),k3_xboole_0(X94,X95)) ),
    inference(forward_demodulation,[],[f39816,f1020])).

fof(f1020,plain,(
    ! [X17,X16] : k3_xboole_0(X16,X17) = k5_xboole_0(X16,k4_xboole_0(X16,X17)) ),
    inference(forward_demodulation,[],[f1010,f26])).

fof(f1010,plain,(
    ! [X17,X16] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k5_xboole_0(X16,k4_xboole_0(X16,X17)) ),
    inference(superposition,[],[f59,f601])).

fof(f601,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f593,f156])).

fof(f593,plain,(
    ! [X0,X1] : k3_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[],[f26,f550])).

fof(f550,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5) ),
    inference(forward_demodulation,[],[f526,f22])).

fof(f526,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,k3_xboole_0(X5,X6))) ),
    inference(superposition,[],[f485,f25])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f25,f20])).

fof(f39816,plain,(
    ! [X94,X95] : k3_xboole_0(k2_xboole_0(X94,X95),k5_xboole_0(X95,X94)) = k4_xboole_0(k2_xboole_0(X94,X95),k5_xboole_0(X94,k4_xboole_0(X94,X95))) ),
    inference(forward_demodulation,[],[f39815,f19417])).

fof(f19417,plain,(
    ! [X101,X102,X100] : k5_xboole_0(X101,k5_xboole_0(X102,k2_xboole_0(X100,X101))) = k5_xboole_0(X102,k4_xboole_0(X100,X101)) ),
    inference(superposition,[],[f2166,f12352])).

fof(f12352,plain,(
    ! [X24,X23] : k4_xboole_0(X24,X23) = k5_xboole_0(k2_xboole_0(X24,X23),X23) ),
    inference(superposition,[],[f2326,f12232])).

fof(f12232,plain,(
    ! [X6,X5] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(superposition,[],[f12183,f143])).

fof(f143,plain,(
    ! [X3] : k2_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(superposition,[],[f30,f129])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f22,f20])).

fof(f12183,plain,(
    ! [X78,X77] : k2_xboole_0(X77,X78) = k2_xboole_0(k2_xboole_0(X78,X77),k1_xboole_0) ),
    inference(forward_demodulation,[],[f12079,f12164])).

fof(f12164,plain,(
    ! [X10,X9] : k2_xboole_0(X9,X10) = k3_xboole_0(k2_xboole_0(X9,X10),k2_xboole_0(X10,X9)) ),
    inference(forward_demodulation,[],[f12163,f174])).

fof(f12163,plain,(
    ! [X10,X9] : k3_xboole_0(k2_xboole_0(X9,X10),k2_xboole_0(X10,X9)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X9,X10)) ),
    inference(forward_demodulation,[],[f12050,f52])).

fof(f12050,plain,(
    ! [X10,X9] : k3_xboole_0(k2_xboole_0(X9,X10),k2_xboole_0(X10,X9)) = k4_xboole_0(k2_xboole_0(X9,X10),k1_xboole_0) ),
    inference(superposition,[],[f26,f11973])).

fof(f11973,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X9,X10),k2_xboole_0(X10,X9)) ),
    inference(forward_demodulation,[],[f11972,f24])).

fof(f11972,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),k2_xboole_0(X10,X9)) ),
    inference(forward_demodulation,[],[f11971,f21])).

fof(f11971,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X10,X9),X9),k2_xboole_0(X10,X9)) ),
    inference(forward_demodulation,[],[f11970,f2153])).

fof(f2153,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X10)) = k5_xboole_0(k4_xboole_0(X8,X9),X10) ),
    inference(superposition,[],[f29,f25])).

fof(f29,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f11970,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X10,k5_xboole_0(k3_xboole_0(X10,X9),X9)),k2_xboole_0(X10,X9)) ),
    inference(forward_demodulation,[],[f11969,f2166])).

fof(f11969,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(k3_xboole_0(X10,X9),k5_xboole_0(X9,X10)),k2_xboole_0(X10,X9)) ),
    inference(forward_demodulation,[],[f11784,f21])).

fof(f11784,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(k5_xboole_0(X9,X10),k3_xboole_0(X10,X9)),k2_xboole_0(X10,X9)) ),
    inference(superposition,[],[f485,f460])).

fof(f460,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f27,f21])).

fof(f12079,plain,(
    ! [X78,X77] : k2_xboole_0(X77,X78) = k2_xboole_0(k3_xboole_0(k2_xboole_0(X78,X77),k2_xboole_0(X77,X78)),k1_xboole_0) ),
    inference(superposition,[],[f2050,f11973])).

fof(f2050,plain,(
    ! [X4,X3] : k2_xboole_0(k3_xboole_0(X4,X3),k4_xboole_0(X3,X4)) = X3 ),
    inference(superposition,[],[f1244,f20])).

fof(f1244,plain,(
    ! [X8,X7] : k2_xboole_0(k3_xboole_0(X7,X8),k4_xboole_0(X7,X8)) = X7 ),
    inference(forward_demodulation,[],[f1243,f602])).

fof(f602,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(forward_demodulation,[],[f594,f45])).

fof(f594,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f24,f550])).

fof(f1243,plain,(
    ! [X8,X7] : k2_xboole_0(X7,k4_xboole_0(X7,X8)) = k2_xboole_0(k3_xboole_0(X7,X8),k4_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f1214,f708])).

fof(f708,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f675,f174])).

fof(f675,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X1) ),
    inference(superposition,[],[f28,f99])).

fof(f99,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = k3_xboole_0(X1,X1) ),
    inference(superposition,[],[f88,f52])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f1214,plain,(
    ! [X8,X7] : k2_xboole_0(X7,k4_xboole_0(X7,X8)) = k2_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X7,k4_xboole_0(X7,X8))) ),
    inference(superposition,[],[f27,f1020])).

fof(f2326,plain,(
    ! [X15,X16] : k4_xboole_0(X16,X15) = k5_xboole_0(k2_xboole_0(X15,X16),X15) ),
    inference(superposition,[],[f2247,f24])).

fof(f2247,plain,(
    ! [X12,X13] : k5_xboole_0(k5_xboole_0(X13,X12),X13) = X12 ),
    inference(superposition,[],[f2210,f2210])).

fof(f2210,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f2189,f21])).

fof(f2189,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f2150,f46])).

fof(f2150,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f29,f189])).

fof(f189,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f184,f32])).

fof(f184,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f25,f173])).

fof(f173,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(superposition,[],[f156,f88])).

fof(f2166,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f29,f21])).

fof(f39815,plain,(
    ! [X94,X95] : k3_xboole_0(k2_xboole_0(X94,X95),k5_xboole_0(X95,X94)) = k4_xboole_0(k2_xboole_0(X94,X95),k5_xboole_0(X95,k5_xboole_0(X94,k2_xboole_0(X94,X95)))) ),
    inference(forward_demodulation,[],[f39548,f29])).

fof(f39548,plain,(
    ! [X94,X95] : k3_xboole_0(k2_xboole_0(X94,X95),k5_xboole_0(X95,X94)) = k4_xboole_0(k2_xboole_0(X94,X95),k5_xboole_0(k5_xboole_0(X95,X94),k2_xboole_0(X94,X95))) ),
    inference(superposition,[],[f19913,f925])).

fof(f925,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(k2_xboole_0(X2,X1),k5_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f924,f46])).

fof(f924,plain,(
    ! [X2,X1] : k2_xboole_0(k2_xboole_0(X2,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f893,f21])).

fof(f893,plain,(
    ! [X2,X1] : k2_xboole_0(k2_xboole_0(X2,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(k2_xboole_0(X2,X1),k1_xboole_0) ),
    inference(superposition,[],[f24,f524])).

fof(f19913,plain,(
    ! [X39,X40] : k3_xboole_0(X40,X39) = k4_xboole_0(k2_xboole_0(X40,X39),k5_xboole_0(X39,X40)) ),
    inference(forward_demodulation,[],[f19912,f1020])).

fof(f19912,plain,(
    ! [X39,X40] : k4_xboole_0(k2_xboole_0(X40,X39),k5_xboole_0(X39,X40)) = k5_xboole_0(X40,k4_xboole_0(X40,X39)) ),
    inference(forward_demodulation,[],[f19911,f19417])).

fof(f19911,plain,(
    ! [X39,X40] : k4_xboole_0(k2_xboole_0(X40,X39),k5_xboole_0(X39,X40)) = k5_xboole_0(X39,k5_xboole_0(X40,k2_xboole_0(X40,X39))) ),
    inference(forward_demodulation,[],[f19789,f29])).

fof(f19789,plain,(
    ! [X39,X40] : k4_xboole_0(k2_xboole_0(X40,X39),k5_xboole_0(X39,X40)) = k5_xboole_0(k5_xboole_0(X39,X40),k2_xboole_0(X40,X39)) ),
    inference(superposition,[],[f276,f460])).

fof(f276,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f275,f21])).

fof(f275,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X0) = k5_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f266,f174])).

fof(f266,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X0) = k5_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f59,f96])).

fof(f96,plain,(
    ! [X2,X1] : k2_xboole_0(k1_xboole_0,X1) = k3_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f89,f52])).

fof(f89,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f26,f23])).

fof(f40,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl2_1
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f76,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f64,f73])).

fof(f73,plain,
    ( spl2_2
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f64,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f61,f32])).

fof(f61,plain,(
    ! [X6] : k3_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f25,f46])).

fof(f41,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f18,f38])).

fof(f18,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:54:51 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.46  % (22890)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (22881)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (22889)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  % (22891)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (22891)Refutation not found, incomplete strategy% (22891)------------------------------
% 0.20/0.47  % (22891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (22891)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (22891)Memory used [KB]: 10490
% 0.20/0.47  % (22891)Time elapsed: 0.060 s
% 0.20/0.47  % (22891)------------------------------
% 0.20/0.47  % (22891)------------------------------
% 0.20/0.47  % (22894)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (22886)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (22893)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (22882)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (22879)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (22897)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (22884)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (22895)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (22896)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % (22887)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.50  % (22892)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.50  % (22885)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.51  % (22883)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.51  % (22888)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 4.71/1.00  % (22884)Time limit reached!
% 4.71/1.00  % (22884)------------------------------
% 4.71/1.00  % (22884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.28/1.02  % (22884)Termination reason: Time limit
% 5.28/1.02  
% 5.28/1.02  % (22884)Memory used [KB]: 17014
% 5.28/1.02  % (22884)Time elapsed: 0.604 s
% 5.28/1.02  % (22884)------------------------------
% 5.28/1.02  % (22884)------------------------------
% 12.37/1.97  % (22886)Time limit reached!
% 12.37/1.97  % (22886)------------------------------
% 12.37/1.97  % (22886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.97/1.98  % (22886)Termination reason: Time limit
% 12.97/1.98  
% 12.97/1.98  % (22886)Memory used [KB]: 44391
% 12.97/1.98  % (22886)Time elapsed: 1.510 s
% 12.97/1.98  % (22886)------------------------------
% 12.97/1.98  % (22886)------------------------------
% 12.97/1.98  % (22885)Time limit reached!
% 12.97/1.98  % (22885)------------------------------
% 12.97/1.98  % (22885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.97/1.98  % (22885)Termination reason: Time limit
% 12.97/1.98  
% 12.97/1.98  % (22885)Memory used [KB]: 42600
% 12.97/1.98  % (22885)Time elapsed: 1.574 s
% 12.97/1.98  % (22885)------------------------------
% 12.97/1.98  % (22885)------------------------------
% 12.97/2.02  % (22879)Refutation found. Thanks to Tanya!
% 12.97/2.02  % SZS status Theorem for theBenchmark
% 12.97/2.03  % SZS output start Proof for theBenchmark
% 12.97/2.03  fof(f57825,plain,(
% 12.97/2.03    $false),
% 12.97/2.03    inference(avatar_sat_refutation,[],[f41,f76,f57738])).
% 12.97/2.03  fof(f57738,plain,(
% 12.97/2.03    spl2_1),
% 12.97/2.03    inference(avatar_contradiction_clause,[],[f57737])).
% 12.97/2.03  fof(f57737,plain,(
% 12.97/2.03    $false | spl2_1),
% 12.97/2.03    inference(subsumption_resolution,[],[f57251,f21])).
% 12.97/2.03  fof(f21,plain,(
% 12.97/2.03    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 12.97/2.03    inference(cnf_transformation,[],[f2])).
% 12.97/2.03  fof(f2,axiom,(
% 12.97/2.03    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 12.97/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 12.97/2.03  fof(f57251,plain,(
% 12.97/2.03    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK1,sK0) | spl2_1),
% 12.97/2.03    inference(superposition,[],[f40,f39819])).
% 12.97/2.04  fof(f39819,plain,(
% 12.97/2.04    ( ! [X94,X95] : (k5_xboole_0(X95,X94) = k4_xboole_0(k2_xboole_0(X94,X95),k3_xboole_0(X94,X95))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f39818,f927])).
% 12.97/2.04  fof(f927,plain,(
% 12.97/2.04    ( ! [X4,X3] : (k5_xboole_0(X3,X4) = k3_xboole_0(k5_xboole_0(X3,X4),k2_xboole_0(X4,X3))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f926,f174])).
% 12.97/2.04  fof(f174,plain,(
% 12.97/2.04    ( ! [X2] : (k2_xboole_0(k1_xboole_0,X2) = X2) )),
% 12.97/2.04    inference(superposition,[],[f156,f52])).
% 12.97/2.04  fof(f52,plain,(
% 12.97/2.04    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X3)) )),
% 12.97/2.04    inference(superposition,[],[f46,f24])).
% 12.97/2.04  fof(f24,plain,(
% 12.97/2.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 12.97/2.04    inference(cnf_transformation,[],[f11])).
% 12.97/2.04  fof(f11,axiom,(
% 12.97/2.04    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 12.97/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 12.97/2.04  fof(f46,plain,(
% 12.97/2.04    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 12.97/2.04    inference(superposition,[],[f45,f21])).
% 12.97/2.04  fof(f45,plain,(
% 12.97/2.04    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = X2) )),
% 12.97/2.04    inference(forward_demodulation,[],[f43,f19])).
% 12.97/2.04  fof(f19,plain,(
% 12.97/2.04    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 12.97/2.04    inference(cnf_transformation,[],[f14])).
% 12.97/2.04  fof(f14,plain,(
% 12.97/2.04    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 12.97/2.04    inference(rectify,[],[f3])).
% 12.97/2.04  fof(f3,axiom,(
% 12.97/2.04    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 12.97/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 12.97/2.04  fof(f43,plain,(
% 12.97/2.04    ( ! [X2] : (k2_xboole_0(X2,X2) = k5_xboole_0(X2,k1_xboole_0)) )),
% 12.97/2.04    inference(superposition,[],[f24,f32])).
% 12.97/2.04  fof(f32,plain,(
% 12.97/2.04    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 12.97/2.04    inference(superposition,[],[f23,f19])).
% 12.97/2.04  fof(f23,plain,(
% 12.97/2.04    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 12.97/2.04    inference(cnf_transformation,[],[f6])).
% 12.97/2.04  fof(f6,axiom,(
% 12.97/2.04    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 12.97/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 12.97/2.04  fof(f156,plain,(
% 12.97/2.04    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.97/2.04    inference(forward_demodulation,[],[f150,f45])).
% 12.97/2.04  fof(f150,plain,(
% 12.97/2.04    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 12.97/2.04    inference(superposition,[],[f25,f139])).
% 12.97/2.04  fof(f139,plain,(
% 12.97/2.04    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)) )),
% 12.97/2.04    inference(superposition,[],[f129,f20])).
% 12.97/2.04  fof(f20,plain,(
% 12.97/2.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 12.97/2.04    inference(cnf_transformation,[],[f1])).
% 12.97/2.04  fof(f1,axiom,(
% 12.97/2.04    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 12.97/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 12.97/2.04  fof(f129,plain,(
% 12.97/2.04    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 12.97/2.04    inference(superposition,[],[f113,f45])).
% 12.97/2.04  fof(f113,plain,(
% 12.97/2.04    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0)) )),
% 12.97/2.04    inference(superposition,[],[f109,f22])).
% 12.97/2.04  fof(f22,plain,(
% 12.97/2.04    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 12.97/2.04    inference(cnf_transformation,[],[f5])).
% 12.97/2.04  fof(f5,axiom,(
% 12.97/2.04    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 12.97/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 12.97/2.04  fof(f109,plain,(
% 12.97/2.04    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f108,f32])).
% 12.97/2.04  fof(f108,plain,(
% 12.97/2.04    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,k2_xboole_0(k1_xboole_0,X0))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f101,f52])).
% 12.97/2.04  fof(f101,plain,(
% 12.97/2.04    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 12.97/2.04    inference(superposition,[],[f25,f88])).
% 12.97/2.04  fof(f88,plain,(
% 12.97/2.04    ( ! [X0] : (k3_xboole_0(X0,X0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 12.97/2.04    inference(superposition,[],[f26,f32])).
% 12.97/2.04  fof(f26,plain,(
% 12.97/2.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 12.97/2.04    inference(cnf_transformation,[],[f7])).
% 12.97/2.04  fof(f7,axiom,(
% 12.97/2.04    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 12.97/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 12.97/2.04  fof(f25,plain,(
% 12.97/2.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 12.97/2.04    inference(cnf_transformation,[],[f4])).
% 12.97/2.04  fof(f4,axiom,(
% 12.97/2.04    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 12.97/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 12.97/2.04  fof(f926,plain,(
% 12.97/2.04    ( ! [X4,X3] : (k3_xboole_0(k5_xboole_0(X3,X4),k2_xboole_0(X4,X3)) = k2_xboole_0(k1_xboole_0,k5_xboole_0(X3,X4))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f894,f52])).
% 12.97/2.04  fof(f894,plain,(
% 12.97/2.04    ( ! [X4,X3] : (k3_xboole_0(k5_xboole_0(X3,X4),k2_xboole_0(X4,X3)) = k4_xboole_0(k5_xboole_0(X3,X4),k1_xboole_0)) )),
% 12.97/2.04    inference(superposition,[],[f26,f524])).
% 12.97/2.04  fof(f524,plain,(
% 12.97/2.04    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X1,X2))) )),
% 12.97/2.04    inference(superposition,[],[f485,f21])).
% 12.97/2.04  fof(f485,plain,(
% 12.97/2.04    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X4,X5),k2_xboole_0(X4,X5))) )),
% 12.97/2.04    inference(superposition,[],[f23,f27])).
% 12.97/2.04  fof(f27,plain,(
% 12.97/2.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 12.97/2.04    inference(cnf_transformation,[],[f10])).
% 12.97/2.04  fof(f10,axiom,(
% 12.97/2.04    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 12.97/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).
% 12.97/2.04  fof(f39818,plain,(
% 12.97/2.04    ( ! [X94,X95] : (k4_xboole_0(k2_xboole_0(X94,X95),k3_xboole_0(X94,X95)) = k3_xboole_0(k5_xboole_0(X95,X94),k2_xboole_0(X94,X95))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f39817,f20])).
% 12.97/2.04  fof(f39817,plain,(
% 12.97/2.04    ( ! [X94,X95] : (k3_xboole_0(k2_xboole_0(X94,X95),k5_xboole_0(X95,X94)) = k4_xboole_0(k2_xboole_0(X94,X95),k3_xboole_0(X94,X95))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f39816,f1020])).
% 12.97/2.04  fof(f1020,plain,(
% 12.97/2.04    ( ! [X17,X16] : (k3_xboole_0(X16,X17) = k5_xboole_0(X16,k4_xboole_0(X16,X17))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f1010,f26])).
% 12.97/2.04  fof(f1010,plain,(
% 12.97/2.04    ( ! [X17,X16] : (k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k5_xboole_0(X16,k4_xboole_0(X16,X17))) )),
% 12.97/2.04    inference(superposition,[],[f59,f601])).
% 12.97/2.04  fof(f601,plain,(
% 12.97/2.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 12.97/2.04    inference(forward_demodulation,[],[f593,f156])).
% 12.97/2.04  fof(f593,plain,(
% 12.97/2.04    ( ! [X0,X1] : (k3_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) )),
% 12.97/2.04    inference(superposition,[],[f26,f550])).
% 12.97/2.04  fof(f550,plain,(
% 12.97/2.04    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5)) )),
% 12.97/2.04    inference(forward_demodulation,[],[f526,f22])).
% 12.97/2.04  fof(f526,plain,(
% 12.97/2.04    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,k3_xboole_0(X5,X6)))) )),
% 12.97/2.04    inference(superposition,[],[f485,f25])).
% 12.97/2.04  fof(f59,plain,(
% 12.97/2.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 12.97/2.04    inference(superposition,[],[f25,f20])).
% 12.97/2.04  fof(f39816,plain,(
% 12.97/2.04    ( ! [X94,X95] : (k3_xboole_0(k2_xboole_0(X94,X95),k5_xboole_0(X95,X94)) = k4_xboole_0(k2_xboole_0(X94,X95),k5_xboole_0(X94,k4_xboole_0(X94,X95)))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f39815,f19417])).
% 12.97/2.04  fof(f19417,plain,(
% 12.97/2.04    ( ! [X101,X102,X100] : (k5_xboole_0(X101,k5_xboole_0(X102,k2_xboole_0(X100,X101))) = k5_xboole_0(X102,k4_xboole_0(X100,X101))) )),
% 12.97/2.04    inference(superposition,[],[f2166,f12352])).
% 12.97/2.04  fof(f12352,plain,(
% 12.97/2.04    ( ! [X24,X23] : (k4_xboole_0(X24,X23) = k5_xboole_0(k2_xboole_0(X24,X23),X23)) )),
% 12.97/2.04    inference(superposition,[],[f2326,f12232])).
% 12.97/2.04  fof(f12232,plain,(
% 12.97/2.04    ( ! [X6,X5] : (k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5)) )),
% 12.97/2.04    inference(superposition,[],[f12183,f143])).
% 12.97/2.04  fof(f143,plain,(
% 12.97/2.04    ( ! [X3] : (k2_xboole_0(X3,k1_xboole_0) = X3) )),
% 12.97/2.04    inference(superposition,[],[f30,f129])).
% 12.97/2.04  fof(f30,plain,(
% 12.97/2.04    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0) )),
% 12.97/2.04    inference(superposition,[],[f22,f20])).
% 12.97/2.04  fof(f12183,plain,(
% 12.97/2.04    ( ! [X78,X77] : (k2_xboole_0(X77,X78) = k2_xboole_0(k2_xboole_0(X78,X77),k1_xboole_0)) )),
% 12.97/2.04    inference(forward_demodulation,[],[f12079,f12164])).
% 12.97/2.04  fof(f12164,plain,(
% 12.97/2.04    ( ! [X10,X9] : (k2_xboole_0(X9,X10) = k3_xboole_0(k2_xboole_0(X9,X10),k2_xboole_0(X10,X9))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f12163,f174])).
% 12.97/2.04  fof(f12163,plain,(
% 12.97/2.04    ( ! [X10,X9] : (k3_xboole_0(k2_xboole_0(X9,X10),k2_xboole_0(X10,X9)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X9,X10))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f12050,f52])).
% 12.97/2.04  fof(f12050,plain,(
% 12.97/2.04    ( ! [X10,X9] : (k3_xboole_0(k2_xboole_0(X9,X10),k2_xboole_0(X10,X9)) = k4_xboole_0(k2_xboole_0(X9,X10),k1_xboole_0)) )),
% 12.97/2.04    inference(superposition,[],[f26,f11973])).
% 12.97/2.04  fof(f11973,plain,(
% 12.97/2.04    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X9,X10),k2_xboole_0(X10,X9))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f11972,f24])).
% 12.97/2.04  fof(f11972,plain,(
% 12.97/2.04    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),k2_xboole_0(X10,X9))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f11971,f21])).
% 12.97/2.04  fof(f11971,plain,(
% 12.97/2.04    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X10,X9),X9),k2_xboole_0(X10,X9))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f11970,f2153])).
% 12.97/2.04  fof(f2153,plain,(
% 12.97/2.04    ( ! [X10,X8,X9] : (k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X10)) = k5_xboole_0(k4_xboole_0(X8,X9),X10)) )),
% 12.97/2.04    inference(superposition,[],[f29,f25])).
% 12.97/2.04  fof(f29,plain,(
% 12.97/2.04    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 12.97/2.04    inference(cnf_transformation,[],[f9])).
% 12.97/2.04  fof(f9,axiom,(
% 12.97/2.04    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 12.97/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 12.97/2.04  fof(f11970,plain,(
% 12.97/2.04    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X10,k5_xboole_0(k3_xboole_0(X10,X9),X9)),k2_xboole_0(X10,X9))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f11969,f2166])).
% 12.97/2.04  fof(f11969,plain,(
% 12.97/2.04    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(k3_xboole_0(X10,X9),k5_xboole_0(X9,X10)),k2_xboole_0(X10,X9))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f11784,f21])).
% 12.97/2.04  fof(f11784,plain,(
% 12.97/2.04    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(k5_xboole_0(X9,X10),k3_xboole_0(X10,X9)),k2_xboole_0(X10,X9))) )),
% 12.97/2.04    inference(superposition,[],[f485,f460])).
% 12.97/2.04  fof(f460,plain,(
% 12.97/2.04    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X1,X2))) )),
% 12.97/2.04    inference(superposition,[],[f27,f21])).
% 12.97/2.04  fof(f12079,plain,(
% 12.97/2.04    ( ! [X78,X77] : (k2_xboole_0(X77,X78) = k2_xboole_0(k3_xboole_0(k2_xboole_0(X78,X77),k2_xboole_0(X77,X78)),k1_xboole_0)) )),
% 12.97/2.04    inference(superposition,[],[f2050,f11973])).
% 12.97/2.04  fof(f2050,plain,(
% 12.97/2.04    ( ! [X4,X3] : (k2_xboole_0(k3_xboole_0(X4,X3),k4_xboole_0(X3,X4)) = X3) )),
% 12.97/2.04    inference(superposition,[],[f1244,f20])).
% 12.97/2.04  fof(f1244,plain,(
% 12.97/2.04    ( ! [X8,X7] : (k2_xboole_0(k3_xboole_0(X7,X8),k4_xboole_0(X7,X8)) = X7) )),
% 12.97/2.04    inference(forward_demodulation,[],[f1243,f602])).
% 12.97/2.04  fof(f602,plain,(
% 12.97/2.04    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 12.97/2.04    inference(forward_demodulation,[],[f594,f45])).
% 12.97/2.04  fof(f594,plain,(
% 12.97/2.04    ( ! [X2,X3] : (k5_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 12.97/2.04    inference(superposition,[],[f24,f550])).
% 12.97/2.04  fof(f1243,plain,(
% 12.97/2.04    ( ! [X8,X7] : (k2_xboole_0(X7,k4_xboole_0(X7,X8)) = k2_xboole_0(k3_xboole_0(X7,X8),k4_xboole_0(X7,X8))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f1214,f708])).
% 12.97/2.04  fof(f708,plain,(
% 12.97/2.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f675,f174])).
% 12.97/2.04  fof(f675,plain,(
% 12.97/2.04    ( ! [X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X1)) )),
% 12.97/2.04    inference(superposition,[],[f28,f99])).
% 12.97/2.04  fof(f99,plain,(
% 12.97/2.04    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = k3_xboole_0(X1,X1)) )),
% 12.97/2.04    inference(superposition,[],[f88,f52])).
% 12.97/2.04  fof(f28,plain,(
% 12.97/2.04    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 12.97/2.04    inference(cnf_transformation,[],[f8])).
% 12.97/2.04  fof(f8,axiom,(
% 12.97/2.04    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 12.97/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 12.97/2.04  fof(f1214,plain,(
% 12.97/2.04    ( ! [X8,X7] : (k2_xboole_0(X7,k4_xboole_0(X7,X8)) = k2_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X7,k4_xboole_0(X7,X8)))) )),
% 12.97/2.04    inference(superposition,[],[f27,f1020])).
% 12.97/2.04  fof(f2326,plain,(
% 12.97/2.04    ( ! [X15,X16] : (k4_xboole_0(X16,X15) = k5_xboole_0(k2_xboole_0(X15,X16),X15)) )),
% 12.97/2.04    inference(superposition,[],[f2247,f24])).
% 12.97/2.04  fof(f2247,plain,(
% 12.97/2.04    ( ! [X12,X13] : (k5_xboole_0(k5_xboole_0(X13,X12),X13) = X12) )),
% 12.97/2.04    inference(superposition,[],[f2210,f2210])).
% 12.97/2.04  fof(f2210,plain,(
% 12.97/2.04    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 12.97/2.04    inference(superposition,[],[f2189,f21])).
% 12.97/2.04  fof(f2189,plain,(
% 12.97/2.04    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 12.97/2.04    inference(forward_demodulation,[],[f2150,f46])).
% 12.97/2.04  fof(f2150,plain,(
% 12.97/2.04    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 12.97/2.04    inference(superposition,[],[f29,f189])).
% 12.97/2.04  fof(f189,plain,(
% 12.97/2.04    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 12.97/2.04    inference(forward_demodulation,[],[f184,f32])).
% 12.97/2.04  fof(f184,plain,(
% 12.97/2.04    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 12.97/2.04    inference(superposition,[],[f25,f173])).
% 12.97/2.04  fof(f173,plain,(
% 12.97/2.04    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 12.97/2.04    inference(superposition,[],[f156,f88])).
% 12.97/2.04  fof(f2166,plain,(
% 12.97/2.04    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))) )),
% 12.97/2.04    inference(superposition,[],[f29,f21])).
% 12.97/2.04  fof(f39815,plain,(
% 12.97/2.04    ( ! [X94,X95] : (k3_xboole_0(k2_xboole_0(X94,X95),k5_xboole_0(X95,X94)) = k4_xboole_0(k2_xboole_0(X94,X95),k5_xboole_0(X95,k5_xboole_0(X94,k2_xboole_0(X94,X95))))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f39548,f29])).
% 12.97/2.04  fof(f39548,plain,(
% 12.97/2.04    ( ! [X94,X95] : (k3_xboole_0(k2_xboole_0(X94,X95),k5_xboole_0(X95,X94)) = k4_xboole_0(k2_xboole_0(X94,X95),k5_xboole_0(k5_xboole_0(X95,X94),k2_xboole_0(X94,X95)))) )),
% 12.97/2.04    inference(superposition,[],[f19913,f925])).
% 12.97/2.04  fof(f925,plain,(
% 12.97/2.04    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(k2_xboole_0(X2,X1),k5_xboole_0(X1,X2))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f924,f46])).
% 12.97/2.04  fof(f924,plain,(
% 12.97/2.04    ( ! [X2,X1] : (k2_xboole_0(k2_xboole_0(X2,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X2,X1))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f893,f21])).
% 12.97/2.04  fof(f893,plain,(
% 12.97/2.04    ( ! [X2,X1] : (k2_xboole_0(k2_xboole_0(X2,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(k2_xboole_0(X2,X1),k1_xboole_0)) )),
% 12.97/2.04    inference(superposition,[],[f24,f524])).
% 12.97/2.04  fof(f19913,plain,(
% 12.97/2.04    ( ! [X39,X40] : (k3_xboole_0(X40,X39) = k4_xboole_0(k2_xboole_0(X40,X39),k5_xboole_0(X39,X40))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f19912,f1020])).
% 12.97/2.04  fof(f19912,plain,(
% 12.97/2.04    ( ! [X39,X40] : (k4_xboole_0(k2_xboole_0(X40,X39),k5_xboole_0(X39,X40)) = k5_xboole_0(X40,k4_xboole_0(X40,X39))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f19911,f19417])).
% 12.97/2.04  fof(f19911,plain,(
% 12.97/2.04    ( ! [X39,X40] : (k4_xboole_0(k2_xboole_0(X40,X39),k5_xboole_0(X39,X40)) = k5_xboole_0(X39,k5_xboole_0(X40,k2_xboole_0(X40,X39)))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f19789,f29])).
% 12.97/2.04  fof(f19789,plain,(
% 12.97/2.04    ( ! [X39,X40] : (k4_xboole_0(k2_xboole_0(X40,X39),k5_xboole_0(X39,X40)) = k5_xboole_0(k5_xboole_0(X39,X40),k2_xboole_0(X40,X39))) )),
% 12.97/2.04    inference(superposition,[],[f276,f460])).
% 12.97/2.04  fof(f276,plain,(
% 12.97/2.04    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f275,f21])).
% 12.97/2.04  fof(f275,plain,(
% 12.97/2.04    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X0) = k5_xboole_0(k2_xboole_0(X0,X1),X0)) )),
% 12.97/2.04    inference(forward_demodulation,[],[f266,f174])).
% 12.97/2.04  fof(f266,plain,(
% 12.97/2.04    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X0) = k5_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,X0))) )),
% 12.97/2.04    inference(superposition,[],[f59,f96])).
% 12.97/2.04  fof(f96,plain,(
% 12.97/2.04    ( ! [X2,X1] : (k2_xboole_0(k1_xboole_0,X1) = k3_xboole_0(X1,k2_xboole_0(X1,X2))) )),
% 12.97/2.04    inference(forward_demodulation,[],[f89,f52])).
% 12.97/2.04  fof(f89,plain,(
% 12.97/2.04    ( ! [X2,X1] : (k3_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X1,k1_xboole_0)) )),
% 12.97/2.04    inference(superposition,[],[f26,f23])).
% 12.97/2.04  fof(f40,plain,(
% 12.97/2.04    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) | spl2_1),
% 12.97/2.04    inference(avatar_component_clause,[],[f38])).
% 12.97/2.04  fof(f38,plain,(
% 12.97/2.04    spl2_1 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 12.97/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 12.97/2.04  fof(f76,plain,(
% 12.97/2.04    spl2_2),
% 12.97/2.04    inference(avatar_split_clause,[],[f64,f73])).
% 12.97/2.04  fof(f73,plain,(
% 12.97/2.04    spl2_2 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)),
% 12.97/2.04    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 12.97/2.04  fof(f64,plain,(
% 12.97/2.04    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)),
% 12.97/2.04    inference(superposition,[],[f61,f32])).
% 12.97/2.04  fof(f61,plain,(
% 12.97/2.04    ( ! [X6] : (k3_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,X6)) )),
% 12.97/2.04    inference(superposition,[],[f25,f46])).
% 12.97/2.04  fof(f41,plain,(
% 12.97/2.04    ~spl2_1),
% 12.97/2.04    inference(avatar_split_clause,[],[f18,f38])).
% 12.97/2.04  fof(f18,plain,(
% 12.97/2.04    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 12.97/2.04    inference(cnf_transformation,[],[f17])).
% 12.97/2.04  fof(f17,plain,(
% 12.97/2.04    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 12.97/2.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 12.97/2.04  fof(f16,plain,(
% 12.97/2.04    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 12.97/2.04    introduced(choice_axiom,[])).
% 12.97/2.04  fof(f15,plain,(
% 12.97/2.04    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 12.97/2.04    inference(ennf_transformation,[],[f13])).
% 12.97/2.04  fof(f13,negated_conjecture,(
% 12.97/2.04    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 12.97/2.04    inference(negated_conjecture,[],[f12])).
% 12.97/2.04  fof(f12,conjecture,(
% 12.97/2.04    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 12.97/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 12.97/2.04  % SZS output end Proof for theBenchmark
% 12.97/2.04  % (22879)------------------------------
% 12.97/2.04  % (22879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.97/2.04  % (22879)Termination reason: Refutation
% 12.97/2.04  
% 12.97/2.04  % (22879)Memory used [KB]: 38762
% 12.97/2.04  % (22879)Time elapsed: 1.590 s
% 12.97/2.04  % (22879)------------------------------
% 12.97/2.04  % (22879)------------------------------
% 12.97/2.04  % (22876)Success in time 1.685 s
%------------------------------------------------------------------------------
