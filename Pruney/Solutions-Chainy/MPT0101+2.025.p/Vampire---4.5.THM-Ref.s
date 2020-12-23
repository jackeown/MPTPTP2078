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
% DateTime   : Thu Dec  3 12:31:55 EST 2020

% Result     : Theorem 28.92s
% Output     : Refutation 29.37s
% Verified   : 
% Statistics : Number of formulae       : 1073 (2225316 expanded)
%              Number of leaves         :    9 (741772 expanded)
%              Depth                    :   83
%              Number of atoms          : 1074 (2225317 expanded)
%              Number of equality atoms : 1073 (2225316 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67738,plain,(
    $false ),
    inference(subsumption_resolution,[],[f67737,f59166])).

fof(f59166,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k5_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X1,X0))) ),
    inference(superposition,[],[f59143,f14])).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f59143,plain,(
    ! [X196,X195] : k2_xboole_0(X195,X196) = k5_xboole_0(X196,k5_xboole_0(X196,k2_xboole_0(X195,X196))) ),
    inference(forward_demodulation,[],[f59142,f19314])).

fof(f19314,plain,(
    ! [X41,X40] : k2_xboole_0(X40,X41) = k5_xboole_0(k2_xboole_0(X40,X41),k4_xboole_0(X41,k2_xboole_0(X40,X41))) ),
    inference(forward_demodulation,[],[f19313,f84])).

fof(f84,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(k2_xboole_0(X7,X6),k2_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f83,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f24,f15])).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f15,f16])).

fof(f16,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f83,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k2_xboole_0(X7,X6)) = k2_xboole_0(k2_xboole_0(X7,X6),k2_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f77,f14])).

fof(f77,plain,(
    ! [X6,X7] : k2_xboole_0(k2_xboole_0(X7,X6),X6) = k2_xboole_0(k2_xboole_0(X7,X6),k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f25,f25])).

fof(f19313,plain,(
    ! [X41,X40] : k2_xboole_0(X40,X41) = k5_xboole_0(k2_xboole_0(k2_xboole_0(X41,X40),k2_xboole_0(X40,X41)),k4_xboole_0(X41,k2_xboole_0(X40,X41))) ),
    inference(forward_demodulation,[],[f19312,f5692])).

fof(f5692,plain,(
    ! [X72,X73] : k2_xboole_0(X72,X73) = k5_xboole_0(k2_xboole_0(X73,X72),k4_xboole_0(X73,k2_xboole_0(X72,X73))) ),
    inference(forward_demodulation,[],[f5691,f25])).

fof(f5691,plain,(
    ! [X72,X73] : k5_xboole_0(k2_xboole_0(X73,X72),k4_xboole_0(X73,k2_xboole_0(X72,X73))) = k2_xboole_0(X72,k2_xboole_0(X73,X72)) ),
    inference(forward_demodulation,[],[f5690,f14])).

fof(f5690,plain,(
    ! [X72,X73] : k2_xboole_0(k2_xboole_0(X73,X72),X72) = k5_xboole_0(k2_xboole_0(X73,X72),k4_xboole_0(X73,k2_xboole_0(X72,X73))) ),
    inference(forward_demodulation,[],[f5407,f5482])).

fof(f5482,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k2_xboole_0(X15,X14)) = k4_xboole_0(k3_xboole_0(X15,X14),X14) ),
    inference(forward_demodulation,[],[f5481,f69])).

fof(f69,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,X5)) = k4_xboole_0(X4,k2_xboole_0(X3,X5)) ),
    inference(forward_demodulation,[],[f59,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f59,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,X5)) = k4_xboole_0(k4_xboole_0(X4,X3),X5) ),
    inference(superposition,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f16,f14])).

fof(f5481,plain,(
    ! [X14,X15] : k4_xboole_0(k2_xboole_0(X15,X14),k2_xboole_0(X15,X14)) = k4_xboole_0(k3_xboole_0(X15,X14),X14) ),
    inference(forward_demodulation,[],[f5360,f515])).

fof(f515,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X2),X1) ),
    inference(forward_demodulation,[],[f504,f443])).

fof(f443,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(k3_xboole_0(X3,X5),X4) ),
    inference(forward_demodulation,[],[f442,f355])).

fof(f355,plain,(
    ! [X10,X8,X9] : k4_xboole_0(k3_xboole_0(X8,X9),X10) = k4_xboole_0(X8,k2_xboole_0(X10,k4_xboole_0(X8,X9))) ),
    inference(superposition,[],[f60,f14])).

fof(f60,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X6,X7),X8)) = k4_xboole_0(k3_xboole_0(X6,X7),X8) ),
    inference(superposition,[],[f20,f17])).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f442,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X5))) ),
    inference(backward_demodulation,[],[f72,f419])).

fof(f419,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X1,k4_xboole_0(X2,X0)) = k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X0))) ),
    inference(superposition,[],[f66,f14])).

fof(f66,plain,(
    ! [X10,X11,X9] : k2_xboole_0(X11,k4_xboole_0(X9,X10)) = k2_xboole_0(X11,k4_xboole_0(X9,k2_xboole_0(X10,X11))) ),
    inference(superposition,[],[f15,f20])).

fof(f72,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k2_xboole_0(X4,X5)))) ),
    inference(forward_demodulation,[],[f62,f20])).

fof(f62,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(k4_xboole_0(X3,X4),X5))) ),
    inference(superposition,[],[f20,f17])).

fof(f504,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X2),X1) ),
    inference(superposition,[],[f443,f16])).

fof(f5360,plain,(
    ! [X14,X15] : k4_xboole_0(k2_xboole_0(X15,X14),k2_xboole_0(X15,X14)) = k4_xboole_0(k3_xboole_0(k2_xboole_0(X15,X14),X14),X14) ),
    inference(superposition,[],[f353,f160])).

fof(f160,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f53,f14])).

fof(f53,plain,(
    ! [X8,X7] : k2_xboole_0(X7,X8) = k2_xboole_0(X7,k2_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f49,f15])).

fof(f49,plain,(
    ! [X8,X7] : k2_xboole_0(X7,k2_xboole_0(X7,X8)) = k2_xboole_0(X7,k4_xboole_0(X8,X7)) ),
    inference(superposition,[],[f15,f21])).

fof(f353,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k2_xboole_0(X5,X4)) = k4_xboole_0(k3_xboole_0(X4,X5),X5) ),
    inference(superposition,[],[f60,f211])).

fof(f211,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(forward_demodulation,[],[f210,f82])).

fof(f82,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f81,f15])).

fof(f81,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X5,X4)) = k2_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f76,f14])).

fof(f76,plain,(
    ! [X4,X5] : k2_xboole_0(k4_xboole_0(X5,X4),X4) = k2_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5)) ),
    inference(superposition,[],[f25,f15])).

fof(f210,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X1,X0),X0) = k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f184,f15])).

fof(f184,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f15,f23])).

fof(f23,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) ),
    inference(superposition,[],[f16,f15])).

fof(f5407,plain,(
    ! [X72,X73] : k2_xboole_0(k2_xboole_0(X73,X72),X72) = k5_xboole_0(k2_xboole_0(X73,X72),k4_xboole_0(k3_xboole_0(X72,X73),X73)) ),
    inference(superposition,[],[f137,f353])).

fof(f137,plain,(
    ! [X10,X9] : k2_xboole_0(X10,X9) = k5_xboole_0(X10,k4_xboole_0(X9,X10)) ),
    inference(forward_demodulation,[],[f136,f15])).

fof(f136,plain,(
    ! [X10,X9] : k5_xboole_0(X10,k4_xboole_0(X9,X10)) = k2_xboole_0(X10,k4_xboole_0(X9,X10)) ),
    inference(forward_demodulation,[],[f135,f14])).

fof(f135,plain,(
    ! [X10,X9] : k5_xboole_0(X10,k4_xboole_0(X9,X10)) = k2_xboole_0(k4_xboole_0(X9,X10),X10) ),
    inference(forward_demodulation,[],[f115,f15])).

fof(f115,plain,(
    ! [X10,X9] : k5_xboole_0(X10,k4_xboole_0(X9,X10)) = k2_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X10,k4_xboole_0(X9,X10))) ),
    inference(superposition,[],[f34,f50])).

fof(f50,plain,(
    ! [X4,X5] : k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4) ),
    inference(forward_demodulation,[],[f44,f21])).

fof(f44,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X5,X4),X4) = k4_xboole_0(k2_xboole_0(X4,X5),X4) ),
    inference(superposition,[],[f21,f15])).

fof(f34,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3)) = k5_xboole_0(X2,X3) ),
    inference(superposition,[],[f18,f14])).

fof(f18,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f19312,plain,(
    ! [X41,X40] : k5_xboole_0(k2_xboole_0(k2_xboole_0(X41,X40),k2_xboole_0(X40,X41)),k4_xboole_0(X41,k2_xboole_0(X40,X41))) = k5_xboole_0(k2_xboole_0(X41,X40),k4_xboole_0(X41,k2_xboole_0(X40,X41))) ),
    inference(forward_demodulation,[],[f19183,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f58,f20])).

fof(f58,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f20,f16])).

fof(f19183,plain,(
    ! [X41,X40] : k5_xboole_0(k2_xboole_0(k2_xboole_0(X41,X40),k2_xboole_0(X40,X41)),k4_xboole_0(k2_xboole_0(X41,X40),k2_xboole_0(X40,X41))) = k5_xboole_0(k2_xboole_0(X41,X40),k4_xboole_0(k2_xboole_0(X41,X40),k2_xboole_0(X40,X41))) ),
    inference(superposition,[],[f828,f84])).

fof(f828,plain,(
    ! [X12,X11] : k5_xboole_0(k2_xboole_0(X11,X12),k4_xboole_0(X12,X11)) = k5_xboole_0(k2_xboole_0(X12,X11),k4_xboole_0(X12,X11)) ),
    inference(forward_demodulation,[],[f827,f16])).

fof(f827,plain,(
    ! [X12,X11] : k5_xboole_0(k2_xboole_0(X12,X11),k4_xboole_0(k2_xboole_0(X12,X11),X11)) = k5_xboole_0(k2_xboole_0(X11,X12),k4_xboole_0(X12,X11)) ),
    inference(forward_demodulation,[],[f826,f213])).

fof(f213,plain,(
    ! [X4,X5] : k5_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) = k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,k2_xboole_0(X4,X5))) ),
    inference(forward_demodulation,[],[f212,f53])).

fof(f212,plain,(
    ! [X4,X5] : k5_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) = k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,k2_xboole_0(X4,k2_xboole_0(X4,X5)))) ),
    inference(forward_demodulation,[],[f186,f20])).

fof(f186,plain,(
    ! [X4,X5] : k5_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) = k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5))) ),
    inference(superposition,[],[f18,f23])).

fof(f826,plain,(
    ! [X12,X11] : k5_xboole_0(k2_xboole_0(X12,X11),k4_xboole_0(k2_xboole_0(X12,X11),X11)) = k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(X12,X11)),k4_xboole_0(X12,k2_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f825,f193])).

fof(f193,plain,(
    ! [X0,X1] : k3_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f26,f171])).

fof(f171,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f23,f14])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f17,f16])).

fof(f825,plain,(
    ! [X12,X11] : k5_xboole_0(k2_xboole_0(X12,X11),k4_xboole_0(k2_xboole_0(X12,X11),X11)) = k2_xboole_0(k3_xboole_0(k2_xboole_0(X12,X11),X11),k4_xboole_0(X12,k2_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f774,f68])).

fof(f774,plain,(
    ! [X12,X11] : k5_xboole_0(k2_xboole_0(X12,X11),k4_xboole_0(k2_xboole_0(X12,X11),X11)) = k2_xboole_0(k3_xboole_0(k2_xboole_0(X12,X11),X11),k4_xboole_0(k2_xboole_0(X12,X11),k2_xboole_0(X11,X12))) ),
    inference(superposition,[],[f39,f25])).

fof(f39,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X2))) ),
    inference(forward_demodulation,[],[f31,f20])).

fof(f31,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),X2)) ),
    inference(superposition,[],[f18,f17])).

fof(f59142,plain,(
    ! [X196,X195] : k5_xboole_0(X196,k5_xboole_0(X196,k2_xboole_0(X195,X196))) = k5_xboole_0(k2_xboole_0(X195,X196),k4_xboole_0(X196,k2_xboole_0(X195,X196))) ),
    inference(forward_demodulation,[],[f59141,f34082])).

fof(f34082,plain,(
    ! [X74,X73] : k4_xboole_0(X73,k2_xboole_0(X74,X73)) = k4_xboole_0(X73,k2_xboole_0(X74,k3_xboole_0(X73,X73))) ),
    inference(forward_demodulation,[],[f34081,f32621])).

fof(f32621,plain,(
    ! [X2,X3] : k4_xboole_0(X3,k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(backward_demodulation,[],[f16915,f32479])).

fof(f32479,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k3_xboole_0(X6,X7)) = k4_xboole_0(k3_xboole_0(X6,X6),X7) ),
    inference(backward_demodulation,[],[f5619,f32478])).

fof(f32478,plain,(
    ! [X78,X77] : k4_xboole_0(X77,k3_xboole_0(X77,X78)) = k4_xboole_0(k2_xboole_0(X77,k4_xboole_0(X77,X78)),k3_xboole_0(X77,X78)) ),
    inference(forward_demodulation,[],[f32477,f31349])).

fof(f31349,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(X0,k2_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f1273,f31348])).

fof(f31348,plain,(
    ! [X187,X186] : k4_xboole_0(X186,k5_xboole_0(X186,k4_xboole_0(X186,X187))) = k4_xboole_0(X186,k3_xboole_0(X186,X187)) ),
    inference(forward_demodulation,[],[f31347,f27])).

fof(f27,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f17,f17])).

fof(f31347,plain,(
    ! [X187,X186] : k3_xboole_0(X186,k4_xboole_0(X186,X187)) = k4_xboole_0(X186,k5_xboole_0(X186,k4_xboole_0(X186,X187))) ),
    inference(forward_demodulation,[],[f30935,f31105])).

fof(f31105,plain,(
    ! [X30,X31] : k5_xboole_0(X30,k4_xboole_0(X30,X31)) = k5_xboole_0(k4_xboole_0(X30,X31),k2_xboole_0(X30,k5_xboole_0(X31,X31))) ),
    inference(forward_demodulation,[],[f31104,f134])).

fof(f134,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,X2)),k3_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f40,f133])).

fof(f133,plain,(
    ! [X4,X5] : k5_xboole_0(k4_xboole_0(X4,X5),X4) = k5_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f132,f39])).

fof(f132,plain,(
    ! [X4,X5] : k5_xboole_0(k4_xboole_0(X4,X5),X4) = k2_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,k2_xboole_0(X5,X4))) ),
    inference(forward_demodulation,[],[f113,f20])).

fof(f113,plain,(
    ! [X4,X5] : k5_xboole_0(k4_xboole_0(X4,X5),X4) = k2_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X4,X5),X4)) ),
    inference(superposition,[],[f34,f17])).

fof(f40,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X2,X3),X2) = k2_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,X2)),k3_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f33,f20])).

fof(f33,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X2,X3),X2) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X2),k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f18,f17])).

fof(f31104,plain,(
    ! [X30,X31] : k5_xboole_0(k4_xboole_0(X30,X31),k2_xboole_0(X30,k5_xboole_0(X31,X31))) = k2_xboole_0(k4_xboole_0(X30,k2_xboole_0(X31,X30)),k3_xboole_0(X30,X31)) ),
    inference(forward_demodulation,[],[f31103,f21137])).

fof(f21137,plain,(
    ! [X130,X128,X129] : k4_xboole_0(X129,k2_xboole_0(X128,X130)) = k4_xboole_0(X129,k2_xboole_0(X128,k2_xboole_0(X130,k5_xboole_0(X128,X128)))) ),
    inference(forward_demodulation,[],[f20722,f7772])).

fof(f7772,plain,(
    ! [X2,X3] : k2_xboole_0(X3,X2) = k2_xboole_0(X2,k2_xboole_0(X3,X3)) ),
    inference(backward_demodulation,[],[f3177,f7759])).

fof(f7759,plain,(
    ! [X2,X3] : k2_xboole_0(X3,X2) = k2_xboole_0(k2_xboole_0(X3,X3),k4_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f266,f7758])).

fof(f7758,plain,(
    ! [X17,X16] : k2_xboole_0(X16,X17) = k2_xboole_0(k2_xboole_0(X16,X16),X17) ),
    inference(forward_demodulation,[],[f7757,f15])).

fof(f7757,plain,(
    ! [X17,X16] : k2_xboole_0(X16,k4_xboole_0(X17,X16)) = k2_xboole_0(k2_xboole_0(X16,X16),X17) ),
    inference(forward_demodulation,[],[f7724,f407])).

fof(f407,plain,(
    ! [X14,X15,X13] : k2_xboole_0(X15,k4_xboole_0(X13,X14)) = k5_xboole_0(X15,k4_xboole_0(X13,k2_xboole_0(X14,X15))) ),
    inference(superposition,[],[f137,f20])).

fof(f7724,plain,(
    ! [X17,X16] : k2_xboole_0(k2_xboole_0(X16,X16),X17) = k5_xboole_0(X16,k4_xboole_0(X17,k2_xboole_0(X16,X16))) ),
    inference(superposition,[],[f7516,f137])).

fof(f7516,plain,(
    ! [X2,X3] : k5_xboole_0(X3,X2) = k5_xboole_0(k2_xboole_0(X3,X3),X2) ),
    inference(forward_demodulation,[],[f7515,f5579])).

fof(f5579,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k3_xboole_0(X0,X0),X1)) ),
    inference(backward_demodulation,[],[f978,f5562])).

fof(f5562,plain,(
    ! [X39,X40] : k4_xboole_0(X40,k2_xboole_0(X39,k4_xboole_0(X39,X40))) = k4_xboole_0(k3_xboole_0(X40,X40),X39) ),
    inference(backward_demodulation,[],[f2872,f5561])).

fof(f5561,plain,(
    ! [X14,X13] : k4_xboole_0(k3_xboole_0(X13,X13),X14) = k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X14,k2_xboole_0(X13,X14))) ),
    inference(forward_demodulation,[],[f5381,f5482])).

fof(f5381,plain,(
    ! [X14,X13] : k4_xboole_0(k3_xboole_0(X13,X13),X14) = k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k3_xboole_0(X13,X14),X14)) ),
    inference(superposition,[],[f448,f353])).

fof(f448,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,k2_xboole_0(X7,X8))) = k4_xboole_0(k3_xboole_0(X6,X8),X7) ),
    inference(backward_demodulation,[],[f65,f443])).

fof(f65,plain,(
    ! [X6,X8,X7] : k3_xboole_0(k4_xboole_0(X6,X7),X8) = k4_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,k2_xboole_0(X7,X8))) ),
    inference(superposition,[],[f17,f20])).

fof(f2872,plain,(
    ! [X39,X40] : k4_xboole_0(k4_xboole_0(X40,X39),k4_xboole_0(X39,k2_xboole_0(X40,X39))) = k4_xboole_0(X40,k2_xboole_0(X39,k4_xboole_0(X39,X40))) ),
    inference(forward_demodulation,[],[f2871,f736])).

fof(f736,plain,(
    ! [X8,X9] : k4_xboole_0(k5_xboole_0(X8,k2_xboole_0(X9,X8)),k4_xboole_0(X8,k2_xboole_0(X9,X8))) = k4_xboole_0(X9,k2_xboole_0(X8,k4_xboole_0(X8,X9))) ),
    inference(forward_demodulation,[],[f735,f66])).

fof(f735,plain,(
    ! [X8,X9] : k4_xboole_0(k5_xboole_0(X8,k2_xboole_0(X9,X8)),k4_xboole_0(X8,k2_xboole_0(X9,X8))) = k4_xboole_0(X9,k2_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X9,X8)))) ),
    inference(forward_demodulation,[],[f664,f20])).

fof(f664,plain,(
    ! [X8,X9] : k4_xboole_0(k4_xboole_0(X9,X8),k4_xboole_0(X8,k2_xboole_0(X9,X8))) = k4_xboole_0(k5_xboole_0(X8,k2_xboole_0(X9,X8)),k4_xboole_0(X8,k2_xboole_0(X9,X8))) ),
    inference(superposition,[],[f21,f32])).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f18,f16])).

fof(f2871,plain,(
    ! [X39,X40] : k4_xboole_0(k4_xboole_0(X40,X39),k4_xboole_0(X39,k2_xboole_0(X40,X39))) = k4_xboole_0(k5_xboole_0(X39,k2_xboole_0(X40,X39)),k4_xboole_0(X39,k2_xboole_0(X40,X39))) ),
    inference(forward_demodulation,[],[f2870,f25])).

fof(f2870,plain,(
    ! [X39,X40] : k4_xboole_0(k4_xboole_0(X40,X39),k4_xboole_0(X39,k2_xboole_0(X40,k2_xboole_0(X39,X40)))) = k4_xboole_0(k5_xboole_0(X39,k2_xboole_0(X40,X39)),k4_xboole_0(X39,k2_xboole_0(X40,k2_xboole_0(X39,X40)))) ),
    inference(forward_demodulation,[],[f2869,f15])).

fof(f2869,plain,(
    ! [X39,X40] : k4_xboole_0(k4_xboole_0(X40,X39),k4_xboole_0(X39,k2_xboole_0(X40,k2_xboole_0(X39,k4_xboole_0(X40,X39))))) = k4_xboole_0(k5_xboole_0(X39,k2_xboole_0(X40,X39)),k4_xboole_0(X39,k2_xboole_0(X40,k2_xboole_0(X39,k4_xboole_0(X40,X39))))) ),
    inference(forward_demodulation,[],[f2868,f71])).

fof(f71,plain,(
    ! [X12,X10,X11,X9] : k4_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X11),X12)) = k4_xboole_0(X9,k2_xboole_0(X10,k2_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f70,f20])).

fof(f70,plain,(
    ! [X12,X10,X11,X9] : k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X11,X12)) = k4_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X11),X12)) ),
    inference(forward_demodulation,[],[f61,f20])).

fof(f61,plain,(
    ! [X12,X10,X11,X9] : k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X11,X12)) = k4_xboole_0(k4_xboole_0(X9,k2_xboole_0(X10,X11)),X12) ),
    inference(superposition,[],[f20,f20])).

fof(f2868,plain,(
    ! [X39,X40] : k4_xboole_0(k4_xboole_0(X40,X39),k4_xboole_0(X39,k2_xboole_0(k2_xboole_0(X40,X39),k4_xboole_0(X40,X39)))) = k4_xboole_0(k5_xboole_0(X39,k2_xboole_0(X40,X39)),k4_xboole_0(X39,k2_xboole_0(k2_xboole_0(X40,X39),k4_xboole_0(X40,X39)))) ),
    inference(forward_demodulation,[],[f2793,f20])).

fof(f2793,plain,(
    ! [X39,X40] : k4_xboole_0(k4_xboole_0(X40,X39),k4_xboole_0(k4_xboole_0(X39,k2_xboole_0(X40,X39)),k4_xboole_0(X40,X39))) = k4_xboole_0(k5_xboole_0(X39,k2_xboole_0(X40,X39)),k4_xboole_0(k4_xboole_0(X39,k2_xboole_0(X40,X39)),k4_xboole_0(X40,X39))) ),
    inference(superposition,[],[f171,f32])).

fof(f978,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(forward_demodulation,[],[f923,f165])).

fof(f165,plain,(
    ! [X10,X11] : k5_xboole_0(X11,X10) = k2_xboole_0(k4_xboole_0(X10,X11),k5_xboole_0(X11,X10)) ),
    inference(superposition,[],[f53,f34])).

fof(f923,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X1,X0),k5_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[],[f15,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f36,f20])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f16,f18])).

fof(f7515,plain,(
    ! [X2,X3] : k5_xboole_0(k2_xboole_0(X3,X3),X2) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X3,X3),X2)) ),
    inference(forward_demodulation,[],[f7514,f60])).

fof(f7514,plain,(
    ! [X2,X3] : k5_xboole_0(k2_xboole_0(X3,X3),X2) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,X3),X2))) ),
    inference(forward_demodulation,[],[f7513,f20])).

fof(f7513,plain,(
    ! [X2,X3] : k5_xboole_0(k2_xboole_0(X3,X3),X2) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X3)),X2)) ),
    inference(forward_demodulation,[],[f7512,f52])).

fof(f52,plain,(
    ! [X6,X5] : k3_xboole_0(k2_xboole_0(X5,X6),X5) = k4_xboole_0(X5,k4_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f48,f23])).

fof(f48,plain,(
    ! [X6,X5] : k3_xboole_0(k2_xboole_0(X5,X6),X5) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) ),
    inference(superposition,[],[f17,f21])).

fof(f7512,plain,(
    ! [X2,X3] : k5_xboole_0(k2_xboole_0(X3,X3),X2) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(k2_xboole_0(X3,X3),X3),X2)) ),
    inference(forward_demodulation,[],[f7417,f284])).

fof(f284,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X4,k2_xboole_0(X5,X5)) ),
    inference(forward_demodulation,[],[f267,f17])).

fof(f267,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,k2_xboole_0(X5,X5)) ),
    inference(superposition,[],[f17,f100])).

fof(f100,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(X1,X1)) ),
    inference(superposition,[],[f50,f20])).

fof(f7417,plain,(
    ! [X2,X3] : k5_xboole_0(k2_xboole_0(X3,X3),X2) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(k2_xboole_0(X3,X3),k2_xboole_0(X3,X3)),X2)) ),
    inference(superposition,[],[f5579,f100])).

fof(f266,plain,(
    ! [X2,X3] : k2_xboole_0(k2_xboole_0(X3,X3),X2) = k2_xboole_0(k2_xboole_0(X3,X3),k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f15,f100])).

fof(f3177,plain,(
    ! [X2,X3] : k2_xboole_0(k2_xboole_0(X3,X3),k4_xboole_0(X2,X3)) = k2_xboole_0(X2,k2_xboole_0(X3,X3)) ),
    inference(superposition,[],[f2970,f100])).

fof(f2970,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f2903,f14])).

fof(f2903,plain,(
    ! [X6,X5] : k2_xboole_0(X5,X6) = k2_xboole_0(k4_xboole_0(X5,X6),X6) ),
    inference(forward_demodulation,[],[f2902,f1163])).

fof(f1163,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f82,f14])).

fof(f2902,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),X6) = k2_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f2815,f15])).

fof(f2815,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,X6)) = k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f15,f171])).

fof(f20722,plain,(
    ! [X130,X128,X129] : k4_xboole_0(X129,k2_xboole_0(X130,k2_xboole_0(X128,X128))) = k4_xboole_0(X129,k2_xboole_0(X128,k2_xboole_0(X130,k5_xboole_0(X128,X128)))) ),
    inference(superposition,[],[f1068,f12977])).

fof(f12977,plain,(
    ! [X40] : k2_xboole_0(X40,X40) = k2_xboole_0(k5_xboole_0(X40,X40),X40) ),
    inference(forward_demodulation,[],[f12976,f6715])).

fof(f6715,plain,(
    ! [X54,X53] : k2_xboole_0(X53,X54) = k2_xboole_0(k2_xboole_0(X53,X54),k3_xboole_0(X53,X53)) ),
    inference(forward_demodulation,[],[f6714,f53])).

fof(f6714,plain,(
    ! [X54,X53] : k2_xboole_0(k2_xboole_0(X53,X54),k3_xboole_0(X53,X53)) = k2_xboole_0(X53,k2_xboole_0(X53,X54)) ),
    inference(forward_demodulation,[],[f6713,f14])).

fof(f6713,plain,(
    ! [X54,X53] : k2_xboole_0(k2_xboole_0(X53,X54),k3_xboole_0(X53,X53)) = k2_xboole_0(k2_xboole_0(X53,X54),X53) ),
    inference(forward_demodulation,[],[f6672,f2634])).

fof(f2634,plain,(
    ! [X30,X28,X29] : k2_xboole_0(k2_xboole_0(X28,X30),k2_xboole_0(X28,X29)) = k2_xboole_0(k2_xboole_0(X28,X30),X29) ),
    inference(forward_demodulation,[],[f2563,f15])).

fof(f2563,plain,(
    ! [X30,X28,X29] : k2_xboole_0(k2_xboole_0(X28,X30),k2_xboole_0(X28,X29)) = k2_xboole_0(k2_xboole_0(X28,X30),k4_xboole_0(X29,k2_xboole_0(X28,X30))) ),
    inference(superposition,[],[f15,f69])).

fof(f6672,plain,(
    ! [X54,X53] : k2_xboole_0(k2_xboole_0(X53,X54),k3_xboole_0(X53,X53)) = k2_xboole_0(k2_xboole_0(X53,X54),k2_xboole_0(X53,X53)) ),
    inference(superposition,[],[f601,f6177])).

fof(f6177,plain,(
    ! [X44] : k2_xboole_0(k3_xboole_0(X44,X44),X44) = k2_xboole_0(X44,X44) ),
    inference(forward_demodulation,[],[f6118,f211])).

fof(f6118,plain,(
    ! [X44] : k2_xboole_0(k3_xboole_0(X44,X44),X44) = k2_xboole_0(k4_xboole_0(X44,X44),X44) ),
    inference(superposition,[],[f2903,f5896])).

fof(f5896,plain,(
    ! [X15] : k4_xboole_0(X15,X15) = k4_xboole_0(k3_xboole_0(X15,X15),X15) ),
    inference(forward_demodulation,[],[f5895,f17])).

fof(f5895,plain,(
    ! [X15] : k4_xboole_0(X15,X15) = k4_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X15)),X15) ),
    inference(forward_demodulation,[],[f5894,f52])).

fof(f5894,plain,(
    ! [X15] : k4_xboole_0(X15,X15) = k4_xboole_0(k3_xboole_0(k2_xboole_0(X15,X15),X15),X15) ),
    inference(forward_demodulation,[],[f5893,f284])).

fof(f5893,plain,(
    ! [X15] : k4_xboole_0(X15,X15) = k4_xboole_0(k3_xboole_0(k2_xboole_0(X15,X15),k2_xboole_0(X15,X15)),X15) ),
    inference(forward_demodulation,[],[f5892,f1939])).

fof(f1939,plain,(
    ! [X2] : k4_xboole_0(X2,X2) = k4_xboole_0(X2,k2_xboole_0(X2,k5_xboole_0(X2,X2))) ),
    inference(forward_demodulation,[],[f1938,f16])).

fof(f1938,plain,(
    ! [X2] : k4_xboole_0(X2,k2_xboole_0(X2,k5_xboole_0(X2,X2))) = k4_xboole_0(k2_xboole_0(X2,X2),X2) ),
    inference(forward_demodulation,[],[f1937,f100])).

fof(f1937,plain,(
    ! [X2] : k4_xboole_0(X2,k2_xboole_0(X2,k5_xboole_0(X2,X2))) = k4_xboole_0(k2_xboole_0(X2,X2),k2_xboole_0(X2,X2)) ),
    inference(forward_demodulation,[],[f1936,f15])).

fof(f1936,plain,(
    ! [X2] : k4_xboole_0(k2_xboole_0(X2,X2),k2_xboole_0(X2,k4_xboole_0(X2,X2))) = k4_xboole_0(X2,k2_xboole_0(X2,k5_xboole_0(X2,X2))) ),
    inference(forward_demodulation,[],[f1935,f1734])).

fof(f1734,plain,(
    ! [X6,X7] : k4_xboole_0(X7,k2_xboole_0(X6,k5_xboole_0(X6,X7))) = k4_xboole_0(k5_xboole_0(X7,X6),k5_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f1693,f20])).

fof(f1693,plain,(
    ! [X6,X7] : k4_xboole_0(k4_xboole_0(X7,X6),k5_xboole_0(X6,X7)) = k4_xboole_0(k5_xboole_0(X7,X6),k5_xboole_0(X6,X7)) ),
    inference(superposition,[],[f21,f86])).

fof(f86,plain,(
    ! [X8,X9] : k2_xboole_0(k5_xboole_0(X8,X9),k4_xboole_0(X9,X8)) = k5_xboole_0(X9,X8) ),
    inference(forward_demodulation,[],[f85,f18])).

fof(f85,plain,(
    ! [X8,X9] : k2_xboole_0(k4_xboole_0(X9,X8),k4_xboole_0(X8,X9)) = k2_xboole_0(k5_xboole_0(X8,X9),k4_xboole_0(X9,X8)) ),
    inference(forward_demodulation,[],[f78,f14])).

fof(f78,plain,(
    ! [X8,X9] : k2_xboole_0(k4_xboole_0(X9,X8),k4_xboole_0(X8,X9)) = k2_xboole_0(k4_xboole_0(X9,X8),k5_xboole_0(X8,X9)) ),
    inference(superposition,[],[f25,f18])).

fof(f1935,plain,(
    ! [X2] : k4_xboole_0(k2_xboole_0(X2,X2),k2_xboole_0(X2,k4_xboole_0(X2,X2))) = k4_xboole_0(k5_xboole_0(X2,X2),k5_xboole_0(X2,X2)) ),
    inference(forward_demodulation,[],[f1934,f259])).

fof(f259,plain,(
    ! [X4,X5] : k4_xboole_0(X5,k4_xboole_0(X4,X4)) = k4_xboole_0(X5,k5_xboole_0(X4,X4)) ),
    inference(superposition,[],[f100,f34])).

fof(f1934,plain,(
    ! [X2] : k4_xboole_0(k2_xboole_0(X2,X2),k2_xboole_0(X2,k4_xboole_0(X2,X2))) = k4_xboole_0(k5_xboole_0(X2,X2),k4_xboole_0(X2,X2)) ),
    inference(forward_demodulation,[],[f1922,f100])).

fof(f1922,plain,(
    ! [X2] : k4_xboole_0(k2_xboole_0(X2,X2),k2_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(X2,X2)))) = k4_xboole_0(k5_xboole_0(X2,X2),k4_xboole_0(X2,k2_xboole_0(X2,X2))) ),
    inference(superposition,[],[f41,f1718])).

fof(f1718,plain,(
    ! [X6] : k5_xboole_0(X6,X6) = k5_xboole_0(k2_xboole_0(X6,X6),X6) ),
    inference(forward_demodulation,[],[f1717,f86])).

fof(f1717,plain,(
    ! [X6] : k5_xboole_0(k2_xboole_0(X6,X6),X6) = k2_xboole_0(k5_xboole_0(X6,X6),k4_xboole_0(X6,X6)) ),
    inference(forward_demodulation,[],[f1676,f16])).

fof(f1676,plain,(
    ! [X6] : k5_xboole_0(k2_xboole_0(X6,X6),X6) = k2_xboole_0(k5_xboole_0(X6,X6),k4_xboole_0(k2_xboole_0(X6,X6),X6)) ),
    inference(superposition,[],[f86,f704])).

fof(f704,plain,(
    ! [X2] : k5_xboole_0(X2,k2_xboole_0(X2,X2)) = k5_xboole_0(X2,X2) ),
    inference(forward_demodulation,[],[f646,f18])).

fof(f646,plain,(
    ! [X2] : k5_xboole_0(X2,k2_xboole_0(X2,X2)) = k2_xboole_0(k4_xboole_0(X2,X2),k4_xboole_0(X2,X2)) ),
    inference(superposition,[],[f32,f100])).

fof(f5892,plain,(
    ! [X15] : k4_xboole_0(k3_xboole_0(k2_xboole_0(X15,X15),k2_xboole_0(X15,X15)),X15) = k4_xboole_0(X15,k2_xboole_0(X15,k5_xboole_0(X15,X15))) ),
    inference(forward_demodulation,[],[f5891,f1734])).

fof(f5891,plain,(
    ! [X15] : k4_xboole_0(k3_xboole_0(k2_xboole_0(X15,X15),k2_xboole_0(X15,X15)),X15) = k4_xboole_0(k5_xboole_0(X15,X15),k5_xboole_0(X15,X15)) ),
    inference(forward_demodulation,[],[f5890,f259])).

fof(f5890,plain,(
    ! [X15] : k4_xboole_0(k3_xboole_0(k2_xboole_0(X15,X15),k2_xboole_0(X15,X15)),X15) = k4_xboole_0(k5_xboole_0(X15,X15),k4_xboole_0(X15,X15)) ),
    inference(forward_demodulation,[],[f5808,f100])).

fof(f5808,plain,(
    ! [X15] : k4_xboole_0(k3_xboole_0(k2_xboole_0(X15,X15),k2_xboole_0(X15,X15)),X15) = k4_xboole_0(k5_xboole_0(X15,X15),k4_xboole_0(X15,k2_xboole_0(X15,X15))) ),
    inference(superposition,[],[f5563,f1718])).

fof(f5563,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k3_xboole_0(X0,X0),X1) ),
    inference(backward_demodulation,[],[f41,f5562])).

fof(f601,plain,(
    ! [X8,X7,X9] : k2_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X7,X8)) = k2_xboole_0(k2_xboole_0(X8,X9),X7) ),
    inference(forward_demodulation,[],[f575,f15])).

fof(f575,plain,(
    ! [X8,X7,X9] : k2_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X7,X8)) = k2_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X7,k2_xboole_0(X8,X9))) ),
    inference(superposition,[],[f15,f68])).

fof(f12976,plain,(
    ! [X40] : k2_xboole_0(k5_xboole_0(X40,X40),X40) = k2_xboole_0(k2_xboole_0(X40,X40),k3_xboole_0(X40,X40)) ),
    inference(forward_demodulation,[],[f12886,f3059])).

fof(f3059,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k4_xboole_0(X0,k5_xboole_0(X0,X0)) ),
    inference(superposition,[],[f351,f97])).

fof(f97,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f50,f17])).

fof(f351,plain,(
    ! [X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k5_xboole_0(X1,X0)) ),
    inference(superposition,[],[f60,f34])).

fof(f12886,plain,(
    ! [X40] : k2_xboole_0(k5_xboole_0(X40,X40),X40) = k2_xboole_0(k2_xboole_0(X40,X40),k4_xboole_0(X40,k5_xboole_0(X40,X40))) ),
    inference(superposition,[],[f307,f9809])).

fof(f9809,plain,(
    ! [X17] : k2_xboole_0(X17,X17) = k2_xboole_0(X17,k5_xboole_0(X17,X17)) ),
    inference(backward_demodulation,[],[f9080,f9808])).

fof(f9808,plain,(
    ! [X16] : k2_xboole_0(X16,X16) = k5_xboole_0(k5_xboole_0(X16,X16),k2_xboole_0(X16,k5_xboole_0(X16,X16))) ),
    inference(forward_demodulation,[],[f9807,f14])).

fof(f9807,plain,(
    ! [X16] : k2_xboole_0(X16,X16) = k5_xboole_0(k5_xboole_0(X16,X16),k2_xboole_0(k5_xboole_0(X16,X16),X16)) ),
    inference(forward_demodulation,[],[f9806,f137])).

fof(f9806,plain,(
    ! [X16] : k5_xboole_0(k5_xboole_0(X16,X16),k2_xboole_0(k5_xboole_0(X16,X16),X16)) = k5_xboole_0(X16,k4_xboole_0(X16,X16)) ),
    inference(forward_demodulation,[],[f9805,f134])).

fof(f9805,plain,(
    ! [X16] : k5_xboole_0(k5_xboole_0(X16,X16),k2_xboole_0(k5_xboole_0(X16,X16),X16)) = k2_xboole_0(k4_xboole_0(X16,k2_xboole_0(X16,X16)),k3_xboole_0(X16,X16)) ),
    inference(forward_demodulation,[],[f9804,f7927])).

fof(f7927,plain,(
    ! [X45,X44] : k4_xboole_0(X44,k2_xboole_0(X45,X44)) = k4_xboole_0(X44,k2_xboole_0(X45,k5_xboole_0(X44,X45))) ),
    inference(forward_demodulation,[],[f7926,f25])).

fof(f7926,plain,(
    ! [X45,X44] : k4_xboole_0(X44,k2_xboole_0(X45,k5_xboole_0(X44,X45))) = k4_xboole_0(X44,k2_xboole_0(X45,k2_xboole_0(X44,X45))) ),
    inference(forward_demodulation,[],[f7925,f20])).

fof(f7925,plain,(
    ! [X45,X44] : k4_xboole_0(k4_xboole_0(X44,X45),k2_xboole_0(X44,X45)) = k4_xboole_0(X44,k2_xboole_0(X45,k5_xboole_0(X44,X45))) ),
    inference(forward_demodulation,[],[f7924,f5947])).

fof(f5947,plain,(
    ! [X33,X32] : k4_xboole_0(X32,k2_xboole_0(X33,k5_xboole_0(X32,X33))) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X32,X32),X33),k2_xboole_0(X32,X33)) ),
    inference(forward_demodulation,[],[f5946,f1589])).

fof(f1589,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k3_xboole_0(X8,k4_xboole_0(X7,X6)),X6) = k4_xboole_0(k3_xboole_0(X8,X7),X6) ),
    inference(forward_demodulation,[],[f1510,f448])).

fof(f1510,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k3_xboole_0(X8,k4_xboole_0(X7,X6)),X6) = k4_xboole_0(k4_xboole_0(X8,X6),k4_xboole_0(X8,k2_xboole_0(X6,X7))) ),
    inference(superposition,[],[f448,f15])).

fof(f5946,plain,(
    ! [X33,X32] : k4_xboole_0(X32,k2_xboole_0(X33,k5_xboole_0(X32,X33))) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X32,k4_xboole_0(X32,X33)),X33),k2_xboole_0(X32,X33)) ),
    inference(forward_demodulation,[],[f5945,f443])).

fof(f5945,plain,(
    ! [X33,X32] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(X32,X33)),k2_xboole_0(X32,X33)) = k4_xboole_0(X32,k2_xboole_0(X33,k5_xboole_0(X32,X33))) ),
    inference(forward_demodulation,[],[f5944,f2304])).

fof(f2304,plain,(
    ! [X14,X15] : k4_xboole_0(k5_xboole_0(k2_xboole_0(X14,X15),k4_xboole_0(X15,X14)),k4_xboole_0(X14,k4_xboole_0(X15,X14))) = k4_xboole_0(X15,k2_xboole_0(X14,k5_xboole_0(X15,X14))) ),
    inference(backward_demodulation,[],[f971,f2303])).

fof(f2303,plain,(
    ! [X17,X16] : k4_xboole_0(X17,k2_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X17,X16))))) = k4_xboole_0(X17,k2_xboole_0(X16,k5_xboole_0(X17,X16))) ),
    inference(backward_demodulation,[],[f975,f2301])).

fof(f2301,plain,(
    ! [X33,X34] : k5_xboole_0(X34,X33) = k2_xboole_0(k5_xboole_0(X33,X34),k4_xboole_0(X33,k2_xboole_0(X34,k4_xboole_0(X34,X33)))) ),
    inference(forward_demodulation,[],[f2300,f18])).

fof(f2300,plain,(
    ! [X33,X34] : k2_xboole_0(k4_xboole_0(X34,X33),k4_xboole_0(X33,X34)) = k2_xboole_0(k5_xboole_0(X33,X34),k4_xboole_0(X33,k2_xboole_0(X34,k4_xboole_0(X34,X33)))) ),
    inference(forward_demodulation,[],[f2236,f20])).

fof(f2236,plain,(
    ! [X33,X34] : k2_xboole_0(k4_xboole_0(X34,X33),k4_xboole_0(X33,X34)) = k2_xboole_0(k5_xboole_0(X33,X34),k4_xboole_0(k4_xboole_0(X33,X34),k4_xboole_0(X34,X33))) ),
    inference(superposition,[],[f307,f18])).

fof(f975,plain,(
    ! [X17,X16] : k4_xboole_0(X17,k2_xboole_0(X16,k2_xboole_0(k5_xboole_0(X16,X17),k4_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X17,X16)))))) = k4_xboole_0(X17,k2_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X17,X16))))) ),
    inference(forward_demodulation,[],[f974,f741])).

fof(f741,plain,(
    ! [X10,X11] : k4_xboole_0(k5_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(X10,k2_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X10,X11))))) ),
    inference(forward_demodulation,[],[f740,f419])).

fof(f740,plain,(
    ! [X10,X11] : k4_xboole_0(k5_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(X10,k2_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11)))))) ),
    inference(forward_demodulation,[],[f739,f71])).

fof(f739,plain,(
    ! [X10,X11] : k4_xboole_0(k5_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(X10,k2_xboole_0(k2_xboole_0(X11,X10),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11))))) ),
    inference(forward_demodulation,[],[f738,f20])).

fof(f738,plain,(
    ! [X10,X11] : k4_xboole_0(k4_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(k5_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11)))) ),
    inference(forward_demodulation,[],[f737,f66])).

fof(f737,plain,(
    ! [X10,X11] : k4_xboole_0(k4_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,k2_xboole_0(X11,X10))))) = k4_xboole_0(k5_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,k2_xboole_0(X11,X10))))) ),
    inference(forward_demodulation,[],[f665,f20])).

fof(f665,plain,(
    ! [X10,X11] : k4_xboole_0(k4_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(k4_xboole_0(X11,X10),k4_xboole_0(X10,k2_xboole_0(X11,X10)))) = k4_xboole_0(k5_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(k4_xboole_0(X11,X10),k4_xboole_0(X10,k2_xboole_0(X11,X10)))) ),
    inference(superposition,[],[f23,f32])).

fof(f974,plain,(
    ! [X17,X16] : k4_xboole_0(X17,k2_xboole_0(X16,k2_xboole_0(k5_xboole_0(X16,X17),k4_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X17,X16)))))) = k4_xboole_0(k5_xboole_0(X17,k2_xboole_0(X16,X17)),k4_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X17,X16)))) ),
    inference(forward_demodulation,[],[f973,f130])).

fof(f130,plain,(
    ! [X0,X1] : k5_xboole_0(k2_xboole_0(X0,X1),X1) = k5_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f30,f111])).

fof(f111,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X0,X1))) = k5_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f34,f16])).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f18,f16])).

fof(f973,plain,(
    ! [X17,X16] : k4_xboole_0(X17,k2_xboole_0(X16,k2_xboole_0(k5_xboole_0(X16,X17),k4_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X17,X16)))))) = k4_xboole_0(k5_xboole_0(k2_xboole_0(X16,X17),X17),k4_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X17,X16)))) ),
    inference(forward_demodulation,[],[f972,f336])).

fof(f336,plain,(
    ! [X6,X4,X5] : k5_xboole_0(k4_xboole_0(X4,X5),k5_xboole_0(X5,X6)) = k5_xboole_0(k2_xboole_0(X5,X4),X6) ),
    inference(superposition,[],[f19,f109])).

fof(f109,plain,(
    ! [X4,X5] : k2_xboole_0(X5,X4) = k5_xboole_0(k4_xboole_0(X4,X5),X5) ),
    inference(forward_demodulation,[],[f108,f15])).

fof(f108,plain,(
    ! [X4,X5] : k5_xboole_0(k4_xboole_0(X4,X5),X5) = k2_xboole_0(X5,k4_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f107,f14])).

fof(f107,plain,(
    ! [X4,X5] : k5_xboole_0(k4_xboole_0(X4,X5),X5) = k2_xboole_0(k4_xboole_0(X4,X5),X5) ),
    inference(forward_demodulation,[],[f102,f15])).

fof(f102,plain,(
    ! [X4,X5] : k5_xboole_0(k4_xboole_0(X4,X5),X5) = k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X4,X5))) ),
    inference(superposition,[],[f18,f50])).

fof(f19,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f972,plain,(
    ! [X17,X16] : k4_xboole_0(k5_xboole_0(k4_xboole_0(X17,X16),k5_xboole_0(X16,X17)),k4_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X17,X16)))) = k4_xboole_0(X17,k2_xboole_0(X16,k2_xboole_0(k5_xboole_0(X16,X17),k4_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X17,X16)))))) ),
    inference(forward_demodulation,[],[f920,f20])).

fof(f920,plain,(
    ! [X17,X16] : k4_xboole_0(k5_xboole_0(k4_xboole_0(X17,X16),k5_xboole_0(X16,X17)),k4_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X17,X16)))) = k4_xboole_0(k4_xboole_0(X17,X16),k2_xboole_0(k5_xboole_0(X16,X17),k4_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X17,X16))))) ),
    inference(superposition,[],[f41,f41])).

fof(f971,plain,(
    ! [X14,X15] : k4_xboole_0(X15,k2_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X15,X14))))) = k4_xboole_0(k5_xboole_0(k2_xboole_0(X14,X15),k4_xboole_0(X15,X14)),k4_xboole_0(X14,k4_xboole_0(X15,X14))) ),
    inference(forward_demodulation,[],[f970,f121])).

fof(f121,plain,(
    ! [X2,X3] : k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2) ),
    inference(superposition,[],[f34,f18])).

fof(f970,plain,(
    ! [X14,X15] : k4_xboole_0(k5_xboole_0(k4_xboole_0(X15,X14),k2_xboole_0(X14,X15)),k4_xboole_0(X14,k4_xboole_0(X15,X14))) = k4_xboole_0(X15,k2_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X15,X14))))) ),
    inference(forward_demodulation,[],[f969,f53])).

fof(f969,plain,(
    ! [X14,X15] : k4_xboole_0(k5_xboole_0(k4_xboole_0(X15,X14),k2_xboole_0(X14,X15)),k4_xboole_0(X14,k4_xboole_0(X15,X14))) = k4_xboole_0(X15,k2_xboole_0(X14,k2_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X15,X14)))))) ),
    inference(forward_demodulation,[],[f968,f20])).

fof(f968,plain,(
    ! [X14,X15] : k4_xboole_0(k5_xboole_0(k4_xboole_0(X15,X14),k2_xboole_0(X14,X15)),k4_xboole_0(X14,k4_xboole_0(X15,X14))) = k4_xboole_0(k4_xboole_0(X15,X14),k2_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X15,X14))))) ),
    inference(forward_demodulation,[],[f919,f71])).

fof(f919,plain,(
    ! [X14,X15] : k4_xboole_0(k5_xboole_0(k4_xboole_0(X15,X14),k2_xboole_0(X14,X15)),k4_xboole_0(X14,k4_xboole_0(X15,X14))) = k4_xboole_0(k4_xboole_0(X15,X14),k2_xboole_0(k2_xboole_0(X14,X15),k4_xboole_0(X14,k4_xboole_0(X15,X14)))) ),
    inference(superposition,[],[f41,f23])).

fof(f5944,plain,(
    ! [X33,X32] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(X32,X33)),k2_xboole_0(X32,X33)) = k4_xboole_0(k5_xboole_0(k2_xboole_0(X33,X32),k4_xboole_0(X32,X33)),k4_xboole_0(X33,k4_xboole_0(X32,X33))) ),
    inference(forward_demodulation,[],[f5828,f2900])).

fof(f2900,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k5_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f2899,f216])).

fof(f216,plain,(
    ! [X6,X7] : k2_xboole_0(k4_xboole_0(X7,k2_xboole_0(X6,X7)),k4_xboole_0(X6,k4_xboole_0(X7,X6))) = k5_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) ),
    inference(forward_demodulation,[],[f215,f121])).

fof(f215,plain,(
    ! [X6,X7] : k5_xboole_0(k4_xboole_0(X7,X6),k2_xboole_0(X6,X7)) = k2_xboole_0(k4_xboole_0(X7,k2_xboole_0(X6,X7)),k4_xboole_0(X6,k4_xboole_0(X7,X6))) ),
    inference(forward_demodulation,[],[f214,f53])).

fof(f214,plain,(
    ! [X6,X7] : k5_xboole_0(k4_xboole_0(X7,X6),k2_xboole_0(X6,X7)) = k2_xboole_0(k4_xboole_0(X7,k2_xboole_0(X6,k2_xboole_0(X6,X7))),k4_xboole_0(X6,k4_xboole_0(X7,X6))) ),
    inference(forward_demodulation,[],[f187,f20])).

fof(f187,plain,(
    ! [X6,X7] : k5_xboole_0(k4_xboole_0(X7,X6),k2_xboole_0(X6,X7)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X7,X6),k2_xboole_0(X6,X7)),k4_xboole_0(X6,k4_xboole_0(X7,X6))) ),
    inference(superposition,[],[f18,f23])).

fof(f2899,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X1)),k4_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f2813,f25])).

fof(f2813,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X2))),k4_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(superposition,[],[f64,f171])).

fof(f64,plain,(
    ! [X4,X5,X3] : k5_xboole_0(k4_xboole_0(X3,X4),X5) = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X4,X5)),k4_xboole_0(X5,k4_xboole_0(X3,X4))) ),
    inference(superposition,[],[f18,f20])).

fof(f5828,plain,(
    ! [X33,X32] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(X32,X33)),k2_xboole_0(X32,X33)) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X32,X33),k2_xboole_0(X32,X33)),k4_xboole_0(X33,k4_xboole_0(X32,X33))) ),
    inference(superposition,[],[f5563,f171])).

fof(f7924,plain,(
    ! [X45,X44] : k4_xboole_0(k4_xboole_0(X44,X45),k2_xboole_0(X44,X45)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X44,X44),X45),k2_xboole_0(X44,X45)) ),
    inference(forward_demodulation,[],[f7923,f1589])).

fof(f7923,plain,(
    ! [X45,X44] : k4_xboole_0(k4_xboole_0(X44,X45),k2_xboole_0(X44,X45)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X44,k4_xboole_0(X44,X45)),X45),k2_xboole_0(X44,X45)) ),
    inference(forward_demodulation,[],[f7835,f443])).

fof(f7835,plain,(
    ! [X45,X44] : k4_xboole_0(k4_xboole_0(X44,X45),k2_xboole_0(X44,X45)) = k4_xboole_0(k3_xboole_0(k4_xboole_0(X44,X45),k4_xboole_0(X44,X45)),k2_xboole_0(X44,X45)) ),
    inference(superposition,[],[f5924,f2903])).

fof(f5924,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k2_xboole_0(X17,X18)) = k4_xboole_0(k3_xboole_0(X17,X17),k2_xboole_0(X17,X18)) ),
    inference(forward_demodulation,[],[f5822,f1125])).

fof(f1125,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k2_xboole_0(X7,X8)) = k4_xboole_0(k5_xboole_0(X7,k2_xboole_0(X7,X8)),k4_xboole_0(X8,X7)) ),
    inference(forward_demodulation,[],[f1119,f282])).

fof(f282,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X6,k2_xboole_0(X7,X8)) = k4_xboole_0(X6,k2_xboole_0(X7,k2_xboole_0(X8,X8))) ),
    inference(forward_demodulation,[],[f263,f20])).

fof(f263,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k4_xboole_0(X6,X7),X8) = k4_xboole_0(X6,k2_xboole_0(X7,k2_xboole_0(X8,X8))) ),
    inference(superposition,[],[f100,f20])).

fof(f1119,plain,(
    ! [X8,X7] : k4_xboole_0(k5_xboole_0(X7,k2_xboole_0(X7,X8)),k4_xboole_0(X8,X7)) = k4_xboole_0(X7,k2_xboole_0(X7,k2_xboole_0(X8,X8))) ),
    inference(backward_demodulation,[],[f962,f1118])).

fof(f1118,plain,(
    ! [X14,X17,X15,X16] : k4_xboole_0(X17,k2_xboole_0(X14,k2_xboole_0(X15,X16))) = k4_xboole_0(X17,k2_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X16,X14)))) ),
    inference(forward_demodulation,[],[f1117,f66])).

fof(f1117,plain,(
    ! [X14,X17,X15,X16] : k4_xboole_0(X17,k2_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X16,k2_xboole_0(X14,X15))))) = k4_xboole_0(X17,k2_xboole_0(X14,k2_xboole_0(X15,X16))) ),
    inference(forward_demodulation,[],[f1070,f71])).

fof(f1070,plain,(
    ! [X14,X17,X15,X16] : k4_xboole_0(X17,k2_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X16,k2_xboole_0(X14,X15))))) = k4_xboole_0(X17,k2_xboole_0(k2_xboole_0(X14,X15),X16)) ),
    inference(superposition,[],[f71,f15])).

fof(f962,plain,(
    ! [X8,X7] : k4_xboole_0(k5_xboole_0(X7,k2_xboole_0(X7,X8)),k4_xboole_0(X8,X7)) = k4_xboole_0(X7,k2_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X8,X7)))) ),
    inference(forward_demodulation,[],[f916,f71])).

fof(f916,plain,(
    ! [X8,X7] : k4_xboole_0(k5_xboole_0(X7,k2_xboole_0(X7,X8)),k4_xboole_0(X8,X7)) = k4_xboole_0(X7,k2_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X8,X7))) ),
    inference(superposition,[],[f41,f21])).

fof(f5822,plain,(
    ! [X17,X18] : k4_xboole_0(k3_xboole_0(X17,X17),k2_xboole_0(X17,X18)) = k4_xboole_0(k5_xboole_0(X17,k2_xboole_0(X17,X18)),k4_xboole_0(X18,X17)) ),
    inference(superposition,[],[f5563,f21])).

fof(f9804,plain,(
    ! [X16] : k5_xboole_0(k5_xboole_0(X16,X16),k2_xboole_0(k5_xboole_0(X16,X16),X16)) = k2_xboole_0(k4_xboole_0(X16,k2_xboole_0(X16,k5_xboole_0(X16,X16))),k3_xboole_0(X16,X16)) ),
    inference(forward_demodulation,[],[f9803,f1479])).

fof(f1479,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k2_xboole_0(X0,X1)) = k4_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f1478,f25])).

fof(f1478,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k2_xboole_0(X1,X0)) = k4_xboole_0(X2,k2_xboole_0(X0,k2_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f1426,f53])).

fof(f1426,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k2_xboole_0(X1,X0)) = k4_xboole_0(X2,k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X1,X0)))) ),
    inference(superposition,[],[f71,f84])).

fof(f9803,plain,(
    ! [X16] : k5_xboole_0(k5_xboole_0(X16,X16),k2_xboole_0(k5_xboole_0(X16,X16),X16)) = k2_xboole_0(k4_xboole_0(X16,k2_xboole_0(k5_xboole_0(X16,X16),X16)),k3_xboole_0(X16,X16)) ),
    inference(forward_demodulation,[],[f9802,f5482])).

fof(f9802,plain,(
    ! [X16] : k5_xboole_0(k5_xboole_0(X16,X16),k2_xboole_0(k5_xboole_0(X16,X16),X16)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(k5_xboole_0(X16,X16),X16),X16),k3_xboole_0(X16,X16)) ),
    inference(forward_demodulation,[],[f9801,f353])).

fof(f9801,plain,(
    ! [X16] : k5_xboole_0(k5_xboole_0(X16,X16),k2_xboole_0(k5_xboole_0(X16,X16),X16)) = k2_xboole_0(k4_xboole_0(k5_xboole_0(X16,X16),k2_xboole_0(X16,k5_xboole_0(X16,X16))),k3_xboole_0(X16,X16)) ),
    inference(forward_demodulation,[],[f9568,f1479])).

fof(f9568,plain,(
    ! [X16] : k5_xboole_0(k5_xboole_0(X16,X16),k2_xboole_0(k5_xboole_0(X16,X16),X16)) = k2_xboole_0(k4_xboole_0(k5_xboole_0(X16,X16),k2_xboole_0(k5_xboole_0(X16,X16),X16)),k3_xboole_0(X16,X16)) ),
    inference(superposition,[],[f46,f3059])).

fof(f46,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X1,X2)),k4_xboole_0(X2,X1)) ),
    inference(superposition,[],[f18,f21])).

fof(f9080,plain,(
    ! [X17] : k2_xboole_0(X17,k5_xboole_0(X17,X17)) = k5_xboole_0(k5_xboole_0(X17,X17),k2_xboole_0(X17,k5_xboole_0(X17,X17))) ),
    inference(forward_demodulation,[],[f8993,f7763])).

fof(f7763,plain,(
    ! [X8,X9] : k2_xboole_0(X9,X8) = k5_xboole_0(k4_xboole_0(X8,X9),k2_xboole_0(X9,X9)) ),
    inference(backward_demodulation,[],[f329,f7758])).

fof(f329,plain,(
    ! [X8,X9] : k2_xboole_0(k2_xboole_0(X9,X9),X8) = k5_xboole_0(k4_xboole_0(X8,X9),k2_xboole_0(X9,X9)) ),
    inference(superposition,[],[f109,f100])).

fof(f8993,plain,(
    ! [X17] : k5_xboole_0(k5_xboole_0(X17,X17),k2_xboole_0(X17,k5_xboole_0(X17,X17))) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X17,X17),X17),k2_xboole_0(X17,X17)) ),
    inference(superposition,[],[f991,f7553])).

fof(f7553,plain,(
    ! [X16] : k2_xboole_0(X16,X16) = k5_xboole_0(k5_xboole_0(X16,X16),X16) ),
    inference(forward_demodulation,[],[f7552,f15])).

fof(f7552,plain,(
    ! [X16] : k5_xboole_0(k5_xboole_0(X16,X16),X16) = k2_xboole_0(X16,k4_xboole_0(X16,X16)) ),
    inference(forward_demodulation,[],[f7551,f243])).

fof(f243,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k4_xboole_0(X6,X7)) = k2_xboole_0(k3_xboole_0(X6,X7),k4_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f226,f14])).

fof(f226,plain,(
    ! [X6,X7] : k2_xboole_0(k4_xboole_0(X6,X7),X6) = k2_xboole_0(k3_xboole_0(X6,X7),k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f211,f17])).

fof(f7551,plain,(
    ! [X16] : k5_xboole_0(k5_xboole_0(X16,X16),X16) = k2_xboole_0(k3_xboole_0(X16,X16),k4_xboole_0(X16,X16)) ),
    inference(forward_demodulation,[],[f7422,f5923])).

fof(f5923,plain,(
    ! [X16] : k4_xboole_0(X16,X16) = k4_xboole_0(k3_xboole_0(k5_xboole_0(X16,X16),k5_xboole_0(X16,X16)),X16) ),
    inference(forward_demodulation,[],[f5922,f5742])).

fof(f5742,plain,(
    ! [X12] : k4_xboole_0(k5_xboole_0(X12,k5_xboole_0(X12,X12)),k3_xboole_0(X12,X12)) = k4_xboole_0(X12,X12) ),
    inference(forward_demodulation,[],[f5741,f100])).

fof(f5741,plain,(
    ! [X12] : k4_xboole_0(k5_xboole_0(X12,k5_xboole_0(X12,X12)),k3_xboole_0(X12,X12)) = k4_xboole_0(X12,k2_xboole_0(X12,X12)) ),
    inference(forward_demodulation,[],[f5740,f282])).

fof(f5740,plain,(
    ! [X12] : k4_xboole_0(k5_xboole_0(X12,k5_xboole_0(X12,X12)),k3_xboole_0(X12,X12)) = k4_xboole_0(X12,k2_xboole_0(X12,k2_xboole_0(X12,X12))) ),
    inference(forward_demodulation,[],[f5739,f1118])).

fof(f5739,plain,(
    ! [X12] : k4_xboole_0(k5_xboole_0(X12,k5_xboole_0(X12,X12)),k3_xboole_0(X12,X12)) = k4_xboole_0(X12,k2_xboole_0(X12,k2_xboole_0(X12,k4_xboole_0(X12,X12)))) ),
    inference(forward_demodulation,[],[f5732,f4799])).

fof(f4799,plain,(
    ! [X66,X67,X65] : k4_xboole_0(k5_xboole_0(X66,X65),k2_xboole_0(X67,k4_xboole_0(X66,X65))) = k4_xboole_0(X65,k2_xboole_0(X66,k2_xboole_0(X67,k4_xboole_0(X66,X65)))) ),
    inference(forward_demodulation,[],[f4704,f20])).

fof(f4704,plain,(
    ! [X66,X67,X65] : k4_xboole_0(k4_xboole_0(X65,X66),k2_xboole_0(X67,k4_xboole_0(X66,X65))) = k4_xboole_0(k5_xboole_0(X66,X65),k2_xboole_0(X67,k4_xboole_0(X66,X65))) ),
    inference(superposition,[],[f559,f34])).

fof(f559,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k2_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X2,X0),k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f68,f14])).

fof(f5732,plain,(
    ! [X12] : k4_xboole_0(k5_xboole_0(X12,k5_xboole_0(X12,X12)),k3_xboole_0(X12,X12)) = k4_xboole_0(k5_xboole_0(X12,X12),k2_xboole_0(X12,k4_xboole_0(X12,X12))) ),
    inference(backward_demodulation,[],[f3739,f5731])).

fof(f5731,plain,(
    ! [X4,X5] : k2_xboole_0(X5,k3_xboole_0(X4,X5)) = k2_xboole_0(X5,k4_xboole_0(X5,X4)) ),
    inference(forward_demodulation,[],[f5425,f5637])).

fof(f5637,plain,(
    ! [X15,X16] : k2_xboole_0(X15,k4_xboole_0(X15,X16)) = k2_xboole_0(X15,k4_xboole_0(X16,k2_xboole_0(X15,X16))) ),
    inference(forward_demodulation,[],[f5382,f5482])).

fof(f5382,plain,(
    ! [X15,X16] : k2_xboole_0(X15,k4_xboole_0(X15,X16)) = k2_xboole_0(X15,k4_xboole_0(k3_xboole_0(X15,X16),X16)) ),
    inference(superposition,[],[f66,f353])).

fof(f5425,plain,(
    ! [X4,X5] : k2_xboole_0(X5,k3_xboole_0(X4,X5)) = k2_xboole_0(X5,k4_xboole_0(X4,k2_xboole_0(X5,X4))) ),
    inference(superposition,[],[f15,f353])).

fof(f3739,plain,(
    ! [X12] : k4_xboole_0(k5_xboole_0(X12,X12),k2_xboole_0(X12,k3_xboole_0(X12,X12))) = k4_xboole_0(k5_xboole_0(X12,k5_xboole_0(X12,X12)),k3_xboole_0(X12,X12)) ),
    inference(forward_demodulation,[],[f3704,f19])).

fof(f3704,plain,(
    ! [X12] : k4_xboole_0(k5_xboole_0(k5_xboole_0(X12,X12),X12),k3_xboole_0(X12,X12)) = k4_xboole_0(k5_xboole_0(X12,X12),k2_xboole_0(X12,k3_xboole_0(X12,X12))) ),
    inference(superposition,[],[f41,f3059])).

fof(f5922,plain,(
    ! [X16] : k4_xboole_0(k3_xboole_0(k5_xboole_0(X16,X16),k5_xboole_0(X16,X16)),X16) = k4_xboole_0(k5_xboole_0(X16,k5_xboole_0(X16,X16)),k3_xboole_0(X16,X16)) ),
    inference(forward_demodulation,[],[f5821,f19])).

fof(f5821,plain,(
    ! [X16] : k4_xboole_0(k3_xboole_0(k5_xboole_0(X16,X16),k5_xboole_0(X16,X16)),X16) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X16,X16),X16),k3_xboole_0(X16,X16)) ),
    inference(superposition,[],[f5563,f3059])).

fof(f7422,plain,(
    ! [X16] : k5_xboole_0(k5_xboole_0(X16,X16),X16) = k2_xboole_0(k3_xboole_0(X16,X16),k4_xboole_0(k3_xboole_0(k5_xboole_0(X16,X16),k5_xboole_0(X16,X16)),X16)) ),
    inference(superposition,[],[f5579,f3059])).

fof(f991,plain,(
    ! [X17,X18] : k5_xboole_0(X18,k2_xboole_0(X17,X18)) = k5_xboole_0(k4_xboole_0(X18,X17),k5_xboole_0(X18,X17)) ),
    inference(forward_demodulation,[],[f990,f688])).

fof(f688,plain,(
    ! [X15,X16] : k2_xboole_0(k4_xboole_0(X16,k2_xboole_0(X15,k5_xboole_0(X16,X15))),k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(X16,X15)))) = k5_xboole_0(X16,k2_xboole_0(X15,X16)) ),
    inference(forward_demodulation,[],[f687,f137])).

fof(f687,plain,(
    ! [X15,X16] : k2_xboole_0(k4_xboole_0(X16,k2_xboole_0(X15,k5_xboole_0(X16,X15))),k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(X16,X15)))) = k5_xboole_0(X16,k5_xboole_0(X15,k4_xboole_0(X16,X15))) ),
    inference(forward_demodulation,[],[f686,f19])).

fof(f686,plain,(
    ! [X15,X16] : k2_xboole_0(k4_xboole_0(X16,k2_xboole_0(X15,k5_xboole_0(X16,X15))),k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(X16,X15)))) = k5_xboole_0(k5_xboole_0(X16,X15),k4_xboole_0(X16,X15)) ),
    inference(forward_demodulation,[],[f685,f121])).

fof(f685,plain,(
    ! [X15,X16] : k5_xboole_0(k4_xboole_0(X16,X15),k5_xboole_0(X16,X15)) = k2_xboole_0(k4_xboole_0(X16,k2_xboole_0(X15,k5_xboole_0(X16,X15))),k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(X16,X15)))) ),
    inference(forward_demodulation,[],[f684,f20])).

fof(f684,plain,(
    ! [X15,X16] : k5_xboole_0(k4_xboole_0(X16,X15),k5_xboole_0(X16,X15)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X16,X15),k5_xboole_0(X16,X15)),k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(X16,X15)))) ),
    inference(forward_demodulation,[],[f639,f20])).

fof(f639,plain,(
    ! [X15,X16] : k5_xboole_0(k4_xboole_0(X16,X15),k5_xboole_0(X16,X15)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X16,X15),k5_xboole_0(X16,X15)),k4_xboole_0(k4_xboole_0(X15,X16),k4_xboole_0(X16,X15))) ),
    inference(superposition,[],[f32,f34])).

fof(f990,plain,(
    ! [X17,X18] : k5_xboole_0(k4_xboole_0(X18,X17),k5_xboole_0(X18,X17)) = k2_xboole_0(k4_xboole_0(X18,k2_xboole_0(X17,k5_xboole_0(X18,X17))),k4_xboole_0(X17,k2_xboole_0(X18,k4_xboole_0(X18,X17)))) ),
    inference(forward_demodulation,[],[f989,f86])).

fof(f989,plain,(
    ! [X17,X18] : k5_xboole_0(k4_xboole_0(X18,X17),k2_xboole_0(k5_xboole_0(X17,X18),k4_xboole_0(X18,X17))) = k2_xboole_0(k4_xboole_0(X18,k2_xboole_0(X17,k2_xboole_0(k5_xboole_0(X17,X18),k4_xboole_0(X18,X17)))),k4_xboole_0(X17,k2_xboole_0(X18,k4_xboole_0(X18,X17)))) ),
    inference(forward_demodulation,[],[f931,f20])).

fof(f931,plain,(
    ! [X17,X18] : k5_xboole_0(k4_xboole_0(X18,X17),k2_xboole_0(k5_xboole_0(X17,X18),k4_xboole_0(X18,X17))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X18,X17),k2_xboole_0(k5_xboole_0(X17,X18),k4_xboole_0(X18,X17))),k4_xboole_0(X17,k2_xboole_0(X18,k4_xboole_0(X18,X17)))) ),
    inference(superposition,[],[f32,f41])).

fof(f307,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f306,f211])).

fof(f306,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f305,f15])).

fof(f305,plain,(
    ! [X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f289,f193])).

fof(f289,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X1),X1)) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f29,f16])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f28,f14])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f15,f17])).

fof(f1068,plain,(
    ! [X6,X8,X7,X9] : k4_xboole_0(X9,k2_xboole_0(X6,k2_xboole_0(X7,X8))) = k4_xboole_0(X9,k2_xboole_0(X8,k2_xboole_0(X6,X7))) ),
    inference(superposition,[],[f71,f14])).

fof(f31103,plain,(
    ! [X30,X31] : k5_xboole_0(k4_xboole_0(X30,X31),k2_xboole_0(X30,k5_xboole_0(X31,X31))) = k2_xboole_0(k4_xboole_0(X30,k2_xboole_0(X31,k2_xboole_0(X30,k5_xboole_0(X31,X31)))),k3_xboole_0(X30,X31)) ),
    inference(forward_demodulation,[],[f31102,f20])).

fof(f31102,plain,(
    ! [X30,X31] : k5_xboole_0(k4_xboole_0(X30,X31),k2_xboole_0(X30,k5_xboole_0(X31,X31))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X30,X31),k2_xboole_0(X30,k5_xboole_0(X31,X31))),k3_xboole_0(X30,X31)) ),
    inference(forward_demodulation,[],[f30877,f17])).

fof(f30877,plain,(
    ! [X30,X31] : k5_xboole_0(k4_xboole_0(X30,X31),k2_xboole_0(X30,k5_xboole_0(X31,X31))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X30,X31),k2_xboole_0(X30,k5_xboole_0(X31,X31))),k4_xboole_0(X30,k4_xboole_0(X30,X31))) ),
    inference(superposition,[],[f32,f13571])).

fof(f13571,plain,(
    ! [X35,X36] : k2_xboole_0(X35,k4_xboole_0(X35,X36)) = k2_xboole_0(X35,k5_xboole_0(X36,X36)) ),
    inference(forward_demodulation,[],[f13570,f100])).

fof(f13570,plain,(
    ! [X35,X36] : k2_xboole_0(X35,k5_xboole_0(X36,X36)) = k2_xboole_0(X35,k4_xboole_0(X35,k2_xboole_0(X36,X36))) ),
    inference(forward_demodulation,[],[f13569,f20])).

fof(f13569,plain,(
    ! [X35,X36] : k2_xboole_0(X35,k4_xboole_0(k4_xboole_0(X35,X36),X36)) = k2_xboole_0(X35,k5_xboole_0(X36,X36)) ),
    inference(forward_demodulation,[],[f13568,f12336])).

fof(f12336,plain,(
    ! [X21,X20] : k2_xboole_0(X21,k5_xboole_0(X20,X20)) = k2_xboole_0(X21,k4_xboole_0(X20,X20)) ),
    inference(superposition,[],[f9458,f34])).

fof(f9458,plain,(
    ! [X35,X34] : k2_xboole_0(X35,X34) = k2_xboole_0(X35,k2_xboole_0(X34,X34)) ),
    inference(forward_demodulation,[],[f9363,f25])).

fof(f9363,plain,(
    ! [X35,X34] : k2_xboole_0(X35,k2_xboole_0(X34,X34)) = k2_xboole_0(X35,k2_xboole_0(X34,X35)) ),
    inference(superposition,[],[f25,f7758])).

fof(f13568,plain,(
    ! [X35,X36] : k2_xboole_0(X35,k4_xboole_0(k4_xboole_0(X35,X36),X36)) = k2_xboole_0(X35,k4_xboole_0(X36,X36)) ),
    inference(forward_demodulation,[],[f13474,f4001])).

fof(f4001,plain,(
    ! [X14,X12,X13] : k2_xboole_0(X13,k4_xboole_0(k2_xboole_0(X12,X13),X14)) = k2_xboole_0(X13,k4_xboole_0(X12,X14)) ),
    inference(forward_demodulation,[],[f3945,f419])).

fof(f3945,plain,(
    ! [X14,X12,X13] : k2_xboole_0(X13,k4_xboole_0(X12,k2_xboole_0(X13,X14))) = k2_xboole_0(X13,k4_xboole_0(k2_xboole_0(X12,X13),X14)) ),
    inference(superposition,[],[f419,f68])).

fof(f13474,plain,(
    ! [X35,X36] : k2_xboole_0(X35,k4_xboole_0(k4_xboole_0(X35,X36),X36)) = k2_xboole_0(X35,k4_xboole_0(k2_xboole_0(X36,X35),X36)) ),
    inference(superposition,[],[f463,f82])).

fof(f463,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1)) ),
    inference(forward_demodulation,[],[f429,f66])).

fof(f429,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f66,f16])).

fof(f30935,plain,(
    ! [X187,X186] : k3_xboole_0(X186,k4_xboole_0(X186,X187)) = k4_xboole_0(X186,k5_xboole_0(k4_xboole_0(X186,X187),k2_xboole_0(X186,k5_xboole_0(X187,X187)))) ),
    inference(superposition,[],[f5513,f13571])).

fof(f5513,plain,(
    ! [X41,X40] : k3_xboole_0(X41,X40) = k4_xboole_0(X41,k5_xboole_0(X40,k2_xboole_0(X41,X40))) ),
    inference(backward_demodulation,[],[f3548,f5493])).

fof(f5493,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X5,k2_xboole_0(X4,X5))) ),
    inference(backward_demodulation,[],[f4407,f5482])).

fof(f4407,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(k3_xboole_0(X4,X5),X5)) ),
    inference(superposition,[],[f97,f4152])).

fof(f4152,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X1) ),
    inference(superposition,[],[f507,f97])).

fof(f507,plain,(
    ! [X10,X11,X9] : k4_xboole_0(k3_xboole_0(X9,X11),k4_xboole_0(X9,X10)) = k3_xboole_0(k3_xboole_0(X9,X10),X11) ),
    inference(superposition,[],[f443,f17])).

fof(f3548,plain,(
    ! [X41,X40] : k4_xboole_0(k3_xboole_0(X41,X40),k4_xboole_0(X40,k2_xboole_0(X41,X40))) = k4_xboole_0(X41,k5_xboole_0(X40,k2_xboole_0(X41,X40))) ),
    inference(superposition,[],[f355,f32])).

fof(f1273,plain,(
    ! [X0,X1] : k4_xboole_0(k3_xboole_0(X0,k2_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[],[f60,f134])).

fof(f32477,plain,(
    ! [X78,X77] : k4_xboole_0(k2_xboole_0(X77,k4_xboole_0(X77,X78)),k3_xboole_0(X77,X78)) = k4_xboole_0(k3_xboole_0(X77,k2_xboole_0(X78,X77)),k3_xboole_0(X77,X78)) ),
    inference(forward_demodulation,[],[f32476,f25429])).

fof(f25429,plain,(
    ! [X70,X69] : k3_xboole_0(X69,k2_xboole_0(X70,X69)) = k3_xboole_0(k2_xboole_0(X69,k4_xboole_0(X69,X70)),k2_xboole_0(X69,k4_xboole_0(X69,X70))) ),
    inference(forward_demodulation,[],[f25428,f17])).

fof(f25428,plain,(
    ! [X70,X69] : k3_xboole_0(k2_xboole_0(X69,k4_xboole_0(X69,X70)),k2_xboole_0(X69,k4_xboole_0(X69,X70))) = k4_xboole_0(X69,k4_xboole_0(X69,k2_xboole_0(X70,X69))) ),
    inference(forward_demodulation,[],[f25396,f182])).

fof(f182,plain,(
    ! [X10,X8,X9] : k4_xboole_0(X10,k4_xboole_0(X8,k2_xboole_0(X9,X10))) = k4_xboole_0(k2_xboole_0(X10,k4_xboole_0(X8,X9)),k4_xboole_0(X8,k2_xboole_0(X9,X10))) ),
    inference(superposition,[],[f23,f20])).

fof(f25396,plain,(
    ! [X70,X69] : k3_xboole_0(k2_xboole_0(X69,k4_xboole_0(X69,X70)),k2_xboole_0(X69,k4_xboole_0(X69,X70))) = k4_xboole_0(k2_xboole_0(X69,k4_xboole_0(X69,X70)),k4_xboole_0(X69,k2_xboole_0(X70,X69))) ),
    inference(backward_demodulation,[],[f11862,f25363])).

fof(f25363,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k2_xboole_0(X7,X6)) = k4_xboole_0(k3_xboole_0(X6,X7),X6) ),
    inference(backward_demodulation,[],[f383,f25362])).

fof(f25362,plain,(
    ! [X30,X31] : k4_xboole_0(k3_xboole_0(X30,X31),k3_xboole_0(X30,X31)) = k4_xboole_0(X30,k2_xboole_0(X31,X30)) ),
    inference(forward_demodulation,[],[f25361,f17471])).

fof(f17471,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k2_xboole_0(X16,X15)) = k4_xboole_0(k4_xboole_0(X15,X16),k2_xboole_0(X15,k4_xboole_0(X15,X16))) ),
    inference(forward_demodulation,[],[f17470,f5927])).

fof(f5927,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k2_xboole_0(X7,X6)) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X6,X7)),k3_xboole_0(X6,X7)) ),
    inference(backward_demodulation,[],[f3134,f5925])).

fof(f5925,plain,(
    ! [X19,X20] : k4_xboole_0(X20,k2_xboole_0(X19,X20)) = k4_xboole_0(k3_xboole_0(X20,X20),k2_xboole_0(X19,X20)) ),
    inference(forward_demodulation,[],[f5823,f734])).

fof(f734,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k2_xboole_0(X7,X6)) = k4_xboole_0(k5_xboole_0(X6,k2_xboole_0(X7,X6)),k4_xboole_0(X7,X6)) ),
    inference(forward_demodulation,[],[f733,f25])).

fof(f733,plain,(
    ! [X6,X7] : k4_xboole_0(k5_xboole_0(X6,k2_xboole_0(X7,X6)),k4_xboole_0(X7,X6)) = k4_xboole_0(X6,k2_xboole_0(X7,k2_xboole_0(X6,X7))) ),
    inference(forward_demodulation,[],[f732,f15])).

fof(f732,plain,(
    ! [X6,X7] : k4_xboole_0(k5_xboole_0(X6,k2_xboole_0(X7,X6)),k4_xboole_0(X7,X6)) = k4_xboole_0(X6,k2_xboole_0(X7,k2_xboole_0(X6,k4_xboole_0(X7,X6)))) ),
    inference(forward_demodulation,[],[f731,f71])).

fof(f731,plain,(
    ! [X6,X7] : k4_xboole_0(k5_xboole_0(X6,k2_xboole_0(X7,X6)),k4_xboole_0(X7,X6)) = k4_xboole_0(X6,k2_xboole_0(k2_xboole_0(X7,X6),k4_xboole_0(X7,X6))) ),
    inference(forward_demodulation,[],[f663,f20])).

fof(f663,plain,(
    ! [X6,X7] : k4_xboole_0(k4_xboole_0(X6,k2_xboole_0(X7,X6)),k4_xboole_0(X7,X6)) = k4_xboole_0(k5_xboole_0(X6,k2_xboole_0(X7,X6)),k4_xboole_0(X7,X6)) ),
    inference(superposition,[],[f16,f32])).

fof(f5823,plain,(
    ! [X19,X20] : k4_xboole_0(k3_xboole_0(X20,X20),k2_xboole_0(X19,X20)) = k4_xboole_0(k5_xboole_0(X20,k2_xboole_0(X19,X20)),k4_xboole_0(X19,X20)) ),
    inference(superposition,[],[f5563,f16])).

fof(f3134,plain,(
    ! [X6,X7] : k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X6,X7)),k3_xboole_0(X6,X7)) = k4_xboole_0(k3_xboole_0(X6,X6),k2_xboole_0(X7,X6)) ),
    inference(backward_demodulation,[],[f863,f3132])).

fof(f3132,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k2_xboole_0(X36,k2_xboole_0(X35,k3_xboole_0(X35,X36)))) = k4_xboole_0(k3_xboole_0(X35,X35),k2_xboole_0(X36,X35)) ),
    inference(forward_demodulation,[],[f3131,f20])).

fof(f3131,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k2_xboole_0(X36,k2_xboole_0(X35,k3_xboole_0(X35,X36)))) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X35,X35),X36),X35) ),
    inference(forward_demodulation,[],[f3130,f443])).

fof(f3130,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k2_xboole_0(X36,k2_xboole_0(X35,k3_xboole_0(X35,X36)))) = k4_xboole_0(k3_xboole_0(k4_xboole_0(X35,X36),X35),X35) ),
    inference(forward_demodulation,[],[f3129,f353])).

fof(f3129,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k2_xboole_0(X36,k2_xboole_0(X35,k3_xboole_0(X35,X36)))) = k4_xboole_0(k4_xboole_0(X35,X36),k2_xboole_0(X35,k4_xboole_0(X35,X36))) ),
    inference(forward_demodulation,[],[f3128,f416])).

fof(f416,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k4_xboole_0(X6,X7)) = k5_xboole_0(k4_xboole_0(X6,X7),k3_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f404,f14])).

fof(f404,plain,(
    ! [X6,X7] : k2_xboole_0(k4_xboole_0(X6,X7),X6) = k5_xboole_0(k4_xboole_0(X6,X7),k3_xboole_0(X6,X7)) ),
    inference(superposition,[],[f137,f17])).

fof(f3128,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k2_xboole_0(X36,k2_xboole_0(X35,k3_xboole_0(X35,X36)))) = k4_xboole_0(k4_xboole_0(X35,X36),k5_xboole_0(k4_xboole_0(X35,X36),k3_xboole_0(X35,X36))) ),
    inference(forward_demodulation,[],[f3127,f121])).

fof(f3127,plain,(
    ! [X35,X36] : k4_xboole_0(k4_xboole_0(X35,X36),k5_xboole_0(k3_xboole_0(X35,X36),k4_xboole_0(X35,X36))) = k4_xboole_0(X35,k2_xboole_0(X36,k2_xboole_0(X35,k3_xboole_0(X35,X36)))) ),
    inference(forward_demodulation,[],[f3126,f1108])).

fof(f1108,plain,(
    ! [X10,X8,X11,X9] : k4_xboole_0(X10,k2_xboole_0(X8,k2_xboole_0(k4_xboole_0(X9,X8),X11))) = k4_xboole_0(X10,k2_xboole_0(X8,k2_xboole_0(X9,X11))) ),
    inference(forward_demodulation,[],[f1053,f71])).

fof(f1053,plain,(
    ! [X10,X8,X11,X9] : k4_xboole_0(X10,k2_xboole_0(X8,k2_xboole_0(k4_xboole_0(X9,X8),X11))) = k4_xboole_0(X10,k2_xboole_0(k2_xboole_0(X8,X9),X11)) ),
    inference(superposition,[],[f71,f15])).

fof(f3126,plain,(
    ! [X35,X36] : k4_xboole_0(k4_xboole_0(X35,X36),k5_xboole_0(k3_xboole_0(X35,X36),k4_xboole_0(X35,X36))) = k4_xboole_0(X35,k2_xboole_0(X36,k2_xboole_0(k4_xboole_0(X35,X36),k3_xboole_0(X35,X36)))) ),
    inference(forward_demodulation,[],[f3125,f20])).

fof(f3125,plain,(
    ! [X35,X36] : k4_xboole_0(k4_xboole_0(X35,X36),k5_xboole_0(k3_xboole_0(X35,X36),k4_xboole_0(X35,X36))) = k4_xboole_0(k4_xboole_0(X35,X36),k2_xboole_0(k4_xboole_0(X35,X36),k3_xboole_0(X35,X36))) ),
    inference(forward_demodulation,[],[f3124,f1479])).

fof(f3124,plain,(
    ! [X35,X36] : k4_xboole_0(k4_xboole_0(X35,X36),k5_xboole_0(k3_xboole_0(X35,X36),k4_xboole_0(X35,X36))) = k4_xboole_0(k4_xboole_0(X35,X36),k2_xboole_0(k3_xboole_0(X35,X36),k4_xboole_0(X35,X36))) ),
    inference(forward_demodulation,[],[f3057,f353])).

fof(f3057,plain,(
    ! [X35,X36] : k4_xboole_0(k4_xboole_0(X35,X36),k5_xboole_0(k3_xboole_0(X35,X36),k4_xboole_0(X35,X36))) = k4_xboole_0(k3_xboole_0(k4_xboole_0(X35,X36),k3_xboole_0(X35,X36)),k3_xboole_0(X35,X36)) ),
    inference(superposition,[],[f351,f97])).

fof(f863,plain,(
    ! [X6,X7] : k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X6,X7)),k3_xboole_0(X6,X7)) = k4_xboole_0(X6,k2_xboole_0(X7,k2_xboole_0(X6,k3_xboole_0(X6,X7)))) ),
    inference(forward_demodulation,[],[f862,f71])).

fof(f862,plain,(
    ! [X6,X7] : k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X6,X7)),k3_xboole_0(X6,X7)) = k4_xboole_0(X6,k2_xboole_0(k2_xboole_0(X7,X6),k3_xboole_0(X6,X7))) ),
    inference(forward_demodulation,[],[f788,f20])).

fof(f788,plain,(
    ! [X6,X7] : k4_xboole_0(k4_xboole_0(X6,k2_xboole_0(X7,X6)),k3_xboole_0(X6,X7)) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X6,X7)),k3_xboole_0(X6,X7)) ),
    inference(superposition,[],[f21,f39])).

fof(f17470,plain,(
    ! [X15,X16] : k4_xboole_0(k4_xboole_0(X15,X16),k2_xboole_0(X15,k4_xboole_0(X15,X16))) = k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X15,X16)),k3_xboole_0(X15,X16)) ),
    inference(forward_demodulation,[],[f17153,f5552])).

fof(f5552,plain,(
    ! [X21,X22] : k5_xboole_0(k4_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))) = k5_xboole_0(X21,k4_xboole_0(X21,X22)) ),
    inference(backward_demodulation,[],[f5491,f5550])).

fof(f5550,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X3,k2_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f5376,f5482])).

fof(f5376,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X2,X3),X3)) ),
    inference(superposition,[],[f39,f353])).

fof(f5491,plain,(
    ! [X21,X22] : k5_xboole_0(k4_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))) = k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X22,k2_xboole_0(X21,X22))) ),
    inference(backward_demodulation,[],[f2755,f5482])).

fof(f2755,plain,(
    ! [X21,X22] : k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(k3_xboole_0(X21,X22),X22)) = k5_xboole_0(k4_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))) ),
    inference(forward_demodulation,[],[f2754,f29])).

fof(f2754,plain,(
    ! [X21,X22] : k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(k3_xboole_0(X21,X22),X22)) = k5_xboole_0(k4_xboole_0(X21,X22),k2_xboole_0(k4_xboole_0(X21,X22),k3_xboole_0(X21,X22))) ),
    inference(forward_demodulation,[],[f2753,f14])).

fof(f2753,plain,(
    ! [X21,X22] : k5_xboole_0(k4_xboole_0(X21,X22),k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,X22))) = k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(k3_xboole_0(X21,X22),X22)) ),
    inference(forward_demodulation,[],[f2752,f355])).

fof(f2752,plain,(
    ! [X21,X22] : k5_xboole_0(k4_xboole_0(X21,X22),k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,X22))) = k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,k2_xboole_0(X22,k4_xboole_0(X21,X22)))) ),
    inference(forward_demodulation,[],[f2751,f20])).

fof(f2751,plain,(
    ! [X21,X22] : k5_xboole_0(k4_xboole_0(X21,X22),k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,X22))) = k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(k4_xboole_0(X21,X22),k4_xboole_0(X21,X22))) ),
    inference(forward_demodulation,[],[f2750,f227])).

fof(f227,plain,(
    ! [X10,X8,X9] : k2_xboole_0(X10,k4_xboole_0(X8,X9)) = k2_xboole_0(k4_xboole_0(X8,k2_xboole_0(X9,X10)),X10) ),
    inference(superposition,[],[f211,f20])).

fof(f2750,plain,(
    ! [X21,X22] : k5_xboole_0(k4_xboole_0(X21,X22),k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,X22))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X21,X22),k2_xboole_0(k4_xboole_0(X21,X22),k3_xboole_0(X21,X22))),k3_xboole_0(X21,X22)) ),
    inference(forward_demodulation,[],[f2697,f1479])).

fof(f2697,plain,(
    ! [X21,X22] : k5_xboole_0(k4_xboole_0(X21,X22),k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,X22))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X21,X22),k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,X22))),k3_xboole_0(X21,X22)) ),
    inference(superposition,[],[f32,f97])).

fof(f17153,plain,(
    ! [X15,X16] : k4_xboole_0(k4_xboole_0(X15,X16),k2_xboole_0(X15,k4_xboole_0(X15,X16))) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X15,X16),k2_xboole_0(X15,k4_xboole_0(X15,X16))),k3_xboole_0(X15,X16)) ),
    inference(superposition,[],[f734,f17])).

fof(f25361,plain,(
    ! [X30,X31] : k4_xboole_0(k3_xboole_0(X30,X31),k3_xboole_0(X30,X31)) = k4_xboole_0(k4_xboole_0(X30,X31),k2_xboole_0(X30,k4_xboole_0(X30,X31))) ),
    inference(forward_demodulation,[],[f25360,f29])).

fof(f25360,plain,(
    ! [X30,X31] : k4_xboole_0(k3_xboole_0(X30,X31),k3_xboole_0(X30,X31)) = k4_xboole_0(k4_xboole_0(X30,X31),k2_xboole_0(k4_xboole_0(X30,X31),k3_xboole_0(X30,X31))) ),
    inference(forward_demodulation,[],[f25111,f14])).

fof(f25111,plain,(
    ! [X30,X31] : k4_xboole_0(k3_xboole_0(X30,X31),k3_xboole_0(X30,X31)) = k4_xboole_0(k4_xboole_0(X30,X31),k2_xboole_0(k3_xboole_0(X30,X31),k4_xboole_0(X30,X31))) ),
    inference(superposition,[],[f4741,f385])).

fof(f385,plain,(
    ! [X19,X17,X18] : k4_xboole_0(k3_xboole_0(X17,X18),k2_xboole_0(X19,k4_xboole_0(X17,X18))) = k4_xboole_0(k3_xboole_0(X17,X18),X19) ),
    inference(forward_demodulation,[],[f358,f60])).

fof(f358,plain,(
    ! [X19,X17,X18] : k4_xboole_0(k3_xboole_0(X17,X18),k2_xboole_0(X19,k4_xboole_0(X17,X18))) = k4_xboole_0(X17,k2_xboole_0(k4_xboole_0(X17,X18),X19)) ),
    inference(superposition,[],[f60,f25])).

fof(f4741,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(X3,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f559,f69])).

fof(f383,plain,(
    ! [X6,X7] : k4_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X7)) = k4_xboole_0(k3_xboole_0(X6,X7),X6) ),
    inference(backward_demodulation,[],[f354,f355])).

fof(f354,plain,(
    ! [X6,X7] : k4_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X7)) = k4_xboole_0(X6,k2_xboole_0(X6,k4_xboole_0(X6,X7))) ),
    inference(superposition,[],[f60,f29])).

fof(f11862,plain,(
    ! [X70,X69] : k3_xboole_0(k2_xboole_0(X69,k4_xboole_0(X69,X70)),k2_xboole_0(X69,k4_xboole_0(X69,X70))) = k4_xboole_0(k2_xboole_0(X69,k4_xboole_0(X69,X70)),k4_xboole_0(k3_xboole_0(X69,X70),X69)) ),
    inference(forward_demodulation,[],[f11721,f385])).

fof(f11721,plain,(
    ! [X70,X69] : k4_xboole_0(k2_xboole_0(X69,k4_xboole_0(X69,X70)),k4_xboole_0(k3_xboole_0(X69,X70),k2_xboole_0(X69,k4_xboole_0(X69,X70)))) = k3_xboole_0(k2_xboole_0(X69,k4_xboole_0(X69,X70)),k2_xboole_0(X69,k4_xboole_0(X69,X70))) ),
    inference(superposition,[],[f193,f323])).

fof(f323,plain,(
    ! [X10,X11] : k2_xboole_0(X10,k4_xboole_0(X10,X11)) = k2_xboole_0(k3_xboole_0(X10,X11),k2_xboole_0(X10,k4_xboole_0(X10,X11))) ),
    inference(forward_demodulation,[],[f322,f29])).

fof(f322,plain,(
    ! [X10,X11] : k2_xboole_0(k4_xboole_0(X10,X11),k3_xboole_0(X10,X11)) = k2_xboole_0(k3_xboole_0(X10,X11),k2_xboole_0(X10,k4_xboole_0(X10,X11))) ),
    inference(forward_demodulation,[],[f301,f14])).

fof(f301,plain,(
    ! [X10,X11] : k2_xboole_0(k3_xboole_0(X10,X11),k4_xboole_0(X10,X11)) = k2_xboole_0(k3_xboole_0(X10,X11),k2_xboole_0(X10,k4_xboole_0(X10,X11))) ),
    inference(superposition,[],[f25,f29])).

fof(f32476,plain,(
    ! [X78,X77] : k4_xboole_0(k2_xboole_0(X77,k4_xboole_0(X77,X78)),k3_xboole_0(X77,X78)) = k4_xboole_0(k3_xboole_0(k2_xboole_0(X77,k4_xboole_0(X77,X78)),k2_xboole_0(X77,k4_xboole_0(X77,X78))),k3_xboole_0(X77,X78)) ),
    inference(forward_demodulation,[],[f32475,f14])).

fof(f32475,plain,(
    ! [X78,X77] : k4_xboole_0(k3_xboole_0(k2_xboole_0(X77,k4_xboole_0(X77,X78)),k2_xboole_0(X77,k4_xboole_0(X77,X78))),k3_xboole_0(X77,X78)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X77,X78),X77),k3_xboole_0(X77,X78)) ),
    inference(forward_demodulation,[],[f32474,f29014])).

fof(f29014,plain,(
    ! [X10,X8,X9] : k2_xboole_0(k4_xboole_0(X8,X9),X10) = k2_xboole_0(k2_xboole_0(X10,k4_xboole_0(X8,X9)),k4_xboole_0(k3_xboole_0(X8,X8),X9)) ),
    inference(forward_demodulation,[],[f28776,f1589])).

fof(f28776,plain,(
    ! [X10,X8,X9] : k2_xboole_0(k4_xboole_0(X8,X9),X10) = k2_xboole_0(k2_xboole_0(X10,k4_xboole_0(X8,X9)),k4_xboole_0(k3_xboole_0(X8,k4_xboole_0(X8,X9)),X9)) ),
    inference(superposition,[],[f8440,f443])).

fof(f8440,plain,(
    ! [X19,X20] : k2_xboole_0(X19,X20) = k2_xboole_0(k2_xboole_0(X20,X19),k3_xboole_0(X19,X19)) ),
    inference(forward_demodulation,[],[f8439,f25])).

fof(f8439,plain,(
    ! [X19,X20] : k2_xboole_0(k2_xboole_0(X20,X19),k3_xboole_0(X19,X19)) = k2_xboole_0(X19,k2_xboole_0(X20,X19)) ),
    inference(forward_demodulation,[],[f8438,f14])).

fof(f8438,plain,(
    ! [X19,X20] : k2_xboole_0(k2_xboole_0(X20,X19),k3_xboole_0(X19,X19)) = k2_xboole_0(k2_xboole_0(X20,X19),X19) ),
    inference(forward_demodulation,[],[f8313,f15])).

fof(f8313,plain,(
    ! [X19,X20] : k2_xboole_0(k2_xboole_0(X20,X19),k3_xboole_0(X19,X19)) = k2_xboole_0(k2_xboole_0(X20,X19),k4_xboole_0(X19,k2_xboole_0(X20,X19))) ),
    inference(superposition,[],[f15,f5925])).

fof(f32474,plain,(
    ! [X78,X77] : k4_xboole_0(k3_xboole_0(k2_xboole_0(X77,k4_xboole_0(X77,X78)),k2_xboole_0(X77,k4_xboole_0(X77,X78))),k3_xboole_0(X77,X78)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X77,k4_xboole_0(X77,X78)),k4_xboole_0(k3_xboole_0(X77,X77),X78)),k3_xboole_0(X77,X78)) ),
    inference(forward_demodulation,[],[f32269,f6468])).

fof(f6468,plain,(
    ! [X17,X16] : k3_xboole_0(X16,X17) = k3_xboole_0(k2_xboole_0(X16,k4_xboole_0(X16,X17)),k3_xboole_0(X16,X17)) ),
    inference(backward_demodulation,[],[f5618,f6466])).

fof(f6466,plain,(
    ! [X62,X63] : k3_xboole_0(X62,X63) = k4_xboole_0(k3_xboole_0(X62,X63),k4_xboole_0(k3_xboole_0(X62,X62),X63)) ),
    inference(forward_demodulation,[],[f6465,f1589])).

fof(f6465,plain,(
    ! [X62,X63] : k3_xboole_0(X62,X63) = k4_xboole_0(k3_xboole_0(X62,X63),k4_xboole_0(k3_xboole_0(X62,k4_xboole_0(X62,X63)),X63)) ),
    inference(forward_demodulation,[],[f6464,f443])).

fof(f6464,plain,(
    ! [X62,X63] : k3_xboole_0(X62,X63) = k4_xboole_0(k3_xboole_0(X62,X63),k3_xboole_0(k4_xboole_0(X62,X63),k4_xboole_0(X62,X63))) ),
    inference(forward_demodulation,[],[f6463,f97])).

fof(f6463,plain,(
    ! [X62,X63] : k4_xboole_0(k3_xboole_0(X62,X63),k3_xboole_0(k4_xboole_0(X62,X63),k4_xboole_0(X62,X63))) = k4_xboole_0(k3_xboole_0(X62,X63),k4_xboole_0(X62,X63)) ),
    inference(forward_demodulation,[],[f6407,f60])).

fof(f6407,plain,(
    ! [X62,X63] : k4_xboole_0(k3_xboole_0(X62,X63),k3_xboole_0(k4_xboole_0(X62,X63),k4_xboole_0(X62,X63))) = k4_xboole_0(X62,k2_xboole_0(k4_xboole_0(X62,X63),k4_xboole_0(X62,X63))) ),
    inference(superposition,[],[f60,f6160])).

fof(f6160,plain,(
    ! [X23] : k2_xboole_0(X23,X23) = k2_xboole_0(X23,k3_xboole_0(X23,X23)) ),
    inference(forward_demodulation,[],[f6101,f109])).

fof(f6101,plain,(
    ! [X23] : k2_xboole_0(X23,k3_xboole_0(X23,X23)) = k5_xboole_0(k4_xboole_0(X23,X23),X23) ),
    inference(superposition,[],[f109,f5896])).

fof(f5618,plain,(
    ! [X17,X16] : k3_xboole_0(k2_xboole_0(X16,k4_xboole_0(X16,X17)),k3_xboole_0(X16,X17)) = k4_xboole_0(k3_xboole_0(X16,X17),k4_xboole_0(k3_xboole_0(X16,X16),X17)) ),
    inference(backward_demodulation,[],[f5511,f5562])).

fof(f5511,plain,(
    ! [X17,X16] : k3_xboole_0(k2_xboole_0(X16,k4_xboole_0(X16,X17)),k3_xboole_0(X16,X17)) = k4_xboole_0(k3_xboole_0(X16,X17),k4_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X17,X16)))) ),
    inference(backward_demodulation,[],[f324,f5507])).

fof(f5507,plain,(
    ! [X12,X11] : k4_xboole_0(X11,k2_xboole_0(X12,k3_xboole_0(X11,X12))) = k4_xboole_0(X11,k2_xboole_0(X12,k4_xboole_0(X12,X11))) ),
    inference(forward_demodulation,[],[f5485,f2872])).

fof(f5485,plain,(
    ! [X12,X11] : k4_xboole_0(X11,k2_xboole_0(X12,k3_xboole_0(X11,X12))) = k4_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X12,k2_xboole_0(X11,X12))) ),
    inference(backward_demodulation,[],[f459,f5482])).

fof(f459,plain,(
    ! [X12,X11] : k4_xboole_0(X11,k2_xboole_0(X12,k3_xboole_0(X11,X12))) = k4_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(k3_xboole_0(X11,X12),X12)) ),
    inference(forward_demodulation,[],[f458,f443])).

fof(f458,plain,(
    ! [X12,X11] : k4_xboole_0(k4_xboole_0(X11,X12),k3_xboole_0(k4_xboole_0(X11,X12),X12)) = k4_xboole_0(X11,k2_xboole_0(X12,k3_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f457,f14])).

fof(f457,plain,(
    ! [X12,X11] : k4_xboole_0(k4_xboole_0(X11,X12),k3_xboole_0(k4_xboole_0(X11,X12),X12)) = k4_xboole_0(X11,k2_xboole_0(k3_xboole_0(X11,X12),X12)) ),
    inference(forward_demodulation,[],[f456,f20])).

fof(f456,plain,(
    ! [X12,X11] : k4_xboole_0(k4_xboole_0(X11,X12),k3_xboole_0(k4_xboole_0(X11,X12),X12)) = k4_xboole_0(k4_xboole_0(X11,k3_xboole_0(X11,X12)),X12) ),
    inference(forward_demodulation,[],[f449,f27])).

fof(f449,plain,(
    ! [X12,X11] : k4_xboole_0(k4_xboole_0(X11,X12),k3_xboole_0(k4_xboole_0(X11,X12),X12)) = k4_xboole_0(k3_xboole_0(X11,k4_xboole_0(X11,X12)),X12) ),
    inference(backward_demodulation,[],[f105,f443])).

fof(f105,plain,(
    ! [X12,X11] : k4_xboole_0(k4_xboole_0(X11,X12),k3_xboole_0(k4_xboole_0(X11,X12),X12)) = k3_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X12)) ),
    inference(superposition,[],[f27,f50])).

fof(f324,plain,(
    ! [X17,X16] : k3_xboole_0(k2_xboole_0(X16,k4_xboole_0(X16,X17)),k3_xboole_0(X16,X17)) = k4_xboole_0(k3_xboole_0(X16,X17),k4_xboole_0(X16,k2_xboole_0(X17,k3_xboole_0(X16,X17)))) ),
    inference(forward_demodulation,[],[f304,f20])).

fof(f304,plain,(
    ! [X17,X16] : k4_xboole_0(k3_xboole_0(X16,X17),k4_xboole_0(k4_xboole_0(X16,X17),k3_xboole_0(X16,X17))) = k3_xboole_0(k2_xboole_0(X16,k4_xboole_0(X16,X17)),k3_xboole_0(X16,X17)) ),
    inference(superposition,[],[f193,f29])).

fof(f32269,plain,(
    ! [X78,X77] : k4_xboole_0(k3_xboole_0(k2_xboole_0(X77,k4_xboole_0(X77,X78)),k2_xboole_0(X77,k4_xboole_0(X77,X78))),k3_xboole_0(X77,X78)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X77,k4_xboole_0(X77,X78)),k4_xboole_0(k3_xboole_0(X77,X77),X78)),k3_xboole_0(k2_xboole_0(X77,k4_xboole_0(X77,X78)),k3_xboole_0(X77,X78))) ),
    inference(superposition,[],[f5619,f5619])).

fof(f5619,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,k4_xboole_0(X6,X7)),k3_xboole_0(X6,X7)) = k4_xboole_0(k3_xboole_0(X6,X6),X7) ),
    inference(backward_demodulation,[],[f5512,f5562])).

fof(f5512,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k2_xboole_0(X7,k4_xboole_0(X7,X6))) = k4_xboole_0(k2_xboole_0(X6,k4_xboole_0(X6,X7)),k3_xboole_0(X6,X7)) ),
    inference(backward_demodulation,[],[f209,f5507])).

fof(f209,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,k4_xboole_0(X6,X7)),k3_xboole_0(X6,X7)) = k4_xboole_0(X6,k2_xboole_0(X7,k3_xboole_0(X6,X7))) ),
    inference(forward_demodulation,[],[f208,f20])).

fof(f208,plain,(
    ! [X6,X7] : k4_xboole_0(k4_xboole_0(X6,X7),k3_xboole_0(X6,X7)) = k4_xboole_0(k2_xboole_0(X6,k4_xboole_0(X6,X7)),k3_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f181,f14])).

fof(f181,plain,(
    ! [X6,X7] : k4_xboole_0(k4_xboole_0(X6,X7),k3_xboole_0(X6,X7)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X6,X7),X6),k3_xboole_0(X6,X7)) ),
    inference(superposition,[],[f23,f17])).

fof(f16915,plain,(
    ! [X2,X3] : k4_xboole_0(X3,k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X2,X2),X3)) ),
    inference(forward_demodulation,[],[f16914,f5482])).

fof(f16914,plain,(
    ! [X2,X3] : k4_xboole_0(k3_xboole_0(X2,X3),X3) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X2,X2),X3)) ),
    inference(forward_demodulation,[],[f16913,f355])).

fof(f16913,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X2,X2),X3)) ),
    inference(forward_demodulation,[],[f16912,f20])).

fof(f16912,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X2,X2),X3)) ),
    inference(forward_demodulation,[],[f16838,f1589])).

fof(f16838,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X2,k4_xboole_0(X2,X3)),X3)) ),
    inference(superposition,[],[f9022,f443])).

fof(f9022,plain,(
    ! [X2] : k4_xboole_0(X2,X2) = k4_xboole_0(X2,k3_xboole_0(X2,X2)) ),
    inference(backward_demodulation,[],[f6366,f9014])).

fof(f9014,plain,(
    ! [X12] : k4_xboole_0(X12,X12) = k4_xboole_0(k2_xboole_0(X12,X12),k3_xboole_0(X12,X12)) ),
    inference(backward_demodulation,[],[f5742,f9007])).

fof(f9007,plain,(
    ! [X2] : k2_xboole_0(X2,X2) = k5_xboole_0(X2,k5_xboole_0(X2,X2)) ),
    inference(forward_demodulation,[],[f9006,f25])).

fof(f9006,plain,(
    ! [X2] : k2_xboole_0(X2,k2_xboole_0(X2,X2)) = k5_xboole_0(X2,k5_xboole_0(X2,X2)) ),
    inference(forward_demodulation,[],[f9005,f7772])).

fof(f9005,plain,(
    ! [X2] : k2_xboole_0(k2_xboole_0(X2,X2),k2_xboole_0(X2,X2)) = k5_xboole_0(X2,k5_xboole_0(X2,X2)) ),
    inference(forward_demodulation,[],[f9004,f7527])).

fof(f7527,plain,(
    ! [X19,X20] : k5_xboole_0(X19,k2_xboole_0(X20,X20)) = k5_xboole_0(X20,X19) ),
    inference(backward_demodulation,[],[f274,f7517])).

fof(f7517,plain,(
    ! [X8,X9] : k5_xboole_0(X9,X8) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X9,X9),X8),k4_xboole_0(X8,X9)) ),
    inference(backward_demodulation,[],[f269,f7516])).

fof(f269,plain,(
    ! [X8,X9] : k5_xboole_0(k2_xboole_0(X9,X9),X8) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X9,X9),X8),k4_xboole_0(X8,X9)) ),
    inference(superposition,[],[f18,f100])).

fof(f274,plain,(
    ! [X19,X20] : k5_xboole_0(X19,k2_xboole_0(X20,X20)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X20,X20),X19),k4_xboole_0(X19,X20)) ),
    inference(superposition,[],[f34,f100])).

fof(f9004,plain,(
    ! [X2] : k2_xboole_0(k2_xboole_0(X2,X2),k2_xboole_0(X2,X2)) = k5_xboole_0(k5_xboole_0(X2,X2),k2_xboole_0(X2,X2)) ),
    inference(forward_demodulation,[],[f9003,f704])).

fof(f9003,plain,(
    ! [X2] : k2_xboole_0(k2_xboole_0(X2,X2),k2_xboole_0(X2,X2)) = k5_xboole_0(k5_xboole_0(X2,k2_xboole_0(X2,X2)),k2_xboole_0(X2,X2)) ),
    inference(forward_demodulation,[],[f8965,f130])).

fof(f8965,plain,(
    ! [X2] : k2_xboole_0(k2_xboole_0(X2,X2),k2_xboole_0(X2,X2)) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X2,X2),X2),k2_xboole_0(X2,X2)) ),
    inference(superposition,[],[f7553,f7538])).

fof(f7538,plain,(
    ! [X2,X3] : k5_xboole_0(X2,X3) = k5_xboole_0(X2,k2_xboole_0(X3,X3)) ),
    inference(forward_demodulation,[],[f7519,f86])).

fof(f7519,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k2_xboole_0(X3,X3)) = k2_xboole_0(k5_xboole_0(X3,X2),k4_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f1681,f7516])).

fof(f1681,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k2_xboole_0(X3,X3)) = k2_xboole_0(k5_xboole_0(k2_xboole_0(X3,X3),X2),k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f86,f100])).

fof(f6366,plain,(
    ! [X2] : k4_xboole_0(X2,k3_xboole_0(X2,X2)) = k4_xboole_0(k2_xboole_0(X2,X2),k3_xboole_0(X2,X2)) ),
    inference(superposition,[],[f16,f6160])).

fof(f34081,plain,(
    ! [X74,X73] : k4_xboole_0(X73,k2_xboole_0(X74,k3_xboole_0(X73,X73))) = k4_xboole_0(k4_xboole_0(X74,X73),k4_xboole_0(X74,k3_xboole_0(X74,X73))) ),
    inference(forward_demodulation,[],[f34080,f32484])).

fof(f32484,plain,(
    ! [X39,X40] : k4_xboole_0(X40,k2_xboole_0(X39,k4_xboole_0(X39,X40))) = k4_xboole_0(X40,k3_xboole_0(X40,X39)) ),
    inference(backward_demodulation,[],[f5562,f32479])).

fof(f34080,plain,(
    ! [X74,X73] : k4_xboole_0(X73,k2_xboole_0(X74,k3_xboole_0(X73,X73))) = k4_xboole_0(k4_xboole_0(X74,X73),k4_xboole_0(X74,k2_xboole_0(X73,k4_xboole_0(X73,X74)))) ),
    inference(forward_demodulation,[],[f34079,f5731])).

fof(f34079,plain,(
    ! [X74,X73] : k4_xboole_0(X73,k2_xboole_0(X74,k3_xboole_0(X73,X73))) = k4_xboole_0(k4_xboole_0(X74,X73),k4_xboole_0(X74,k2_xboole_0(X73,k3_xboole_0(X74,X73)))) ),
    inference(forward_demodulation,[],[f34078,f1479])).

fof(f34078,plain,(
    ! [X74,X73] : k4_xboole_0(X73,k2_xboole_0(X74,k3_xboole_0(X73,X73))) = k4_xboole_0(k4_xboole_0(X74,X73),k4_xboole_0(X74,k2_xboole_0(k3_xboole_0(X74,X73),X73))) ),
    inference(forward_demodulation,[],[f34077,f20])).

fof(f34077,plain,(
    ! [X74,X73] : k4_xboole_0(X73,k2_xboole_0(X74,k3_xboole_0(X73,X73))) = k4_xboole_0(k4_xboole_0(X74,X73),k4_xboole_0(k4_xboole_0(X74,k3_xboole_0(X74,X73)),X73)) ),
    inference(forward_demodulation,[],[f34076,f12278])).

fof(f12278,plain,(
    ! [X19,X18] : k4_xboole_0(X18,k3_xboole_0(X18,X19)) = k3_xboole_0(X18,k5_xboole_0(X19,k2_xboole_0(X18,X19))) ),
    inference(forward_demodulation,[],[f12171,f5493])).

fof(f12171,plain,(
    ! [X19,X18] : k4_xboole_0(X18,k4_xboole_0(k3_xboole_0(X18,X19),k4_xboole_0(X19,k2_xboole_0(X18,X19)))) = k3_xboole_0(X18,k5_xboole_0(X19,k2_xboole_0(X18,X19))) ),
    inference(superposition,[],[f364,f111])).

fof(f364,plain,(
    ! [X6,X7,X5] : k3_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),X7)) = k4_xboole_0(X5,k4_xboole_0(k3_xboole_0(X5,X6),X7)) ),
    inference(superposition,[],[f17,f60])).

fof(f34076,plain,(
    ! [X74,X73] : k4_xboole_0(X73,k2_xboole_0(X74,k3_xboole_0(X73,X73))) = k4_xboole_0(k4_xboole_0(X74,X73),k4_xboole_0(k3_xboole_0(X74,k5_xboole_0(X73,k2_xboole_0(X74,X73))),X73)) ),
    inference(forward_demodulation,[],[f34075,f443])).

fof(f34075,plain,(
    ! [X74,X73] : k4_xboole_0(k4_xboole_0(X74,X73),k3_xboole_0(k4_xboole_0(X74,X73),k5_xboole_0(X73,k2_xboole_0(X74,X73)))) = k4_xboole_0(X73,k2_xboole_0(X74,k3_xboole_0(X73,X73))) ),
    inference(forward_demodulation,[],[f34074,f33071])).

fof(f33071,plain,(
    ! [X23,X21,X22] : k4_xboole_0(k5_xboole_0(k2_xboole_0(X21,X22),k2_xboole_0(X22,X23)),k4_xboole_0(X21,k2_xboole_0(X22,X23))) = k4_xboole_0(X23,k2_xboole_0(X22,k3_xboole_0(X23,X21))) ),
    inference(backward_demodulation,[],[f32845,f33003])).

fof(f33003,plain,(
    ! [X26,X24,X25] : k4_xboole_0(X25,k3_xboole_0(X25,k2_xboole_0(X24,X26))) = k4_xboole_0(X25,k2_xboole_0(X24,k3_xboole_0(X25,X26))) ),
    inference(forward_demodulation,[],[f32871,f534])).

fof(f534,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,k3_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X1,X2))),X1) ),
    inference(forward_demodulation,[],[f533,f15])).

fof(f533,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X1,X2))),X1) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k3_xboole_0(X0,X2),X1))) ),
    inference(forward_demodulation,[],[f532,f443])).

fof(f532,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,k3_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X1,X2))),X1) ),
    inference(forward_demodulation,[],[f531,f27])).

fof(f531,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,k3_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))),X1) ),
    inference(forward_demodulation,[],[f530,f20])).

fof(f530,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,k3_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k3_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2)),X1) ),
    inference(forward_demodulation,[],[f513,f20])).

fof(f513,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2)),X1) = k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(superposition,[],[f27,f443])).

fof(f32871,plain,(
    ! [X26,X24,X25] : k4_xboole_0(X25,k3_xboole_0(X25,k2_xboole_0(X24,X26))) = k4_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,k2_xboole_0(X24,X26))),X24) ),
    inference(backward_demodulation,[],[f30004,f32479])).

fof(f30004,plain,(
    ! [X26,X24,X25] : k4_xboole_0(k3_xboole_0(X25,X25),k2_xboole_0(X24,X26)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X25,X25),k2_xboole_0(X24,X26)),X24) ),
    inference(forward_demodulation,[],[f30003,f1589])).

fof(f30003,plain,(
    ! [X26,X24,X25] : k4_xboole_0(k3_xboole_0(X25,X25),k2_xboole_0(X24,X26)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X25,k4_xboole_0(X25,k2_xboole_0(X24,X26))),k2_xboole_0(X24,X26)),X24) ),
    inference(forward_demodulation,[],[f30002,f443])).

fof(f30002,plain,(
    ! [X26,X24,X25] : k4_xboole_0(k3_xboole_0(X25,X25),k2_xboole_0(X24,X26)) = k4_xboole_0(k3_xboole_0(k4_xboole_0(X25,k2_xboole_0(X24,X26)),k4_xboole_0(X25,k2_xboole_0(X24,X26))),X24) ),
    inference(forward_demodulation,[],[f30001,f29998])).

fof(f29998,plain,(
    ! [X90,X91,X89] : k4_xboole_0(k2_xboole_0(X89,k4_xboole_0(X90,X91)),k4_xboole_0(X89,k4_xboole_0(X90,k2_xboole_0(X89,X91)))) = k4_xboole_0(k3_xboole_0(X90,X90),k2_xboole_0(X89,X91)) ),
    inference(backward_demodulation,[],[f4064,f29995])).

fof(f29995,plain,(
    ! [X23,X21,X22] : k4_xboole_0(k3_xboole_0(X22,X22),k2_xboole_0(X21,X23)) = k4_xboole_0(X22,k2_xboole_0(X21,k2_xboole_0(X23,k4_xboole_0(X21,k4_xboole_0(X22,X21))))) ),
    inference(forward_demodulation,[],[f29994,f7772])).

fof(f29994,plain,(
    ! [X23,X21,X22] : k4_xboole_0(X22,k2_xboole_0(X21,k2_xboole_0(X23,k4_xboole_0(X21,k4_xboole_0(X22,X21))))) = k4_xboole_0(k3_xboole_0(X22,X22),k2_xboole_0(X23,k2_xboole_0(X21,X21))) ),
    inference(forward_demodulation,[],[f29993,f71])).

fof(f29993,plain,(
    ! [X23,X21,X22] : k4_xboole_0(X22,k2_xboole_0(X21,k2_xboole_0(X23,k4_xboole_0(X21,k4_xboole_0(X22,X21))))) = k4_xboole_0(k3_xboole_0(X22,X22),k2_xboole_0(k2_xboole_0(X23,X21),X21)) ),
    inference(forward_demodulation,[],[f29992,f20])).

fof(f29992,plain,(
    ! [X23,X21,X22] : k4_xboole_0(X22,k2_xboole_0(X21,k2_xboole_0(X23,k4_xboole_0(X21,k4_xboole_0(X22,X21))))) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X22,X22),k2_xboole_0(X23,X21)),X21) ),
    inference(forward_demodulation,[],[f29991,f1589])).

fof(f29991,plain,(
    ! [X23,X21,X22] : k4_xboole_0(X22,k2_xboole_0(X21,k2_xboole_0(X23,k4_xboole_0(X21,k4_xboole_0(X22,X21))))) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X22,k4_xboole_0(X22,k2_xboole_0(X23,X21))),k2_xboole_0(X23,X21)),X21) ),
    inference(forward_demodulation,[],[f29990,f443])).

fof(f29990,plain,(
    ! [X23,X21,X22] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X22,k2_xboole_0(X23,X21)),k4_xboole_0(X22,k2_xboole_0(X23,X21))),X21) = k4_xboole_0(X22,k2_xboole_0(X21,k2_xboole_0(X23,k4_xboole_0(X21,k4_xboole_0(X22,X21))))) ),
    inference(forward_demodulation,[],[f29989,f4064])).

fof(f29989,plain,(
    ! [X23,X21,X22] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X22,k2_xboole_0(X23,X21)),k4_xboole_0(X22,k2_xboole_0(X23,X21))),X21) = k4_xboole_0(k2_xboole_0(X21,k4_xboole_0(X22,X23)),k4_xboole_0(X21,k4_xboole_0(X22,k2_xboole_0(X21,X23)))) ),
    inference(forward_demodulation,[],[f29988,f25])).

fof(f29988,plain,(
    ! [X23,X21,X22] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X22,k2_xboole_0(X23,X21)),k4_xboole_0(X22,k2_xboole_0(X23,X21))),X21) = k4_xboole_0(k2_xboole_0(X21,k4_xboole_0(X22,X23)),k4_xboole_0(X21,k4_xboole_0(X22,k2_xboole_0(X21,k2_xboole_0(X23,X21))))) ),
    inference(forward_demodulation,[],[f29987,f4034])).

fof(f4034,plain,(
    ! [X30,X31,X29] : k4_xboole_0(X29,k4_xboole_0(X30,k2_xboole_0(X31,X29))) = k4_xboole_0(X29,k4_xboole_0(X30,k2_xboole_0(X29,X31))) ),
    inference(forward_demodulation,[],[f4033,f25])).

fof(f4033,plain,(
    ! [X30,X31,X29] : k4_xboole_0(X29,k4_xboole_0(X30,k2_xboole_0(X31,X29))) = k4_xboole_0(X29,k4_xboole_0(X30,k2_xboole_0(X29,k2_xboole_0(X31,X29)))) ),
    inference(forward_demodulation,[],[f4032,f71])).

fof(f4032,plain,(
    ! [X30,X31,X29] : k4_xboole_0(X29,k4_xboole_0(X30,k2_xboole_0(X31,X29))) = k4_xboole_0(X29,k4_xboole_0(X30,k2_xboole_0(k2_xboole_0(X29,X31),X29))) ),
    inference(forward_demodulation,[],[f4031,f20])).

fof(f4031,plain,(
    ! [X30,X31,X29] : k4_xboole_0(X29,k4_xboole_0(k4_xboole_0(X30,k2_xboole_0(X29,X31)),X29)) = k4_xboole_0(X29,k4_xboole_0(X30,k2_xboole_0(X31,X29))) ),
    inference(forward_demodulation,[],[f4030,f20])).

fof(f4030,plain,(
    ! [X30,X31,X29] : k4_xboole_0(X29,k4_xboole_0(k4_xboole_0(X30,k2_xboole_0(X29,X31)),X29)) = k4_xboole_0(X29,k4_xboole_0(k4_xboole_0(X30,X31),X29)) ),
    inference(forward_demodulation,[],[f3958,f52])).

fof(f3958,plain,(
    ! [X30,X31,X29] : k4_xboole_0(X29,k4_xboole_0(k4_xboole_0(X30,k2_xboole_0(X29,X31)),X29)) = k3_xboole_0(k2_xboole_0(X29,k4_xboole_0(X30,X31)),X29) ),
    inference(superposition,[],[f52,f419])).

fof(f29987,plain,(
    ! [X23,X21,X22] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X22,k2_xboole_0(X23,X21)),k4_xboole_0(X22,k2_xboole_0(X23,X21))),X21) = k4_xboole_0(k2_xboole_0(X21,k4_xboole_0(X22,X23)),k4_xboole_0(X21,k4_xboole_0(X22,k2_xboole_0(k2_xboole_0(X23,X21),X21)))) ),
    inference(forward_demodulation,[],[f29818,f20])).

fof(f29818,plain,(
    ! [X23,X21,X22] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X22,k2_xboole_0(X23,X21)),k4_xboole_0(X22,k2_xboole_0(X23,X21))),X21) = k4_xboole_0(k2_xboole_0(X21,k4_xboole_0(X22,X23)),k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X22,k2_xboole_0(X23,X21)),X21))) ),
    inference(superposition,[],[f5578,f66])).

fof(f5578,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X3,X2))) = k4_xboole_0(k3_xboole_0(X3,X3),X2) ),
    inference(backward_demodulation,[],[f956,f5562])).

fof(f956,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X3,X2))) = k4_xboole_0(X3,k2_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(backward_demodulation,[],[f92,f951])).

fof(f951,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k2_xboole_0(X13,k4_xboole_0(X13,X12))) = k3_xboole_0(k2_xboole_0(X13,X12),k4_xboole_0(X12,X13)) ),
    inference(forward_demodulation,[],[f950,f110])).

fof(f110,plain,(
    ! [X10,X8,X9] : k4_xboole_0(k4_xboole_0(X8,X9),k2_xboole_0(X9,X10)) = k4_xboole_0(X8,k2_xboole_0(X9,X10)) ),
    inference(forward_demodulation,[],[f104,f20])).

fof(f104,plain,(
    ! [X10,X8,X9] : k4_xboole_0(k4_xboole_0(X8,X9),k2_xboole_0(X9,X10)) = k4_xboole_0(k4_xboole_0(X8,X9),X10) ),
    inference(superposition,[],[f20,f50])).

fof(f950,plain,(
    ! [X12,X13] : k3_xboole_0(k2_xboole_0(X13,X12),k4_xboole_0(X12,X13)) = k4_xboole_0(k4_xboole_0(X12,X13),k2_xboole_0(X13,k4_xboole_0(X13,X12))) ),
    inference(forward_demodulation,[],[f949,f462])).

fof(f462,plain,(
    ! [X26,X27,X25] : k2_xboole_0(X26,k4_xboole_0(X27,k4_xboole_0(X25,X26))) = k2_xboole_0(X26,k4_xboole_0(X27,X25)) ),
    inference(forward_demodulation,[],[f427,f419])).

fof(f427,plain,(
    ! [X26,X27,X25] : k2_xboole_0(X26,k4_xboole_0(X27,k4_xboole_0(X25,X26))) = k2_xboole_0(X26,k4_xboole_0(X27,k2_xboole_0(X26,X25))) ),
    inference(superposition,[],[f66,f211])).

fof(f949,plain,(
    ! [X12,X13] : k4_xboole_0(k4_xboole_0(X12,X13),k2_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X12,X13)))) = k3_xboole_0(k2_xboole_0(X13,X12),k4_xboole_0(X12,X13)) ),
    inference(forward_demodulation,[],[f912,f92])).

fof(f912,plain,(
    ! [X12,X13] : k4_xboole_0(k4_xboole_0(X12,X13),k2_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X12,X13)))) = k4_xboole_0(k2_xboole_0(X13,X12),k4_xboole_0(X13,k4_xboole_0(X12,X13))) ),
    inference(superposition,[],[f41,f109])).

fof(f92,plain,(
    ! [X2,X3] : k3_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(forward_demodulation,[],[f89,f52])).

fof(f89,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k3_xboole_0(k2_xboole_0(X2,X3),X2)) = k3_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) ),
    inference(superposition,[],[f27,f21])).

fof(f4064,plain,(
    ! [X90,X91,X89] : k4_xboole_0(k2_xboole_0(X89,k4_xboole_0(X90,X91)),k4_xboole_0(X89,k4_xboole_0(X90,k2_xboole_0(X89,X91)))) = k4_xboole_0(X90,k2_xboole_0(X89,k2_xboole_0(X91,k4_xboole_0(X89,k4_xboole_0(X90,X89))))) ),
    inference(forward_demodulation,[],[f4063,f3987])).

fof(f3987,plain,(
    ! [X14,X12,X15,X13] : k2_xboole_0(X12,k4_xboole_0(X15,k4_xboole_0(X13,k2_xboole_0(X14,X12)))) = k2_xboole_0(X12,k4_xboole_0(X15,k4_xboole_0(X13,X14))) ),
    inference(forward_demodulation,[],[f3922,f419])).

fof(f3922,plain,(
    ! [X14,X12,X15,X13] : k2_xboole_0(X12,k4_xboole_0(X15,k4_xboole_0(X13,k2_xboole_0(X14,X12)))) = k2_xboole_0(X12,k4_xboole_0(X15,k2_xboole_0(X12,k4_xboole_0(X13,X14)))) ),
    inference(superposition,[],[f419,f66])).

fof(f4063,plain,(
    ! [X90,X91,X89] : k4_xboole_0(k2_xboole_0(X89,k4_xboole_0(X90,X91)),k4_xboole_0(X89,k4_xboole_0(X90,k2_xboole_0(X89,X91)))) = k4_xboole_0(X90,k2_xboole_0(X89,k2_xboole_0(X91,k4_xboole_0(X89,k4_xboole_0(X90,k2_xboole_0(X89,X91)))))) ),
    inference(forward_demodulation,[],[f4062,f71])).

fof(f4062,plain,(
    ! [X90,X91,X89] : k4_xboole_0(k2_xboole_0(X89,k4_xboole_0(X90,X91)),k4_xboole_0(X89,k4_xboole_0(X90,k2_xboole_0(X89,X91)))) = k4_xboole_0(X90,k2_xboole_0(k2_xboole_0(X89,X91),k4_xboole_0(X89,k4_xboole_0(X90,k2_xboole_0(X89,X91))))) ),
    inference(forward_demodulation,[],[f3975,f20])).

fof(f3975,plain,(
    ! [X90,X91,X89] : k4_xboole_0(k4_xboole_0(X90,k2_xboole_0(X89,X91)),k4_xboole_0(X89,k4_xboole_0(X90,k2_xboole_0(X89,X91)))) = k4_xboole_0(k2_xboole_0(X89,k4_xboole_0(X90,X91)),k4_xboole_0(X89,k4_xboole_0(X90,k2_xboole_0(X89,X91)))) ),
    inference(superposition,[],[f171,f419])).

fof(f30001,plain,(
    ! [X26,X24,X25] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X25,k2_xboole_0(X24,X26)),k4_xboole_0(X25,k2_xboole_0(X24,X26))),X24) = k4_xboole_0(k2_xboole_0(X24,k4_xboole_0(X25,X26)),k4_xboole_0(X24,k4_xboole_0(X25,k2_xboole_0(X24,X26)))) ),
    inference(forward_demodulation,[],[f30000,f53])).

fof(f30000,plain,(
    ! [X26,X24,X25] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X25,k2_xboole_0(X24,X26)),k4_xboole_0(X25,k2_xboole_0(X24,X26))),X24) = k4_xboole_0(k2_xboole_0(X24,k4_xboole_0(X25,X26)),k4_xboole_0(X24,k4_xboole_0(X25,k2_xboole_0(X24,k2_xboole_0(X24,X26))))) ),
    inference(forward_demodulation,[],[f29999,f4034])).

fof(f29999,plain,(
    ! [X26,X24,X25] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X25,k2_xboole_0(X24,X26)),k4_xboole_0(X25,k2_xboole_0(X24,X26))),X24) = k4_xboole_0(k2_xboole_0(X24,k4_xboole_0(X25,X26)),k4_xboole_0(X24,k4_xboole_0(X25,k2_xboole_0(k2_xboole_0(X24,X26),X24)))) ),
    inference(forward_demodulation,[],[f29819,f20])).

fof(f29819,plain,(
    ! [X26,X24,X25] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X25,k2_xboole_0(X24,X26)),k4_xboole_0(X25,k2_xboole_0(X24,X26))),X24) = k4_xboole_0(k2_xboole_0(X24,k4_xboole_0(X25,X26)),k4_xboole_0(X24,k4_xboole_0(k4_xboole_0(X25,k2_xboole_0(X24,X26)),X24))) ),
    inference(superposition,[],[f5578,f419])).

fof(f32845,plain,(
    ! [X23,X21,X22] : k4_xboole_0(k5_xboole_0(k2_xboole_0(X21,X22),k2_xboole_0(X22,X23)),k4_xboole_0(X21,k2_xboole_0(X22,X23))) = k4_xboole_0(X23,k3_xboole_0(X23,k2_xboole_0(X22,X21))) ),
    inference(backward_demodulation,[],[f21197,f32479])).

fof(f21197,plain,(
    ! [X23,X21,X22] : k4_xboole_0(k5_xboole_0(k2_xboole_0(X21,X22),k2_xboole_0(X22,X23)),k4_xboole_0(X21,k2_xboole_0(X22,X23))) = k4_xboole_0(k3_xboole_0(X23,X23),k2_xboole_0(X22,X21)) ),
    inference(backward_demodulation,[],[f7132,f21195])).

fof(f21195,plain,(
    ! [X23,X21,X22] : k4_xboole_0(k3_xboole_0(k2_xboole_0(X22,X23),k2_xboole_0(X22,X23)),k2_xboole_0(X21,X22)) = k4_xboole_0(k3_xboole_0(X23,X23),k2_xboole_0(X22,X21)) ),
    inference(backward_demodulation,[],[f5824,f21194])).

fof(f21194,plain,(
    ! [X12,X13,X11] : k4_xboole_0(k5_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X11,X12)),k4_xboole_0(X11,k2_xboole_0(X12,X13))) = k4_xboole_0(k3_xboole_0(X13,X13),k2_xboole_0(X12,X11)) ),
    inference(forward_demodulation,[],[f21193,f6818])).

fof(f6818,plain,(
    ! [X64,X62,X63] : k4_xboole_0(X64,k2_xboole_0(X62,k2_xboole_0(X63,k4_xboole_0(X63,X64)))) = k4_xboole_0(k3_xboole_0(X64,X64),k2_xboole_0(X62,X63)) ),
    inference(backward_demodulation,[],[f4075,f6817])).

fof(f6817,plain,(
    ! [X26,X24,X25] : k4_xboole_0(k5_xboole_0(k2_xboole_0(X24,X26),k2_xboole_0(X24,X25)),k4_xboole_0(X25,k2_xboole_0(X24,X26))) = k4_xboole_0(k3_xboole_0(X26,X26),k2_xboole_0(X24,X25)) ),
    inference(backward_demodulation,[],[f5937,f6816])).

fof(f6816,plain,(
    ! [X37,X35,X36,X34] : k4_xboole_0(k3_xboole_0(X37,k2_xboole_0(X34,X35)),k2_xboole_0(X34,X36)) = k4_xboole_0(k3_xboole_0(X37,X35),k2_xboole_0(X34,X36)) ),
    inference(forward_demodulation,[],[f6732,f1589])).

fof(f6732,plain,(
    ! [X37,X35,X36,X34] : k4_xboole_0(k3_xboole_0(X37,k2_xboole_0(X34,X35)),k2_xboole_0(X34,X36)) = k4_xboole_0(k3_xboole_0(X37,k4_xboole_0(X35,k2_xboole_0(X34,X36))),k2_xboole_0(X34,X36)) ),
    inference(superposition,[],[f1589,f69])).

fof(f5937,plain,(
    ! [X26,X24,X25] : k4_xboole_0(k5_xboole_0(k2_xboole_0(X24,X26),k2_xboole_0(X24,X25)),k4_xboole_0(X25,k2_xboole_0(X24,X26))) = k4_xboole_0(k3_xboole_0(X26,k2_xboole_0(X24,X26)),k2_xboole_0(X24,X25)) ),
    inference(forward_demodulation,[],[f5825,f2665])).

fof(f2665,plain,(
    ! [X109,X107,X110,X108] : k4_xboole_0(k3_xboole_0(k2_xboole_0(X107,X108),X110),k2_xboole_0(X107,X109)) = k4_xboole_0(k3_xboole_0(X108,X110),k2_xboole_0(X107,X109)) ),
    inference(forward_demodulation,[],[f2588,f443])).

fof(f2588,plain,(
    ! [X109,X107,X110,X108] : k4_xboole_0(k3_xboole_0(k2_xboole_0(X107,X108),X110),k2_xboole_0(X107,X109)) = k3_xboole_0(k4_xboole_0(X108,k2_xboole_0(X107,X109)),X110) ),
    inference(superposition,[],[f443,f69])).

fof(f5825,plain,(
    ! [X26,X24,X25] : k4_xboole_0(k3_xboole_0(k2_xboole_0(X24,X26),k2_xboole_0(X24,X26)),k2_xboole_0(X24,X25)) = k4_xboole_0(k5_xboole_0(k2_xboole_0(X24,X26),k2_xboole_0(X24,X25)),k4_xboole_0(X25,k2_xboole_0(X24,X26))) ),
    inference(superposition,[],[f5563,f69])).

fof(f4075,plain,(
    ! [X64,X62,X63] : k4_xboole_0(k5_xboole_0(k2_xboole_0(X62,X64),k2_xboole_0(X62,X63)),k4_xboole_0(X63,k2_xboole_0(X62,X64))) = k4_xboole_0(X64,k2_xboole_0(X62,k2_xboole_0(X63,k4_xboole_0(X63,X64)))) ),
    inference(backward_demodulation,[],[f2653,f4074])).

fof(f4074,plain,(
    ! [X118,X116,X114,X117,X115] : k4_xboole_0(X118,k2_xboole_0(X114,k2_xboole_0(X115,k4_xboole_0(X116,X117)))) = k4_xboole_0(X118,k2_xboole_0(X114,k2_xboole_0(X115,k4_xboole_0(X116,k2_xboole_0(X114,X117))))) ),
    inference(forward_demodulation,[],[f4073,f4007])).

fof(f4007,plain,(
    ! [X26,X24,X27,X25] : k2_xboole_0(X26,k4_xboole_0(X24,k2_xboole_0(X25,k2_xboole_0(X26,X27)))) = k2_xboole_0(X26,k4_xboole_0(X24,k2_xboole_0(X25,X27))) ),
    inference(forward_demodulation,[],[f3949,f20])).

fof(f3949,plain,(
    ! [X26,X24,X27,X25] : k2_xboole_0(X26,k4_xboole_0(k4_xboole_0(X24,X25),X27)) = k2_xboole_0(X26,k4_xboole_0(X24,k2_xboole_0(X25,k2_xboole_0(X26,X27)))) ),
    inference(superposition,[],[f419,f20])).

fof(f4073,plain,(
    ! [X118,X116,X114,X117,X115] : k4_xboole_0(X118,k2_xboole_0(X114,k2_xboole_0(X115,k4_xboole_0(X116,X117)))) = k4_xboole_0(X118,k2_xboole_0(X114,k2_xboole_0(X115,k4_xboole_0(X116,k2_xboole_0(X114,k2_xboole_0(X115,X117)))))) ),
    inference(forward_demodulation,[],[f4072,f71])).

fof(f4072,plain,(
    ! [X118,X116,X114,X117,X115] : k4_xboole_0(X118,k2_xboole_0(X114,k2_xboole_0(X115,k4_xboole_0(X116,k2_xboole_0(k2_xboole_0(X114,X115),X117))))) = k4_xboole_0(X118,k2_xboole_0(X114,k2_xboole_0(X115,k4_xboole_0(X116,X117)))) ),
    inference(forward_demodulation,[],[f3983,f71])).

fof(f3983,plain,(
    ! [X118,X116,X114,X117,X115] : k4_xboole_0(X118,k2_xboole_0(X114,k2_xboole_0(X115,k4_xboole_0(X116,k2_xboole_0(k2_xboole_0(X114,X115),X117))))) = k4_xboole_0(X118,k2_xboole_0(k2_xboole_0(X114,X115),k4_xboole_0(X116,X117))) ),
    inference(superposition,[],[f71,f419])).

fof(f2653,plain,(
    ! [X64,X62,X63] : k4_xboole_0(k5_xboole_0(k2_xboole_0(X62,X64),k2_xboole_0(X62,X63)),k4_xboole_0(X63,k2_xboole_0(X62,X64))) = k4_xboole_0(X64,k2_xboole_0(X62,k2_xboole_0(X63,k4_xboole_0(X63,k2_xboole_0(X62,X64))))) ),
    inference(forward_demodulation,[],[f2652,f69])).

fof(f2652,plain,(
    ! [X64,X62,X63] : k4_xboole_0(k5_xboole_0(k2_xboole_0(X62,X64),k2_xboole_0(X62,X63)),k4_xboole_0(X63,k2_xboole_0(X62,X64))) = k4_xboole_0(k2_xboole_0(X62,X64),k2_xboole_0(X62,k2_xboole_0(X63,k4_xboole_0(X63,k2_xboole_0(X62,X64))))) ),
    inference(forward_demodulation,[],[f2574,f71])).

fof(f2574,plain,(
    ! [X64,X62,X63] : k4_xboole_0(k5_xboole_0(k2_xboole_0(X62,X64),k2_xboole_0(X62,X63)),k4_xboole_0(X63,k2_xboole_0(X62,X64))) = k4_xboole_0(k2_xboole_0(X62,X64),k2_xboole_0(k2_xboole_0(X62,X63),k4_xboole_0(X63,k2_xboole_0(X62,X64)))) ),
    inference(superposition,[],[f41,f69])).

fof(f21193,plain,(
    ! [X12,X13,X11] : k4_xboole_0(k5_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X11,X12)),k4_xboole_0(X11,k2_xboole_0(X12,X13))) = k4_xboole_0(X13,k2_xboole_0(X12,k2_xboole_0(X11,k4_xboole_0(X11,X13)))) ),
    inference(forward_demodulation,[],[f21192,f12516])).

fof(f12516,plain,(
    ! [X151,X149,X150,X148] : k4_xboole_0(X151,k2_xboole_0(X148,k2_xboole_0(X149,X150))) = k4_xboole_0(X151,k2_xboole_0(X148,k2_xboole_0(X150,X149))) ),
    inference(forward_demodulation,[],[f12515,f7772])).

fof(f12515,plain,(
    ! [X151,X149,X150,X148] : k4_xboole_0(X151,k2_xboole_0(X148,k2_xboole_0(X149,k2_xboole_0(X150,X150)))) = k4_xboole_0(X151,k2_xboole_0(X148,k2_xboole_0(X149,X150))) ),
    inference(forward_demodulation,[],[f12417,f71])).

fof(f12417,plain,(
    ! [X151,X149,X150,X148] : k4_xboole_0(X151,k2_xboole_0(X148,k2_xboole_0(X149,k2_xboole_0(X150,X150)))) = k4_xboole_0(X151,k2_xboole_0(k2_xboole_0(X148,X149),X150)) ),
    inference(superposition,[],[f71,f9458])).

fof(f21192,plain,(
    ! [X12,X13,X11] : k4_xboole_0(k5_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X11,X12)),k4_xboole_0(X11,k2_xboole_0(X12,X13))) = k4_xboole_0(X13,k2_xboole_0(X12,k2_xboole_0(k4_xboole_0(X11,X13),X11))) ),
    inference(backward_demodulation,[],[f967,f20779])).

fof(f20779,plain,(
    ! [X43,X41,X42,X40] : k4_xboole_0(X41,k2_xboole_0(X40,k2_xboole_0(X42,X43))) = k4_xboole_0(k2_xboole_0(X40,X41),k2_xboole_0(X43,k2_xboole_0(X40,X42))) ),
    inference(superposition,[],[f1068,f69])).

fof(f967,plain,(
    ! [X12,X13,X11] : k4_xboole_0(k5_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X11,X12)),k4_xboole_0(X11,k2_xboole_0(X12,X13))) = k4_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X11,k2_xboole_0(X12,k4_xboole_0(X11,X13)))) ),
    inference(forward_demodulation,[],[f966,f419])).

fof(f966,plain,(
    ! [X12,X13,X11] : k4_xboole_0(k5_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X11,X12)),k4_xboole_0(X11,k2_xboole_0(X12,X13))) = k4_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X11,k2_xboole_0(X12,k4_xboole_0(X11,k2_xboole_0(X12,X13))))) ),
    inference(forward_demodulation,[],[f918,f71])).

fof(f918,plain,(
    ! [X12,X13,X11] : k4_xboole_0(k5_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X11,X12)),k4_xboole_0(X11,k2_xboole_0(X12,X13))) = k4_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(k2_xboole_0(X11,X12),k4_xboole_0(X11,k2_xboole_0(X12,X13)))) ),
    inference(superposition,[],[f41,f68])).

fof(f5824,plain,(
    ! [X23,X21,X22] : k4_xboole_0(k3_xboole_0(k2_xboole_0(X22,X23),k2_xboole_0(X22,X23)),k2_xboole_0(X21,X22)) = k4_xboole_0(k5_xboole_0(k2_xboole_0(X22,X23),k2_xboole_0(X21,X22)),k4_xboole_0(X21,k2_xboole_0(X22,X23))) ),
    inference(superposition,[],[f5563,f68])).

fof(f7132,plain,(
    ! [X23,X21,X22] : k4_xboole_0(k3_xboole_0(k2_xboole_0(X22,X23),k2_xboole_0(X22,X23)),k2_xboole_0(X21,X22)) = k4_xboole_0(k5_xboole_0(k2_xboole_0(X21,X22),k2_xboole_0(X22,X23)),k4_xboole_0(X21,k2_xboole_0(X22,X23))) ),
    inference(superposition,[],[f5564,f68])).

fof(f5564,plain,(
    ! [X6,X7] : k4_xboole_0(k5_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = k4_xboole_0(k3_xboole_0(X7,X7),X6) ),
    inference(backward_demodulation,[],[f51,f5562])).

fof(f51,plain,(
    ! [X6,X7] : k4_xboole_0(k5_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = k4_xboole_0(X7,k2_xboole_0(X6,k4_xboole_0(X6,X7))) ),
    inference(forward_demodulation,[],[f45,f20])).

fof(f45,plain,(
    ! [X6,X7] : k4_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7)) = k4_xboole_0(k5_xboole_0(X6,X7),k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f21,f18])).

fof(f34074,plain,(
    ! [X74,X73] : k4_xboole_0(k4_xboole_0(X74,X73),k3_xboole_0(k4_xboole_0(X74,X73),k5_xboole_0(X73,k2_xboole_0(X74,X73)))) = k4_xboole_0(k5_xboole_0(k2_xboole_0(X73,X74),k2_xboole_0(X74,X73)),k4_xboole_0(X73,k2_xboole_0(X74,X73))) ),
    inference(forward_demodulation,[],[f33844,f336])).

fof(f33844,plain,(
    ! [X74,X73] : k4_xboole_0(k4_xboole_0(X74,X73),k3_xboole_0(k4_xboole_0(X74,X73),k5_xboole_0(X73,k2_xboole_0(X74,X73)))) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X74,X73),k5_xboole_0(X73,k2_xboole_0(X74,X73))),k4_xboole_0(X73,k2_xboole_0(X74,X73))) ),
    inference(superposition,[],[f32485,f734])).

fof(f32485,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(backward_demodulation,[],[f5563,f32479])).

fof(f59141,plain,(
    ! [X196,X195] : k5_xboole_0(X196,k5_xboole_0(X196,k2_xboole_0(X195,X196))) = k5_xboole_0(k2_xboole_0(X195,X196),k4_xboole_0(X196,k2_xboole_0(X195,k3_xboole_0(X196,X196)))) ),
    inference(forward_demodulation,[],[f59140,f34049])).

fof(f34049,plain,(
    ! [X47,X48,X49] : k3_xboole_0(k2_xboole_0(X47,X48),k4_xboole_0(X48,k2_xboole_0(X47,X49))) = k4_xboole_0(X48,k2_xboole_0(X47,k3_xboole_0(X48,X49))) ),
    inference(backward_demodulation,[],[f2569,f34048])).

fof(f34048,plain,(
    ! [X57,X56,X55] : k4_xboole_0(k2_xboole_0(X55,X57),k3_xboole_0(k2_xboole_0(X55,X57),k2_xboole_0(X55,X56))) = k4_xboole_0(X57,k2_xboole_0(X55,k3_xboole_0(X57,X56))) ),
    inference(forward_demodulation,[],[f33837,f33014])).

fof(f33014,plain,(
    ! [X26,X24,X25] : k4_xboole_0(k5_xboole_0(k2_xboole_0(X24,X26),k2_xboole_0(X24,X25)),k4_xboole_0(X25,k2_xboole_0(X24,X26))) = k4_xboole_0(X26,k2_xboole_0(X24,k3_xboole_0(X26,X25))) ),
    inference(backward_demodulation,[],[f32786,f33003])).

fof(f32786,plain,(
    ! [X26,X24,X25] : k4_xboole_0(k5_xboole_0(k2_xboole_0(X24,X26),k2_xboole_0(X24,X25)),k4_xboole_0(X25,k2_xboole_0(X24,X26))) = k4_xboole_0(X26,k3_xboole_0(X26,k2_xboole_0(X24,X25))) ),
    inference(backward_demodulation,[],[f6817,f32479])).

fof(f33837,plain,(
    ! [X57,X56,X55] : k4_xboole_0(k2_xboole_0(X55,X57),k3_xboole_0(k2_xboole_0(X55,X57),k2_xboole_0(X55,X56))) = k4_xboole_0(k5_xboole_0(k2_xboole_0(X55,X57),k2_xboole_0(X55,X56)),k4_xboole_0(X56,k2_xboole_0(X55,X57))) ),
    inference(superposition,[],[f32485,f69])).

fof(f2569,plain,(
    ! [X47,X48,X49] : k4_xboole_0(k2_xboole_0(X47,X48),k3_xboole_0(k2_xboole_0(X47,X48),k2_xboole_0(X47,X49))) = k3_xboole_0(k2_xboole_0(X47,X48),k4_xboole_0(X48,k2_xboole_0(X47,X49))) ),
    inference(superposition,[],[f27,f69])).

fof(f59140,plain,(
    ! [X196,X195] : k5_xboole_0(k2_xboole_0(X195,X196),k3_xboole_0(k2_xboole_0(X195,X196),k4_xboole_0(X196,k2_xboole_0(X195,X196)))) = k5_xboole_0(X196,k5_xboole_0(X196,k2_xboole_0(X195,X196))) ),
    inference(forward_demodulation,[],[f59139,f27586])).

fof(f27586,plain,(
    ! [X2,X3] : k5_xboole_0(X3,k2_xboole_0(X2,X3)) = k5_xboole_0(k2_xboole_0(X3,X2),k2_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(forward_demodulation,[],[f27585,f5502])).

fof(f5502,plain,(
    ! [X14,X13] : k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X14)) = k5_xboole_0(X14,k2_xboole_0(X13,X14)) ),
    inference(forward_demodulation,[],[f5483,f111])).

fof(f5483,plain,(
    ! [X14,X13] : k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X14)) = k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X14,k2_xboole_0(X13,X14))) ),
    inference(backward_demodulation,[],[f451,f5482])).

fof(f451,plain,(
    ! [X14,X13] : k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X14)) = k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k3_xboole_0(X13,X14),X14)) ),
    inference(backward_demodulation,[],[f295,f443])).

fof(f295,plain,(
    ! [X14,X13] : k2_xboole_0(k4_xboole_0(X13,X14),k3_xboole_0(k4_xboole_0(X13,X14),X14)) = k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X14)) ),
    inference(superposition,[],[f29,f50])).

fof(f27585,plain,(
    ! [X2,X3] : k5_xboole_0(k2_xboole_0(X3,X2),k2_xboole_0(X3,k4_xboole_0(X3,X2))) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f27584,f13251])).

fof(f13251,plain,(
    ! [X14,X15,X13] : k5_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k3_xboole_0(X13,X14),X15)) = k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X15)) ),
    inference(forward_demodulation,[],[f13250,f3562])).

fof(f3562,plain,(
    ! [X12,X13,X11] : k2_xboole_0(k4_xboole_0(X11,X13),k4_xboole_0(X11,X12)) = k2_xboole_0(k4_xboole_0(X11,X13),k4_xboole_0(k3_xboole_0(X11,X13),X12)) ),
    inference(superposition,[],[f66,f355])).

fof(f13250,plain,(
    ! [X14,X15,X13] : k5_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k3_xboole_0(X13,X14),X15)) = k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k3_xboole_0(X13,X14),X15)) ),
    inference(forward_demodulation,[],[f13249,f14])).

fof(f13249,plain,(
    ! [X14,X15,X13] : k5_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k3_xboole_0(X13,X14),X15)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X13,X14),X15),k4_xboole_0(X13,X14)) ),
    inference(forward_demodulation,[],[f13085,f211])).

fof(f13085,plain,(
    ! [X14,X15,X13] : k5_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k3_xboole_0(X13,X14),X15)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k3_xboole_0(X13,X14),X15)),k4_xboole_0(k3_xboole_0(X13,X14),X15)) ),
    inference(superposition,[],[f63,f385])).

fof(f63,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f18,f20])).

fof(f27584,plain,(
    ! [X2,X3] : k5_xboole_0(k2_xboole_0(X3,X2),k2_xboole_0(X3,k4_xboole_0(X3,X2))) = k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X2,X3),X3)) ),
    inference(forward_demodulation,[],[f27583,f443])).

fof(f27583,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(k4_xboole_0(X2,X3),X3)) = k5_xboole_0(k2_xboole_0(X3,X2),k2_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(forward_demodulation,[],[f27582,f5731])).

fof(f27582,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(k4_xboole_0(X2,X3),X3)) = k5_xboole_0(k2_xboole_0(X3,X2),k2_xboole_0(X3,k3_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f27322,f27544])).

fof(f27544,plain,(
    ! [X80,X78,X79] : k5_xboole_0(k2_xboole_0(X79,X78),k2_xboole_0(X79,k3_xboole_0(X78,X80))) = k5_xboole_0(k4_xboole_0(X78,X79),k5_xboole_0(k2_xboole_0(X79,X78),k2_xboole_0(X79,k4_xboole_0(X78,X80)))) ),
    inference(backward_demodulation,[],[f26656,f27526])).

fof(f27526,plain,(
    ! [X26,X24,X25] : k5_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(X24,k2_xboole_0(X25,X26))) = k5_xboole_0(k2_xboole_0(X25,X24),k2_xboole_0(X25,k4_xboole_0(X24,X26))) ),
    inference(backward_demodulation,[],[f23941,f27517])).

fof(f27517,plain,(
    ! [X43,X44,X42] : k2_xboole_0(k4_xboole_0(X43,k2_xboole_0(X42,k2_xboole_0(X44,X43))),k4_xboole_0(k3_xboole_0(X42,X44),X43)) = k5_xboole_0(k2_xboole_0(X43,X42),k2_xboole_0(X43,k4_xboole_0(X42,X44))) ),
    inference(backward_demodulation,[],[f24915,f27300])).

fof(f27300,plain,(
    ! [X116,X114,X115,X113] : k5_xboole_0(k2_xboole_0(X115,X116),k2_xboole_0(X115,k4_xboole_0(X113,X114))) = k5_xboole_0(k4_xboole_0(X116,X115),k4_xboole_0(X113,k2_xboole_0(X114,X115))) ),
    inference(superposition,[],[f2638,f20])).

fof(f2638,plain,(
    ! [X6,X8,X7] : k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X8,X6)) = k5_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,X8)) ),
    inference(backward_demodulation,[],[f1857,f2637])).

fof(f2637,plain,(
    ! [X35,X36,X34] : k5_xboole_0(k2_xboole_0(X34,X35),k2_xboole_0(X34,X36)) = k2_xboole_0(k4_xboole_0(X35,k2_xboole_0(X34,X36)),k4_xboole_0(X36,k2_xboole_0(X34,X35))) ),
    inference(forward_demodulation,[],[f2565,f69])).

fof(f2565,plain,(
    ! [X35,X36,X34] : k5_xboole_0(k2_xboole_0(X34,X35),k2_xboole_0(X34,X36)) = k2_xboole_0(k4_xboole_0(X35,k2_xboole_0(X34,X36)),k4_xboole_0(k2_xboole_0(X34,X36),k2_xboole_0(X34,X35))) ),
    inference(superposition,[],[f18,f69])).

fof(f1857,plain,(
    ! [X6,X8,X7] : k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X8,X6)) = k2_xboole_0(k4_xboole_0(X7,k2_xboole_0(X6,X8)),k4_xboole_0(X8,k2_xboole_0(X6,X7))) ),
    inference(forward_demodulation,[],[f1856,f15])).

fof(f1856,plain,(
    ! [X6,X8,X7] : k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X8,X6)) = k2_xboole_0(k4_xboole_0(X7,k2_xboole_0(X6,k4_xboole_0(X8,X6))),k4_xboole_0(X8,k2_xboole_0(X6,X7))) ),
    inference(forward_demodulation,[],[f1775,f20])).

fof(f1775,plain,(
    ! [X6,X8,X7] : k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X8,X6)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X8,X6)),k4_xboole_0(X8,k2_xboole_0(X6,X7))) ),
    inference(superposition,[],[f63,f15])).

fof(f24915,plain,(
    ! [X43,X44,X42] : k5_xboole_0(k4_xboole_0(X42,X43),k4_xboole_0(X42,k2_xboole_0(X44,X43))) = k2_xboole_0(k4_xboole_0(X43,k2_xboole_0(X42,k2_xboole_0(X44,X43))),k4_xboole_0(k3_xboole_0(X42,X44),X43)) ),
    inference(forward_demodulation,[],[f24914,f23464])).

fof(f23464,plain,(
    ! [X105,X106,X104] : k4_xboole_0(X105,k2_xboole_0(X106,k2_xboole_0(X104,X105))) = k4_xboole_0(k3_xboole_0(X106,X105),k2_xboole_0(X104,X105)) ),
    inference(forward_demodulation,[],[f23463,f4693])).

fof(f4693,plain,(
    ! [X21,X22,X20] : k4_xboole_0(X20,k2_xboole_0(X22,k2_xboole_0(X21,X20))) = k4_xboole_0(k2_xboole_0(X21,X20),k2_xboole_0(X22,k2_xboole_0(X21,X20))) ),
    inference(superposition,[],[f559,f160])).

fof(f23463,plain,(
    ! [X105,X106,X104] : k4_xboole_0(k2_xboole_0(X104,X105),k2_xboole_0(X106,k2_xboole_0(X104,X105))) = k4_xboole_0(k3_xboole_0(X106,X105),k2_xboole_0(X104,X105)) ),
    inference(forward_demodulation,[],[f23462,f3513])).

fof(f3513,plain,(
    ! [X59,X60,X58] : k4_xboole_0(k3_xboole_0(X60,k4_xboole_0(X58,X59)),k2_xboole_0(X58,X59)) = k4_xboole_0(k3_xboole_0(X60,X59),k2_xboole_0(X58,X59)) ),
    inference(backward_demodulation,[],[f2383,f3512])).

fof(f3512,plain,(
    ! [X30,X28,X29] : k4_xboole_0(k3_xboole_0(X30,k2_xboole_0(X29,X28)),k2_xboole_0(X28,X29)) = k4_xboole_0(k3_xboole_0(X30,X29),k2_xboole_0(X28,X29)) ),
    inference(backward_demodulation,[],[f1517,f3467])).

fof(f3467,plain,(
    ! [X74,X75,X73] : k4_xboole_0(k3_xboole_0(X75,X74),k2_xboole_0(X73,X74)) = k4_xboole_0(k4_xboole_0(X75,k2_xboole_0(X73,X74)),k4_xboole_0(X75,k2_xboole_0(X74,X73))) ),
    inference(superposition,[],[f448,f3007])).

fof(f3007,plain,(
    ! [X14,X13] : k2_xboole_0(X14,X13) = k2_xboole_0(k2_xboole_0(X13,X14),X14) ),
    inference(forward_demodulation,[],[f2961,f211])).

fof(f2961,plain,(
    ! [X14,X13] : k2_xboole_0(k2_xboole_0(X13,X14),X14) = k2_xboole_0(k4_xboole_0(X13,X14),X14) ),
    inference(superposition,[],[f2903,f16])).

fof(f1517,plain,(
    ! [X30,X28,X29] : k4_xboole_0(k3_xboole_0(X30,k2_xboole_0(X29,X28)),k2_xboole_0(X28,X29)) = k4_xboole_0(k4_xboole_0(X30,k2_xboole_0(X28,X29)),k4_xboole_0(X30,k2_xboole_0(X29,X28))) ),
    inference(superposition,[],[f448,f84])).

fof(f2383,plain,(
    ! [X59,X60,X58] : k4_xboole_0(k3_xboole_0(X60,k4_xboole_0(X58,X59)),k2_xboole_0(X58,X59)) = k4_xboole_0(k3_xboole_0(X60,k2_xboole_0(X59,X58)),k2_xboole_0(X58,X59)) ),
    inference(forward_demodulation,[],[f2278,f1517])).

fof(f2278,plain,(
    ! [X59,X60,X58] : k4_xboole_0(k3_xboole_0(X60,k4_xboole_0(X58,X59)),k2_xboole_0(X58,X59)) = k4_xboole_0(k4_xboole_0(X60,k2_xboole_0(X58,X59)),k4_xboole_0(X60,k2_xboole_0(X59,X58))) ),
    inference(superposition,[],[f448,f307])).

fof(f23462,plain,(
    ! [X105,X106,X104] : k4_xboole_0(k2_xboole_0(X104,X105),k2_xboole_0(X106,k2_xboole_0(X104,X105))) = k4_xboole_0(k3_xboole_0(X106,k4_xboole_0(X104,X105)),k2_xboole_0(X104,X105)) ),
    inference(forward_demodulation,[],[f23285,f5484])).

fof(f5484,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k4_xboole_0(X3,k2_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f452,f5482])).

fof(f452,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X2,X3),X3) ),
    inference(backward_demodulation,[],[f101,f443])).

fof(f101,plain,(
    ! [X2,X3] : k3_xboole_0(k4_xboole_0(X2,X3),X3) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f17,f50])).

fof(f23285,plain,(
    ! [X105,X106,X104] : k4_xboole_0(k3_xboole_0(X106,k4_xboole_0(X104,X105)),k2_xboole_0(X104,X105)) = k4_xboole_0(k4_xboole_0(X106,k2_xboole_0(X104,X105)),k4_xboole_0(X106,k2_xboole_0(X104,X105))) ),
    inference(superposition,[],[f448,f2384])).

fof(f2384,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f310,f14])).

fof(f310,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f309,f211])).

fof(f309,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X3,X2),X2) = k2_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f308,f15])).

fof(f308,plain,(
    ! [X2,X3] : k2_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(forward_demodulation,[],[f290,f52])).

fof(f290,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X3,X2),k3_xboole_0(k2_xboole_0(X2,X3),X2)) = k2_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) ),
    inference(superposition,[],[f29,f21])).

fof(f24914,plain,(
    ! [X43,X44,X42] : k5_xboole_0(k4_xboole_0(X42,X43),k4_xboole_0(X42,k2_xboole_0(X44,X43))) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X42,X43),k2_xboole_0(X44,X43)),k4_xboole_0(k3_xboole_0(X42,X44),X43)) ),
    inference(forward_demodulation,[],[f24913,f3554])).

fof(f3554,plain,(
    ! [X10,X8,X11,X9] : k4_xboole_0(X8,k2_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X8,X11)))) = k4_xboole_0(k3_xboole_0(X8,X11),k2_xboole_0(X9,X10)) ),
    inference(superposition,[],[f355,f71])).

fof(f24913,plain,(
    ! [X43,X44,X42] : k5_xboole_0(k4_xboole_0(X42,X43),k4_xboole_0(X42,k2_xboole_0(X44,X43))) = k2_xboole_0(k4_xboole_0(X42,k2_xboole_0(X44,k2_xboole_0(X43,k4_xboole_0(X42,X43)))),k4_xboole_0(k3_xboole_0(X42,X44),X43)) ),
    inference(forward_demodulation,[],[f24912,f71])).

fof(f24912,plain,(
    ! [X43,X44,X42] : k5_xboole_0(k4_xboole_0(X42,X43),k4_xboole_0(X42,k2_xboole_0(X44,X43))) = k2_xboole_0(k4_xboole_0(X42,k2_xboole_0(k2_xboole_0(X44,X43),k4_xboole_0(X42,X43))),k4_xboole_0(k3_xboole_0(X42,X44),X43)) ),
    inference(forward_demodulation,[],[f24625,f20])).

fof(f24625,plain,(
    ! [X43,X44,X42] : k5_xboole_0(k4_xboole_0(X42,X43),k4_xboole_0(X42,k2_xboole_0(X44,X43))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X42,k2_xboole_0(X44,X43)),k4_xboole_0(X42,X43)),k4_xboole_0(k3_xboole_0(X42,X44),X43)) ),
    inference(superposition,[],[f34,f1508])).

fof(f1508,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X2,X1),X0) = k4_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(X2,k2_xboole_0(X1,X0))) ),
    inference(superposition,[],[f448,f14])).

fof(f23941,plain,(
    ! [X26,X24,X25] : k2_xboole_0(k4_xboole_0(X25,k2_xboole_0(X24,k2_xboole_0(X26,X25))),k4_xboole_0(k3_xboole_0(X24,X26),X25)) = k5_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(X24,k2_xboole_0(X25,X26))) ),
    inference(forward_demodulation,[],[f23940,f20])).

fof(f23940,plain,(
    ! [X26,X24,X25] : k5_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(k4_xboole_0(X24,X25),X26)) = k2_xboole_0(k4_xboole_0(X25,k2_xboole_0(X24,k2_xboole_0(X26,X25))),k4_xboole_0(k3_xboole_0(X24,X26),X25)) ),
    inference(forward_demodulation,[],[f23939,f23464])).

fof(f23939,plain,(
    ! [X26,X24,X25] : k5_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(k4_xboole_0(X24,X25),X26)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X24,X25),k2_xboole_0(X26,X25)),k4_xboole_0(k3_xboole_0(X24,X26),X25)) ),
    inference(forward_demodulation,[],[f23938,f20775])).

fof(f20775,plain,(
    ! [X24,X23,X25,X22] : k4_xboole_0(k3_xboole_0(X22,X23),k2_xboole_0(X24,X25)) = k4_xboole_0(X22,k2_xboole_0(X25,k2_xboole_0(k4_xboole_0(X22,X23),X24))) ),
    inference(superposition,[],[f1068,f60])).

fof(f23938,plain,(
    ! [X26,X24,X25] : k5_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(k4_xboole_0(X24,X25),X26)) = k2_xboole_0(k4_xboole_0(X24,k2_xboole_0(X25,k2_xboole_0(k4_xboole_0(X24,X25),X26))),k4_xboole_0(k3_xboole_0(X24,X26),X25)) ),
    inference(forward_demodulation,[],[f23578,f443])).

fof(f23578,plain,(
    ! [X26,X24,X25] : k5_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(k4_xboole_0(X24,X25),X26)) = k2_xboole_0(k4_xboole_0(X24,k2_xboole_0(X25,k2_xboole_0(k4_xboole_0(X24,X25),X26))),k3_xboole_0(k4_xboole_0(X24,X25),X26)) ),
    inference(superposition,[],[f1244,f20])).

fof(f1244,plain,(
    ! [X0,X1] : k5_xboole_0(X1,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X1,X0)),k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f134,f14])).

fof(f26656,plain,(
    ! [X80,X78,X79] : k5_xboole_0(k4_xboole_0(X78,X79),k5_xboole_0(k4_xboole_0(X78,X79),k4_xboole_0(X78,k2_xboole_0(X79,X80)))) = k5_xboole_0(k2_xboole_0(X79,X78),k2_xboole_0(X79,k3_xboole_0(X78,X80))) ),
    inference(forward_demodulation,[],[f26655,f2638])).

fof(f26655,plain,(
    ! [X80,X78,X79] : k5_xboole_0(k4_xboole_0(X78,X79),k5_xboole_0(k4_xboole_0(X78,X79),k4_xboole_0(X78,k2_xboole_0(X79,X80)))) = k5_xboole_0(k4_xboole_0(X78,X79),k4_xboole_0(k3_xboole_0(X78,X80),X79)) ),
    inference(forward_demodulation,[],[f26537,f443])).

fof(f26537,plain,(
    ! [X80,X78,X79] : k5_xboole_0(k4_xboole_0(X78,X79),k3_xboole_0(k4_xboole_0(X78,X79),X80)) = k5_xboole_0(k4_xboole_0(X78,X79),k5_xboole_0(k4_xboole_0(X78,X79),k4_xboole_0(X78,k2_xboole_0(X79,X80)))) ),
    inference(superposition,[],[f26072,f20])).

fof(f26072,plain,(
    ! [X21,X22] : k5_xboole_0(X21,k5_xboole_0(X21,k4_xboole_0(X21,X22))) = k5_xboole_0(X21,k3_xboole_0(X21,X22)) ),
    inference(backward_demodulation,[],[f7751,f26035])).

fof(f26035,plain,(
    ! [X61,X62] : k5_xboole_0(X61,k3_xboole_0(X61,X62)) = k5_xboole_0(k3_xboole_0(X61,X62),k2_xboole_0(X61,k4_xboole_0(X61,X62))) ),
    inference(backward_demodulation,[],[f11507,f26014])).

fof(f26014,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X3,X4)) = k2_xboole_0(X3,k3_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f25779,f66])).

fof(f25779,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k3_xboole_0(X3,X4)) = k2_xboole_0(X3,k4_xboole_0(X3,k2_xboole_0(X4,X3))) ),
    inference(superposition,[],[f15,f25363])).

fof(f11507,plain,(
    ! [X61,X62] : k5_xboole_0(k3_xboole_0(X61,X62),k2_xboole_0(X61,k3_xboole_0(X61,X62))) = k5_xboole_0(X61,k3_xboole_0(X61,X62)) ),
    inference(forward_demodulation,[],[f11506,f18])).

fof(f11506,plain,(
    ! [X61,X62] : k5_xboole_0(k3_xboole_0(X61,X62),k2_xboole_0(X61,k3_xboole_0(X61,X62))) = k2_xboole_0(k4_xboole_0(X61,k3_xboole_0(X61,X62)),k4_xboole_0(k3_xboole_0(X61,X62),X61)) ),
    inference(forward_demodulation,[],[f11505,f100])).

fof(f11505,plain,(
    ! [X61,X62] : k5_xboole_0(k3_xboole_0(X61,X62),k2_xboole_0(X61,k3_xboole_0(X61,X62))) = k2_xboole_0(k4_xboole_0(X61,k2_xboole_0(k3_xboole_0(X61,X62),k3_xboole_0(X61,X62))),k4_xboole_0(k3_xboole_0(X61,X62),X61)) ),
    inference(forward_demodulation,[],[f11504,f20])).

fof(f11504,plain,(
    ! [X61,X62] : k5_xboole_0(k3_xboole_0(X61,X62),k2_xboole_0(X61,k3_xboole_0(X61,X62))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X61,k3_xboole_0(X61,X62)),k3_xboole_0(X61,X62)),k4_xboole_0(k3_xboole_0(X61,X62),X61)) ),
    inference(forward_demodulation,[],[f11503,f8042])).

fof(f8042,plain,(
    ! [X4,X3] : k4_xboole_0(k3_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k2_xboole_0(X3,k3_xboole_0(X3,X4))) ),
    inference(forward_demodulation,[],[f8039,f355])).

fof(f8039,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k2_xboole_0(X3,k3_xboole_0(X3,X4))) = k4_xboole_0(X3,k2_xboole_0(X3,k4_xboole_0(X3,X4))) ),
    inference(backward_demodulation,[],[f8015,f8038])).

fof(f8038,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k4_xboole_0(k3_xboole_0(X5,X5),X6)) = k2_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f7860,f419])).

fof(f7860,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k4_xboole_0(k3_xboole_0(X5,X5),X6)) = k2_xboole_0(X5,k4_xboole_0(X5,k2_xboole_0(X5,X6))) ),
    inference(superposition,[],[f419,f5924])).

fof(f8015,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k2_xboole_0(X3,k4_xboole_0(k3_xboole_0(X3,X3),X4))) = k4_xboole_0(X3,k2_xboole_0(X3,k3_xboole_0(X3,X4))) ),
    inference(forward_demodulation,[],[f8014,f1479])).

fof(f8014,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k2_xboole_0(X3,k4_xboole_0(k3_xboole_0(X3,X3),X4))) = k4_xboole_0(X3,k2_xboole_0(k3_xboole_0(X3,X4),X3)) ),
    inference(forward_demodulation,[],[f7852,f5505])).

fof(f5505,plain,(
    ! [X10,X8,X9] : k4_xboole_0(k3_xboole_0(k3_xboole_0(X8,X9),X10),X9) = k4_xboole_0(X9,k2_xboole_0(k3_xboole_0(X8,X10),X9)) ),
    inference(backward_demodulation,[],[f3806,f5484])).

fof(f3806,plain,(
    ! [X10,X8,X9] : k4_xboole_0(k4_xboole_0(k3_xboole_0(X8,X10),X9),k4_xboole_0(k3_xboole_0(X8,X10),X9)) = k4_xboole_0(k3_xboole_0(k3_xboole_0(X8,X9),X10),X9) ),
    inference(forward_demodulation,[],[f3805,f3685])).

fof(f3685,plain,(
    ! [X121,X118,X120,X119] : k4_xboole_0(k3_xboole_0(X118,X121),k2_xboole_0(X119,k4_xboole_0(X118,X120))) = k4_xboole_0(k3_xboole_0(k3_xboole_0(X118,X120),X121),X119) ),
    inference(forward_demodulation,[],[f3596,f443])).

fof(f3596,plain,(
    ! [X121,X118,X120,X119] : k4_xboole_0(k3_xboole_0(X118,X121),k2_xboole_0(X119,k4_xboole_0(X118,X120))) = k3_xboole_0(k4_xboole_0(k3_xboole_0(X118,X120),X119),X121) ),
    inference(superposition,[],[f443,f355])).

fof(f3805,plain,(
    ! [X10,X8,X9] : k4_xboole_0(k4_xboole_0(k3_xboole_0(X8,X10),X9),k4_xboole_0(k3_xboole_0(X8,X10),X9)) = k4_xboole_0(k3_xboole_0(X8,X10),k2_xboole_0(X9,k4_xboole_0(X8,X9))) ),
    inference(forward_demodulation,[],[f3761,f20])).

fof(f3761,plain,(
    ! [X10,X8,X9] : k4_xboole_0(k4_xboole_0(k3_xboole_0(X8,X10),X9),k4_xboole_0(k3_xboole_0(X8,X10),X9)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X8,X10),X9),k4_xboole_0(X8,X9)) ),
    inference(superposition,[],[f383,f443])).

fof(f7852,plain,(
    ! [X4,X3] : k4_xboole_0(k3_xboole_0(k3_xboole_0(X3,X3),X4),X3) = k4_xboole_0(X3,k2_xboole_0(X3,k4_xboole_0(k3_xboole_0(X3,X3),X4))) ),
    inference(superposition,[],[f5924,f355])).

fof(f11503,plain,(
    ! [X61,X62] : k5_xboole_0(k3_xboole_0(X61,X62),k2_xboole_0(X61,k3_xboole_0(X61,X62))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X61,k3_xboole_0(X61,X62)),k3_xboole_0(X61,X62)),k4_xboole_0(X61,k2_xboole_0(X61,k3_xboole_0(X61,X62)))) ),
    inference(forward_demodulation,[],[f11502,f1479])).

fof(f11502,plain,(
    ! [X61,X62] : k5_xboole_0(k3_xboole_0(X61,X62),k2_xboole_0(X61,k3_xboole_0(X61,X62))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X61,k3_xboole_0(X61,X62)),k3_xboole_0(X61,X62)),k4_xboole_0(X61,k2_xboole_0(k3_xboole_0(X61,X62),X61))) ),
    inference(forward_demodulation,[],[f11501,f5482])).

fof(f11501,plain,(
    ! [X61,X62] : k5_xboole_0(k3_xboole_0(X61,X62),k2_xboole_0(X61,k3_xboole_0(X61,X62))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X61,k3_xboole_0(X61,X62)),k3_xboole_0(X61,X62)),k4_xboole_0(k3_xboole_0(k3_xboole_0(X61,X62),X61),X61)) ),
    inference(forward_demodulation,[],[f11429,f353])).

fof(f11429,plain,(
    ! [X61,X62] : k5_xboole_0(k3_xboole_0(X61,X62),k2_xboole_0(X61,k3_xboole_0(X61,X62))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X61,k3_xboole_0(X61,X62)),k3_xboole_0(X61,X62)),k4_xboole_0(k3_xboole_0(X61,X62),k2_xboole_0(X61,k3_xboole_0(X61,X62)))) ),
    inference(superposition,[],[f112,f311])).

fof(f311,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k3_xboole_0(X6,X7)) = k2_xboole_0(k3_xboole_0(X6,X7),k4_xboole_0(X6,k3_xboole_0(X6,X7))) ),
    inference(forward_demodulation,[],[f292,f27])).

fof(f292,plain,(
    ! [X6,X7] : k2_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,k4_xboole_0(X6,X7))) = k2_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(superposition,[],[f29,f17])).

fof(f112,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k2_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,k2_xboole_0(X2,X3))) ),
    inference(superposition,[],[f34,f21])).

fof(f7751,plain,(
    ! [X21,X22] : k5_xboole_0(k3_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))) = k5_xboole_0(X21,k5_xboole_0(X21,k4_xboole_0(X21,X22))) ),
    inference(backward_demodulation,[],[f5634,f7749])).

fof(f7749,plain,(
    ! [X14,X15] : k5_xboole_0(X14,k5_xboole_0(X14,X15)) = k5_xboole_0(k4_xboole_0(X14,X14),X15) ),
    inference(forward_demodulation,[],[f7715,f19])).

fof(f7715,plain,(
    ! [X14,X15] : k5_xboole_0(k4_xboole_0(X14,X14),X15) = k5_xboole_0(k5_xboole_0(X14,X14),X15) ),
    inference(superposition,[],[f7516,f34])).

fof(f5634,plain,(
    ! [X21,X22] : k5_xboole_0(k3_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))) = k5_xboole_0(k4_xboole_0(X21,X21),k4_xboole_0(X21,X22)) ),
    inference(forward_demodulation,[],[f5617,f3655])).

fof(f3655,plain,(
    ! [X4,X2,X3] : k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X4)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X2,X4),X3),k4_xboole_0(k3_xboole_0(X2,X3),X4)) ),
    inference(forward_demodulation,[],[f3654,f355])).

fof(f3654,plain,(
    ! [X4,X2,X3] : k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X4)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X2,X4),X3),k4_xboole_0(X2,k2_xboole_0(X4,k4_xboole_0(X2,X3)))) ),
    inference(forward_demodulation,[],[f3559,f20])).

fof(f3559,plain,(
    ! [X4,X2,X3] : k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X4)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X2,X4),X3),k4_xboole_0(k4_xboole_0(X2,X4),k4_xboole_0(X2,X3))) ),
    inference(superposition,[],[f64,f355])).

fof(f5617,plain,(
    ! [X21,X22] : k5_xboole_0(k3_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X21,X22),X21),k4_xboole_0(k3_xboole_0(X21,X21),X22)) ),
    inference(backward_demodulation,[],[f5510,f5562])).

fof(f5510,plain,(
    ! [X21,X22] : k5_xboole_0(k3_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X21,X22),X21),k4_xboole_0(X21,k2_xboole_0(X22,k4_xboole_0(X22,X21)))) ),
    inference(backward_demodulation,[],[f696,f5507])).

fof(f696,plain,(
    ! [X21,X22] : k5_xboole_0(k3_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X21,X22),X21),k4_xboole_0(X21,k2_xboole_0(X22,k3_xboole_0(X21,X22)))) ),
    inference(forward_demodulation,[],[f695,f385])).

fof(f695,plain,(
    ! [X21,X22] : k5_xboole_0(k3_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))),k4_xboole_0(X21,k2_xboole_0(X22,k3_xboole_0(X21,X22)))) ),
    inference(forward_demodulation,[],[f642,f20])).

fof(f642,plain,(
    ! [X21,X22] : k5_xboole_0(k3_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))),k4_xboole_0(k4_xboole_0(X21,X22),k3_xboole_0(X21,X22))) ),
    inference(superposition,[],[f32,f29])).

fof(f27322,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(k4_xboole_0(X2,X3),X3)) = k5_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(k2_xboole_0(X3,X2),k2_xboole_0(X3,k4_xboole_0(X2,X3)))) ),
    inference(superposition,[],[f26072,f2638])).

fof(f59139,plain,(
    ! [X196,X195] : k5_xboole_0(k2_xboole_0(X195,X196),k3_xboole_0(k2_xboole_0(X195,X196),k4_xboole_0(X196,k2_xboole_0(X195,X196)))) = k5_xboole_0(X196,k5_xboole_0(k2_xboole_0(X196,X195),k2_xboole_0(X196,k4_xboole_0(X196,X195)))) ),
    inference(forward_demodulation,[],[f59138,f49830])).

fof(f49830,plain,(
    ! [X6,X8,X7] : k5_xboole_0(k2_xboole_0(X6,X7),k5_xboole_0(X7,X8)) = k5_xboole_0(X7,k5_xboole_0(k2_xboole_0(X7,X6),X8)) ),
    inference(forward_demodulation,[],[f49705,f19])).

fof(f49705,plain,(
    ! [X6,X8,X7] : k5_xboole_0(k2_xboole_0(X6,X7),k5_xboole_0(X7,X8)) = k5_xboole_0(k5_xboole_0(X7,k2_xboole_0(X7,X6)),X8) ),
    inference(superposition,[],[f19,f7547])).

fof(f7547,plain,(
    ! [X8,X7] : k5_xboole_0(X7,k2_xboole_0(X7,X8)) = k5_xboole_0(k2_xboole_0(X8,X7),X7) ),
    inference(forward_demodulation,[],[f7546,f6545])).

fof(f6545,plain,(
    ! [X21,X22] : k2_xboole_0(k4_xboole_0(X21,k2_xboole_0(X22,X21)),k4_xboole_0(k3_xboole_0(X21,X21),X22)) = k5_xboole_0(X22,k2_xboole_0(X22,X21)) ),
    inference(backward_demodulation,[],[f5591,f6544])).

fof(f6544,plain,(
    ! [X26,X27] : k5_xboole_0(k2_xboole_0(X27,X26),k4_xboole_0(X27,k4_xboole_0(X26,X27))) = k5_xboole_0(X27,k2_xboole_0(X27,X26)) ),
    inference(forward_demodulation,[],[f6481,f211])).

fof(f6481,plain,(
    ! [X26,X27] : k5_xboole_0(X27,k2_xboole_0(k4_xboole_0(X26,X27),X27)) = k5_xboole_0(k2_xboole_0(X27,X26),k4_xboole_0(X27,k4_xboole_0(X26,X27))) ),
    inference(superposition,[],[f995,f109])).

fof(f995,plain,(
    ! [X21,X22] : k5_xboole_0(k5_xboole_0(X21,X22),k4_xboole_0(X22,X21)) = k5_xboole_0(X22,k2_xboole_0(X21,X22)) ),
    inference(forward_demodulation,[],[f994,f692])).

fof(f692,plain,(
    ! [X17,X18] : k2_xboole_0(k4_xboole_0(X18,k2_xboole_0(X17,k5_xboole_0(X17,X18))),k4_xboole_0(X17,k2_xboole_0(X18,k4_xboole_0(X18,X17)))) = k5_xboole_0(X18,k2_xboole_0(X17,X18)) ),
    inference(forward_demodulation,[],[f691,f130])).

fof(f691,plain,(
    ! [X17,X18] : k2_xboole_0(k4_xboole_0(X18,k2_xboole_0(X17,k5_xboole_0(X17,X18))),k4_xboole_0(X17,k2_xboole_0(X18,k4_xboole_0(X18,X17)))) = k5_xboole_0(k2_xboole_0(X17,X18),X18) ),
    inference(forward_demodulation,[],[f690,f336])).

fof(f690,plain,(
    ! [X17,X18] : k5_xboole_0(k4_xboole_0(X18,X17),k5_xboole_0(X17,X18)) = k2_xboole_0(k4_xboole_0(X18,k2_xboole_0(X17,k5_xboole_0(X17,X18))),k4_xboole_0(X17,k2_xboole_0(X18,k4_xboole_0(X18,X17)))) ),
    inference(forward_demodulation,[],[f689,f20])).

fof(f689,plain,(
    ! [X17,X18] : k5_xboole_0(k4_xboole_0(X18,X17),k5_xboole_0(X17,X18)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X18,X17),k5_xboole_0(X17,X18)),k4_xboole_0(X17,k2_xboole_0(X18,k4_xboole_0(X18,X17)))) ),
    inference(forward_demodulation,[],[f640,f20])).

fof(f640,plain,(
    ! [X17,X18] : k5_xboole_0(k4_xboole_0(X18,X17),k5_xboole_0(X17,X18)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X18,X17),k5_xboole_0(X17,X18)),k4_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X18,X17))) ),
    inference(superposition,[],[f32,f18])).

fof(f994,plain,(
    ! [X21,X22] : k5_xboole_0(k5_xboole_0(X21,X22),k4_xboole_0(X22,X21)) = k2_xboole_0(k4_xboole_0(X22,k2_xboole_0(X21,k5_xboole_0(X21,X22))),k4_xboole_0(X21,k2_xboole_0(X22,k4_xboole_0(X22,X21)))) ),
    inference(forward_demodulation,[],[f933,f20])).

fof(f933,plain,(
    ! [X21,X22] : k5_xboole_0(k5_xboole_0(X21,X22),k4_xboole_0(X22,X21)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X22,X21),k5_xboole_0(X21,X22)),k4_xboole_0(X21,k2_xboole_0(X22,k4_xboole_0(X22,X21)))) ),
    inference(superposition,[],[f34,f41])).

fof(f5591,plain,(
    ! [X21,X22] : k5_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(X22,k4_xboole_0(X21,X22))) = k2_xboole_0(k4_xboole_0(X21,k2_xboole_0(X22,X21)),k4_xboole_0(k3_xboole_0(X21,X21),X22)) ),
    inference(backward_demodulation,[],[f1323,f5562])).

fof(f1323,plain,(
    ! [X21,X22] : k2_xboole_0(k4_xboole_0(X21,k2_xboole_0(X22,X21)),k4_xboole_0(X21,k2_xboole_0(X22,k4_xboole_0(X22,X21)))) = k5_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(X22,k4_xboole_0(X21,X22))) ),
    inference(forward_demodulation,[],[f1322,f23])).

fof(f1322,plain,(
    ! [X21,X22] : k5_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(X21,X22))) = k2_xboole_0(k4_xboole_0(X21,k2_xboole_0(X22,X21)),k4_xboole_0(X21,k2_xboole_0(X22,k4_xboole_0(X22,X21)))) ),
    inference(forward_demodulation,[],[f1321,f69])).

fof(f1321,plain,(
    ! [X21,X22] : k5_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(X21,X22))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X22,X21),k2_xboole_0(X22,X21)),k4_xboole_0(X21,k2_xboole_0(X22,k4_xboole_0(X22,X21)))) ),
    inference(forward_demodulation,[],[f1254,f951])).

fof(f1254,plain,(
    ! [X21,X22] : k5_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(X21,X22))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X22,X21),k2_xboole_0(X22,X21)),k3_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(X21,X22))) ),
    inference(superposition,[],[f134,f82])).

fof(f7546,plain,(
    ! [X8,X7] : k5_xboole_0(k2_xboole_0(X8,X7),X7) = k2_xboole_0(k4_xboole_0(X8,k2_xboole_0(X7,X8)),k4_xboole_0(k3_xboole_0(X8,X8),X7)) ),
    inference(forward_demodulation,[],[f7545,f5482])).

fof(f7545,plain,(
    ! [X8,X7] : k5_xboole_0(k2_xboole_0(X8,X7),X7) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X7,X8),X8),k4_xboole_0(k3_xboole_0(X8,X8),X7)) ),
    inference(forward_demodulation,[],[f7544,f515])).

fof(f7544,plain,(
    ! [X8,X7] : k5_xboole_0(k2_xboole_0(X8,X7),X7) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X7,X8),X8),k4_xboole_0(k3_xboole_0(k2_xboole_0(X8,X7),X8),X7)) ),
    inference(forward_demodulation,[],[f7419,f1593])).

fof(f1593,plain,(
    ! [X14,X15,X13] : k4_xboole_0(k3_xboole_0(X15,k2_xboole_0(X14,X13)),X13) = k4_xboole_0(k3_xboole_0(X15,X14),X13) ),
    inference(forward_demodulation,[],[f1512,f1508])).

fof(f1512,plain,(
    ! [X14,X15,X13] : k4_xboole_0(k3_xboole_0(X15,k2_xboole_0(X14,X13)),X13) = k4_xboole_0(k4_xboole_0(X15,X13),k4_xboole_0(X15,k2_xboole_0(X14,X13))) ),
    inference(superposition,[],[f448,f160])).

fof(f7419,plain,(
    ! [X8,X7] : k5_xboole_0(k2_xboole_0(X8,X7),X7) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X7,X8),X8),k4_xboole_0(k3_xboole_0(k2_xboole_0(X8,X7),k2_xboole_0(X8,X7)),X7)) ),
    inference(superposition,[],[f5579,f353])).

fof(f59138,plain,(
    ! [X196,X195] : k5_xboole_0(k2_xboole_0(X195,X196),k3_xboole_0(k2_xboole_0(X195,X196),k4_xboole_0(X196,k2_xboole_0(X195,X196)))) = k5_xboole_0(k2_xboole_0(X195,X196),k5_xboole_0(X196,k2_xboole_0(X196,k4_xboole_0(X196,X195)))) ),
    inference(forward_demodulation,[],[f58451,f59034])).

fof(f59034,plain,(
    ! [X140,X139] : k5_xboole_0(k2_xboole_0(X139,X140),k3_xboole_0(k2_xboole_0(X140,X139),k2_xboole_0(X139,X140))) = k5_xboole_0(X140,k2_xboole_0(X140,k4_xboole_0(X140,X139))) ),
    inference(forward_demodulation,[],[f59033,f43400])).

fof(f43400,plain,(
    ! [X52,X53] : k5_xboole_0(X53,k3_xboole_0(X53,k2_xboole_0(X52,X53))) = k5_xboole_0(X53,k2_xboole_0(X53,k4_xboole_0(X53,X52))) ),
    inference(backward_demodulation,[],[f37749,f43399])).

fof(f43399,plain,(
    ! [X56,X55] : k5_xboole_0(k5_xboole_0(X55,k2_xboole_0(X56,X55)),k4_xboole_0(X56,X55)) = k5_xboole_0(X55,k2_xboole_0(X55,k4_xboole_0(X55,X56))) ),
    inference(forward_demodulation,[],[f43398,f25384])).

fof(f25384,plain,(
    ! [X57,X58] : k5_xboole_0(X58,k2_xboole_0(X58,k4_xboole_0(X58,X57))) = k2_xboole_0(k4_xboole_0(X57,k2_xboole_0(X58,X57)),k4_xboole_0(X58,k2_xboole_0(X57,X58))) ),
    inference(backward_demodulation,[],[f10425,f25363])).

fof(f10425,plain,(
    ! [X57,X58] : k5_xboole_0(X58,k2_xboole_0(X58,k4_xboole_0(X58,X57))) = k2_xboole_0(k4_xboole_0(X57,k2_xboole_0(X58,X57)),k4_xboole_0(k3_xboole_0(X58,X57),X58)) ),
    inference(forward_demodulation,[],[f10424,f355])).

fof(f10424,plain,(
    ! [X57,X58] : k5_xboole_0(X58,k2_xboole_0(X58,k4_xboole_0(X58,X57))) = k2_xboole_0(k4_xboole_0(X57,k2_xboole_0(X58,X57)),k4_xboole_0(X58,k2_xboole_0(X58,k4_xboole_0(X58,X57)))) ),
    inference(forward_demodulation,[],[f10423,f5731])).

fof(f10423,plain,(
    ! [X57,X58] : k5_xboole_0(X58,k2_xboole_0(X58,k3_xboole_0(X57,X58))) = k2_xboole_0(k4_xboole_0(X57,k2_xboole_0(X58,X57)),k4_xboole_0(X58,k2_xboole_0(X58,k3_xboole_0(X57,X58)))) ),
    inference(forward_demodulation,[],[f10422,f14])).

fof(f10422,plain,(
    ! [X57,X58] : k2_xboole_0(k4_xboole_0(X57,k2_xboole_0(X58,X57)),k4_xboole_0(X58,k2_xboole_0(X58,k3_xboole_0(X57,X58)))) = k5_xboole_0(X58,k2_xboole_0(k3_xboole_0(X57,X58),X58)) ),
    inference(forward_demodulation,[],[f10211,f1479])).

fof(f10211,plain,(
    ! [X57,X58] : k5_xboole_0(X58,k2_xboole_0(k3_xboole_0(X57,X58),X58)) = k2_xboole_0(k4_xboole_0(X57,k2_xboole_0(X58,X57)),k4_xboole_0(X58,k2_xboole_0(k3_xboole_0(X57,X58),X58))) ),
    inference(superposition,[],[f111,f353])).

fof(f43398,plain,(
    ! [X56,X55] : k5_xboole_0(k5_xboole_0(X55,k2_xboole_0(X56,X55)),k4_xboole_0(X56,X55)) = k2_xboole_0(k4_xboole_0(X56,k2_xboole_0(X55,X56)),k4_xboole_0(X55,k2_xboole_0(X56,X55))) ),
    inference(forward_demodulation,[],[f43397,f17763])).

fof(f17763,plain,(
    ! [X64,X65] : k4_xboole_0(X65,k2_xboole_0(X64,X65)) = k4_xboole_0(X65,k2_xboole_0(X64,k5_xboole_0(X64,k2_xboole_0(X65,X64)))) ),
    inference(backward_demodulation,[],[f8409,f17762])).

fof(f17762,plain,(
    ! [X123,X122] : k4_xboole_0(X123,k2_xboole_0(X122,X123)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X123,X123),X122),k5_xboole_0(X122,k2_xboole_0(X123,X122))) ),
    inference(forward_demodulation,[],[f17761,f1589])).

fof(f17761,plain,(
    ! [X123,X122] : k4_xboole_0(X123,k2_xboole_0(X122,X123)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X123,k4_xboole_0(X123,X122)),X122),k5_xboole_0(X122,k2_xboole_0(X123,X122))) ),
    inference(forward_demodulation,[],[f17760,f443])).

fof(f17760,plain,(
    ! [X123,X122] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X123,X122),k4_xboole_0(X123,X122)),k5_xboole_0(X122,k2_xboole_0(X123,X122))) = k4_xboole_0(X123,k2_xboole_0(X122,X123)) ),
    inference(forward_demodulation,[],[f17759,f5925])).

fof(f17759,plain,(
    ! [X123,X122] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X123,X122),k4_xboole_0(X123,X122)),k5_xboole_0(X122,k2_xboole_0(X123,X122))) = k4_xboole_0(k3_xboole_0(X123,X123),k2_xboole_0(X122,X123)) ),
    inference(forward_demodulation,[],[f17758,f608])).

fof(f608,plain,(
    ! [X57,X54,X56,X55] : k4_xboole_0(k3_xboole_0(k2_xboole_0(X54,X55),X57),k2_xboole_0(X55,X56)) = k4_xboole_0(k3_xboole_0(X54,X57),k2_xboole_0(X55,X56)) ),
    inference(forward_demodulation,[],[f590,f443])).

fof(f590,plain,(
    ! [X57,X54,X56,X55] : k4_xboole_0(k3_xboole_0(k2_xboole_0(X54,X55),X57),k2_xboole_0(X55,X56)) = k3_xboole_0(k4_xboole_0(X54,k2_xboole_0(X55,X56)),X57) ),
    inference(superposition,[],[f443,f68])).

fof(f17758,plain,(
    ! [X123,X122] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X123,X122),k4_xboole_0(X123,X122)),k5_xboole_0(X122,k2_xboole_0(X123,X122))) = k4_xboole_0(k3_xboole_0(k2_xboole_0(X123,X122),X123),k2_xboole_0(X122,X123)) ),
    inference(forward_demodulation,[],[f17757,f3512])).

fof(f17757,plain,(
    ! [X123,X122] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X123,X122),k4_xboole_0(X123,X122)),k5_xboole_0(X122,k2_xboole_0(X123,X122))) = k4_xboole_0(k3_xboole_0(k2_xboole_0(X123,X122),k2_xboole_0(X123,X122)),k2_xboole_0(X122,X123)) ),
    inference(forward_demodulation,[],[f17756,f7132])).

fof(f17756,plain,(
    ! [X123,X122] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X123,X122),k4_xboole_0(X123,X122)),k5_xboole_0(X122,k2_xboole_0(X123,X122))) = k4_xboole_0(k5_xboole_0(k2_xboole_0(X122,X123),k2_xboole_0(X123,X122)),k4_xboole_0(X122,k2_xboole_0(X123,X122))) ),
    inference(forward_demodulation,[],[f17240,f336])).

fof(f17240,plain,(
    ! [X123,X122] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X123,X122),k4_xboole_0(X123,X122)),k5_xboole_0(X122,k2_xboole_0(X123,X122))) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X123,X122),k5_xboole_0(X122,k2_xboole_0(X123,X122))),k4_xboole_0(X122,k2_xboole_0(X123,X122))) ),
    inference(superposition,[],[f5563,f734])).

fof(f8409,plain,(
    ! [X64,X65] : k4_xboole_0(k4_xboole_0(k3_xboole_0(X65,X65),X64),k5_xboole_0(X64,k2_xboole_0(X65,X64))) = k4_xboole_0(X65,k2_xboole_0(X64,k5_xboole_0(X64,k2_xboole_0(X65,X64)))) ),
    inference(forward_demodulation,[],[f8408,f20])).

fof(f8408,plain,(
    ! [X64,X65] : k4_xboole_0(k4_xboole_0(X65,X64),k5_xboole_0(X64,k2_xboole_0(X65,X64))) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X65,X65),X64),k5_xboole_0(X64,k2_xboole_0(X65,X64))) ),
    inference(forward_demodulation,[],[f8407,f1589])).

fof(f8407,plain,(
    ! [X64,X65] : k4_xboole_0(k4_xboole_0(X65,X64),k5_xboole_0(X64,k2_xboole_0(X65,X64))) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X65,k4_xboole_0(X65,X64)),X64),k5_xboole_0(X64,k2_xboole_0(X65,X64))) ),
    inference(forward_demodulation,[],[f8295,f443])).

fof(f8295,plain,(
    ! [X64,X65] : k4_xboole_0(k4_xboole_0(X65,X64),k5_xboole_0(X64,k2_xboole_0(X65,X64))) = k4_xboole_0(k3_xboole_0(k4_xboole_0(X65,X64),k4_xboole_0(X65,X64)),k5_xboole_0(X64,k2_xboole_0(X65,X64))) ),
    inference(superposition,[],[f5925,f32])).

fof(f43397,plain,(
    ! [X56,X55] : k5_xboole_0(k5_xboole_0(X55,k2_xboole_0(X56,X55)),k4_xboole_0(X56,X55)) = k2_xboole_0(k4_xboole_0(X56,k2_xboole_0(X55,k5_xboole_0(X55,k2_xboole_0(X56,X55)))),k4_xboole_0(X55,k2_xboole_0(X56,X55))) ),
    inference(forward_demodulation,[],[f43396,f20])).

fof(f43396,plain,(
    ! [X56,X55] : k5_xboole_0(k5_xboole_0(X55,k2_xboole_0(X56,X55)),k4_xboole_0(X56,X55)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X56,X55),k5_xboole_0(X55,k2_xboole_0(X56,X55))),k4_xboole_0(X55,k2_xboole_0(X56,X55))) ),
    inference(forward_demodulation,[],[f42649,f32545])).

fof(f32545,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k2_xboole_0(X11,X10)) = k4_xboole_0(k5_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(X11,k3_xboole_0(X11,X10))) ),
    inference(backward_demodulation,[],[f7944,f32479])).

fof(f7944,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k2_xboole_0(X11,X10)) = k4_xboole_0(k5_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(k3_xboole_0(X11,X11),X10)) ),
    inference(backward_demodulation,[],[f5600,f7927])).

fof(f5600,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k2_xboole_0(X11,k5_xboole_0(X10,X11))) = k4_xboole_0(k5_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(k3_xboole_0(X11,X11),X10)) ),
    inference(backward_demodulation,[],[f2305,f5562])).

fof(f2305,plain,(
    ! [X10,X11] : k4_xboole_0(k5_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(X10,k2_xboole_0(X11,k5_xboole_0(X10,X11))) ),
    inference(backward_demodulation,[],[f741,f2303])).

fof(f42649,plain,(
    ! [X56,X55] : k5_xboole_0(k5_xboole_0(X55,k2_xboole_0(X56,X55)),k4_xboole_0(X56,X55)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X56,X55),k5_xboole_0(X55,k2_xboole_0(X56,X55))),k4_xboole_0(k5_xboole_0(X55,k2_xboole_0(X56,X55)),k4_xboole_0(X56,k3_xboole_0(X56,X55)))) ),
    inference(superposition,[],[f32492,f32488])).

fof(f32488,plain,(
    ! [X30,X29] : k3_xboole_0(k5_xboole_0(X29,k2_xboole_0(X30,X29)),k4_xboole_0(X30,X29)) = k4_xboole_0(X30,k3_xboole_0(X30,X29)) ),
    inference(backward_demodulation,[],[f5570,f32479])).

fof(f5570,plain,(
    ! [X30,X29] : k3_xboole_0(k5_xboole_0(X29,k2_xboole_0(X30,X29)),k4_xboole_0(X30,X29)) = k4_xboole_0(k3_xboole_0(X30,X30),X29) ),
    inference(backward_demodulation,[],[f750,f5562])).

fof(f750,plain,(
    ! [X30,X29] : k3_xboole_0(k5_xboole_0(X29,k2_xboole_0(X30,X29)),k4_xboole_0(X30,X29)) = k4_xboole_0(X30,k2_xboole_0(X29,k4_xboole_0(X29,X30))) ),
    inference(forward_demodulation,[],[f749,f66])).

fof(f749,plain,(
    ! [X30,X29] : k3_xboole_0(k5_xboole_0(X29,k2_xboole_0(X30,X29)),k4_xboole_0(X30,X29)) = k4_xboole_0(X30,k2_xboole_0(X29,k4_xboole_0(X29,k2_xboole_0(X30,X29)))) ),
    inference(forward_demodulation,[],[f748,f20])).

fof(f748,plain,(
    ! [X30,X29] : k3_xboole_0(k5_xboole_0(X29,k2_xboole_0(X30,X29)),k4_xboole_0(X30,X29)) = k4_xboole_0(k4_xboole_0(X30,X29),k4_xboole_0(X29,k2_xboole_0(X30,X29))) ),
    inference(forward_demodulation,[],[f747,f25])).

fof(f747,plain,(
    ! [X30,X29] : k3_xboole_0(k5_xboole_0(X29,k2_xboole_0(X30,X29)),k4_xboole_0(X30,X29)) = k4_xboole_0(k4_xboole_0(X30,X29),k4_xboole_0(X29,k2_xboole_0(X30,k2_xboole_0(X29,X30)))) ),
    inference(forward_demodulation,[],[f746,f15])).

fof(f746,plain,(
    ! [X30,X29] : k3_xboole_0(k5_xboole_0(X29,k2_xboole_0(X30,X29)),k4_xboole_0(X30,X29)) = k4_xboole_0(k4_xboole_0(X30,X29),k4_xboole_0(X29,k2_xboole_0(X30,k2_xboole_0(X29,k4_xboole_0(X30,X29))))) ),
    inference(forward_demodulation,[],[f745,f71])).

fof(f745,plain,(
    ! [X30,X29] : k3_xboole_0(k5_xboole_0(X29,k2_xboole_0(X30,X29)),k4_xboole_0(X30,X29)) = k4_xboole_0(k4_xboole_0(X30,X29),k4_xboole_0(X29,k2_xboole_0(k2_xboole_0(X30,X29),k4_xboole_0(X30,X29)))) ),
    inference(forward_demodulation,[],[f673,f20])).

fof(f673,plain,(
    ! [X30,X29] : k4_xboole_0(k4_xboole_0(X30,X29),k4_xboole_0(k4_xboole_0(X29,k2_xboole_0(X30,X29)),k4_xboole_0(X30,X29))) = k3_xboole_0(k5_xboole_0(X29,k2_xboole_0(X30,X29)),k4_xboole_0(X30,X29)) ),
    inference(superposition,[],[f193,f32])).

fof(f32492,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f5579,f32479])).

fof(f37749,plain,(
    ! [X52,X53] : k5_xboole_0(X53,k3_xboole_0(X53,k2_xboole_0(X52,X53))) = k5_xboole_0(k5_xboole_0(X53,k2_xboole_0(X52,X53)),k4_xboole_0(X52,X53)) ),
    inference(superposition,[],[f34160,f16])).

fof(f34160,plain,(
    ! [X4,X5] : k5_xboole_0(k5_xboole_0(X4,X5),k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k3_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f34159,f25782])).

fof(f25782,plain,(
    ! [X10,X9] : k5_xboole_0(X9,k3_xboole_0(X9,X10)) = k2_xboole_0(k4_xboole_0(X9,k3_xboole_0(X9,X10)),k4_xboole_0(X9,k2_xboole_0(X10,X9))) ),
    inference(superposition,[],[f18,f25363])).

fof(f34159,plain,(
    ! [X4,X5] : k5_xboole_0(k5_xboole_0(X4,X5),k4_xboole_0(X5,X4)) = k2_xboole_0(k4_xboole_0(X4,k3_xboole_0(X4,X5)),k4_xboole_0(X4,k2_xboole_0(X5,X4))) ),
    inference(forward_demodulation,[],[f33869,f15096])).

fof(f15096,plain,(
    ! [X45,X44] : k4_xboole_0(X44,k2_xboole_0(X45,X44)) = k4_xboole_0(X45,k2_xboole_0(X44,k5_xboole_0(X44,X45))) ),
    inference(forward_demodulation,[],[f15095,f7930])).

fof(f7930,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k2_xboole_0(X8,X7)) = k4_xboole_0(k5_xboole_0(X7,X8),k5_xboole_0(X7,X8)) ),
    inference(backward_demodulation,[],[f2207,f7927])).

fof(f2207,plain,(
    ! [X8,X7] : k4_xboole_0(k5_xboole_0(X7,X8),k5_xboole_0(X7,X8)) = k4_xboole_0(X7,k2_xboole_0(X8,k5_xboole_0(X7,X8))) ),
    inference(forward_demodulation,[],[f2180,f20])).

fof(f2180,plain,(
    ! [X8,X7] : k4_xboole_0(k4_xboole_0(X7,X8),k5_xboole_0(X7,X8)) = k4_xboole_0(k5_xboole_0(X7,X8),k5_xboole_0(X7,X8)) ),
    inference(superposition,[],[f21,f144])).

fof(f144,plain,(
    ! [X2,X3] : k5_xboole_0(X3,X2) = k2_xboole_0(k5_xboole_0(X3,X2),k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f143,f18])).

fof(f143,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3)) = k2_xboole_0(k5_xboole_0(X3,X2),k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f125,f14])).

fof(f125,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X3,X2),k5_xboole_0(X3,X2)) ),
    inference(superposition,[],[f25,f34])).

fof(f15095,plain,(
    ! [X45,X44] : k4_xboole_0(k5_xboole_0(X44,X45),k5_xboole_0(X44,X45)) = k4_xboole_0(X45,k2_xboole_0(X44,k5_xboole_0(X44,X45))) ),
    inference(forward_demodulation,[],[f14973,f1734])).

fof(f14973,plain,(
    ! [X45,X44] : k4_xboole_0(k5_xboole_0(X44,X45),k5_xboole_0(X44,X45)) = k4_xboole_0(k5_xboole_0(X45,X44),k5_xboole_0(X44,X45)) ),
    inference(superposition,[],[f566,f86])).

fof(f566,plain,(
    ! [X24,X23,X22] : k4_xboole_0(X24,k5_xboole_0(X23,X22)) = k4_xboole_0(k2_xboole_0(X24,k4_xboole_0(X22,X23)),k5_xboole_0(X23,X22)) ),
    inference(superposition,[],[f68,f34])).

fof(f33869,plain,(
    ! [X4,X5] : k5_xboole_0(k5_xboole_0(X4,X5),k4_xboole_0(X5,X4)) = k2_xboole_0(k4_xboole_0(X4,k3_xboole_0(X4,X5)),k4_xboole_0(X5,k2_xboole_0(X4,k5_xboole_0(X4,X5)))) ),
    inference(superposition,[],[f63,f32485])).

fof(f59033,plain,(
    ! [X140,X139] : k5_xboole_0(k2_xboole_0(X139,X140),k3_xboole_0(k2_xboole_0(X140,X139),k2_xboole_0(X139,X140))) = k5_xboole_0(X140,k3_xboole_0(X140,k2_xboole_0(X139,X140))) ),
    inference(forward_demodulation,[],[f59032,f37386])).

fof(f37386,plain,(
    ! [X8,X7] : k5_xboole_0(X8,k2_xboole_0(X7,X8)) = k5_xboole_0(X7,k3_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f37385,f284])).

fof(f37385,plain,(
    ! [X8,X7] : k5_xboole_0(X8,k2_xboole_0(X7,X8)) = k5_xboole_0(X7,k3_xboole_0(X7,k2_xboole_0(X8,X8))) ),
    inference(forward_demodulation,[],[f37384,f991])).

fof(f37384,plain,(
    ! [X8,X7] : k5_xboole_0(X7,k3_xboole_0(X7,k2_xboole_0(X8,X8))) = k5_xboole_0(k4_xboole_0(X8,X7),k5_xboole_0(X8,X7)) ),
    inference(forward_demodulation,[],[f37274,f9438])).

fof(f9438,plain,(
    ! [X28,X29] : k4_xboole_0(X28,X29) = k4_xboole_0(k2_xboole_0(X28,X28),X29) ),
    inference(forward_demodulation,[],[f9360,f16])).

fof(f9360,plain,(
    ! [X28,X29] : k4_xboole_0(k2_xboole_0(X28,X28),X29) = k4_xboole_0(k2_xboole_0(X28,X29),X29) ),
    inference(superposition,[],[f16,f7758])).

fof(f37274,plain,(
    ! [X8,X7] : k5_xboole_0(X7,k3_xboole_0(X7,k2_xboole_0(X8,X8))) = k5_xboole_0(k4_xboole_0(k2_xboole_0(X8,X8),X7),k5_xboole_0(X8,X7)) ),
    inference(superposition,[],[f34158,f7527])).

fof(f34158,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X3,X2),k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f34157,f26088])).

fof(f26088,plain,(
    ! [X8,X7] : k2_xboole_0(k4_xboole_0(X7,k2_xboole_0(X8,X7)),k4_xboole_0(X7,k3_xboole_0(X7,X8))) = k5_xboole_0(X7,k3_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f25781,f121])).

fof(f25781,plain,(
    ! [X8,X7] : k5_xboole_0(k3_xboole_0(X7,X8),X7) = k2_xboole_0(k4_xboole_0(X7,k2_xboole_0(X8,X7)),k4_xboole_0(X7,k3_xboole_0(X7,X8))) ),
    inference(superposition,[],[f18,f25363])).

fof(f34157,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X3,X2),k5_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,X2)),k4_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f33868,f15096])).

fof(f33868,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X3,X2),k5_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X2,k5_xboole_0(X2,X3))),k4_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(superposition,[],[f64,f32485])).

fof(f59032,plain,(
    ! [X140,X139] : k5_xboole_0(k2_xboole_0(X139,X140),k3_xboole_0(k2_xboole_0(X140,X139),k2_xboole_0(X139,X140))) = k5_xboole_0(k2_xboole_0(X139,X140),k2_xboole_0(X140,k2_xboole_0(X139,X140))) ),
    inference(forward_demodulation,[],[f59031,f16337])).

fof(f16337,plain,(
    ! [X37,X36] : k5_xboole_0(X37,k2_xboole_0(X36,X37)) = k5_xboole_0(X37,k2_xboole_0(X37,X36)) ),
    inference(forward_demodulation,[],[f16336,f25])).

fof(f16336,plain,(
    ! [X37,X36] : k5_xboole_0(X37,k2_xboole_0(X36,X37)) = k5_xboole_0(X37,k2_xboole_0(X37,k2_xboole_0(X36,X37))) ),
    inference(forward_demodulation,[],[f16130,f18])).

fof(f16130,plain,(
    ! [X37,X36] : k5_xboole_0(X37,k2_xboole_0(X37,k2_xboole_0(X36,X37))) = k2_xboole_0(k4_xboole_0(X37,k2_xboole_0(X36,X37)),k4_xboole_0(k2_xboole_0(X36,X37),X37)) ),
    inference(superposition,[],[f714,f500])).

fof(f500,plain,(
    ! [X14,X13] : k2_xboole_0(X14,X13) = k2_xboole_0(k2_xboole_0(X14,X13),X13) ),
    inference(forward_demodulation,[],[f493,f170])).

fof(f170,plain,(
    ! [X10,X9] : k2_xboole_0(X9,X10) = k2_xboole_0(k2_xboole_0(X9,X10),k2_xboole_0(X9,X10)) ),
    inference(forward_demodulation,[],[f169,f53])).

fof(f169,plain,(
    ! [X10,X9] : k2_xboole_0(X9,k2_xboole_0(X9,X10)) = k2_xboole_0(k2_xboole_0(X9,X10),k2_xboole_0(X9,X10)) ),
    inference(forward_demodulation,[],[f168,f14])).

fof(f168,plain,(
    ! [X10,X9] : k2_xboole_0(k2_xboole_0(X9,X10),X9) = k2_xboole_0(k2_xboole_0(X9,X10),k2_xboole_0(X9,X10)) ),
    inference(superposition,[],[f25,f53])).

fof(f493,plain,(
    ! [X14,X13] : k2_xboole_0(k2_xboole_0(X14,X13),X13) = k2_xboole_0(k2_xboole_0(X14,X13),k2_xboole_0(X14,X13)) ),
    inference(superposition,[],[f25,f160])).

fof(f714,plain,(
    ! [X2,X3] : k5_xboole_0(X3,k2_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X2,X3)),k4_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f713,f25])).

fof(f713,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X2,X3)),k4_xboole_0(X2,X3)) = k5_xboole_0(X3,k2_xboole_0(X3,k2_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f712,f14])).

fof(f712,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X2,X3)),k4_xboole_0(X2,X3)) = k5_xboole_0(X3,k2_xboole_0(k2_xboole_0(X2,X3),X3)) ),
    inference(forward_demodulation,[],[f711,f282])).

fof(f711,plain,(
    ! [X2,X3] : k5_xboole_0(X3,k2_xboole_0(k2_xboole_0(X2,X3),X3)) = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X2,k2_xboole_0(X3,X3))),k4_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f650,f71])).

fof(f650,plain,(
    ! [X2,X3] : k5_xboole_0(X3,k2_xboole_0(k2_xboole_0(X2,X3),X3)) = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(X2,X3),X3)),k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f32,f16])).

fof(f59031,plain,(
    ! [X140,X139] : k5_xboole_0(k2_xboole_0(X139,X140),k3_xboole_0(k2_xboole_0(X140,X139),k2_xboole_0(X139,X140))) = k5_xboole_0(k2_xboole_0(X139,X140),k2_xboole_0(k2_xboole_0(X139,X140),X140)) ),
    inference(forward_demodulation,[],[f59030,f211])).

fof(f59030,plain,(
    ! [X140,X139] : k5_xboole_0(k2_xboole_0(X139,X140),k2_xboole_0(k4_xboole_0(X140,k2_xboole_0(X139,X140)),k2_xboole_0(X139,X140))) = k5_xboole_0(k2_xboole_0(X139,X140),k3_xboole_0(k2_xboole_0(X140,X139),k2_xboole_0(X139,X140))) ),
    inference(forward_demodulation,[],[f59029,f121])).

fof(f59029,plain,(
    ! [X140,X139] : k5_xboole_0(k2_xboole_0(X139,X140),k2_xboole_0(k4_xboole_0(X140,k2_xboole_0(X139,X140)),k2_xboole_0(X139,X140))) = k5_xboole_0(k3_xboole_0(k2_xboole_0(X140,X139),k2_xboole_0(X139,X140)),k2_xboole_0(X139,X140)) ),
    inference(forward_demodulation,[],[f58427,f19314])).

fof(f58427,plain,(
    ! [X140,X139] : k5_xboole_0(k2_xboole_0(X139,X140),k2_xboole_0(k4_xboole_0(X140,k2_xboole_0(X139,X140)),k2_xboole_0(X139,X140))) = k5_xboole_0(k3_xboole_0(k2_xboole_0(X140,X139),k2_xboole_0(X139,X140)),k5_xboole_0(k2_xboole_0(X139,X140),k4_xboole_0(X140,k2_xboole_0(X139,X140)))) ),
    inference(superposition,[],[f991,f250])).

fof(f250,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X7,X6),k4_xboole_0(X6,k2_xboole_0(X7,X6))) = k3_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X7,X6)) ),
    inference(superposition,[],[f193,f25])).

fof(f58451,plain,(
    ! [X196,X195] : k5_xboole_0(k2_xboole_0(X195,X196),k3_xboole_0(k2_xboole_0(X195,X196),k4_xboole_0(X196,k2_xboole_0(X195,X196)))) = k5_xboole_0(k2_xboole_0(X195,X196),k5_xboole_0(k2_xboole_0(X195,X196),k3_xboole_0(k2_xboole_0(X196,X195),k2_xboole_0(X195,X196)))) ),
    inference(superposition,[],[f26072,f250])).

fof(f67737,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK0,k2_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f55,f67736])).

fof(f67736,plain,(
    ! [X107,X106] : k5_xboole_0(X106,k2_xboole_0(X106,X107)) = k5_xboole_0(X107,k3_xboole_0(X106,X107)) ),
    inference(forward_demodulation,[],[f67735,f63363])).

fof(f63363,plain,(
    ! [X19,X20] : k3_xboole_0(X19,X20) = k3_xboole_0(X20,k3_xboole_0(X19,X19)) ),
    inference(forward_demodulation,[],[f63055,f61012])).

fof(f61012,plain,(
    ! [X17,X16] : k3_xboole_0(X16,X17) = k4_xboole_0(X16,k3_xboole_0(X16,k5_xboole_0(k3_xboole_0(X16,X16),X17))) ),
    inference(forward_demodulation,[],[f60871,f33565])).

fof(f33565,plain,(
    ! [X70,X69] : k3_xboole_0(X69,X70) = k3_xboole_0(k3_xboole_0(X69,X69),X70) ),
    inference(forward_demodulation,[],[f33564,f33479])).

fof(f33479,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k3_xboole_0(X5,k3_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f33478,f8704])).

fof(f8704,plain,(
    ! [X17,X18] : k3_xboole_0(X17,X18) = k3_xboole_0(k3_xboole_0(X17,X18),X17) ),
    inference(backward_demodulation,[],[f2748,f8614])).

fof(f8614,plain,(
    ! [X24,X23] : k3_xboole_0(X23,X24) = k3_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X23,X24)) ),
    inference(superposition,[],[f4152,f6468])).

fof(f2748,plain,(
    ! [X17,X18] : k3_xboole_0(k3_xboole_0(X17,X18),k3_xboole_0(X17,X18)) = k3_xboole_0(k3_xboole_0(X17,X18),X17) ),
    inference(forward_demodulation,[],[f2747,f17])).

fof(f2747,plain,(
    ! [X17,X18] : k3_xboole_0(k3_xboole_0(X17,X18),k3_xboole_0(X17,X18)) = k4_xboole_0(k3_xboole_0(X17,X18),k4_xboole_0(k3_xboole_0(X17,X18),X17)) ),
    inference(forward_demodulation,[],[f2695,f2738])).

fof(f2738,plain,(
    ! [X6,X7] : k4_xboole_0(k3_xboole_0(X6,X7),X6) = k3_xboole_0(k3_xboole_0(X6,X7),k4_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f2690,f383])).

fof(f2690,plain,(
    ! [X6,X7] : k4_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X7)) = k3_xboole_0(k3_xboole_0(X6,X7),k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f17,f97])).

fof(f2695,plain,(
    ! [X17,X18] : k4_xboole_0(k3_xboole_0(X17,X18),k3_xboole_0(k3_xboole_0(X17,X18),k4_xboole_0(X17,X18))) = k3_xboole_0(k3_xboole_0(X17,X18),k3_xboole_0(X17,X18)) ),
    inference(superposition,[],[f27,f97])).

fof(f33478,plain,(
    ! [X6,X5] : k3_xboole_0(k3_xboole_0(X5,X6),X5) = k3_xboole_0(X5,k3_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f33477,f17])).

fof(f33477,plain,(
    ! [X6,X5] : k3_xboole_0(k3_xboole_0(X5,X6),X5) = k4_xboole_0(X5,k4_xboole_0(X5,k3_xboole_0(X5,X6))) ),
    inference(forward_demodulation,[],[f33304,f27])).

fof(f33304,plain,(
    ! [X6,X5] : k3_xboole_0(k3_xboole_0(X5,X6),X5) = k4_xboole_0(X5,k3_xboole_0(X5,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f32479,f507])).

fof(f33564,plain,(
    ! [X70,X69] : k3_xboole_0(k3_xboole_0(X69,X69),X70) = k3_xboole_0(X69,k3_xboole_0(X69,X70)) ),
    inference(forward_demodulation,[],[f33563,f17])).

fof(f33563,plain,(
    ! [X70,X69] : k3_xboole_0(k3_xboole_0(X69,X69),X70) = k4_xboole_0(X69,k4_xboole_0(X69,k3_xboole_0(X69,X70))) ),
    inference(forward_demodulation,[],[f33562,f33479])).

fof(f33562,plain,(
    ! [X70,X69] : k3_xboole_0(k3_xboole_0(X69,X69),X70) = k4_xboole_0(X69,k4_xboole_0(X69,k3_xboole_0(X69,k3_xboole_0(X69,X70)))) ),
    inference(forward_demodulation,[],[f33561,f27])).

fof(f33561,plain,(
    ! [X70,X69] : k3_xboole_0(k3_xboole_0(X69,X69),X70) = k4_xboole_0(X69,k3_xboole_0(X69,k4_xboole_0(X69,k3_xboole_0(X69,X70)))) ),
    inference(forward_demodulation,[],[f33331,f32479])).

fof(f33331,plain,(
    ! [X70,X69] : k3_xboole_0(k3_xboole_0(X69,X69),X70) = k4_xboole_0(X69,k3_xboole_0(X69,k4_xboole_0(k3_xboole_0(X69,X69),X70))) ),
    inference(superposition,[],[f32479,f17])).

fof(f60871,plain,(
    ! [X17,X16] : k4_xboole_0(X16,k3_xboole_0(X16,k5_xboole_0(k3_xboole_0(X16,X16),X17))) = k3_xboole_0(k3_xboole_0(X16,X16),X17) ),
    inference(superposition,[],[f60514,f32479])).

fof(f60514,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k4_xboole_0(X2,k5_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f352,f60285])).

fof(f60285,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f59413,f443])).

fof(f59413,plain,(
    ! [X30,X29] : k3_xboole_0(X29,X30) = k3_xboole_0(k4_xboole_0(X29,k4_xboole_0(X30,X29)),X30) ),
    inference(backward_demodulation,[],[f8650,f59404])).

fof(f59404,plain,(
    ! [X28,X29] : k4_xboole_0(X28,k4_xboole_0(X29,X28)) = k3_xboole_0(X28,k2_xboole_0(X29,X28)) ),
    inference(backward_demodulation,[],[f5644,f59348])).

fof(f59348,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f12269,f59343])).

fof(f59343,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(X7,X6)) = k3_xboole_0(X6,k2_xboole_0(X6,X7)) ),
    inference(backward_demodulation,[],[f12272,f59322])).

fof(f59322,plain,(
    ! [X19,X18] : k4_xboole_0(X18,k4_xboole_0(X19,X18)) = k4_xboole_0(X18,k4_xboole_0(X18,k2_xboole_0(X19,X18))) ),
    inference(backward_demodulation,[],[f33951,f59314])).

fof(f59314,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k2_xboole_0(X18,X17)) = k3_xboole_0(X17,k4_xboole_0(X18,X17)) ),
    inference(forward_demodulation,[],[f59308,f31096])).

fof(f31096,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k2_xboole_0(X13,X12)) = k4_xboole_0(X12,k2_xboole_0(X12,k5_xboole_0(X13,X13))) ),
    inference(forward_demodulation,[],[f30870,f25363])).

fof(f30870,plain,(
    ! [X12,X13] : k4_xboole_0(k3_xboole_0(X12,X13),X12) = k4_xboole_0(X12,k2_xboole_0(X12,k5_xboole_0(X13,X13))) ),
    inference(superposition,[],[f355,f13571])).

fof(f59308,plain,(
    ! [X17,X18] : k3_xboole_0(X17,k4_xboole_0(X18,X17)) = k4_xboole_0(X17,k2_xboole_0(X17,k5_xboole_0(X18,X18))) ),
    inference(backward_demodulation,[],[f26904,f59285])).

fof(f59285,plain,(
    ! [X12,X11] : k5_xboole_0(k2_xboole_0(X11,X12),k4_xboole_0(X12,X11)) = k2_xboole_0(X11,k5_xboole_0(X12,X12)) ),
    inference(backward_demodulation,[],[f828,f59284])).

fof(f59284,plain,(
    ! [X59,X60] : k2_xboole_0(X60,k5_xboole_0(X59,X59)) = k5_xboole_0(k2_xboole_0(X59,X60),k4_xboole_0(X59,X60)) ),
    inference(backward_demodulation,[],[f48900,f59166])).

fof(f48900,plain,(
    ! [X59,X60] : k5_xboole_0(X60,k5_xboole_0(X60,k2_xboole_0(X60,k5_xboole_0(X59,X59)))) = k5_xboole_0(k2_xboole_0(X59,X60),k4_xboole_0(X59,X60)) ),
    inference(backward_demodulation,[],[f32749,f48898])).

fof(f48898,plain,(
    ! [X116,X115] : k5_xboole_0(k2_xboole_0(X115,X116),k4_xboole_0(X115,X116)) = k5_xboole_0(k2_xboole_0(X115,X116),k4_xboole_0(X115,k3_xboole_0(X115,X116))) ),
    inference(forward_demodulation,[],[f48897,f47583])).

fof(f47583,plain,(
    ! [X130,X129] : k5_xboole_0(k2_xboole_0(X130,X129),k4_xboole_0(X130,X129)) = k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(X129,X130)) ),
    inference(forward_demodulation,[],[f47582,f32697])).

fof(f32697,plain,(
    ! [X4,X5] : k2_xboole_0(X5,X4) = k2_xboole_0(k4_xboole_0(X4,k3_xboole_0(X4,X5)),k4_xboole_0(X5,k4_xboole_0(X4,X5))) ),
    inference(backward_demodulation,[],[f29410,f32479])).

fof(f29410,plain,(
    ! [X4,X5] : k2_xboole_0(X5,X4) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X4,X4),X5),k4_xboole_0(X5,k4_xboole_0(X4,X5))) ),
    inference(forward_demodulation,[],[f29409,f211])).

fof(f29409,plain,(
    ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,X5),X5) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X4,X4),X5),k4_xboole_0(X5,k4_xboole_0(X4,X5))) ),
    inference(forward_demodulation,[],[f29408,f137])).

fof(f29408,plain,(
    ! [X4,X5] : k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X4,X5))) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X4,X4),X5),k4_xboole_0(X5,k4_xboole_0(X4,X5))) ),
    inference(forward_demodulation,[],[f29169,f100])).

fof(f29169,plain,(
    ! [X4,X5] : k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X4,X5))) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X4,X4),X5),k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)))) ),
    inference(superposition,[],[f63,f5577])).

fof(f5577,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X4,k4_xboole_0(X5,X4))) = k4_xboole_0(k3_xboole_0(X5,X5),X4) ),
    inference(backward_demodulation,[],[f955,f5562])).

fof(f955,plain,(
    ! [X4,X5] : k4_xboole_0(X5,k2_xboole_0(X4,k4_xboole_0(X4,X5))) = k4_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X4,k4_xboole_0(X5,X4))) ),
    inference(backward_demodulation,[],[f207,f951])).

fof(f207,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X4,k4_xboole_0(X5,X4))) = k3_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) ),
    inference(forward_demodulation,[],[f206,f92])).

fof(f206,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X4,k4_xboole_0(X5,X4))) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X4,k4_xboole_0(X5,X4))) ),
    inference(forward_demodulation,[],[f180,f82])).

fof(f180,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X4,k4_xboole_0(X5,X4))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5)),k4_xboole_0(X4,k4_xboole_0(X5,X4))) ),
    inference(superposition,[],[f23,f23])).

fof(f47582,plain,(
    ! [X130,X129] : k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k4_xboole_0(X129,k4_xboole_0(X130,X129)))) = k5_xboole_0(k2_xboole_0(X130,X129),k4_xboole_0(X130,X129)) ),
    inference(forward_demodulation,[],[f47581,f47480])).

fof(f47480,plain,(
    ! [X24,X25] : k5_xboole_0(k2_xboole_0(X25,X24),k4_xboole_0(X25,X24)) = k2_xboole_0(k4_xboole_0(X25,k2_xboole_0(X24,X25)),k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X25,X24),k5_xboole_0(X25,X25)))) ),
    inference(forward_demodulation,[],[f47479,f32707])).

fof(f32707,plain,(
    ! [X114,X113] : k5_xboole_0(k2_xboole_0(X113,X114),k4_xboole_0(X113,X114)) = k5_xboole_0(k2_xboole_0(X114,X113),k4_xboole_0(X113,k3_xboole_0(X113,X114))) ),
    inference(backward_demodulation,[],[f29487,f32479])).

fof(f29487,plain,(
    ! [X114,X113] : k5_xboole_0(k2_xboole_0(X114,X113),k4_xboole_0(k3_xboole_0(X113,X113),X114)) = k5_xboole_0(k2_xboole_0(X113,X114),k4_xboole_0(X113,X114)) ),
    inference(forward_demodulation,[],[f29486,f21541])).

fof(f21541,plain,(
    ! [X28,X29] : k5_xboole_0(k4_xboole_0(X29,X28),k2_xboole_0(X28,X29)) = k5_xboole_0(k2_xboole_0(X29,X28),k4_xboole_0(X29,X28)) ),
    inference(forward_demodulation,[],[f21395,f20477])).

fof(f20477,plain,(
    ! [X165,X166,X164] : k5_xboole_0(k2_xboole_0(X165,X166),X164) = k2_xboole_0(k4_xboole_0(X164,k2_xboole_0(X166,X165)),k5_xboole_0(k2_xboole_0(X165,X166),X164)) ),
    inference(superposition,[],[f165,f1479])).

fof(f21395,plain,(
    ! [X28,X29] : k5_xboole_0(k4_xboole_0(X29,X28),k2_xboole_0(X28,X29)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X29,X28),k2_xboole_0(X28,X29)),k5_xboole_0(k2_xboole_0(X29,X28),k4_xboole_0(X29,X28))) ),
    inference(superposition,[],[f1736,f828])).

fof(f1736,plain,(
    ! [X10,X11] : k5_xboole_0(X11,X10) = k2_xboole_0(k4_xboole_0(X11,X10),k5_xboole_0(X10,X11)) ),
    inference(forward_demodulation,[],[f1695,f166])).

fof(f166,plain,(
    ! [X12,X13] : k5_xboole_0(X12,X13) = k2_xboole_0(k4_xboole_0(X12,X13),k5_xboole_0(X12,X13)) ),
    inference(superposition,[],[f53,f18])).

fof(f1695,plain,(
    ! [X10,X11] : k2_xboole_0(k4_xboole_0(X11,X10),k5_xboole_0(X10,X11)) = k2_xboole_0(k4_xboole_0(X11,X10),k5_xboole_0(X11,X10)) ),
    inference(superposition,[],[f25,f86])).

fof(f29486,plain,(
    ! [X114,X113] : k5_xboole_0(k2_xboole_0(X114,X113),k4_xboole_0(k3_xboole_0(X113,X113),X114)) = k5_xboole_0(k4_xboole_0(X113,X114),k2_xboole_0(X114,X113)) ),
    inference(forward_demodulation,[],[f29485,f211])).

fof(f29485,plain,(
    ! [X114,X113] : k5_xboole_0(k2_xboole_0(X114,X113),k4_xboole_0(k3_xboole_0(X113,X113),X114)) = k5_xboole_0(k4_xboole_0(X113,X114),k2_xboole_0(k4_xboole_0(X113,X114),X114)) ),
    inference(forward_demodulation,[],[f29484,f211])).

fof(f29484,plain,(
    ! [X114,X113] : k5_xboole_0(k4_xboole_0(X113,X114),k2_xboole_0(k4_xboole_0(X114,k4_xboole_0(X113,X114)),k4_xboole_0(X113,X114))) = k5_xboole_0(k2_xboole_0(X114,X113),k4_xboole_0(k3_xboole_0(X113,X113),X114)) ),
    inference(forward_demodulation,[],[f29483,f121])).

fof(f29483,plain,(
    ! [X114,X113] : k5_xboole_0(k4_xboole_0(X113,X114),k2_xboole_0(k4_xboole_0(X114,k4_xboole_0(X113,X114)),k4_xboole_0(X113,X114))) = k5_xboole_0(k4_xboole_0(k3_xboole_0(X113,X113),X114),k2_xboole_0(X114,X113)) ),
    inference(forward_demodulation,[],[f29482,f211])).

fof(f29482,plain,(
    ! [X114,X113] : k5_xboole_0(k4_xboole_0(X113,X114),k2_xboole_0(k4_xboole_0(X114,k4_xboole_0(X113,X114)),k4_xboole_0(X113,X114))) = k5_xboole_0(k4_xboole_0(k3_xboole_0(X113,X113),X114),k2_xboole_0(k4_xboole_0(X113,X114),X114)) ),
    inference(forward_demodulation,[],[f29210,f109])).

fof(f29210,plain,(
    ! [X114,X113] : k5_xboole_0(k4_xboole_0(X113,X114),k2_xboole_0(k4_xboole_0(X114,k4_xboole_0(X113,X114)),k4_xboole_0(X113,X114))) = k5_xboole_0(k4_xboole_0(k3_xboole_0(X113,X113),X114),k5_xboole_0(k4_xboole_0(X114,k4_xboole_0(X113,X114)),k4_xboole_0(X113,X114))) ),
    inference(superposition,[],[f984,f5577])).

fof(f984,plain,(
    ! [X6,X7] : k5_xboole_0(k4_xboole_0(X7,X6),k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k2_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f983,f692])).

fof(f983,plain,(
    ! [X6,X7] : k5_xboole_0(k4_xboole_0(X7,X6),k5_xboole_0(X6,X7)) = k2_xboole_0(k4_xboole_0(X7,k2_xboole_0(X6,k5_xboole_0(X6,X7))),k4_xboole_0(X6,k2_xboole_0(X7,k4_xboole_0(X7,X6)))) ),
    inference(forward_demodulation,[],[f926,f20])).

fof(f926,plain,(
    ! [X6,X7] : k5_xboole_0(k4_xboole_0(X7,X6),k5_xboole_0(X6,X7)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X7,X6),k5_xboole_0(X6,X7)),k4_xboole_0(X6,k2_xboole_0(X7,k4_xboole_0(X7,X6)))) ),
    inference(superposition,[],[f18,f41])).

fof(f47479,plain,(
    ! [X24,X25] : k2_xboole_0(k4_xboole_0(X25,k2_xboole_0(X24,X25)),k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X25,X24),k5_xboole_0(X25,X25)))) = k5_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X25,k3_xboole_0(X25,X24))) ),
    inference(forward_demodulation,[],[f47478,f121])).

fof(f47478,plain,(
    ! [X24,X25] : k5_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)) = k2_xboole_0(k4_xboole_0(X25,k2_xboole_0(X24,X25)),k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X25,X24),k5_xboole_0(X25,X25)))) ),
    inference(forward_demodulation,[],[f47477,f7772])).

fof(f47477,plain,(
    ! [X24,X25] : k5_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)) = k2_xboole_0(k4_xboole_0(X25,k2_xboole_0(X25,k2_xboole_0(X24,X24))),k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X25,X24),k5_xboole_0(X25,X25)))) ),
    inference(forward_demodulation,[],[f47476,f1118])).

fof(f47476,plain,(
    ! [X24,X25] : k5_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)) = k2_xboole_0(k4_xboole_0(X25,k2_xboole_0(X25,k2_xboole_0(X24,k4_xboole_0(X24,X25)))),k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X25,X24),k5_xboole_0(X25,X25)))) ),
    inference(forward_demodulation,[],[f47475,f5731])).

fof(f47475,plain,(
    ! [X24,X25] : k5_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)) = k2_xboole_0(k4_xboole_0(X25,k2_xboole_0(X25,k2_xboole_0(X24,k3_xboole_0(X25,X24)))),k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X25,X24),k5_xboole_0(X25,X25)))) ),
    inference(forward_demodulation,[],[f47474,f12516])).

fof(f47474,plain,(
    ! [X24,X25] : k5_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)) = k2_xboole_0(k4_xboole_0(X25,k2_xboole_0(X25,k2_xboole_0(k3_xboole_0(X25,X24),X24))),k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X25,X24),k5_xboole_0(X25,X25)))) ),
    inference(forward_demodulation,[],[f47473,f1068])).

fof(f47473,plain,(
    ! [X24,X25] : k5_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)) = k2_xboole_0(k4_xboole_0(X25,k2_xboole_0(k3_xboole_0(X25,X24),k2_xboole_0(X24,X25))),k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X25,X24),k5_xboole_0(X25,X25)))) ),
    inference(forward_demodulation,[],[f47472,f20])).

fof(f47472,plain,(
    ! [X24,X25] : k5_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)),k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X25,X24),k5_xboole_0(X25,X25)))) ),
    inference(forward_demodulation,[],[f47471,f12336])).

fof(f47471,plain,(
    ! [X24,X25] : k5_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)),k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X25,X24),k4_xboole_0(X25,X25)))) ),
    inference(forward_demodulation,[],[f47470,f3999])).

fof(f3999,plain,(
    ! [X70,X68,X69] : k2_xboole_0(k4_xboole_0(X68,X69),k4_xboole_0(X70,k3_xboole_0(X68,X69))) = k2_xboole_0(k4_xboole_0(X68,X69),k4_xboole_0(X70,X68)) ),
    inference(forward_demodulation,[],[f3936,f66])).

fof(f3936,plain,(
    ! [X70,X68,X69] : k2_xboole_0(k4_xboole_0(X68,X69),k4_xboole_0(X70,k3_xboole_0(X68,X69))) = k2_xboole_0(k4_xboole_0(X68,X69),k4_xboole_0(X70,k2_xboole_0(X68,k4_xboole_0(X68,X69)))) ),
    inference(superposition,[],[f419,f29])).

fof(f47470,plain,(
    ! [X24,X25] : k5_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)),k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X25,X24),k4_xboole_0(X25,k3_xboole_0(X25,X24))))) ),
    inference(forward_demodulation,[],[f47113,f20])).

fof(f47113,plain,(
    ! [X24,X25] : k5_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)),k4_xboole_0(k4_xboole_0(X24,k4_xboole_0(X25,X24)),k4_xboole_0(X25,k3_xboole_0(X25,X24)))) ),
    inference(superposition,[],[f32,f32499])).

fof(f32499,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,k3_xboole_0(X5,X4))) ),
    inference(backward_demodulation,[],[f5590,f32479])).

fof(f5590,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(k3_xboole_0(X5,X5),X4)) ),
    inference(backward_demodulation,[],[f1238,f5562])).

fof(f1238,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,k2_xboole_0(X4,k4_xboole_0(X4,X5)))) ),
    inference(forward_demodulation,[],[f1237,f53])).

fof(f1237,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k2_xboole_0(X4,X5)) = k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,k2_xboole_0(X4,k4_xboole_0(X4,X5)))) ),
    inference(forward_demodulation,[],[f1236,f14])).

fof(f1236,plain,(
    ! [X4,X5] : k2_xboole_0(k2_xboole_0(X4,X5),X4) = k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,k2_xboole_0(X4,k4_xboole_0(X4,X5)))) ),
    inference(backward_demodulation,[],[f953,f1235])).

fof(f1235,plain,(
    ! [X24,X23,X22] : k2_xboole_0(k2_xboole_0(X23,X22),k4_xboole_0(X24,k4_xboole_0(X22,X23))) = k2_xboole_0(k2_xboole_0(X23,X22),X24) ),
    inference(forward_demodulation,[],[f1191,f15])).

fof(f1191,plain,(
    ! [X24,X23,X22] : k2_xboole_0(k2_xboole_0(X23,X22),k4_xboole_0(X24,k4_xboole_0(X22,X23))) = k2_xboole_0(k2_xboole_0(X23,X22),k4_xboole_0(X24,k2_xboole_0(X23,X22))) ),
    inference(superposition,[],[f66,f82])).

fof(f953,plain,(
    ! [X4,X5] : k2_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X4,k4_xboole_0(X5,X4))) = k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,k2_xboole_0(X4,k4_xboole_0(X4,X5)))) ),
    inference(backward_demodulation,[],[f291,f951])).

fof(f291,plain,(
    ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,X4)),k3_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4))) = k2_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X4,k4_xboole_0(X5,X4))) ),
    inference(superposition,[],[f29,f23])).

fof(f47581,plain,(
    ! [X130,X129] : k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k4_xboole_0(X129,k4_xboole_0(X130,X129)))) = k2_xboole_0(k4_xboole_0(X130,k2_xboole_0(X129,X130)),k4_xboole_0(X129,k2_xboole_0(k4_xboole_0(X130,X129),k5_xboole_0(X130,X130)))) ),
    inference(forward_demodulation,[],[f47580,f7772])).

fof(f47580,plain,(
    ! [X130,X129] : k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k4_xboole_0(X129,k4_xboole_0(X130,X129)))) = k2_xboole_0(k4_xboole_0(X130,k2_xboole_0(X130,k2_xboole_0(X129,X129))),k4_xboole_0(X129,k2_xboole_0(k4_xboole_0(X130,X129),k5_xboole_0(X130,X130)))) ),
    inference(forward_demodulation,[],[f47579,f1118])).

fof(f47579,plain,(
    ! [X130,X129] : k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k4_xboole_0(X129,k4_xboole_0(X130,X129)))) = k2_xboole_0(k4_xboole_0(X130,k2_xboole_0(X130,k2_xboole_0(X129,k4_xboole_0(X129,X130)))),k4_xboole_0(X129,k2_xboole_0(k4_xboole_0(X130,X129),k5_xboole_0(X130,X130)))) ),
    inference(forward_demodulation,[],[f47578,f5731])).

fof(f47578,plain,(
    ! [X130,X129] : k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k4_xboole_0(X129,k4_xboole_0(X130,X129)))) = k2_xboole_0(k4_xboole_0(X130,k2_xboole_0(X130,k2_xboole_0(X129,k3_xboole_0(X130,X129)))),k4_xboole_0(X129,k2_xboole_0(k4_xboole_0(X130,X129),k5_xboole_0(X130,X130)))) ),
    inference(forward_demodulation,[],[f47577,f12516])).

fof(f47577,plain,(
    ! [X130,X129] : k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k4_xboole_0(X129,k4_xboole_0(X130,X129)))) = k2_xboole_0(k4_xboole_0(X130,k2_xboole_0(X130,k2_xboole_0(k3_xboole_0(X130,X129),X129))),k4_xboole_0(X129,k2_xboole_0(k4_xboole_0(X130,X129),k5_xboole_0(X130,X130)))) ),
    inference(forward_demodulation,[],[f47576,f1068])).

fof(f47576,plain,(
    ! [X130,X129] : k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k4_xboole_0(X129,k4_xboole_0(X130,X129)))) = k2_xboole_0(k4_xboole_0(X130,k2_xboole_0(k3_xboole_0(X130,X129),k2_xboole_0(X129,X130))),k4_xboole_0(X129,k2_xboole_0(k4_xboole_0(X130,X129),k5_xboole_0(X130,X130)))) ),
    inference(forward_demodulation,[],[f47575,f20])).

fof(f47575,plain,(
    ! [X130,X129] : k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k4_xboole_0(X129,k4_xboole_0(X130,X129)))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(X129,X130)),k4_xboole_0(X129,k2_xboole_0(k4_xboole_0(X130,X129),k5_xboole_0(X130,X130)))) ),
    inference(forward_demodulation,[],[f47574,f12336])).

fof(f47574,plain,(
    ! [X130,X129] : k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k4_xboole_0(X129,k4_xboole_0(X130,X129)))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(X129,X130)),k4_xboole_0(X129,k2_xboole_0(k4_xboole_0(X130,X129),k4_xboole_0(X130,X130)))) ),
    inference(forward_demodulation,[],[f47573,f3999])).

fof(f47573,plain,(
    ! [X130,X129] : k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k4_xboole_0(X129,k4_xboole_0(X130,X129)))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(X129,X130)),k4_xboole_0(X129,k2_xboole_0(k4_xboole_0(X130,X129),k4_xboole_0(X130,k3_xboole_0(X130,X129))))) ),
    inference(forward_demodulation,[],[f47155,f20])).

fof(f47155,plain,(
    ! [X130,X129] : k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k4_xboole_0(X129,k4_xboole_0(X130,X129)))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(X129,X130)),k4_xboole_0(k4_xboole_0(X129,k4_xboole_0(X130,X129)),k4_xboole_0(X130,k3_xboole_0(X130,X129)))) ),
    inference(superposition,[],[f714,f32499])).

fof(f48897,plain,(
    ! [X116,X115] : k5_xboole_0(k4_xboole_0(X115,k3_xboole_0(X115,X116)),k2_xboole_0(X116,X115)) = k5_xboole_0(k2_xboole_0(X115,X116),k4_xboole_0(X115,k3_xboole_0(X115,X116))) ),
    inference(forward_demodulation,[],[f48896,f2941])).

fof(f2941,plain,(
    ! [X41,X42] : k2_xboole_0(X41,X42) = k2_xboole_0(k4_xboole_0(X42,k4_xboole_0(X41,X42)),k2_xboole_0(X41,X42)) ),
    inference(forward_demodulation,[],[f2831,f1163])).

fof(f2831,plain,(
    ! [X41,X42] : k2_xboole_0(k4_xboole_0(X41,X42),k2_xboole_0(X41,X42)) = k2_xboole_0(k4_xboole_0(X42,k4_xboole_0(X41,X42)),k2_xboole_0(k4_xboole_0(X41,X42),k2_xboole_0(X41,X42))) ),
    inference(superposition,[],[f82,f171])).

fof(f48896,plain,(
    ! [X116,X115] : k5_xboole_0(k4_xboole_0(X115,k3_xboole_0(X115,X116)),k2_xboole_0(X116,X115)) = k5_xboole_0(k2_xboole_0(k4_xboole_0(X116,k4_xboole_0(X115,X116)),k2_xboole_0(X115,X116)),k4_xboole_0(X115,k3_xboole_0(X115,X116))) ),
    inference(forward_demodulation,[],[f48895,f2917])).

fof(f2917,plain,(
    ! [X21,X20] : k2_xboole_0(X21,X20) = k2_xboole_0(k2_xboole_0(X20,X21),k4_xboole_0(X21,k4_xboole_0(X20,X21))) ),
    inference(forward_demodulation,[],[f2916,f1238])).

fof(f2916,plain,(
    ! [X21,X20] : k2_xboole_0(k2_xboole_0(X20,X21),k4_xboole_0(X21,k4_xboole_0(X20,X21))) = k2_xboole_0(k4_xboole_0(X21,k4_xboole_0(X20,X21)),k4_xboole_0(X20,k2_xboole_0(X21,k4_xboole_0(X21,X20)))) ),
    inference(forward_demodulation,[],[f2822,f2912])).

fof(f2912,plain,(
    ! [X17,X16] : k4_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X17,X16))) = k3_xboole_0(k2_xboole_0(X16,X17),k4_xboole_0(X16,X17)) ),
    inference(forward_demodulation,[],[f2911,f955])).

fof(f2911,plain,(
    ! [X17,X16] : k4_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X17,k4_xboole_0(X16,X17))) = k3_xboole_0(k2_xboole_0(X16,X17),k4_xboole_0(X16,X17)) ),
    inference(forward_demodulation,[],[f2910,f194])).

fof(f194,plain,(
    ! [X0,X1] : k3_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f88,f193])).

fof(f88,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X1),X1)) = k3_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f27,f16])).

fof(f2910,plain,(
    ! [X17,X16] : k4_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X17,k4_xboole_0(X16,X17))) = k4_xboole_0(k2_xboole_0(X16,X17),k4_xboole_0(X17,k4_xboole_0(X16,X17))) ),
    inference(forward_demodulation,[],[f2820,f1163])).

fof(f2820,plain,(
    ! [X17,X16] : k4_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X17,k4_xboole_0(X16,X17))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X16,X17),k2_xboole_0(X16,X17)),k4_xboole_0(X17,k4_xboole_0(X16,X17))) ),
    inference(superposition,[],[f23,f171])).

fof(f2822,plain,(
    ! [X21,X20] : k2_xboole_0(k4_xboole_0(X21,k4_xboole_0(X20,X21)),k3_xboole_0(k2_xboole_0(X20,X21),k4_xboole_0(X20,X21))) = k2_xboole_0(k2_xboole_0(X20,X21),k4_xboole_0(X21,k4_xboole_0(X20,X21))) ),
    inference(superposition,[],[f29,f171])).

fof(f48895,plain,(
    ! [X116,X115] : k5_xboole_0(k2_xboole_0(k4_xboole_0(X116,k4_xboole_0(X115,X116)),k2_xboole_0(X115,X116)),k4_xboole_0(X115,k3_xboole_0(X115,X116))) = k5_xboole_0(k4_xboole_0(X115,k3_xboole_0(X115,X116)),k2_xboole_0(k2_xboole_0(X115,X116),k4_xboole_0(X116,k4_xboole_0(X115,X116)))) ),
    inference(forward_demodulation,[],[f48230,f121])).

fof(f48230,plain,(
    ! [X116,X115] : k5_xboole_0(k2_xboole_0(k4_xboole_0(X116,k4_xboole_0(X115,X116)),k2_xboole_0(X115,X116)),k4_xboole_0(X115,k3_xboole_0(X115,X116))) = k5_xboole_0(k2_xboole_0(k2_xboole_0(X115,X116),k4_xboole_0(X116,k4_xboole_0(X115,X116))),k4_xboole_0(X115,k3_xboole_0(X115,X116))) ),
    inference(superposition,[],[f828,f32507])).

fof(f32507,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f5607,f32479])).

fof(f5607,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(k3_xboole_0(X0,X0),X1) ),
    inference(backward_demodulation,[],[f2913,f5562])).

fof(f2913,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f194,f2912])).

fof(f32749,plain,(
    ! [X59,X60] : k5_xboole_0(X60,k5_xboole_0(X60,k2_xboole_0(X60,k5_xboole_0(X59,X59)))) = k5_xboole_0(k2_xboole_0(X59,X60),k4_xboole_0(X59,k3_xboole_0(X59,X60))) ),
    inference(backward_demodulation,[],[f31196,f32479])).

fof(f31196,plain,(
    ! [X59,X60] : k5_xboole_0(k2_xboole_0(X59,X60),k4_xboole_0(k3_xboole_0(X59,X59),X60)) = k5_xboole_0(X60,k5_xboole_0(X60,k2_xboole_0(X60,k5_xboole_0(X59,X59)))) ),
    inference(backward_demodulation,[],[f26619,f31115])).

fof(f31115,plain,(
    ! [X15,X16] : k5_xboole_0(X15,k5_xboole_0(X16,k5_xboole_0(X15,X16))) = k5_xboole_0(X15,k2_xboole_0(X15,k5_xboole_0(X16,X16))) ),
    inference(backward_demodulation,[],[f7942,f31114])).

fof(f31114,plain,(
    ! [X35,X34] : k2_xboole_0(k4_xboole_0(X34,k2_xboole_0(X35,X34)),k4_xboole_0(X34,k2_xboole_0(X35,X34))) = k5_xboole_0(X34,k2_xboole_0(X34,k5_xboole_0(X35,X35))) ),
    inference(forward_demodulation,[],[f31113,f31096])).

fof(f31113,plain,(
    ! [X35,X34] : k5_xboole_0(X34,k2_xboole_0(X34,k5_xboole_0(X35,X35))) = k2_xboole_0(k4_xboole_0(X34,k2_xboole_0(X34,k5_xboole_0(X35,X35))),k4_xboole_0(X34,k2_xboole_0(X35,X34))) ),
    inference(forward_demodulation,[],[f30879,f20])).

fof(f30879,plain,(
    ! [X35,X34] : k5_xboole_0(X34,k2_xboole_0(X34,k5_xboole_0(X35,X35))) = k2_xboole_0(k4_xboole_0(X34,k2_xboole_0(X34,k5_xboole_0(X35,X35))),k4_xboole_0(k4_xboole_0(X34,X35),X34)) ),
    inference(superposition,[],[f46,f13571])).

fof(f7942,plain,(
    ! [X15,X16] : k5_xboole_0(X15,k5_xboole_0(X16,k5_xboole_0(X15,X16))) = k2_xboole_0(k4_xboole_0(X15,k2_xboole_0(X16,X15)),k4_xboole_0(X15,k2_xboole_0(X16,X15))) ),
    inference(backward_demodulation,[],[f4948,f7927])).

fof(f4948,plain,(
    ! [X15,X16] : k5_xboole_0(X15,k5_xboole_0(X16,k5_xboole_0(X15,X16))) = k2_xboole_0(k4_xboole_0(X15,k2_xboole_0(X16,k5_xboole_0(X15,X16))),k4_xboole_0(X15,k2_xboole_0(X16,k5_xboole_0(X15,X16)))) ),
    inference(forward_demodulation,[],[f4947,f19])).

fof(f4947,plain,(
    ! [X15,X16] : k5_xboole_0(k5_xboole_0(X15,X16),k5_xboole_0(X15,X16)) = k2_xboole_0(k4_xboole_0(X15,k2_xboole_0(X16,k5_xboole_0(X15,X16))),k4_xboole_0(X15,k2_xboole_0(X16,k5_xboole_0(X15,X16)))) ),
    inference(forward_demodulation,[],[f4946,f2207])).

fof(f4946,plain,(
    ! [X15,X16] : k5_xboole_0(k5_xboole_0(X15,X16),k5_xboole_0(X15,X16)) = k2_xboole_0(k4_xboole_0(k5_xboole_0(X15,X16),k5_xboole_0(X15,X16)),k4_xboole_0(X15,k2_xboole_0(X16,k5_xboole_0(X15,X16)))) ),
    inference(forward_demodulation,[],[f4900,f20])).

fof(f4900,plain,(
    ! [X15,X16] : k5_xboole_0(k5_xboole_0(X15,X16),k5_xboole_0(X15,X16)) = k2_xboole_0(k4_xboole_0(k5_xboole_0(X15,X16),k5_xboole_0(X15,X16)),k4_xboole_0(k4_xboole_0(X15,X16),k5_xboole_0(X15,X16))) ),
    inference(superposition,[],[f32,f166])).

fof(f26619,plain,(
    ! [X59,X60] : k5_xboole_0(X60,k5_xboole_0(X60,k5_xboole_0(X59,k5_xboole_0(X60,X59)))) = k5_xboole_0(k2_xboole_0(X59,X60),k4_xboole_0(k3_xboole_0(X59,X59),X60)) ),
    inference(forward_demodulation,[],[f26618,f5606])).

fof(f5606,plain,(
    ! [X17,X16] : k3_xboole_0(k2_xboole_0(X16,X17),k4_xboole_0(X16,X17)) = k4_xboole_0(k3_xboole_0(X16,X16),X17) ),
    inference(backward_demodulation,[],[f2912,f5562])).

fof(f26618,plain,(
    ! [X59,X60] : k5_xboole_0(k2_xboole_0(X59,X60),k3_xboole_0(k2_xboole_0(X59,X60),k4_xboole_0(X59,X60))) = k5_xboole_0(X60,k5_xboole_0(X60,k5_xboole_0(X59,k5_xboole_0(X60,X59)))) ),
    inference(forward_demodulation,[],[f26617,f7959])).

fof(f7959,plain,(
    ! [X10,X9] : k5_xboole_0(k2_xboole_0(X10,X9),k2_xboole_0(X10,X9)) = k5_xboole_0(X9,k5_xboole_0(X10,k5_xboole_0(X9,X10))) ),
    inference(backward_demodulation,[],[f682,f7942])).

fof(f682,plain,(
    ! [X10,X9] : k5_xboole_0(k2_xboole_0(X10,X9),k2_xboole_0(X10,X9)) = k2_xboole_0(k4_xboole_0(X9,k2_xboole_0(X10,X9)),k4_xboole_0(X9,k2_xboole_0(X10,X9))) ),
    inference(forward_demodulation,[],[f636,f69])).

fof(f636,plain,(
    ! [X10,X9] : k5_xboole_0(k2_xboole_0(X10,X9),k2_xboole_0(X10,X9)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X10,X9),k2_xboole_0(X10,X9)),k4_xboole_0(X9,k2_xboole_0(X10,X9))) ),
    inference(superposition,[],[f32,f160])).

fof(f26617,plain,(
    ! [X59,X60] : k5_xboole_0(k2_xboole_0(X59,X60),k3_xboole_0(k2_xboole_0(X59,X60),k4_xboole_0(X59,X60))) = k5_xboole_0(X60,k5_xboole_0(k2_xboole_0(X59,X60),k2_xboole_0(X59,X60))) ),
    inference(forward_demodulation,[],[f26616,f147])).

fof(f147,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f121,f19])).

fof(f26616,plain,(
    ! [X59,X60] : k5_xboole_0(k2_xboole_0(X59,X60),k3_xboole_0(k2_xboole_0(X59,X60),k4_xboole_0(X59,X60))) = k5_xboole_0(k2_xboole_0(X59,X60),k5_xboole_0(X60,k2_xboole_0(X59,X60))) ),
    inference(forward_demodulation,[],[f26528,f7644])).

fof(f7644,plain,(
    ! [X59,X58] : k5_xboole_0(k2_xboole_0(X58,X59),k4_xboole_0(X59,k4_xboole_0(X58,X59))) = k5_xboole_0(X59,k2_xboole_0(X58,X59)) ),
    inference(backward_demodulation,[],[f7096,f7643])).

fof(f7643,plain,(
    ! [X10,X11] : k5_xboole_0(X11,k2_xboole_0(X10,X11)) = k2_xboole_0(k4_xboole_0(X11,k2_xboole_0(X10,X11)),k4_xboole_0(k3_xboole_0(X10,X10),X11)) ),
    inference(forward_demodulation,[],[f7642,f130])).

fof(f7642,plain,(
    ! [X10,X11] : k5_xboole_0(k2_xboole_0(X10,X11),X11) = k2_xboole_0(k4_xboole_0(X11,k2_xboole_0(X10,X11)),k4_xboole_0(k3_xboole_0(X10,X10),X11)) ),
    inference(forward_demodulation,[],[f7455,f1593])).

fof(f7455,plain,(
    ! [X10,X11] : k5_xboole_0(k2_xboole_0(X10,X11),X11) = k2_xboole_0(k4_xboole_0(X11,k2_xboole_0(X10,X11)),k4_xboole_0(k3_xboole_0(X10,k2_xboole_0(X10,X11)),X11)) ),
    inference(superposition,[],[f5579,f515])).

fof(f7096,plain,(
    ! [X59,X58] : k2_xboole_0(k4_xboole_0(X59,k2_xboole_0(X58,X59)),k4_xboole_0(k3_xboole_0(X58,X58),X59)) = k5_xboole_0(k2_xboole_0(X58,X59),k4_xboole_0(X59,k4_xboole_0(X58,X59))) ),
    inference(forward_demodulation,[],[f7095,f171])).

fof(f7095,plain,(
    ! [X59,X58] : k5_xboole_0(k2_xboole_0(X58,X59),k4_xboole_0(k2_xboole_0(X58,X59),k4_xboole_0(X58,X59))) = k2_xboole_0(k4_xboole_0(X59,k2_xboole_0(X58,X59)),k4_xboole_0(k3_xboole_0(X58,X58),X59)) ),
    inference(forward_demodulation,[],[f7094,f69])).

fof(f7094,plain,(
    ! [X59,X58] : k5_xboole_0(k2_xboole_0(X58,X59),k4_xboole_0(k2_xboole_0(X58,X59),k4_xboole_0(X58,X59))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X58,X59),k2_xboole_0(X58,X59)),k4_xboole_0(k3_xboole_0(X58,X58),X59)) ),
    inference(forward_demodulation,[],[f6994,f5606])).

fof(f6994,plain,(
    ! [X59,X58] : k5_xboole_0(k2_xboole_0(X58,X59),k4_xboole_0(k2_xboole_0(X58,X59),k4_xboole_0(X58,X59))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X58,X59),k2_xboole_0(X58,X59)),k3_xboole_0(k2_xboole_0(X58,X59),k4_xboole_0(X58,X59))) ),
    inference(superposition,[],[f134,f1163])).

fof(f26528,plain,(
    ! [X59,X60] : k5_xboole_0(k2_xboole_0(X59,X60),k3_xboole_0(k2_xboole_0(X59,X60),k4_xboole_0(X59,X60))) = k5_xboole_0(k2_xboole_0(X59,X60),k5_xboole_0(k2_xboole_0(X59,X60),k4_xboole_0(X60,k4_xboole_0(X59,X60)))) ),
    inference(superposition,[],[f26072,f171])).

fof(f26904,plain,(
    ! [X17,X18] : k3_xboole_0(X17,k4_xboole_0(X18,X17)) = k4_xboole_0(X17,k5_xboole_0(k2_xboole_0(X17,X18),k4_xboole_0(X18,X17))) ),
    inference(forward_demodulation,[],[f26763,f2900])).

fof(f26763,plain,(
    ! [X17,X18] : k3_xboole_0(X17,k4_xboole_0(X18,X17)) = k4_xboole_0(X17,k5_xboole_0(k4_xboole_0(X18,X17),k2_xboole_0(X18,X17))) ),
    inference(superposition,[],[f5513,f2970])).

fof(f33951,plain,(
    ! [X19,X18] : k4_xboole_0(X18,k4_xboole_0(X19,X18)) = k4_xboole_0(X18,k3_xboole_0(X18,k4_xboole_0(X19,X18))) ),
    inference(forward_demodulation,[],[f33950,f23])).

fof(f33950,plain,(
    ! [X19,X18] : k4_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(X19,X18)) = k4_xboole_0(X18,k3_xboole_0(X18,k4_xboole_0(X19,X18))) ),
    inference(forward_demodulation,[],[f33949,f100])).

fof(f33949,plain,(
    ! [X19,X18] : k4_xboole_0(X18,k3_xboole_0(X18,k4_xboole_0(X19,X18))) = k4_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(X19,k2_xboole_0(X18,X18))) ),
    inference(forward_demodulation,[],[f33795,f20])).

fof(f33795,plain,(
    ! [X19,X18] : k4_xboole_0(X18,k3_xboole_0(X18,k4_xboole_0(X19,X18))) = k4_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(k4_xboole_0(X19,X18),X18)) ),
    inference(superposition,[],[f32485,f137])).

fof(f12272,plain,(
    ! [X6,X7] : k3_xboole_0(X6,k2_xboole_0(X6,X7)) = k4_xboole_0(X6,k4_xboole_0(X6,k2_xboole_0(X7,X6))) ),
    inference(forward_demodulation,[],[f12165,f3537])).

fof(f3537,plain,(
    ! [X14,X13] : k4_xboole_0(X13,k2_xboole_0(X14,X13)) = k4_xboole_0(k3_xboole_0(X13,X14),k2_xboole_0(X13,X14)) ),
    inference(superposition,[],[f355,f307])).

fof(f12165,plain,(
    ! [X6,X7] : k3_xboole_0(X6,k2_xboole_0(X6,X7)) = k4_xboole_0(X6,k4_xboole_0(k3_xboole_0(X6,X7),k2_xboole_0(X6,X7))) ),
    inference(superposition,[],[f364,f1163])).

fof(f12269,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f12162,f5482])).

fof(f12162,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(k3_xboole_0(X0,X1),X1)) ),
    inference(superposition,[],[f364,f2903])).

fof(f5644,plain,(
    ! [X28,X29] : k3_xboole_0(X28,k2_xboole_0(X29,X28)) = k4_xboole_0(X28,k4_xboole_0(X29,k2_xboole_0(X28,X29))) ),
    inference(forward_demodulation,[],[f5387,f5482])).

fof(f5387,plain,(
    ! [X28,X29] : k3_xboole_0(X28,k2_xboole_0(X29,X28)) = k4_xboole_0(X28,k4_xboole_0(k3_xboole_0(X28,X29),X29)) ),
    inference(superposition,[],[f17,f353])).

fof(f8650,plain,(
    ! [X30,X29] : k3_xboole_0(X29,X30) = k3_xboole_0(k3_xboole_0(X29,k2_xboole_0(X30,X29)),X30) ),
    inference(backward_demodulation,[],[f5936,f8649])).

fof(f8649,plain,(
    ! [X57,X58] : k3_xboole_0(X57,X58) = k3_xboole_0(k5_xboole_0(X57,k4_xboole_0(X57,X58)),k3_xboole_0(X57,X58)) ),
    inference(forward_demodulation,[],[f8648,f39])).

fof(f8648,plain,(
    ! [X57,X58] : k3_xboole_0(X57,X58) = k3_xboole_0(k2_xboole_0(k3_xboole_0(X57,X58),k4_xboole_0(X57,k2_xboole_0(X58,X57))),k3_xboole_0(X57,X58)) ),
    inference(forward_demodulation,[],[f8586,f4152])).

fof(f8586,plain,(
    ! [X57,X58] : k3_xboole_0(k3_xboole_0(X57,X58),X58) = k3_xboole_0(k2_xboole_0(k3_xboole_0(X57,X58),k4_xboole_0(X57,k2_xboole_0(X58,X57))),k3_xboole_0(k3_xboole_0(X57,X58),X58)) ),
    inference(superposition,[],[f6468,f353])).

fof(f5936,plain,(
    ! [X30,X29] : k3_xboole_0(k3_xboole_0(X29,k2_xboole_0(X30,X29)),X30) = k3_xboole_0(k5_xboole_0(X29,k4_xboole_0(X29,X30)),k3_xboole_0(X29,X30)) ),
    inference(forward_demodulation,[],[f5929,f507])).

fof(f5929,plain,(
    ! [X30,X29] : k4_xboole_0(k3_xboole_0(X29,X30),k4_xboole_0(X29,k2_xboole_0(X30,X29))) = k3_xboole_0(k5_xboole_0(X29,k4_xboole_0(X29,X30)),k3_xboole_0(X29,X30)) ),
    inference(backward_demodulation,[],[f3136,f5925])).

fof(f3136,plain,(
    ! [X30,X29] : k3_xboole_0(k5_xboole_0(X29,k4_xboole_0(X29,X30)),k3_xboole_0(X29,X30)) = k4_xboole_0(k3_xboole_0(X29,X30),k4_xboole_0(k3_xboole_0(X29,X29),k2_xboole_0(X30,X29))) ),
    inference(backward_demodulation,[],[f1041,f3132])).

fof(f1041,plain,(
    ! [X30,X29] : k3_xboole_0(k5_xboole_0(X29,k4_xboole_0(X29,X30)),k3_xboole_0(X29,X30)) = k4_xboole_0(k3_xboole_0(X29,X30),k4_xboole_0(X29,k2_xboole_0(X30,k2_xboole_0(X29,k3_xboole_0(X29,X30))))) ),
    inference(forward_demodulation,[],[f1040,f71])).

fof(f1040,plain,(
    ! [X30,X29] : k3_xboole_0(k5_xboole_0(X29,k4_xboole_0(X29,X30)),k3_xboole_0(X29,X30)) = k4_xboole_0(k3_xboole_0(X29,X30),k4_xboole_0(X29,k2_xboole_0(k2_xboole_0(X30,X29),k3_xboole_0(X29,X30)))) ),
    inference(forward_demodulation,[],[f1014,f20])).

fof(f1014,plain,(
    ! [X30,X29] : k4_xboole_0(k3_xboole_0(X29,X30),k4_xboole_0(k4_xboole_0(X29,k2_xboole_0(X30,X29)),k3_xboole_0(X29,X30))) = k3_xboole_0(k5_xboole_0(X29,k4_xboole_0(X29,X30)),k3_xboole_0(X29,X30)) ),
    inference(superposition,[],[f52,f39])).

fof(f352,plain,(
    ! [X2,X3] : k4_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = k4_xboole_0(X2,k5_xboole_0(X2,X3)) ),
    inference(superposition,[],[f60,f18])).

fof(f63055,plain,(
    ! [X19,X20] : k3_xboole_0(X20,k3_xboole_0(X19,X19)) = k4_xboole_0(X19,k3_xboole_0(X19,k5_xboole_0(k3_xboole_0(X19,X19),X20))) ),
    inference(superposition,[],[f62989,f32479])).

fof(f62989,plain,(
    ! [X17,X16] : k3_xboole_0(X16,X17) = k4_xboole_0(X17,k5_xboole_0(X17,X16)) ),
    inference(forward_demodulation,[],[f62942,f60569])).

fof(f60569,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X3,X2)) ),
    inference(backward_demodulation,[],[f15641,f60516])).

fof(f60516,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k4_xboole_0(X3,k5_xboole_0(X4,X3)) ),
    inference(backward_demodulation,[],[f3301,f60514])).

fof(f3301,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k5_xboole_0(X4,X3)) = k4_xboole_0(X3,k5_xboole_0(X3,X4)) ),
    inference(superposition,[],[f352,f351])).

fof(f15641,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k5_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X3,X2)) ),
    inference(superposition,[],[f567,f15])).

fof(f567,plain,(
    ! [X26,X27,X25] : k4_xboole_0(X27,k5_xboole_0(X25,X26)) = k4_xboole_0(k2_xboole_0(X27,k4_xboole_0(X25,X26)),k5_xboole_0(X25,X26)) ),
    inference(superposition,[],[f68,f18])).

fof(f62942,plain,(
    ! [X17,X16] : k4_xboole_0(X17,k5_xboole_0(X17,X16)) = k4_xboole_0(k2_xboole_0(X16,X17),k5_xboole_0(X17,X16)) ),
    inference(superposition,[],[f378,f165])).

fof(f378,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(forward_demodulation,[],[f377,f20])).

fof(f377,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,X1)),X2) ),
    inference(forward_demodulation,[],[f343,f193])).

fof(f343,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),X2) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(superposition,[],[f60,f16])).

fof(f67735,plain,(
    ! [X107,X106] : k5_xboole_0(X106,k2_xboole_0(X106,X107)) = k5_xboole_0(X107,k3_xboole_0(X107,k3_xboole_0(X106,X106))) ),
    inference(forward_demodulation,[],[f67734,f32618])).

fof(f32618,plain,(
    ! [X80,X79] : k5_xboole_0(X80,k2_xboole_0(X80,X79)) = k5_xboole_0(k4_xboole_0(X80,k3_xboole_0(X80,X79)),k5_xboole_0(X80,X79)) ),
    inference(backward_demodulation,[],[f16430,f32479])).

fof(f16430,plain,(
    ! [X80,X79] : k5_xboole_0(X80,k2_xboole_0(X80,X79)) = k5_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k5_xboole_0(X80,X79)) ),
    inference(forward_demodulation,[],[f16429,f5584])).

fof(f5584,plain,(
    ! [X33,X32] : k5_xboole_0(X32,X33) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X32,X32),X33),k4_xboole_0(X33,X32)) ),
    inference(backward_demodulation,[],[f998,f5562])).

fof(f998,plain,(
    ! [X33,X32] : k5_xboole_0(X32,X33) = k2_xboole_0(k4_xboole_0(X32,k2_xboole_0(X33,k4_xboole_0(X33,X32))),k4_xboole_0(X33,X32)) ),
    inference(forward_demodulation,[],[f938,f165])).

fof(f938,plain,(
    ! [X33,X32] : k2_xboole_0(k4_xboole_0(X33,X32),k5_xboole_0(X32,X33)) = k2_xboole_0(k4_xboole_0(X32,k2_xboole_0(X33,k4_xboole_0(X33,X32))),k4_xboole_0(X33,X32)) ),
    inference(superposition,[],[f211,f41])).

fof(f16429,plain,(
    ! [X80,X79] : k5_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k2_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k4_xboole_0(X79,X80))) = k5_xboole_0(X80,k2_xboole_0(X80,X79)) ),
    inference(forward_demodulation,[],[f16428,f6545])).

fof(f16428,plain,(
    ! [X80,X79] : k5_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k2_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k4_xboole_0(X79,X80))) = k2_xboole_0(k4_xboole_0(X79,k2_xboole_0(X80,X79)),k4_xboole_0(k3_xboole_0(X79,X79),X80)) ),
    inference(forward_demodulation,[],[f16427,f9319])).

fof(f9319,plain,(
    ! [X17,X18] : k4_xboole_0(X18,k2_xboole_0(X17,X18)) = k4_xboole_0(k3_xboole_0(X17,X17),k2_xboole_0(X18,k5_xboole_0(X17,X18))) ),
    inference(forward_demodulation,[],[f9318,f6137])).

fof(f6137,plain,(
    ! [X2,X1] : k4_xboole_0(X2,k2_xboole_0(X1,X2)) = k4_xboole_0(X2,k2_xboole_0(k3_xboole_0(X1,X1),X2)) ),
    inference(forward_demodulation,[],[f6136,f5484])).

fof(f6136,plain,(
    ! [X2,X1] : k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k2_xboole_0(k3_xboole_0(X1,X1),X2)) ),
    inference(forward_demodulation,[],[f6135,f5506])).

fof(f5506,plain,(
    ! [X50,X48,X49] : k4_xboole_0(k4_xboole_0(k3_xboole_0(X48,X50),X49),k4_xboole_0(X48,X49)) = k4_xboole_0(X49,k2_xboole_0(k3_xboole_0(X48,X50),X49)) ),
    inference(backward_demodulation,[],[f4217,f5505])).

fof(f4217,plain,(
    ! [X50,X48,X49] : k4_xboole_0(k4_xboole_0(k3_xboole_0(X48,X50),X49),k4_xboole_0(X48,X49)) = k4_xboole_0(k3_xboole_0(k3_xboole_0(X48,X49),X50),X49) ),
    inference(forward_demodulation,[],[f4216,f443])).

fof(f4216,plain,(
    ! [X50,X48,X49] : k4_xboole_0(k4_xboole_0(k3_xboole_0(X48,X50),X49),k4_xboole_0(X48,X49)) = k3_xboole_0(k4_xboole_0(k3_xboole_0(X48,X49),X49),X50) ),
    inference(forward_demodulation,[],[f4215,f443])).

fof(f4215,plain,(
    ! [X50,X48,X49] : k3_xboole_0(k3_xboole_0(k4_xboole_0(X48,X49),X49),X50) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X48,X50),X49),k4_xboole_0(X48,X49)) ),
    inference(forward_demodulation,[],[f4145,f443])).

fof(f4145,plain,(
    ! [X50,X48,X49] : k3_xboole_0(k3_xboole_0(k4_xboole_0(X48,X49),X49),X50) = k4_xboole_0(k3_xboole_0(k4_xboole_0(X48,X49),X50),k4_xboole_0(X48,X49)) ),
    inference(superposition,[],[f507,f50])).

fof(f6135,plain,(
    ! [X2,X1] : k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X1,X1),X2),k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f6078,f1589])).

fof(f6078,plain,(
    ! [X2,X1] : k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X1,k4_xboole_0(X1,X2)),X2),k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f5896,f443])).

fof(f9318,plain,(
    ! [X17,X18] : k4_xboole_0(k3_xboole_0(X17,X17),k2_xboole_0(X18,k5_xboole_0(X17,X18))) = k4_xboole_0(X18,k2_xboole_0(k3_xboole_0(X17,X17),X18)) ),
    inference(forward_demodulation,[],[f9317,f5484])).

fof(f9317,plain,(
    ! [X17,X18] : k4_xboole_0(k4_xboole_0(k3_xboole_0(X17,X17),X18),k4_xboole_0(k3_xboole_0(X17,X17),X18)) = k4_xboole_0(k3_xboole_0(X17,X17),k2_xboole_0(X18,k5_xboole_0(X17,X18))) ),
    inference(forward_demodulation,[],[f9166,f20])).

fof(f9166,plain,(
    ! [X17,X18] : k4_xboole_0(k4_xboole_0(k3_xboole_0(X17,X17),X18),k4_xboole_0(k3_xboole_0(X17,X17),X18)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X17,X17),X18),k5_xboole_0(X17,X18)) ),
    inference(superposition,[],[f383,f8066])).

fof(f8066,plain,(
    ! [X10,X11] : k3_xboole_0(k5_xboole_0(X11,X10),k4_xboole_0(X11,X10)) = k4_xboole_0(k3_xboole_0(X11,X11),X10) ),
    inference(backward_demodulation,[],[f5565,f8047])).

fof(f8047,plain,(
    ! [X12,X13] : k4_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(k3_xboole_0(X12,X12),X13)) = k4_xboole_0(k3_xboole_0(X13,X13),X12) ),
    inference(backward_demodulation,[],[f5566,f8046])).

fof(f8046,plain,(
    ! [X10,X11] : k3_xboole_0(k5_xboole_0(X11,X10),k4_xboole_0(X10,X11)) = k4_xboole_0(k3_xboole_0(X10,X10),X11) ),
    inference(forward_demodulation,[],[f8040,f5562])).

fof(f8040,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k2_xboole_0(X11,k4_xboole_0(X11,X10))) = k3_xboole_0(k5_xboole_0(X11,X10),k4_xboole_0(X10,X11)) ),
    inference(backward_demodulation,[],[f5580,f8038])).

fof(f5580,plain,(
    ! [X10,X11] : k3_xboole_0(k5_xboole_0(X11,X10),k4_xboole_0(X10,X11)) = k4_xboole_0(X10,k2_xboole_0(X11,k4_xboole_0(k3_xboole_0(X11,X11),X10))) ),
    inference(backward_demodulation,[],[f979,f5562])).

fof(f979,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k2_xboole_0(X11,k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11))))) = k3_xboole_0(k5_xboole_0(X11,X10),k4_xboole_0(X10,X11)) ),
    inference(backward_demodulation,[],[f201,f924])).

fof(f924,plain,(
    ! [X2,X3] : k3_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = k4_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X3,X2)))) ),
    inference(superposition,[],[f17,f41])).

fof(f201,plain,(
    ! [X10,X11] : k4_xboole_0(k5_xboole_0(X11,X10),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(X10,k2_xboole_0(X11,k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11))))) ),
    inference(forward_demodulation,[],[f200,f20])).

fof(f200,plain,(
    ! [X10,X11] : k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(k5_xboole_0(X11,X10),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11)))) ),
    inference(forward_demodulation,[],[f176,f20])).

fof(f176,plain,(
    ! [X10,X11] : k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(k4_xboole_0(X11,X10),k4_xboole_0(X10,X11))) = k4_xboole_0(k5_xboole_0(X11,X10),k4_xboole_0(k4_xboole_0(X11,X10),k4_xboole_0(X10,X11))) ),
    inference(superposition,[],[f23,f34])).

fof(f5566,plain,(
    ! [X12,X13] : k3_xboole_0(k5_xboole_0(X12,X13),k4_xboole_0(X13,X12)) = k4_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(k3_xboole_0(X12,X12),X13)) ),
    inference(backward_demodulation,[],[f256,f5562])).

fof(f256,plain,(
    ! [X12,X13] : k3_xboole_0(k5_xboole_0(X12,X13),k4_xboole_0(X13,X12)) = k4_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(X12,k2_xboole_0(X13,k4_xboole_0(X13,X12)))) ),
    inference(forward_demodulation,[],[f253,f20])).

fof(f253,plain,(
    ! [X12,X13] : k4_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X13,X12))) = k3_xboole_0(k5_xboole_0(X12,X13),k4_xboole_0(X13,X12)) ),
    inference(superposition,[],[f193,f18])).

fof(f5565,plain,(
    ! [X10,X11] : k3_xboole_0(k5_xboole_0(X11,X10),k4_xboole_0(X11,X10)) = k4_xboole_0(k4_xboole_0(X11,X10),k4_xboole_0(k3_xboole_0(X10,X10),X11)) ),
    inference(backward_demodulation,[],[f255,f5562])).

fof(f255,plain,(
    ! [X10,X11] : k3_xboole_0(k5_xboole_0(X11,X10),k4_xboole_0(X11,X10)) = k4_xboole_0(k4_xboole_0(X11,X10),k4_xboole_0(X10,k2_xboole_0(X11,k4_xboole_0(X11,X10)))) ),
    inference(forward_demodulation,[],[f252,f20])).

fof(f252,plain,(
    ! [X10,X11] : k4_xboole_0(k4_xboole_0(X11,X10),k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X11,X10))) = k3_xboole_0(k5_xboole_0(X11,X10),k4_xboole_0(X11,X10)) ),
    inference(superposition,[],[f193,f34])).

fof(f16427,plain,(
    ! [X80,X79] : k5_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k2_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k4_xboole_0(X79,X80))) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),k2_xboole_0(X79,k5_xboole_0(X80,X79))),k4_xboole_0(k3_xboole_0(X79,X79),X80)) ),
    inference(forward_demodulation,[],[f16426,f20])).

fof(f16426,plain,(
    ! [X80,X79] : k5_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k2_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k4_xboole_0(X79,X80))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k5_xboole_0(X80,X79)),k4_xboole_0(k3_xboole_0(X79,X79),X80)) ),
    inference(forward_demodulation,[],[f16425,f5562])).

fof(f16425,plain,(
    ! [X80,X79] : k5_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k2_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k4_xboole_0(X79,X80))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k5_xboole_0(X80,X79)),k4_xboole_0(X79,k2_xboole_0(X80,k4_xboole_0(X80,X79)))) ),
    inference(forward_demodulation,[],[f16424,f8038])).

fof(f16424,plain,(
    ! [X80,X79] : k5_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k2_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k4_xboole_0(X79,X80))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k5_xboole_0(X80,X79)),k4_xboole_0(X79,k2_xboole_0(X80,k4_xboole_0(k3_xboole_0(X80,X80),X79)))) ),
    inference(forward_demodulation,[],[f16151,f20])).

fof(f16151,plain,(
    ! [X80,X79] : k5_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k2_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k4_xboole_0(X79,X80))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k5_xboole_0(X80,X79)),k4_xboole_0(k4_xboole_0(X79,X80),k4_xboole_0(k3_xboole_0(X80,X80),X79))) ),
    inference(superposition,[],[f714,f5579])).

fof(f67734,plain,(
    ! [X107,X106] : k5_xboole_0(X107,k3_xboole_0(X107,k3_xboole_0(X106,X106))) = k5_xboole_0(k4_xboole_0(X106,k3_xboole_0(X106,X107)),k5_xboole_0(X106,X107)) ),
    inference(forward_demodulation,[],[f67626,f32479])).

fof(f67626,plain,(
    ! [X107,X106] : k5_xboole_0(X107,k3_xboole_0(X107,k3_xboole_0(X106,X106))) = k5_xboole_0(k4_xboole_0(k3_xboole_0(X106,X106),X107),k5_xboole_0(X106,X107)) ),
    inference(superposition,[],[f34190,f66331])).

fof(f66331,plain,(
    ! [X47,X46] : k5_xboole_0(X46,X47) = k5_xboole_0(k3_xboole_0(X46,X46),X47) ),
    inference(forward_demodulation,[],[f66303,f32500])).

fof(f32500,plain,(
    ! [X24,X23] : k5_xboole_0(X23,X24) = k2_xboole_0(k5_xboole_0(X24,X23),k4_xboole_0(X23,k3_xboole_0(X23,X24))) ),
    inference(backward_demodulation,[],[f5596,f32479])).

fof(f5596,plain,(
    ! [X24,X23] : k5_xboole_0(X23,X24) = k2_xboole_0(k5_xboole_0(X24,X23),k4_xboole_0(k3_xboole_0(X23,X23),X24)) ),
    inference(backward_demodulation,[],[f2292,f5562])).

fof(f2292,plain,(
    ! [X24,X23] : k5_xboole_0(X23,X24) = k2_xboole_0(k5_xboole_0(X24,X23),k4_xboole_0(X23,k2_xboole_0(X24,k4_xboole_0(X24,X23)))) ),
    inference(forward_demodulation,[],[f2291,f165])).

fof(f2291,plain,(
    ! [X24,X23] : k2_xboole_0(k4_xboole_0(X24,X23),k5_xboole_0(X23,X24)) = k2_xboole_0(k5_xboole_0(X24,X23),k4_xboole_0(X23,k2_xboole_0(X24,k4_xboole_0(X24,X23)))) ),
    inference(forward_demodulation,[],[f2231,f41])).

fof(f2231,plain,(
    ! [X24,X23] : k2_xboole_0(k4_xboole_0(X24,X23),k5_xboole_0(X23,X24)) = k2_xboole_0(k5_xboole_0(X24,X23),k4_xboole_0(k5_xboole_0(X23,X24),k4_xboole_0(X24,X23))) ),
    inference(superposition,[],[f307,f86])).

fof(f66303,plain,(
    ! [X47,X46] : k5_xboole_0(k3_xboole_0(X46,X46),X47) = k2_xboole_0(k5_xboole_0(X47,X46),k4_xboole_0(X46,k3_xboole_0(X46,X47))) ),
    inference(backward_demodulation,[],[f33356,f66299])).

fof(f66299,plain,(
    ! [X83,X84] : k5_xboole_0(X83,X84) = k5_xboole_0(X83,k3_xboole_0(X84,X84)) ),
    inference(forward_demodulation,[],[f66298,f64204])).

fof(f64204,plain,(
    ! [X92,X93] : k5_xboole_0(X92,X93) = k2_xboole_0(k4_xboole_0(X93,k3_xboole_0(X93,X92)),k4_xboole_0(X92,k3_xboole_0(X93,X92))) ),
    inference(superposition,[],[f32975,f63047])).

fof(f63047,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(superposition,[],[f62989,f60514])).

fof(f32975,plain,(
    ! [X15,X16] : k5_xboole_0(X16,X15) = k2_xboole_0(k4_xboole_0(X15,k3_xboole_0(X15,X16)),k4_xboole_0(X16,k3_xboole_0(X16,X15))) ),
    inference(forward_demodulation,[],[f32555,f32479])).

fof(f32555,plain,(
    ! [X15,X16] : k5_xboole_0(X16,X15) = k2_xboole_0(k4_xboole_0(X15,k3_xboole_0(X15,X16)),k4_xboole_0(k3_xboole_0(X16,X16),X15)) ),
    inference(backward_demodulation,[],[f8052,f32479])).

fof(f8052,plain,(
    ! [X15,X16] : k5_xboole_0(X16,X15) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X15,X15),X16),k4_xboole_0(k3_xboole_0(X16,X16),X15)) ),
    inference(backward_demodulation,[],[f5599,f8046])).

fof(f5599,plain,(
    ! [X15,X16] : k5_xboole_0(X16,X15) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X15,X15),X16),k3_xboole_0(k5_xboole_0(X15,X16),k4_xboole_0(X16,X15))) ),
    inference(backward_demodulation,[],[f2302,f5562])).

fof(f2302,plain,(
    ! [X15,X16] : k5_xboole_0(X16,X15) = k2_xboole_0(k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(X16,X15))),k3_xboole_0(k5_xboole_0(X15,X16),k4_xboole_0(X16,X15))) ),
    inference(backward_demodulation,[],[f930,f2301])).

fof(f930,plain,(
    ! [X15,X16] : k2_xboole_0(k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(X16,X15))),k3_xboole_0(k5_xboole_0(X15,X16),k4_xboole_0(X16,X15))) = k2_xboole_0(k5_xboole_0(X15,X16),k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(X16,X15)))) ),
    inference(superposition,[],[f29,f41])).

fof(f66298,plain,(
    ! [X83,X84] : k5_xboole_0(X83,k3_xboole_0(X84,X84)) = k2_xboole_0(k4_xboole_0(X84,k3_xboole_0(X84,X83)),k4_xboole_0(X83,k3_xboole_0(X84,X83))) ),
    inference(forward_demodulation,[],[f66203,f32479])).

fof(f66203,plain,(
    ! [X83,X84] : k5_xboole_0(X83,k3_xboole_0(X84,X84)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X84,X84),X83),k4_xboole_0(X83,k3_xboole_0(X84,X83))) ),
    inference(superposition,[],[f32492,f63363])).

fof(f33356,plain,(
    ! [X47,X46] : k5_xboole_0(k3_xboole_0(X46,X46),X47) = k2_xboole_0(k5_xboole_0(X47,k3_xboole_0(X46,X46)),k4_xboole_0(X46,k3_xboole_0(X46,X47))) ),
    inference(superposition,[],[f86,f32479])).

fof(f34190,plain,(
    ! [X24,X23] : k5_xboole_0(X23,k3_xboole_0(X23,X24)) = k5_xboole_0(k4_xboole_0(X24,X23),k5_xboole_0(X24,X23)) ),
    inference(forward_demodulation,[],[f34189,f86])).

fof(f34189,plain,(
    ! [X24,X23] : k5_xboole_0(k4_xboole_0(X24,X23),k2_xboole_0(k5_xboole_0(X23,X24),k4_xboole_0(X24,X23))) = k5_xboole_0(X23,k3_xboole_0(X23,X24)) ),
    inference(forward_demodulation,[],[f34188,f26088])).

fof(f34188,plain,(
    ! [X24,X23] : k5_xboole_0(k4_xboole_0(X24,X23),k2_xboole_0(k5_xboole_0(X23,X24),k4_xboole_0(X24,X23))) = k2_xboole_0(k4_xboole_0(X23,k2_xboole_0(X24,X23)),k4_xboole_0(X23,k3_xboole_0(X23,X24))) ),
    inference(forward_demodulation,[],[f34187,f28284])).

fof(f28284,plain,(
    ! [X88,X87] : k4_xboole_0(X87,k2_xboole_0(X88,X87)) = k4_xboole_0(X88,k2_xboole_0(X87,k2_xboole_0(X88,k5_xboole_0(X87,X88)))) ),
    inference(forward_demodulation,[],[f28283,f7955])).

fof(f7955,plain,(
    ! [X31,X32] : k4_xboole_0(X31,k2_xboole_0(X32,X31)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X31,X31),X32),k5_xboole_0(X31,X32)) ),
    inference(backward_demodulation,[],[f6363,f7927])).

fof(f6363,plain,(
    ! [X31,X32] : k4_xboole_0(X31,k2_xboole_0(X32,k5_xboole_0(X31,X32))) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X31,X31),X32),k5_xboole_0(X31,X32)) ),
    inference(forward_demodulation,[],[f6362,f1589])).

fof(f6362,plain,(
    ! [X31,X32] : k4_xboole_0(X31,k2_xboole_0(X32,k5_xboole_0(X31,X32))) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X31,k4_xboole_0(X31,X32)),X32),k5_xboole_0(X31,X32)) ),
    inference(forward_demodulation,[],[f6361,f443])).

fof(f6361,plain,(
    ! [X31,X32] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X31,X32),k4_xboole_0(X31,X32)),k5_xboole_0(X31,X32)) = k4_xboole_0(X31,k2_xboole_0(X32,k5_xboole_0(X31,X32))) ),
    inference(forward_demodulation,[],[f6360,f5600])).

fof(f6360,plain,(
    ! [X31,X32] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X31,X32),k4_xboole_0(X31,X32)),k5_xboole_0(X31,X32)) = k4_xboole_0(k5_xboole_0(X31,k2_xboole_0(X32,X31)),k4_xboole_0(k3_xboole_0(X32,X32),X31)) ),
    inference(forward_demodulation,[],[f6280,f5564])).

fof(f6280,plain,(
    ! [X31,X32] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X31,X32),k4_xboole_0(X31,X32)),k5_xboole_0(X31,X32)) = k4_xboole_0(k5_xboole_0(X31,k2_xboole_0(X32,X31)),k4_xboole_0(k5_xboole_0(X31,X32),k4_xboole_0(X31,X32))) ),
    inference(superposition,[],[f5563,f991])).

fof(f28283,plain,(
    ! [X88,X87] : k4_xboole_0(X88,k2_xboole_0(X87,k2_xboole_0(X88,k5_xboole_0(X87,X88)))) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X87,X87),X88),k5_xboole_0(X87,X88)) ),
    inference(forward_demodulation,[],[f28282,f1589])).

fof(f28282,plain,(
    ! [X88,X87] : k4_xboole_0(X88,k2_xboole_0(X87,k2_xboole_0(X88,k5_xboole_0(X87,X88)))) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X87,k4_xboole_0(X87,X88)),X88),k5_xboole_0(X87,X88)) ),
    inference(forward_demodulation,[],[f28281,f443])).

fof(f28281,plain,(
    ! [X88,X87] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X87,X88),k4_xboole_0(X87,X88)),k5_xboole_0(X87,X88)) = k4_xboole_0(X88,k2_xboole_0(X87,k2_xboole_0(X88,k5_xboole_0(X87,X88)))) ),
    inference(forward_demodulation,[],[f28280,f28262])).

fof(f28262,plain,(
    ! [X81,X82] : k3_xboole_0(k5_xboole_0(X82,k5_xboole_0(X81,k5_xboole_0(X81,X82))),k4_xboole_0(X82,k2_xboole_0(X81,X82))) = k4_xboole_0(X81,k2_xboole_0(X82,k2_xboole_0(X81,k5_xboole_0(X82,X81)))) ),
    inference(forward_demodulation,[],[f28261,f12516])).

fof(f28261,plain,(
    ! [X81,X82] : k3_xboole_0(k5_xboole_0(X82,k5_xboole_0(X81,k5_xboole_0(X81,X82))),k4_xboole_0(X82,k2_xboole_0(X81,X82))) = k4_xboole_0(X81,k2_xboole_0(X82,k2_xboole_0(k5_xboole_0(X82,X81),X81))) ),
    inference(forward_demodulation,[],[f28260,f1118])).

fof(f28260,plain,(
    ! [X81,X82] : k3_xboole_0(k5_xboole_0(X82,k5_xboole_0(X81,k5_xboole_0(X81,X82))),k4_xboole_0(X82,k2_xboole_0(X81,X82))) = k4_xboole_0(X81,k2_xboole_0(X82,k2_xboole_0(k5_xboole_0(X82,X81),k4_xboole_0(X81,X82)))) ),
    inference(forward_demodulation,[],[f28259,f12516])).

fof(f28259,plain,(
    ! [X81,X82] : k3_xboole_0(k5_xboole_0(X82,k5_xboole_0(X81,k5_xboole_0(X81,X82))),k4_xboole_0(X82,k2_xboole_0(X81,X82))) = k4_xboole_0(X81,k2_xboole_0(X82,k2_xboole_0(k4_xboole_0(X81,X82),k5_xboole_0(X82,X81)))) ),
    inference(forward_demodulation,[],[f28258,f24792])).

fof(f24792,plain,(
    ! [X47,X48,X49] : k4_xboole_0(k3_xboole_0(X49,k4_xboole_0(X48,X47)),k5_xboole_0(X47,X48)) = k4_xboole_0(X48,k2_xboole_0(X47,k2_xboole_0(X49,k5_xboole_0(X47,X48)))) ),
    inference(backward_demodulation,[],[f19897,f24791])).

fof(f24791,plain,(
    ! [X99,X97,X98] : k4_xboole_0(k3_xboole_0(X99,k5_xboole_0(X97,X98)),k5_xboole_0(X98,X97)) = k4_xboole_0(X97,k2_xboole_0(X98,k2_xboole_0(X99,k5_xboole_0(X98,X97)))) ),
    inference(forward_demodulation,[],[f24790,f4798])).

fof(f4798,plain,(
    ! [X64,X62,X63] : k4_xboole_0(k5_xboole_0(X63,X62),k2_xboole_0(X64,k5_xboole_0(X63,X62))) = k4_xboole_0(X62,k2_xboole_0(X63,k2_xboole_0(X64,k5_xboole_0(X63,X62)))) ),
    inference(forward_demodulation,[],[f4703,f20])).

fof(f4703,plain,(
    ! [X64,X62,X63] : k4_xboole_0(k4_xboole_0(X62,X63),k2_xboole_0(X64,k5_xboole_0(X63,X62))) = k4_xboole_0(k5_xboole_0(X63,X62),k2_xboole_0(X64,k5_xboole_0(X63,X62))) ),
    inference(superposition,[],[f559,f165])).

fof(f24790,plain,(
    ! [X99,X97,X98] : k4_xboole_0(k3_xboole_0(X99,k5_xboole_0(X97,X98)),k5_xboole_0(X98,X97)) = k4_xboole_0(k5_xboole_0(X98,X97),k2_xboole_0(X99,k5_xboole_0(X98,X97))) ),
    inference(forward_demodulation,[],[f24555,f5484])).

fof(f24555,plain,(
    ! [X99,X97,X98] : k4_xboole_0(k3_xboole_0(X99,k5_xboole_0(X97,X98)),k5_xboole_0(X98,X97)) = k4_xboole_0(k4_xboole_0(X99,k5_xboole_0(X98,X97)),k4_xboole_0(X99,k5_xboole_0(X98,X97))) ),
    inference(superposition,[],[f1508,f1452])).

fof(f1452,plain,(
    ! [X28,X27] : k5_xboole_0(X28,X27) = k2_xboole_0(k5_xboole_0(X27,X28),k5_xboole_0(X28,X27)) ),
    inference(forward_demodulation,[],[f1401,f18])).

fof(f1401,plain,(
    ! [X28,X27] : k2_xboole_0(k4_xboole_0(X28,X27),k4_xboole_0(X27,X28)) = k2_xboole_0(k5_xboole_0(X27,X28),k2_xboole_0(k4_xboole_0(X28,X27),k4_xboole_0(X27,X28))) ),
    inference(superposition,[],[f84,f18])).

fof(f19897,plain,(
    ! [X47,X48,X49] : k4_xboole_0(k3_xboole_0(X49,k4_xboole_0(X48,X47)),k5_xboole_0(X47,X48)) = k4_xboole_0(k3_xboole_0(X49,k5_xboole_0(X48,X47)),k5_xboole_0(X47,X48)) ),
    inference(backward_demodulation,[],[f1711,f19796])).

fof(f19796,plain,(
    ! [X109,X107,X108] : k4_xboole_0(k3_xboole_0(X109,k5_xboole_0(X108,X107)),k5_xboole_0(X107,X108)) = k4_xboole_0(k4_xboole_0(X109,k5_xboole_0(X107,X108)),k4_xboole_0(X109,k5_xboole_0(X108,X107))) ),
    inference(superposition,[],[f448,f1452])).

fof(f1711,plain,(
    ! [X47,X48,X49] : k4_xboole_0(k3_xboole_0(X49,k4_xboole_0(X48,X47)),k5_xboole_0(X47,X48)) = k4_xboole_0(k4_xboole_0(X49,k5_xboole_0(X47,X48)),k4_xboole_0(X49,k5_xboole_0(X48,X47))) ),
    inference(superposition,[],[f448,f86])).

fof(f28258,plain,(
    ! [X81,X82] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X81,X82),k4_xboole_0(X81,X82)),k5_xboole_0(X82,X81)) = k3_xboole_0(k5_xboole_0(X82,k5_xboole_0(X81,k5_xboole_0(X81,X82))),k4_xboole_0(X82,k2_xboole_0(X81,X82))) ),
    inference(forward_demodulation,[],[f28257,f19])).

fof(f28257,plain,(
    ! [X81,X82] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X81,X82),k4_xboole_0(X81,X82)),k5_xboole_0(X82,X81)) = k3_xboole_0(k5_xboole_0(k5_xboole_0(X82,X81),k5_xboole_0(X81,X82)),k4_xboole_0(X82,k2_xboole_0(X81,X82))) ),
    inference(forward_demodulation,[],[f28256,f15096])).

fof(f28256,plain,(
    ! [X81,X82] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X81,X82),k4_xboole_0(X81,X82)),k5_xboole_0(X82,X81)) = k3_xboole_0(k5_xboole_0(k5_xboole_0(X82,X81),k5_xboole_0(X81,X82)),k4_xboole_0(X81,k2_xboole_0(X82,k5_xboole_0(X82,X81)))) ),
    inference(forward_demodulation,[],[f28081,f20])).

fof(f28081,plain,(
    ! [X81,X82] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X81,X82),k4_xboole_0(X81,X82)),k5_xboole_0(X82,X81)) = k3_xboole_0(k5_xboole_0(k5_xboole_0(X82,X81),k5_xboole_0(X81,X82)),k4_xboole_0(k4_xboole_0(X81,X82),k5_xboole_0(X82,X81))) ),
    inference(superposition,[],[f5570,f1736])).

fof(f28280,plain,(
    ! [X88,X87] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X87,X88),k4_xboole_0(X87,X88)),k5_xboole_0(X87,X88)) = k3_xboole_0(k5_xboole_0(X87,k5_xboole_0(X88,k5_xboole_0(X88,X87))),k4_xboole_0(X87,k2_xboole_0(X88,X87))) ),
    inference(forward_demodulation,[],[f28279,f19])).

fof(f28279,plain,(
    ! [X88,X87] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X87,X88),k4_xboole_0(X87,X88)),k5_xboole_0(X87,X88)) = k3_xboole_0(k5_xboole_0(k5_xboole_0(X87,X88),k5_xboole_0(X88,X87)),k4_xboole_0(X87,k2_xboole_0(X88,X87))) ),
    inference(forward_demodulation,[],[f28278,f7927])).

fof(f28278,plain,(
    ! [X88,X87] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X87,X88),k4_xboole_0(X87,X88)),k5_xboole_0(X87,X88)) = k3_xboole_0(k5_xboole_0(k5_xboole_0(X87,X88),k5_xboole_0(X88,X87)),k4_xboole_0(X87,k2_xboole_0(X88,k5_xboole_0(X87,X88)))) ),
    inference(forward_demodulation,[],[f28084,f20])).

fof(f28084,plain,(
    ! [X88,X87] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X87,X88),k4_xboole_0(X87,X88)),k5_xboole_0(X87,X88)) = k3_xboole_0(k5_xboole_0(k5_xboole_0(X87,X88),k5_xboole_0(X88,X87)),k4_xboole_0(k4_xboole_0(X87,X88),k5_xboole_0(X87,X88))) ),
    inference(superposition,[],[f5570,f7291])).

fof(f7291,plain,(
    ! [X6,X5] : k5_xboole_0(X6,X5) = k2_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f7154,f5579])).

fof(f7154,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(X5,X6)) = k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(k3_xboole_0(X6,X6),X5)) ),
    inference(superposition,[],[f15,f5564])).

fof(f34187,plain,(
    ! [X24,X23] : k5_xboole_0(k4_xboole_0(X24,X23),k2_xboole_0(k5_xboole_0(X23,X24),k4_xboole_0(X24,X23))) = k2_xboole_0(k4_xboole_0(X24,k2_xboole_0(X23,k2_xboole_0(X24,k5_xboole_0(X23,X24)))),k4_xboole_0(X23,k3_xboole_0(X23,X24))) ),
    inference(forward_demodulation,[],[f34186,f12516])).

fof(f34186,plain,(
    ! [X24,X23] : k5_xboole_0(k4_xboole_0(X24,X23),k2_xboole_0(k5_xboole_0(X23,X24),k4_xboole_0(X24,X23))) = k2_xboole_0(k4_xboole_0(X24,k2_xboole_0(X23,k2_xboole_0(k5_xboole_0(X23,X24),X24))),k4_xboole_0(X23,k3_xboole_0(X23,X24))) ),
    inference(forward_demodulation,[],[f34185,f1118])).

fof(f34185,plain,(
    ! [X24,X23] : k5_xboole_0(k4_xboole_0(X24,X23),k2_xboole_0(k5_xboole_0(X23,X24),k4_xboole_0(X24,X23))) = k2_xboole_0(k4_xboole_0(X24,k2_xboole_0(X23,k2_xboole_0(k5_xboole_0(X23,X24),k4_xboole_0(X24,X23)))),k4_xboole_0(X23,k3_xboole_0(X23,X24))) ),
    inference(forward_demodulation,[],[f34184,f25180])).

fof(f25180,plain,(
    ! [X30,X31,X32] : k4_xboole_0(X30,k2_xboole_0(X31,k2_xboole_0(X32,k4_xboole_0(X30,X31)))) = k4_xboole_0(X32,k2_xboole_0(X32,k4_xboole_0(X30,X31))) ),
    inference(superposition,[],[f4741,f20])).

fof(f34184,plain,(
    ! [X24,X23] : k5_xboole_0(k4_xboole_0(X24,X23),k2_xboole_0(k5_xboole_0(X23,X24),k4_xboole_0(X24,X23))) = k2_xboole_0(k4_xboole_0(k5_xboole_0(X23,X24),k2_xboole_0(k5_xboole_0(X23,X24),k4_xboole_0(X24,X23))),k4_xboole_0(X23,k3_xboole_0(X23,X24))) ),
    inference(forward_demodulation,[],[f33878,f4741])).

fof(f33878,plain,(
    ! [X24,X23] : k5_xboole_0(k4_xboole_0(X24,X23),k2_xboole_0(k5_xboole_0(X23,X24),k4_xboole_0(X24,X23))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X24,X23),k2_xboole_0(k5_xboole_0(X23,X24),k4_xboole_0(X24,X23))),k4_xboole_0(X23,k3_xboole_0(X23,X24))) ),
    inference(superposition,[],[f32,f32485])).

fof(f55,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f13,f19])).

fof(f13,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:56:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (32230)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (32240)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (32233)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (32235)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (32244)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (32234)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (32237)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (32241)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (32232)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (32241)Refutation not found, incomplete strategy% (32241)------------------------------
% 0.22/0.48  % (32241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (32241)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (32241)Memory used [KB]: 10618
% 0.22/0.48  % (32243)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (32241)Time elapsed: 0.061 s
% 0.22/0.48  % (32241)------------------------------
% 0.22/0.48  % (32241)------------------------------
% 0.22/0.49  % (32236)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (32247)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (32231)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (32239)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (32245)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (32242)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.51  % (32238)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.52  % (32246)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 5.63/1.07  % (32234)Time limit reached!
% 5.63/1.07  % (32234)------------------------------
% 5.63/1.07  % (32234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.63/1.07  % (32234)Termination reason: Time limit
% 5.63/1.07  
% 5.63/1.07  % (32234)Memory used [KB]: 14583
% 5.63/1.07  % (32234)Time elapsed: 0.652 s
% 5.63/1.07  % (32234)------------------------------
% 5.63/1.07  % (32234)------------------------------
% 12.54/1.94  % (32235)Time limit reached!
% 12.54/1.94  % (32235)------------------------------
% 12.54/1.94  % (32235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.54/1.96  % (32235)Termination reason: Time limit
% 12.54/1.96  
% 12.54/1.96  % (32235)Memory used [KB]: 47973
% 12.54/1.96  % (32235)Time elapsed: 1.512 s
% 12.54/1.96  % (32235)------------------------------
% 12.54/1.96  % (32235)------------------------------
% 12.79/1.97  % (32236)Time limit reached!
% 12.79/1.97  % (32236)------------------------------
% 12.79/1.97  % (32236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.79/1.97  % (32236)Termination reason: Time limit
% 12.79/1.97  
% 12.79/1.97  % (32236)Memory used [KB]: 25458
% 12.79/1.97  % (32236)Time elapsed: 1.549 s
% 12.79/1.97  % (32236)------------------------------
% 12.79/1.97  % (32236)------------------------------
% 14.46/2.23  % (32232)Time limit reached!
% 14.46/2.23  % (32232)------------------------------
% 14.46/2.23  % (32232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.46/2.23  % (32232)Termination reason: Time limit
% 14.46/2.23  
% 14.46/2.23  % (32232)Memory used [KB]: 40425
% 14.46/2.23  % (32232)Time elapsed: 1.803 s
% 14.46/2.23  % (32232)------------------------------
% 14.46/2.23  % (32232)------------------------------
% 17.69/2.63  % (32242)Time limit reached!
% 17.69/2.63  % (32242)------------------------------
% 17.69/2.63  % (32242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.69/2.63  % (32242)Termination reason: Time limit
% 17.69/2.63  % (32242)Termination phase: Saturation
% 17.69/2.63  
% 17.69/2.63  % (32242)Memory used [KB]: 39146
% 17.69/2.63  % (32242)Time elapsed: 2.200 s
% 17.69/2.63  % (32242)------------------------------
% 17.69/2.63  % (32242)------------------------------
% 28.92/4.00  % (32233)Refutation found. Thanks to Tanya!
% 28.92/4.00  % SZS status Theorem for theBenchmark
% 28.92/4.00  % SZS output start Proof for theBenchmark
% 28.92/4.00  fof(f67738,plain,(
% 28.92/4.00    $false),
% 28.92/4.00    inference(subsumption_resolution,[],[f67737,f59166])).
% 28.92/4.00  fof(f59166,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k5_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X1,X0)))) )),
% 28.92/4.00    inference(superposition,[],[f59143,f14])).
% 28.92/4.00  fof(f14,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 28.92/4.00    inference(cnf_transformation,[],[f1])).
% 28.92/4.00  fof(f1,axiom,(
% 28.92/4.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 28.92/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 28.92/4.00  fof(f59143,plain,(
% 28.92/4.00    ( ! [X196,X195] : (k2_xboole_0(X195,X196) = k5_xboole_0(X196,k5_xboole_0(X196,k2_xboole_0(X195,X196)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f59142,f19314])).
% 28.92/4.00  fof(f19314,plain,(
% 28.92/4.00    ( ! [X41,X40] : (k2_xboole_0(X40,X41) = k5_xboole_0(k2_xboole_0(X40,X41),k4_xboole_0(X41,k2_xboole_0(X40,X41)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f19313,f84])).
% 28.92/4.00  fof(f84,plain,(
% 28.92/4.00    ( ! [X6,X7] : (k2_xboole_0(X6,X7) = k2_xboole_0(k2_xboole_0(X7,X6),k2_xboole_0(X6,X7))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f83,f25])).
% 28.92/4.00  fof(f25,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f24,f15])).
% 28.92/4.00  fof(f15,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 28.92/4.00    inference(cnf_transformation,[],[f3])).
% 28.92/4.00  fof(f3,axiom,(
% 28.92/4.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 28.92/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 28.92/4.00  fof(f24,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 28.92/4.00    inference(superposition,[],[f15,f16])).
% 28.92/4.00  fof(f16,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 28.92/4.00    inference(cnf_transformation,[],[f4])).
% 28.92/4.00  fof(f4,axiom,(
% 28.92/4.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 28.92/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 28.92/4.00  fof(f83,plain,(
% 28.92/4.00    ( ! [X6,X7] : (k2_xboole_0(X6,k2_xboole_0(X7,X6)) = k2_xboole_0(k2_xboole_0(X7,X6),k2_xboole_0(X6,X7))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f77,f14])).
% 28.92/4.00  fof(f77,plain,(
% 28.92/4.00    ( ! [X6,X7] : (k2_xboole_0(k2_xboole_0(X7,X6),X6) = k2_xboole_0(k2_xboole_0(X7,X6),k2_xboole_0(X6,X7))) )),
% 28.92/4.00    inference(superposition,[],[f25,f25])).
% 28.92/4.00  fof(f19313,plain,(
% 28.92/4.00    ( ! [X41,X40] : (k2_xboole_0(X40,X41) = k5_xboole_0(k2_xboole_0(k2_xboole_0(X41,X40),k2_xboole_0(X40,X41)),k4_xboole_0(X41,k2_xboole_0(X40,X41)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f19312,f5692])).
% 28.92/4.00  fof(f5692,plain,(
% 28.92/4.00    ( ! [X72,X73] : (k2_xboole_0(X72,X73) = k5_xboole_0(k2_xboole_0(X73,X72),k4_xboole_0(X73,k2_xboole_0(X72,X73)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f5691,f25])).
% 28.92/4.00  fof(f5691,plain,(
% 28.92/4.00    ( ! [X72,X73] : (k5_xboole_0(k2_xboole_0(X73,X72),k4_xboole_0(X73,k2_xboole_0(X72,X73))) = k2_xboole_0(X72,k2_xboole_0(X73,X72))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f5690,f14])).
% 28.92/4.00  fof(f5690,plain,(
% 28.92/4.00    ( ! [X72,X73] : (k2_xboole_0(k2_xboole_0(X73,X72),X72) = k5_xboole_0(k2_xboole_0(X73,X72),k4_xboole_0(X73,k2_xboole_0(X72,X73)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f5407,f5482])).
% 28.92/4.00  fof(f5482,plain,(
% 28.92/4.00    ( ! [X14,X15] : (k4_xboole_0(X14,k2_xboole_0(X15,X14)) = k4_xboole_0(k3_xboole_0(X15,X14),X14)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f5481,f69])).
% 28.92/4.00  fof(f69,plain,(
% 28.92/4.00    ( ! [X4,X5,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,X5)) = k4_xboole_0(X4,k2_xboole_0(X3,X5))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f59,f20])).
% 28.92/4.00  fof(f20,plain,(
% 28.92/4.00    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 28.92/4.00    inference(cnf_transformation,[],[f5])).
% 28.92/4.00  fof(f5,axiom,(
% 28.92/4.00    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 28.92/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 28.92/4.00  fof(f59,plain,(
% 28.92/4.00    ( ! [X4,X5,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,X5)) = k4_xboole_0(k4_xboole_0(X4,X3),X5)) )),
% 28.92/4.00    inference(superposition,[],[f20,f21])).
% 28.92/4.00  fof(f21,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 28.92/4.00    inference(superposition,[],[f16,f14])).
% 28.92/4.00  fof(f5481,plain,(
% 28.92/4.00    ( ! [X14,X15] : (k4_xboole_0(k2_xboole_0(X15,X14),k2_xboole_0(X15,X14)) = k4_xboole_0(k3_xboole_0(X15,X14),X14)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f5360,f515])).
% 28.92/4.00  fof(f515,plain,(
% 28.92/4.00    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X2),X1)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f504,f443])).
% 28.92/4.00  fof(f443,plain,(
% 28.92/4.00    ( ! [X4,X5,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(k3_xboole_0(X3,X5),X4)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f442,f355])).
% 28.92/4.00  fof(f355,plain,(
% 28.92/4.00    ( ! [X10,X8,X9] : (k4_xboole_0(k3_xboole_0(X8,X9),X10) = k4_xboole_0(X8,k2_xboole_0(X10,k4_xboole_0(X8,X9)))) )),
% 28.92/4.00    inference(superposition,[],[f60,f14])).
% 28.92/4.00  fof(f60,plain,(
% 28.92/4.00    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X6,X7),X8)) = k4_xboole_0(k3_xboole_0(X6,X7),X8)) )),
% 28.92/4.00    inference(superposition,[],[f20,f17])).
% 28.92/4.00  fof(f17,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 28.92/4.00    inference(cnf_transformation,[],[f6])).
% 28.92/4.00  fof(f6,axiom,(
% 28.92/4.00    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 28.92/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 28.92/4.00  fof(f442,plain,(
% 28.92/4.00    ( ! [X4,X5,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X5)))) )),
% 28.92/4.00    inference(backward_demodulation,[],[f72,f419])).
% 28.92/4.00  fof(f419,plain,(
% 28.92/4.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,k4_xboole_0(X2,X0)) = k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X0)))) )),
% 28.92/4.00    inference(superposition,[],[f66,f14])).
% 28.92/4.00  fof(f66,plain,(
% 28.92/4.00    ( ! [X10,X11,X9] : (k2_xboole_0(X11,k4_xboole_0(X9,X10)) = k2_xboole_0(X11,k4_xboole_0(X9,k2_xboole_0(X10,X11)))) )),
% 28.92/4.00    inference(superposition,[],[f15,f20])).
% 28.92/4.00  fof(f72,plain,(
% 28.92/4.00    ( ! [X4,X5,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k2_xboole_0(X4,X5))))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f62,f20])).
% 28.92/4.00  fof(f62,plain,(
% 28.92/4.00    ( ! [X4,X5,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(k4_xboole_0(X3,X4),X5)))) )),
% 28.92/4.00    inference(superposition,[],[f20,f17])).
% 28.92/4.00  fof(f504,plain,(
% 28.92/4.00    ( ! [X2,X0,X1] : (k3_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X2),X1)) )),
% 28.92/4.00    inference(superposition,[],[f443,f16])).
% 28.92/4.00  fof(f5360,plain,(
% 28.92/4.00    ( ! [X14,X15] : (k4_xboole_0(k2_xboole_0(X15,X14),k2_xboole_0(X15,X14)) = k4_xboole_0(k3_xboole_0(k2_xboole_0(X15,X14),X14),X14)) )),
% 28.92/4.00    inference(superposition,[],[f353,f160])).
% 28.92/4.00  fof(f160,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 28.92/4.00    inference(superposition,[],[f53,f14])).
% 28.92/4.00  fof(f53,plain,(
% 28.92/4.00    ( ! [X8,X7] : (k2_xboole_0(X7,X8) = k2_xboole_0(X7,k2_xboole_0(X7,X8))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f49,f15])).
% 28.92/4.00  fof(f49,plain,(
% 28.92/4.00    ( ! [X8,X7] : (k2_xboole_0(X7,k2_xboole_0(X7,X8)) = k2_xboole_0(X7,k4_xboole_0(X8,X7))) )),
% 28.92/4.00    inference(superposition,[],[f15,f21])).
% 28.92/4.00  fof(f353,plain,(
% 28.92/4.00    ( ! [X4,X5] : (k4_xboole_0(X4,k2_xboole_0(X5,X4)) = k4_xboole_0(k3_xboole_0(X4,X5),X5)) )),
% 28.92/4.00    inference(superposition,[],[f60,f211])).
% 28.92/4.00  fof(f211,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f210,f82])).
% 28.92/4.00  fof(f82,plain,(
% 28.92/4.00    ( ! [X4,X5] : (k2_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f81,f15])).
% 28.92/4.00  fof(f81,plain,(
% 28.92/4.00    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X5,X4)) = k2_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f76,f14])).
% 28.92/4.00  fof(f76,plain,(
% 28.92/4.00    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X5,X4),X4) = k2_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5))) )),
% 28.92/4.00    inference(superposition,[],[f25,f15])).
% 28.92/4.00  fof(f210,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,X0),X0) = k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f184,f15])).
% 28.92/4.00  fof(f184,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 28.92/4.00    inference(superposition,[],[f15,f23])).
% 28.92/4.00  fof(f23,plain,(
% 28.92/4.00    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4))) )),
% 28.92/4.00    inference(superposition,[],[f16,f15])).
% 28.92/4.00  fof(f5407,plain,(
% 28.92/4.00    ( ! [X72,X73] : (k2_xboole_0(k2_xboole_0(X73,X72),X72) = k5_xboole_0(k2_xboole_0(X73,X72),k4_xboole_0(k3_xboole_0(X72,X73),X73))) )),
% 28.92/4.00    inference(superposition,[],[f137,f353])).
% 28.92/4.00  fof(f137,plain,(
% 28.92/4.00    ( ! [X10,X9] : (k2_xboole_0(X10,X9) = k5_xboole_0(X10,k4_xboole_0(X9,X10))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f136,f15])).
% 28.92/4.00  fof(f136,plain,(
% 28.92/4.00    ( ! [X10,X9] : (k5_xboole_0(X10,k4_xboole_0(X9,X10)) = k2_xboole_0(X10,k4_xboole_0(X9,X10))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f135,f14])).
% 28.92/4.00  fof(f135,plain,(
% 28.92/4.00    ( ! [X10,X9] : (k5_xboole_0(X10,k4_xboole_0(X9,X10)) = k2_xboole_0(k4_xboole_0(X9,X10),X10)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f115,f15])).
% 28.92/4.00  fof(f115,plain,(
% 28.92/4.00    ( ! [X10,X9] : (k5_xboole_0(X10,k4_xboole_0(X9,X10)) = k2_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X10,k4_xboole_0(X9,X10)))) )),
% 28.92/4.00    inference(superposition,[],[f34,f50])).
% 28.92/4.00  fof(f50,plain,(
% 28.92/4.00    ( ! [X4,X5] : (k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f44,f21])).
% 28.92/4.00  fof(f44,plain,(
% 28.92/4.00    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X5,X4),X4) = k4_xboole_0(k2_xboole_0(X4,X5),X4)) )),
% 28.92/4.00    inference(superposition,[],[f21,f15])).
% 28.92/4.00  fof(f34,plain,(
% 28.92/4.00    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3)) = k5_xboole_0(X2,X3)) )),
% 28.92/4.00    inference(superposition,[],[f18,f14])).
% 28.92/4.00  fof(f18,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 28.92/4.00    inference(cnf_transformation,[],[f2])).
% 28.92/4.00  fof(f2,axiom,(
% 28.92/4.00    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 28.92/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 28.92/4.00  fof(f19312,plain,(
% 28.92/4.00    ( ! [X41,X40] : (k5_xboole_0(k2_xboole_0(k2_xboole_0(X41,X40),k2_xboole_0(X40,X41)),k4_xboole_0(X41,k2_xboole_0(X40,X41))) = k5_xboole_0(k2_xboole_0(X41,X40),k4_xboole_0(X41,k2_xboole_0(X40,X41)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f19183,f68])).
% 28.92/4.00  fof(f68,plain,(
% 28.92/4.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f58,f20])).
% 28.92/4.00  fof(f58,plain,(
% 28.92/4.00    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))) )),
% 28.92/4.00    inference(superposition,[],[f20,f16])).
% 28.92/4.00  fof(f19183,plain,(
% 28.92/4.00    ( ! [X41,X40] : (k5_xboole_0(k2_xboole_0(k2_xboole_0(X41,X40),k2_xboole_0(X40,X41)),k4_xboole_0(k2_xboole_0(X41,X40),k2_xboole_0(X40,X41))) = k5_xboole_0(k2_xboole_0(X41,X40),k4_xboole_0(k2_xboole_0(X41,X40),k2_xboole_0(X40,X41)))) )),
% 28.92/4.00    inference(superposition,[],[f828,f84])).
% 28.92/4.00  fof(f828,plain,(
% 28.92/4.00    ( ! [X12,X11] : (k5_xboole_0(k2_xboole_0(X11,X12),k4_xboole_0(X12,X11)) = k5_xboole_0(k2_xboole_0(X12,X11),k4_xboole_0(X12,X11))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f827,f16])).
% 28.92/4.00  fof(f827,plain,(
% 28.92/4.00    ( ! [X12,X11] : (k5_xboole_0(k2_xboole_0(X12,X11),k4_xboole_0(k2_xboole_0(X12,X11),X11)) = k5_xboole_0(k2_xboole_0(X11,X12),k4_xboole_0(X12,X11))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f826,f213])).
% 28.92/4.00  fof(f213,plain,(
% 28.92/4.00    ( ! [X4,X5] : (k5_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) = k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,k2_xboole_0(X4,X5)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f212,f53])).
% 28.92/4.00  fof(f212,plain,(
% 28.92/4.00    ( ! [X4,X5] : (k5_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) = k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,k2_xboole_0(X4,k2_xboole_0(X4,X5))))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f186,f20])).
% 28.92/4.00  fof(f186,plain,(
% 28.92/4.00    ( ! [X4,X5] : (k5_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) = k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5)))) )),
% 28.92/4.00    inference(superposition,[],[f18,f23])).
% 28.92/4.00  fof(f826,plain,(
% 28.92/4.00    ( ! [X12,X11] : (k5_xboole_0(k2_xboole_0(X12,X11),k4_xboole_0(k2_xboole_0(X12,X11),X11)) = k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(X12,X11)),k4_xboole_0(X12,k2_xboole_0(X11,X12)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f825,f193])).
% 28.92/4.00  fof(f193,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k3_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 28.92/4.00    inference(backward_demodulation,[],[f26,f171])).
% 28.92/4.00  fof(f171,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,X0))) )),
% 28.92/4.00    inference(superposition,[],[f23,f14])).
% 28.92/4.00  fof(f26,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k3_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 28.92/4.00    inference(superposition,[],[f17,f16])).
% 28.92/4.00  fof(f825,plain,(
% 28.92/4.00    ( ! [X12,X11] : (k5_xboole_0(k2_xboole_0(X12,X11),k4_xboole_0(k2_xboole_0(X12,X11),X11)) = k2_xboole_0(k3_xboole_0(k2_xboole_0(X12,X11),X11),k4_xboole_0(X12,k2_xboole_0(X11,X12)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f774,f68])).
% 28.92/4.00  fof(f774,plain,(
% 28.92/4.00    ( ! [X12,X11] : (k5_xboole_0(k2_xboole_0(X12,X11),k4_xboole_0(k2_xboole_0(X12,X11),X11)) = k2_xboole_0(k3_xboole_0(k2_xboole_0(X12,X11),X11),k4_xboole_0(k2_xboole_0(X12,X11),k2_xboole_0(X11,X12)))) )),
% 28.92/4.00    inference(superposition,[],[f39,f25])).
% 28.92/4.00  fof(f39,plain,(
% 28.92/4.00    ( ! [X2,X3] : (k5_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X2)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f31,f20])).
% 28.92/4.00  fof(f31,plain,(
% 28.92/4.00    ( ! [X2,X3] : (k5_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),X2))) )),
% 28.92/4.00    inference(superposition,[],[f18,f17])).
% 28.92/4.00  fof(f59142,plain,(
% 28.92/4.00    ( ! [X196,X195] : (k5_xboole_0(X196,k5_xboole_0(X196,k2_xboole_0(X195,X196))) = k5_xboole_0(k2_xboole_0(X195,X196),k4_xboole_0(X196,k2_xboole_0(X195,X196)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f59141,f34082])).
% 28.92/4.00  fof(f34082,plain,(
% 28.92/4.00    ( ! [X74,X73] : (k4_xboole_0(X73,k2_xboole_0(X74,X73)) = k4_xboole_0(X73,k2_xboole_0(X74,k3_xboole_0(X73,X73)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f34081,f32621])).
% 28.92/4.00  fof(f32621,plain,(
% 28.92/4.00    ( ! [X2,X3] : (k4_xboole_0(X3,k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k3_xboole_0(X2,X3)))) )),
% 28.92/4.00    inference(backward_demodulation,[],[f16915,f32479])).
% 28.92/4.00  fof(f32479,plain,(
% 28.92/4.00    ( ! [X6,X7] : (k4_xboole_0(X6,k3_xboole_0(X6,X7)) = k4_xboole_0(k3_xboole_0(X6,X6),X7)) )),
% 28.92/4.00    inference(backward_demodulation,[],[f5619,f32478])).
% 28.92/4.00  fof(f32478,plain,(
% 28.92/4.00    ( ! [X78,X77] : (k4_xboole_0(X77,k3_xboole_0(X77,X78)) = k4_xboole_0(k2_xboole_0(X77,k4_xboole_0(X77,X78)),k3_xboole_0(X77,X78))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f32477,f31349])).
% 28.92/4.00  fof(f31349,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(X0,k2_xboole_0(X1,X0)),k3_xboole_0(X0,X1))) )),
% 28.92/4.00    inference(backward_demodulation,[],[f1273,f31348])).
% 28.92/4.00  fof(f31348,plain,(
% 28.92/4.00    ( ! [X187,X186] : (k4_xboole_0(X186,k5_xboole_0(X186,k4_xboole_0(X186,X187))) = k4_xboole_0(X186,k3_xboole_0(X186,X187))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f31347,f27])).
% 28.92/4.00  fof(f27,plain,(
% 28.92/4.00    ( ! [X2,X3] : (k3_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 28.92/4.00    inference(superposition,[],[f17,f17])).
% 28.92/4.00  fof(f31347,plain,(
% 28.92/4.00    ( ! [X187,X186] : (k3_xboole_0(X186,k4_xboole_0(X186,X187)) = k4_xboole_0(X186,k5_xboole_0(X186,k4_xboole_0(X186,X187)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f30935,f31105])).
% 28.92/4.00  fof(f31105,plain,(
% 28.92/4.00    ( ! [X30,X31] : (k5_xboole_0(X30,k4_xboole_0(X30,X31)) = k5_xboole_0(k4_xboole_0(X30,X31),k2_xboole_0(X30,k5_xboole_0(X31,X31)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f31104,f134])).
% 28.92/4.00  fof(f134,plain,(
% 28.92/4.00    ( ! [X2,X3] : (k5_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,X2)),k3_xboole_0(X2,X3))) )),
% 28.92/4.00    inference(backward_demodulation,[],[f40,f133])).
% 28.92/4.00  fof(f133,plain,(
% 28.92/4.00    ( ! [X4,X5] : (k5_xboole_0(k4_xboole_0(X4,X5),X4) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f132,f39])).
% 28.92/4.00  fof(f132,plain,(
% 28.92/4.00    ( ! [X4,X5] : (k5_xboole_0(k4_xboole_0(X4,X5),X4) = k2_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,k2_xboole_0(X5,X4)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f113,f20])).
% 28.92/4.00  fof(f113,plain,(
% 28.92/4.00    ( ! [X4,X5] : (k5_xboole_0(k4_xboole_0(X4,X5),X4) = k2_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X4,X5),X4))) )),
% 28.92/4.00    inference(superposition,[],[f34,f17])).
% 28.92/4.00  fof(f40,plain,(
% 28.92/4.00    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X2,X3),X2) = k2_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,X2)),k3_xboole_0(X2,X3))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f33,f20])).
% 28.92/4.00  fof(f33,plain,(
% 28.92/4.00    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X2,X3),X2) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X2),k3_xboole_0(X2,X3))) )),
% 28.92/4.00    inference(superposition,[],[f18,f17])).
% 28.92/4.00  fof(f31104,plain,(
% 28.92/4.00    ( ! [X30,X31] : (k5_xboole_0(k4_xboole_0(X30,X31),k2_xboole_0(X30,k5_xboole_0(X31,X31))) = k2_xboole_0(k4_xboole_0(X30,k2_xboole_0(X31,X30)),k3_xboole_0(X30,X31))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f31103,f21137])).
% 28.92/4.00  fof(f21137,plain,(
% 28.92/4.00    ( ! [X130,X128,X129] : (k4_xboole_0(X129,k2_xboole_0(X128,X130)) = k4_xboole_0(X129,k2_xboole_0(X128,k2_xboole_0(X130,k5_xboole_0(X128,X128))))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f20722,f7772])).
% 28.92/4.00  fof(f7772,plain,(
% 28.92/4.00    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = k2_xboole_0(X2,k2_xboole_0(X3,X3))) )),
% 28.92/4.00    inference(backward_demodulation,[],[f3177,f7759])).
% 28.92/4.00  fof(f7759,plain,(
% 28.92/4.00    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = k2_xboole_0(k2_xboole_0(X3,X3),k4_xboole_0(X2,X3))) )),
% 28.92/4.00    inference(backward_demodulation,[],[f266,f7758])).
% 28.92/4.00  fof(f7758,plain,(
% 28.92/4.00    ( ! [X17,X16] : (k2_xboole_0(X16,X17) = k2_xboole_0(k2_xboole_0(X16,X16),X17)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f7757,f15])).
% 28.92/4.00  fof(f7757,plain,(
% 28.92/4.00    ( ! [X17,X16] : (k2_xboole_0(X16,k4_xboole_0(X17,X16)) = k2_xboole_0(k2_xboole_0(X16,X16),X17)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f7724,f407])).
% 28.92/4.00  fof(f407,plain,(
% 28.92/4.00    ( ! [X14,X15,X13] : (k2_xboole_0(X15,k4_xboole_0(X13,X14)) = k5_xboole_0(X15,k4_xboole_0(X13,k2_xboole_0(X14,X15)))) )),
% 28.92/4.00    inference(superposition,[],[f137,f20])).
% 28.92/4.00  fof(f7724,plain,(
% 28.92/4.00    ( ! [X17,X16] : (k2_xboole_0(k2_xboole_0(X16,X16),X17) = k5_xboole_0(X16,k4_xboole_0(X17,k2_xboole_0(X16,X16)))) )),
% 28.92/4.00    inference(superposition,[],[f7516,f137])).
% 28.92/4.00  fof(f7516,plain,(
% 28.92/4.00    ( ! [X2,X3] : (k5_xboole_0(X3,X2) = k5_xboole_0(k2_xboole_0(X3,X3),X2)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f7515,f5579])).
% 28.92/4.00  fof(f5579,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k3_xboole_0(X0,X0),X1))) )),
% 28.92/4.00    inference(backward_demodulation,[],[f978,f5562])).
% 28.92/4.00  fof(f5562,plain,(
% 28.92/4.00    ( ! [X39,X40] : (k4_xboole_0(X40,k2_xboole_0(X39,k4_xboole_0(X39,X40))) = k4_xboole_0(k3_xboole_0(X40,X40),X39)) )),
% 28.92/4.00    inference(backward_demodulation,[],[f2872,f5561])).
% 28.92/4.00  fof(f5561,plain,(
% 28.92/4.00    ( ! [X14,X13] : (k4_xboole_0(k3_xboole_0(X13,X13),X14) = k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X14,k2_xboole_0(X13,X14)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f5381,f5482])).
% 28.92/4.00  fof(f5381,plain,(
% 28.92/4.00    ( ! [X14,X13] : (k4_xboole_0(k3_xboole_0(X13,X13),X14) = k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k3_xboole_0(X13,X14),X14))) )),
% 28.92/4.00    inference(superposition,[],[f448,f353])).
% 28.92/4.00  fof(f448,plain,(
% 28.92/4.00    ( ! [X6,X8,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,k2_xboole_0(X7,X8))) = k4_xboole_0(k3_xboole_0(X6,X8),X7)) )),
% 28.92/4.00    inference(backward_demodulation,[],[f65,f443])).
% 28.92/4.00  fof(f65,plain,(
% 28.92/4.00    ( ! [X6,X8,X7] : (k3_xboole_0(k4_xboole_0(X6,X7),X8) = k4_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,k2_xboole_0(X7,X8)))) )),
% 28.92/4.00    inference(superposition,[],[f17,f20])).
% 28.92/4.00  fof(f2872,plain,(
% 28.92/4.00    ( ! [X39,X40] : (k4_xboole_0(k4_xboole_0(X40,X39),k4_xboole_0(X39,k2_xboole_0(X40,X39))) = k4_xboole_0(X40,k2_xboole_0(X39,k4_xboole_0(X39,X40)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f2871,f736])).
% 28.92/4.00  fof(f736,plain,(
% 28.92/4.00    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(X8,k2_xboole_0(X9,X8)),k4_xboole_0(X8,k2_xboole_0(X9,X8))) = k4_xboole_0(X9,k2_xboole_0(X8,k4_xboole_0(X8,X9)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f735,f66])).
% 28.92/4.00  fof(f735,plain,(
% 28.92/4.00    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(X8,k2_xboole_0(X9,X8)),k4_xboole_0(X8,k2_xboole_0(X9,X8))) = k4_xboole_0(X9,k2_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X9,X8))))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f664,f20])).
% 28.92/4.00  fof(f664,plain,(
% 28.92/4.00    ( ! [X8,X9] : (k4_xboole_0(k4_xboole_0(X9,X8),k4_xboole_0(X8,k2_xboole_0(X9,X8))) = k4_xboole_0(k5_xboole_0(X8,k2_xboole_0(X9,X8)),k4_xboole_0(X8,k2_xboole_0(X9,X8)))) )),
% 28.92/4.00    inference(superposition,[],[f21,f32])).
% 28.92/4.00  fof(f32,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k5_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) )),
% 28.92/4.00    inference(superposition,[],[f18,f16])).
% 28.92/4.00  fof(f2871,plain,(
% 28.92/4.00    ( ! [X39,X40] : (k4_xboole_0(k4_xboole_0(X40,X39),k4_xboole_0(X39,k2_xboole_0(X40,X39))) = k4_xboole_0(k5_xboole_0(X39,k2_xboole_0(X40,X39)),k4_xboole_0(X39,k2_xboole_0(X40,X39)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f2870,f25])).
% 28.92/4.00  fof(f2870,plain,(
% 28.92/4.00    ( ! [X39,X40] : (k4_xboole_0(k4_xboole_0(X40,X39),k4_xboole_0(X39,k2_xboole_0(X40,k2_xboole_0(X39,X40)))) = k4_xboole_0(k5_xboole_0(X39,k2_xboole_0(X40,X39)),k4_xboole_0(X39,k2_xboole_0(X40,k2_xboole_0(X39,X40))))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f2869,f15])).
% 28.92/4.00  fof(f2869,plain,(
% 28.92/4.00    ( ! [X39,X40] : (k4_xboole_0(k4_xboole_0(X40,X39),k4_xboole_0(X39,k2_xboole_0(X40,k2_xboole_0(X39,k4_xboole_0(X40,X39))))) = k4_xboole_0(k5_xboole_0(X39,k2_xboole_0(X40,X39)),k4_xboole_0(X39,k2_xboole_0(X40,k2_xboole_0(X39,k4_xboole_0(X40,X39)))))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f2868,f71])).
% 28.92/4.00  fof(f71,plain,(
% 28.92/4.00    ( ! [X12,X10,X11,X9] : (k4_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X11),X12)) = k4_xboole_0(X9,k2_xboole_0(X10,k2_xboole_0(X11,X12)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f70,f20])).
% 28.92/4.00  fof(f70,plain,(
% 28.92/4.00    ( ! [X12,X10,X11,X9] : (k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X11,X12)) = k4_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X11),X12))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f61,f20])).
% 28.92/4.00  fof(f61,plain,(
% 28.92/4.00    ( ! [X12,X10,X11,X9] : (k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X11,X12)) = k4_xboole_0(k4_xboole_0(X9,k2_xboole_0(X10,X11)),X12)) )),
% 28.92/4.00    inference(superposition,[],[f20,f20])).
% 28.92/4.00  fof(f2868,plain,(
% 28.92/4.00    ( ! [X39,X40] : (k4_xboole_0(k4_xboole_0(X40,X39),k4_xboole_0(X39,k2_xboole_0(k2_xboole_0(X40,X39),k4_xboole_0(X40,X39)))) = k4_xboole_0(k5_xboole_0(X39,k2_xboole_0(X40,X39)),k4_xboole_0(X39,k2_xboole_0(k2_xboole_0(X40,X39),k4_xboole_0(X40,X39))))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f2793,f20])).
% 28.92/4.00  fof(f2793,plain,(
% 28.92/4.00    ( ! [X39,X40] : (k4_xboole_0(k4_xboole_0(X40,X39),k4_xboole_0(k4_xboole_0(X39,k2_xboole_0(X40,X39)),k4_xboole_0(X40,X39))) = k4_xboole_0(k5_xboole_0(X39,k2_xboole_0(X40,X39)),k4_xboole_0(k4_xboole_0(X39,k2_xboole_0(X40,X39)),k4_xboole_0(X40,X39)))) )),
% 28.92/4.00    inference(superposition,[],[f171,f32])).
% 28.92/4.00  fof(f978,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,X0))))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f923,f165])).
% 28.92/4.00  fof(f165,plain,(
% 28.92/4.00    ( ! [X10,X11] : (k5_xboole_0(X11,X10) = k2_xboole_0(k4_xboole_0(X10,X11),k5_xboole_0(X11,X10))) )),
% 28.92/4.00    inference(superposition,[],[f53,f34])).
% 28.92/4.00  fof(f923,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,X0),k5_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,X0))))) )),
% 28.92/4.00    inference(superposition,[],[f15,f41])).
% 28.92/4.00  fof(f41,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f36,f20])).
% 28.92/4.00  fof(f36,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 28.92/4.00    inference(superposition,[],[f16,f18])).
% 28.92/4.00  fof(f7515,plain,(
% 28.92/4.00    ( ! [X2,X3] : (k5_xboole_0(k2_xboole_0(X3,X3),X2) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X3,X3),X2))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f7514,f60])).
% 28.92/4.00  fof(f7514,plain,(
% 28.92/4.00    ( ! [X2,X3] : (k5_xboole_0(k2_xboole_0(X3,X3),X2) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,X3),X2)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f7513,f20])).
% 28.92/4.00  fof(f7513,plain,(
% 28.92/4.00    ( ! [X2,X3] : (k5_xboole_0(k2_xboole_0(X3,X3),X2) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X3)),X2))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f7512,f52])).
% 28.92/4.00  fof(f52,plain,(
% 28.92/4.00    ( ! [X6,X5] : (k3_xboole_0(k2_xboole_0(X5,X6),X5) = k4_xboole_0(X5,k4_xboole_0(X6,X5))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f48,f23])).
% 28.92/4.00  fof(f48,plain,(
% 28.92/4.00    ( ! [X6,X5] : (k3_xboole_0(k2_xboole_0(X5,X6),X5) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5))) )),
% 28.92/4.00    inference(superposition,[],[f17,f21])).
% 28.92/4.00  fof(f7512,plain,(
% 28.92/4.00    ( ! [X2,X3] : (k5_xboole_0(k2_xboole_0(X3,X3),X2) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(k2_xboole_0(X3,X3),X3),X2))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f7417,f284])).
% 28.92/4.00  fof(f284,plain,(
% 28.92/4.00    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k3_xboole_0(X4,k2_xboole_0(X5,X5))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f267,f17])).
% 28.92/4.00  fof(f267,plain,(
% 28.92/4.00    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,k2_xboole_0(X5,X5))) )),
% 28.92/4.00    inference(superposition,[],[f17,f100])).
% 28.92/4.00  fof(f100,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(X1,X1))) )),
% 28.92/4.00    inference(superposition,[],[f50,f20])).
% 28.92/4.00  fof(f7417,plain,(
% 28.92/4.00    ( ! [X2,X3] : (k5_xboole_0(k2_xboole_0(X3,X3),X2) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(k2_xboole_0(X3,X3),k2_xboole_0(X3,X3)),X2))) )),
% 28.92/4.00    inference(superposition,[],[f5579,f100])).
% 28.92/4.00  fof(f266,plain,(
% 28.92/4.00    ( ! [X2,X3] : (k2_xboole_0(k2_xboole_0(X3,X3),X2) = k2_xboole_0(k2_xboole_0(X3,X3),k4_xboole_0(X2,X3))) )),
% 28.92/4.00    inference(superposition,[],[f15,f100])).
% 28.92/4.00  fof(f3177,plain,(
% 28.92/4.00    ( ! [X2,X3] : (k2_xboole_0(k2_xboole_0(X3,X3),k4_xboole_0(X2,X3)) = k2_xboole_0(X2,k2_xboole_0(X3,X3))) )),
% 28.92/4.00    inference(superposition,[],[f2970,f100])).
% 28.92/4.00  fof(f2970,plain,(
% 28.92/4.00    ( ! [X4,X5] : (k2_xboole_0(X4,X5) = k2_xboole_0(X5,k4_xboole_0(X4,X5))) )),
% 28.92/4.00    inference(superposition,[],[f2903,f14])).
% 28.92/4.00  fof(f2903,plain,(
% 28.92/4.00    ( ! [X6,X5] : (k2_xboole_0(X5,X6) = k2_xboole_0(k4_xboole_0(X5,X6),X6)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f2902,f1163])).
% 28.92/4.00  fof(f1163,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X1,X0))) )),
% 28.92/4.00    inference(superposition,[],[f82,f14])).
% 28.92/4.00  fof(f2902,plain,(
% 28.92/4.00    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),X6) = k2_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,X6))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f2815,f15])).
% 28.92/4.00  fof(f2815,plain,(
% 28.92/4.00    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,X6)) = k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 28.92/4.00    inference(superposition,[],[f15,f171])).
% 28.92/4.00  fof(f20722,plain,(
% 28.92/4.00    ( ! [X130,X128,X129] : (k4_xboole_0(X129,k2_xboole_0(X130,k2_xboole_0(X128,X128))) = k4_xboole_0(X129,k2_xboole_0(X128,k2_xboole_0(X130,k5_xboole_0(X128,X128))))) )),
% 28.92/4.00    inference(superposition,[],[f1068,f12977])).
% 28.92/4.00  fof(f12977,plain,(
% 28.92/4.00    ( ! [X40] : (k2_xboole_0(X40,X40) = k2_xboole_0(k5_xboole_0(X40,X40),X40)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f12976,f6715])).
% 28.92/4.00  fof(f6715,plain,(
% 28.92/4.00    ( ! [X54,X53] : (k2_xboole_0(X53,X54) = k2_xboole_0(k2_xboole_0(X53,X54),k3_xboole_0(X53,X53))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f6714,f53])).
% 28.92/4.00  fof(f6714,plain,(
% 28.92/4.00    ( ! [X54,X53] : (k2_xboole_0(k2_xboole_0(X53,X54),k3_xboole_0(X53,X53)) = k2_xboole_0(X53,k2_xboole_0(X53,X54))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f6713,f14])).
% 28.92/4.00  fof(f6713,plain,(
% 28.92/4.00    ( ! [X54,X53] : (k2_xboole_0(k2_xboole_0(X53,X54),k3_xboole_0(X53,X53)) = k2_xboole_0(k2_xboole_0(X53,X54),X53)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f6672,f2634])).
% 28.92/4.00  fof(f2634,plain,(
% 28.92/4.00    ( ! [X30,X28,X29] : (k2_xboole_0(k2_xboole_0(X28,X30),k2_xboole_0(X28,X29)) = k2_xboole_0(k2_xboole_0(X28,X30),X29)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f2563,f15])).
% 28.92/4.00  fof(f2563,plain,(
% 28.92/4.00    ( ! [X30,X28,X29] : (k2_xboole_0(k2_xboole_0(X28,X30),k2_xboole_0(X28,X29)) = k2_xboole_0(k2_xboole_0(X28,X30),k4_xboole_0(X29,k2_xboole_0(X28,X30)))) )),
% 28.92/4.00    inference(superposition,[],[f15,f69])).
% 28.92/4.00  fof(f6672,plain,(
% 28.92/4.00    ( ! [X54,X53] : (k2_xboole_0(k2_xboole_0(X53,X54),k3_xboole_0(X53,X53)) = k2_xboole_0(k2_xboole_0(X53,X54),k2_xboole_0(X53,X53))) )),
% 28.92/4.00    inference(superposition,[],[f601,f6177])).
% 28.92/4.00  fof(f6177,plain,(
% 28.92/4.00    ( ! [X44] : (k2_xboole_0(k3_xboole_0(X44,X44),X44) = k2_xboole_0(X44,X44)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f6118,f211])).
% 28.92/4.00  fof(f6118,plain,(
% 28.92/4.00    ( ! [X44] : (k2_xboole_0(k3_xboole_0(X44,X44),X44) = k2_xboole_0(k4_xboole_0(X44,X44),X44)) )),
% 28.92/4.00    inference(superposition,[],[f2903,f5896])).
% 28.92/4.00  fof(f5896,plain,(
% 28.92/4.00    ( ! [X15] : (k4_xboole_0(X15,X15) = k4_xboole_0(k3_xboole_0(X15,X15),X15)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f5895,f17])).
% 28.92/4.00  fof(f5895,plain,(
% 28.92/4.00    ( ! [X15] : (k4_xboole_0(X15,X15) = k4_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X15)),X15)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f5894,f52])).
% 28.92/4.00  fof(f5894,plain,(
% 28.92/4.00    ( ! [X15] : (k4_xboole_0(X15,X15) = k4_xboole_0(k3_xboole_0(k2_xboole_0(X15,X15),X15),X15)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f5893,f284])).
% 28.92/4.00  fof(f5893,plain,(
% 28.92/4.00    ( ! [X15] : (k4_xboole_0(X15,X15) = k4_xboole_0(k3_xboole_0(k2_xboole_0(X15,X15),k2_xboole_0(X15,X15)),X15)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f5892,f1939])).
% 28.92/4.00  fof(f1939,plain,(
% 28.92/4.00    ( ! [X2] : (k4_xboole_0(X2,X2) = k4_xboole_0(X2,k2_xboole_0(X2,k5_xboole_0(X2,X2)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f1938,f16])).
% 28.92/4.00  fof(f1938,plain,(
% 28.92/4.00    ( ! [X2] : (k4_xboole_0(X2,k2_xboole_0(X2,k5_xboole_0(X2,X2))) = k4_xboole_0(k2_xboole_0(X2,X2),X2)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f1937,f100])).
% 28.92/4.00  fof(f1937,plain,(
% 28.92/4.00    ( ! [X2] : (k4_xboole_0(X2,k2_xboole_0(X2,k5_xboole_0(X2,X2))) = k4_xboole_0(k2_xboole_0(X2,X2),k2_xboole_0(X2,X2))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f1936,f15])).
% 28.92/4.00  fof(f1936,plain,(
% 28.92/4.00    ( ! [X2] : (k4_xboole_0(k2_xboole_0(X2,X2),k2_xboole_0(X2,k4_xboole_0(X2,X2))) = k4_xboole_0(X2,k2_xboole_0(X2,k5_xboole_0(X2,X2)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f1935,f1734])).
% 28.92/4.00  fof(f1734,plain,(
% 28.92/4.00    ( ! [X6,X7] : (k4_xboole_0(X7,k2_xboole_0(X6,k5_xboole_0(X6,X7))) = k4_xboole_0(k5_xboole_0(X7,X6),k5_xboole_0(X6,X7))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f1693,f20])).
% 28.92/4.00  fof(f1693,plain,(
% 28.92/4.00    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X7,X6),k5_xboole_0(X6,X7)) = k4_xboole_0(k5_xboole_0(X7,X6),k5_xboole_0(X6,X7))) )),
% 28.92/4.00    inference(superposition,[],[f21,f86])).
% 28.92/4.00  fof(f86,plain,(
% 28.92/4.00    ( ! [X8,X9] : (k2_xboole_0(k5_xboole_0(X8,X9),k4_xboole_0(X9,X8)) = k5_xboole_0(X9,X8)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f85,f18])).
% 28.92/4.00  fof(f85,plain,(
% 28.92/4.00    ( ! [X8,X9] : (k2_xboole_0(k4_xboole_0(X9,X8),k4_xboole_0(X8,X9)) = k2_xboole_0(k5_xboole_0(X8,X9),k4_xboole_0(X9,X8))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f78,f14])).
% 28.92/4.00  fof(f78,plain,(
% 28.92/4.00    ( ! [X8,X9] : (k2_xboole_0(k4_xboole_0(X9,X8),k4_xboole_0(X8,X9)) = k2_xboole_0(k4_xboole_0(X9,X8),k5_xboole_0(X8,X9))) )),
% 28.92/4.00    inference(superposition,[],[f25,f18])).
% 28.92/4.00  fof(f1935,plain,(
% 28.92/4.00    ( ! [X2] : (k4_xboole_0(k2_xboole_0(X2,X2),k2_xboole_0(X2,k4_xboole_0(X2,X2))) = k4_xboole_0(k5_xboole_0(X2,X2),k5_xboole_0(X2,X2))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f1934,f259])).
% 28.92/4.00  fof(f259,plain,(
% 28.92/4.00    ( ! [X4,X5] : (k4_xboole_0(X5,k4_xboole_0(X4,X4)) = k4_xboole_0(X5,k5_xboole_0(X4,X4))) )),
% 28.92/4.00    inference(superposition,[],[f100,f34])).
% 28.92/4.00  fof(f1934,plain,(
% 28.92/4.00    ( ! [X2] : (k4_xboole_0(k2_xboole_0(X2,X2),k2_xboole_0(X2,k4_xboole_0(X2,X2))) = k4_xboole_0(k5_xboole_0(X2,X2),k4_xboole_0(X2,X2))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f1922,f100])).
% 28.92/4.00  fof(f1922,plain,(
% 28.92/4.00    ( ! [X2] : (k4_xboole_0(k2_xboole_0(X2,X2),k2_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(X2,X2)))) = k4_xboole_0(k5_xboole_0(X2,X2),k4_xboole_0(X2,k2_xboole_0(X2,X2)))) )),
% 28.92/4.00    inference(superposition,[],[f41,f1718])).
% 28.92/4.00  fof(f1718,plain,(
% 28.92/4.00    ( ! [X6] : (k5_xboole_0(X6,X6) = k5_xboole_0(k2_xboole_0(X6,X6),X6)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f1717,f86])).
% 28.92/4.00  fof(f1717,plain,(
% 28.92/4.00    ( ! [X6] : (k5_xboole_0(k2_xboole_0(X6,X6),X6) = k2_xboole_0(k5_xboole_0(X6,X6),k4_xboole_0(X6,X6))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f1676,f16])).
% 28.92/4.00  fof(f1676,plain,(
% 28.92/4.00    ( ! [X6] : (k5_xboole_0(k2_xboole_0(X6,X6),X6) = k2_xboole_0(k5_xboole_0(X6,X6),k4_xboole_0(k2_xboole_0(X6,X6),X6))) )),
% 28.92/4.00    inference(superposition,[],[f86,f704])).
% 28.92/4.00  fof(f704,plain,(
% 28.92/4.00    ( ! [X2] : (k5_xboole_0(X2,k2_xboole_0(X2,X2)) = k5_xboole_0(X2,X2)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f646,f18])).
% 28.92/4.00  fof(f646,plain,(
% 28.92/4.00    ( ! [X2] : (k5_xboole_0(X2,k2_xboole_0(X2,X2)) = k2_xboole_0(k4_xboole_0(X2,X2),k4_xboole_0(X2,X2))) )),
% 28.92/4.00    inference(superposition,[],[f32,f100])).
% 28.92/4.00  fof(f5892,plain,(
% 28.92/4.00    ( ! [X15] : (k4_xboole_0(k3_xboole_0(k2_xboole_0(X15,X15),k2_xboole_0(X15,X15)),X15) = k4_xboole_0(X15,k2_xboole_0(X15,k5_xboole_0(X15,X15)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f5891,f1734])).
% 28.92/4.00  fof(f5891,plain,(
% 28.92/4.00    ( ! [X15] : (k4_xboole_0(k3_xboole_0(k2_xboole_0(X15,X15),k2_xboole_0(X15,X15)),X15) = k4_xboole_0(k5_xboole_0(X15,X15),k5_xboole_0(X15,X15))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f5890,f259])).
% 28.92/4.00  fof(f5890,plain,(
% 28.92/4.00    ( ! [X15] : (k4_xboole_0(k3_xboole_0(k2_xboole_0(X15,X15),k2_xboole_0(X15,X15)),X15) = k4_xboole_0(k5_xboole_0(X15,X15),k4_xboole_0(X15,X15))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f5808,f100])).
% 28.92/4.00  fof(f5808,plain,(
% 28.92/4.00    ( ! [X15] : (k4_xboole_0(k3_xboole_0(k2_xboole_0(X15,X15),k2_xboole_0(X15,X15)),X15) = k4_xboole_0(k5_xboole_0(X15,X15),k4_xboole_0(X15,k2_xboole_0(X15,X15)))) )),
% 28.92/4.00    inference(superposition,[],[f5563,f1718])).
% 28.92/4.00  fof(f5563,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k3_xboole_0(X0,X0),X1)) )),
% 28.92/4.00    inference(backward_demodulation,[],[f41,f5562])).
% 28.92/4.00  fof(f601,plain,(
% 28.92/4.00    ( ! [X8,X7,X9] : (k2_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X7,X8)) = k2_xboole_0(k2_xboole_0(X8,X9),X7)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f575,f15])).
% 28.92/4.00  fof(f575,plain,(
% 28.92/4.00    ( ! [X8,X7,X9] : (k2_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X7,X8)) = k2_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X7,k2_xboole_0(X8,X9)))) )),
% 28.92/4.00    inference(superposition,[],[f15,f68])).
% 28.92/4.00  fof(f12976,plain,(
% 28.92/4.00    ( ! [X40] : (k2_xboole_0(k5_xboole_0(X40,X40),X40) = k2_xboole_0(k2_xboole_0(X40,X40),k3_xboole_0(X40,X40))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f12886,f3059])).
% 28.92/4.00  fof(f3059,plain,(
% 28.92/4.00    ( ! [X0] : (k3_xboole_0(X0,X0) = k4_xboole_0(X0,k5_xboole_0(X0,X0))) )),
% 28.92/4.00    inference(superposition,[],[f351,f97])).
% 28.92/4.00  fof(f97,plain,(
% 28.92/4.00    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5))) )),
% 28.92/4.00    inference(superposition,[],[f50,f17])).
% 28.92/4.00  fof(f351,plain,(
% 28.92/4.00    ( ! [X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k5_xboole_0(X1,X0))) )),
% 28.92/4.00    inference(superposition,[],[f60,f34])).
% 28.92/4.00  fof(f12886,plain,(
% 28.92/4.00    ( ! [X40] : (k2_xboole_0(k5_xboole_0(X40,X40),X40) = k2_xboole_0(k2_xboole_0(X40,X40),k4_xboole_0(X40,k5_xboole_0(X40,X40)))) )),
% 28.92/4.00    inference(superposition,[],[f307,f9809])).
% 28.92/4.00  fof(f9809,plain,(
% 28.92/4.00    ( ! [X17] : (k2_xboole_0(X17,X17) = k2_xboole_0(X17,k5_xboole_0(X17,X17))) )),
% 28.92/4.00    inference(backward_demodulation,[],[f9080,f9808])).
% 28.92/4.00  fof(f9808,plain,(
% 28.92/4.00    ( ! [X16] : (k2_xboole_0(X16,X16) = k5_xboole_0(k5_xboole_0(X16,X16),k2_xboole_0(X16,k5_xboole_0(X16,X16)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f9807,f14])).
% 28.92/4.00  fof(f9807,plain,(
% 28.92/4.00    ( ! [X16] : (k2_xboole_0(X16,X16) = k5_xboole_0(k5_xboole_0(X16,X16),k2_xboole_0(k5_xboole_0(X16,X16),X16))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f9806,f137])).
% 28.92/4.00  fof(f9806,plain,(
% 28.92/4.00    ( ! [X16] : (k5_xboole_0(k5_xboole_0(X16,X16),k2_xboole_0(k5_xboole_0(X16,X16),X16)) = k5_xboole_0(X16,k4_xboole_0(X16,X16))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f9805,f134])).
% 28.92/4.00  fof(f9805,plain,(
% 28.92/4.00    ( ! [X16] : (k5_xboole_0(k5_xboole_0(X16,X16),k2_xboole_0(k5_xboole_0(X16,X16),X16)) = k2_xboole_0(k4_xboole_0(X16,k2_xboole_0(X16,X16)),k3_xboole_0(X16,X16))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f9804,f7927])).
% 28.92/4.00  fof(f7927,plain,(
% 28.92/4.00    ( ! [X45,X44] : (k4_xboole_0(X44,k2_xboole_0(X45,X44)) = k4_xboole_0(X44,k2_xboole_0(X45,k5_xboole_0(X44,X45)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f7926,f25])).
% 28.92/4.00  fof(f7926,plain,(
% 28.92/4.00    ( ! [X45,X44] : (k4_xboole_0(X44,k2_xboole_0(X45,k5_xboole_0(X44,X45))) = k4_xboole_0(X44,k2_xboole_0(X45,k2_xboole_0(X44,X45)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f7925,f20])).
% 28.92/4.00  fof(f7925,plain,(
% 28.92/4.00    ( ! [X45,X44] : (k4_xboole_0(k4_xboole_0(X44,X45),k2_xboole_0(X44,X45)) = k4_xboole_0(X44,k2_xboole_0(X45,k5_xboole_0(X44,X45)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f7924,f5947])).
% 28.92/4.00  fof(f5947,plain,(
% 28.92/4.00    ( ! [X33,X32] : (k4_xboole_0(X32,k2_xboole_0(X33,k5_xboole_0(X32,X33))) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X32,X32),X33),k2_xboole_0(X32,X33))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f5946,f1589])).
% 28.92/4.00  fof(f1589,plain,(
% 28.92/4.00    ( ! [X6,X8,X7] : (k4_xboole_0(k3_xboole_0(X8,k4_xboole_0(X7,X6)),X6) = k4_xboole_0(k3_xboole_0(X8,X7),X6)) )),
% 28.92/4.00    inference(forward_demodulation,[],[f1510,f448])).
% 28.92/4.00  fof(f1510,plain,(
% 28.92/4.00    ( ! [X6,X8,X7] : (k4_xboole_0(k3_xboole_0(X8,k4_xboole_0(X7,X6)),X6) = k4_xboole_0(k4_xboole_0(X8,X6),k4_xboole_0(X8,k2_xboole_0(X6,X7)))) )),
% 28.92/4.00    inference(superposition,[],[f448,f15])).
% 28.92/4.00  fof(f5946,plain,(
% 28.92/4.00    ( ! [X33,X32] : (k4_xboole_0(X32,k2_xboole_0(X33,k5_xboole_0(X32,X33))) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X32,k4_xboole_0(X32,X33)),X33),k2_xboole_0(X32,X33))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f5945,f443])).
% 28.92/4.00  fof(f5945,plain,(
% 28.92/4.00    ( ! [X33,X32] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(X32,X33)),k2_xboole_0(X32,X33)) = k4_xboole_0(X32,k2_xboole_0(X33,k5_xboole_0(X32,X33)))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f5944,f2304])).
% 28.92/4.00  fof(f2304,plain,(
% 28.92/4.00    ( ! [X14,X15] : (k4_xboole_0(k5_xboole_0(k2_xboole_0(X14,X15),k4_xboole_0(X15,X14)),k4_xboole_0(X14,k4_xboole_0(X15,X14))) = k4_xboole_0(X15,k2_xboole_0(X14,k5_xboole_0(X15,X14)))) )),
% 28.92/4.00    inference(backward_demodulation,[],[f971,f2303])).
% 28.92/4.00  fof(f2303,plain,(
% 28.92/4.00    ( ! [X17,X16] : (k4_xboole_0(X17,k2_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X17,X16))))) = k4_xboole_0(X17,k2_xboole_0(X16,k5_xboole_0(X17,X16)))) )),
% 28.92/4.00    inference(backward_demodulation,[],[f975,f2301])).
% 28.92/4.00  fof(f2301,plain,(
% 28.92/4.00    ( ! [X33,X34] : (k5_xboole_0(X34,X33) = k2_xboole_0(k5_xboole_0(X33,X34),k4_xboole_0(X33,k2_xboole_0(X34,k4_xboole_0(X34,X33))))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f2300,f18])).
% 28.92/4.00  fof(f2300,plain,(
% 28.92/4.00    ( ! [X33,X34] : (k2_xboole_0(k4_xboole_0(X34,X33),k4_xboole_0(X33,X34)) = k2_xboole_0(k5_xboole_0(X33,X34),k4_xboole_0(X33,k2_xboole_0(X34,k4_xboole_0(X34,X33))))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f2236,f20])).
% 28.92/4.00  fof(f2236,plain,(
% 28.92/4.00    ( ! [X33,X34] : (k2_xboole_0(k4_xboole_0(X34,X33),k4_xboole_0(X33,X34)) = k2_xboole_0(k5_xboole_0(X33,X34),k4_xboole_0(k4_xboole_0(X33,X34),k4_xboole_0(X34,X33)))) )),
% 28.92/4.00    inference(superposition,[],[f307,f18])).
% 28.92/4.00  fof(f975,plain,(
% 28.92/4.00    ( ! [X17,X16] : (k4_xboole_0(X17,k2_xboole_0(X16,k2_xboole_0(k5_xboole_0(X16,X17),k4_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X17,X16)))))) = k4_xboole_0(X17,k2_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X17,X16)))))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f974,f741])).
% 28.92/4.00  fof(f741,plain,(
% 28.92/4.00    ( ! [X10,X11] : (k4_xboole_0(k5_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(X10,k2_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X10,X11)))))) )),
% 28.92/4.00    inference(forward_demodulation,[],[f740,f419])).
% 28.92/4.01  fof(f740,plain,(
% 28.92/4.01    ( ! [X10,X11] : (k4_xboole_0(k5_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(X10,k2_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11))))))) )),
% 28.92/4.01    inference(forward_demodulation,[],[f739,f71])).
% 28.92/4.01  fof(f739,plain,(
% 28.92/4.01    ( ! [X10,X11] : (k4_xboole_0(k5_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(X10,k2_xboole_0(k2_xboole_0(X11,X10),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11)))))) )),
% 28.92/4.01    inference(forward_demodulation,[],[f738,f20])).
% 28.92/4.01  fof(f738,plain,(
% 28.92/4.01    ( ! [X10,X11] : (k4_xboole_0(k4_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(k5_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11))))) )),
% 28.92/4.01    inference(forward_demodulation,[],[f737,f66])).
% 28.92/4.01  fof(f737,plain,(
% 28.92/4.01    ( ! [X10,X11] : (k4_xboole_0(k4_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,k2_xboole_0(X11,X10))))) = k4_xboole_0(k5_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,k2_xboole_0(X11,X10)))))) )),
% 28.92/4.01    inference(forward_demodulation,[],[f665,f20])).
% 28.92/4.03  fof(f665,plain,(
% 28.92/4.03    ( ! [X10,X11] : (k4_xboole_0(k4_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(k4_xboole_0(X11,X10),k4_xboole_0(X10,k2_xboole_0(X11,X10)))) = k4_xboole_0(k5_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(k4_xboole_0(X11,X10),k4_xboole_0(X10,k2_xboole_0(X11,X10))))) )),
% 28.92/4.03    inference(superposition,[],[f23,f32])).
% 28.92/4.03  fof(f974,plain,(
% 28.92/4.03    ( ! [X17,X16] : (k4_xboole_0(X17,k2_xboole_0(X16,k2_xboole_0(k5_xboole_0(X16,X17),k4_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X17,X16)))))) = k4_xboole_0(k5_xboole_0(X17,k2_xboole_0(X16,X17)),k4_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X17,X16))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f973,f130])).
% 28.92/4.03  fof(f130,plain,(
% 28.92/4.03    ( ! [X0,X1] : (k5_xboole_0(k2_xboole_0(X0,X1),X1) = k5_xboole_0(X1,k2_xboole_0(X0,X1))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f30,f111])).
% 28.92/4.03  fof(f111,plain,(
% 28.92/4.03    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X0,X1))) = k5_xboole_0(X1,k2_xboole_0(X0,X1))) )),
% 28.92/4.03    inference(superposition,[],[f34,f16])).
% 28.92/4.03  fof(f30,plain,(
% 28.92/4.03    ( ! [X0,X1] : (k5_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X0,X1)))) )),
% 28.92/4.03    inference(superposition,[],[f18,f16])).
% 28.92/4.03  fof(f973,plain,(
% 28.92/4.03    ( ! [X17,X16] : (k4_xboole_0(X17,k2_xboole_0(X16,k2_xboole_0(k5_xboole_0(X16,X17),k4_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X17,X16)))))) = k4_xboole_0(k5_xboole_0(k2_xboole_0(X16,X17),X17),k4_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X17,X16))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f972,f336])).
% 28.92/4.03  fof(f336,plain,(
% 28.92/4.03    ( ! [X6,X4,X5] : (k5_xboole_0(k4_xboole_0(X4,X5),k5_xboole_0(X5,X6)) = k5_xboole_0(k2_xboole_0(X5,X4),X6)) )),
% 28.92/4.03    inference(superposition,[],[f19,f109])).
% 28.92/4.03  fof(f109,plain,(
% 28.92/4.03    ( ! [X4,X5] : (k2_xboole_0(X5,X4) = k5_xboole_0(k4_xboole_0(X4,X5),X5)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f108,f15])).
% 28.92/4.03  fof(f108,plain,(
% 28.92/4.03    ( ! [X4,X5] : (k5_xboole_0(k4_xboole_0(X4,X5),X5) = k2_xboole_0(X5,k4_xboole_0(X4,X5))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f107,f14])).
% 28.92/4.03  fof(f107,plain,(
% 28.92/4.03    ( ! [X4,X5] : (k5_xboole_0(k4_xboole_0(X4,X5),X5) = k2_xboole_0(k4_xboole_0(X4,X5),X5)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f102,f15])).
% 28.92/4.03  fof(f102,plain,(
% 28.92/4.03    ( ! [X4,X5] : (k5_xboole_0(k4_xboole_0(X4,X5),X5) = k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X4,X5)))) )),
% 28.92/4.03    inference(superposition,[],[f18,f50])).
% 28.92/4.03  fof(f19,plain,(
% 28.92/4.03    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 28.92/4.03    inference(cnf_transformation,[],[f7])).
% 28.92/4.03  fof(f7,axiom,(
% 28.92/4.03    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 28.92/4.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 28.92/4.03  fof(f972,plain,(
% 28.92/4.03    ( ! [X17,X16] : (k4_xboole_0(k5_xboole_0(k4_xboole_0(X17,X16),k5_xboole_0(X16,X17)),k4_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X17,X16)))) = k4_xboole_0(X17,k2_xboole_0(X16,k2_xboole_0(k5_xboole_0(X16,X17),k4_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X17,X16))))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f920,f20])).
% 28.92/4.03  fof(f920,plain,(
% 28.92/4.03    ( ! [X17,X16] : (k4_xboole_0(k5_xboole_0(k4_xboole_0(X17,X16),k5_xboole_0(X16,X17)),k4_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X17,X16)))) = k4_xboole_0(k4_xboole_0(X17,X16),k2_xboole_0(k5_xboole_0(X16,X17),k4_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X17,X16)))))) )),
% 28.92/4.03    inference(superposition,[],[f41,f41])).
% 28.92/4.03  fof(f971,plain,(
% 28.92/4.03    ( ! [X14,X15] : (k4_xboole_0(X15,k2_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X15,X14))))) = k4_xboole_0(k5_xboole_0(k2_xboole_0(X14,X15),k4_xboole_0(X15,X14)),k4_xboole_0(X14,k4_xboole_0(X15,X14)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f970,f121])).
% 28.92/4.03  fof(f121,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2)) )),
% 28.92/4.03    inference(superposition,[],[f34,f18])).
% 28.92/4.03  fof(f970,plain,(
% 28.92/4.03    ( ! [X14,X15] : (k4_xboole_0(k5_xboole_0(k4_xboole_0(X15,X14),k2_xboole_0(X14,X15)),k4_xboole_0(X14,k4_xboole_0(X15,X14))) = k4_xboole_0(X15,k2_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X15,X14)))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f969,f53])).
% 28.92/4.03  fof(f969,plain,(
% 28.92/4.03    ( ! [X14,X15] : (k4_xboole_0(k5_xboole_0(k4_xboole_0(X15,X14),k2_xboole_0(X14,X15)),k4_xboole_0(X14,k4_xboole_0(X15,X14))) = k4_xboole_0(X15,k2_xboole_0(X14,k2_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X15,X14))))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f968,f20])).
% 28.92/4.03  fof(f968,plain,(
% 28.92/4.03    ( ! [X14,X15] : (k4_xboole_0(k5_xboole_0(k4_xboole_0(X15,X14),k2_xboole_0(X14,X15)),k4_xboole_0(X14,k4_xboole_0(X15,X14))) = k4_xboole_0(k4_xboole_0(X15,X14),k2_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X14,k4_xboole_0(X15,X14)))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f919,f71])).
% 28.92/4.03  fof(f919,plain,(
% 28.92/4.03    ( ! [X14,X15] : (k4_xboole_0(k5_xboole_0(k4_xboole_0(X15,X14),k2_xboole_0(X14,X15)),k4_xboole_0(X14,k4_xboole_0(X15,X14))) = k4_xboole_0(k4_xboole_0(X15,X14),k2_xboole_0(k2_xboole_0(X14,X15),k4_xboole_0(X14,k4_xboole_0(X15,X14))))) )),
% 28.92/4.03    inference(superposition,[],[f41,f23])).
% 28.92/4.03  fof(f5944,plain,(
% 28.92/4.03    ( ! [X33,X32] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(X32,X33)),k2_xboole_0(X32,X33)) = k4_xboole_0(k5_xboole_0(k2_xboole_0(X33,X32),k4_xboole_0(X32,X33)),k4_xboole_0(X33,k4_xboole_0(X32,X33)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f5828,f2900])).
% 28.92/4.03  fof(f2900,plain,(
% 28.92/4.03    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k5_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X1,X2))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f2899,f216])).
% 28.92/4.03  fof(f216,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X7,k2_xboole_0(X6,X7)),k4_xboole_0(X6,k4_xboole_0(X7,X6))) = k5_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f215,f121])).
% 28.92/4.03  fof(f215,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k5_xboole_0(k4_xboole_0(X7,X6),k2_xboole_0(X6,X7)) = k2_xboole_0(k4_xboole_0(X7,k2_xboole_0(X6,X7)),k4_xboole_0(X6,k4_xboole_0(X7,X6)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f214,f53])).
% 28.92/4.03  fof(f214,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k5_xboole_0(k4_xboole_0(X7,X6),k2_xboole_0(X6,X7)) = k2_xboole_0(k4_xboole_0(X7,k2_xboole_0(X6,k2_xboole_0(X6,X7))),k4_xboole_0(X6,k4_xboole_0(X7,X6)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f187,f20])).
% 28.92/4.03  fof(f187,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k5_xboole_0(k4_xboole_0(X7,X6),k2_xboole_0(X6,X7)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X7,X6),k2_xboole_0(X6,X7)),k4_xboole_0(X6,k4_xboole_0(X7,X6)))) )),
% 28.92/4.03    inference(superposition,[],[f18,f23])).
% 28.92/4.03  fof(f2899,plain,(
% 28.92/4.03    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X1)),k4_xboole_0(X2,k4_xboole_0(X1,X2)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f2813,f25])).
% 28.92/4.03  fof(f2813,plain,(
% 28.92/4.03    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X2))),k4_xboole_0(X2,k4_xboole_0(X1,X2)))) )),
% 28.92/4.03    inference(superposition,[],[f64,f171])).
% 28.92/4.03  fof(f64,plain,(
% 28.92/4.03    ( ! [X4,X5,X3] : (k5_xboole_0(k4_xboole_0(X3,X4),X5) = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X4,X5)),k4_xboole_0(X5,k4_xboole_0(X3,X4)))) )),
% 28.92/4.03    inference(superposition,[],[f18,f20])).
% 28.92/4.03  fof(f5828,plain,(
% 28.92/4.03    ( ! [X33,X32] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(X32,X33)),k2_xboole_0(X32,X33)) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X32,X33),k2_xboole_0(X32,X33)),k4_xboole_0(X33,k4_xboole_0(X32,X33)))) )),
% 28.92/4.03    inference(superposition,[],[f5563,f171])).
% 28.92/4.03  fof(f7924,plain,(
% 28.92/4.03    ( ! [X45,X44] : (k4_xboole_0(k4_xboole_0(X44,X45),k2_xboole_0(X44,X45)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X44,X44),X45),k2_xboole_0(X44,X45))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f7923,f1589])).
% 28.92/4.03  fof(f7923,plain,(
% 28.92/4.03    ( ! [X45,X44] : (k4_xboole_0(k4_xboole_0(X44,X45),k2_xboole_0(X44,X45)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X44,k4_xboole_0(X44,X45)),X45),k2_xboole_0(X44,X45))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f7835,f443])).
% 28.92/4.03  fof(f7835,plain,(
% 28.92/4.03    ( ! [X45,X44] : (k4_xboole_0(k4_xboole_0(X44,X45),k2_xboole_0(X44,X45)) = k4_xboole_0(k3_xboole_0(k4_xboole_0(X44,X45),k4_xboole_0(X44,X45)),k2_xboole_0(X44,X45))) )),
% 28.92/4.03    inference(superposition,[],[f5924,f2903])).
% 28.92/4.03  fof(f5924,plain,(
% 28.92/4.03    ( ! [X17,X18] : (k4_xboole_0(X17,k2_xboole_0(X17,X18)) = k4_xboole_0(k3_xboole_0(X17,X17),k2_xboole_0(X17,X18))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f5822,f1125])).
% 28.92/4.03  fof(f1125,plain,(
% 28.92/4.03    ( ! [X8,X7] : (k4_xboole_0(X7,k2_xboole_0(X7,X8)) = k4_xboole_0(k5_xboole_0(X7,k2_xboole_0(X7,X8)),k4_xboole_0(X8,X7))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f1119,f282])).
% 28.92/4.03  fof(f282,plain,(
% 28.92/4.03    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k2_xboole_0(X7,X8)) = k4_xboole_0(X6,k2_xboole_0(X7,k2_xboole_0(X8,X8)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f263,f20])).
% 28.92/4.03  fof(f263,plain,(
% 28.92/4.03    ( ! [X6,X8,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),X8) = k4_xboole_0(X6,k2_xboole_0(X7,k2_xboole_0(X8,X8)))) )),
% 28.92/4.03    inference(superposition,[],[f100,f20])).
% 28.92/4.03  fof(f1119,plain,(
% 28.92/4.03    ( ! [X8,X7] : (k4_xboole_0(k5_xboole_0(X7,k2_xboole_0(X7,X8)),k4_xboole_0(X8,X7)) = k4_xboole_0(X7,k2_xboole_0(X7,k2_xboole_0(X8,X8)))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f962,f1118])).
% 28.92/4.03  fof(f1118,plain,(
% 28.92/4.03    ( ! [X14,X17,X15,X16] : (k4_xboole_0(X17,k2_xboole_0(X14,k2_xboole_0(X15,X16))) = k4_xboole_0(X17,k2_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X16,X14))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f1117,f66])).
% 28.92/4.03  fof(f1117,plain,(
% 28.92/4.03    ( ! [X14,X17,X15,X16] : (k4_xboole_0(X17,k2_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X16,k2_xboole_0(X14,X15))))) = k4_xboole_0(X17,k2_xboole_0(X14,k2_xboole_0(X15,X16)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f1070,f71])).
% 28.92/4.03  fof(f1070,plain,(
% 28.92/4.03    ( ! [X14,X17,X15,X16] : (k4_xboole_0(X17,k2_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X16,k2_xboole_0(X14,X15))))) = k4_xboole_0(X17,k2_xboole_0(k2_xboole_0(X14,X15),X16))) )),
% 28.92/4.03    inference(superposition,[],[f71,f15])).
% 28.92/4.03  fof(f962,plain,(
% 28.92/4.03    ( ! [X8,X7] : (k4_xboole_0(k5_xboole_0(X7,k2_xboole_0(X7,X8)),k4_xboole_0(X8,X7)) = k4_xboole_0(X7,k2_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X8,X7))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f916,f71])).
% 28.92/4.03  fof(f916,plain,(
% 28.92/4.03    ( ! [X8,X7] : (k4_xboole_0(k5_xboole_0(X7,k2_xboole_0(X7,X8)),k4_xboole_0(X8,X7)) = k4_xboole_0(X7,k2_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X8,X7)))) )),
% 28.92/4.03    inference(superposition,[],[f41,f21])).
% 28.92/4.03  fof(f5822,plain,(
% 28.92/4.03    ( ! [X17,X18] : (k4_xboole_0(k3_xboole_0(X17,X17),k2_xboole_0(X17,X18)) = k4_xboole_0(k5_xboole_0(X17,k2_xboole_0(X17,X18)),k4_xboole_0(X18,X17))) )),
% 28.92/4.03    inference(superposition,[],[f5563,f21])).
% 28.92/4.03  fof(f9804,plain,(
% 28.92/4.03    ( ! [X16] : (k5_xboole_0(k5_xboole_0(X16,X16),k2_xboole_0(k5_xboole_0(X16,X16),X16)) = k2_xboole_0(k4_xboole_0(X16,k2_xboole_0(X16,k5_xboole_0(X16,X16))),k3_xboole_0(X16,X16))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f9803,f1479])).
% 28.92/4.03  fof(f1479,plain,(
% 28.92/4.03    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_xboole_0(X0,X1)) = k4_xboole_0(X2,k2_xboole_0(X1,X0))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f1478,f25])).
% 28.92/4.03  fof(f1478,plain,(
% 28.92/4.03    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_xboole_0(X1,X0)) = k4_xboole_0(X2,k2_xboole_0(X0,k2_xboole_0(X1,X0)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f1426,f53])).
% 28.92/4.03  fof(f1426,plain,(
% 28.92/4.03    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_xboole_0(X1,X0)) = k4_xboole_0(X2,k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X1,X0))))) )),
% 28.92/4.03    inference(superposition,[],[f71,f84])).
% 28.92/4.03  fof(f9803,plain,(
% 28.92/4.03    ( ! [X16] : (k5_xboole_0(k5_xboole_0(X16,X16),k2_xboole_0(k5_xboole_0(X16,X16),X16)) = k2_xboole_0(k4_xboole_0(X16,k2_xboole_0(k5_xboole_0(X16,X16),X16)),k3_xboole_0(X16,X16))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f9802,f5482])).
% 28.92/4.03  fof(f9802,plain,(
% 28.92/4.03    ( ! [X16] : (k5_xboole_0(k5_xboole_0(X16,X16),k2_xboole_0(k5_xboole_0(X16,X16),X16)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(k5_xboole_0(X16,X16),X16),X16),k3_xboole_0(X16,X16))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f9801,f353])).
% 28.92/4.03  fof(f9801,plain,(
% 28.92/4.03    ( ! [X16] : (k5_xboole_0(k5_xboole_0(X16,X16),k2_xboole_0(k5_xboole_0(X16,X16),X16)) = k2_xboole_0(k4_xboole_0(k5_xboole_0(X16,X16),k2_xboole_0(X16,k5_xboole_0(X16,X16))),k3_xboole_0(X16,X16))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f9568,f1479])).
% 28.92/4.03  fof(f9568,plain,(
% 28.92/4.03    ( ! [X16] : (k5_xboole_0(k5_xboole_0(X16,X16),k2_xboole_0(k5_xboole_0(X16,X16),X16)) = k2_xboole_0(k4_xboole_0(k5_xboole_0(X16,X16),k2_xboole_0(k5_xboole_0(X16,X16),X16)),k3_xboole_0(X16,X16))) )),
% 28.92/4.03    inference(superposition,[],[f46,f3059])).
% 28.92/4.03  fof(f46,plain,(
% 28.92/4.03    ( ! [X2,X1] : (k5_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X1,X2)),k4_xboole_0(X2,X1))) )),
% 28.92/4.03    inference(superposition,[],[f18,f21])).
% 28.92/4.03  fof(f9080,plain,(
% 28.92/4.03    ( ! [X17] : (k2_xboole_0(X17,k5_xboole_0(X17,X17)) = k5_xboole_0(k5_xboole_0(X17,X17),k2_xboole_0(X17,k5_xboole_0(X17,X17)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f8993,f7763])).
% 28.92/4.03  fof(f7763,plain,(
% 28.92/4.03    ( ! [X8,X9] : (k2_xboole_0(X9,X8) = k5_xboole_0(k4_xboole_0(X8,X9),k2_xboole_0(X9,X9))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f329,f7758])).
% 28.92/4.03  fof(f329,plain,(
% 28.92/4.03    ( ! [X8,X9] : (k2_xboole_0(k2_xboole_0(X9,X9),X8) = k5_xboole_0(k4_xboole_0(X8,X9),k2_xboole_0(X9,X9))) )),
% 28.92/4.03    inference(superposition,[],[f109,f100])).
% 28.92/4.03  fof(f8993,plain,(
% 28.92/4.03    ( ! [X17] : (k5_xboole_0(k5_xboole_0(X17,X17),k2_xboole_0(X17,k5_xboole_0(X17,X17))) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X17,X17),X17),k2_xboole_0(X17,X17))) )),
% 28.92/4.03    inference(superposition,[],[f991,f7553])).
% 28.92/4.03  fof(f7553,plain,(
% 28.92/4.03    ( ! [X16] : (k2_xboole_0(X16,X16) = k5_xboole_0(k5_xboole_0(X16,X16),X16)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f7552,f15])).
% 28.92/4.03  fof(f7552,plain,(
% 28.92/4.03    ( ! [X16] : (k5_xboole_0(k5_xboole_0(X16,X16),X16) = k2_xboole_0(X16,k4_xboole_0(X16,X16))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f7551,f243])).
% 28.92/4.03  fof(f243,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k2_xboole_0(X6,k4_xboole_0(X6,X7)) = k2_xboole_0(k3_xboole_0(X6,X7),k4_xboole_0(X6,X7))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f226,f14])).
% 28.92/4.03  fof(f226,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X6,X7),X6) = k2_xboole_0(k3_xboole_0(X6,X7),k4_xboole_0(X6,X7))) )),
% 28.92/4.03    inference(superposition,[],[f211,f17])).
% 28.92/4.03  fof(f7551,plain,(
% 28.92/4.03    ( ! [X16] : (k5_xboole_0(k5_xboole_0(X16,X16),X16) = k2_xboole_0(k3_xboole_0(X16,X16),k4_xboole_0(X16,X16))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f7422,f5923])).
% 28.92/4.03  fof(f5923,plain,(
% 28.92/4.03    ( ! [X16] : (k4_xboole_0(X16,X16) = k4_xboole_0(k3_xboole_0(k5_xboole_0(X16,X16),k5_xboole_0(X16,X16)),X16)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f5922,f5742])).
% 28.92/4.03  fof(f5742,plain,(
% 28.92/4.03    ( ! [X12] : (k4_xboole_0(k5_xboole_0(X12,k5_xboole_0(X12,X12)),k3_xboole_0(X12,X12)) = k4_xboole_0(X12,X12)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f5741,f100])).
% 28.92/4.03  fof(f5741,plain,(
% 28.92/4.03    ( ! [X12] : (k4_xboole_0(k5_xboole_0(X12,k5_xboole_0(X12,X12)),k3_xboole_0(X12,X12)) = k4_xboole_0(X12,k2_xboole_0(X12,X12))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f5740,f282])).
% 28.92/4.03  fof(f5740,plain,(
% 28.92/4.03    ( ! [X12] : (k4_xboole_0(k5_xboole_0(X12,k5_xboole_0(X12,X12)),k3_xboole_0(X12,X12)) = k4_xboole_0(X12,k2_xboole_0(X12,k2_xboole_0(X12,X12)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f5739,f1118])).
% 28.92/4.03  fof(f5739,plain,(
% 28.92/4.03    ( ! [X12] : (k4_xboole_0(k5_xboole_0(X12,k5_xboole_0(X12,X12)),k3_xboole_0(X12,X12)) = k4_xboole_0(X12,k2_xboole_0(X12,k2_xboole_0(X12,k4_xboole_0(X12,X12))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f5732,f4799])).
% 28.92/4.03  fof(f4799,plain,(
% 28.92/4.03    ( ! [X66,X67,X65] : (k4_xboole_0(k5_xboole_0(X66,X65),k2_xboole_0(X67,k4_xboole_0(X66,X65))) = k4_xboole_0(X65,k2_xboole_0(X66,k2_xboole_0(X67,k4_xboole_0(X66,X65))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f4704,f20])).
% 28.92/4.03  fof(f4704,plain,(
% 28.92/4.03    ( ! [X66,X67,X65] : (k4_xboole_0(k4_xboole_0(X65,X66),k2_xboole_0(X67,k4_xboole_0(X66,X65))) = k4_xboole_0(k5_xboole_0(X66,X65),k2_xboole_0(X67,k4_xboole_0(X66,X65)))) )),
% 28.92/4.03    inference(superposition,[],[f559,f34])).
% 28.92/4.03  fof(f559,plain,(
% 28.92/4.03    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X2,X0),k2_xboole_0(X1,X0))) )),
% 28.92/4.03    inference(superposition,[],[f68,f14])).
% 28.92/4.03  fof(f5732,plain,(
% 28.92/4.03    ( ! [X12] : (k4_xboole_0(k5_xboole_0(X12,k5_xboole_0(X12,X12)),k3_xboole_0(X12,X12)) = k4_xboole_0(k5_xboole_0(X12,X12),k2_xboole_0(X12,k4_xboole_0(X12,X12)))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f3739,f5731])).
% 28.92/4.03  fof(f5731,plain,(
% 28.92/4.03    ( ! [X4,X5] : (k2_xboole_0(X5,k3_xboole_0(X4,X5)) = k2_xboole_0(X5,k4_xboole_0(X5,X4))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f5425,f5637])).
% 28.92/4.03  fof(f5637,plain,(
% 28.92/4.03    ( ! [X15,X16] : (k2_xboole_0(X15,k4_xboole_0(X15,X16)) = k2_xboole_0(X15,k4_xboole_0(X16,k2_xboole_0(X15,X16)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f5382,f5482])).
% 28.92/4.03  fof(f5382,plain,(
% 28.92/4.03    ( ! [X15,X16] : (k2_xboole_0(X15,k4_xboole_0(X15,X16)) = k2_xboole_0(X15,k4_xboole_0(k3_xboole_0(X15,X16),X16))) )),
% 28.92/4.03    inference(superposition,[],[f66,f353])).
% 28.92/4.03  fof(f5425,plain,(
% 28.92/4.03    ( ! [X4,X5] : (k2_xboole_0(X5,k3_xboole_0(X4,X5)) = k2_xboole_0(X5,k4_xboole_0(X4,k2_xboole_0(X5,X4)))) )),
% 28.92/4.03    inference(superposition,[],[f15,f353])).
% 28.92/4.03  fof(f3739,plain,(
% 28.92/4.03    ( ! [X12] : (k4_xboole_0(k5_xboole_0(X12,X12),k2_xboole_0(X12,k3_xboole_0(X12,X12))) = k4_xboole_0(k5_xboole_0(X12,k5_xboole_0(X12,X12)),k3_xboole_0(X12,X12))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f3704,f19])).
% 28.92/4.03  fof(f3704,plain,(
% 28.92/4.03    ( ! [X12] : (k4_xboole_0(k5_xboole_0(k5_xboole_0(X12,X12),X12),k3_xboole_0(X12,X12)) = k4_xboole_0(k5_xboole_0(X12,X12),k2_xboole_0(X12,k3_xboole_0(X12,X12)))) )),
% 28.92/4.03    inference(superposition,[],[f41,f3059])).
% 28.92/4.03  fof(f5922,plain,(
% 28.92/4.03    ( ! [X16] : (k4_xboole_0(k3_xboole_0(k5_xboole_0(X16,X16),k5_xboole_0(X16,X16)),X16) = k4_xboole_0(k5_xboole_0(X16,k5_xboole_0(X16,X16)),k3_xboole_0(X16,X16))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f5821,f19])).
% 28.92/4.03  fof(f5821,plain,(
% 28.92/4.03    ( ! [X16] : (k4_xboole_0(k3_xboole_0(k5_xboole_0(X16,X16),k5_xboole_0(X16,X16)),X16) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X16,X16),X16),k3_xboole_0(X16,X16))) )),
% 28.92/4.03    inference(superposition,[],[f5563,f3059])).
% 28.92/4.03  fof(f7422,plain,(
% 28.92/4.03    ( ! [X16] : (k5_xboole_0(k5_xboole_0(X16,X16),X16) = k2_xboole_0(k3_xboole_0(X16,X16),k4_xboole_0(k3_xboole_0(k5_xboole_0(X16,X16),k5_xboole_0(X16,X16)),X16))) )),
% 28.92/4.03    inference(superposition,[],[f5579,f3059])).
% 28.92/4.03  fof(f991,plain,(
% 28.92/4.03    ( ! [X17,X18] : (k5_xboole_0(X18,k2_xboole_0(X17,X18)) = k5_xboole_0(k4_xboole_0(X18,X17),k5_xboole_0(X18,X17))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f990,f688])).
% 28.92/4.03  fof(f688,plain,(
% 28.92/4.03    ( ! [X15,X16] : (k2_xboole_0(k4_xboole_0(X16,k2_xboole_0(X15,k5_xboole_0(X16,X15))),k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(X16,X15)))) = k5_xboole_0(X16,k2_xboole_0(X15,X16))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f687,f137])).
% 28.92/4.03  fof(f687,plain,(
% 28.92/4.03    ( ! [X15,X16] : (k2_xboole_0(k4_xboole_0(X16,k2_xboole_0(X15,k5_xboole_0(X16,X15))),k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(X16,X15)))) = k5_xboole_0(X16,k5_xboole_0(X15,k4_xboole_0(X16,X15)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f686,f19])).
% 28.92/4.03  fof(f686,plain,(
% 28.92/4.03    ( ! [X15,X16] : (k2_xboole_0(k4_xboole_0(X16,k2_xboole_0(X15,k5_xboole_0(X16,X15))),k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(X16,X15)))) = k5_xboole_0(k5_xboole_0(X16,X15),k4_xboole_0(X16,X15))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f685,f121])).
% 28.92/4.03  fof(f685,plain,(
% 28.92/4.03    ( ! [X15,X16] : (k5_xboole_0(k4_xboole_0(X16,X15),k5_xboole_0(X16,X15)) = k2_xboole_0(k4_xboole_0(X16,k2_xboole_0(X15,k5_xboole_0(X16,X15))),k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(X16,X15))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f684,f20])).
% 28.92/4.03  fof(f684,plain,(
% 28.92/4.03    ( ! [X15,X16] : (k5_xboole_0(k4_xboole_0(X16,X15),k5_xboole_0(X16,X15)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X16,X15),k5_xboole_0(X16,X15)),k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(X16,X15))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f639,f20])).
% 28.92/4.03  fof(f639,plain,(
% 28.92/4.03    ( ! [X15,X16] : (k5_xboole_0(k4_xboole_0(X16,X15),k5_xboole_0(X16,X15)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X16,X15),k5_xboole_0(X16,X15)),k4_xboole_0(k4_xboole_0(X15,X16),k4_xboole_0(X16,X15)))) )),
% 28.92/4.03    inference(superposition,[],[f32,f34])).
% 28.92/4.03  fof(f990,plain,(
% 28.92/4.03    ( ! [X17,X18] : (k5_xboole_0(k4_xboole_0(X18,X17),k5_xboole_0(X18,X17)) = k2_xboole_0(k4_xboole_0(X18,k2_xboole_0(X17,k5_xboole_0(X18,X17))),k4_xboole_0(X17,k2_xboole_0(X18,k4_xboole_0(X18,X17))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f989,f86])).
% 28.92/4.03  fof(f989,plain,(
% 28.92/4.03    ( ! [X17,X18] : (k5_xboole_0(k4_xboole_0(X18,X17),k2_xboole_0(k5_xboole_0(X17,X18),k4_xboole_0(X18,X17))) = k2_xboole_0(k4_xboole_0(X18,k2_xboole_0(X17,k2_xboole_0(k5_xboole_0(X17,X18),k4_xboole_0(X18,X17)))),k4_xboole_0(X17,k2_xboole_0(X18,k4_xboole_0(X18,X17))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f931,f20])).
% 28.92/4.03  fof(f931,plain,(
% 28.92/4.03    ( ! [X17,X18] : (k5_xboole_0(k4_xboole_0(X18,X17),k2_xboole_0(k5_xboole_0(X17,X18),k4_xboole_0(X18,X17))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X18,X17),k2_xboole_0(k5_xboole_0(X17,X18),k4_xboole_0(X18,X17))),k4_xboole_0(X17,k2_xboole_0(X18,k4_xboole_0(X18,X17))))) )),
% 28.92/4.03    inference(superposition,[],[f32,f41])).
% 28.92/4.03  fof(f307,plain,(
% 28.92/4.03    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f306,f211])).
% 28.92/4.03  fof(f306,plain,(
% 28.92/4.03    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f305,f15])).
% 28.92/4.03  fof(f305,plain,(
% 28.92/4.03    ( ! [X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f289,f193])).
% 28.92/4.03  fof(f289,plain,(
% 28.92/4.03    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X1),X1)) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 28.92/4.03    inference(superposition,[],[f29,f16])).
% 28.92/4.03  fof(f29,plain,(
% 28.92/4.03    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f28,f14])).
% 28.92/4.03  fof(f28,plain,(
% 28.92/4.03    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 28.92/4.03    inference(superposition,[],[f15,f17])).
% 28.92/4.03  fof(f1068,plain,(
% 28.92/4.03    ( ! [X6,X8,X7,X9] : (k4_xboole_0(X9,k2_xboole_0(X6,k2_xboole_0(X7,X8))) = k4_xboole_0(X9,k2_xboole_0(X8,k2_xboole_0(X6,X7)))) )),
% 28.92/4.03    inference(superposition,[],[f71,f14])).
% 28.92/4.03  fof(f31103,plain,(
% 28.92/4.03    ( ! [X30,X31] : (k5_xboole_0(k4_xboole_0(X30,X31),k2_xboole_0(X30,k5_xboole_0(X31,X31))) = k2_xboole_0(k4_xboole_0(X30,k2_xboole_0(X31,k2_xboole_0(X30,k5_xboole_0(X31,X31)))),k3_xboole_0(X30,X31))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f31102,f20])).
% 28.92/4.03  fof(f31102,plain,(
% 28.92/4.03    ( ! [X30,X31] : (k5_xboole_0(k4_xboole_0(X30,X31),k2_xboole_0(X30,k5_xboole_0(X31,X31))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X30,X31),k2_xboole_0(X30,k5_xboole_0(X31,X31))),k3_xboole_0(X30,X31))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f30877,f17])).
% 28.92/4.03  fof(f30877,plain,(
% 28.92/4.03    ( ! [X30,X31] : (k5_xboole_0(k4_xboole_0(X30,X31),k2_xboole_0(X30,k5_xboole_0(X31,X31))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X30,X31),k2_xboole_0(X30,k5_xboole_0(X31,X31))),k4_xboole_0(X30,k4_xboole_0(X30,X31)))) )),
% 28.92/4.03    inference(superposition,[],[f32,f13571])).
% 28.92/4.03  fof(f13571,plain,(
% 28.92/4.03    ( ! [X35,X36] : (k2_xboole_0(X35,k4_xboole_0(X35,X36)) = k2_xboole_0(X35,k5_xboole_0(X36,X36))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f13570,f100])).
% 28.92/4.03  fof(f13570,plain,(
% 28.92/4.03    ( ! [X35,X36] : (k2_xboole_0(X35,k5_xboole_0(X36,X36)) = k2_xboole_0(X35,k4_xboole_0(X35,k2_xboole_0(X36,X36)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f13569,f20])).
% 28.92/4.03  fof(f13569,plain,(
% 28.92/4.03    ( ! [X35,X36] : (k2_xboole_0(X35,k4_xboole_0(k4_xboole_0(X35,X36),X36)) = k2_xboole_0(X35,k5_xboole_0(X36,X36))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f13568,f12336])).
% 28.92/4.03  fof(f12336,plain,(
% 28.92/4.03    ( ! [X21,X20] : (k2_xboole_0(X21,k5_xboole_0(X20,X20)) = k2_xboole_0(X21,k4_xboole_0(X20,X20))) )),
% 28.92/4.03    inference(superposition,[],[f9458,f34])).
% 28.92/4.03  fof(f9458,plain,(
% 28.92/4.03    ( ! [X35,X34] : (k2_xboole_0(X35,X34) = k2_xboole_0(X35,k2_xboole_0(X34,X34))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f9363,f25])).
% 28.92/4.03  fof(f9363,plain,(
% 28.92/4.03    ( ! [X35,X34] : (k2_xboole_0(X35,k2_xboole_0(X34,X34)) = k2_xboole_0(X35,k2_xboole_0(X34,X35))) )),
% 28.92/4.03    inference(superposition,[],[f25,f7758])).
% 28.92/4.03  fof(f13568,plain,(
% 28.92/4.03    ( ! [X35,X36] : (k2_xboole_0(X35,k4_xboole_0(k4_xboole_0(X35,X36),X36)) = k2_xboole_0(X35,k4_xboole_0(X36,X36))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f13474,f4001])).
% 28.92/4.03  fof(f4001,plain,(
% 28.92/4.03    ( ! [X14,X12,X13] : (k2_xboole_0(X13,k4_xboole_0(k2_xboole_0(X12,X13),X14)) = k2_xboole_0(X13,k4_xboole_0(X12,X14))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f3945,f419])).
% 28.92/4.03  fof(f3945,plain,(
% 28.92/4.03    ( ! [X14,X12,X13] : (k2_xboole_0(X13,k4_xboole_0(X12,k2_xboole_0(X13,X14))) = k2_xboole_0(X13,k4_xboole_0(k2_xboole_0(X12,X13),X14))) )),
% 28.92/4.03    inference(superposition,[],[f419,f68])).
% 28.92/4.03  fof(f13474,plain,(
% 28.92/4.03    ( ! [X35,X36] : (k2_xboole_0(X35,k4_xboole_0(k4_xboole_0(X35,X36),X36)) = k2_xboole_0(X35,k4_xboole_0(k2_xboole_0(X36,X35),X36))) )),
% 28.92/4.03    inference(superposition,[],[f463,f82])).
% 28.92/4.03  fof(f463,plain,(
% 28.92/4.03    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f429,f66])).
% 28.92/4.03  fof(f429,plain,(
% 28.92/4.03    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 28.92/4.03    inference(superposition,[],[f66,f16])).
% 28.92/4.03  fof(f30935,plain,(
% 28.92/4.03    ( ! [X187,X186] : (k3_xboole_0(X186,k4_xboole_0(X186,X187)) = k4_xboole_0(X186,k5_xboole_0(k4_xboole_0(X186,X187),k2_xboole_0(X186,k5_xboole_0(X187,X187))))) )),
% 28.92/4.03    inference(superposition,[],[f5513,f13571])).
% 28.92/4.03  fof(f5513,plain,(
% 28.92/4.03    ( ! [X41,X40] : (k3_xboole_0(X41,X40) = k4_xboole_0(X41,k5_xboole_0(X40,k2_xboole_0(X41,X40)))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f3548,f5493])).
% 28.92/4.03  fof(f5493,plain,(
% 28.92/4.03    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X5,k2_xboole_0(X4,X5)))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f4407,f5482])).
% 28.92/4.03  fof(f4407,plain,(
% 28.92/4.03    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(k3_xboole_0(X4,X5),X5))) )),
% 28.92/4.03    inference(superposition,[],[f97,f4152])).
% 28.92/4.03  fof(f4152,plain,(
% 28.92/4.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X1)) )),
% 28.92/4.03    inference(superposition,[],[f507,f97])).
% 28.92/4.03  fof(f507,plain,(
% 28.92/4.03    ( ! [X10,X11,X9] : (k4_xboole_0(k3_xboole_0(X9,X11),k4_xboole_0(X9,X10)) = k3_xboole_0(k3_xboole_0(X9,X10),X11)) )),
% 28.92/4.03    inference(superposition,[],[f443,f17])).
% 28.92/4.03  fof(f3548,plain,(
% 28.92/4.03    ( ! [X41,X40] : (k4_xboole_0(k3_xboole_0(X41,X40),k4_xboole_0(X40,k2_xboole_0(X41,X40))) = k4_xboole_0(X41,k5_xboole_0(X40,k2_xboole_0(X41,X40)))) )),
% 28.92/4.03    inference(superposition,[],[f355,f32])).
% 28.92/4.03  fof(f1273,plain,(
% 28.92/4.03    ( ! [X0,X1] : (k4_xboole_0(k3_xboole_0(X0,k2_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 28.92/4.03    inference(superposition,[],[f60,f134])).
% 28.92/4.03  fof(f32477,plain,(
% 28.92/4.03    ( ! [X78,X77] : (k4_xboole_0(k2_xboole_0(X77,k4_xboole_0(X77,X78)),k3_xboole_0(X77,X78)) = k4_xboole_0(k3_xboole_0(X77,k2_xboole_0(X78,X77)),k3_xboole_0(X77,X78))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f32476,f25429])).
% 28.92/4.03  fof(f25429,plain,(
% 28.92/4.03    ( ! [X70,X69] : (k3_xboole_0(X69,k2_xboole_0(X70,X69)) = k3_xboole_0(k2_xboole_0(X69,k4_xboole_0(X69,X70)),k2_xboole_0(X69,k4_xboole_0(X69,X70)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f25428,f17])).
% 28.92/4.03  fof(f25428,plain,(
% 28.92/4.03    ( ! [X70,X69] : (k3_xboole_0(k2_xboole_0(X69,k4_xboole_0(X69,X70)),k2_xboole_0(X69,k4_xboole_0(X69,X70))) = k4_xboole_0(X69,k4_xboole_0(X69,k2_xboole_0(X70,X69)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f25396,f182])).
% 28.92/4.03  fof(f182,plain,(
% 28.92/4.03    ( ! [X10,X8,X9] : (k4_xboole_0(X10,k4_xboole_0(X8,k2_xboole_0(X9,X10))) = k4_xboole_0(k2_xboole_0(X10,k4_xboole_0(X8,X9)),k4_xboole_0(X8,k2_xboole_0(X9,X10)))) )),
% 28.92/4.03    inference(superposition,[],[f23,f20])).
% 28.92/4.03  fof(f25396,plain,(
% 28.92/4.03    ( ! [X70,X69] : (k3_xboole_0(k2_xboole_0(X69,k4_xboole_0(X69,X70)),k2_xboole_0(X69,k4_xboole_0(X69,X70))) = k4_xboole_0(k2_xboole_0(X69,k4_xboole_0(X69,X70)),k4_xboole_0(X69,k2_xboole_0(X70,X69)))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f11862,f25363])).
% 28.92/4.03  fof(f25363,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k4_xboole_0(X6,k2_xboole_0(X7,X6)) = k4_xboole_0(k3_xboole_0(X6,X7),X6)) )),
% 28.92/4.03    inference(backward_demodulation,[],[f383,f25362])).
% 28.92/4.03  fof(f25362,plain,(
% 28.92/4.03    ( ! [X30,X31] : (k4_xboole_0(k3_xboole_0(X30,X31),k3_xboole_0(X30,X31)) = k4_xboole_0(X30,k2_xboole_0(X31,X30))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f25361,f17471])).
% 28.92/4.03  fof(f17471,plain,(
% 28.92/4.03    ( ! [X15,X16] : (k4_xboole_0(X15,k2_xboole_0(X16,X15)) = k4_xboole_0(k4_xboole_0(X15,X16),k2_xboole_0(X15,k4_xboole_0(X15,X16)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f17470,f5927])).
% 28.92/4.03  fof(f5927,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k4_xboole_0(X6,k2_xboole_0(X7,X6)) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X6,X7)),k3_xboole_0(X6,X7))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f3134,f5925])).
% 28.92/4.03  fof(f5925,plain,(
% 28.92/4.03    ( ! [X19,X20] : (k4_xboole_0(X20,k2_xboole_0(X19,X20)) = k4_xboole_0(k3_xboole_0(X20,X20),k2_xboole_0(X19,X20))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f5823,f734])).
% 28.92/4.03  fof(f734,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k4_xboole_0(X6,k2_xboole_0(X7,X6)) = k4_xboole_0(k5_xboole_0(X6,k2_xboole_0(X7,X6)),k4_xboole_0(X7,X6))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f733,f25])).
% 28.92/4.03  fof(f733,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k4_xboole_0(k5_xboole_0(X6,k2_xboole_0(X7,X6)),k4_xboole_0(X7,X6)) = k4_xboole_0(X6,k2_xboole_0(X7,k2_xboole_0(X6,X7)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f732,f15])).
% 28.92/4.03  fof(f732,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k4_xboole_0(k5_xboole_0(X6,k2_xboole_0(X7,X6)),k4_xboole_0(X7,X6)) = k4_xboole_0(X6,k2_xboole_0(X7,k2_xboole_0(X6,k4_xboole_0(X7,X6))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f731,f71])).
% 28.92/4.03  fof(f731,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k4_xboole_0(k5_xboole_0(X6,k2_xboole_0(X7,X6)),k4_xboole_0(X7,X6)) = k4_xboole_0(X6,k2_xboole_0(k2_xboole_0(X7,X6),k4_xboole_0(X7,X6)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f663,f20])).
% 28.92/4.03  fof(f663,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X6,k2_xboole_0(X7,X6)),k4_xboole_0(X7,X6)) = k4_xboole_0(k5_xboole_0(X6,k2_xboole_0(X7,X6)),k4_xboole_0(X7,X6))) )),
% 28.92/4.03    inference(superposition,[],[f16,f32])).
% 28.92/4.03  fof(f5823,plain,(
% 28.92/4.03    ( ! [X19,X20] : (k4_xboole_0(k3_xboole_0(X20,X20),k2_xboole_0(X19,X20)) = k4_xboole_0(k5_xboole_0(X20,k2_xboole_0(X19,X20)),k4_xboole_0(X19,X20))) )),
% 28.92/4.03    inference(superposition,[],[f5563,f16])).
% 28.92/4.03  fof(f3134,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X6,X7)),k3_xboole_0(X6,X7)) = k4_xboole_0(k3_xboole_0(X6,X6),k2_xboole_0(X7,X6))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f863,f3132])).
% 28.92/4.03  fof(f3132,plain,(
% 28.92/4.03    ( ! [X35,X36] : (k4_xboole_0(X35,k2_xboole_0(X36,k2_xboole_0(X35,k3_xboole_0(X35,X36)))) = k4_xboole_0(k3_xboole_0(X35,X35),k2_xboole_0(X36,X35))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f3131,f20])).
% 28.92/4.03  fof(f3131,plain,(
% 28.92/4.03    ( ! [X35,X36] : (k4_xboole_0(X35,k2_xboole_0(X36,k2_xboole_0(X35,k3_xboole_0(X35,X36)))) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X35,X35),X36),X35)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f3130,f443])).
% 28.92/4.03  fof(f3130,plain,(
% 28.92/4.03    ( ! [X35,X36] : (k4_xboole_0(X35,k2_xboole_0(X36,k2_xboole_0(X35,k3_xboole_0(X35,X36)))) = k4_xboole_0(k3_xboole_0(k4_xboole_0(X35,X36),X35),X35)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f3129,f353])).
% 28.92/4.03  fof(f3129,plain,(
% 28.92/4.03    ( ! [X35,X36] : (k4_xboole_0(X35,k2_xboole_0(X36,k2_xboole_0(X35,k3_xboole_0(X35,X36)))) = k4_xboole_0(k4_xboole_0(X35,X36),k2_xboole_0(X35,k4_xboole_0(X35,X36)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f3128,f416])).
% 28.92/4.03  fof(f416,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k2_xboole_0(X6,k4_xboole_0(X6,X7)) = k5_xboole_0(k4_xboole_0(X6,X7),k3_xboole_0(X6,X7))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f404,f14])).
% 28.92/4.03  fof(f404,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X6,X7),X6) = k5_xboole_0(k4_xboole_0(X6,X7),k3_xboole_0(X6,X7))) )),
% 28.92/4.03    inference(superposition,[],[f137,f17])).
% 28.92/4.03  fof(f3128,plain,(
% 28.92/4.03    ( ! [X35,X36] : (k4_xboole_0(X35,k2_xboole_0(X36,k2_xboole_0(X35,k3_xboole_0(X35,X36)))) = k4_xboole_0(k4_xboole_0(X35,X36),k5_xboole_0(k4_xboole_0(X35,X36),k3_xboole_0(X35,X36)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f3127,f121])).
% 28.92/4.03  fof(f3127,plain,(
% 28.92/4.03    ( ! [X35,X36] : (k4_xboole_0(k4_xboole_0(X35,X36),k5_xboole_0(k3_xboole_0(X35,X36),k4_xboole_0(X35,X36))) = k4_xboole_0(X35,k2_xboole_0(X36,k2_xboole_0(X35,k3_xboole_0(X35,X36))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f3126,f1108])).
% 28.92/4.03  fof(f1108,plain,(
% 28.92/4.03    ( ! [X10,X8,X11,X9] : (k4_xboole_0(X10,k2_xboole_0(X8,k2_xboole_0(k4_xboole_0(X9,X8),X11))) = k4_xboole_0(X10,k2_xboole_0(X8,k2_xboole_0(X9,X11)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f1053,f71])).
% 28.92/4.03  fof(f1053,plain,(
% 28.92/4.03    ( ! [X10,X8,X11,X9] : (k4_xboole_0(X10,k2_xboole_0(X8,k2_xboole_0(k4_xboole_0(X9,X8),X11))) = k4_xboole_0(X10,k2_xboole_0(k2_xboole_0(X8,X9),X11))) )),
% 28.92/4.03    inference(superposition,[],[f71,f15])).
% 28.92/4.03  fof(f3126,plain,(
% 28.92/4.03    ( ! [X35,X36] : (k4_xboole_0(k4_xboole_0(X35,X36),k5_xboole_0(k3_xboole_0(X35,X36),k4_xboole_0(X35,X36))) = k4_xboole_0(X35,k2_xboole_0(X36,k2_xboole_0(k4_xboole_0(X35,X36),k3_xboole_0(X35,X36))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f3125,f20])).
% 28.92/4.03  fof(f3125,plain,(
% 28.92/4.03    ( ! [X35,X36] : (k4_xboole_0(k4_xboole_0(X35,X36),k5_xboole_0(k3_xboole_0(X35,X36),k4_xboole_0(X35,X36))) = k4_xboole_0(k4_xboole_0(X35,X36),k2_xboole_0(k4_xboole_0(X35,X36),k3_xboole_0(X35,X36)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f3124,f1479])).
% 28.92/4.03  fof(f3124,plain,(
% 28.92/4.03    ( ! [X35,X36] : (k4_xboole_0(k4_xboole_0(X35,X36),k5_xboole_0(k3_xboole_0(X35,X36),k4_xboole_0(X35,X36))) = k4_xboole_0(k4_xboole_0(X35,X36),k2_xboole_0(k3_xboole_0(X35,X36),k4_xboole_0(X35,X36)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f3057,f353])).
% 28.92/4.03  fof(f3057,plain,(
% 28.92/4.03    ( ! [X35,X36] : (k4_xboole_0(k4_xboole_0(X35,X36),k5_xboole_0(k3_xboole_0(X35,X36),k4_xboole_0(X35,X36))) = k4_xboole_0(k3_xboole_0(k4_xboole_0(X35,X36),k3_xboole_0(X35,X36)),k3_xboole_0(X35,X36))) )),
% 28.92/4.03    inference(superposition,[],[f351,f97])).
% 28.92/4.03  fof(f863,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X6,X7)),k3_xboole_0(X6,X7)) = k4_xboole_0(X6,k2_xboole_0(X7,k2_xboole_0(X6,k3_xboole_0(X6,X7))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f862,f71])).
% 28.92/4.03  fof(f862,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X6,X7)),k3_xboole_0(X6,X7)) = k4_xboole_0(X6,k2_xboole_0(k2_xboole_0(X7,X6),k3_xboole_0(X6,X7)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f788,f20])).
% 28.92/4.03  fof(f788,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X6,k2_xboole_0(X7,X6)),k3_xboole_0(X6,X7)) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X6,X7)),k3_xboole_0(X6,X7))) )),
% 28.92/4.03    inference(superposition,[],[f21,f39])).
% 28.92/4.03  fof(f17470,plain,(
% 28.92/4.03    ( ! [X15,X16] : (k4_xboole_0(k4_xboole_0(X15,X16),k2_xboole_0(X15,k4_xboole_0(X15,X16))) = k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X15,X16)),k3_xboole_0(X15,X16))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f17153,f5552])).
% 28.92/4.03  fof(f5552,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k5_xboole_0(k4_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))) = k5_xboole_0(X21,k4_xboole_0(X21,X22))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f5491,f5550])).
% 28.92/4.03  fof(f5550,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k5_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X3,k2_xboole_0(X2,X3)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f5376,f5482])).
% 28.92/4.03  fof(f5376,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k5_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X2,X3),X3))) )),
% 28.92/4.03    inference(superposition,[],[f39,f353])).
% 28.92/4.03  fof(f5491,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k5_xboole_0(k4_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))) = k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X22,k2_xboole_0(X21,X22)))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f2755,f5482])).
% 28.92/4.03  fof(f2755,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(k3_xboole_0(X21,X22),X22)) = k5_xboole_0(k4_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f2754,f29])).
% 28.92/4.03  fof(f2754,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(k3_xboole_0(X21,X22),X22)) = k5_xboole_0(k4_xboole_0(X21,X22),k2_xboole_0(k4_xboole_0(X21,X22),k3_xboole_0(X21,X22)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f2753,f14])).
% 28.92/4.03  fof(f2753,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k5_xboole_0(k4_xboole_0(X21,X22),k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,X22))) = k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(k3_xboole_0(X21,X22),X22))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f2752,f355])).
% 28.92/4.03  fof(f2752,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k5_xboole_0(k4_xboole_0(X21,X22),k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,X22))) = k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,k2_xboole_0(X22,k4_xboole_0(X21,X22))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f2751,f20])).
% 28.92/4.03  fof(f2751,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k5_xboole_0(k4_xboole_0(X21,X22),k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,X22))) = k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(k4_xboole_0(X21,X22),k4_xboole_0(X21,X22)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f2750,f227])).
% 28.92/4.03  fof(f227,plain,(
% 28.92/4.03    ( ! [X10,X8,X9] : (k2_xboole_0(X10,k4_xboole_0(X8,X9)) = k2_xboole_0(k4_xboole_0(X8,k2_xboole_0(X9,X10)),X10)) )),
% 28.92/4.03    inference(superposition,[],[f211,f20])).
% 28.92/4.03  fof(f2750,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k5_xboole_0(k4_xboole_0(X21,X22),k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,X22))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X21,X22),k2_xboole_0(k4_xboole_0(X21,X22),k3_xboole_0(X21,X22))),k3_xboole_0(X21,X22))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f2697,f1479])).
% 28.92/4.03  fof(f2697,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k5_xboole_0(k4_xboole_0(X21,X22),k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,X22))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X21,X22),k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,X22))),k3_xboole_0(X21,X22))) )),
% 28.92/4.03    inference(superposition,[],[f32,f97])).
% 28.92/4.03  fof(f17153,plain,(
% 28.92/4.03    ( ! [X15,X16] : (k4_xboole_0(k4_xboole_0(X15,X16),k2_xboole_0(X15,k4_xboole_0(X15,X16))) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X15,X16),k2_xboole_0(X15,k4_xboole_0(X15,X16))),k3_xboole_0(X15,X16))) )),
% 28.92/4.03    inference(superposition,[],[f734,f17])).
% 28.92/4.03  fof(f25361,plain,(
% 28.92/4.03    ( ! [X30,X31] : (k4_xboole_0(k3_xboole_0(X30,X31),k3_xboole_0(X30,X31)) = k4_xboole_0(k4_xboole_0(X30,X31),k2_xboole_0(X30,k4_xboole_0(X30,X31)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f25360,f29])).
% 28.92/4.03  fof(f25360,plain,(
% 28.92/4.03    ( ! [X30,X31] : (k4_xboole_0(k3_xboole_0(X30,X31),k3_xboole_0(X30,X31)) = k4_xboole_0(k4_xboole_0(X30,X31),k2_xboole_0(k4_xboole_0(X30,X31),k3_xboole_0(X30,X31)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f25111,f14])).
% 28.92/4.03  fof(f25111,plain,(
% 28.92/4.03    ( ! [X30,X31] : (k4_xboole_0(k3_xboole_0(X30,X31),k3_xboole_0(X30,X31)) = k4_xboole_0(k4_xboole_0(X30,X31),k2_xboole_0(k3_xboole_0(X30,X31),k4_xboole_0(X30,X31)))) )),
% 28.92/4.03    inference(superposition,[],[f4741,f385])).
% 28.92/4.03  fof(f385,plain,(
% 28.92/4.03    ( ! [X19,X17,X18] : (k4_xboole_0(k3_xboole_0(X17,X18),k2_xboole_0(X19,k4_xboole_0(X17,X18))) = k4_xboole_0(k3_xboole_0(X17,X18),X19)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f358,f60])).
% 28.92/4.03  fof(f358,plain,(
% 28.92/4.03    ( ! [X19,X17,X18] : (k4_xboole_0(k3_xboole_0(X17,X18),k2_xboole_0(X19,k4_xboole_0(X17,X18))) = k4_xboole_0(X17,k2_xboole_0(k4_xboole_0(X17,X18),X19))) )),
% 28.92/4.03    inference(superposition,[],[f60,f25])).
% 28.92/4.03  fof(f4741,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(X3,k2_xboole_0(X2,X3))) )),
% 28.92/4.03    inference(superposition,[],[f559,f69])).
% 28.92/4.03  fof(f383,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k4_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X7)) = k4_xboole_0(k3_xboole_0(X6,X7),X6)) )),
% 28.92/4.03    inference(backward_demodulation,[],[f354,f355])).
% 28.92/4.03  fof(f354,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k4_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X7)) = k4_xboole_0(X6,k2_xboole_0(X6,k4_xboole_0(X6,X7)))) )),
% 28.92/4.03    inference(superposition,[],[f60,f29])).
% 28.92/4.03  fof(f11862,plain,(
% 28.92/4.03    ( ! [X70,X69] : (k3_xboole_0(k2_xboole_0(X69,k4_xboole_0(X69,X70)),k2_xboole_0(X69,k4_xboole_0(X69,X70))) = k4_xboole_0(k2_xboole_0(X69,k4_xboole_0(X69,X70)),k4_xboole_0(k3_xboole_0(X69,X70),X69))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f11721,f385])).
% 28.92/4.03  fof(f11721,plain,(
% 28.92/4.03    ( ! [X70,X69] : (k4_xboole_0(k2_xboole_0(X69,k4_xboole_0(X69,X70)),k4_xboole_0(k3_xboole_0(X69,X70),k2_xboole_0(X69,k4_xboole_0(X69,X70)))) = k3_xboole_0(k2_xboole_0(X69,k4_xboole_0(X69,X70)),k2_xboole_0(X69,k4_xboole_0(X69,X70)))) )),
% 28.92/4.03    inference(superposition,[],[f193,f323])).
% 28.92/4.03  fof(f323,plain,(
% 28.92/4.03    ( ! [X10,X11] : (k2_xboole_0(X10,k4_xboole_0(X10,X11)) = k2_xboole_0(k3_xboole_0(X10,X11),k2_xboole_0(X10,k4_xboole_0(X10,X11)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f322,f29])).
% 28.92/4.03  fof(f322,plain,(
% 28.92/4.03    ( ! [X10,X11] : (k2_xboole_0(k4_xboole_0(X10,X11),k3_xboole_0(X10,X11)) = k2_xboole_0(k3_xboole_0(X10,X11),k2_xboole_0(X10,k4_xboole_0(X10,X11)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f301,f14])).
% 28.92/4.03  fof(f301,plain,(
% 28.92/4.03    ( ! [X10,X11] : (k2_xboole_0(k3_xboole_0(X10,X11),k4_xboole_0(X10,X11)) = k2_xboole_0(k3_xboole_0(X10,X11),k2_xboole_0(X10,k4_xboole_0(X10,X11)))) )),
% 28.92/4.03    inference(superposition,[],[f25,f29])).
% 28.92/4.03  fof(f32476,plain,(
% 28.92/4.03    ( ! [X78,X77] : (k4_xboole_0(k2_xboole_0(X77,k4_xboole_0(X77,X78)),k3_xboole_0(X77,X78)) = k4_xboole_0(k3_xboole_0(k2_xboole_0(X77,k4_xboole_0(X77,X78)),k2_xboole_0(X77,k4_xboole_0(X77,X78))),k3_xboole_0(X77,X78))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f32475,f14])).
% 28.92/4.03  fof(f32475,plain,(
% 28.92/4.03    ( ! [X78,X77] : (k4_xboole_0(k3_xboole_0(k2_xboole_0(X77,k4_xboole_0(X77,X78)),k2_xboole_0(X77,k4_xboole_0(X77,X78))),k3_xboole_0(X77,X78)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X77,X78),X77),k3_xboole_0(X77,X78))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f32474,f29014])).
% 28.92/4.03  fof(f29014,plain,(
% 28.92/4.03    ( ! [X10,X8,X9] : (k2_xboole_0(k4_xboole_0(X8,X9),X10) = k2_xboole_0(k2_xboole_0(X10,k4_xboole_0(X8,X9)),k4_xboole_0(k3_xboole_0(X8,X8),X9))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f28776,f1589])).
% 28.92/4.03  fof(f28776,plain,(
% 28.92/4.03    ( ! [X10,X8,X9] : (k2_xboole_0(k4_xboole_0(X8,X9),X10) = k2_xboole_0(k2_xboole_0(X10,k4_xboole_0(X8,X9)),k4_xboole_0(k3_xboole_0(X8,k4_xboole_0(X8,X9)),X9))) )),
% 28.92/4.03    inference(superposition,[],[f8440,f443])).
% 28.92/4.03  fof(f8440,plain,(
% 28.92/4.03    ( ! [X19,X20] : (k2_xboole_0(X19,X20) = k2_xboole_0(k2_xboole_0(X20,X19),k3_xboole_0(X19,X19))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f8439,f25])).
% 28.92/4.03  fof(f8439,plain,(
% 28.92/4.03    ( ! [X19,X20] : (k2_xboole_0(k2_xboole_0(X20,X19),k3_xboole_0(X19,X19)) = k2_xboole_0(X19,k2_xboole_0(X20,X19))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f8438,f14])).
% 28.92/4.03  fof(f8438,plain,(
% 28.92/4.03    ( ! [X19,X20] : (k2_xboole_0(k2_xboole_0(X20,X19),k3_xboole_0(X19,X19)) = k2_xboole_0(k2_xboole_0(X20,X19),X19)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f8313,f15])).
% 28.92/4.03  fof(f8313,plain,(
% 28.92/4.03    ( ! [X19,X20] : (k2_xboole_0(k2_xboole_0(X20,X19),k3_xboole_0(X19,X19)) = k2_xboole_0(k2_xboole_0(X20,X19),k4_xboole_0(X19,k2_xboole_0(X20,X19)))) )),
% 28.92/4.03    inference(superposition,[],[f15,f5925])).
% 28.92/4.03  fof(f32474,plain,(
% 28.92/4.03    ( ! [X78,X77] : (k4_xboole_0(k3_xboole_0(k2_xboole_0(X77,k4_xboole_0(X77,X78)),k2_xboole_0(X77,k4_xboole_0(X77,X78))),k3_xboole_0(X77,X78)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X77,k4_xboole_0(X77,X78)),k4_xboole_0(k3_xboole_0(X77,X77),X78)),k3_xboole_0(X77,X78))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f32269,f6468])).
% 28.92/4.03  fof(f6468,plain,(
% 28.92/4.03    ( ! [X17,X16] : (k3_xboole_0(X16,X17) = k3_xboole_0(k2_xboole_0(X16,k4_xboole_0(X16,X17)),k3_xboole_0(X16,X17))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f5618,f6466])).
% 28.92/4.03  fof(f6466,plain,(
% 28.92/4.03    ( ! [X62,X63] : (k3_xboole_0(X62,X63) = k4_xboole_0(k3_xboole_0(X62,X63),k4_xboole_0(k3_xboole_0(X62,X62),X63))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f6465,f1589])).
% 28.92/4.03  fof(f6465,plain,(
% 28.92/4.03    ( ! [X62,X63] : (k3_xboole_0(X62,X63) = k4_xboole_0(k3_xboole_0(X62,X63),k4_xboole_0(k3_xboole_0(X62,k4_xboole_0(X62,X63)),X63))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f6464,f443])).
% 28.92/4.03  fof(f6464,plain,(
% 28.92/4.03    ( ! [X62,X63] : (k3_xboole_0(X62,X63) = k4_xboole_0(k3_xboole_0(X62,X63),k3_xboole_0(k4_xboole_0(X62,X63),k4_xboole_0(X62,X63)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f6463,f97])).
% 28.92/4.03  fof(f6463,plain,(
% 28.92/4.03    ( ! [X62,X63] : (k4_xboole_0(k3_xboole_0(X62,X63),k3_xboole_0(k4_xboole_0(X62,X63),k4_xboole_0(X62,X63))) = k4_xboole_0(k3_xboole_0(X62,X63),k4_xboole_0(X62,X63))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f6407,f60])).
% 28.92/4.03  fof(f6407,plain,(
% 28.92/4.03    ( ! [X62,X63] : (k4_xboole_0(k3_xboole_0(X62,X63),k3_xboole_0(k4_xboole_0(X62,X63),k4_xboole_0(X62,X63))) = k4_xboole_0(X62,k2_xboole_0(k4_xboole_0(X62,X63),k4_xboole_0(X62,X63)))) )),
% 28.92/4.03    inference(superposition,[],[f60,f6160])).
% 28.92/4.03  fof(f6160,plain,(
% 28.92/4.03    ( ! [X23] : (k2_xboole_0(X23,X23) = k2_xboole_0(X23,k3_xboole_0(X23,X23))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f6101,f109])).
% 28.92/4.03  fof(f6101,plain,(
% 28.92/4.03    ( ! [X23] : (k2_xboole_0(X23,k3_xboole_0(X23,X23)) = k5_xboole_0(k4_xboole_0(X23,X23),X23)) )),
% 28.92/4.03    inference(superposition,[],[f109,f5896])).
% 28.92/4.03  fof(f5618,plain,(
% 28.92/4.03    ( ! [X17,X16] : (k3_xboole_0(k2_xboole_0(X16,k4_xboole_0(X16,X17)),k3_xboole_0(X16,X17)) = k4_xboole_0(k3_xboole_0(X16,X17),k4_xboole_0(k3_xboole_0(X16,X16),X17))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f5511,f5562])).
% 28.92/4.03  fof(f5511,plain,(
% 28.92/4.03    ( ! [X17,X16] : (k3_xboole_0(k2_xboole_0(X16,k4_xboole_0(X16,X17)),k3_xboole_0(X16,X17)) = k4_xboole_0(k3_xboole_0(X16,X17),k4_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X17,X16))))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f324,f5507])).
% 28.92/4.03  fof(f5507,plain,(
% 28.92/4.03    ( ! [X12,X11] : (k4_xboole_0(X11,k2_xboole_0(X12,k3_xboole_0(X11,X12))) = k4_xboole_0(X11,k2_xboole_0(X12,k4_xboole_0(X12,X11)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f5485,f2872])).
% 28.92/4.03  fof(f5485,plain,(
% 28.92/4.03    ( ! [X12,X11] : (k4_xboole_0(X11,k2_xboole_0(X12,k3_xboole_0(X11,X12))) = k4_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X12,k2_xboole_0(X11,X12)))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f459,f5482])).
% 28.92/4.03  fof(f459,plain,(
% 28.92/4.03    ( ! [X12,X11] : (k4_xboole_0(X11,k2_xboole_0(X12,k3_xboole_0(X11,X12))) = k4_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(k3_xboole_0(X11,X12),X12))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f458,f443])).
% 28.92/4.03  fof(f458,plain,(
% 28.92/4.03    ( ! [X12,X11] : (k4_xboole_0(k4_xboole_0(X11,X12),k3_xboole_0(k4_xboole_0(X11,X12),X12)) = k4_xboole_0(X11,k2_xboole_0(X12,k3_xboole_0(X11,X12)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f457,f14])).
% 28.92/4.03  fof(f457,plain,(
% 28.92/4.03    ( ! [X12,X11] : (k4_xboole_0(k4_xboole_0(X11,X12),k3_xboole_0(k4_xboole_0(X11,X12),X12)) = k4_xboole_0(X11,k2_xboole_0(k3_xboole_0(X11,X12),X12))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f456,f20])).
% 28.92/4.03  fof(f456,plain,(
% 28.92/4.03    ( ! [X12,X11] : (k4_xboole_0(k4_xboole_0(X11,X12),k3_xboole_0(k4_xboole_0(X11,X12),X12)) = k4_xboole_0(k4_xboole_0(X11,k3_xboole_0(X11,X12)),X12)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f449,f27])).
% 28.92/4.03  fof(f449,plain,(
% 28.92/4.03    ( ! [X12,X11] : (k4_xboole_0(k4_xboole_0(X11,X12),k3_xboole_0(k4_xboole_0(X11,X12),X12)) = k4_xboole_0(k3_xboole_0(X11,k4_xboole_0(X11,X12)),X12)) )),
% 28.92/4.03    inference(backward_demodulation,[],[f105,f443])).
% 28.92/4.03  fof(f105,plain,(
% 28.92/4.03    ( ! [X12,X11] : (k4_xboole_0(k4_xboole_0(X11,X12),k3_xboole_0(k4_xboole_0(X11,X12),X12)) = k3_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X12))) )),
% 28.92/4.03    inference(superposition,[],[f27,f50])).
% 28.92/4.03  fof(f324,plain,(
% 28.92/4.03    ( ! [X17,X16] : (k3_xboole_0(k2_xboole_0(X16,k4_xboole_0(X16,X17)),k3_xboole_0(X16,X17)) = k4_xboole_0(k3_xboole_0(X16,X17),k4_xboole_0(X16,k2_xboole_0(X17,k3_xboole_0(X16,X17))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f304,f20])).
% 28.92/4.03  fof(f304,plain,(
% 28.92/4.03    ( ! [X17,X16] : (k4_xboole_0(k3_xboole_0(X16,X17),k4_xboole_0(k4_xboole_0(X16,X17),k3_xboole_0(X16,X17))) = k3_xboole_0(k2_xboole_0(X16,k4_xboole_0(X16,X17)),k3_xboole_0(X16,X17))) )),
% 28.92/4.03    inference(superposition,[],[f193,f29])).
% 28.92/4.03  fof(f32269,plain,(
% 28.92/4.03    ( ! [X78,X77] : (k4_xboole_0(k3_xboole_0(k2_xboole_0(X77,k4_xboole_0(X77,X78)),k2_xboole_0(X77,k4_xboole_0(X77,X78))),k3_xboole_0(X77,X78)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X77,k4_xboole_0(X77,X78)),k4_xboole_0(k3_xboole_0(X77,X77),X78)),k3_xboole_0(k2_xboole_0(X77,k4_xboole_0(X77,X78)),k3_xboole_0(X77,X78)))) )),
% 28.92/4.03    inference(superposition,[],[f5619,f5619])).
% 28.92/4.03  fof(f5619,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,k4_xboole_0(X6,X7)),k3_xboole_0(X6,X7)) = k4_xboole_0(k3_xboole_0(X6,X6),X7)) )),
% 28.92/4.03    inference(backward_demodulation,[],[f5512,f5562])).
% 28.92/4.03  fof(f5512,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k4_xboole_0(X6,k2_xboole_0(X7,k4_xboole_0(X7,X6))) = k4_xboole_0(k2_xboole_0(X6,k4_xboole_0(X6,X7)),k3_xboole_0(X6,X7))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f209,f5507])).
% 28.92/4.03  fof(f209,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,k4_xboole_0(X6,X7)),k3_xboole_0(X6,X7)) = k4_xboole_0(X6,k2_xboole_0(X7,k3_xboole_0(X6,X7)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f208,f20])).
% 28.92/4.03  fof(f208,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),k3_xboole_0(X6,X7)) = k4_xboole_0(k2_xboole_0(X6,k4_xboole_0(X6,X7)),k3_xboole_0(X6,X7))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f181,f14])).
% 28.92/4.03  fof(f181,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),k3_xboole_0(X6,X7)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X6,X7),X6),k3_xboole_0(X6,X7))) )),
% 28.92/4.03    inference(superposition,[],[f23,f17])).
% 28.92/4.03  fof(f16915,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k4_xboole_0(X3,k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X2,X2),X3))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f16914,f5482])).
% 28.92/4.03  fof(f16914,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k4_xboole_0(k3_xboole_0(X2,X3),X3) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X2,X2),X3))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f16913,f355])).
% 28.92/4.03  fof(f16913,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X2,X2),X3))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f16912,f20])).
% 28.92/4.03  fof(f16912,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X2,X2),X3))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f16838,f1589])).
% 28.92/4.03  fof(f16838,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X2,k4_xboole_0(X2,X3)),X3))) )),
% 28.92/4.03    inference(superposition,[],[f9022,f443])).
% 28.92/4.03  fof(f9022,plain,(
% 28.92/4.03    ( ! [X2] : (k4_xboole_0(X2,X2) = k4_xboole_0(X2,k3_xboole_0(X2,X2))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f6366,f9014])).
% 28.92/4.03  fof(f9014,plain,(
% 28.92/4.03    ( ! [X12] : (k4_xboole_0(X12,X12) = k4_xboole_0(k2_xboole_0(X12,X12),k3_xboole_0(X12,X12))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f5742,f9007])).
% 28.92/4.03  fof(f9007,plain,(
% 28.92/4.03    ( ! [X2] : (k2_xboole_0(X2,X2) = k5_xboole_0(X2,k5_xboole_0(X2,X2))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f9006,f25])).
% 28.92/4.03  fof(f9006,plain,(
% 28.92/4.03    ( ! [X2] : (k2_xboole_0(X2,k2_xboole_0(X2,X2)) = k5_xboole_0(X2,k5_xboole_0(X2,X2))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f9005,f7772])).
% 28.92/4.03  fof(f9005,plain,(
% 28.92/4.03    ( ! [X2] : (k2_xboole_0(k2_xboole_0(X2,X2),k2_xboole_0(X2,X2)) = k5_xboole_0(X2,k5_xboole_0(X2,X2))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f9004,f7527])).
% 28.92/4.03  fof(f7527,plain,(
% 28.92/4.03    ( ! [X19,X20] : (k5_xboole_0(X19,k2_xboole_0(X20,X20)) = k5_xboole_0(X20,X19)) )),
% 28.92/4.03    inference(backward_demodulation,[],[f274,f7517])).
% 28.92/4.03  fof(f7517,plain,(
% 28.92/4.03    ( ! [X8,X9] : (k5_xboole_0(X9,X8) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X9,X9),X8),k4_xboole_0(X8,X9))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f269,f7516])).
% 28.92/4.03  fof(f269,plain,(
% 28.92/4.03    ( ! [X8,X9] : (k5_xboole_0(k2_xboole_0(X9,X9),X8) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X9,X9),X8),k4_xboole_0(X8,X9))) )),
% 28.92/4.03    inference(superposition,[],[f18,f100])).
% 28.92/4.03  fof(f274,plain,(
% 28.92/4.03    ( ! [X19,X20] : (k5_xboole_0(X19,k2_xboole_0(X20,X20)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X20,X20),X19),k4_xboole_0(X19,X20))) )),
% 28.92/4.03    inference(superposition,[],[f34,f100])).
% 28.92/4.03  fof(f9004,plain,(
% 28.92/4.03    ( ! [X2] : (k2_xboole_0(k2_xboole_0(X2,X2),k2_xboole_0(X2,X2)) = k5_xboole_0(k5_xboole_0(X2,X2),k2_xboole_0(X2,X2))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f9003,f704])).
% 28.92/4.03  fof(f9003,plain,(
% 28.92/4.03    ( ! [X2] : (k2_xboole_0(k2_xboole_0(X2,X2),k2_xboole_0(X2,X2)) = k5_xboole_0(k5_xboole_0(X2,k2_xboole_0(X2,X2)),k2_xboole_0(X2,X2))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f8965,f130])).
% 28.92/4.03  fof(f8965,plain,(
% 28.92/4.03    ( ! [X2] : (k2_xboole_0(k2_xboole_0(X2,X2),k2_xboole_0(X2,X2)) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X2,X2),X2),k2_xboole_0(X2,X2))) )),
% 28.92/4.03    inference(superposition,[],[f7553,f7538])).
% 28.92/4.03  fof(f7538,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k5_xboole_0(X2,k2_xboole_0(X3,X3))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f7519,f86])).
% 28.92/4.03  fof(f7519,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k5_xboole_0(X2,k2_xboole_0(X3,X3)) = k2_xboole_0(k5_xboole_0(X3,X2),k4_xboole_0(X2,X3))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f1681,f7516])).
% 28.92/4.03  fof(f1681,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k5_xboole_0(X2,k2_xboole_0(X3,X3)) = k2_xboole_0(k5_xboole_0(k2_xboole_0(X3,X3),X2),k4_xboole_0(X2,X3))) )),
% 28.92/4.03    inference(superposition,[],[f86,f100])).
% 28.92/4.03  fof(f6366,plain,(
% 28.92/4.03    ( ! [X2] : (k4_xboole_0(X2,k3_xboole_0(X2,X2)) = k4_xboole_0(k2_xboole_0(X2,X2),k3_xboole_0(X2,X2))) )),
% 28.92/4.03    inference(superposition,[],[f16,f6160])).
% 28.92/4.03  fof(f34081,plain,(
% 28.92/4.03    ( ! [X74,X73] : (k4_xboole_0(X73,k2_xboole_0(X74,k3_xboole_0(X73,X73))) = k4_xboole_0(k4_xboole_0(X74,X73),k4_xboole_0(X74,k3_xboole_0(X74,X73)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f34080,f32484])).
% 28.92/4.03  fof(f32484,plain,(
% 28.92/4.03    ( ! [X39,X40] : (k4_xboole_0(X40,k2_xboole_0(X39,k4_xboole_0(X39,X40))) = k4_xboole_0(X40,k3_xboole_0(X40,X39))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f5562,f32479])).
% 28.92/4.03  fof(f34080,plain,(
% 28.92/4.03    ( ! [X74,X73] : (k4_xboole_0(X73,k2_xboole_0(X74,k3_xboole_0(X73,X73))) = k4_xboole_0(k4_xboole_0(X74,X73),k4_xboole_0(X74,k2_xboole_0(X73,k4_xboole_0(X73,X74))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f34079,f5731])).
% 28.92/4.03  fof(f34079,plain,(
% 28.92/4.03    ( ! [X74,X73] : (k4_xboole_0(X73,k2_xboole_0(X74,k3_xboole_0(X73,X73))) = k4_xboole_0(k4_xboole_0(X74,X73),k4_xboole_0(X74,k2_xboole_0(X73,k3_xboole_0(X74,X73))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f34078,f1479])).
% 28.92/4.03  fof(f34078,plain,(
% 28.92/4.03    ( ! [X74,X73] : (k4_xboole_0(X73,k2_xboole_0(X74,k3_xboole_0(X73,X73))) = k4_xboole_0(k4_xboole_0(X74,X73),k4_xboole_0(X74,k2_xboole_0(k3_xboole_0(X74,X73),X73)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f34077,f20])).
% 28.92/4.03  fof(f34077,plain,(
% 28.92/4.03    ( ! [X74,X73] : (k4_xboole_0(X73,k2_xboole_0(X74,k3_xboole_0(X73,X73))) = k4_xboole_0(k4_xboole_0(X74,X73),k4_xboole_0(k4_xboole_0(X74,k3_xboole_0(X74,X73)),X73))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f34076,f12278])).
% 28.92/4.03  fof(f12278,plain,(
% 28.92/4.03    ( ! [X19,X18] : (k4_xboole_0(X18,k3_xboole_0(X18,X19)) = k3_xboole_0(X18,k5_xboole_0(X19,k2_xboole_0(X18,X19)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f12171,f5493])).
% 28.92/4.03  fof(f12171,plain,(
% 28.92/4.03    ( ! [X19,X18] : (k4_xboole_0(X18,k4_xboole_0(k3_xboole_0(X18,X19),k4_xboole_0(X19,k2_xboole_0(X18,X19)))) = k3_xboole_0(X18,k5_xboole_0(X19,k2_xboole_0(X18,X19)))) )),
% 28.92/4.03    inference(superposition,[],[f364,f111])).
% 28.92/4.03  fof(f364,plain,(
% 28.92/4.03    ( ! [X6,X7,X5] : (k3_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),X7)) = k4_xboole_0(X5,k4_xboole_0(k3_xboole_0(X5,X6),X7))) )),
% 28.92/4.03    inference(superposition,[],[f17,f60])).
% 28.92/4.03  fof(f34076,plain,(
% 28.92/4.03    ( ! [X74,X73] : (k4_xboole_0(X73,k2_xboole_0(X74,k3_xboole_0(X73,X73))) = k4_xboole_0(k4_xboole_0(X74,X73),k4_xboole_0(k3_xboole_0(X74,k5_xboole_0(X73,k2_xboole_0(X74,X73))),X73))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f34075,f443])).
% 28.92/4.03  fof(f34075,plain,(
% 28.92/4.03    ( ! [X74,X73] : (k4_xboole_0(k4_xboole_0(X74,X73),k3_xboole_0(k4_xboole_0(X74,X73),k5_xboole_0(X73,k2_xboole_0(X74,X73)))) = k4_xboole_0(X73,k2_xboole_0(X74,k3_xboole_0(X73,X73)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f34074,f33071])).
% 28.92/4.03  fof(f33071,plain,(
% 28.92/4.03    ( ! [X23,X21,X22] : (k4_xboole_0(k5_xboole_0(k2_xboole_0(X21,X22),k2_xboole_0(X22,X23)),k4_xboole_0(X21,k2_xboole_0(X22,X23))) = k4_xboole_0(X23,k2_xboole_0(X22,k3_xboole_0(X23,X21)))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f32845,f33003])).
% 28.92/4.03  fof(f33003,plain,(
% 28.92/4.03    ( ! [X26,X24,X25] : (k4_xboole_0(X25,k3_xboole_0(X25,k2_xboole_0(X24,X26))) = k4_xboole_0(X25,k2_xboole_0(X24,k3_xboole_0(X25,X26)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f32871,f534])).
% 28.92/4.03  fof(f534,plain,(
% 28.92/4.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,k3_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X1,X2))),X1)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f533,f15])).
% 28.92/4.03  fof(f533,plain,(
% 28.92/4.03    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X1,X2))),X1) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k3_xboole_0(X0,X2),X1)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f532,f443])).
% 28.92/4.03  fof(f532,plain,(
% 28.92/4.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,k3_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X1,X2))),X1)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f531,f27])).
% 28.92/4.03  fof(f531,plain,(
% 28.92/4.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,k3_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))),X1)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f530,f20])).
% 28.92/4.03  fof(f530,plain,(
% 28.92/4.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,k3_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k3_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2)),X1)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f513,f20])).
% 28.92/4.03  fof(f513,plain,(
% 28.92/4.03    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2)),X1) = k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 28.92/4.03    inference(superposition,[],[f27,f443])).
% 28.92/4.03  fof(f32871,plain,(
% 28.92/4.03    ( ! [X26,X24,X25] : (k4_xboole_0(X25,k3_xboole_0(X25,k2_xboole_0(X24,X26))) = k4_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,k2_xboole_0(X24,X26))),X24)) )),
% 28.92/4.03    inference(backward_demodulation,[],[f30004,f32479])).
% 28.92/4.03  fof(f30004,plain,(
% 28.92/4.03    ( ! [X26,X24,X25] : (k4_xboole_0(k3_xboole_0(X25,X25),k2_xboole_0(X24,X26)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X25,X25),k2_xboole_0(X24,X26)),X24)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f30003,f1589])).
% 28.92/4.03  fof(f30003,plain,(
% 28.92/4.03    ( ! [X26,X24,X25] : (k4_xboole_0(k3_xboole_0(X25,X25),k2_xboole_0(X24,X26)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X25,k4_xboole_0(X25,k2_xboole_0(X24,X26))),k2_xboole_0(X24,X26)),X24)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f30002,f443])).
% 28.92/4.03  fof(f30002,plain,(
% 28.92/4.03    ( ! [X26,X24,X25] : (k4_xboole_0(k3_xboole_0(X25,X25),k2_xboole_0(X24,X26)) = k4_xboole_0(k3_xboole_0(k4_xboole_0(X25,k2_xboole_0(X24,X26)),k4_xboole_0(X25,k2_xboole_0(X24,X26))),X24)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f30001,f29998])).
% 28.92/4.03  fof(f29998,plain,(
% 28.92/4.03    ( ! [X90,X91,X89] : (k4_xboole_0(k2_xboole_0(X89,k4_xboole_0(X90,X91)),k4_xboole_0(X89,k4_xboole_0(X90,k2_xboole_0(X89,X91)))) = k4_xboole_0(k3_xboole_0(X90,X90),k2_xboole_0(X89,X91))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f4064,f29995])).
% 28.92/4.03  fof(f29995,plain,(
% 28.92/4.03    ( ! [X23,X21,X22] : (k4_xboole_0(k3_xboole_0(X22,X22),k2_xboole_0(X21,X23)) = k4_xboole_0(X22,k2_xboole_0(X21,k2_xboole_0(X23,k4_xboole_0(X21,k4_xboole_0(X22,X21)))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f29994,f7772])).
% 28.92/4.03  fof(f29994,plain,(
% 28.92/4.03    ( ! [X23,X21,X22] : (k4_xboole_0(X22,k2_xboole_0(X21,k2_xboole_0(X23,k4_xboole_0(X21,k4_xboole_0(X22,X21))))) = k4_xboole_0(k3_xboole_0(X22,X22),k2_xboole_0(X23,k2_xboole_0(X21,X21)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f29993,f71])).
% 28.92/4.03  fof(f29993,plain,(
% 28.92/4.03    ( ! [X23,X21,X22] : (k4_xboole_0(X22,k2_xboole_0(X21,k2_xboole_0(X23,k4_xboole_0(X21,k4_xboole_0(X22,X21))))) = k4_xboole_0(k3_xboole_0(X22,X22),k2_xboole_0(k2_xboole_0(X23,X21),X21))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f29992,f20])).
% 28.92/4.03  fof(f29992,plain,(
% 28.92/4.03    ( ! [X23,X21,X22] : (k4_xboole_0(X22,k2_xboole_0(X21,k2_xboole_0(X23,k4_xboole_0(X21,k4_xboole_0(X22,X21))))) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X22,X22),k2_xboole_0(X23,X21)),X21)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f29991,f1589])).
% 28.92/4.03  fof(f29991,plain,(
% 28.92/4.03    ( ! [X23,X21,X22] : (k4_xboole_0(X22,k2_xboole_0(X21,k2_xboole_0(X23,k4_xboole_0(X21,k4_xboole_0(X22,X21))))) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X22,k4_xboole_0(X22,k2_xboole_0(X23,X21))),k2_xboole_0(X23,X21)),X21)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f29990,f443])).
% 28.92/4.03  fof(f29990,plain,(
% 28.92/4.03    ( ! [X23,X21,X22] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X22,k2_xboole_0(X23,X21)),k4_xboole_0(X22,k2_xboole_0(X23,X21))),X21) = k4_xboole_0(X22,k2_xboole_0(X21,k2_xboole_0(X23,k4_xboole_0(X21,k4_xboole_0(X22,X21)))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f29989,f4064])).
% 28.92/4.03  fof(f29989,plain,(
% 28.92/4.03    ( ! [X23,X21,X22] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X22,k2_xboole_0(X23,X21)),k4_xboole_0(X22,k2_xboole_0(X23,X21))),X21) = k4_xboole_0(k2_xboole_0(X21,k4_xboole_0(X22,X23)),k4_xboole_0(X21,k4_xboole_0(X22,k2_xboole_0(X21,X23))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f29988,f25])).
% 28.92/4.03  fof(f29988,plain,(
% 28.92/4.03    ( ! [X23,X21,X22] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X22,k2_xboole_0(X23,X21)),k4_xboole_0(X22,k2_xboole_0(X23,X21))),X21) = k4_xboole_0(k2_xboole_0(X21,k4_xboole_0(X22,X23)),k4_xboole_0(X21,k4_xboole_0(X22,k2_xboole_0(X21,k2_xboole_0(X23,X21)))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f29987,f4034])).
% 28.92/4.03  fof(f4034,plain,(
% 28.92/4.03    ( ! [X30,X31,X29] : (k4_xboole_0(X29,k4_xboole_0(X30,k2_xboole_0(X31,X29))) = k4_xboole_0(X29,k4_xboole_0(X30,k2_xboole_0(X29,X31)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f4033,f25])).
% 28.92/4.03  fof(f4033,plain,(
% 28.92/4.03    ( ! [X30,X31,X29] : (k4_xboole_0(X29,k4_xboole_0(X30,k2_xboole_0(X31,X29))) = k4_xboole_0(X29,k4_xboole_0(X30,k2_xboole_0(X29,k2_xboole_0(X31,X29))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f4032,f71])).
% 28.92/4.03  fof(f4032,plain,(
% 28.92/4.03    ( ! [X30,X31,X29] : (k4_xboole_0(X29,k4_xboole_0(X30,k2_xboole_0(X31,X29))) = k4_xboole_0(X29,k4_xboole_0(X30,k2_xboole_0(k2_xboole_0(X29,X31),X29)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f4031,f20])).
% 28.92/4.03  fof(f4031,plain,(
% 28.92/4.03    ( ! [X30,X31,X29] : (k4_xboole_0(X29,k4_xboole_0(k4_xboole_0(X30,k2_xboole_0(X29,X31)),X29)) = k4_xboole_0(X29,k4_xboole_0(X30,k2_xboole_0(X31,X29)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f4030,f20])).
% 28.92/4.03  fof(f4030,plain,(
% 28.92/4.03    ( ! [X30,X31,X29] : (k4_xboole_0(X29,k4_xboole_0(k4_xboole_0(X30,k2_xboole_0(X29,X31)),X29)) = k4_xboole_0(X29,k4_xboole_0(k4_xboole_0(X30,X31),X29))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f3958,f52])).
% 28.92/4.03  fof(f3958,plain,(
% 28.92/4.03    ( ! [X30,X31,X29] : (k4_xboole_0(X29,k4_xboole_0(k4_xboole_0(X30,k2_xboole_0(X29,X31)),X29)) = k3_xboole_0(k2_xboole_0(X29,k4_xboole_0(X30,X31)),X29)) )),
% 28.92/4.03    inference(superposition,[],[f52,f419])).
% 28.92/4.03  fof(f29987,plain,(
% 28.92/4.03    ( ! [X23,X21,X22] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X22,k2_xboole_0(X23,X21)),k4_xboole_0(X22,k2_xboole_0(X23,X21))),X21) = k4_xboole_0(k2_xboole_0(X21,k4_xboole_0(X22,X23)),k4_xboole_0(X21,k4_xboole_0(X22,k2_xboole_0(k2_xboole_0(X23,X21),X21))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f29818,f20])).
% 28.92/4.03  fof(f29818,plain,(
% 28.92/4.03    ( ! [X23,X21,X22] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X22,k2_xboole_0(X23,X21)),k4_xboole_0(X22,k2_xboole_0(X23,X21))),X21) = k4_xboole_0(k2_xboole_0(X21,k4_xboole_0(X22,X23)),k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X22,k2_xboole_0(X23,X21)),X21)))) )),
% 28.92/4.03    inference(superposition,[],[f5578,f66])).
% 28.92/4.03  fof(f5578,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X3,X2))) = k4_xboole_0(k3_xboole_0(X3,X3),X2)) )),
% 28.92/4.03    inference(backward_demodulation,[],[f956,f5562])).
% 28.92/4.03  fof(f956,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X3,X2))) = k4_xboole_0(X3,k2_xboole_0(X2,k4_xboole_0(X2,X3)))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f92,f951])).
% 28.92/4.03  fof(f951,plain,(
% 28.92/4.03    ( ! [X12,X13] : (k4_xboole_0(X12,k2_xboole_0(X13,k4_xboole_0(X13,X12))) = k3_xboole_0(k2_xboole_0(X13,X12),k4_xboole_0(X12,X13))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f950,f110])).
% 28.92/4.03  fof(f110,plain,(
% 28.92/4.03    ( ! [X10,X8,X9] : (k4_xboole_0(k4_xboole_0(X8,X9),k2_xboole_0(X9,X10)) = k4_xboole_0(X8,k2_xboole_0(X9,X10))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f104,f20])).
% 28.92/4.03  fof(f104,plain,(
% 28.92/4.03    ( ! [X10,X8,X9] : (k4_xboole_0(k4_xboole_0(X8,X9),k2_xboole_0(X9,X10)) = k4_xboole_0(k4_xboole_0(X8,X9),X10)) )),
% 28.92/4.03    inference(superposition,[],[f20,f50])).
% 28.92/4.03  fof(f950,plain,(
% 28.92/4.03    ( ! [X12,X13] : (k3_xboole_0(k2_xboole_0(X13,X12),k4_xboole_0(X12,X13)) = k4_xboole_0(k4_xboole_0(X12,X13),k2_xboole_0(X13,k4_xboole_0(X13,X12)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f949,f462])).
% 28.92/4.03  fof(f462,plain,(
% 28.92/4.03    ( ! [X26,X27,X25] : (k2_xboole_0(X26,k4_xboole_0(X27,k4_xboole_0(X25,X26))) = k2_xboole_0(X26,k4_xboole_0(X27,X25))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f427,f419])).
% 28.92/4.03  fof(f427,plain,(
% 28.92/4.03    ( ! [X26,X27,X25] : (k2_xboole_0(X26,k4_xboole_0(X27,k4_xboole_0(X25,X26))) = k2_xboole_0(X26,k4_xboole_0(X27,k2_xboole_0(X26,X25)))) )),
% 28.92/4.03    inference(superposition,[],[f66,f211])).
% 28.92/4.03  fof(f949,plain,(
% 28.92/4.03    ( ! [X12,X13] : (k4_xboole_0(k4_xboole_0(X12,X13),k2_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X12,X13)))) = k3_xboole_0(k2_xboole_0(X13,X12),k4_xboole_0(X12,X13))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f912,f92])).
% 28.92/4.03  fof(f912,plain,(
% 28.92/4.03    ( ! [X12,X13] : (k4_xboole_0(k4_xboole_0(X12,X13),k2_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X12,X13)))) = k4_xboole_0(k2_xboole_0(X13,X12),k4_xboole_0(X13,k4_xboole_0(X12,X13)))) )),
% 28.92/4.03    inference(superposition,[],[f41,f109])).
% 28.92/4.03  fof(f92,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k3_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X3,X2)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f89,f52])).
% 28.92/4.03  fof(f89,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k3_xboole_0(k2_xboole_0(X2,X3),X2)) = k3_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2))) )),
% 28.92/4.03    inference(superposition,[],[f27,f21])).
% 28.92/4.03  fof(f4064,plain,(
% 28.92/4.03    ( ! [X90,X91,X89] : (k4_xboole_0(k2_xboole_0(X89,k4_xboole_0(X90,X91)),k4_xboole_0(X89,k4_xboole_0(X90,k2_xboole_0(X89,X91)))) = k4_xboole_0(X90,k2_xboole_0(X89,k2_xboole_0(X91,k4_xboole_0(X89,k4_xboole_0(X90,X89)))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f4063,f3987])).
% 28.92/4.03  fof(f3987,plain,(
% 28.92/4.03    ( ! [X14,X12,X15,X13] : (k2_xboole_0(X12,k4_xboole_0(X15,k4_xboole_0(X13,k2_xboole_0(X14,X12)))) = k2_xboole_0(X12,k4_xboole_0(X15,k4_xboole_0(X13,X14)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f3922,f419])).
% 28.92/4.03  fof(f3922,plain,(
% 28.92/4.03    ( ! [X14,X12,X15,X13] : (k2_xboole_0(X12,k4_xboole_0(X15,k4_xboole_0(X13,k2_xboole_0(X14,X12)))) = k2_xboole_0(X12,k4_xboole_0(X15,k2_xboole_0(X12,k4_xboole_0(X13,X14))))) )),
% 28.92/4.03    inference(superposition,[],[f419,f66])).
% 28.92/4.03  fof(f4063,plain,(
% 28.92/4.03    ( ! [X90,X91,X89] : (k4_xboole_0(k2_xboole_0(X89,k4_xboole_0(X90,X91)),k4_xboole_0(X89,k4_xboole_0(X90,k2_xboole_0(X89,X91)))) = k4_xboole_0(X90,k2_xboole_0(X89,k2_xboole_0(X91,k4_xboole_0(X89,k4_xboole_0(X90,k2_xboole_0(X89,X91))))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f4062,f71])).
% 28.92/4.03  fof(f4062,plain,(
% 28.92/4.03    ( ! [X90,X91,X89] : (k4_xboole_0(k2_xboole_0(X89,k4_xboole_0(X90,X91)),k4_xboole_0(X89,k4_xboole_0(X90,k2_xboole_0(X89,X91)))) = k4_xboole_0(X90,k2_xboole_0(k2_xboole_0(X89,X91),k4_xboole_0(X89,k4_xboole_0(X90,k2_xboole_0(X89,X91)))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f3975,f20])).
% 28.92/4.03  fof(f3975,plain,(
% 28.92/4.03    ( ! [X90,X91,X89] : (k4_xboole_0(k4_xboole_0(X90,k2_xboole_0(X89,X91)),k4_xboole_0(X89,k4_xboole_0(X90,k2_xboole_0(X89,X91)))) = k4_xboole_0(k2_xboole_0(X89,k4_xboole_0(X90,X91)),k4_xboole_0(X89,k4_xboole_0(X90,k2_xboole_0(X89,X91))))) )),
% 28.92/4.03    inference(superposition,[],[f171,f419])).
% 28.92/4.03  fof(f30001,plain,(
% 28.92/4.03    ( ! [X26,X24,X25] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X25,k2_xboole_0(X24,X26)),k4_xboole_0(X25,k2_xboole_0(X24,X26))),X24) = k4_xboole_0(k2_xboole_0(X24,k4_xboole_0(X25,X26)),k4_xboole_0(X24,k4_xboole_0(X25,k2_xboole_0(X24,X26))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f30000,f53])).
% 28.92/4.03  fof(f30000,plain,(
% 28.92/4.03    ( ! [X26,X24,X25] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X25,k2_xboole_0(X24,X26)),k4_xboole_0(X25,k2_xboole_0(X24,X26))),X24) = k4_xboole_0(k2_xboole_0(X24,k4_xboole_0(X25,X26)),k4_xboole_0(X24,k4_xboole_0(X25,k2_xboole_0(X24,k2_xboole_0(X24,X26)))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f29999,f4034])).
% 28.92/4.03  fof(f29999,plain,(
% 28.92/4.03    ( ! [X26,X24,X25] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X25,k2_xboole_0(X24,X26)),k4_xboole_0(X25,k2_xboole_0(X24,X26))),X24) = k4_xboole_0(k2_xboole_0(X24,k4_xboole_0(X25,X26)),k4_xboole_0(X24,k4_xboole_0(X25,k2_xboole_0(k2_xboole_0(X24,X26),X24))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f29819,f20])).
% 28.92/4.03  fof(f29819,plain,(
% 28.92/4.03    ( ! [X26,X24,X25] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X25,k2_xboole_0(X24,X26)),k4_xboole_0(X25,k2_xboole_0(X24,X26))),X24) = k4_xboole_0(k2_xboole_0(X24,k4_xboole_0(X25,X26)),k4_xboole_0(X24,k4_xboole_0(k4_xboole_0(X25,k2_xboole_0(X24,X26)),X24)))) )),
% 28.92/4.03    inference(superposition,[],[f5578,f419])).
% 28.92/4.03  fof(f32845,plain,(
% 28.92/4.03    ( ! [X23,X21,X22] : (k4_xboole_0(k5_xboole_0(k2_xboole_0(X21,X22),k2_xboole_0(X22,X23)),k4_xboole_0(X21,k2_xboole_0(X22,X23))) = k4_xboole_0(X23,k3_xboole_0(X23,k2_xboole_0(X22,X21)))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f21197,f32479])).
% 28.92/4.03  fof(f21197,plain,(
% 28.92/4.03    ( ! [X23,X21,X22] : (k4_xboole_0(k5_xboole_0(k2_xboole_0(X21,X22),k2_xboole_0(X22,X23)),k4_xboole_0(X21,k2_xboole_0(X22,X23))) = k4_xboole_0(k3_xboole_0(X23,X23),k2_xboole_0(X22,X21))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f7132,f21195])).
% 28.92/4.03  fof(f21195,plain,(
% 28.92/4.03    ( ! [X23,X21,X22] : (k4_xboole_0(k3_xboole_0(k2_xboole_0(X22,X23),k2_xboole_0(X22,X23)),k2_xboole_0(X21,X22)) = k4_xboole_0(k3_xboole_0(X23,X23),k2_xboole_0(X22,X21))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f5824,f21194])).
% 28.92/4.03  fof(f21194,plain,(
% 28.92/4.03    ( ! [X12,X13,X11] : (k4_xboole_0(k5_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X11,X12)),k4_xboole_0(X11,k2_xboole_0(X12,X13))) = k4_xboole_0(k3_xboole_0(X13,X13),k2_xboole_0(X12,X11))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f21193,f6818])).
% 28.92/4.03  fof(f6818,plain,(
% 28.92/4.03    ( ! [X64,X62,X63] : (k4_xboole_0(X64,k2_xboole_0(X62,k2_xboole_0(X63,k4_xboole_0(X63,X64)))) = k4_xboole_0(k3_xboole_0(X64,X64),k2_xboole_0(X62,X63))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f4075,f6817])).
% 28.92/4.03  fof(f6817,plain,(
% 28.92/4.03    ( ! [X26,X24,X25] : (k4_xboole_0(k5_xboole_0(k2_xboole_0(X24,X26),k2_xboole_0(X24,X25)),k4_xboole_0(X25,k2_xboole_0(X24,X26))) = k4_xboole_0(k3_xboole_0(X26,X26),k2_xboole_0(X24,X25))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f5937,f6816])).
% 28.92/4.03  fof(f6816,plain,(
% 28.92/4.03    ( ! [X37,X35,X36,X34] : (k4_xboole_0(k3_xboole_0(X37,k2_xboole_0(X34,X35)),k2_xboole_0(X34,X36)) = k4_xboole_0(k3_xboole_0(X37,X35),k2_xboole_0(X34,X36))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f6732,f1589])).
% 28.92/4.03  fof(f6732,plain,(
% 28.92/4.03    ( ! [X37,X35,X36,X34] : (k4_xboole_0(k3_xboole_0(X37,k2_xboole_0(X34,X35)),k2_xboole_0(X34,X36)) = k4_xboole_0(k3_xboole_0(X37,k4_xboole_0(X35,k2_xboole_0(X34,X36))),k2_xboole_0(X34,X36))) )),
% 28.92/4.03    inference(superposition,[],[f1589,f69])).
% 28.92/4.03  fof(f5937,plain,(
% 28.92/4.03    ( ! [X26,X24,X25] : (k4_xboole_0(k5_xboole_0(k2_xboole_0(X24,X26),k2_xboole_0(X24,X25)),k4_xboole_0(X25,k2_xboole_0(X24,X26))) = k4_xboole_0(k3_xboole_0(X26,k2_xboole_0(X24,X26)),k2_xboole_0(X24,X25))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f5825,f2665])).
% 28.92/4.03  fof(f2665,plain,(
% 28.92/4.03    ( ! [X109,X107,X110,X108] : (k4_xboole_0(k3_xboole_0(k2_xboole_0(X107,X108),X110),k2_xboole_0(X107,X109)) = k4_xboole_0(k3_xboole_0(X108,X110),k2_xboole_0(X107,X109))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f2588,f443])).
% 28.92/4.03  fof(f2588,plain,(
% 28.92/4.03    ( ! [X109,X107,X110,X108] : (k4_xboole_0(k3_xboole_0(k2_xboole_0(X107,X108),X110),k2_xboole_0(X107,X109)) = k3_xboole_0(k4_xboole_0(X108,k2_xboole_0(X107,X109)),X110)) )),
% 28.92/4.03    inference(superposition,[],[f443,f69])).
% 28.92/4.03  fof(f5825,plain,(
% 28.92/4.03    ( ! [X26,X24,X25] : (k4_xboole_0(k3_xboole_0(k2_xboole_0(X24,X26),k2_xboole_0(X24,X26)),k2_xboole_0(X24,X25)) = k4_xboole_0(k5_xboole_0(k2_xboole_0(X24,X26),k2_xboole_0(X24,X25)),k4_xboole_0(X25,k2_xboole_0(X24,X26)))) )),
% 28.92/4.03    inference(superposition,[],[f5563,f69])).
% 28.92/4.03  fof(f4075,plain,(
% 28.92/4.03    ( ! [X64,X62,X63] : (k4_xboole_0(k5_xboole_0(k2_xboole_0(X62,X64),k2_xboole_0(X62,X63)),k4_xboole_0(X63,k2_xboole_0(X62,X64))) = k4_xboole_0(X64,k2_xboole_0(X62,k2_xboole_0(X63,k4_xboole_0(X63,X64))))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f2653,f4074])).
% 28.92/4.03  fof(f4074,plain,(
% 28.92/4.03    ( ! [X118,X116,X114,X117,X115] : (k4_xboole_0(X118,k2_xboole_0(X114,k2_xboole_0(X115,k4_xboole_0(X116,X117)))) = k4_xboole_0(X118,k2_xboole_0(X114,k2_xboole_0(X115,k4_xboole_0(X116,k2_xboole_0(X114,X117)))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f4073,f4007])).
% 28.92/4.03  fof(f4007,plain,(
% 28.92/4.03    ( ! [X26,X24,X27,X25] : (k2_xboole_0(X26,k4_xboole_0(X24,k2_xboole_0(X25,k2_xboole_0(X26,X27)))) = k2_xboole_0(X26,k4_xboole_0(X24,k2_xboole_0(X25,X27)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f3949,f20])).
% 28.92/4.03  fof(f3949,plain,(
% 28.92/4.03    ( ! [X26,X24,X27,X25] : (k2_xboole_0(X26,k4_xboole_0(k4_xboole_0(X24,X25),X27)) = k2_xboole_0(X26,k4_xboole_0(X24,k2_xboole_0(X25,k2_xboole_0(X26,X27))))) )),
% 28.92/4.03    inference(superposition,[],[f419,f20])).
% 28.92/4.03  fof(f4073,plain,(
% 28.92/4.03    ( ! [X118,X116,X114,X117,X115] : (k4_xboole_0(X118,k2_xboole_0(X114,k2_xboole_0(X115,k4_xboole_0(X116,X117)))) = k4_xboole_0(X118,k2_xboole_0(X114,k2_xboole_0(X115,k4_xboole_0(X116,k2_xboole_0(X114,k2_xboole_0(X115,X117))))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f4072,f71])).
% 28.92/4.03  fof(f4072,plain,(
% 28.92/4.03    ( ! [X118,X116,X114,X117,X115] : (k4_xboole_0(X118,k2_xboole_0(X114,k2_xboole_0(X115,k4_xboole_0(X116,k2_xboole_0(k2_xboole_0(X114,X115),X117))))) = k4_xboole_0(X118,k2_xboole_0(X114,k2_xboole_0(X115,k4_xboole_0(X116,X117))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f3983,f71])).
% 28.92/4.03  fof(f3983,plain,(
% 28.92/4.03    ( ! [X118,X116,X114,X117,X115] : (k4_xboole_0(X118,k2_xboole_0(X114,k2_xboole_0(X115,k4_xboole_0(X116,k2_xboole_0(k2_xboole_0(X114,X115),X117))))) = k4_xboole_0(X118,k2_xboole_0(k2_xboole_0(X114,X115),k4_xboole_0(X116,X117)))) )),
% 28.92/4.03    inference(superposition,[],[f71,f419])).
% 28.92/4.03  fof(f2653,plain,(
% 28.92/4.03    ( ! [X64,X62,X63] : (k4_xboole_0(k5_xboole_0(k2_xboole_0(X62,X64),k2_xboole_0(X62,X63)),k4_xboole_0(X63,k2_xboole_0(X62,X64))) = k4_xboole_0(X64,k2_xboole_0(X62,k2_xboole_0(X63,k4_xboole_0(X63,k2_xboole_0(X62,X64)))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f2652,f69])).
% 28.92/4.03  fof(f2652,plain,(
% 28.92/4.03    ( ! [X64,X62,X63] : (k4_xboole_0(k5_xboole_0(k2_xboole_0(X62,X64),k2_xboole_0(X62,X63)),k4_xboole_0(X63,k2_xboole_0(X62,X64))) = k4_xboole_0(k2_xboole_0(X62,X64),k2_xboole_0(X62,k2_xboole_0(X63,k4_xboole_0(X63,k2_xboole_0(X62,X64)))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f2574,f71])).
% 28.92/4.03  fof(f2574,plain,(
% 28.92/4.03    ( ! [X64,X62,X63] : (k4_xboole_0(k5_xboole_0(k2_xboole_0(X62,X64),k2_xboole_0(X62,X63)),k4_xboole_0(X63,k2_xboole_0(X62,X64))) = k4_xboole_0(k2_xboole_0(X62,X64),k2_xboole_0(k2_xboole_0(X62,X63),k4_xboole_0(X63,k2_xboole_0(X62,X64))))) )),
% 28.92/4.03    inference(superposition,[],[f41,f69])).
% 28.92/4.03  fof(f21193,plain,(
% 28.92/4.03    ( ! [X12,X13,X11] : (k4_xboole_0(k5_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X11,X12)),k4_xboole_0(X11,k2_xboole_0(X12,X13))) = k4_xboole_0(X13,k2_xboole_0(X12,k2_xboole_0(X11,k4_xboole_0(X11,X13))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f21192,f12516])).
% 28.92/4.03  fof(f12516,plain,(
% 28.92/4.03    ( ! [X151,X149,X150,X148] : (k4_xboole_0(X151,k2_xboole_0(X148,k2_xboole_0(X149,X150))) = k4_xboole_0(X151,k2_xboole_0(X148,k2_xboole_0(X150,X149)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f12515,f7772])).
% 28.92/4.03  fof(f12515,plain,(
% 28.92/4.03    ( ! [X151,X149,X150,X148] : (k4_xboole_0(X151,k2_xboole_0(X148,k2_xboole_0(X149,k2_xboole_0(X150,X150)))) = k4_xboole_0(X151,k2_xboole_0(X148,k2_xboole_0(X149,X150)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f12417,f71])).
% 28.92/4.03  fof(f12417,plain,(
% 28.92/4.03    ( ! [X151,X149,X150,X148] : (k4_xboole_0(X151,k2_xboole_0(X148,k2_xboole_0(X149,k2_xboole_0(X150,X150)))) = k4_xboole_0(X151,k2_xboole_0(k2_xboole_0(X148,X149),X150))) )),
% 28.92/4.03    inference(superposition,[],[f71,f9458])).
% 28.92/4.03  fof(f21192,plain,(
% 28.92/4.03    ( ! [X12,X13,X11] : (k4_xboole_0(k5_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X11,X12)),k4_xboole_0(X11,k2_xboole_0(X12,X13))) = k4_xboole_0(X13,k2_xboole_0(X12,k2_xboole_0(k4_xboole_0(X11,X13),X11)))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f967,f20779])).
% 28.92/4.03  fof(f20779,plain,(
% 28.92/4.03    ( ! [X43,X41,X42,X40] : (k4_xboole_0(X41,k2_xboole_0(X40,k2_xboole_0(X42,X43))) = k4_xboole_0(k2_xboole_0(X40,X41),k2_xboole_0(X43,k2_xboole_0(X40,X42)))) )),
% 28.92/4.03    inference(superposition,[],[f1068,f69])).
% 28.92/4.03  fof(f967,plain,(
% 28.92/4.03    ( ! [X12,X13,X11] : (k4_xboole_0(k5_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X11,X12)),k4_xboole_0(X11,k2_xboole_0(X12,X13))) = k4_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X11,k2_xboole_0(X12,k4_xboole_0(X11,X13))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f966,f419])).
% 28.92/4.03  fof(f966,plain,(
% 28.92/4.03    ( ! [X12,X13,X11] : (k4_xboole_0(k5_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X11,X12)),k4_xboole_0(X11,k2_xboole_0(X12,X13))) = k4_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X11,k2_xboole_0(X12,k4_xboole_0(X11,k2_xboole_0(X12,X13)))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f918,f71])).
% 28.92/4.03  fof(f918,plain,(
% 28.92/4.03    ( ! [X12,X13,X11] : (k4_xboole_0(k5_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X11,X12)),k4_xboole_0(X11,k2_xboole_0(X12,X13))) = k4_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(k2_xboole_0(X11,X12),k4_xboole_0(X11,k2_xboole_0(X12,X13))))) )),
% 28.92/4.03    inference(superposition,[],[f41,f68])).
% 28.92/4.03  fof(f5824,plain,(
% 28.92/4.03    ( ! [X23,X21,X22] : (k4_xboole_0(k3_xboole_0(k2_xboole_0(X22,X23),k2_xboole_0(X22,X23)),k2_xboole_0(X21,X22)) = k4_xboole_0(k5_xboole_0(k2_xboole_0(X22,X23),k2_xboole_0(X21,X22)),k4_xboole_0(X21,k2_xboole_0(X22,X23)))) )),
% 28.92/4.03    inference(superposition,[],[f5563,f68])).
% 28.92/4.03  fof(f7132,plain,(
% 28.92/4.03    ( ! [X23,X21,X22] : (k4_xboole_0(k3_xboole_0(k2_xboole_0(X22,X23),k2_xboole_0(X22,X23)),k2_xboole_0(X21,X22)) = k4_xboole_0(k5_xboole_0(k2_xboole_0(X21,X22),k2_xboole_0(X22,X23)),k4_xboole_0(X21,k2_xboole_0(X22,X23)))) )),
% 28.92/4.03    inference(superposition,[],[f5564,f68])).
% 28.92/4.03  fof(f5564,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k4_xboole_0(k5_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = k4_xboole_0(k3_xboole_0(X7,X7),X6)) )),
% 28.92/4.03    inference(backward_demodulation,[],[f51,f5562])).
% 28.92/4.03  fof(f51,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k4_xboole_0(k5_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = k4_xboole_0(X7,k2_xboole_0(X6,k4_xboole_0(X6,X7)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f45,f20])).
% 28.92/4.03  fof(f45,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7)) = k4_xboole_0(k5_xboole_0(X6,X7),k4_xboole_0(X6,X7))) )),
% 28.92/4.03    inference(superposition,[],[f21,f18])).
% 28.92/4.03  fof(f34074,plain,(
% 28.92/4.03    ( ! [X74,X73] : (k4_xboole_0(k4_xboole_0(X74,X73),k3_xboole_0(k4_xboole_0(X74,X73),k5_xboole_0(X73,k2_xboole_0(X74,X73)))) = k4_xboole_0(k5_xboole_0(k2_xboole_0(X73,X74),k2_xboole_0(X74,X73)),k4_xboole_0(X73,k2_xboole_0(X74,X73)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f33844,f336])).
% 28.92/4.03  fof(f33844,plain,(
% 28.92/4.03    ( ! [X74,X73] : (k4_xboole_0(k4_xboole_0(X74,X73),k3_xboole_0(k4_xboole_0(X74,X73),k5_xboole_0(X73,k2_xboole_0(X74,X73)))) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X74,X73),k5_xboole_0(X73,k2_xboole_0(X74,X73))),k4_xboole_0(X73,k2_xboole_0(X74,X73)))) )),
% 28.92/4.03    inference(superposition,[],[f32485,f734])).
% 28.92/4.03  fof(f32485,plain,(
% 28.92/4.03    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f5563,f32479])).
% 28.92/4.03  fof(f59141,plain,(
% 28.92/4.03    ( ! [X196,X195] : (k5_xboole_0(X196,k5_xboole_0(X196,k2_xboole_0(X195,X196))) = k5_xboole_0(k2_xboole_0(X195,X196),k4_xboole_0(X196,k2_xboole_0(X195,k3_xboole_0(X196,X196))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f59140,f34049])).
% 28.92/4.03  fof(f34049,plain,(
% 28.92/4.03    ( ! [X47,X48,X49] : (k3_xboole_0(k2_xboole_0(X47,X48),k4_xboole_0(X48,k2_xboole_0(X47,X49))) = k4_xboole_0(X48,k2_xboole_0(X47,k3_xboole_0(X48,X49)))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f2569,f34048])).
% 28.92/4.03  fof(f34048,plain,(
% 28.92/4.03    ( ! [X57,X56,X55] : (k4_xboole_0(k2_xboole_0(X55,X57),k3_xboole_0(k2_xboole_0(X55,X57),k2_xboole_0(X55,X56))) = k4_xboole_0(X57,k2_xboole_0(X55,k3_xboole_0(X57,X56)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f33837,f33014])).
% 28.92/4.03  fof(f33014,plain,(
% 28.92/4.03    ( ! [X26,X24,X25] : (k4_xboole_0(k5_xboole_0(k2_xboole_0(X24,X26),k2_xboole_0(X24,X25)),k4_xboole_0(X25,k2_xboole_0(X24,X26))) = k4_xboole_0(X26,k2_xboole_0(X24,k3_xboole_0(X26,X25)))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f32786,f33003])).
% 28.92/4.03  fof(f32786,plain,(
% 28.92/4.03    ( ! [X26,X24,X25] : (k4_xboole_0(k5_xboole_0(k2_xboole_0(X24,X26),k2_xboole_0(X24,X25)),k4_xboole_0(X25,k2_xboole_0(X24,X26))) = k4_xboole_0(X26,k3_xboole_0(X26,k2_xboole_0(X24,X25)))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f6817,f32479])).
% 28.92/4.03  fof(f33837,plain,(
% 28.92/4.03    ( ! [X57,X56,X55] : (k4_xboole_0(k2_xboole_0(X55,X57),k3_xboole_0(k2_xboole_0(X55,X57),k2_xboole_0(X55,X56))) = k4_xboole_0(k5_xboole_0(k2_xboole_0(X55,X57),k2_xboole_0(X55,X56)),k4_xboole_0(X56,k2_xboole_0(X55,X57)))) )),
% 28.92/4.03    inference(superposition,[],[f32485,f69])).
% 28.92/4.03  fof(f2569,plain,(
% 28.92/4.03    ( ! [X47,X48,X49] : (k4_xboole_0(k2_xboole_0(X47,X48),k3_xboole_0(k2_xboole_0(X47,X48),k2_xboole_0(X47,X49))) = k3_xboole_0(k2_xboole_0(X47,X48),k4_xboole_0(X48,k2_xboole_0(X47,X49)))) )),
% 28.92/4.03    inference(superposition,[],[f27,f69])).
% 28.92/4.03  fof(f59140,plain,(
% 28.92/4.03    ( ! [X196,X195] : (k5_xboole_0(k2_xboole_0(X195,X196),k3_xboole_0(k2_xboole_0(X195,X196),k4_xboole_0(X196,k2_xboole_0(X195,X196)))) = k5_xboole_0(X196,k5_xboole_0(X196,k2_xboole_0(X195,X196)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f59139,f27586])).
% 28.92/4.03  fof(f27586,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k5_xboole_0(X3,k2_xboole_0(X2,X3)) = k5_xboole_0(k2_xboole_0(X3,X2),k2_xboole_0(X3,k4_xboole_0(X3,X2)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f27585,f5502])).
% 28.92/4.03  fof(f5502,plain,(
% 28.92/4.03    ( ! [X14,X13] : (k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X14)) = k5_xboole_0(X14,k2_xboole_0(X13,X14))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f5483,f111])).
% 28.92/4.03  fof(f5483,plain,(
% 28.92/4.03    ( ! [X14,X13] : (k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X14)) = k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X14,k2_xboole_0(X13,X14)))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f451,f5482])).
% 28.92/4.03  fof(f451,plain,(
% 28.92/4.03    ( ! [X14,X13] : (k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X14)) = k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k3_xboole_0(X13,X14),X14))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f295,f443])).
% 28.92/4.03  fof(f295,plain,(
% 28.92/4.03    ( ! [X14,X13] : (k2_xboole_0(k4_xboole_0(X13,X14),k3_xboole_0(k4_xboole_0(X13,X14),X14)) = k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X14))) )),
% 28.92/4.03    inference(superposition,[],[f29,f50])).
% 28.92/4.03  fof(f27585,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k5_xboole_0(k2_xboole_0(X3,X2),k2_xboole_0(X3,k4_xboole_0(X3,X2))) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f27584,f13251])).
% 28.92/4.03  fof(f13251,plain,(
% 28.92/4.03    ( ! [X14,X15,X13] : (k5_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k3_xboole_0(X13,X14),X15)) = k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,X15))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f13250,f3562])).
% 28.92/4.03  fof(f3562,plain,(
% 28.92/4.03    ( ! [X12,X13,X11] : (k2_xboole_0(k4_xboole_0(X11,X13),k4_xboole_0(X11,X12)) = k2_xboole_0(k4_xboole_0(X11,X13),k4_xboole_0(k3_xboole_0(X11,X13),X12))) )),
% 28.92/4.03    inference(superposition,[],[f66,f355])).
% 28.92/4.03  fof(f13250,plain,(
% 28.92/4.03    ( ! [X14,X15,X13] : (k5_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k3_xboole_0(X13,X14),X15)) = k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k3_xboole_0(X13,X14),X15))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f13249,f14])).
% 28.92/4.03  fof(f13249,plain,(
% 28.92/4.03    ( ! [X14,X15,X13] : (k5_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k3_xboole_0(X13,X14),X15)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X13,X14),X15),k4_xboole_0(X13,X14))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f13085,f211])).
% 28.92/4.03  fof(f13085,plain,(
% 28.92/4.03    ( ! [X14,X15,X13] : (k5_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k3_xboole_0(X13,X14),X15)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(k3_xboole_0(X13,X14),X15)),k4_xboole_0(k3_xboole_0(X13,X14),X15))) )),
% 28.92/4.03    inference(superposition,[],[f63,f385])).
% 28.92/4.03  fof(f63,plain,(
% 28.92/4.03    ( ! [X2,X0,X1] : (k5_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 28.92/4.03    inference(superposition,[],[f18,f20])).
% 28.92/4.03  fof(f27584,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k5_xboole_0(k2_xboole_0(X3,X2),k2_xboole_0(X3,k4_xboole_0(X3,X2))) = k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k3_xboole_0(X2,X3),X3))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f27583,f443])).
% 28.92/4.03  fof(f27583,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(k4_xboole_0(X2,X3),X3)) = k5_xboole_0(k2_xboole_0(X3,X2),k2_xboole_0(X3,k4_xboole_0(X3,X2)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f27582,f5731])).
% 28.92/4.03  fof(f27582,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(k4_xboole_0(X2,X3),X3)) = k5_xboole_0(k2_xboole_0(X3,X2),k2_xboole_0(X3,k3_xboole_0(X2,X3)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f27322,f27544])).
% 28.92/4.03  fof(f27544,plain,(
% 28.92/4.03    ( ! [X80,X78,X79] : (k5_xboole_0(k2_xboole_0(X79,X78),k2_xboole_0(X79,k3_xboole_0(X78,X80))) = k5_xboole_0(k4_xboole_0(X78,X79),k5_xboole_0(k2_xboole_0(X79,X78),k2_xboole_0(X79,k4_xboole_0(X78,X80))))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f26656,f27526])).
% 28.92/4.03  fof(f27526,plain,(
% 28.92/4.03    ( ! [X26,X24,X25] : (k5_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(X24,k2_xboole_0(X25,X26))) = k5_xboole_0(k2_xboole_0(X25,X24),k2_xboole_0(X25,k4_xboole_0(X24,X26)))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f23941,f27517])).
% 28.92/4.03  fof(f27517,plain,(
% 28.92/4.03    ( ! [X43,X44,X42] : (k2_xboole_0(k4_xboole_0(X43,k2_xboole_0(X42,k2_xboole_0(X44,X43))),k4_xboole_0(k3_xboole_0(X42,X44),X43)) = k5_xboole_0(k2_xboole_0(X43,X42),k2_xboole_0(X43,k4_xboole_0(X42,X44)))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f24915,f27300])).
% 28.92/4.03  fof(f27300,plain,(
% 28.92/4.03    ( ! [X116,X114,X115,X113] : (k5_xboole_0(k2_xboole_0(X115,X116),k2_xboole_0(X115,k4_xboole_0(X113,X114))) = k5_xboole_0(k4_xboole_0(X116,X115),k4_xboole_0(X113,k2_xboole_0(X114,X115)))) )),
% 28.92/4.03    inference(superposition,[],[f2638,f20])).
% 28.92/4.03  fof(f2638,plain,(
% 28.92/4.03    ( ! [X6,X8,X7] : (k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X8,X6)) = k5_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,X8))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f1857,f2637])).
% 28.92/4.03  fof(f2637,plain,(
% 28.92/4.03    ( ! [X35,X36,X34] : (k5_xboole_0(k2_xboole_0(X34,X35),k2_xboole_0(X34,X36)) = k2_xboole_0(k4_xboole_0(X35,k2_xboole_0(X34,X36)),k4_xboole_0(X36,k2_xboole_0(X34,X35)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f2565,f69])).
% 28.92/4.03  fof(f2565,plain,(
% 28.92/4.03    ( ! [X35,X36,X34] : (k5_xboole_0(k2_xboole_0(X34,X35),k2_xboole_0(X34,X36)) = k2_xboole_0(k4_xboole_0(X35,k2_xboole_0(X34,X36)),k4_xboole_0(k2_xboole_0(X34,X36),k2_xboole_0(X34,X35)))) )),
% 28.92/4.03    inference(superposition,[],[f18,f69])).
% 28.92/4.03  fof(f1857,plain,(
% 28.92/4.03    ( ! [X6,X8,X7] : (k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X8,X6)) = k2_xboole_0(k4_xboole_0(X7,k2_xboole_0(X6,X8)),k4_xboole_0(X8,k2_xboole_0(X6,X7)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f1856,f15])).
% 28.92/4.03  fof(f1856,plain,(
% 28.92/4.03    ( ! [X6,X8,X7] : (k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X8,X6)) = k2_xboole_0(k4_xboole_0(X7,k2_xboole_0(X6,k4_xboole_0(X8,X6))),k4_xboole_0(X8,k2_xboole_0(X6,X7)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f1775,f20])).
% 28.92/4.03  fof(f1775,plain,(
% 28.92/4.03    ( ! [X6,X8,X7] : (k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X8,X6)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X8,X6)),k4_xboole_0(X8,k2_xboole_0(X6,X7)))) )),
% 28.92/4.03    inference(superposition,[],[f63,f15])).
% 28.92/4.03  fof(f24915,plain,(
% 28.92/4.03    ( ! [X43,X44,X42] : (k5_xboole_0(k4_xboole_0(X42,X43),k4_xboole_0(X42,k2_xboole_0(X44,X43))) = k2_xboole_0(k4_xboole_0(X43,k2_xboole_0(X42,k2_xboole_0(X44,X43))),k4_xboole_0(k3_xboole_0(X42,X44),X43))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f24914,f23464])).
% 28.92/4.03  fof(f23464,plain,(
% 28.92/4.03    ( ! [X105,X106,X104] : (k4_xboole_0(X105,k2_xboole_0(X106,k2_xboole_0(X104,X105))) = k4_xboole_0(k3_xboole_0(X106,X105),k2_xboole_0(X104,X105))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f23463,f4693])).
% 28.92/4.03  fof(f4693,plain,(
% 28.92/4.03    ( ! [X21,X22,X20] : (k4_xboole_0(X20,k2_xboole_0(X22,k2_xboole_0(X21,X20))) = k4_xboole_0(k2_xboole_0(X21,X20),k2_xboole_0(X22,k2_xboole_0(X21,X20)))) )),
% 28.92/4.03    inference(superposition,[],[f559,f160])).
% 28.92/4.03  fof(f23463,plain,(
% 28.92/4.03    ( ! [X105,X106,X104] : (k4_xboole_0(k2_xboole_0(X104,X105),k2_xboole_0(X106,k2_xboole_0(X104,X105))) = k4_xboole_0(k3_xboole_0(X106,X105),k2_xboole_0(X104,X105))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f23462,f3513])).
% 28.92/4.03  fof(f3513,plain,(
% 28.92/4.03    ( ! [X59,X60,X58] : (k4_xboole_0(k3_xboole_0(X60,k4_xboole_0(X58,X59)),k2_xboole_0(X58,X59)) = k4_xboole_0(k3_xboole_0(X60,X59),k2_xboole_0(X58,X59))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f2383,f3512])).
% 28.92/4.03  fof(f3512,plain,(
% 28.92/4.03    ( ! [X30,X28,X29] : (k4_xboole_0(k3_xboole_0(X30,k2_xboole_0(X29,X28)),k2_xboole_0(X28,X29)) = k4_xboole_0(k3_xboole_0(X30,X29),k2_xboole_0(X28,X29))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f1517,f3467])).
% 28.92/4.03  fof(f3467,plain,(
% 28.92/4.03    ( ! [X74,X75,X73] : (k4_xboole_0(k3_xboole_0(X75,X74),k2_xboole_0(X73,X74)) = k4_xboole_0(k4_xboole_0(X75,k2_xboole_0(X73,X74)),k4_xboole_0(X75,k2_xboole_0(X74,X73)))) )),
% 28.92/4.03    inference(superposition,[],[f448,f3007])).
% 28.92/4.03  fof(f3007,plain,(
% 28.92/4.03    ( ! [X14,X13] : (k2_xboole_0(X14,X13) = k2_xboole_0(k2_xboole_0(X13,X14),X14)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f2961,f211])).
% 28.92/4.03  fof(f2961,plain,(
% 28.92/4.03    ( ! [X14,X13] : (k2_xboole_0(k2_xboole_0(X13,X14),X14) = k2_xboole_0(k4_xboole_0(X13,X14),X14)) )),
% 28.92/4.03    inference(superposition,[],[f2903,f16])).
% 28.92/4.03  fof(f1517,plain,(
% 28.92/4.03    ( ! [X30,X28,X29] : (k4_xboole_0(k3_xboole_0(X30,k2_xboole_0(X29,X28)),k2_xboole_0(X28,X29)) = k4_xboole_0(k4_xboole_0(X30,k2_xboole_0(X28,X29)),k4_xboole_0(X30,k2_xboole_0(X29,X28)))) )),
% 28.92/4.03    inference(superposition,[],[f448,f84])).
% 28.92/4.03  fof(f2383,plain,(
% 28.92/4.03    ( ! [X59,X60,X58] : (k4_xboole_0(k3_xboole_0(X60,k4_xboole_0(X58,X59)),k2_xboole_0(X58,X59)) = k4_xboole_0(k3_xboole_0(X60,k2_xboole_0(X59,X58)),k2_xboole_0(X58,X59))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f2278,f1517])).
% 28.92/4.03  fof(f2278,plain,(
% 28.92/4.03    ( ! [X59,X60,X58] : (k4_xboole_0(k3_xboole_0(X60,k4_xboole_0(X58,X59)),k2_xboole_0(X58,X59)) = k4_xboole_0(k4_xboole_0(X60,k2_xboole_0(X58,X59)),k4_xboole_0(X60,k2_xboole_0(X59,X58)))) )),
% 28.92/4.03    inference(superposition,[],[f448,f307])).
% 28.92/4.03  fof(f23462,plain,(
% 28.92/4.03    ( ! [X105,X106,X104] : (k4_xboole_0(k2_xboole_0(X104,X105),k2_xboole_0(X106,k2_xboole_0(X104,X105))) = k4_xboole_0(k3_xboole_0(X106,k4_xboole_0(X104,X105)),k2_xboole_0(X104,X105))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f23285,f5484])).
% 28.92/4.03  fof(f5484,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k4_xboole_0(X3,k2_xboole_0(X2,X3))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f452,f5482])).
% 28.92/4.03  fof(f452,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X2,X3),X3)) )),
% 28.92/4.03    inference(backward_demodulation,[],[f101,f443])).
% 28.92/4.03  fof(f101,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k3_xboole_0(k4_xboole_0(X2,X3),X3) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3))) )),
% 28.92/4.03    inference(superposition,[],[f17,f50])).
% 28.92/4.03  fof(f23285,plain,(
% 28.92/4.03    ( ! [X105,X106,X104] : (k4_xboole_0(k3_xboole_0(X106,k4_xboole_0(X104,X105)),k2_xboole_0(X104,X105)) = k4_xboole_0(k4_xboole_0(X106,k2_xboole_0(X104,X105)),k4_xboole_0(X106,k2_xboole_0(X104,X105)))) )),
% 28.92/4.03    inference(superposition,[],[f448,f2384])).
% 28.92/4.03  fof(f2384,plain,(
% 28.92/4.03    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,X0))) )),
% 28.92/4.03    inference(superposition,[],[f310,f14])).
% 28.92/4.03  fof(f310,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f309,f211])).
% 28.92/4.03  fof(f309,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X3,X2),X2) = k2_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f308,f15])).
% 28.92/4.03  fof(f308,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k2_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,k4_xboole_0(X3,X2)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f290,f52])).
% 28.92/4.03  fof(f290,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X3,X2),k3_xboole_0(k2_xboole_0(X2,X3),X2)) = k2_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2))) )),
% 28.92/4.03    inference(superposition,[],[f29,f21])).
% 28.92/4.03  fof(f24914,plain,(
% 28.92/4.03    ( ! [X43,X44,X42] : (k5_xboole_0(k4_xboole_0(X42,X43),k4_xboole_0(X42,k2_xboole_0(X44,X43))) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X42,X43),k2_xboole_0(X44,X43)),k4_xboole_0(k3_xboole_0(X42,X44),X43))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f24913,f3554])).
% 28.92/4.03  fof(f3554,plain,(
% 28.92/4.03    ( ! [X10,X8,X11,X9] : (k4_xboole_0(X8,k2_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X8,X11)))) = k4_xboole_0(k3_xboole_0(X8,X11),k2_xboole_0(X9,X10))) )),
% 28.92/4.03    inference(superposition,[],[f355,f71])).
% 28.92/4.03  fof(f24913,plain,(
% 28.92/4.03    ( ! [X43,X44,X42] : (k5_xboole_0(k4_xboole_0(X42,X43),k4_xboole_0(X42,k2_xboole_0(X44,X43))) = k2_xboole_0(k4_xboole_0(X42,k2_xboole_0(X44,k2_xboole_0(X43,k4_xboole_0(X42,X43)))),k4_xboole_0(k3_xboole_0(X42,X44),X43))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f24912,f71])).
% 28.92/4.03  fof(f24912,plain,(
% 28.92/4.03    ( ! [X43,X44,X42] : (k5_xboole_0(k4_xboole_0(X42,X43),k4_xboole_0(X42,k2_xboole_0(X44,X43))) = k2_xboole_0(k4_xboole_0(X42,k2_xboole_0(k2_xboole_0(X44,X43),k4_xboole_0(X42,X43))),k4_xboole_0(k3_xboole_0(X42,X44),X43))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f24625,f20])).
% 28.92/4.03  fof(f24625,plain,(
% 28.92/4.03    ( ! [X43,X44,X42] : (k5_xboole_0(k4_xboole_0(X42,X43),k4_xboole_0(X42,k2_xboole_0(X44,X43))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X42,k2_xboole_0(X44,X43)),k4_xboole_0(X42,X43)),k4_xboole_0(k3_xboole_0(X42,X44),X43))) )),
% 28.92/4.03    inference(superposition,[],[f34,f1508])).
% 28.92/4.03  fof(f1508,plain,(
% 28.92/4.03    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X2,X1),X0) = k4_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(X2,k2_xboole_0(X1,X0)))) )),
% 28.92/4.03    inference(superposition,[],[f448,f14])).
% 28.92/4.03  fof(f23941,plain,(
% 28.92/4.03    ( ! [X26,X24,X25] : (k2_xboole_0(k4_xboole_0(X25,k2_xboole_0(X24,k2_xboole_0(X26,X25))),k4_xboole_0(k3_xboole_0(X24,X26),X25)) = k5_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(X24,k2_xboole_0(X25,X26)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f23940,f20])).
% 28.92/4.03  fof(f23940,plain,(
% 28.92/4.03    ( ! [X26,X24,X25] : (k5_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(k4_xboole_0(X24,X25),X26)) = k2_xboole_0(k4_xboole_0(X25,k2_xboole_0(X24,k2_xboole_0(X26,X25))),k4_xboole_0(k3_xboole_0(X24,X26),X25))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f23939,f23464])).
% 28.92/4.03  fof(f23939,plain,(
% 28.92/4.03    ( ! [X26,X24,X25] : (k5_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(k4_xboole_0(X24,X25),X26)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X24,X25),k2_xboole_0(X26,X25)),k4_xboole_0(k3_xboole_0(X24,X26),X25))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f23938,f20775])).
% 28.92/4.03  fof(f20775,plain,(
% 28.92/4.03    ( ! [X24,X23,X25,X22] : (k4_xboole_0(k3_xboole_0(X22,X23),k2_xboole_0(X24,X25)) = k4_xboole_0(X22,k2_xboole_0(X25,k2_xboole_0(k4_xboole_0(X22,X23),X24)))) )),
% 28.92/4.03    inference(superposition,[],[f1068,f60])).
% 28.92/4.03  fof(f23938,plain,(
% 28.92/4.03    ( ! [X26,X24,X25] : (k5_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(k4_xboole_0(X24,X25),X26)) = k2_xboole_0(k4_xboole_0(X24,k2_xboole_0(X25,k2_xboole_0(k4_xboole_0(X24,X25),X26))),k4_xboole_0(k3_xboole_0(X24,X26),X25))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f23578,f443])).
% 28.92/4.03  fof(f23578,plain,(
% 28.92/4.03    ( ! [X26,X24,X25] : (k5_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(k4_xboole_0(X24,X25),X26)) = k2_xboole_0(k4_xboole_0(X24,k2_xboole_0(X25,k2_xboole_0(k4_xboole_0(X24,X25),X26))),k3_xboole_0(k4_xboole_0(X24,X25),X26))) )),
% 28.92/4.03    inference(superposition,[],[f1244,f20])).
% 28.92/4.03  fof(f1244,plain,(
% 28.92/4.03    ( ! [X0,X1] : (k5_xboole_0(X1,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X1,X0)),k3_xboole_0(X1,X0))) )),
% 28.92/4.03    inference(superposition,[],[f134,f14])).
% 28.92/4.03  fof(f26656,plain,(
% 28.92/4.03    ( ! [X80,X78,X79] : (k5_xboole_0(k4_xboole_0(X78,X79),k5_xboole_0(k4_xboole_0(X78,X79),k4_xboole_0(X78,k2_xboole_0(X79,X80)))) = k5_xboole_0(k2_xboole_0(X79,X78),k2_xboole_0(X79,k3_xboole_0(X78,X80)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f26655,f2638])).
% 28.92/4.03  fof(f26655,plain,(
% 28.92/4.03    ( ! [X80,X78,X79] : (k5_xboole_0(k4_xboole_0(X78,X79),k5_xboole_0(k4_xboole_0(X78,X79),k4_xboole_0(X78,k2_xboole_0(X79,X80)))) = k5_xboole_0(k4_xboole_0(X78,X79),k4_xboole_0(k3_xboole_0(X78,X80),X79))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f26537,f443])).
% 28.92/4.03  fof(f26537,plain,(
% 28.92/4.03    ( ! [X80,X78,X79] : (k5_xboole_0(k4_xboole_0(X78,X79),k3_xboole_0(k4_xboole_0(X78,X79),X80)) = k5_xboole_0(k4_xboole_0(X78,X79),k5_xboole_0(k4_xboole_0(X78,X79),k4_xboole_0(X78,k2_xboole_0(X79,X80))))) )),
% 28.92/4.03    inference(superposition,[],[f26072,f20])).
% 28.92/4.03  fof(f26072,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k5_xboole_0(X21,k5_xboole_0(X21,k4_xboole_0(X21,X22))) = k5_xboole_0(X21,k3_xboole_0(X21,X22))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f7751,f26035])).
% 28.92/4.03  fof(f26035,plain,(
% 28.92/4.03    ( ! [X61,X62] : (k5_xboole_0(X61,k3_xboole_0(X61,X62)) = k5_xboole_0(k3_xboole_0(X61,X62),k2_xboole_0(X61,k4_xboole_0(X61,X62)))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f11507,f26014])).
% 28.92/4.03  fof(f26014,plain,(
% 28.92/4.03    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X3,X4)) = k2_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f25779,f66])).
% 28.92/4.03  fof(f25779,plain,(
% 28.92/4.03    ( ! [X4,X3] : (k2_xboole_0(X3,k3_xboole_0(X3,X4)) = k2_xboole_0(X3,k4_xboole_0(X3,k2_xboole_0(X4,X3)))) )),
% 28.92/4.03    inference(superposition,[],[f15,f25363])).
% 28.92/4.03  fof(f11507,plain,(
% 28.92/4.03    ( ! [X61,X62] : (k5_xboole_0(k3_xboole_0(X61,X62),k2_xboole_0(X61,k3_xboole_0(X61,X62))) = k5_xboole_0(X61,k3_xboole_0(X61,X62))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f11506,f18])).
% 28.92/4.03  fof(f11506,plain,(
% 28.92/4.03    ( ! [X61,X62] : (k5_xboole_0(k3_xboole_0(X61,X62),k2_xboole_0(X61,k3_xboole_0(X61,X62))) = k2_xboole_0(k4_xboole_0(X61,k3_xboole_0(X61,X62)),k4_xboole_0(k3_xboole_0(X61,X62),X61))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f11505,f100])).
% 28.92/4.03  fof(f11505,plain,(
% 28.92/4.03    ( ! [X61,X62] : (k5_xboole_0(k3_xboole_0(X61,X62),k2_xboole_0(X61,k3_xboole_0(X61,X62))) = k2_xboole_0(k4_xboole_0(X61,k2_xboole_0(k3_xboole_0(X61,X62),k3_xboole_0(X61,X62))),k4_xboole_0(k3_xboole_0(X61,X62),X61))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f11504,f20])).
% 28.92/4.03  fof(f11504,plain,(
% 28.92/4.03    ( ! [X61,X62] : (k5_xboole_0(k3_xboole_0(X61,X62),k2_xboole_0(X61,k3_xboole_0(X61,X62))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X61,k3_xboole_0(X61,X62)),k3_xboole_0(X61,X62)),k4_xboole_0(k3_xboole_0(X61,X62),X61))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f11503,f8042])).
% 28.92/4.03  fof(f8042,plain,(
% 28.92/4.03    ( ! [X4,X3] : (k4_xboole_0(k3_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k2_xboole_0(X3,k3_xboole_0(X3,X4)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f8039,f355])).
% 28.92/4.03  fof(f8039,plain,(
% 28.92/4.03    ( ! [X4,X3] : (k4_xboole_0(X3,k2_xboole_0(X3,k3_xboole_0(X3,X4))) = k4_xboole_0(X3,k2_xboole_0(X3,k4_xboole_0(X3,X4)))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f8015,f8038])).
% 28.92/4.03  fof(f8038,plain,(
% 28.92/4.03    ( ! [X6,X5] : (k2_xboole_0(X5,k4_xboole_0(k3_xboole_0(X5,X5),X6)) = k2_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f7860,f419])).
% 28.92/4.03  fof(f7860,plain,(
% 28.92/4.03    ( ! [X6,X5] : (k2_xboole_0(X5,k4_xboole_0(k3_xboole_0(X5,X5),X6)) = k2_xboole_0(X5,k4_xboole_0(X5,k2_xboole_0(X5,X6)))) )),
% 28.92/4.03    inference(superposition,[],[f419,f5924])).
% 28.92/4.03  fof(f8015,plain,(
% 28.92/4.03    ( ! [X4,X3] : (k4_xboole_0(X3,k2_xboole_0(X3,k4_xboole_0(k3_xboole_0(X3,X3),X4))) = k4_xboole_0(X3,k2_xboole_0(X3,k3_xboole_0(X3,X4)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f8014,f1479])).
% 28.92/4.03  fof(f8014,plain,(
% 28.92/4.03    ( ! [X4,X3] : (k4_xboole_0(X3,k2_xboole_0(X3,k4_xboole_0(k3_xboole_0(X3,X3),X4))) = k4_xboole_0(X3,k2_xboole_0(k3_xboole_0(X3,X4),X3))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f7852,f5505])).
% 28.92/4.03  fof(f5505,plain,(
% 28.92/4.03    ( ! [X10,X8,X9] : (k4_xboole_0(k3_xboole_0(k3_xboole_0(X8,X9),X10),X9) = k4_xboole_0(X9,k2_xboole_0(k3_xboole_0(X8,X10),X9))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f3806,f5484])).
% 28.92/4.03  fof(f3806,plain,(
% 28.92/4.03    ( ! [X10,X8,X9] : (k4_xboole_0(k4_xboole_0(k3_xboole_0(X8,X10),X9),k4_xboole_0(k3_xboole_0(X8,X10),X9)) = k4_xboole_0(k3_xboole_0(k3_xboole_0(X8,X9),X10),X9)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f3805,f3685])).
% 28.92/4.03  fof(f3685,plain,(
% 28.92/4.03    ( ! [X121,X118,X120,X119] : (k4_xboole_0(k3_xboole_0(X118,X121),k2_xboole_0(X119,k4_xboole_0(X118,X120))) = k4_xboole_0(k3_xboole_0(k3_xboole_0(X118,X120),X121),X119)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f3596,f443])).
% 28.92/4.03  fof(f3596,plain,(
% 28.92/4.03    ( ! [X121,X118,X120,X119] : (k4_xboole_0(k3_xboole_0(X118,X121),k2_xboole_0(X119,k4_xboole_0(X118,X120))) = k3_xboole_0(k4_xboole_0(k3_xboole_0(X118,X120),X119),X121)) )),
% 28.92/4.03    inference(superposition,[],[f443,f355])).
% 28.92/4.03  fof(f3805,plain,(
% 28.92/4.03    ( ! [X10,X8,X9] : (k4_xboole_0(k4_xboole_0(k3_xboole_0(X8,X10),X9),k4_xboole_0(k3_xboole_0(X8,X10),X9)) = k4_xboole_0(k3_xboole_0(X8,X10),k2_xboole_0(X9,k4_xboole_0(X8,X9)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f3761,f20])).
% 28.92/4.03  fof(f3761,plain,(
% 28.92/4.03    ( ! [X10,X8,X9] : (k4_xboole_0(k4_xboole_0(k3_xboole_0(X8,X10),X9),k4_xboole_0(k3_xboole_0(X8,X10),X9)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X8,X10),X9),k4_xboole_0(X8,X9))) )),
% 28.92/4.03    inference(superposition,[],[f383,f443])).
% 28.92/4.03  fof(f7852,plain,(
% 28.92/4.03    ( ! [X4,X3] : (k4_xboole_0(k3_xboole_0(k3_xboole_0(X3,X3),X4),X3) = k4_xboole_0(X3,k2_xboole_0(X3,k4_xboole_0(k3_xboole_0(X3,X3),X4)))) )),
% 28.92/4.03    inference(superposition,[],[f5924,f355])).
% 28.92/4.03  fof(f11503,plain,(
% 28.92/4.03    ( ! [X61,X62] : (k5_xboole_0(k3_xboole_0(X61,X62),k2_xboole_0(X61,k3_xboole_0(X61,X62))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X61,k3_xboole_0(X61,X62)),k3_xboole_0(X61,X62)),k4_xboole_0(X61,k2_xboole_0(X61,k3_xboole_0(X61,X62))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f11502,f1479])).
% 28.92/4.03  fof(f11502,plain,(
% 28.92/4.03    ( ! [X61,X62] : (k5_xboole_0(k3_xboole_0(X61,X62),k2_xboole_0(X61,k3_xboole_0(X61,X62))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X61,k3_xboole_0(X61,X62)),k3_xboole_0(X61,X62)),k4_xboole_0(X61,k2_xboole_0(k3_xboole_0(X61,X62),X61)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f11501,f5482])).
% 28.92/4.03  fof(f11501,plain,(
% 28.92/4.03    ( ! [X61,X62] : (k5_xboole_0(k3_xboole_0(X61,X62),k2_xboole_0(X61,k3_xboole_0(X61,X62))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X61,k3_xboole_0(X61,X62)),k3_xboole_0(X61,X62)),k4_xboole_0(k3_xboole_0(k3_xboole_0(X61,X62),X61),X61))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f11429,f353])).
% 28.92/4.03  fof(f11429,plain,(
% 28.92/4.03    ( ! [X61,X62] : (k5_xboole_0(k3_xboole_0(X61,X62),k2_xboole_0(X61,k3_xboole_0(X61,X62))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X61,k3_xboole_0(X61,X62)),k3_xboole_0(X61,X62)),k4_xboole_0(k3_xboole_0(X61,X62),k2_xboole_0(X61,k3_xboole_0(X61,X62))))) )),
% 28.92/4.03    inference(superposition,[],[f112,f311])).
% 28.92/4.03  fof(f311,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k2_xboole_0(X6,k3_xboole_0(X6,X7)) = k2_xboole_0(k3_xboole_0(X6,X7),k4_xboole_0(X6,k3_xboole_0(X6,X7)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f292,f27])).
% 28.92/4.03  fof(f292,plain,(
% 28.92/4.03    ( ! [X6,X7] : (k2_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,k4_xboole_0(X6,X7))) = k2_xboole_0(X6,k3_xboole_0(X6,X7))) )),
% 28.92/4.03    inference(superposition,[],[f29,f17])).
% 28.92/4.03  fof(f112,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k5_xboole_0(X2,k2_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,k2_xboole_0(X2,X3)))) )),
% 28.92/4.03    inference(superposition,[],[f34,f21])).
% 28.92/4.03  fof(f7751,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k5_xboole_0(k3_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))) = k5_xboole_0(X21,k5_xboole_0(X21,k4_xboole_0(X21,X22)))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f5634,f7749])).
% 28.92/4.03  fof(f7749,plain,(
% 28.92/4.03    ( ! [X14,X15] : (k5_xboole_0(X14,k5_xboole_0(X14,X15)) = k5_xboole_0(k4_xboole_0(X14,X14),X15)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f7715,f19])).
% 28.92/4.03  fof(f7715,plain,(
% 28.92/4.03    ( ! [X14,X15] : (k5_xboole_0(k4_xboole_0(X14,X14),X15) = k5_xboole_0(k5_xboole_0(X14,X14),X15)) )),
% 28.92/4.03    inference(superposition,[],[f7516,f34])).
% 28.92/4.03  fof(f5634,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k5_xboole_0(k3_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))) = k5_xboole_0(k4_xboole_0(X21,X21),k4_xboole_0(X21,X22))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f5617,f3655])).
% 28.92/4.03  fof(f3655,plain,(
% 28.92/4.03    ( ! [X4,X2,X3] : (k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X4)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X2,X4),X3),k4_xboole_0(k3_xboole_0(X2,X3),X4))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f3654,f355])).
% 28.92/4.03  fof(f3654,plain,(
% 28.92/4.03    ( ! [X4,X2,X3] : (k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X4)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X2,X4),X3),k4_xboole_0(X2,k2_xboole_0(X4,k4_xboole_0(X2,X3))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f3559,f20])).
% 28.92/4.03  fof(f3559,plain,(
% 28.92/4.03    ( ! [X4,X2,X3] : (k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X4)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X2,X4),X3),k4_xboole_0(k4_xboole_0(X2,X4),k4_xboole_0(X2,X3)))) )),
% 28.92/4.03    inference(superposition,[],[f64,f355])).
% 28.92/4.03  fof(f5617,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k5_xboole_0(k3_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X21,X22),X21),k4_xboole_0(k3_xboole_0(X21,X21),X22))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f5510,f5562])).
% 28.92/4.03  fof(f5510,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k5_xboole_0(k3_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X21,X22),X21),k4_xboole_0(X21,k2_xboole_0(X22,k4_xboole_0(X22,X21))))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f696,f5507])).
% 28.92/4.03  fof(f696,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k5_xboole_0(k3_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X21,X22),X21),k4_xboole_0(X21,k2_xboole_0(X22,k3_xboole_0(X21,X22))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f695,f385])).
% 28.92/4.03  fof(f695,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k5_xboole_0(k3_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))),k4_xboole_0(X21,k2_xboole_0(X22,k3_xboole_0(X21,X22))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f642,f20])).
% 28.92/4.03  fof(f642,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k5_xboole_0(k3_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X21,X22),k2_xboole_0(X21,k4_xboole_0(X21,X22))),k4_xboole_0(k4_xboole_0(X21,X22),k3_xboole_0(X21,X22)))) )),
% 28.92/4.03    inference(superposition,[],[f32,f29])).
% 28.92/4.03  fof(f27322,plain,(
% 28.92/4.03    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(k4_xboole_0(X2,X3),X3)) = k5_xboole_0(k4_xboole_0(X2,X3),k5_xboole_0(k2_xboole_0(X3,X2),k2_xboole_0(X3,k4_xboole_0(X2,X3))))) )),
% 28.92/4.03    inference(superposition,[],[f26072,f2638])).
% 28.92/4.03  fof(f59139,plain,(
% 28.92/4.03    ( ! [X196,X195] : (k5_xboole_0(k2_xboole_0(X195,X196),k3_xboole_0(k2_xboole_0(X195,X196),k4_xboole_0(X196,k2_xboole_0(X195,X196)))) = k5_xboole_0(X196,k5_xboole_0(k2_xboole_0(X196,X195),k2_xboole_0(X196,k4_xboole_0(X196,X195))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f59138,f49830])).
% 28.92/4.03  fof(f49830,plain,(
% 28.92/4.03    ( ! [X6,X8,X7] : (k5_xboole_0(k2_xboole_0(X6,X7),k5_xboole_0(X7,X8)) = k5_xboole_0(X7,k5_xboole_0(k2_xboole_0(X7,X6),X8))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f49705,f19])).
% 28.92/4.03  fof(f49705,plain,(
% 28.92/4.03    ( ! [X6,X8,X7] : (k5_xboole_0(k2_xboole_0(X6,X7),k5_xboole_0(X7,X8)) = k5_xboole_0(k5_xboole_0(X7,k2_xboole_0(X7,X6)),X8)) )),
% 28.92/4.03    inference(superposition,[],[f19,f7547])).
% 28.92/4.03  fof(f7547,plain,(
% 28.92/4.03    ( ! [X8,X7] : (k5_xboole_0(X7,k2_xboole_0(X7,X8)) = k5_xboole_0(k2_xboole_0(X8,X7),X7)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f7546,f6545])).
% 28.92/4.03  fof(f6545,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k2_xboole_0(k4_xboole_0(X21,k2_xboole_0(X22,X21)),k4_xboole_0(k3_xboole_0(X21,X21),X22)) = k5_xboole_0(X22,k2_xboole_0(X22,X21))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f5591,f6544])).
% 28.92/4.03  fof(f6544,plain,(
% 28.92/4.03    ( ! [X26,X27] : (k5_xboole_0(k2_xboole_0(X27,X26),k4_xboole_0(X27,k4_xboole_0(X26,X27))) = k5_xboole_0(X27,k2_xboole_0(X27,X26))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f6481,f211])).
% 28.92/4.03  fof(f6481,plain,(
% 28.92/4.03    ( ! [X26,X27] : (k5_xboole_0(X27,k2_xboole_0(k4_xboole_0(X26,X27),X27)) = k5_xboole_0(k2_xboole_0(X27,X26),k4_xboole_0(X27,k4_xboole_0(X26,X27)))) )),
% 28.92/4.03    inference(superposition,[],[f995,f109])).
% 28.92/4.03  fof(f995,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k5_xboole_0(k5_xboole_0(X21,X22),k4_xboole_0(X22,X21)) = k5_xboole_0(X22,k2_xboole_0(X21,X22))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f994,f692])).
% 28.92/4.03  fof(f692,plain,(
% 28.92/4.03    ( ! [X17,X18] : (k2_xboole_0(k4_xboole_0(X18,k2_xboole_0(X17,k5_xboole_0(X17,X18))),k4_xboole_0(X17,k2_xboole_0(X18,k4_xboole_0(X18,X17)))) = k5_xboole_0(X18,k2_xboole_0(X17,X18))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f691,f130])).
% 28.92/4.03  fof(f691,plain,(
% 28.92/4.03    ( ! [X17,X18] : (k2_xboole_0(k4_xboole_0(X18,k2_xboole_0(X17,k5_xboole_0(X17,X18))),k4_xboole_0(X17,k2_xboole_0(X18,k4_xboole_0(X18,X17)))) = k5_xboole_0(k2_xboole_0(X17,X18),X18)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f690,f336])).
% 28.92/4.03  fof(f690,plain,(
% 28.92/4.03    ( ! [X17,X18] : (k5_xboole_0(k4_xboole_0(X18,X17),k5_xboole_0(X17,X18)) = k2_xboole_0(k4_xboole_0(X18,k2_xboole_0(X17,k5_xboole_0(X17,X18))),k4_xboole_0(X17,k2_xboole_0(X18,k4_xboole_0(X18,X17))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f689,f20])).
% 28.92/4.03  fof(f689,plain,(
% 28.92/4.03    ( ! [X17,X18] : (k5_xboole_0(k4_xboole_0(X18,X17),k5_xboole_0(X17,X18)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X18,X17),k5_xboole_0(X17,X18)),k4_xboole_0(X17,k2_xboole_0(X18,k4_xboole_0(X18,X17))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f640,f20])).
% 28.92/4.03  fof(f640,plain,(
% 28.92/4.03    ( ! [X17,X18] : (k5_xboole_0(k4_xboole_0(X18,X17),k5_xboole_0(X17,X18)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X18,X17),k5_xboole_0(X17,X18)),k4_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X18,X17)))) )),
% 28.92/4.03    inference(superposition,[],[f32,f18])).
% 28.92/4.03  fof(f994,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k5_xboole_0(k5_xboole_0(X21,X22),k4_xboole_0(X22,X21)) = k2_xboole_0(k4_xboole_0(X22,k2_xboole_0(X21,k5_xboole_0(X21,X22))),k4_xboole_0(X21,k2_xboole_0(X22,k4_xboole_0(X22,X21))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f933,f20])).
% 28.92/4.03  fof(f933,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k5_xboole_0(k5_xboole_0(X21,X22),k4_xboole_0(X22,X21)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X22,X21),k5_xboole_0(X21,X22)),k4_xboole_0(X21,k2_xboole_0(X22,k4_xboole_0(X22,X21))))) )),
% 28.92/4.03    inference(superposition,[],[f34,f41])).
% 28.92/4.03  fof(f5591,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k5_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(X22,k4_xboole_0(X21,X22))) = k2_xboole_0(k4_xboole_0(X21,k2_xboole_0(X22,X21)),k4_xboole_0(k3_xboole_0(X21,X21),X22))) )),
% 28.92/4.03    inference(backward_demodulation,[],[f1323,f5562])).
% 28.92/4.03  fof(f1323,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k2_xboole_0(k4_xboole_0(X21,k2_xboole_0(X22,X21)),k4_xboole_0(X21,k2_xboole_0(X22,k4_xboole_0(X22,X21)))) = k5_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(X22,k4_xboole_0(X21,X22)))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f1322,f23])).
% 28.92/4.03  fof(f1322,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k5_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(X21,X22))) = k2_xboole_0(k4_xboole_0(X21,k2_xboole_0(X22,X21)),k4_xboole_0(X21,k2_xboole_0(X22,k4_xboole_0(X22,X21))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f1321,f69])).
% 28.92/4.03  fof(f1321,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k5_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(X21,X22))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X22,X21),k2_xboole_0(X22,X21)),k4_xboole_0(X21,k2_xboole_0(X22,k4_xboole_0(X22,X21))))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f1254,f951])).
% 28.92/4.03  fof(f1254,plain,(
% 28.92/4.03    ( ! [X21,X22] : (k5_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(X21,X22))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X22,X21),k2_xboole_0(X22,X21)),k3_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(X21,X22)))) )),
% 28.92/4.03    inference(superposition,[],[f134,f82])).
% 28.92/4.03  fof(f7546,plain,(
% 28.92/4.03    ( ! [X8,X7] : (k5_xboole_0(k2_xboole_0(X8,X7),X7) = k2_xboole_0(k4_xboole_0(X8,k2_xboole_0(X7,X8)),k4_xboole_0(k3_xboole_0(X8,X8),X7))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f7545,f5482])).
% 28.92/4.03  fof(f7545,plain,(
% 28.92/4.03    ( ! [X8,X7] : (k5_xboole_0(k2_xboole_0(X8,X7),X7) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X7,X8),X8),k4_xboole_0(k3_xboole_0(X8,X8),X7))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f7544,f515])).
% 28.92/4.03  fof(f7544,plain,(
% 28.92/4.03    ( ! [X8,X7] : (k5_xboole_0(k2_xboole_0(X8,X7),X7) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X7,X8),X8),k4_xboole_0(k3_xboole_0(k2_xboole_0(X8,X7),X8),X7))) )),
% 28.92/4.03    inference(forward_demodulation,[],[f7419,f1593])).
% 28.92/4.03  fof(f1593,plain,(
% 28.92/4.03    ( ! [X14,X15,X13] : (k4_xboole_0(k3_xboole_0(X15,k2_xboole_0(X14,X13)),X13) = k4_xboole_0(k3_xboole_0(X15,X14),X13)) )),
% 28.92/4.03    inference(forward_demodulation,[],[f1512,f1508])).
% 28.92/4.03  fof(f1512,plain,(
% 28.92/4.03    ( ! [X14,X15,X13] : (k4_xboole_0(k3_xboole_0(X15,k2_xboole_0(X14,X13)),X13) = k4_xboole_0(k4_xboole_0(X15,X13),k4_xboole_0(X15,k2_xboole_0(X14,X13)))) )),
% 28.92/4.03    inference(superposition,[],[f448,f160])).
% 28.92/4.04  fof(f7419,plain,(
% 28.92/4.04    ( ! [X8,X7] : (k5_xboole_0(k2_xboole_0(X8,X7),X7) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X7,X8),X8),k4_xboole_0(k3_xboole_0(k2_xboole_0(X8,X7),k2_xboole_0(X8,X7)),X7))) )),
% 28.92/4.04    inference(superposition,[],[f5579,f353])).
% 28.92/4.04  fof(f59138,plain,(
% 28.92/4.04    ( ! [X196,X195] : (k5_xboole_0(k2_xboole_0(X195,X196),k3_xboole_0(k2_xboole_0(X195,X196),k4_xboole_0(X196,k2_xboole_0(X195,X196)))) = k5_xboole_0(k2_xboole_0(X195,X196),k5_xboole_0(X196,k2_xboole_0(X196,k4_xboole_0(X196,X195))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f58451,f59034])).
% 28.92/4.04  fof(f59034,plain,(
% 28.92/4.04    ( ! [X140,X139] : (k5_xboole_0(k2_xboole_0(X139,X140),k3_xboole_0(k2_xboole_0(X140,X139),k2_xboole_0(X139,X140))) = k5_xboole_0(X140,k2_xboole_0(X140,k4_xboole_0(X140,X139)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f59033,f43400])).
% 28.92/4.04  fof(f43400,plain,(
% 28.92/4.04    ( ! [X52,X53] : (k5_xboole_0(X53,k3_xboole_0(X53,k2_xboole_0(X52,X53))) = k5_xboole_0(X53,k2_xboole_0(X53,k4_xboole_0(X53,X52)))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f37749,f43399])).
% 28.92/4.04  fof(f43399,plain,(
% 28.92/4.04    ( ! [X56,X55] : (k5_xboole_0(k5_xboole_0(X55,k2_xboole_0(X56,X55)),k4_xboole_0(X56,X55)) = k5_xboole_0(X55,k2_xboole_0(X55,k4_xboole_0(X55,X56)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f43398,f25384])).
% 28.92/4.04  fof(f25384,plain,(
% 28.92/4.04    ( ! [X57,X58] : (k5_xboole_0(X58,k2_xboole_0(X58,k4_xboole_0(X58,X57))) = k2_xboole_0(k4_xboole_0(X57,k2_xboole_0(X58,X57)),k4_xboole_0(X58,k2_xboole_0(X57,X58)))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f10425,f25363])).
% 28.92/4.04  fof(f10425,plain,(
% 28.92/4.04    ( ! [X57,X58] : (k5_xboole_0(X58,k2_xboole_0(X58,k4_xboole_0(X58,X57))) = k2_xboole_0(k4_xboole_0(X57,k2_xboole_0(X58,X57)),k4_xboole_0(k3_xboole_0(X58,X57),X58))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f10424,f355])).
% 28.92/4.04  fof(f10424,plain,(
% 28.92/4.04    ( ! [X57,X58] : (k5_xboole_0(X58,k2_xboole_0(X58,k4_xboole_0(X58,X57))) = k2_xboole_0(k4_xboole_0(X57,k2_xboole_0(X58,X57)),k4_xboole_0(X58,k2_xboole_0(X58,k4_xboole_0(X58,X57))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f10423,f5731])).
% 28.92/4.04  fof(f10423,plain,(
% 28.92/4.04    ( ! [X57,X58] : (k5_xboole_0(X58,k2_xboole_0(X58,k3_xboole_0(X57,X58))) = k2_xboole_0(k4_xboole_0(X57,k2_xboole_0(X58,X57)),k4_xboole_0(X58,k2_xboole_0(X58,k3_xboole_0(X57,X58))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f10422,f14])).
% 28.92/4.04  fof(f10422,plain,(
% 28.92/4.04    ( ! [X57,X58] : (k2_xboole_0(k4_xboole_0(X57,k2_xboole_0(X58,X57)),k4_xboole_0(X58,k2_xboole_0(X58,k3_xboole_0(X57,X58)))) = k5_xboole_0(X58,k2_xboole_0(k3_xboole_0(X57,X58),X58))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f10211,f1479])).
% 28.92/4.04  fof(f10211,plain,(
% 28.92/4.04    ( ! [X57,X58] : (k5_xboole_0(X58,k2_xboole_0(k3_xboole_0(X57,X58),X58)) = k2_xboole_0(k4_xboole_0(X57,k2_xboole_0(X58,X57)),k4_xboole_0(X58,k2_xboole_0(k3_xboole_0(X57,X58),X58)))) )),
% 28.92/4.04    inference(superposition,[],[f111,f353])).
% 28.92/4.04  fof(f43398,plain,(
% 28.92/4.04    ( ! [X56,X55] : (k5_xboole_0(k5_xboole_0(X55,k2_xboole_0(X56,X55)),k4_xboole_0(X56,X55)) = k2_xboole_0(k4_xboole_0(X56,k2_xboole_0(X55,X56)),k4_xboole_0(X55,k2_xboole_0(X56,X55)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f43397,f17763])).
% 28.92/4.04  fof(f17763,plain,(
% 28.92/4.04    ( ! [X64,X65] : (k4_xboole_0(X65,k2_xboole_0(X64,X65)) = k4_xboole_0(X65,k2_xboole_0(X64,k5_xboole_0(X64,k2_xboole_0(X65,X64))))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f8409,f17762])).
% 28.92/4.04  fof(f17762,plain,(
% 28.92/4.04    ( ! [X123,X122] : (k4_xboole_0(X123,k2_xboole_0(X122,X123)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X123,X123),X122),k5_xboole_0(X122,k2_xboole_0(X123,X122)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f17761,f1589])).
% 28.92/4.04  fof(f17761,plain,(
% 28.92/4.04    ( ! [X123,X122] : (k4_xboole_0(X123,k2_xboole_0(X122,X123)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X123,k4_xboole_0(X123,X122)),X122),k5_xboole_0(X122,k2_xboole_0(X123,X122)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f17760,f443])).
% 28.92/4.04  fof(f17760,plain,(
% 28.92/4.04    ( ! [X123,X122] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X123,X122),k4_xboole_0(X123,X122)),k5_xboole_0(X122,k2_xboole_0(X123,X122))) = k4_xboole_0(X123,k2_xboole_0(X122,X123))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f17759,f5925])).
% 28.92/4.04  fof(f17759,plain,(
% 28.92/4.04    ( ! [X123,X122] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X123,X122),k4_xboole_0(X123,X122)),k5_xboole_0(X122,k2_xboole_0(X123,X122))) = k4_xboole_0(k3_xboole_0(X123,X123),k2_xboole_0(X122,X123))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f17758,f608])).
% 28.92/4.04  fof(f608,plain,(
% 28.92/4.04    ( ! [X57,X54,X56,X55] : (k4_xboole_0(k3_xboole_0(k2_xboole_0(X54,X55),X57),k2_xboole_0(X55,X56)) = k4_xboole_0(k3_xboole_0(X54,X57),k2_xboole_0(X55,X56))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f590,f443])).
% 28.92/4.04  fof(f590,plain,(
% 28.92/4.04    ( ! [X57,X54,X56,X55] : (k4_xboole_0(k3_xboole_0(k2_xboole_0(X54,X55),X57),k2_xboole_0(X55,X56)) = k3_xboole_0(k4_xboole_0(X54,k2_xboole_0(X55,X56)),X57)) )),
% 28.92/4.04    inference(superposition,[],[f443,f68])).
% 28.92/4.04  fof(f17758,plain,(
% 28.92/4.04    ( ! [X123,X122] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X123,X122),k4_xboole_0(X123,X122)),k5_xboole_0(X122,k2_xboole_0(X123,X122))) = k4_xboole_0(k3_xboole_0(k2_xboole_0(X123,X122),X123),k2_xboole_0(X122,X123))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f17757,f3512])).
% 28.92/4.04  fof(f17757,plain,(
% 28.92/4.04    ( ! [X123,X122] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X123,X122),k4_xboole_0(X123,X122)),k5_xboole_0(X122,k2_xboole_0(X123,X122))) = k4_xboole_0(k3_xboole_0(k2_xboole_0(X123,X122),k2_xboole_0(X123,X122)),k2_xboole_0(X122,X123))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f17756,f7132])).
% 28.92/4.04  fof(f17756,plain,(
% 28.92/4.04    ( ! [X123,X122] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X123,X122),k4_xboole_0(X123,X122)),k5_xboole_0(X122,k2_xboole_0(X123,X122))) = k4_xboole_0(k5_xboole_0(k2_xboole_0(X122,X123),k2_xboole_0(X123,X122)),k4_xboole_0(X122,k2_xboole_0(X123,X122)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f17240,f336])).
% 28.92/4.04  fof(f17240,plain,(
% 28.92/4.04    ( ! [X123,X122] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X123,X122),k4_xboole_0(X123,X122)),k5_xboole_0(X122,k2_xboole_0(X123,X122))) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X123,X122),k5_xboole_0(X122,k2_xboole_0(X123,X122))),k4_xboole_0(X122,k2_xboole_0(X123,X122)))) )),
% 28.92/4.04    inference(superposition,[],[f5563,f734])).
% 28.92/4.04  fof(f8409,plain,(
% 28.92/4.04    ( ! [X64,X65] : (k4_xboole_0(k4_xboole_0(k3_xboole_0(X65,X65),X64),k5_xboole_0(X64,k2_xboole_0(X65,X64))) = k4_xboole_0(X65,k2_xboole_0(X64,k5_xboole_0(X64,k2_xboole_0(X65,X64))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f8408,f20])).
% 28.92/4.04  fof(f8408,plain,(
% 28.92/4.04    ( ! [X64,X65] : (k4_xboole_0(k4_xboole_0(X65,X64),k5_xboole_0(X64,k2_xboole_0(X65,X64))) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X65,X65),X64),k5_xboole_0(X64,k2_xboole_0(X65,X64)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f8407,f1589])).
% 28.92/4.04  fof(f8407,plain,(
% 28.92/4.04    ( ! [X64,X65] : (k4_xboole_0(k4_xboole_0(X65,X64),k5_xboole_0(X64,k2_xboole_0(X65,X64))) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X65,k4_xboole_0(X65,X64)),X64),k5_xboole_0(X64,k2_xboole_0(X65,X64)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f8295,f443])).
% 28.92/4.04  fof(f8295,plain,(
% 28.92/4.04    ( ! [X64,X65] : (k4_xboole_0(k4_xboole_0(X65,X64),k5_xboole_0(X64,k2_xboole_0(X65,X64))) = k4_xboole_0(k3_xboole_0(k4_xboole_0(X65,X64),k4_xboole_0(X65,X64)),k5_xboole_0(X64,k2_xboole_0(X65,X64)))) )),
% 28.92/4.04    inference(superposition,[],[f5925,f32])).
% 28.92/4.04  fof(f43397,plain,(
% 28.92/4.04    ( ! [X56,X55] : (k5_xboole_0(k5_xboole_0(X55,k2_xboole_0(X56,X55)),k4_xboole_0(X56,X55)) = k2_xboole_0(k4_xboole_0(X56,k2_xboole_0(X55,k5_xboole_0(X55,k2_xboole_0(X56,X55)))),k4_xboole_0(X55,k2_xboole_0(X56,X55)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f43396,f20])).
% 28.92/4.04  fof(f43396,plain,(
% 28.92/4.04    ( ! [X56,X55] : (k5_xboole_0(k5_xboole_0(X55,k2_xboole_0(X56,X55)),k4_xboole_0(X56,X55)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X56,X55),k5_xboole_0(X55,k2_xboole_0(X56,X55))),k4_xboole_0(X55,k2_xboole_0(X56,X55)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f42649,f32545])).
% 28.92/4.04  fof(f32545,plain,(
% 28.92/4.04    ( ! [X10,X11] : (k4_xboole_0(X10,k2_xboole_0(X11,X10)) = k4_xboole_0(k5_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(X11,k3_xboole_0(X11,X10)))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f7944,f32479])).
% 28.92/4.04  fof(f7944,plain,(
% 28.92/4.04    ( ! [X10,X11] : (k4_xboole_0(X10,k2_xboole_0(X11,X10)) = k4_xboole_0(k5_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(k3_xboole_0(X11,X11),X10))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f5600,f7927])).
% 28.92/4.04  fof(f5600,plain,(
% 28.92/4.04    ( ! [X10,X11] : (k4_xboole_0(X10,k2_xboole_0(X11,k5_xboole_0(X10,X11))) = k4_xboole_0(k5_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(k3_xboole_0(X11,X11),X10))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f2305,f5562])).
% 28.92/4.04  fof(f2305,plain,(
% 28.92/4.04    ( ! [X10,X11] : (k4_xboole_0(k5_xboole_0(X10,k2_xboole_0(X11,X10)),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(X10,k2_xboole_0(X11,k5_xboole_0(X10,X11)))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f741,f2303])).
% 28.92/4.04  fof(f42649,plain,(
% 28.92/4.04    ( ! [X56,X55] : (k5_xboole_0(k5_xboole_0(X55,k2_xboole_0(X56,X55)),k4_xboole_0(X56,X55)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X56,X55),k5_xboole_0(X55,k2_xboole_0(X56,X55))),k4_xboole_0(k5_xboole_0(X55,k2_xboole_0(X56,X55)),k4_xboole_0(X56,k3_xboole_0(X56,X55))))) )),
% 28.92/4.04    inference(superposition,[],[f32492,f32488])).
% 28.92/4.04  fof(f32488,plain,(
% 28.92/4.04    ( ! [X30,X29] : (k3_xboole_0(k5_xboole_0(X29,k2_xboole_0(X30,X29)),k4_xboole_0(X30,X29)) = k4_xboole_0(X30,k3_xboole_0(X30,X29))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f5570,f32479])).
% 28.92/4.04  fof(f5570,plain,(
% 28.92/4.04    ( ! [X30,X29] : (k3_xboole_0(k5_xboole_0(X29,k2_xboole_0(X30,X29)),k4_xboole_0(X30,X29)) = k4_xboole_0(k3_xboole_0(X30,X30),X29)) )),
% 28.92/4.04    inference(backward_demodulation,[],[f750,f5562])).
% 28.92/4.04  fof(f750,plain,(
% 28.92/4.04    ( ! [X30,X29] : (k3_xboole_0(k5_xboole_0(X29,k2_xboole_0(X30,X29)),k4_xboole_0(X30,X29)) = k4_xboole_0(X30,k2_xboole_0(X29,k4_xboole_0(X29,X30)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f749,f66])).
% 28.92/4.04  fof(f749,plain,(
% 28.92/4.04    ( ! [X30,X29] : (k3_xboole_0(k5_xboole_0(X29,k2_xboole_0(X30,X29)),k4_xboole_0(X30,X29)) = k4_xboole_0(X30,k2_xboole_0(X29,k4_xboole_0(X29,k2_xboole_0(X30,X29))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f748,f20])).
% 28.92/4.04  fof(f748,plain,(
% 28.92/4.04    ( ! [X30,X29] : (k3_xboole_0(k5_xboole_0(X29,k2_xboole_0(X30,X29)),k4_xboole_0(X30,X29)) = k4_xboole_0(k4_xboole_0(X30,X29),k4_xboole_0(X29,k2_xboole_0(X30,X29)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f747,f25])).
% 28.92/4.04  fof(f747,plain,(
% 28.92/4.04    ( ! [X30,X29] : (k3_xboole_0(k5_xboole_0(X29,k2_xboole_0(X30,X29)),k4_xboole_0(X30,X29)) = k4_xboole_0(k4_xboole_0(X30,X29),k4_xboole_0(X29,k2_xboole_0(X30,k2_xboole_0(X29,X30))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f746,f15])).
% 28.92/4.04  fof(f746,plain,(
% 28.92/4.04    ( ! [X30,X29] : (k3_xboole_0(k5_xboole_0(X29,k2_xboole_0(X30,X29)),k4_xboole_0(X30,X29)) = k4_xboole_0(k4_xboole_0(X30,X29),k4_xboole_0(X29,k2_xboole_0(X30,k2_xboole_0(X29,k4_xboole_0(X30,X29)))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f745,f71])).
% 28.92/4.04  fof(f745,plain,(
% 28.92/4.04    ( ! [X30,X29] : (k3_xboole_0(k5_xboole_0(X29,k2_xboole_0(X30,X29)),k4_xboole_0(X30,X29)) = k4_xboole_0(k4_xboole_0(X30,X29),k4_xboole_0(X29,k2_xboole_0(k2_xboole_0(X30,X29),k4_xboole_0(X30,X29))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f673,f20])).
% 28.92/4.04  fof(f673,plain,(
% 28.92/4.04    ( ! [X30,X29] : (k4_xboole_0(k4_xboole_0(X30,X29),k4_xboole_0(k4_xboole_0(X29,k2_xboole_0(X30,X29)),k4_xboole_0(X30,X29))) = k3_xboole_0(k5_xboole_0(X29,k2_xboole_0(X30,X29)),k4_xboole_0(X30,X29))) )),
% 28.92/4.04    inference(superposition,[],[f193,f32])).
% 28.92/4.04  fof(f32492,plain,(
% 28.92/4.04    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f5579,f32479])).
% 28.92/4.04  fof(f37749,plain,(
% 28.92/4.04    ( ! [X52,X53] : (k5_xboole_0(X53,k3_xboole_0(X53,k2_xboole_0(X52,X53))) = k5_xboole_0(k5_xboole_0(X53,k2_xboole_0(X52,X53)),k4_xboole_0(X52,X53))) )),
% 28.92/4.04    inference(superposition,[],[f34160,f16])).
% 28.92/4.04  fof(f34160,plain,(
% 28.92/4.04    ( ! [X4,X5] : (k5_xboole_0(k5_xboole_0(X4,X5),k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k3_xboole_0(X4,X5))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f34159,f25782])).
% 28.92/4.04  fof(f25782,plain,(
% 28.92/4.04    ( ! [X10,X9] : (k5_xboole_0(X9,k3_xboole_0(X9,X10)) = k2_xboole_0(k4_xboole_0(X9,k3_xboole_0(X9,X10)),k4_xboole_0(X9,k2_xboole_0(X10,X9)))) )),
% 28.92/4.04    inference(superposition,[],[f18,f25363])).
% 28.92/4.04  fof(f34159,plain,(
% 28.92/4.04    ( ! [X4,X5] : (k5_xboole_0(k5_xboole_0(X4,X5),k4_xboole_0(X5,X4)) = k2_xboole_0(k4_xboole_0(X4,k3_xboole_0(X4,X5)),k4_xboole_0(X4,k2_xboole_0(X5,X4)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f33869,f15096])).
% 28.92/4.04  fof(f15096,plain,(
% 28.92/4.04    ( ! [X45,X44] : (k4_xboole_0(X44,k2_xboole_0(X45,X44)) = k4_xboole_0(X45,k2_xboole_0(X44,k5_xboole_0(X44,X45)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f15095,f7930])).
% 28.92/4.04  fof(f7930,plain,(
% 28.92/4.04    ( ! [X8,X7] : (k4_xboole_0(X7,k2_xboole_0(X8,X7)) = k4_xboole_0(k5_xboole_0(X7,X8),k5_xboole_0(X7,X8))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f2207,f7927])).
% 28.92/4.04  fof(f2207,plain,(
% 28.92/4.04    ( ! [X8,X7] : (k4_xboole_0(k5_xboole_0(X7,X8),k5_xboole_0(X7,X8)) = k4_xboole_0(X7,k2_xboole_0(X8,k5_xboole_0(X7,X8)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f2180,f20])).
% 28.92/4.04  fof(f2180,plain,(
% 28.92/4.04    ( ! [X8,X7] : (k4_xboole_0(k4_xboole_0(X7,X8),k5_xboole_0(X7,X8)) = k4_xboole_0(k5_xboole_0(X7,X8),k5_xboole_0(X7,X8))) )),
% 28.92/4.04    inference(superposition,[],[f21,f144])).
% 28.92/4.04  fof(f144,plain,(
% 28.92/4.04    ( ! [X2,X3] : (k5_xboole_0(X3,X2) = k2_xboole_0(k5_xboole_0(X3,X2),k4_xboole_0(X3,X2))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f143,f18])).
% 28.92/4.04  fof(f143,plain,(
% 28.92/4.04    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3)) = k2_xboole_0(k5_xboole_0(X3,X2),k4_xboole_0(X3,X2))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f125,f14])).
% 28.92/4.04  fof(f125,plain,(
% 28.92/4.04    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X3,X2),k5_xboole_0(X3,X2))) )),
% 28.92/4.04    inference(superposition,[],[f25,f34])).
% 28.92/4.04  fof(f15095,plain,(
% 28.92/4.04    ( ! [X45,X44] : (k4_xboole_0(k5_xboole_0(X44,X45),k5_xboole_0(X44,X45)) = k4_xboole_0(X45,k2_xboole_0(X44,k5_xboole_0(X44,X45)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f14973,f1734])).
% 28.92/4.04  fof(f14973,plain,(
% 28.92/4.04    ( ! [X45,X44] : (k4_xboole_0(k5_xboole_0(X44,X45),k5_xboole_0(X44,X45)) = k4_xboole_0(k5_xboole_0(X45,X44),k5_xboole_0(X44,X45))) )),
% 28.92/4.04    inference(superposition,[],[f566,f86])).
% 28.92/4.04  fof(f566,plain,(
% 28.92/4.04    ( ! [X24,X23,X22] : (k4_xboole_0(X24,k5_xboole_0(X23,X22)) = k4_xboole_0(k2_xboole_0(X24,k4_xboole_0(X22,X23)),k5_xboole_0(X23,X22))) )),
% 28.92/4.04    inference(superposition,[],[f68,f34])).
% 28.92/4.04  fof(f33869,plain,(
% 28.92/4.04    ( ! [X4,X5] : (k5_xboole_0(k5_xboole_0(X4,X5),k4_xboole_0(X5,X4)) = k2_xboole_0(k4_xboole_0(X4,k3_xboole_0(X4,X5)),k4_xboole_0(X5,k2_xboole_0(X4,k5_xboole_0(X4,X5))))) )),
% 28.92/4.04    inference(superposition,[],[f63,f32485])).
% 28.92/4.04  fof(f59033,plain,(
% 28.92/4.04    ( ! [X140,X139] : (k5_xboole_0(k2_xboole_0(X139,X140),k3_xboole_0(k2_xboole_0(X140,X139),k2_xboole_0(X139,X140))) = k5_xboole_0(X140,k3_xboole_0(X140,k2_xboole_0(X139,X140)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f59032,f37386])).
% 28.92/4.04  fof(f37386,plain,(
% 28.92/4.04    ( ! [X8,X7] : (k5_xboole_0(X8,k2_xboole_0(X7,X8)) = k5_xboole_0(X7,k3_xboole_0(X7,X8))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f37385,f284])).
% 28.92/4.04  fof(f37385,plain,(
% 28.92/4.04    ( ! [X8,X7] : (k5_xboole_0(X8,k2_xboole_0(X7,X8)) = k5_xboole_0(X7,k3_xboole_0(X7,k2_xboole_0(X8,X8)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f37384,f991])).
% 28.92/4.04  fof(f37384,plain,(
% 28.92/4.04    ( ! [X8,X7] : (k5_xboole_0(X7,k3_xboole_0(X7,k2_xboole_0(X8,X8))) = k5_xboole_0(k4_xboole_0(X8,X7),k5_xboole_0(X8,X7))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f37274,f9438])).
% 28.92/4.04  fof(f9438,plain,(
% 28.92/4.04    ( ! [X28,X29] : (k4_xboole_0(X28,X29) = k4_xboole_0(k2_xboole_0(X28,X28),X29)) )),
% 28.92/4.04    inference(forward_demodulation,[],[f9360,f16])).
% 28.92/4.04  fof(f9360,plain,(
% 28.92/4.04    ( ! [X28,X29] : (k4_xboole_0(k2_xboole_0(X28,X28),X29) = k4_xboole_0(k2_xboole_0(X28,X29),X29)) )),
% 28.92/4.04    inference(superposition,[],[f16,f7758])).
% 28.92/4.04  fof(f37274,plain,(
% 28.92/4.04    ( ! [X8,X7] : (k5_xboole_0(X7,k3_xboole_0(X7,k2_xboole_0(X8,X8))) = k5_xboole_0(k4_xboole_0(k2_xboole_0(X8,X8),X7),k5_xboole_0(X8,X7))) )),
% 28.92/4.04    inference(superposition,[],[f34158,f7527])).
% 28.92/4.04  fof(f34158,plain,(
% 28.92/4.04    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X3,X2),k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f34157,f26088])).
% 28.92/4.04  fof(f26088,plain,(
% 28.92/4.04    ( ! [X8,X7] : (k2_xboole_0(k4_xboole_0(X7,k2_xboole_0(X8,X7)),k4_xboole_0(X7,k3_xboole_0(X7,X8))) = k5_xboole_0(X7,k3_xboole_0(X7,X8))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f25781,f121])).
% 28.92/4.04  fof(f25781,plain,(
% 28.92/4.04    ( ! [X8,X7] : (k5_xboole_0(k3_xboole_0(X7,X8),X7) = k2_xboole_0(k4_xboole_0(X7,k2_xboole_0(X8,X7)),k4_xboole_0(X7,k3_xboole_0(X7,X8)))) )),
% 28.92/4.04    inference(superposition,[],[f18,f25363])).
% 28.92/4.04  fof(f34157,plain,(
% 28.92/4.04    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X3,X2),k5_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,X2)),k4_xboole_0(X2,k3_xboole_0(X2,X3)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f33868,f15096])).
% 28.92/4.04  fof(f33868,plain,(
% 28.92/4.04    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X3,X2),k5_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X2,k5_xboole_0(X2,X3))),k4_xboole_0(X2,k3_xboole_0(X2,X3)))) )),
% 28.92/4.04    inference(superposition,[],[f64,f32485])).
% 28.92/4.04  fof(f59032,plain,(
% 28.92/4.04    ( ! [X140,X139] : (k5_xboole_0(k2_xboole_0(X139,X140),k3_xboole_0(k2_xboole_0(X140,X139),k2_xboole_0(X139,X140))) = k5_xboole_0(k2_xboole_0(X139,X140),k2_xboole_0(X140,k2_xboole_0(X139,X140)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f59031,f16337])).
% 28.92/4.04  fof(f16337,plain,(
% 28.92/4.04    ( ! [X37,X36] : (k5_xboole_0(X37,k2_xboole_0(X36,X37)) = k5_xboole_0(X37,k2_xboole_0(X37,X36))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f16336,f25])).
% 28.92/4.04  fof(f16336,plain,(
% 28.92/4.04    ( ! [X37,X36] : (k5_xboole_0(X37,k2_xboole_0(X36,X37)) = k5_xboole_0(X37,k2_xboole_0(X37,k2_xboole_0(X36,X37)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f16130,f18])).
% 28.92/4.04  fof(f16130,plain,(
% 28.92/4.04    ( ! [X37,X36] : (k5_xboole_0(X37,k2_xboole_0(X37,k2_xboole_0(X36,X37))) = k2_xboole_0(k4_xboole_0(X37,k2_xboole_0(X36,X37)),k4_xboole_0(k2_xboole_0(X36,X37),X37))) )),
% 28.92/4.04    inference(superposition,[],[f714,f500])).
% 28.92/4.04  fof(f500,plain,(
% 28.92/4.04    ( ! [X14,X13] : (k2_xboole_0(X14,X13) = k2_xboole_0(k2_xboole_0(X14,X13),X13)) )),
% 28.92/4.04    inference(forward_demodulation,[],[f493,f170])).
% 28.92/4.04  fof(f170,plain,(
% 28.92/4.04    ( ! [X10,X9] : (k2_xboole_0(X9,X10) = k2_xboole_0(k2_xboole_0(X9,X10),k2_xboole_0(X9,X10))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f169,f53])).
% 28.92/4.04  fof(f169,plain,(
% 28.92/4.04    ( ! [X10,X9] : (k2_xboole_0(X9,k2_xboole_0(X9,X10)) = k2_xboole_0(k2_xboole_0(X9,X10),k2_xboole_0(X9,X10))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f168,f14])).
% 28.92/4.04  fof(f168,plain,(
% 28.92/4.04    ( ! [X10,X9] : (k2_xboole_0(k2_xboole_0(X9,X10),X9) = k2_xboole_0(k2_xboole_0(X9,X10),k2_xboole_0(X9,X10))) )),
% 28.92/4.04    inference(superposition,[],[f25,f53])).
% 28.92/4.04  fof(f493,plain,(
% 28.92/4.04    ( ! [X14,X13] : (k2_xboole_0(k2_xboole_0(X14,X13),X13) = k2_xboole_0(k2_xboole_0(X14,X13),k2_xboole_0(X14,X13))) )),
% 28.92/4.04    inference(superposition,[],[f25,f160])).
% 28.92/4.04  fof(f714,plain,(
% 28.92/4.04    ( ! [X2,X3] : (k5_xboole_0(X3,k2_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X2,X3)),k4_xboole_0(X2,X3))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f713,f25])).
% 28.92/4.04  fof(f713,plain,(
% 28.92/4.04    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X2,X3)),k4_xboole_0(X2,X3)) = k5_xboole_0(X3,k2_xboole_0(X3,k2_xboole_0(X2,X3)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f712,f14])).
% 28.92/4.04  fof(f712,plain,(
% 28.92/4.04    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X2,X3)),k4_xboole_0(X2,X3)) = k5_xboole_0(X3,k2_xboole_0(k2_xboole_0(X2,X3),X3))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f711,f282])).
% 28.92/4.04  fof(f711,plain,(
% 28.92/4.04    ( ! [X2,X3] : (k5_xboole_0(X3,k2_xboole_0(k2_xboole_0(X2,X3),X3)) = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X2,k2_xboole_0(X3,X3))),k4_xboole_0(X2,X3))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f650,f71])).
% 28.92/4.04  fof(f650,plain,(
% 28.92/4.04    ( ! [X2,X3] : (k5_xboole_0(X3,k2_xboole_0(k2_xboole_0(X2,X3),X3)) = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(X2,X3),X3)),k4_xboole_0(X2,X3))) )),
% 28.92/4.04    inference(superposition,[],[f32,f16])).
% 28.92/4.04  fof(f59031,plain,(
% 28.92/4.04    ( ! [X140,X139] : (k5_xboole_0(k2_xboole_0(X139,X140),k3_xboole_0(k2_xboole_0(X140,X139),k2_xboole_0(X139,X140))) = k5_xboole_0(k2_xboole_0(X139,X140),k2_xboole_0(k2_xboole_0(X139,X140),X140))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f59030,f211])).
% 28.92/4.04  fof(f59030,plain,(
% 28.92/4.04    ( ! [X140,X139] : (k5_xboole_0(k2_xboole_0(X139,X140),k2_xboole_0(k4_xboole_0(X140,k2_xboole_0(X139,X140)),k2_xboole_0(X139,X140))) = k5_xboole_0(k2_xboole_0(X139,X140),k3_xboole_0(k2_xboole_0(X140,X139),k2_xboole_0(X139,X140)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f59029,f121])).
% 28.92/4.04  fof(f59029,plain,(
% 28.92/4.04    ( ! [X140,X139] : (k5_xboole_0(k2_xboole_0(X139,X140),k2_xboole_0(k4_xboole_0(X140,k2_xboole_0(X139,X140)),k2_xboole_0(X139,X140))) = k5_xboole_0(k3_xboole_0(k2_xboole_0(X140,X139),k2_xboole_0(X139,X140)),k2_xboole_0(X139,X140))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f58427,f19314])).
% 28.92/4.04  fof(f58427,plain,(
% 28.92/4.04    ( ! [X140,X139] : (k5_xboole_0(k2_xboole_0(X139,X140),k2_xboole_0(k4_xboole_0(X140,k2_xboole_0(X139,X140)),k2_xboole_0(X139,X140))) = k5_xboole_0(k3_xboole_0(k2_xboole_0(X140,X139),k2_xboole_0(X139,X140)),k5_xboole_0(k2_xboole_0(X139,X140),k4_xboole_0(X140,k2_xboole_0(X139,X140))))) )),
% 28.92/4.04    inference(superposition,[],[f991,f250])).
% 28.92/4.04  fof(f250,plain,(
% 28.92/4.04    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X7,X6),k4_xboole_0(X6,k2_xboole_0(X7,X6))) = k3_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X7,X6))) )),
% 28.92/4.04    inference(superposition,[],[f193,f25])).
% 28.92/4.04  fof(f58451,plain,(
% 28.92/4.04    ( ! [X196,X195] : (k5_xboole_0(k2_xboole_0(X195,X196),k3_xboole_0(k2_xboole_0(X195,X196),k4_xboole_0(X196,k2_xboole_0(X195,X196)))) = k5_xboole_0(k2_xboole_0(X195,X196),k5_xboole_0(k2_xboole_0(X195,X196),k3_xboole_0(k2_xboole_0(X196,X195),k2_xboole_0(X195,X196))))) )),
% 28.92/4.04    inference(superposition,[],[f26072,f250])).
% 28.92/4.04  fof(f67737,plain,(
% 28.92/4.04    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK0,k2_xboole_0(sK0,sK1)))),
% 28.92/4.04    inference(backward_demodulation,[],[f55,f67736])).
% 28.92/4.04  fof(f67736,plain,(
% 28.92/4.04    ( ! [X107,X106] : (k5_xboole_0(X106,k2_xboole_0(X106,X107)) = k5_xboole_0(X107,k3_xboole_0(X106,X107))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f67735,f63363])).
% 28.92/4.04  fof(f63363,plain,(
% 28.92/4.04    ( ! [X19,X20] : (k3_xboole_0(X19,X20) = k3_xboole_0(X20,k3_xboole_0(X19,X19))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f63055,f61012])).
% 28.92/4.04  fof(f61012,plain,(
% 28.92/4.04    ( ! [X17,X16] : (k3_xboole_0(X16,X17) = k4_xboole_0(X16,k3_xboole_0(X16,k5_xboole_0(k3_xboole_0(X16,X16),X17)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f60871,f33565])).
% 28.92/4.04  fof(f33565,plain,(
% 28.92/4.04    ( ! [X70,X69] : (k3_xboole_0(X69,X70) = k3_xboole_0(k3_xboole_0(X69,X69),X70)) )),
% 28.92/4.04    inference(forward_demodulation,[],[f33564,f33479])).
% 28.92/4.04  fof(f33479,plain,(
% 28.92/4.04    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k3_xboole_0(X5,k3_xboole_0(X5,X6))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f33478,f8704])).
% 28.92/4.04  fof(f8704,plain,(
% 28.92/4.04    ( ! [X17,X18] : (k3_xboole_0(X17,X18) = k3_xboole_0(k3_xboole_0(X17,X18),X17)) )),
% 28.92/4.04    inference(backward_demodulation,[],[f2748,f8614])).
% 28.92/4.04  fof(f8614,plain,(
% 28.92/4.04    ( ! [X24,X23] : (k3_xboole_0(X23,X24) = k3_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X23,X24))) )),
% 28.92/4.04    inference(superposition,[],[f4152,f6468])).
% 28.92/4.04  fof(f2748,plain,(
% 28.92/4.04    ( ! [X17,X18] : (k3_xboole_0(k3_xboole_0(X17,X18),k3_xboole_0(X17,X18)) = k3_xboole_0(k3_xboole_0(X17,X18),X17)) )),
% 28.92/4.04    inference(forward_demodulation,[],[f2747,f17])).
% 28.92/4.04  fof(f2747,plain,(
% 28.92/4.04    ( ! [X17,X18] : (k3_xboole_0(k3_xboole_0(X17,X18),k3_xboole_0(X17,X18)) = k4_xboole_0(k3_xboole_0(X17,X18),k4_xboole_0(k3_xboole_0(X17,X18),X17))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f2695,f2738])).
% 28.92/4.04  fof(f2738,plain,(
% 28.92/4.04    ( ! [X6,X7] : (k4_xboole_0(k3_xboole_0(X6,X7),X6) = k3_xboole_0(k3_xboole_0(X6,X7),k4_xboole_0(X6,X7))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f2690,f383])).
% 28.92/4.04  fof(f2690,plain,(
% 28.92/4.04    ( ! [X6,X7] : (k4_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X7)) = k3_xboole_0(k3_xboole_0(X6,X7),k4_xboole_0(X6,X7))) )),
% 28.92/4.04    inference(superposition,[],[f17,f97])).
% 28.92/4.04  fof(f2695,plain,(
% 28.92/4.04    ( ! [X17,X18] : (k4_xboole_0(k3_xboole_0(X17,X18),k3_xboole_0(k3_xboole_0(X17,X18),k4_xboole_0(X17,X18))) = k3_xboole_0(k3_xboole_0(X17,X18),k3_xboole_0(X17,X18))) )),
% 28.92/4.04    inference(superposition,[],[f27,f97])).
% 28.92/4.04  fof(f33478,plain,(
% 28.92/4.04    ( ! [X6,X5] : (k3_xboole_0(k3_xboole_0(X5,X6),X5) = k3_xboole_0(X5,k3_xboole_0(X5,X6))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f33477,f17])).
% 28.92/4.04  fof(f33477,plain,(
% 28.92/4.04    ( ! [X6,X5] : (k3_xboole_0(k3_xboole_0(X5,X6),X5) = k4_xboole_0(X5,k4_xboole_0(X5,k3_xboole_0(X5,X6)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f33304,f27])).
% 28.92/4.04  fof(f33304,plain,(
% 28.92/4.04    ( ! [X6,X5] : (k3_xboole_0(k3_xboole_0(X5,X6),X5) = k4_xboole_0(X5,k3_xboole_0(X5,k4_xboole_0(X5,X6)))) )),
% 28.92/4.04    inference(superposition,[],[f32479,f507])).
% 28.92/4.04  fof(f33564,plain,(
% 28.92/4.04    ( ! [X70,X69] : (k3_xboole_0(k3_xboole_0(X69,X69),X70) = k3_xboole_0(X69,k3_xboole_0(X69,X70))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f33563,f17])).
% 28.92/4.04  fof(f33563,plain,(
% 28.92/4.04    ( ! [X70,X69] : (k3_xboole_0(k3_xboole_0(X69,X69),X70) = k4_xboole_0(X69,k4_xboole_0(X69,k3_xboole_0(X69,X70)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f33562,f33479])).
% 28.92/4.04  fof(f33562,plain,(
% 28.92/4.04    ( ! [X70,X69] : (k3_xboole_0(k3_xboole_0(X69,X69),X70) = k4_xboole_0(X69,k4_xboole_0(X69,k3_xboole_0(X69,k3_xboole_0(X69,X70))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f33561,f27])).
% 28.92/4.04  fof(f33561,plain,(
% 28.92/4.04    ( ! [X70,X69] : (k3_xboole_0(k3_xboole_0(X69,X69),X70) = k4_xboole_0(X69,k3_xboole_0(X69,k4_xboole_0(X69,k3_xboole_0(X69,X70))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f33331,f32479])).
% 28.92/4.04  fof(f33331,plain,(
% 28.92/4.04    ( ! [X70,X69] : (k3_xboole_0(k3_xboole_0(X69,X69),X70) = k4_xboole_0(X69,k3_xboole_0(X69,k4_xboole_0(k3_xboole_0(X69,X69),X70)))) )),
% 28.92/4.04    inference(superposition,[],[f32479,f17])).
% 28.92/4.04  fof(f60871,plain,(
% 28.92/4.04    ( ! [X17,X16] : (k4_xboole_0(X16,k3_xboole_0(X16,k5_xboole_0(k3_xboole_0(X16,X16),X17))) = k3_xboole_0(k3_xboole_0(X16,X16),X17)) )),
% 28.92/4.04    inference(superposition,[],[f60514,f32479])).
% 28.92/4.04  fof(f60514,plain,(
% 28.92/4.04    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k4_xboole_0(X2,k5_xboole_0(X2,X3))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f352,f60285])).
% 28.92/4.04  fof(f60285,plain,(
% 28.92/4.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 28.92/4.04    inference(superposition,[],[f59413,f443])).
% 28.92/4.04  fof(f59413,plain,(
% 28.92/4.04    ( ! [X30,X29] : (k3_xboole_0(X29,X30) = k3_xboole_0(k4_xboole_0(X29,k4_xboole_0(X30,X29)),X30)) )),
% 28.92/4.04    inference(backward_demodulation,[],[f8650,f59404])).
% 28.92/4.04  fof(f59404,plain,(
% 28.92/4.04    ( ! [X28,X29] : (k4_xboole_0(X28,k4_xboole_0(X29,X28)) = k3_xboole_0(X28,k2_xboole_0(X29,X28))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f5644,f59348])).
% 28.92/4.04  fof(f59348,plain,(
% 28.92/4.04    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X1)))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f12269,f59343])).
% 28.92/4.04  fof(f59343,plain,(
% 28.92/4.04    ( ! [X6,X7] : (k4_xboole_0(X6,k4_xboole_0(X7,X6)) = k3_xboole_0(X6,k2_xboole_0(X6,X7))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f12272,f59322])).
% 28.92/4.04  fof(f59322,plain,(
% 28.92/4.04    ( ! [X19,X18] : (k4_xboole_0(X18,k4_xboole_0(X19,X18)) = k4_xboole_0(X18,k4_xboole_0(X18,k2_xboole_0(X19,X18)))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f33951,f59314])).
% 28.92/4.04  fof(f59314,plain,(
% 28.92/4.04    ( ! [X17,X18] : (k4_xboole_0(X17,k2_xboole_0(X18,X17)) = k3_xboole_0(X17,k4_xboole_0(X18,X17))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f59308,f31096])).
% 28.92/4.04  fof(f31096,plain,(
% 28.92/4.04    ( ! [X12,X13] : (k4_xboole_0(X12,k2_xboole_0(X13,X12)) = k4_xboole_0(X12,k2_xboole_0(X12,k5_xboole_0(X13,X13)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f30870,f25363])).
% 28.92/4.04  fof(f30870,plain,(
% 28.92/4.04    ( ! [X12,X13] : (k4_xboole_0(k3_xboole_0(X12,X13),X12) = k4_xboole_0(X12,k2_xboole_0(X12,k5_xboole_0(X13,X13)))) )),
% 28.92/4.04    inference(superposition,[],[f355,f13571])).
% 28.92/4.04  fof(f59308,plain,(
% 28.92/4.04    ( ! [X17,X18] : (k3_xboole_0(X17,k4_xboole_0(X18,X17)) = k4_xboole_0(X17,k2_xboole_0(X17,k5_xboole_0(X18,X18)))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f26904,f59285])).
% 28.92/4.04  fof(f59285,plain,(
% 28.92/4.04    ( ! [X12,X11] : (k5_xboole_0(k2_xboole_0(X11,X12),k4_xboole_0(X12,X11)) = k2_xboole_0(X11,k5_xboole_0(X12,X12))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f828,f59284])).
% 28.92/4.04  fof(f59284,plain,(
% 28.92/4.04    ( ! [X59,X60] : (k2_xboole_0(X60,k5_xboole_0(X59,X59)) = k5_xboole_0(k2_xboole_0(X59,X60),k4_xboole_0(X59,X60))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f48900,f59166])).
% 28.92/4.04  fof(f48900,plain,(
% 28.92/4.04    ( ! [X59,X60] : (k5_xboole_0(X60,k5_xboole_0(X60,k2_xboole_0(X60,k5_xboole_0(X59,X59)))) = k5_xboole_0(k2_xboole_0(X59,X60),k4_xboole_0(X59,X60))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f32749,f48898])).
% 28.92/4.04  fof(f48898,plain,(
% 28.92/4.04    ( ! [X116,X115] : (k5_xboole_0(k2_xboole_0(X115,X116),k4_xboole_0(X115,X116)) = k5_xboole_0(k2_xboole_0(X115,X116),k4_xboole_0(X115,k3_xboole_0(X115,X116)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f48897,f47583])).
% 28.92/4.04  fof(f47583,plain,(
% 28.92/4.04    ( ! [X130,X129] : (k5_xboole_0(k2_xboole_0(X130,X129),k4_xboole_0(X130,X129)) = k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(X129,X130))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f47582,f32697])).
% 28.92/4.04  fof(f32697,plain,(
% 28.92/4.04    ( ! [X4,X5] : (k2_xboole_0(X5,X4) = k2_xboole_0(k4_xboole_0(X4,k3_xboole_0(X4,X5)),k4_xboole_0(X5,k4_xboole_0(X4,X5)))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f29410,f32479])).
% 28.92/4.04  fof(f29410,plain,(
% 28.92/4.04    ( ! [X4,X5] : (k2_xboole_0(X5,X4) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X4,X4),X5),k4_xboole_0(X5,k4_xboole_0(X4,X5)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f29409,f211])).
% 28.92/4.04  fof(f29409,plain,(
% 28.92/4.04    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,X5),X5) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X4,X4),X5),k4_xboole_0(X5,k4_xboole_0(X4,X5)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f29408,f137])).
% 28.92/4.04  fof(f29408,plain,(
% 28.92/4.04    ( ! [X4,X5] : (k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X4,X5))) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X4,X4),X5),k4_xboole_0(X5,k4_xboole_0(X4,X5)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f29169,f100])).
% 28.92/4.04  fof(f29169,plain,(
% 28.92/4.04    ( ! [X4,X5] : (k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X4,X5))) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X4,X4),X5),k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5))))) )),
% 28.92/4.04    inference(superposition,[],[f63,f5577])).
% 28.92/4.04  fof(f5577,plain,(
% 28.92/4.04    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X4,k4_xboole_0(X5,X4))) = k4_xboole_0(k3_xboole_0(X5,X5),X4)) )),
% 28.92/4.04    inference(backward_demodulation,[],[f955,f5562])).
% 28.92/4.04  fof(f955,plain,(
% 28.92/4.04    ( ! [X4,X5] : (k4_xboole_0(X5,k2_xboole_0(X4,k4_xboole_0(X4,X5))) = k4_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X4,k4_xboole_0(X5,X4)))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f207,f951])).
% 28.92/4.04  fof(f207,plain,(
% 28.92/4.04    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X4,k4_xboole_0(X5,X4))) = k3_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f206,f92])).
% 28.92/4.04  fof(f206,plain,(
% 28.92/4.04    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X4,k4_xboole_0(X5,X4))) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X4,k4_xboole_0(X5,X4)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f180,f82])).
% 28.92/4.04  fof(f180,plain,(
% 28.92/4.04    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X4,k4_xboole_0(X5,X4))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X5,X4),k2_xboole_0(X4,X5)),k4_xboole_0(X4,k4_xboole_0(X5,X4)))) )),
% 28.92/4.04    inference(superposition,[],[f23,f23])).
% 28.92/4.04  fof(f47582,plain,(
% 28.92/4.04    ( ! [X130,X129] : (k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k4_xboole_0(X129,k4_xboole_0(X130,X129)))) = k5_xboole_0(k2_xboole_0(X130,X129),k4_xboole_0(X130,X129))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f47581,f47480])).
% 28.92/4.04  fof(f47480,plain,(
% 28.92/4.04    ( ! [X24,X25] : (k5_xboole_0(k2_xboole_0(X25,X24),k4_xboole_0(X25,X24)) = k2_xboole_0(k4_xboole_0(X25,k2_xboole_0(X24,X25)),k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X25,X24),k5_xboole_0(X25,X25))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f47479,f32707])).
% 28.92/4.04  fof(f32707,plain,(
% 28.92/4.04    ( ! [X114,X113] : (k5_xboole_0(k2_xboole_0(X113,X114),k4_xboole_0(X113,X114)) = k5_xboole_0(k2_xboole_0(X114,X113),k4_xboole_0(X113,k3_xboole_0(X113,X114)))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f29487,f32479])).
% 28.92/4.04  fof(f29487,plain,(
% 28.92/4.04    ( ! [X114,X113] : (k5_xboole_0(k2_xboole_0(X114,X113),k4_xboole_0(k3_xboole_0(X113,X113),X114)) = k5_xboole_0(k2_xboole_0(X113,X114),k4_xboole_0(X113,X114))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f29486,f21541])).
% 28.92/4.04  fof(f21541,plain,(
% 28.92/4.04    ( ! [X28,X29] : (k5_xboole_0(k4_xboole_0(X29,X28),k2_xboole_0(X28,X29)) = k5_xboole_0(k2_xboole_0(X29,X28),k4_xboole_0(X29,X28))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f21395,f20477])).
% 28.92/4.04  fof(f20477,plain,(
% 28.92/4.04    ( ! [X165,X166,X164] : (k5_xboole_0(k2_xboole_0(X165,X166),X164) = k2_xboole_0(k4_xboole_0(X164,k2_xboole_0(X166,X165)),k5_xboole_0(k2_xboole_0(X165,X166),X164))) )),
% 28.92/4.04    inference(superposition,[],[f165,f1479])).
% 28.92/4.04  fof(f21395,plain,(
% 28.92/4.04    ( ! [X28,X29] : (k5_xboole_0(k4_xboole_0(X29,X28),k2_xboole_0(X28,X29)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X29,X28),k2_xboole_0(X28,X29)),k5_xboole_0(k2_xboole_0(X29,X28),k4_xboole_0(X29,X28)))) )),
% 28.92/4.04    inference(superposition,[],[f1736,f828])).
% 28.92/4.04  fof(f1736,plain,(
% 28.92/4.04    ( ! [X10,X11] : (k5_xboole_0(X11,X10) = k2_xboole_0(k4_xboole_0(X11,X10),k5_xboole_0(X10,X11))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f1695,f166])).
% 28.92/4.04  fof(f166,plain,(
% 28.92/4.04    ( ! [X12,X13] : (k5_xboole_0(X12,X13) = k2_xboole_0(k4_xboole_0(X12,X13),k5_xboole_0(X12,X13))) )),
% 28.92/4.04    inference(superposition,[],[f53,f18])).
% 28.92/4.04  fof(f1695,plain,(
% 28.92/4.04    ( ! [X10,X11] : (k2_xboole_0(k4_xboole_0(X11,X10),k5_xboole_0(X10,X11)) = k2_xboole_0(k4_xboole_0(X11,X10),k5_xboole_0(X11,X10))) )),
% 28.92/4.04    inference(superposition,[],[f25,f86])).
% 28.92/4.04  fof(f29486,plain,(
% 28.92/4.04    ( ! [X114,X113] : (k5_xboole_0(k2_xboole_0(X114,X113),k4_xboole_0(k3_xboole_0(X113,X113),X114)) = k5_xboole_0(k4_xboole_0(X113,X114),k2_xboole_0(X114,X113))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f29485,f211])).
% 28.92/4.04  fof(f29485,plain,(
% 28.92/4.04    ( ! [X114,X113] : (k5_xboole_0(k2_xboole_0(X114,X113),k4_xboole_0(k3_xboole_0(X113,X113),X114)) = k5_xboole_0(k4_xboole_0(X113,X114),k2_xboole_0(k4_xboole_0(X113,X114),X114))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f29484,f211])).
% 28.92/4.04  fof(f29484,plain,(
% 28.92/4.04    ( ! [X114,X113] : (k5_xboole_0(k4_xboole_0(X113,X114),k2_xboole_0(k4_xboole_0(X114,k4_xboole_0(X113,X114)),k4_xboole_0(X113,X114))) = k5_xboole_0(k2_xboole_0(X114,X113),k4_xboole_0(k3_xboole_0(X113,X113),X114))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f29483,f121])).
% 28.92/4.04  fof(f29483,plain,(
% 28.92/4.04    ( ! [X114,X113] : (k5_xboole_0(k4_xboole_0(X113,X114),k2_xboole_0(k4_xboole_0(X114,k4_xboole_0(X113,X114)),k4_xboole_0(X113,X114))) = k5_xboole_0(k4_xboole_0(k3_xboole_0(X113,X113),X114),k2_xboole_0(X114,X113))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f29482,f211])).
% 28.92/4.04  fof(f29482,plain,(
% 28.92/4.04    ( ! [X114,X113] : (k5_xboole_0(k4_xboole_0(X113,X114),k2_xboole_0(k4_xboole_0(X114,k4_xboole_0(X113,X114)),k4_xboole_0(X113,X114))) = k5_xboole_0(k4_xboole_0(k3_xboole_0(X113,X113),X114),k2_xboole_0(k4_xboole_0(X113,X114),X114))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f29210,f109])).
% 28.92/4.04  fof(f29210,plain,(
% 28.92/4.04    ( ! [X114,X113] : (k5_xboole_0(k4_xboole_0(X113,X114),k2_xboole_0(k4_xboole_0(X114,k4_xboole_0(X113,X114)),k4_xboole_0(X113,X114))) = k5_xboole_0(k4_xboole_0(k3_xboole_0(X113,X113),X114),k5_xboole_0(k4_xboole_0(X114,k4_xboole_0(X113,X114)),k4_xboole_0(X113,X114)))) )),
% 28.92/4.04    inference(superposition,[],[f984,f5577])).
% 28.92/4.04  fof(f984,plain,(
% 28.92/4.04    ( ! [X6,X7] : (k5_xboole_0(k4_xboole_0(X7,X6),k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k2_xboole_0(X6,X7))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f983,f692])).
% 28.92/4.04  fof(f983,plain,(
% 28.92/4.04    ( ! [X6,X7] : (k5_xboole_0(k4_xboole_0(X7,X6),k5_xboole_0(X6,X7)) = k2_xboole_0(k4_xboole_0(X7,k2_xboole_0(X6,k5_xboole_0(X6,X7))),k4_xboole_0(X6,k2_xboole_0(X7,k4_xboole_0(X7,X6))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f926,f20])).
% 28.92/4.04  fof(f926,plain,(
% 28.92/4.04    ( ! [X6,X7] : (k5_xboole_0(k4_xboole_0(X7,X6),k5_xboole_0(X6,X7)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X7,X6),k5_xboole_0(X6,X7)),k4_xboole_0(X6,k2_xboole_0(X7,k4_xboole_0(X7,X6))))) )),
% 28.92/4.04    inference(superposition,[],[f18,f41])).
% 28.92/4.04  fof(f47479,plain,(
% 28.92/4.04    ( ! [X24,X25] : (k2_xboole_0(k4_xboole_0(X25,k2_xboole_0(X24,X25)),k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X25,X24),k5_xboole_0(X25,X25)))) = k5_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X25,k3_xboole_0(X25,X24)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f47478,f121])).
% 28.92/4.04  fof(f47478,plain,(
% 28.92/4.04    ( ! [X24,X25] : (k5_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)) = k2_xboole_0(k4_xboole_0(X25,k2_xboole_0(X24,X25)),k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X25,X24),k5_xboole_0(X25,X25))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f47477,f7772])).
% 28.92/4.04  fof(f47477,plain,(
% 28.92/4.04    ( ! [X24,X25] : (k5_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)) = k2_xboole_0(k4_xboole_0(X25,k2_xboole_0(X25,k2_xboole_0(X24,X24))),k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X25,X24),k5_xboole_0(X25,X25))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f47476,f1118])).
% 28.92/4.04  fof(f47476,plain,(
% 28.92/4.04    ( ! [X24,X25] : (k5_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)) = k2_xboole_0(k4_xboole_0(X25,k2_xboole_0(X25,k2_xboole_0(X24,k4_xboole_0(X24,X25)))),k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X25,X24),k5_xboole_0(X25,X25))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f47475,f5731])).
% 28.92/4.04  fof(f47475,plain,(
% 28.92/4.04    ( ! [X24,X25] : (k5_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)) = k2_xboole_0(k4_xboole_0(X25,k2_xboole_0(X25,k2_xboole_0(X24,k3_xboole_0(X25,X24)))),k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X25,X24),k5_xboole_0(X25,X25))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f47474,f12516])).
% 28.92/4.04  fof(f47474,plain,(
% 28.92/4.04    ( ! [X24,X25] : (k5_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)) = k2_xboole_0(k4_xboole_0(X25,k2_xboole_0(X25,k2_xboole_0(k3_xboole_0(X25,X24),X24))),k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X25,X24),k5_xboole_0(X25,X25))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f47473,f1068])).
% 28.92/4.04  fof(f47473,plain,(
% 28.92/4.04    ( ! [X24,X25] : (k5_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)) = k2_xboole_0(k4_xboole_0(X25,k2_xboole_0(k3_xboole_0(X25,X24),k2_xboole_0(X24,X25))),k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X25,X24),k5_xboole_0(X25,X25))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f47472,f20])).
% 28.92/4.04  fof(f47472,plain,(
% 28.92/4.04    ( ! [X24,X25] : (k5_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)),k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X25,X24),k5_xboole_0(X25,X25))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f47471,f12336])).
% 28.92/4.04  fof(f47471,plain,(
% 28.92/4.04    ( ! [X24,X25] : (k5_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)),k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X25,X24),k4_xboole_0(X25,X25))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f47470,f3999])).
% 28.92/4.04  fof(f3999,plain,(
% 28.92/4.04    ( ! [X70,X68,X69] : (k2_xboole_0(k4_xboole_0(X68,X69),k4_xboole_0(X70,k3_xboole_0(X68,X69))) = k2_xboole_0(k4_xboole_0(X68,X69),k4_xboole_0(X70,X68))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f3936,f66])).
% 28.92/4.04  fof(f3936,plain,(
% 28.92/4.04    ( ! [X70,X68,X69] : (k2_xboole_0(k4_xboole_0(X68,X69),k4_xboole_0(X70,k3_xboole_0(X68,X69))) = k2_xboole_0(k4_xboole_0(X68,X69),k4_xboole_0(X70,k2_xboole_0(X68,k4_xboole_0(X68,X69))))) )),
% 28.92/4.04    inference(superposition,[],[f419,f29])).
% 28.92/4.04  fof(f47470,plain,(
% 28.92/4.04    ( ! [X24,X25] : (k5_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)),k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X25,X24),k4_xboole_0(X25,k3_xboole_0(X25,X24)))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f47113,f20])).
% 28.92/4.04  fof(f47113,plain,(
% 28.92/4.04    ( ! [X24,X25] : (k5_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X25,k3_xboole_0(X25,X24)),k2_xboole_0(X24,X25)),k4_xboole_0(k4_xboole_0(X24,k4_xboole_0(X25,X24)),k4_xboole_0(X25,k3_xboole_0(X25,X24))))) )),
% 28.92/4.04    inference(superposition,[],[f32,f32499])).
% 28.92/4.04  fof(f32499,plain,(
% 28.92/4.04    ( ! [X4,X5] : (k2_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,k3_xboole_0(X5,X4)))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f5590,f32479])).
% 28.92/4.04  fof(f5590,plain,(
% 28.92/4.04    ( ! [X4,X5] : (k2_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(k3_xboole_0(X5,X5),X4))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f1238,f5562])).
% 28.92/4.04  fof(f1238,plain,(
% 28.92/4.04    ( ! [X4,X5] : (k2_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,k2_xboole_0(X4,k4_xboole_0(X4,X5))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f1237,f53])).
% 28.92/4.04  fof(f1237,plain,(
% 28.92/4.04    ( ! [X4,X5] : (k2_xboole_0(X4,k2_xboole_0(X4,X5)) = k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,k2_xboole_0(X4,k4_xboole_0(X4,X5))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f1236,f14])).
% 28.92/4.04  fof(f1236,plain,(
% 28.92/4.04    ( ! [X4,X5] : (k2_xboole_0(k2_xboole_0(X4,X5),X4) = k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,k2_xboole_0(X4,k4_xboole_0(X4,X5))))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f953,f1235])).
% 28.92/4.04  fof(f1235,plain,(
% 28.92/4.04    ( ! [X24,X23,X22] : (k2_xboole_0(k2_xboole_0(X23,X22),k4_xboole_0(X24,k4_xboole_0(X22,X23))) = k2_xboole_0(k2_xboole_0(X23,X22),X24)) )),
% 28.92/4.04    inference(forward_demodulation,[],[f1191,f15])).
% 28.92/4.04  fof(f1191,plain,(
% 28.92/4.04    ( ! [X24,X23,X22] : (k2_xboole_0(k2_xboole_0(X23,X22),k4_xboole_0(X24,k4_xboole_0(X22,X23))) = k2_xboole_0(k2_xboole_0(X23,X22),k4_xboole_0(X24,k2_xboole_0(X23,X22)))) )),
% 28.92/4.04    inference(superposition,[],[f66,f82])).
% 28.92/4.04  fof(f953,plain,(
% 28.92/4.04    ( ! [X4,X5] : (k2_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X4,k4_xboole_0(X5,X4))) = k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,k2_xboole_0(X4,k4_xboole_0(X4,X5))))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f291,f951])).
% 28.92/4.04  fof(f291,plain,(
% 28.92/4.04    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,X4)),k3_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4))) = k2_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X4,k4_xboole_0(X5,X4)))) )),
% 28.92/4.04    inference(superposition,[],[f29,f23])).
% 28.92/4.04  fof(f47581,plain,(
% 28.92/4.04    ( ! [X130,X129] : (k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k4_xboole_0(X129,k4_xboole_0(X130,X129)))) = k2_xboole_0(k4_xboole_0(X130,k2_xboole_0(X129,X130)),k4_xboole_0(X129,k2_xboole_0(k4_xboole_0(X130,X129),k5_xboole_0(X130,X130))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f47580,f7772])).
% 28.92/4.04  fof(f47580,plain,(
% 28.92/4.04    ( ! [X130,X129] : (k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k4_xboole_0(X129,k4_xboole_0(X130,X129)))) = k2_xboole_0(k4_xboole_0(X130,k2_xboole_0(X130,k2_xboole_0(X129,X129))),k4_xboole_0(X129,k2_xboole_0(k4_xboole_0(X130,X129),k5_xboole_0(X130,X130))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f47579,f1118])).
% 28.92/4.04  fof(f47579,plain,(
% 28.92/4.04    ( ! [X130,X129] : (k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k4_xboole_0(X129,k4_xboole_0(X130,X129)))) = k2_xboole_0(k4_xboole_0(X130,k2_xboole_0(X130,k2_xboole_0(X129,k4_xboole_0(X129,X130)))),k4_xboole_0(X129,k2_xboole_0(k4_xboole_0(X130,X129),k5_xboole_0(X130,X130))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f47578,f5731])).
% 28.92/4.04  fof(f47578,plain,(
% 28.92/4.04    ( ! [X130,X129] : (k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k4_xboole_0(X129,k4_xboole_0(X130,X129)))) = k2_xboole_0(k4_xboole_0(X130,k2_xboole_0(X130,k2_xboole_0(X129,k3_xboole_0(X130,X129)))),k4_xboole_0(X129,k2_xboole_0(k4_xboole_0(X130,X129),k5_xboole_0(X130,X130))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f47577,f12516])).
% 28.92/4.04  fof(f47577,plain,(
% 28.92/4.04    ( ! [X130,X129] : (k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k4_xboole_0(X129,k4_xboole_0(X130,X129)))) = k2_xboole_0(k4_xboole_0(X130,k2_xboole_0(X130,k2_xboole_0(k3_xboole_0(X130,X129),X129))),k4_xboole_0(X129,k2_xboole_0(k4_xboole_0(X130,X129),k5_xboole_0(X130,X130))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f47576,f1068])).
% 28.92/4.04  fof(f47576,plain,(
% 28.92/4.04    ( ! [X130,X129] : (k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k4_xboole_0(X129,k4_xboole_0(X130,X129)))) = k2_xboole_0(k4_xboole_0(X130,k2_xboole_0(k3_xboole_0(X130,X129),k2_xboole_0(X129,X130))),k4_xboole_0(X129,k2_xboole_0(k4_xboole_0(X130,X129),k5_xboole_0(X130,X130))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f47575,f20])).
% 28.92/4.04  fof(f47575,plain,(
% 28.92/4.04    ( ! [X130,X129] : (k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k4_xboole_0(X129,k4_xboole_0(X130,X129)))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(X129,X130)),k4_xboole_0(X129,k2_xboole_0(k4_xboole_0(X130,X129),k5_xboole_0(X130,X130))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f47574,f12336])).
% 28.92/4.04  fof(f47574,plain,(
% 28.92/4.04    ( ! [X130,X129] : (k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k4_xboole_0(X129,k4_xboole_0(X130,X129)))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(X129,X130)),k4_xboole_0(X129,k2_xboole_0(k4_xboole_0(X130,X129),k4_xboole_0(X130,X130))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f47573,f3999])).
% 28.92/4.04  fof(f47573,plain,(
% 28.92/4.04    ( ! [X130,X129] : (k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k4_xboole_0(X129,k4_xboole_0(X130,X129)))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(X129,X130)),k4_xboole_0(X129,k2_xboole_0(k4_xboole_0(X130,X129),k4_xboole_0(X130,k3_xboole_0(X130,X129)))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f47155,f20])).
% 28.92/4.04  fof(f47155,plain,(
% 28.92/4.04    ( ! [X130,X129] : (k5_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k4_xboole_0(X129,k4_xboole_0(X130,X129)))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X130,k3_xboole_0(X130,X129)),k2_xboole_0(X129,X130)),k4_xboole_0(k4_xboole_0(X129,k4_xboole_0(X130,X129)),k4_xboole_0(X130,k3_xboole_0(X130,X129))))) )),
% 28.92/4.04    inference(superposition,[],[f714,f32499])).
% 28.92/4.04  fof(f48897,plain,(
% 28.92/4.04    ( ! [X116,X115] : (k5_xboole_0(k4_xboole_0(X115,k3_xboole_0(X115,X116)),k2_xboole_0(X116,X115)) = k5_xboole_0(k2_xboole_0(X115,X116),k4_xboole_0(X115,k3_xboole_0(X115,X116)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f48896,f2941])).
% 28.92/4.04  fof(f2941,plain,(
% 28.92/4.04    ( ! [X41,X42] : (k2_xboole_0(X41,X42) = k2_xboole_0(k4_xboole_0(X42,k4_xboole_0(X41,X42)),k2_xboole_0(X41,X42))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f2831,f1163])).
% 28.92/4.04  fof(f2831,plain,(
% 28.92/4.04    ( ! [X41,X42] : (k2_xboole_0(k4_xboole_0(X41,X42),k2_xboole_0(X41,X42)) = k2_xboole_0(k4_xboole_0(X42,k4_xboole_0(X41,X42)),k2_xboole_0(k4_xboole_0(X41,X42),k2_xboole_0(X41,X42)))) )),
% 28.92/4.04    inference(superposition,[],[f82,f171])).
% 28.92/4.04  fof(f48896,plain,(
% 28.92/4.04    ( ! [X116,X115] : (k5_xboole_0(k4_xboole_0(X115,k3_xboole_0(X115,X116)),k2_xboole_0(X116,X115)) = k5_xboole_0(k2_xboole_0(k4_xboole_0(X116,k4_xboole_0(X115,X116)),k2_xboole_0(X115,X116)),k4_xboole_0(X115,k3_xboole_0(X115,X116)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f48895,f2917])).
% 28.92/4.04  fof(f2917,plain,(
% 28.92/4.04    ( ! [X21,X20] : (k2_xboole_0(X21,X20) = k2_xboole_0(k2_xboole_0(X20,X21),k4_xboole_0(X21,k4_xboole_0(X20,X21)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f2916,f1238])).
% 28.92/4.04  fof(f2916,plain,(
% 28.92/4.04    ( ! [X21,X20] : (k2_xboole_0(k2_xboole_0(X20,X21),k4_xboole_0(X21,k4_xboole_0(X20,X21))) = k2_xboole_0(k4_xboole_0(X21,k4_xboole_0(X20,X21)),k4_xboole_0(X20,k2_xboole_0(X21,k4_xboole_0(X21,X20))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f2822,f2912])).
% 28.92/4.04  fof(f2912,plain,(
% 28.92/4.04    ( ! [X17,X16] : (k4_xboole_0(X16,k2_xboole_0(X17,k4_xboole_0(X17,X16))) = k3_xboole_0(k2_xboole_0(X16,X17),k4_xboole_0(X16,X17))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f2911,f955])).
% 28.92/4.04  fof(f2911,plain,(
% 28.92/4.04    ( ! [X17,X16] : (k4_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X17,k4_xboole_0(X16,X17))) = k3_xboole_0(k2_xboole_0(X16,X17),k4_xboole_0(X16,X17))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f2910,f194])).
% 28.92/4.04  fof(f194,plain,(
% 28.92/4.04    ( ! [X0,X1] : (k3_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1)))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f88,f193])).
% 28.92/4.04  fof(f88,plain,(
% 28.92/4.04    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X1),X1)) = k3_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 28.92/4.04    inference(superposition,[],[f27,f16])).
% 28.92/4.04  fof(f2910,plain,(
% 28.92/4.04    ( ! [X17,X16] : (k4_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X17,k4_xboole_0(X16,X17))) = k4_xboole_0(k2_xboole_0(X16,X17),k4_xboole_0(X17,k4_xboole_0(X16,X17)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f2820,f1163])).
% 28.92/4.04  fof(f2820,plain,(
% 28.92/4.04    ( ! [X17,X16] : (k4_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X17,k4_xboole_0(X16,X17))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X16,X17),k2_xboole_0(X16,X17)),k4_xboole_0(X17,k4_xboole_0(X16,X17)))) )),
% 28.92/4.04    inference(superposition,[],[f23,f171])).
% 28.92/4.04  fof(f2822,plain,(
% 28.92/4.04    ( ! [X21,X20] : (k2_xboole_0(k4_xboole_0(X21,k4_xboole_0(X20,X21)),k3_xboole_0(k2_xboole_0(X20,X21),k4_xboole_0(X20,X21))) = k2_xboole_0(k2_xboole_0(X20,X21),k4_xboole_0(X21,k4_xboole_0(X20,X21)))) )),
% 28.92/4.04    inference(superposition,[],[f29,f171])).
% 28.92/4.04  fof(f48895,plain,(
% 28.92/4.04    ( ! [X116,X115] : (k5_xboole_0(k2_xboole_0(k4_xboole_0(X116,k4_xboole_0(X115,X116)),k2_xboole_0(X115,X116)),k4_xboole_0(X115,k3_xboole_0(X115,X116))) = k5_xboole_0(k4_xboole_0(X115,k3_xboole_0(X115,X116)),k2_xboole_0(k2_xboole_0(X115,X116),k4_xboole_0(X116,k4_xboole_0(X115,X116))))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f48230,f121])).
% 28.92/4.04  fof(f48230,plain,(
% 28.92/4.04    ( ! [X116,X115] : (k5_xboole_0(k2_xboole_0(k4_xboole_0(X116,k4_xboole_0(X115,X116)),k2_xboole_0(X115,X116)),k4_xboole_0(X115,k3_xboole_0(X115,X116))) = k5_xboole_0(k2_xboole_0(k2_xboole_0(X115,X116),k4_xboole_0(X116,k4_xboole_0(X115,X116))),k4_xboole_0(X115,k3_xboole_0(X115,X116)))) )),
% 28.92/4.04    inference(superposition,[],[f828,f32507])).
% 28.92/4.04  fof(f32507,plain,(
% 28.92/4.04    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1)))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f5607,f32479])).
% 28.92/4.04  fof(f5607,plain,(
% 28.92/4.04    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(k3_xboole_0(X0,X0),X1)) )),
% 28.92/4.04    inference(backward_demodulation,[],[f2913,f5562])).
% 28.92/4.04  fof(f2913,plain,(
% 28.92/4.04    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X0,X1)))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f194,f2912])).
% 28.92/4.04  fof(f32749,plain,(
% 28.92/4.04    ( ! [X59,X60] : (k5_xboole_0(X60,k5_xboole_0(X60,k2_xboole_0(X60,k5_xboole_0(X59,X59)))) = k5_xboole_0(k2_xboole_0(X59,X60),k4_xboole_0(X59,k3_xboole_0(X59,X60)))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f31196,f32479])).
% 28.92/4.04  fof(f31196,plain,(
% 28.92/4.04    ( ! [X59,X60] : (k5_xboole_0(k2_xboole_0(X59,X60),k4_xboole_0(k3_xboole_0(X59,X59),X60)) = k5_xboole_0(X60,k5_xboole_0(X60,k2_xboole_0(X60,k5_xboole_0(X59,X59))))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f26619,f31115])).
% 28.92/4.04  fof(f31115,plain,(
% 28.92/4.04    ( ! [X15,X16] : (k5_xboole_0(X15,k5_xboole_0(X16,k5_xboole_0(X15,X16))) = k5_xboole_0(X15,k2_xboole_0(X15,k5_xboole_0(X16,X16)))) )),
% 28.92/4.04    inference(backward_demodulation,[],[f7942,f31114])).
% 28.92/4.04  fof(f31114,plain,(
% 28.92/4.04    ( ! [X35,X34] : (k2_xboole_0(k4_xboole_0(X34,k2_xboole_0(X35,X34)),k4_xboole_0(X34,k2_xboole_0(X35,X34))) = k5_xboole_0(X34,k2_xboole_0(X34,k5_xboole_0(X35,X35)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f31113,f31096])).
% 28.92/4.04  fof(f31113,plain,(
% 28.92/4.04    ( ! [X35,X34] : (k5_xboole_0(X34,k2_xboole_0(X34,k5_xboole_0(X35,X35))) = k2_xboole_0(k4_xboole_0(X34,k2_xboole_0(X34,k5_xboole_0(X35,X35))),k4_xboole_0(X34,k2_xboole_0(X35,X34)))) )),
% 28.92/4.04    inference(forward_demodulation,[],[f30879,f20])).
% 28.92/4.04  fof(f30879,plain,(
% 28.92/4.04    ( ! [X35,X34] : (k5_xboole_0(X34,k2_xboole_0(X34,k5_xboole_0(X35,X35))) = k2_xboole_0(k4_xboole_0(X34,k2_xboole_0(X34,k5_xboole_0(X35,X35))),k4_xboole_0(k4_xboole_0(X34,X35),X34))) )),
% 28.92/4.04    inference(superposition,[],[f46,f13571])).
% 29.37/4.04  fof(f7942,plain,(
% 29.37/4.04    ( ! [X15,X16] : (k5_xboole_0(X15,k5_xboole_0(X16,k5_xboole_0(X15,X16))) = k2_xboole_0(k4_xboole_0(X15,k2_xboole_0(X16,X15)),k4_xboole_0(X15,k2_xboole_0(X16,X15)))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f4948,f7927])).
% 29.37/4.04  fof(f4948,plain,(
% 29.37/4.04    ( ! [X15,X16] : (k5_xboole_0(X15,k5_xboole_0(X16,k5_xboole_0(X15,X16))) = k2_xboole_0(k4_xboole_0(X15,k2_xboole_0(X16,k5_xboole_0(X15,X16))),k4_xboole_0(X15,k2_xboole_0(X16,k5_xboole_0(X15,X16))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f4947,f19])).
% 29.37/4.04  fof(f4947,plain,(
% 29.37/4.04    ( ! [X15,X16] : (k5_xboole_0(k5_xboole_0(X15,X16),k5_xboole_0(X15,X16)) = k2_xboole_0(k4_xboole_0(X15,k2_xboole_0(X16,k5_xboole_0(X15,X16))),k4_xboole_0(X15,k2_xboole_0(X16,k5_xboole_0(X15,X16))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f4946,f2207])).
% 29.37/4.04  fof(f4946,plain,(
% 29.37/4.04    ( ! [X15,X16] : (k5_xboole_0(k5_xboole_0(X15,X16),k5_xboole_0(X15,X16)) = k2_xboole_0(k4_xboole_0(k5_xboole_0(X15,X16),k5_xboole_0(X15,X16)),k4_xboole_0(X15,k2_xboole_0(X16,k5_xboole_0(X15,X16))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f4900,f20])).
% 29.37/4.04  fof(f4900,plain,(
% 29.37/4.04    ( ! [X15,X16] : (k5_xboole_0(k5_xboole_0(X15,X16),k5_xboole_0(X15,X16)) = k2_xboole_0(k4_xboole_0(k5_xboole_0(X15,X16),k5_xboole_0(X15,X16)),k4_xboole_0(k4_xboole_0(X15,X16),k5_xboole_0(X15,X16)))) )),
% 29.37/4.04    inference(superposition,[],[f32,f166])).
% 29.37/4.04  fof(f26619,plain,(
% 29.37/4.04    ( ! [X59,X60] : (k5_xboole_0(X60,k5_xboole_0(X60,k5_xboole_0(X59,k5_xboole_0(X60,X59)))) = k5_xboole_0(k2_xboole_0(X59,X60),k4_xboole_0(k3_xboole_0(X59,X59),X60))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f26618,f5606])).
% 29.37/4.04  fof(f5606,plain,(
% 29.37/4.04    ( ! [X17,X16] : (k3_xboole_0(k2_xboole_0(X16,X17),k4_xboole_0(X16,X17)) = k4_xboole_0(k3_xboole_0(X16,X16),X17)) )),
% 29.37/4.04    inference(backward_demodulation,[],[f2912,f5562])).
% 29.37/4.04  fof(f26618,plain,(
% 29.37/4.04    ( ! [X59,X60] : (k5_xboole_0(k2_xboole_0(X59,X60),k3_xboole_0(k2_xboole_0(X59,X60),k4_xboole_0(X59,X60))) = k5_xboole_0(X60,k5_xboole_0(X60,k5_xboole_0(X59,k5_xboole_0(X60,X59))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f26617,f7959])).
% 29.37/4.04  fof(f7959,plain,(
% 29.37/4.04    ( ! [X10,X9] : (k5_xboole_0(k2_xboole_0(X10,X9),k2_xboole_0(X10,X9)) = k5_xboole_0(X9,k5_xboole_0(X10,k5_xboole_0(X9,X10)))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f682,f7942])).
% 29.37/4.04  fof(f682,plain,(
% 29.37/4.04    ( ! [X10,X9] : (k5_xboole_0(k2_xboole_0(X10,X9),k2_xboole_0(X10,X9)) = k2_xboole_0(k4_xboole_0(X9,k2_xboole_0(X10,X9)),k4_xboole_0(X9,k2_xboole_0(X10,X9)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f636,f69])).
% 29.37/4.04  fof(f636,plain,(
% 29.37/4.04    ( ! [X10,X9] : (k5_xboole_0(k2_xboole_0(X10,X9),k2_xboole_0(X10,X9)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X10,X9),k2_xboole_0(X10,X9)),k4_xboole_0(X9,k2_xboole_0(X10,X9)))) )),
% 29.37/4.04    inference(superposition,[],[f32,f160])).
% 29.37/4.04  fof(f26617,plain,(
% 29.37/4.04    ( ! [X59,X60] : (k5_xboole_0(k2_xboole_0(X59,X60),k3_xboole_0(k2_xboole_0(X59,X60),k4_xboole_0(X59,X60))) = k5_xboole_0(X60,k5_xboole_0(k2_xboole_0(X59,X60),k2_xboole_0(X59,X60)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f26616,f147])).
% 29.37/4.04  fof(f147,plain,(
% 29.37/4.04    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X0,X1))) )),
% 29.37/4.04    inference(superposition,[],[f121,f19])).
% 29.37/4.04  fof(f26616,plain,(
% 29.37/4.04    ( ! [X59,X60] : (k5_xboole_0(k2_xboole_0(X59,X60),k3_xboole_0(k2_xboole_0(X59,X60),k4_xboole_0(X59,X60))) = k5_xboole_0(k2_xboole_0(X59,X60),k5_xboole_0(X60,k2_xboole_0(X59,X60)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f26528,f7644])).
% 29.37/4.04  fof(f7644,plain,(
% 29.37/4.04    ( ! [X59,X58] : (k5_xboole_0(k2_xboole_0(X58,X59),k4_xboole_0(X59,k4_xboole_0(X58,X59))) = k5_xboole_0(X59,k2_xboole_0(X58,X59))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f7096,f7643])).
% 29.37/4.04  fof(f7643,plain,(
% 29.37/4.04    ( ! [X10,X11] : (k5_xboole_0(X11,k2_xboole_0(X10,X11)) = k2_xboole_0(k4_xboole_0(X11,k2_xboole_0(X10,X11)),k4_xboole_0(k3_xboole_0(X10,X10),X11))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f7642,f130])).
% 29.37/4.04  fof(f7642,plain,(
% 29.37/4.04    ( ! [X10,X11] : (k5_xboole_0(k2_xboole_0(X10,X11),X11) = k2_xboole_0(k4_xboole_0(X11,k2_xboole_0(X10,X11)),k4_xboole_0(k3_xboole_0(X10,X10),X11))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f7455,f1593])).
% 29.37/4.04  fof(f7455,plain,(
% 29.37/4.04    ( ! [X10,X11] : (k5_xboole_0(k2_xboole_0(X10,X11),X11) = k2_xboole_0(k4_xboole_0(X11,k2_xboole_0(X10,X11)),k4_xboole_0(k3_xboole_0(X10,k2_xboole_0(X10,X11)),X11))) )),
% 29.37/4.04    inference(superposition,[],[f5579,f515])).
% 29.37/4.04  fof(f7096,plain,(
% 29.37/4.04    ( ! [X59,X58] : (k2_xboole_0(k4_xboole_0(X59,k2_xboole_0(X58,X59)),k4_xboole_0(k3_xboole_0(X58,X58),X59)) = k5_xboole_0(k2_xboole_0(X58,X59),k4_xboole_0(X59,k4_xboole_0(X58,X59)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f7095,f171])).
% 29.37/4.04  fof(f7095,plain,(
% 29.37/4.04    ( ! [X59,X58] : (k5_xboole_0(k2_xboole_0(X58,X59),k4_xboole_0(k2_xboole_0(X58,X59),k4_xboole_0(X58,X59))) = k2_xboole_0(k4_xboole_0(X59,k2_xboole_0(X58,X59)),k4_xboole_0(k3_xboole_0(X58,X58),X59))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f7094,f69])).
% 29.37/4.04  fof(f7094,plain,(
% 29.37/4.04    ( ! [X59,X58] : (k5_xboole_0(k2_xboole_0(X58,X59),k4_xboole_0(k2_xboole_0(X58,X59),k4_xboole_0(X58,X59))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X58,X59),k2_xboole_0(X58,X59)),k4_xboole_0(k3_xboole_0(X58,X58),X59))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f6994,f5606])).
% 29.37/4.04  fof(f6994,plain,(
% 29.37/4.04    ( ! [X59,X58] : (k5_xboole_0(k2_xboole_0(X58,X59),k4_xboole_0(k2_xboole_0(X58,X59),k4_xboole_0(X58,X59))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X58,X59),k2_xboole_0(X58,X59)),k3_xboole_0(k2_xboole_0(X58,X59),k4_xboole_0(X58,X59)))) )),
% 29.37/4.04    inference(superposition,[],[f134,f1163])).
% 29.37/4.04  fof(f26528,plain,(
% 29.37/4.04    ( ! [X59,X60] : (k5_xboole_0(k2_xboole_0(X59,X60),k3_xboole_0(k2_xboole_0(X59,X60),k4_xboole_0(X59,X60))) = k5_xboole_0(k2_xboole_0(X59,X60),k5_xboole_0(k2_xboole_0(X59,X60),k4_xboole_0(X60,k4_xboole_0(X59,X60))))) )),
% 29.37/4.04    inference(superposition,[],[f26072,f171])).
% 29.37/4.04  fof(f26904,plain,(
% 29.37/4.04    ( ! [X17,X18] : (k3_xboole_0(X17,k4_xboole_0(X18,X17)) = k4_xboole_0(X17,k5_xboole_0(k2_xboole_0(X17,X18),k4_xboole_0(X18,X17)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f26763,f2900])).
% 29.37/4.04  fof(f26763,plain,(
% 29.37/4.04    ( ! [X17,X18] : (k3_xboole_0(X17,k4_xboole_0(X18,X17)) = k4_xboole_0(X17,k5_xboole_0(k4_xboole_0(X18,X17),k2_xboole_0(X18,X17)))) )),
% 29.37/4.04    inference(superposition,[],[f5513,f2970])).
% 29.37/4.04  fof(f33951,plain,(
% 29.37/4.04    ( ! [X19,X18] : (k4_xboole_0(X18,k4_xboole_0(X19,X18)) = k4_xboole_0(X18,k3_xboole_0(X18,k4_xboole_0(X19,X18)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f33950,f23])).
% 29.37/4.04  fof(f33950,plain,(
% 29.37/4.04    ( ! [X19,X18] : (k4_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(X19,X18)) = k4_xboole_0(X18,k3_xboole_0(X18,k4_xboole_0(X19,X18)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f33949,f100])).
% 29.37/4.04  fof(f33949,plain,(
% 29.37/4.04    ( ! [X19,X18] : (k4_xboole_0(X18,k3_xboole_0(X18,k4_xboole_0(X19,X18))) = k4_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(X19,k2_xboole_0(X18,X18)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f33795,f20])).
% 29.37/4.04  fof(f33795,plain,(
% 29.37/4.04    ( ! [X19,X18] : (k4_xboole_0(X18,k3_xboole_0(X18,k4_xboole_0(X19,X18))) = k4_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(k4_xboole_0(X19,X18),X18))) )),
% 29.37/4.04    inference(superposition,[],[f32485,f137])).
% 29.37/4.04  fof(f12272,plain,(
% 29.37/4.04    ( ! [X6,X7] : (k3_xboole_0(X6,k2_xboole_0(X6,X7)) = k4_xboole_0(X6,k4_xboole_0(X6,k2_xboole_0(X7,X6)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f12165,f3537])).
% 29.37/4.04  fof(f3537,plain,(
% 29.37/4.04    ( ! [X14,X13] : (k4_xboole_0(X13,k2_xboole_0(X14,X13)) = k4_xboole_0(k3_xboole_0(X13,X14),k2_xboole_0(X13,X14))) )),
% 29.37/4.04    inference(superposition,[],[f355,f307])).
% 29.37/4.04  fof(f12165,plain,(
% 29.37/4.04    ( ! [X6,X7] : (k3_xboole_0(X6,k2_xboole_0(X6,X7)) = k4_xboole_0(X6,k4_xboole_0(k3_xboole_0(X6,X7),k2_xboole_0(X6,X7)))) )),
% 29.37/4.04    inference(superposition,[],[f364,f1163])).
% 29.37/4.04  fof(f12269,plain,(
% 29.37/4.04    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X1)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f12162,f5482])).
% 29.37/4.04  fof(f12162,plain,(
% 29.37/4.04    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(k3_xboole_0(X0,X1),X1))) )),
% 29.37/4.04    inference(superposition,[],[f364,f2903])).
% 29.37/4.04  fof(f5644,plain,(
% 29.37/4.04    ( ! [X28,X29] : (k3_xboole_0(X28,k2_xboole_0(X29,X28)) = k4_xboole_0(X28,k4_xboole_0(X29,k2_xboole_0(X28,X29)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f5387,f5482])).
% 29.37/4.04  fof(f5387,plain,(
% 29.37/4.04    ( ! [X28,X29] : (k3_xboole_0(X28,k2_xboole_0(X29,X28)) = k4_xboole_0(X28,k4_xboole_0(k3_xboole_0(X28,X29),X29))) )),
% 29.37/4.04    inference(superposition,[],[f17,f353])).
% 29.37/4.04  fof(f8650,plain,(
% 29.37/4.04    ( ! [X30,X29] : (k3_xboole_0(X29,X30) = k3_xboole_0(k3_xboole_0(X29,k2_xboole_0(X30,X29)),X30)) )),
% 29.37/4.04    inference(backward_demodulation,[],[f5936,f8649])).
% 29.37/4.04  fof(f8649,plain,(
% 29.37/4.04    ( ! [X57,X58] : (k3_xboole_0(X57,X58) = k3_xboole_0(k5_xboole_0(X57,k4_xboole_0(X57,X58)),k3_xboole_0(X57,X58))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f8648,f39])).
% 29.37/4.04  fof(f8648,plain,(
% 29.37/4.04    ( ! [X57,X58] : (k3_xboole_0(X57,X58) = k3_xboole_0(k2_xboole_0(k3_xboole_0(X57,X58),k4_xboole_0(X57,k2_xboole_0(X58,X57))),k3_xboole_0(X57,X58))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f8586,f4152])).
% 29.37/4.04  fof(f8586,plain,(
% 29.37/4.04    ( ! [X57,X58] : (k3_xboole_0(k3_xboole_0(X57,X58),X58) = k3_xboole_0(k2_xboole_0(k3_xboole_0(X57,X58),k4_xboole_0(X57,k2_xboole_0(X58,X57))),k3_xboole_0(k3_xboole_0(X57,X58),X58))) )),
% 29.37/4.04    inference(superposition,[],[f6468,f353])).
% 29.37/4.04  fof(f5936,plain,(
% 29.37/4.04    ( ! [X30,X29] : (k3_xboole_0(k3_xboole_0(X29,k2_xboole_0(X30,X29)),X30) = k3_xboole_0(k5_xboole_0(X29,k4_xboole_0(X29,X30)),k3_xboole_0(X29,X30))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f5929,f507])).
% 29.37/4.04  fof(f5929,plain,(
% 29.37/4.04    ( ! [X30,X29] : (k4_xboole_0(k3_xboole_0(X29,X30),k4_xboole_0(X29,k2_xboole_0(X30,X29))) = k3_xboole_0(k5_xboole_0(X29,k4_xboole_0(X29,X30)),k3_xboole_0(X29,X30))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f3136,f5925])).
% 29.37/4.04  fof(f3136,plain,(
% 29.37/4.04    ( ! [X30,X29] : (k3_xboole_0(k5_xboole_0(X29,k4_xboole_0(X29,X30)),k3_xboole_0(X29,X30)) = k4_xboole_0(k3_xboole_0(X29,X30),k4_xboole_0(k3_xboole_0(X29,X29),k2_xboole_0(X30,X29)))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f1041,f3132])).
% 29.37/4.04  fof(f1041,plain,(
% 29.37/4.04    ( ! [X30,X29] : (k3_xboole_0(k5_xboole_0(X29,k4_xboole_0(X29,X30)),k3_xboole_0(X29,X30)) = k4_xboole_0(k3_xboole_0(X29,X30),k4_xboole_0(X29,k2_xboole_0(X30,k2_xboole_0(X29,k3_xboole_0(X29,X30)))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f1040,f71])).
% 29.37/4.04  fof(f1040,plain,(
% 29.37/4.04    ( ! [X30,X29] : (k3_xboole_0(k5_xboole_0(X29,k4_xboole_0(X29,X30)),k3_xboole_0(X29,X30)) = k4_xboole_0(k3_xboole_0(X29,X30),k4_xboole_0(X29,k2_xboole_0(k2_xboole_0(X30,X29),k3_xboole_0(X29,X30))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f1014,f20])).
% 29.37/4.04  fof(f1014,plain,(
% 29.37/4.04    ( ! [X30,X29] : (k4_xboole_0(k3_xboole_0(X29,X30),k4_xboole_0(k4_xboole_0(X29,k2_xboole_0(X30,X29)),k3_xboole_0(X29,X30))) = k3_xboole_0(k5_xboole_0(X29,k4_xboole_0(X29,X30)),k3_xboole_0(X29,X30))) )),
% 29.37/4.04    inference(superposition,[],[f52,f39])).
% 29.37/4.04  fof(f352,plain,(
% 29.37/4.04    ( ! [X2,X3] : (k4_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = k4_xboole_0(X2,k5_xboole_0(X2,X3))) )),
% 29.37/4.04    inference(superposition,[],[f60,f18])).
% 29.37/4.04  fof(f63055,plain,(
% 29.37/4.04    ( ! [X19,X20] : (k3_xboole_0(X20,k3_xboole_0(X19,X19)) = k4_xboole_0(X19,k3_xboole_0(X19,k5_xboole_0(k3_xboole_0(X19,X19),X20)))) )),
% 29.37/4.04    inference(superposition,[],[f62989,f32479])).
% 29.37/4.04  fof(f62989,plain,(
% 29.37/4.04    ( ! [X17,X16] : (k3_xboole_0(X16,X17) = k4_xboole_0(X17,k5_xboole_0(X17,X16))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f62942,f60569])).
% 29.37/4.04  fof(f60569,plain,(
% 29.37/4.04    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X3,X2))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f15641,f60516])).
% 29.37/4.04  fof(f60516,plain,(
% 29.37/4.04    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k4_xboole_0(X3,k5_xboole_0(X4,X3))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f3301,f60514])).
% 29.37/4.04  fof(f3301,plain,(
% 29.37/4.04    ( ! [X4,X3] : (k4_xboole_0(X3,k5_xboole_0(X4,X3)) = k4_xboole_0(X3,k5_xboole_0(X3,X4))) )),
% 29.37/4.04    inference(superposition,[],[f352,f351])).
% 29.37/4.04  fof(f15641,plain,(
% 29.37/4.04    ( ! [X2,X3] : (k4_xboole_0(X2,k5_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X3,X2))) )),
% 29.37/4.04    inference(superposition,[],[f567,f15])).
% 29.37/4.04  fof(f567,plain,(
% 29.37/4.04    ( ! [X26,X27,X25] : (k4_xboole_0(X27,k5_xboole_0(X25,X26)) = k4_xboole_0(k2_xboole_0(X27,k4_xboole_0(X25,X26)),k5_xboole_0(X25,X26))) )),
% 29.37/4.04    inference(superposition,[],[f68,f18])).
% 29.37/4.04  fof(f62942,plain,(
% 29.37/4.04    ( ! [X17,X16] : (k4_xboole_0(X17,k5_xboole_0(X17,X16)) = k4_xboole_0(k2_xboole_0(X16,X17),k5_xboole_0(X17,X16))) )),
% 29.37/4.04    inference(superposition,[],[f378,f165])).
% 29.37/4.04  fof(f378,plain,(
% 29.37/4.04    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f377,f20])).
% 29.37/4.04  fof(f377,plain,(
% 29.37/4.04    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,X1)),X2)) )),
% 29.37/4.04    inference(forward_demodulation,[],[f343,f193])).
% 29.37/4.04  fof(f343,plain,(
% 29.37/4.04    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),X2) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 29.37/4.04    inference(superposition,[],[f60,f16])).
% 29.37/4.04  fof(f67735,plain,(
% 29.37/4.04    ( ! [X107,X106] : (k5_xboole_0(X106,k2_xboole_0(X106,X107)) = k5_xboole_0(X107,k3_xboole_0(X107,k3_xboole_0(X106,X106)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f67734,f32618])).
% 29.37/4.04  fof(f32618,plain,(
% 29.37/4.04    ( ! [X80,X79] : (k5_xboole_0(X80,k2_xboole_0(X80,X79)) = k5_xboole_0(k4_xboole_0(X80,k3_xboole_0(X80,X79)),k5_xboole_0(X80,X79))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f16430,f32479])).
% 29.37/4.04  fof(f16430,plain,(
% 29.37/4.04    ( ! [X80,X79] : (k5_xboole_0(X80,k2_xboole_0(X80,X79)) = k5_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k5_xboole_0(X80,X79))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f16429,f5584])).
% 29.37/4.04  fof(f5584,plain,(
% 29.37/4.04    ( ! [X33,X32] : (k5_xboole_0(X32,X33) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X32,X32),X33),k4_xboole_0(X33,X32))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f998,f5562])).
% 29.37/4.04  fof(f998,plain,(
% 29.37/4.04    ( ! [X33,X32] : (k5_xboole_0(X32,X33) = k2_xboole_0(k4_xboole_0(X32,k2_xboole_0(X33,k4_xboole_0(X33,X32))),k4_xboole_0(X33,X32))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f938,f165])).
% 29.37/4.04  fof(f938,plain,(
% 29.37/4.04    ( ! [X33,X32] : (k2_xboole_0(k4_xboole_0(X33,X32),k5_xboole_0(X32,X33)) = k2_xboole_0(k4_xboole_0(X32,k2_xboole_0(X33,k4_xboole_0(X33,X32))),k4_xboole_0(X33,X32))) )),
% 29.37/4.04    inference(superposition,[],[f211,f41])).
% 29.37/4.04  fof(f16429,plain,(
% 29.37/4.04    ( ! [X80,X79] : (k5_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k2_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k4_xboole_0(X79,X80))) = k5_xboole_0(X80,k2_xboole_0(X80,X79))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f16428,f6545])).
% 29.37/4.04  fof(f16428,plain,(
% 29.37/4.04    ( ! [X80,X79] : (k5_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k2_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k4_xboole_0(X79,X80))) = k2_xboole_0(k4_xboole_0(X79,k2_xboole_0(X80,X79)),k4_xboole_0(k3_xboole_0(X79,X79),X80))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f16427,f9319])).
% 29.37/4.04  fof(f9319,plain,(
% 29.37/4.04    ( ! [X17,X18] : (k4_xboole_0(X18,k2_xboole_0(X17,X18)) = k4_xboole_0(k3_xboole_0(X17,X17),k2_xboole_0(X18,k5_xboole_0(X17,X18)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f9318,f6137])).
% 29.37/4.04  fof(f6137,plain,(
% 29.37/4.04    ( ! [X2,X1] : (k4_xboole_0(X2,k2_xboole_0(X1,X2)) = k4_xboole_0(X2,k2_xboole_0(k3_xboole_0(X1,X1),X2))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f6136,f5484])).
% 29.37/4.04  fof(f6136,plain,(
% 29.37/4.04    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k2_xboole_0(k3_xboole_0(X1,X1),X2))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f6135,f5506])).
% 29.37/4.04  fof(f5506,plain,(
% 29.37/4.04    ( ! [X50,X48,X49] : (k4_xboole_0(k4_xboole_0(k3_xboole_0(X48,X50),X49),k4_xboole_0(X48,X49)) = k4_xboole_0(X49,k2_xboole_0(k3_xboole_0(X48,X50),X49))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f4217,f5505])).
% 29.37/4.04  fof(f4217,plain,(
% 29.37/4.04    ( ! [X50,X48,X49] : (k4_xboole_0(k4_xboole_0(k3_xboole_0(X48,X50),X49),k4_xboole_0(X48,X49)) = k4_xboole_0(k3_xboole_0(k3_xboole_0(X48,X49),X50),X49)) )),
% 29.37/4.04    inference(forward_demodulation,[],[f4216,f443])).
% 29.37/4.04  fof(f4216,plain,(
% 29.37/4.04    ( ! [X50,X48,X49] : (k4_xboole_0(k4_xboole_0(k3_xboole_0(X48,X50),X49),k4_xboole_0(X48,X49)) = k3_xboole_0(k4_xboole_0(k3_xboole_0(X48,X49),X49),X50)) )),
% 29.37/4.04    inference(forward_demodulation,[],[f4215,f443])).
% 29.37/4.04  fof(f4215,plain,(
% 29.37/4.04    ( ! [X50,X48,X49] : (k3_xboole_0(k3_xboole_0(k4_xboole_0(X48,X49),X49),X50) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X48,X50),X49),k4_xboole_0(X48,X49))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f4145,f443])).
% 29.37/4.04  fof(f4145,plain,(
% 29.37/4.04    ( ! [X50,X48,X49] : (k3_xboole_0(k3_xboole_0(k4_xboole_0(X48,X49),X49),X50) = k4_xboole_0(k3_xboole_0(k4_xboole_0(X48,X49),X50),k4_xboole_0(X48,X49))) )),
% 29.37/4.04    inference(superposition,[],[f507,f50])).
% 29.37/4.04  fof(f6135,plain,(
% 29.37/4.04    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X1,X1),X2),k4_xboole_0(X1,X2))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f6078,f1589])).
% 29.37/4.04  fof(f6078,plain,(
% 29.37/4.04    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X1,k4_xboole_0(X1,X2)),X2),k4_xboole_0(X1,X2))) )),
% 29.37/4.04    inference(superposition,[],[f5896,f443])).
% 29.37/4.04  fof(f9318,plain,(
% 29.37/4.04    ( ! [X17,X18] : (k4_xboole_0(k3_xboole_0(X17,X17),k2_xboole_0(X18,k5_xboole_0(X17,X18))) = k4_xboole_0(X18,k2_xboole_0(k3_xboole_0(X17,X17),X18))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f9317,f5484])).
% 29.37/4.04  fof(f9317,plain,(
% 29.37/4.04    ( ! [X17,X18] : (k4_xboole_0(k4_xboole_0(k3_xboole_0(X17,X17),X18),k4_xboole_0(k3_xboole_0(X17,X17),X18)) = k4_xboole_0(k3_xboole_0(X17,X17),k2_xboole_0(X18,k5_xboole_0(X17,X18)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f9166,f20])).
% 29.37/4.04  fof(f9166,plain,(
% 29.37/4.04    ( ! [X17,X18] : (k4_xboole_0(k4_xboole_0(k3_xboole_0(X17,X17),X18),k4_xboole_0(k3_xboole_0(X17,X17),X18)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X17,X17),X18),k5_xboole_0(X17,X18))) )),
% 29.37/4.04    inference(superposition,[],[f383,f8066])).
% 29.37/4.04  fof(f8066,plain,(
% 29.37/4.04    ( ! [X10,X11] : (k3_xboole_0(k5_xboole_0(X11,X10),k4_xboole_0(X11,X10)) = k4_xboole_0(k3_xboole_0(X11,X11),X10)) )),
% 29.37/4.04    inference(backward_demodulation,[],[f5565,f8047])).
% 29.37/4.04  fof(f8047,plain,(
% 29.37/4.04    ( ! [X12,X13] : (k4_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(k3_xboole_0(X12,X12),X13)) = k4_xboole_0(k3_xboole_0(X13,X13),X12)) )),
% 29.37/4.04    inference(backward_demodulation,[],[f5566,f8046])).
% 29.37/4.04  fof(f8046,plain,(
% 29.37/4.04    ( ! [X10,X11] : (k3_xboole_0(k5_xboole_0(X11,X10),k4_xboole_0(X10,X11)) = k4_xboole_0(k3_xboole_0(X10,X10),X11)) )),
% 29.37/4.04    inference(forward_demodulation,[],[f8040,f5562])).
% 29.37/4.04  fof(f8040,plain,(
% 29.37/4.04    ( ! [X10,X11] : (k4_xboole_0(X10,k2_xboole_0(X11,k4_xboole_0(X11,X10))) = k3_xboole_0(k5_xboole_0(X11,X10),k4_xboole_0(X10,X11))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f5580,f8038])).
% 29.37/4.04  fof(f5580,plain,(
% 29.37/4.04    ( ! [X10,X11] : (k3_xboole_0(k5_xboole_0(X11,X10),k4_xboole_0(X10,X11)) = k4_xboole_0(X10,k2_xboole_0(X11,k4_xboole_0(k3_xboole_0(X11,X11),X10)))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f979,f5562])).
% 29.37/4.04  fof(f979,plain,(
% 29.37/4.04    ( ! [X10,X11] : (k4_xboole_0(X10,k2_xboole_0(X11,k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11))))) = k3_xboole_0(k5_xboole_0(X11,X10),k4_xboole_0(X10,X11))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f201,f924])).
% 29.37/4.04  fof(f924,plain,(
% 29.37/4.04    ( ! [X2,X3] : (k3_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = k4_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X3,X2))))) )),
% 29.37/4.04    inference(superposition,[],[f17,f41])).
% 29.37/4.04  fof(f201,plain,(
% 29.37/4.04    ( ! [X10,X11] : (k4_xboole_0(k5_xboole_0(X11,X10),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(X10,k2_xboole_0(X11,k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11)))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f200,f20])).
% 29.37/4.04  fof(f200,plain,(
% 29.37/4.04    ( ! [X10,X11] : (k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(k5_xboole_0(X11,X10),k4_xboole_0(X11,k2_xboole_0(X10,k4_xboole_0(X10,X11))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f176,f20])).
% 29.37/4.04  fof(f176,plain,(
% 29.37/4.04    ( ! [X10,X11] : (k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(k4_xboole_0(X11,X10),k4_xboole_0(X10,X11))) = k4_xboole_0(k5_xboole_0(X11,X10),k4_xboole_0(k4_xboole_0(X11,X10),k4_xboole_0(X10,X11)))) )),
% 29.37/4.04    inference(superposition,[],[f23,f34])).
% 29.37/4.04  fof(f5566,plain,(
% 29.37/4.04    ( ! [X12,X13] : (k3_xboole_0(k5_xboole_0(X12,X13),k4_xboole_0(X13,X12)) = k4_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(k3_xboole_0(X12,X12),X13))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f256,f5562])).
% 29.37/4.04  fof(f256,plain,(
% 29.37/4.04    ( ! [X12,X13] : (k3_xboole_0(k5_xboole_0(X12,X13),k4_xboole_0(X13,X12)) = k4_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(X12,k2_xboole_0(X13,k4_xboole_0(X13,X12))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f253,f20])).
% 29.37/4.04  fof(f253,plain,(
% 29.37/4.04    ( ! [X12,X13] : (k4_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X13,X12))) = k3_xboole_0(k5_xboole_0(X12,X13),k4_xboole_0(X13,X12))) )),
% 29.37/4.04    inference(superposition,[],[f193,f18])).
% 29.37/4.04  fof(f5565,plain,(
% 29.37/4.04    ( ! [X10,X11] : (k3_xboole_0(k5_xboole_0(X11,X10),k4_xboole_0(X11,X10)) = k4_xboole_0(k4_xboole_0(X11,X10),k4_xboole_0(k3_xboole_0(X10,X10),X11))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f255,f5562])).
% 29.37/4.04  fof(f255,plain,(
% 29.37/4.04    ( ! [X10,X11] : (k3_xboole_0(k5_xboole_0(X11,X10),k4_xboole_0(X11,X10)) = k4_xboole_0(k4_xboole_0(X11,X10),k4_xboole_0(X10,k2_xboole_0(X11,k4_xboole_0(X11,X10))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f252,f20])).
% 29.37/4.04  fof(f252,plain,(
% 29.37/4.04    ( ! [X10,X11] : (k4_xboole_0(k4_xboole_0(X11,X10),k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X11,X10))) = k3_xboole_0(k5_xboole_0(X11,X10),k4_xboole_0(X11,X10))) )),
% 29.37/4.04    inference(superposition,[],[f193,f34])).
% 29.37/4.04  fof(f16427,plain,(
% 29.37/4.04    ( ! [X80,X79] : (k5_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k2_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k4_xboole_0(X79,X80))) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),k2_xboole_0(X79,k5_xboole_0(X80,X79))),k4_xboole_0(k3_xboole_0(X79,X79),X80))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f16426,f20])).
% 29.37/4.04  fof(f16426,plain,(
% 29.37/4.04    ( ! [X80,X79] : (k5_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k2_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k4_xboole_0(X79,X80))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k5_xboole_0(X80,X79)),k4_xboole_0(k3_xboole_0(X79,X79),X80))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f16425,f5562])).
% 29.37/4.04  fof(f16425,plain,(
% 29.37/4.04    ( ! [X80,X79] : (k5_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k2_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k4_xboole_0(X79,X80))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k5_xboole_0(X80,X79)),k4_xboole_0(X79,k2_xboole_0(X80,k4_xboole_0(X80,X79))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f16424,f8038])).
% 29.37/4.04  fof(f16424,plain,(
% 29.37/4.04    ( ! [X80,X79] : (k5_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k2_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k4_xboole_0(X79,X80))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k5_xboole_0(X80,X79)),k4_xboole_0(X79,k2_xboole_0(X80,k4_xboole_0(k3_xboole_0(X80,X80),X79))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f16151,f20])).
% 29.37/4.04  fof(f16151,plain,(
% 29.37/4.04    ( ! [X80,X79] : (k5_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k2_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k4_xboole_0(X79,X80))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(k3_xboole_0(X80,X80),X79),k5_xboole_0(X80,X79)),k4_xboole_0(k4_xboole_0(X79,X80),k4_xboole_0(k3_xboole_0(X80,X80),X79)))) )),
% 29.37/4.04    inference(superposition,[],[f714,f5579])).
% 29.37/4.04  fof(f67734,plain,(
% 29.37/4.04    ( ! [X107,X106] : (k5_xboole_0(X107,k3_xboole_0(X107,k3_xboole_0(X106,X106))) = k5_xboole_0(k4_xboole_0(X106,k3_xboole_0(X106,X107)),k5_xboole_0(X106,X107))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f67626,f32479])).
% 29.37/4.04  fof(f67626,plain,(
% 29.37/4.04    ( ! [X107,X106] : (k5_xboole_0(X107,k3_xboole_0(X107,k3_xboole_0(X106,X106))) = k5_xboole_0(k4_xboole_0(k3_xboole_0(X106,X106),X107),k5_xboole_0(X106,X107))) )),
% 29.37/4.04    inference(superposition,[],[f34190,f66331])).
% 29.37/4.04  fof(f66331,plain,(
% 29.37/4.04    ( ! [X47,X46] : (k5_xboole_0(X46,X47) = k5_xboole_0(k3_xboole_0(X46,X46),X47)) )),
% 29.37/4.04    inference(forward_demodulation,[],[f66303,f32500])).
% 29.37/4.04  fof(f32500,plain,(
% 29.37/4.04    ( ! [X24,X23] : (k5_xboole_0(X23,X24) = k2_xboole_0(k5_xboole_0(X24,X23),k4_xboole_0(X23,k3_xboole_0(X23,X24)))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f5596,f32479])).
% 29.37/4.04  fof(f5596,plain,(
% 29.37/4.04    ( ! [X24,X23] : (k5_xboole_0(X23,X24) = k2_xboole_0(k5_xboole_0(X24,X23),k4_xboole_0(k3_xboole_0(X23,X23),X24))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f2292,f5562])).
% 29.37/4.04  fof(f2292,plain,(
% 29.37/4.04    ( ! [X24,X23] : (k5_xboole_0(X23,X24) = k2_xboole_0(k5_xboole_0(X24,X23),k4_xboole_0(X23,k2_xboole_0(X24,k4_xboole_0(X24,X23))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f2291,f165])).
% 29.37/4.04  fof(f2291,plain,(
% 29.37/4.04    ( ! [X24,X23] : (k2_xboole_0(k4_xboole_0(X24,X23),k5_xboole_0(X23,X24)) = k2_xboole_0(k5_xboole_0(X24,X23),k4_xboole_0(X23,k2_xboole_0(X24,k4_xboole_0(X24,X23))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f2231,f41])).
% 29.37/4.04  fof(f2231,plain,(
% 29.37/4.04    ( ! [X24,X23] : (k2_xboole_0(k4_xboole_0(X24,X23),k5_xboole_0(X23,X24)) = k2_xboole_0(k5_xboole_0(X24,X23),k4_xboole_0(k5_xboole_0(X23,X24),k4_xboole_0(X24,X23)))) )),
% 29.37/4.04    inference(superposition,[],[f307,f86])).
% 29.37/4.04  fof(f66303,plain,(
% 29.37/4.04    ( ! [X47,X46] : (k5_xboole_0(k3_xboole_0(X46,X46),X47) = k2_xboole_0(k5_xboole_0(X47,X46),k4_xboole_0(X46,k3_xboole_0(X46,X47)))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f33356,f66299])).
% 29.37/4.04  fof(f66299,plain,(
% 29.37/4.04    ( ! [X83,X84] : (k5_xboole_0(X83,X84) = k5_xboole_0(X83,k3_xboole_0(X84,X84))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f66298,f64204])).
% 29.37/4.04  fof(f64204,plain,(
% 29.37/4.04    ( ! [X92,X93] : (k5_xboole_0(X92,X93) = k2_xboole_0(k4_xboole_0(X93,k3_xboole_0(X93,X92)),k4_xboole_0(X92,k3_xboole_0(X93,X92)))) )),
% 29.37/4.04    inference(superposition,[],[f32975,f63047])).
% 29.37/4.04  fof(f63047,plain,(
% 29.37/4.04    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4)) )),
% 29.37/4.04    inference(superposition,[],[f62989,f60514])).
% 29.37/4.04  fof(f32975,plain,(
% 29.37/4.04    ( ! [X15,X16] : (k5_xboole_0(X16,X15) = k2_xboole_0(k4_xboole_0(X15,k3_xboole_0(X15,X16)),k4_xboole_0(X16,k3_xboole_0(X16,X15)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f32555,f32479])).
% 29.37/4.04  fof(f32555,plain,(
% 29.37/4.04    ( ! [X15,X16] : (k5_xboole_0(X16,X15) = k2_xboole_0(k4_xboole_0(X15,k3_xboole_0(X15,X16)),k4_xboole_0(k3_xboole_0(X16,X16),X15))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f8052,f32479])).
% 29.37/4.04  fof(f8052,plain,(
% 29.37/4.04    ( ! [X15,X16] : (k5_xboole_0(X16,X15) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X15,X15),X16),k4_xboole_0(k3_xboole_0(X16,X16),X15))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f5599,f8046])).
% 29.37/4.04  fof(f5599,plain,(
% 29.37/4.04    ( ! [X15,X16] : (k5_xboole_0(X16,X15) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X15,X15),X16),k3_xboole_0(k5_xboole_0(X15,X16),k4_xboole_0(X16,X15)))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f2302,f5562])).
% 29.37/4.04  fof(f2302,plain,(
% 29.37/4.04    ( ! [X15,X16] : (k5_xboole_0(X16,X15) = k2_xboole_0(k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(X16,X15))),k3_xboole_0(k5_xboole_0(X15,X16),k4_xboole_0(X16,X15)))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f930,f2301])).
% 29.37/4.04  fof(f930,plain,(
% 29.37/4.04    ( ! [X15,X16] : (k2_xboole_0(k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(X16,X15))),k3_xboole_0(k5_xboole_0(X15,X16),k4_xboole_0(X16,X15))) = k2_xboole_0(k5_xboole_0(X15,X16),k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(X16,X15))))) )),
% 29.37/4.04    inference(superposition,[],[f29,f41])).
% 29.37/4.04  fof(f66298,plain,(
% 29.37/4.04    ( ! [X83,X84] : (k5_xboole_0(X83,k3_xboole_0(X84,X84)) = k2_xboole_0(k4_xboole_0(X84,k3_xboole_0(X84,X83)),k4_xboole_0(X83,k3_xboole_0(X84,X83)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f66203,f32479])).
% 29.37/4.04  fof(f66203,plain,(
% 29.37/4.04    ( ! [X83,X84] : (k5_xboole_0(X83,k3_xboole_0(X84,X84)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X84,X84),X83),k4_xboole_0(X83,k3_xboole_0(X84,X83)))) )),
% 29.37/4.04    inference(superposition,[],[f32492,f63363])).
% 29.37/4.04  fof(f33356,plain,(
% 29.37/4.04    ( ! [X47,X46] : (k5_xboole_0(k3_xboole_0(X46,X46),X47) = k2_xboole_0(k5_xboole_0(X47,k3_xboole_0(X46,X46)),k4_xboole_0(X46,k3_xboole_0(X46,X47)))) )),
% 29.37/4.04    inference(superposition,[],[f86,f32479])).
% 29.37/4.04  fof(f34190,plain,(
% 29.37/4.04    ( ! [X24,X23] : (k5_xboole_0(X23,k3_xboole_0(X23,X24)) = k5_xboole_0(k4_xboole_0(X24,X23),k5_xboole_0(X24,X23))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f34189,f86])).
% 29.37/4.04  fof(f34189,plain,(
% 29.37/4.04    ( ! [X24,X23] : (k5_xboole_0(k4_xboole_0(X24,X23),k2_xboole_0(k5_xboole_0(X23,X24),k4_xboole_0(X24,X23))) = k5_xboole_0(X23,k3_xboole_0(X23,X24))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f34188,f26088])).
% 29.37/4.04  fof(f34188,plain,(
% 29.37/4.04    ( ! [X24,X23] : (k5_xboole_0(k4_xboole_0(X24,X23),k2_xboole_0(k5_xboole_0(X23,X24),k4_xboole_0(X24,X23))) = k2_xboole_0(k4_xboole_0(X23,k2_xboole_0(X24,X23)),k4_xboole_0(X23,k3_xboole_0(X23,X24)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f34187,f28284])).
% 29.37/4.04  fof(f28284,plain,(
% 29.37/4.04    ( ! [X88,X87] : (k4_xboole_0(X87,k2_xboole_0(X88,X87)) = k4_xboole_0(X88,k2_xboole_0(X87,k2_xboole_0(X88,k5_xboole_0(X87,X88))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f28283,f7955])).
% 29.37/4.04  fof(f7955,plain,(
% 29.37/4.04    ( ! [X31,X32] : (k4_xboole_0(X31,k2_xboole_0(X32,X31)) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X31,X31),X32),k5_xboole_0(X31,X32))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f6363,f7927])).
% 29.37/4.04  fof(f6363,plain,(
% 29.37/4.04    ( ! [X31,X32] : (k4_xboole_0(X31,k2_xboole_0(X32,k5_xboole_0(X31,X32))) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X31,X31),X32),k5_xboole_0(X31,X32))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f6362,f1589])).
% 29.37/4.04  fof(f6362,plain,(
% 29.37/4.04    ( ! [X31,X32] : (k4_xboole_0(X31,k2_xboole_0(X32,k5_xboole_0(X31,X32))) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X31,k4_xboole_0(X31,X32)),X32),k5_xboole_0(X31,X32))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f6361,f443])).
% 29.37/4.04  fof(f6361,plain,(
% 29.37/4.04    ( ! [X31,X32] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X31,X32),k4_xboole_0(X31,X32)),k5_xboole_0(X31,X32)) = k4_xboole_0(X31,k2_xboole_0(X32,k5_xboole_0(X31,X32)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f6360,f5600])).
% 29.37/4.04  fof(f6360,plain,(
% 29.37/4.04    ( ! [X31,X32] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X31,X32),k4_xboole_0(X31,X32)),k5_xboole_0(X31,X32)) = k4_xboole_0(k5_xboole_0(X31,k2_xboole_0(X32,X31)),k4_xboole_0(k3_xboole_0(X32,X32),X31))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f6280,f5564])).
% 29.37/4.04  fof(f6280,plain,(
% 29.37/4.04    ( ! [X31,X32] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X31,X32),k4_xboole_0(X31,X32)),k5_xboole_0(X31,X32)) = k4_xboole_0(k5_xboole_0(X31,k2_xboole_0(X32,X31)),k4_xboole_0(k5_xboole_0(X31,X32),k4_xboole_0(X31,X32)))) )),
% 29.37/4.04    inference(superposition,[],[f5563,f991])).
% 29.37/4.04  fof(f28283,plain,(
% 29.37/4.04    ( ! [X88,X87] : (k4_xboole_0(X88,k2_xboole_0(X87,k2_xboole_0(X88,k5_xboole_0(X87,X88)))) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X87,X87),X88),k5_xboole_0(X87,X88))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f28282,f1589])).
% 29.37/4.04  fof(f28282,plain,(
% 29.37/4.04    ( ! [X88,X87] : (k4_xboole_0(X88,k2_xboole_0(X87,k2_xboole_0(X88,k5_xboole_0(X87,X88)))) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X87,k4_xboole_0(X87,X88)),X88),k5_xboole_0(X87,X88))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f28281,f443])).
% 29.37/4.04  fof(f28281,plain,(
% 29.37/4.04    ( ! [X88,X87] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X87,X88),k4_xboole_0(X87,X88)),k5_xboole_0(X87,X88)) = k4_xboole_0(X88,k2_xboole_0(X87,k2_xboole_0(X88,k5_xboole_0(X87,X88))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f28280,f28262])).
% 29.37/4.04  fof(f28262,plain,(
% 29.37/4.04    ( ! [X81,X82] : (k3_xboole_0(k5_xboole_0(X82,k5_xboole_0(X81,k5_xboole_0(X81,X82))),k4_xboole_0(X82,k2_xboole_0(X81,X82))) = k4_xboole_0(X81,k2_xboole_0(X82,k2_xboole_0(X81,k5_xboole_0(X82,X81))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f28261,f12516])).
% 29.37/4.04  fof(f28261,plain,(
% 29.37/4.04    ( ! [X81,X82] : (k3_xboole_0(k5_xboole_0(X82,k5_xboole_0(X81,k5_xboole_0(X81,X82))),k4_xboole_0(X82,k2_xboole_0(X81,X82))) = k4_xboole_0(X81,k2_xboole_0(X82,k2_xboole_0(k5_xboole_0(X82,X81),X81)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f28260,f1118])).
% 29.37/4.04  fof(f28260,plain,(
% 29.37/4.04    ( ! [X81,X82] : (k3_xboole_0(k5_xboole_0(X82,k5_xboole_0(X81,k5_xboole_0(X81,X82))),k4_xboole_0(X82,k2_xboole_0(X81,X82))) = k4_xboole_0(X81,k2_xboole_0(X82,k2_xboole_0(k5_xboole_0(X82,X81),k4_xboole_0(X81,X82))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f28259,f12516])).
% 29.37/4.04  fof(f28259,plain,(
% 29.37/4.04    ( ! [X81,X82] : (k3_xboole_0(k5_xboole_0(X82,k5_xboole_0(X81,k5_xboole_0(X81,X82))),k4_xboole_0(X82,k2_xboole_0(X81,X82))) = k4_xboole_0(X81,k2_xboole_0(X82,k2_xboole_0(k4_xboole_0(X81,X82),k5_xboole_0(X82,X81))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f28258,f24792])).
% 29.37/4.04  fof(f24792,plain,(
% 29.37/4.04    ( ! [X47,X48,X49] : (k4_xboole_0(k3_xboole_0(X49,k4_xboole_0(X48,X47)),k5_xboole_0(X47,X48)) = k4_xboole_0(X48,k2_xboole_0(X47,k2_xboole_0(X49,k5_xboole_0(X47,X48))))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f19897,f24791])).
% 29.37/4.04  fof(f24791,plain,(
% 29.37/4.04    ( ! [X99,X97,X98] : (k4_xboole_0(k3_xboole_0(X99,k5_xboole_0(X97,X98)),k5_xboole_0(X98,X97)) = k4_xboole_0(X97,k2_xboole_0(X98,k2_xboole_0(X99,k5_xboole_0(X98,X97))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f24790,f4798])).
% 29.37/4.04  fof(f4798,plain,(
% 29.37/4.04    ( ! [X64,X62,X63] : (k4_xboole_0(k5_xboole_0(X63,X62),k2_xboole_0(X64,k5_xboole_0(X63,X62))) = k4_xboole_0(X62,k2_xboole_0(X63,k2_xboole_0(X64,k5_xboole_0(X63,X62))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f4703,f20])).
% 29.37/4.04  fof(f4703,plain,(
% 29.37/4.04    ( ! [X64,X62,X63] : (k4_xboole_0(k4_xboole_0(X62,X63),k2_xboole_0(X64,k5_xboole_0(X63,X62))) = k4_xboole_0(k5_xboole_0(X63,X62),k2_xboole_0(X64,k5_xboole_0(X63,X62)))) )),
% 29.37/4.04    inference(superposition,[],[f559,f165])).
% 29.37/4.04  fof(f24790,plain,(
% 29.37/4.04    ( ! [X99,X97,X98] : (k4_xboole_0(k3_xboole_0(X99,k5_xboole_0(X97,X98)),k5_xboole_0(X98,X97)) = k4_xboole_0(k5_xboole_0(X98,X97),k2_xboole_0(X99,k5_xboole_0(X98,X97)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f24555,f5484])).
% 29.37/4.04  fof(f24555,plain,(
% 29.37/4.04    ( ! [X99,X97,X98] : (k4_xboole_0(k3_xboole_0(X99,k5_xboole_0(X97,X98)),k5_xboole_0(X98,X97)) = k4_xboole_0(k4_xboole_0(X99,k5_xboole_0(X98,X97)),k4_xboole_0(X99,k5_xboole_0(X98,X97)))) )),
% 29.37/4.04    inference(superposition,[],[f1508,f1452])).
% 29.37/4.04  fof(f1452,plain,(
% 29.37/4.04    ( ! [X28,X27] : (k5_xboole_0(X28,X27) = k2_xboole_0(k5_xboole_0(X27,X28),k5_xboole_0(X28,X27))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f1401,f18])).
% 29.37/4.04  fof(f1401,plain,(
% 29.37/4.04    ( ! [X28,X27] : (k2_xboole_0(k4_xboole_0(X28,X27),k4_xboole_0(X27,X28)) = k2_xboole_0(k5_xboole_0(X27,X28),k2_xboole_0(k4_xboole_0(X28,X27),k4_xboole_0(X27,X28)))) )),
% 29.37/4.04    inference(superposition,[],[f84,f18])).
% 29.37/4.04  fof(f19897,plain,(
% 29.37/4.04    ( ! [X47,X48,X49] : (k4_xboole_0(k3_xboole_0(X49,k4_xboole_0(X48,X47)),k5_xboole_0(X47,X48)) = k4_xboole_0(k3_xboole_0(X49,k5_xboole_0(X48,X47)),k5_xboole_0(X47,X48))) )),
% 29.37/4.04    inference(backward_demodulation,[],[f1711,f19796])).
% 29.37/4.04  fof(f19796,plain,(
% 29.37/4.04    ( ! [X109,X107,X108] : (k4_xboole_0(k3_xboole_0(X109,k5_xboole_0(X108,X107)),k5_xboole_0(X107,X108)) = k4_xboole_0(k4_xboole_0(X109,k5_xboole_0(X107,X108)),k4_xboole_0(X109,k5_xboole_0(X108,X107)))) )),
% 29.37/4.04    inference(superposition,[],[f448,f1452])).
% 29.37/4.04  fof(f1711,plain,(
% 29.37/4.04    ( ! [X47,X48,X49] : (k4_xboole_0(k3_xboole_0(X49,k4_xboole_0(X48,X47)),k5_xboole_0(X47,X48)) = k4_xboole_0(k4_xboole_0(X49,k5_xboole_0(X47,X48)),k4_xboole_0(X49,k5_xboole_0(X48,X47)))) )),
% 29.37/4.04    inference(superposition,[],[f448,f86])).
% 29.37/4.04  fof(f28258,plain,(
% 29.37/4.04    ( ! [X81,X82] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X81,X82),k4_xboole_0(X81,X82)),k5_xboole_0(X82,X81)) = k3_xboole_0(k5_xboole_0(X82,k5_xboole_0(X81,k5_xboole_0(X81,X82))),k4_xboole_0(X82,k2_xboole_0(X81,X82)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f28257,f19])).
% 29.37/4.04  fof(f28257,plain,(
% 29.37/4.04    ( ! [X81,X82] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X81,X82),k4_xboole_0(X81,X82)),k5_xboole_0(X82,X81)) = k3_xboole_0(k5_xboole_0(k5_xboole_0(X82,X81),k5_xboole_0(X81,X82)),k4_xboole_0(X82,k2_xboole_0(X81,X82)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f28256,f15096])).
% 29.37/4.04  fof(f28256,plain,(
% 29.37/4.04    ( ! [X81,X82] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X81,X82),k4_xboole_0(X81,X82)),k5_xboole_0(X82,X81)) = k3_xboole_0(k5_xboole_0(k5_xboole_0(X82,X81),k5_xboole_0(X81,X82)),k4_xboole_0(X81,k2_xboole_0(X82,k5_xboole_0(X82,X81))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f28081,f20])).
% 29.37/4.04  fof(f28081,plain,(
% 29.37/4.04    ( ! [X81,X82] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X81,X82),k4_xboole_0(X81,X82)),k5_xboole_0(X82,X81)) = k3_xboole_0(k5_xboole_0(k5_xboole_0(X82,X81),k5_xboole_0(X81,X82)),k4_xboole_0(k4_xboole_0(X81,X82),k5_xboole_0(X82,X81)))) )),
% 29.37/4.04    inference(superposition,[],[f5570,f1736])).
% 29.37/4.04  fof(f28280,plain,(
% 29.37/4.04    ( ! [X88,X87] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X87,X88),k4_xboole_0(X87,X88)),k5_xboole_0(X87,X88)) = k3_xboole_0(k5_xboole_0(X87,k5_xboole_0(X88,k5_xboole_0(X88,X87))),k4_xboole_0(X87,k2_xboole_0(X88,X87)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f28279,f19])).
% 29.37/4.04  fof(f28279,plain,(
% 29.37/4.04    ( ! [X88,X87] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X87,X88),k4_xboole_0(X87,X88)),k5_xboole_0(X87,X88)) = k3_xboole_0(k5_xboole_0(k5_xboole_0(X87,X88),k5_xboole_0(X88,X87)),k4_xboole_0(X87,k2_xboole_0(X88,X87)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f28278,f7927])).
% 29.37/4.04  fof(f28278,plain,(
% 29.37/4.04    ( ! [X88,X87] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X87,X88),k4_xboole_0(X87,X88)),k5_xboole_0(X87,X88)) = k3_xboole_0(k5_xboole_0(k5_xboole_0(X87,X88),k5_xboole_0(X88,X87)),k4_xboole_0(X87,k2_xboole_0(X88,k5_xboole_0(X87,X88))))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f28084,f20])).
% 29.37/4.04  fof(f28084,plain,(
% 29.37/4.04    ( ! [X88,X87] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X87,X88),k4_xboole_0(X87,X88)),k5_xboole_0(X87,X88)) = k3_xboole_0(k5_xboole_0(k5_xboole_0(X87,X88),k5_xboole_0(X88,X87)),k4_xboole_0(k4_xboole_0(X87,X88),k5_xboole_0(X87,X88)))) )),
% 29.37/4.04    inference(superposition,[],[f5570,f7291])).
% 29.37/4.04  fof(f7291,plain,(
% 29.37/4.04    ( ! [X6,X5] : (k5_xboole_0(X6,X5) = k2_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(X5,X6))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f7154,f5579])).
% 29.37/4.04  fof(f7154,plain,(
% 29.37/4.04    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(X5,X6)) = k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(k3_xboole_0(X6,X6),X5))) )),
% 29.37/4.04    inference(superposition,[],[f15,f5564])).
% 29.37/4.04  fof(f34187,plain,(
% 29.37/4.04    ( ! [X24,X23] : (k5_xboole_0(k4_xboole_0(X24,X23),k2_xboole_0(k5_xboole_0(X23,X24),k4_xboole_0(X24,X23))) = k2_xboole_0(k4_xboole_0(X24,k2_xboole_0(X23,k2_xboole_0(X24,k5_xboole_0(X23,X24)))),k4_xboole_0(X23,k3_xboole_0(X23,X24)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f34186,f12516])).
% 29.37/4.04  fof(f34186,plain,(
% 29.37/4.04    ( ! [X24,X23] : (k5_xboole_0(k4_xboole_0(X24,X23),k2_xboole_0(k5_xboole_0(X23,X24),k4_xboole_0(X24,X23))) = k2_xboole_0(k4_xboole_0(X24,k2_xboole_0(X23,k2_xboole_0(k5_xboole_0(X23,X24),X24))),k4_xboole_0(X23,k3_xboole_0(X23,X24)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f34185,f1118])).
% 29.37/4.04  fof(f34185,plain,(
% 29.37/4.04    ( ! [X24,X23] : (k5_xboole_0(k4_xboole_0(X24,X23),k2_xboole_0(k5_xboole_0(X23,X24),k4_xboole_0(X24,X23))) = k2_xboole_0(k4_xboole_0(X24,k2_xboole_0(X23,k2_xboole_0(k5_xboole_0(X23,X24),k4_xboole_0(X24,X23)))),k4_xboole_0(X23,k3_xboole_0(X23,X24)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f34184,f25180])).
% 29.37/4.04  fof(f25180,plain,(
% 29.37/4.04    ( ! [X30,X31,X32] : (k4_xboole_0(X30,k2_xboole_0(X31,k2_xboole_0(X32,k4_xboole_0(X30,X31)))) = k4_xboole_0(X32,k2_xboole_0(X32,k4_xboole_0(X30,X31)))) )),
% 29.37/4.04    inference(superposition,[],[f4741,f20])).
% 29.37/4.04  fof(f34184,plain,(
% 29.37/4.04    ( ! [X24,X23] : (k5_xboole_0(k4_xboole_0(X24,X23),k2_xboole_0(k5_xboole_0(X23,X24),k4_xboole_0(X24,X23))) = k2_xboole_0(k4_xboole_0(k5_xboole_0(X23,X24),k2_xboole_0(k5_xboole_0(X23,X24),k4_xboole_0(X24,X23))),k4_xboole_0(X23,k3_xboole_0(X23,X24)))) )),
% 29.37/4.04    inference(forward_demodulation,[],[f33878,f4741])).
% 29.37/4.04  fof(f33878,plain,(
% 29.37/4.04    ( ! [X24,X23] : (k5_xboole_0(k4_xboole_0(X24,X23),k2_xboole_0(k5_xboole_0(X23,X24),k4_xboole_0(X24,X23))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X24,X23),k2_xboole_0(k5_xboole_0(X23,X24),k4_xboole_0(X24,X23))),k4_xboole_0(X23,k3_xboole_0(X23,X24)))) )),
% 29.37/4.04    inference(superposition,[],[f32,f32485])).
% 29.37/4.04  fof(f55,plain,(
% 29.37/4.04    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),
% 29.37/4.04    inference(superposition,[],[f13,f19])).
% 29.37/4.04  fof(f13,plain,(
% 29.37/4.04    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 29.37/4.04    inference(cnf_transformation,[],[f12])).
% 29.37/4.04  fof(f12,plain,(
% 29.37/4.04    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 29.37/4.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).
% 29.37/4.04  fof(f11,plain,(
% 29.37/4.04    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 29.37/4.04    introduced(choice_axiom,[])).
% 29.37/4.04  fof(f10,plain,(
% 29.37/4.04    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 29.37/4.04    inference(ennf_transformation,[],[f9])).
% 29.37/4.04  fof(f9,negated_conjecture,(
% 29.37/4.04    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 29.37/4.04    inference(negated_conjecture,[],[f8])).
% 29.37/4.04  fof(f8,conjecture,(
% 29.37/4.04    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 29.37/4.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 29.37/4.04  % SZS output end Proof for theBenchmark
% 29.37/4.04  % (32233)------------------------------
% 29.37/4.04  % (32233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 29.37/4.04  % (32233)Termination reason: Refutation
% 29.37/4.04  
% 29.37/4.04  % (32233)Memory used [KB]: 49508
% 29.37/4.04  % (32233)Time elapsed: 3.595 s
% 29.37/4.04  % (32233)------------------------------
% 29.37/4.04  % (32233)------------------------------
% 29.37/4.05  % (32229)Success in time 3.678 s
%------------------------------------------------------------------------------
