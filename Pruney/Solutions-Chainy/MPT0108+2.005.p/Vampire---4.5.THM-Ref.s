%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:18 EST 2020

% Result     : Theorem 8.03s
% Output     : Refutation 8.03s
% Verified   : 
% Statistics : Number of formulae       :  106 (1251 expanded)
%              Number of leaves         :   15 ( 410 expanded)
%              Depth                    :   29
%              Number of atoms          :  109 (1255 expanded)
%              Number of equality atoms :  102 (1247 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7342,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f7294])).

fof(f7294,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f7293])).

fof(f7293,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f39,f7292])).

fof(f7292,plain,(
    ! [X70,X69] : k5_xboole_0(X69,X70) = k4_xboole_0(k2_xboole_0(X69,X70),k3_xboole_0(X69,X70)) ),
    inference(forward_demodulation,[],[f7225,f7054])).

fof(f7054,plain,(
    ! [X48,X49] : k5_xboole_0(X48,X49) = k4_xboole_0(k5_xboole_0(X48,X49),k3_xboole_0(X48,X49)) ),
    inference(forward_demodulation,[],[f7017,f3394])).

fof(f3394,plain,(
    ! [X2,X3] : k5_xboole_0(k2_xboole_0(X3,X2),k3_xboole_0(X3,X2)) = k5_xboole_0(X3,X2) ),
    inference(superposition,[],[f395,f139])).

fof(f139,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f64,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f64,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(backward_demodulation,[],[f55,f62])).

fof(f62,plain,(
    ! [X10,X11] : k2_xboole_0(X10,k4_xboole_0(X10,X11)) = X10 ),
    inference(superposition,[],[f28,f46])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f45,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f25,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f53,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f35,f25])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f395,plain,(
    ! [X6,X8,X7] : k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),X8)) = k5_xboole_0(k2_xboole_0(X6,X7),X8) ),
    inference(superposition,[],[f32,f35])).

fof(f32,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f7017,plain,(
    ! [X48,X49] : k4_xboole_0(k5_xboole_0(X48,X49),k3_xboole_0(X48,X49)) = k5_xboole_0(k2_xboole_0(X48,X49),k3_xboole_0(X48,X49)) ),
    inference(superposition,[],[f5437,f584])).

fof(f584,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3)) ),
    inference(superposition,[],[f33,f30])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f5437,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(forward_demodulation,[],[f5410,f2577])).

fof(f2577,plain,(
    ! [X8,X9] : k4_xboole_0(X9,X8) = k5_xboole_0(X8,k2_xboole_0(X8,X9)) ),
    inference(superposition,[],[f2464,f35])).

fof(f2464,plain,(
    ! [X14,X15] : k5_xboole_0(X14,k5_xboole_0(X14,X15)) = X15 ),
    inference(backward_demodulation,[],[f398,f2463])).

fof(f2463,plain,(
    ! [X17,X18] : k5_xboole_0(k4_xboole_0(X18,X18),X17) = X17 ),
    inference(forward_demodulation,[],[f2433,f2015])).

fof(f2015,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,X1),X2) = X2 ),
    inference(superposition,[],[f1427,f1926])).

fof(f1926,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X0) = k3_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f1878,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f26,f29])).

fof(f1878,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X0) = k3_xboole_0(X0,k4_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f111,f589])).

fof(f589,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f588,f28])).

fof(f588,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f561,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f49,f25])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f25,f26])).

fof(f561,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f33,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f111,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(forward_demodulation,[],[f95,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f95,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(superposition,[],[f22,f25])).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1427,plain,(
    ! [X47,X45,X46] : k2_xboole_0(k3_xboole_0(X47,k4_xboole_0(X45,X46)),X45) = X45 ),
    inference(superposition,[],[f1312,f300])).

fof(f300,plain,(
    ! [X10,X9] : k4_xboole_0(X9,X10) = k3_xboole_0(k4_xboole_0(X9,X10),X9) ),
    inference(forward_demodulation,[],[f281,f157])).

fof(f157,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f152,f31])).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f152,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f63,f35])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f60,f25])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f34,f46])).

fof(f281,plain,(
    ! [X10,X9] : k3_xboole_0(k4_xboole_0(X9,X10),X9) = k3_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,X10)) ),
    inference(superposition,[],[f78,f46])).

fof(f78,plain,(
    ! [X12,X11] : k3_xboole_0(X11,k3_xboole_0(X12,X11)) = k3_xboole_0(X11,X12) ),
    inference(forward_demodulation,[],[f74,f25])).

fof(f74,plain,(
    ! [X12,X11] : k3_xboole_0(X11,k3_xboole_0(X12,X11)) = k4_xboole_0(X11,k4_xboole_0(X11,X12)) ),
    inference(superposition,[],[f25,f47])).

fof(f1312,plain,(
    ! [X14,X15,X13] : k2_xboole_0(k3_xboole_0(X14,k3_xboole_0(X15,X13)),X13) = X13 ),
    inference(superposition,[],[f1294,f240])).

fof(f240,plain,(
    ! [X6,X7,X5] : k3_xboole_0(X5,k3_xboole_0(X6,X7)) = k3_xboole_0(X7,k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f27,f29])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f1294,plain,(
    ! [X8,X7] : k2_xboole_0(k3_xboole_0(X7,X8),X7) = X7 ),
    inference(forward_demodulation,[],[f1258,f612])).

fof(f612,plain,(
    ! [X17,X16] : k2_xboole_0(k5_xboole_0(k3_xboole_0(X16,X17),X16),k3_xboole_0(X16,X17)) = X16 ),
    inference(forward_demodulation,[],[f611,f28])).

fof(f611,plain,(
    ! [X17,X16] : k2_xboole_0(k5_xboole_0(k3_xboole_0(X16,X17),X16),k3_xboole_0(X16,X17)) = k2_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(forward_demodulation,[],[f581,f30])).

fof(f581,plain,(
    ! [X17,X16] : k2_xboole_0(k3_xboole_0(X16,X17),X16) = k2_xboole_0(k5_xboole_0(k3_xboole_0(X16,X17),X16),k3_xboole_0(X16,X17)) ),
    inference(superposition,[],[f33,f297])).

fof(f297,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k3_xboole_0(k3_xboole_0(X5,X6),X5) ),
    inference(forward_demodulation,[],[f279,f157])).

fof(f279,plain,(
    ! [X6,X5] : k3_xboole_0(k3_xboole_0(X5,X6),X5) = k3_xboole_0(k3_xboole_0(X5,X6),k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f78,f50])).

fof(f1258,plain,(
    ! [X8,X7] : k2_xboole_0(k3_xboole_0(X7,X8),X7) = k2_xboole_0(k5_xboole_0(k3_xboole_0(X7,X8),X7),k3_xboole_0(X7,X8)) ),
    inference(superposition,[],[f574,f50])).

fof(f574,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f33,f29])).

fof(f2433,plain,(
    ! [X17,X18] : k2_xboole_0(k4_xboole_0(X18,X18),X17) = k5_xboole_0(k4_xboole_0(X18,X18),X17) ),
    inference(superposition,[],[f35,f2223])).

fof(f2223,plain,(
    ! [X28,X29] : k4_xboole_0(X29,k4_xboole_0(X28,X28)) = X29 ),
    inference(forward_demodulation,[],[f2192,f2015])).

fof(f2192,plain,(
    ! [X28,X29] : k4_xboole_0(X29,k4_xboole_0(X28,X28)) = k2_xboole_0(k4_xboole_0(X28,X28),X29) ),
    inference(superposition,[],[f2015,f1541])).

fof(f1541,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f1507,f35])).

fof(f1507,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f105,f31])).

fof(f105,plain,(
    ! [X10,X11,X9] : k2_xboole_0(X11,k4_xboole_0(X9,X10)) = k5_xboole_0(X11,k4_xboole_0(X9,k2_xboole_0(X10,X11))) ),
    inference(superposition,[],[f35,f22])).

fof(f398,plain,(
    ! [X14,X15] : k5_xboole_0(X14,k5_xboole_0(X14,X15)) = k5_xboole_0(k4_xboole_0(X14,X14),X15) ),
    inference(superposition,[],[f32,f160])).

fof(f160,plain,(
    ! [X4] : k4_xboole_0(X4,X4) = k5_xboole_0(X4,X4) ),
    inference(superposition,[],[f34,f157])).

fof(f5410,plain,(
    ! [X2,X1] : k5_xboole_0(k2_xboole_0(X2,X1),X2) = k5_xboole_0(X2,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f395,f2166])).

fof(f2166,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k5_xboole_0(k4_xboole_0(X11,X10),X10) ),
    inference(forward_demodulation,[],[f2165,f1541])).

fof(f2165,plain,(
    ! [X10,X11] : k2_xboole_0(X10,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X11,X10),X10) ),
    inference(forward_demodulation,[],[f2143,f30])).

fof(f2143,plain,(
    ! [X10,X11] : k2_xboole_0(k4_xboole_0(X11,X10),X10) = k5_xboole_0(k4_xboole_0(X11,X10),X10) ),
    inference(superposition,[],[f35,f2089])).

fof(f2089,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X9,X8)) = X8 ),
    inference(forward_demodulation,[],[f2088,f157])).

fof(f2088,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X8) = k4_xboole_0(X8,k4_xboole_0(X9,X8)) ),
    inference(forward_demodulation,[],[f2018,f25])).

fof(f2018,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X9,X8)) = k4_xboole_0(X8,k4_xboole_0(X8,X8)) ),
    inference(superposition,[],[f26,f1926])).

fof(f7225,plain,(
    ! [X70,X69] : k4_xboole_0(k5_xboole_0(X69,X70),k3_xboole_0(X69,X70)) = k4_xboole_0(k2_xboole_0(X69,X70),k3_xboole_0(X69,X70)) ),
    inference(superposition,[],[f7040,f33])).

fof(f7040,plain,(
    ! [X24,X25] : k4_xboole_0(k2_xboole_0(X25,X24),X24) = k4_xboole_0(X25,X24) ),
    inference(backward_demodulation,[],[f1596,f6996])).

fof(f6996,plain,(
    ! [X2,X1] : k4_xboole_0(X2,X1) = k5_xboole_0(k2_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f5437,f30])).

fof(f1596,plain,(
    ! [X24,X25] : k4_xboole_0(k2_xboole_0(X25,X24),X24) = k5_xboole_0(k2_xboole_0(X25,X24),X24) ),
    inference(superposition,[],[f51,f1560])).

fof(f1560,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k2_xboole_0(X4,X3)) = X3 ),
    inference(forward_demodulation,[],[f1533,f62])).

fof(f1533,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k2_xboole_0(X4,X3)) = k2_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f105,f63])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f34,f29])).

fof(f39,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl2_1
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f40,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f21,f37])).

fof(f21,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:14:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.45  % (3147)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.47  % (3164)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.48  % (3164)Refutation not found, incomplete strategy% (3164)------------------------------
% 0.20/0.48  % (3164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (3164)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (3164)Memory used [KB]: 1663
% 0.20/0.48  % (3164)Time elapsed: 0.092 s
% 0.20/0.48  % (3164)------------------------------
% 0.20/0.48  % (3164)------------------------------
% 0.20/0.49  % (3163)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.49  % (3155)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (3163)Refutation not found, incomplete strategy% (3163)------------------------------
% 0.20/0.50  % (3163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (3163)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (3163)Memory used [KB]: 10746
% 0.20/0.50  % (3163)Time elapsed: 0.111 s
% 0.20/0.50  % (3163)------------------------------
% 0.20/0.50  % (3163)------------------------------
% 0.20/0.50  % (3161)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (3145)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (3159)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (3141)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (3151)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (3141)Refutation not found, incomplete strategy% (3141)------------------------------
% 0.20/0.52  % (3141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (3144)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (3153)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (3161)Refutation not found, incomplete strategy% (3161)------------------------------
% 0.20/0.52  % (3161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (3143)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (3143)Refutation not found, incomplete strategy% (3143)------------------------------
% 0.20/0.52  % (3143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (3143)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (3143)Memory used [KB]: 10618
% 0.20/0.52  % (3143)Time elapsed: 0.120 s
% 0.20/0.52  % (3143)------------------------------
% 0.20/0.52  % (3143)------------------------------
% 0.20/0.52  % (3161)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (3161)Memory used [KB]: 10618
% 0.20/0.52  % (3161)Time elapsed: 0.128 s
% 0.20/0.52  % (3161)------------------------------
% 0.20/0.52  % (3161)------------------------------
% 0.20/0.52  % (3149)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (3141)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (3141)Memory used [KB]: 1663
% 0.20/0.52  % (3141)Time elapsed: 0.115 s
% 0.20/0.52  % (3141)------------------------------
% 0.20/0.52  % (3141)------------------------------
% 0.20/0.53  % (3165)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (3156)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (3149)Refutation not found, incomplete strategy% (3149)------------------------------
% 0.20/0.53  % (3149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (3149)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (3142)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (3149)Memory used [KB]: 10618
% 0.20/0.53  % (3149)Time elapsed: 0.128 s
% 0.20/0.53  % (3149)------------------------------
% 0.20/0.53  % (3149)------------------------------
% 0.20/0.53  % (3169)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (3146)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (3157)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (3154)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (3152)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (3150)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (3167)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (3148)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (3168)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (3170)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (3160)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (3158)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (3162)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (3166)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.56  % (3158)Refutation not found, incomplete strategy% (3158)------------------------------
% 0.20/0.56  % (3158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (3158)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (3158)Memory used [KB]: 10618
% 0.20/0.56  % (3158)Time elapsed: 0.157 s
% 0.20/0.56  % (3158)------------------------------
% 0.20/0.56  % (3158)------------------------------
% 0.20/0.56  % (3162)Refutation not found, incomplete strategy% (3162)------------------------------
% 0.20/0.56  % (3162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (3162)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (3162)Memory used [KB]: 1663
% 0.20/0.57  % (3162)Time elapsed: 0.161 s
% 0.20/0.57  % (3162)------------------------------
% 0.20/0.57  % (3162)------------------------------
% 1.82/0.62  % (3216)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.82/0.62  % (3216)Refutation not found, incomplete strategy% (3216)------------------------------
% 1.82/0.62  % (3216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.62  % (3216)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.62  
% 1.82/0.62  % (3216)Memory used [KB]: 6140
% 1.82/0.62  % (3216)Time elapsed: 0.106 s
% 1.82/0.62  % (3216)------------------------------
% 1.82/0.62  % (3216)------------------------------
% 1.82/0.62  % (3225)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.82/0.63  % (3234)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.16/0.65  % (3232)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.16/0.66  % (3235)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.16/0.67  % (3239)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.16/0.69  % (3267)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.16/0.70  % (3261)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.66/0.76  % (3300)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 3.07/0.81  % (3146)Time limit reached!
% 3.07/0.81  % (3146)------------------------------
% 3.07/0.81  % (3146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.07/0.81  % (3146)Termination reason: Time limit
% 3.07/0.81  
% 3.07/0.81  % (3146)Memory used [KB]: 8827
% 3.07/0.81  % (3146)Time elapsed: 0.406 s
% 3.07/0.81  % (3146)------------------------------
% 3.07/0.81  % (3146)------------------------------
% 3.95/0.91  % (3153)Time limit reached!
% 3.95/0.91  % (3153)------------------------------
% 3.95/0.91  % (3153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.95/0.91  % (3142)Time limit reached!
% 3.95/0.91  % (3142)------------------------------
% 3.95/0.91  % (3142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.95/0.91  % (3142)Termination reason: Time limit
% 3.95/0.91  
% 3.95/0.91  % (3142)Memory used [KB]: 9083
% 3.95/0.91  % (3142)Time elapsed: 0.506 s
% 3.95/0.91  % (3142)------------------------------
% 3.95/0.91  % (3142)------------------------------
% 3.95/0.91  % (3153)Termination reason: Time limit
% 3.95/0.91  
% 3.95/0.91  % (3153)Memory used [KB]: 10874
% 3.95/0.91  % (3153)Time elapsed: 0.509 s
% 3.95/0.91  % (3153)------------------------------
% 3.95/0.91  % (3153)------------------------------
% 4.31/0.95  % (3361)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 4.31/0.95  % (3234)Time limit reached!
% 4.31/0.95  % (3234)------------------------------
% 4.31/0.95  % (3234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/0.95  % (3234)Termination reason: Time limit
% 4.31/0.95  % (3234)Termination phase: Saturation
% 4.31/0.95  
% 4.31/0.95  % (3234)Memory used [KB]: 8315
% 4.31/0.95  % (3234)Time elapsed: 0.400 s
% 4.31/0.95  % (3234)------------------------------
% 4.31/0.95  % (3234)------------------------------
% 4.31/0.96  % (3235)Time limit reached!
% 4.31/0.96  % (3235)------------------------------
% 4.31/0.96  % (3235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/0.96  % (3235)Termination reason: Time limit
% 4.31/0.96  
% 4.31/0.96  % (3235)Memory used [KB]: 13688
% 4.31/0.96  % (3235)Time elapsed: 0.406 s
% 4.31/0.96  % (3235)------------------------------
% 4.31/0.96  % (3235)------------------------------
% 4.31/1.00  % (3169)Time limit reached!
% 4.31/1.00  % (3169)------------------------------
% 4.31/1.00  % (3169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/1.00  % (3169)Termination reason: Time limit
% 4.31/1.00  
% 4.31/1.00  % (3169)Memory used [KB]: 9083
% 4.31/1.00  % (3169)Time elapsed: 0.604 s
% 4.31/1.00  % (3169)------------------------------
% 4.31/1.00  % (3169)------------------------------
% 4.31/1.00  % (3410)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 4.31/1.00  % (3151)Time limit reached!
% 4.31/1.00  % (3151)------------------------------
% 4.31/1.00  % (3151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/1.00  % (3151)Termination reason: Time limit
% 4.31/1.00  
% 4.31/1.00  % (3151)Memory used [KB]: 33517
% 4.31/1.00  % (3151)Time elapsed: 0.581 s
% 4.31/1.00  % (3151)------------------------------
% 4.31/1.00  % (3151)------------------------------
% 4.74/1.02  % (3408)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 4.74/1.02  % (3408)Refutation not found, incomplete strategy% (3408)------------------------------
% 4.74/1.02  % (3408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.74/1.03  % (3410)Refutation not found, incomplete strategy% (3410)------------------------------
% 4.74/1.03  % (3410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.74/1.03  % (3410)Termination reason: Refutation not found, incomplete strategy
% 4.74/1.03  
% 4.74/1.03  % (3410)Memory used [KB]: 1663
% 4.74/1.03  % (3410)Time elapsed: 0.095 s
% 4.74/1.03  % (3410)------------------------------
% 4.74/1.03  % (3410)------------------------------
% 4.74/1.03  % (3408)Termination reason: Refutation not found, incomplete strategy
% 4.74/1.03  
% 4.74/1.03  % (3408)Memory used [KB]: 6140
% 4.74/1.03  % (3408)Time elapsed: 0.096 s
% 4.74/1.03  % (3408)------------------------------
% 4.74/1.03  % (3408)------------------------------
% 4.74/1.03  % (3157)Time limit reached!
% 4.74/1.03  % (3157)------------------------------
% 4.74/1.03  % (3157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.74/1.03  % (3157)Termination reason: Time limit
% 4.74/1.03  
% 4.74/1.03  % (3157)Memory used [KB]: 16502
% 4.74/1.03  % (3157)Time elapsed: 0.612 s
% 4.74/1.03  % (3157)------------------------------
% 4.74/1.03  % (3157)------------------------------
% 4.74/1.04  % (3148)Time limit reached!
% 4.74/1.04  % (3148)------------------------------
% 4.74/1.04  % (3148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.74/1.04  % (3148)Termination reason: Time limit
% 4.74/1.04  % (3148)Termination phase: Saturation
% 4.74/1.04  
% 4.74/1.04  % (3148)Memory used [KB]: 12792
% 4.74/1.04  % (3148)Time elapsed: 0.613 s
% 4.74/1.04  % (3148)------------------------------
% 4.74/1.04  % (3148)------------------------------
% 4.74/1.05  % (3412)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 4.74/1.06  % (3413)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 5.65/1.09  % (3413)Refutation not found, incomplete strategy% (3413)------------------------------
% 5.65/1.09  % (3413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.65/1.09  % (3413)Termination reason: Refutation not found, incomplete strategy
% 5.65/1.09  
% 5.65/1.09  % (3413)Memory used [KB]: 1663
% 5.65/1.09  % (3413)Time elapsed: 0.111 s
% 5.65/1.09  % (3413)------------------------------
% 5.65/1.09  % (3413)------------------------------
% 5.65/1.11  % (3414)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 5.65/1.13  % (3415)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 5.65/1.13  % (3415)Refutation not found, incomplete strategy% (3415)------------------------------
% 5.65/1.13  % (3415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.65/1.13  % (3415)Termination reason: Refutation not found, incomplete strategy
% 5.65/1.13  
% 5.65/1.13  % (3415)Memory used [KB]: 6268
% 5.65/1.13  % (3415)Time elapsed: 0.109 s
% 5.65/1.13  % (3415)------------------------------
% 5.65/1.13  % (3415)------------------------------
% 5.65/1.14  % (3417)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 5.65/1.15  % (3416)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 6.36/1.17  % (3418)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 6.36/1.17  % (3419)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 6.58/1.23  % (3420)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 6.80/1.25  % (3421)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 8.03/1.42  % (3225)Refutation found. Thanks to Tanya!
% 8.03/1.42  % SZS status Theorem for theBenchmark
% 8.03/1.42  % SZS output start Proof for theBenchmark
% 8.03/1.42  fof(f7342,plain,(
% 8.03/1.42    $false),
% 8.03/1.42    inference(avatar_sat_refutation,[],[f40,f7294])).
% 8.03/1.42  fof(f7294,plain,(
% 8.03/1.42    spl2_1),
% 8.03/1.42    inference(avatar_contradiction_clause,[],[f7293])).
% 8.03/1.42  fof(f7293,plain,(
% 8.03/1.42    $false | spl2_1),
% 8.03/1.42    inference(subsumption_resolution,[],[f39,f7292])).
% 8.03/1.42  fof(f7292,plain,(
% 8.03/1.42    ( ! [X70,X69] : (k5_xboole_0(X69,X70) = k4_xboole_0(k2_xboole_0(X69,X70),k3_xboole_0(X69,X70))) )),
% 8.03/1.42    inference(forward_demodulation,[],[f7225,f7054])).
% 8.03/1.42  fof(f7054,plain,(
% 8.03/1.42    ( ! [X48,X49] : (k5_xboole_0(X48,X49) = k4_xboole_0(k5_xboole_0(X48,X49),k3_xboole_0(X48,X49))) )),
% 8.03/1.42    inference(forward_demodulation,[],[f7017,f3394])).
% 8.03/1.42  fof(f3394,plain,(
% 8.03/1.42    ( ! [X2,X3] : (k5_xboole_0(k2_xboole_0(X3,X2),k3_xboole_0(X3,X2)) = k5_xboole_0(X3,X2)) )),
% 8.03/1.42    inference(superposition,[],[f395,f139])).
% 8.03/1.42  fof(f139,plain,(
% 8.03/1.42    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = X0) )),
% 8.03/1.42    inference(superposition,[],[f64,f29])).
% 8.03/1.42  fof(f29,plain,(
% 8.03/1.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 8.03/1.42    inference(cnf_transformation,[],[f2])).
% 8.03/1.42  fof(f2,axiom,(
% 8.03/1.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 8.03/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 8.03/1.42  fof(f64,plain,(
% 8.03/1.42    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0) )),
% 8.03/1.42    inference(backward_demodulation,[],[f55,f62])).
% 8.03/1.42  fof(f62,plain,(
% 8.03/1.42    ( ! [X10,X11] : (k2_xboole_0(X10,k4_xboole_0(X10,X11)) = X10) )),
% 8.03/1.42    inference(superposition,[],[f28,f46])).
% 8.03/1.42  fof(f46,plain,(
% 8.03/1.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 8.03/1.42    inference(forward_demodulation,[],[f45,f26])).
% 8.03/1.42  fof(f26,plain,(
% 8.03/1.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.03/1.42    inference(cnf_transformation,[],[f10])).
% 8.03/1.42  fof(f10,axiom,(
% 8.03/1.42    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 8.03/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 8.03/1.42  fof(f45,plain,(
% 8.03/1.42    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 8.03/1.42    inference(superposition,[],[f25,f25])).
% 8.03/1.42  fof(f25,plain,(
% 8.03/1.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 8.03/1.42    inference(cnf_transformation,[],[f11])).
% 8.03/1.42  fof(f11,axiom,(
% 8.03/1.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 8.03/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 8.03/1.42  fof(f28,plain,(
% 8.03/1.42    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 8.03/1.42    inference(cnf_transformation,[],[f7])).
% 8.03/1.42  fof(f7,axiom,(
% 8.03/1.42    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 8.03/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 8.03/1.42  fof(f55,plain,(
% 8.03/1.42    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 8.03/1.42    inference(forward_demodulation,[],[f53,f30])).
% 8.03/1.42  fof(f30,plain,(
% 8.03/1.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 8.03/1.42    inference(cnf_transformation,[],[f1])).
% 8.03/1.42  fof(f1,axiom,(
% 8.03/1.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 8.03/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 8.03/1.42  fof(f53,plain,(
% 8.03/1.42    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 8.03/1.42    inference(superposition,[],[f35,f25])).
% 8.03/1.42  fof(f35,plain,(
% 8.03/1.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 8.03/1.42    inference(cnf_transformation,[],[f15])).
% 8.03/1.42  fof(f15,axiom,(
% 8.03/1.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 8.03/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 8.03/1.42  fof(f395,plain,(
% 8.03/1.42    ( ! [X6,X8,X7] : (k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),X8)) = k5_xboole_0(k2_xboole_0(X6,X7),X8)) )),
% 8.03/1.42    inference(superposition,[],[f32,f35])).
% 8.03/1.42  fof(f32,plain,(
% 8.03/1.42    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 8.03/1.42    inference(cnf_transformation,[],[f13])).
% 8.03/1.42  fof(f13,axiom,(
% 8.03/1.42    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 8.03/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 8.03/1.42  fof(f7017,plain,(
% 8.03/1.42    ( ! [X48,X49] : (k4_xboole_0(k5_xboole_0(X48,X49),k3_xboole_0(X48,X49)) = k5_xboole_0(k2_xboole_0(X48,X49),k3_xboole_0(X48,X49))) )),
% 8.03/1.42    inference(superposition,[],[f5437,f584])).
% 8.03/1.42  fof(f584,plain,(
% 8.03/1.42    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))) )),
% 8.03/1.42    inference(superposition,[],[f33,f30])).
% 8.03/1.42  fof(f33,plain,(
% 8.03/1.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 8.03/1.42    inference(cnf_transformation,[],[f14])).
% 8.03/1.42  fof(f14,axiom,(
% 8.03/1.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 8.03/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).
% 8.03/1.42  fof(f5437,plain,(
% 8.03/1.42    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 8.03/1.42    inference(forward_demodulation,[],[f5410,f2577])).
% 8.03/1.42  fof(f2577,plain,(
% 8.03/1.42    ( ! [X8,X9] : (k4_xboole_0(X9,X8) = k5_xboole_0(X8,k2_xboole_0(X8,X9))) )),
% 8.03/1.42    inference(superposition,[],[f2464,f35])).
% 8.03/1.42  fof(f2464,plain,(
% 8.03/1.42    ( ! [X14,X15] : (k5_xboole_0(X14,k5_xboole_0(X14,X15)) = X15) )),
% 8.03/1.42    inference(backward_demodulation,[],[f398,f2463])).
% 8.03/1.43  fof(f2463,plain,(
% 8.03/1.43    ( ! [X17,X18] : (k5_xboole_0(k4_xboole_0(X18,X18),X17) = X17) )),
% 8.03/1.43    inference(forward_demodulation,[],[f2433,f2015])).
% 8.03/1.43  fof(f2015,plain,(
% 8.03/1.43    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,X1),X2) = X2) )),
% 8.03/1.43    inference(superposition,[],[f1427,f1926])).
% 8.03/1.43  fof(f1926,plain,(
% 8.03/1.43    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = k3_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 8.03/1.43    inference(forward_demodulation,[],[f1878,f47])).
% 8.03/1.43  fof(f47,plain,(
% 8.03/1.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 8.03/1.43    inference(superposition,[],[f26,f29])).
% 8.03/1.43  fof(f1878,plain,(
% 8.03/1.43    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = k3_xboole_0(X0,k4_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 8.03/1.43    inference(superposition,[],[f111,f589])).
% 8.03/1.43  fof(f589,plain,(
% 8.03/1.43    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0) )),
% 8.03/1.43    inference(forward_demodulation,[],[f588,f28])).
% 8.03/1.43  fof(f588,plain,(
% 8.03/1.43    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 8.03/1.43    inference(forward_demodulation,[],[f561,f50])).
% 8.03/1.43  fof(f50,plain,(
% 8.03/1.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.03/1.43    inference(forward_demodulation,[],[f49,f25])).
% 8.03/1.43  fof(f49,plain,(
% 8.03/1.43    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.03/1.43    inference(superposition,[],[f25,f26])).
% 8.03/1.43  fof(f561,plain,(
% 8.03/1.43    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 8.03/1.43    inference(superposition,[],[f33,f34])).
% 8.03/1.43  fof(f34,plain,(
% 8.03/1.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.03/1.43    inference(cnf_transformation,[],[f4])).
% 8.03/1.43  fof(f4,axiom,(
% 8.03/1.43    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 8.03/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 8.03/1.43  fof(f111,plain,(
% 8.03/1.43    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 8.03/1.43    inference(forward_demodulation,[],[f95,f23])).
% 8.03/1.43  fof(f23,plain,(
% 8.03/1.43    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 8.03/1.43    inference(cnf_transformation,[],[f12])).
% 8.03/1.43  fof(f12,axiom,(
% 8.03/1.43    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 8.03/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 8.03/1.43  fof(f95,plain,(
% 8.03/1.43    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 8.03/1.43    inference(superposition,[],[f22,f25])).
% 8.03/1.43  fof(f22,plain,(
% 8.03/1.43    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 8.03/1.43    inference(cnf_transformation,[],[f9])).
% 8.03/1.43  fof(f9,axiom,(
% 8.03/1.43    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 8.03/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 8.03/1.43  fof(f1427,plain,(
% 8.03/1.43    ( ! [X47,X45,X46] : (k2_xboole_0(k3_xboole_0(X47,k4_xboole_0(X45,X46)),X45) = X45) )),
% 8.03/1.43    inference(superposition,[],[f1312,f300])).
% 8.03/1.43  fof(f300,plain,(
% 8.03/1.43    ( ! [X10,X9] : (k4_xboole_0(X9,X10) = k3_xboole_0(k4_xboole_0(X9,X10),X9)) )),
% 8.03/1.43    inference(forward_demodulation,[],[f281,f157])).
% 8.03/1.43  fof(f157,plain,(
% 8.03/1.43    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 8.03/1.43    inference(forward_demodulation,[],[f152,f31])).
% 8.03/1.43  fof(f31,plain,(
% 8.03/1.43    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 8.03/1.43    inference(cnf_transformation,[],[f18])).
% 8.03/1.43  fof(f18,plain,(
% 8.03/1.43    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 8.03/1.43    inference(rectify,[],[f3])).
% 8.03/1.43  fof(f3,axiom,(
% 8.03/1.43    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 8.03/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 8.03/1.43  fof(f152,plain,(
% 8.03/1.43    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_xboole_0(X0,X0)) )),
% 8.03/1.43    inference(superposition,[],[f63,f35])).
% 8.03/1.43  fof(f63,plain,(
% 8.03/1.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 8.03/1.43    inference(forward_demodulation,[],[f60,f25])).
% 8.03/1.43  fof(f60,plain,(
% 8.03/1.43    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 8.03/1.43    inference(superposition,[],[f34,f46])).
% 8.03/1.43  fof(f281,plain,(
% 8.03/1.43    ( ! [X10,X9] : (k3_xboole_0(k4_xboole_0(X9,X10),X9) = k3_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,X10))) )),
% 8.03/1.43    inference(superposition,[],[f78,f46])).
% 8.03/1.43  fof(f78,plain,(
% 8.03/1.43    ( ! [X12,X11] : (k3_xboole_0(X11,k3_xboole_0(X12,X11)) = k3_xboole_0(X11,X12)) )),
% 8.03/1.43    inference(forward_demodulation,[],[f74,f25])).
% 8.03/1.43  fof(f74,plain,(
% 8.03/1.43    ( ! [X12,X11] : (k3_xboole_0(X11,k3_xboole_0(X12,X11)) = k4_xboole_0(X11,k4_xboole_0(X11,X12))) )),
% 8.03/1.43    inference(superposition,[],[f25,f47])).
% 8.03/1.43  fof(f1312,plain,(
% 8.03/1.43    ( ! [X14,X15,X13] : (k2_xboole_0(k3_xboole_0(X14,k3_xboole_0(X15,X13)),X13) = X13) )),
% 8.03/1.43    inference(superposition,[],[f1294,f240])).
% 8.03/1.43  fof(f240,plain,(
% 8.03/1.43    ( ! [X6,X7,X5] : (k3_xboole_0(X5,k3_xboole_0(X6,X7)) = k3_xboole_0(X7,k3_xboole_0(X5,X6))) )),
% 8.03/1.43    inference(superposition,[],[f27,f29])).
% 8.03/1.43  fof(f27,plain,(
% 8.03/1.43    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 8.03/1.43    inference(cnf_transformation,[],[f5])).
% 8.03/1.43  fof(f5,axiom,(
% 8.03/1.43    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 8.03/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 8.03/1.43  fof(f1294,plain,(
% 8.03/1.43    ( ! [X8,X7] : (k2_xboole_0(k3_xboole_0(X7,X8),X7) = X7) )),
% 8.03/1.43    inference(forward_demodulation,[],[f1258,f612])).
% 8.03/1.43  fof(f612,plain,(
% 8.03/1.43    ( ! [X17,X16] : (k2_xboole_0(k5_xboole_0(k3_xboole_0(X16,X17),X16),k3_xboole_0(X16,X17)) = X16) )),
% 8.03/1.43    inference(forward_demodulation,[],[f611,f28])).
% 8.03/1.43  fof(f611,plain,(
% 8.03/1.43    ( ! [X17,X16] : (k2_xboole_0(k5_xboole_0(k3_xboole_0(X16,X17),X16),k3_xboole_0(X16,X17)) = k2_xboole_0(X16,k3_xboole_0(X16,X17))) )),
% 8.03/1.43    inference(forward_demodulation,[],[f581,f30])).
% 8.03/1.43  fof(f581,plain,(
% 8.03/1.43    ( ! [X17,X16] : (k2_xboole_0(k3_xboole_0(X16,X17),X16) = k2_xboole_0(k5_xboole_0(k3_xboole_0(X16,X17),X16),k3_xboole_0(X16,X17))) )),
% 8.03/1.43    inference(superposition,[],[f33,f297])).
% 8.03/1.43  fof(f297,plain,(
% 8.03/1.43    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k3_xboole_0(k3_xboole_0(X5,X6),X5)) )),
% 8.03/1.43    inference(forward_demodulation,[],[f279,f157])).
% 8.03/1.43  fof(f279,plain,(
% 8.03/1.43    ( ! [X6,X5] : (k3_xboole_0(k3_xboole_0(X5,X6),X5) = k3_xboole_0(k3_xboole_0(X5,X6),k3_xboole_0(X5,X6))) )),
% 8.03/1.43    inference(superposition,[],[f78,f50])).
% 8.03/1.43  fof(f1258,plain,(
% 8.03/1.43    ( ! [X8,X7] : (k2_xboole_0(k3_xboole_0(X7,X8),X7) = k2_xboole_0(k5_xboole_0(k3_xboole_0(X7,X8),X7),k3_xboole_0(X7,X8))) )),
% 8.03/1.43    inference(superposition,[],[f574,f50])).
% 8.03/1.43  fof(f574,plain,(
% 8.03/1.43    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X2,X1))) )),
% 8.03/1.43    inference(superposition,[],[f33,f29])).
% 8.03/1.43  fof(f2433,plain,(
% 8.03/1.43    ( ! [X17,X18] : (k2_xboole_0(k4_xboole_0(X18,X18),X17) = k5_xboole_0(k4_xboole_0(X18,X18),X17)) )),
% 8.03/1.43    inference(superposition,[],[f35,f2223])).
% 8.03/1.43  fof(f2223,plain,(
% 8.03/1.43    ( ! [X28,X29] : (k4_xboole_0(X29,k4_xboole_0(X28,X28)) = X29) )),
% 8.03/1.43    inference(forward_demodulation,[],[f2192,f2015])).
% 8.03/1.43  fof(f2192,plain,(
% 8.03/1.43    ( ! [X28,X29] : (k4_xboole_0(X29,k4_xboole_0(X28,X28)) = k2_xboole_0(k4_xboole_0(X28,X28),X29)) )),
% 8.03/1.43    inference(superposition,[],[f2015,f1541])).
% 8.03/1.43  fof(f1541,plain,(
% 8.03/1.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 8.03/1.43    inference(forward_demodulation,[],[f1507,f35])).
% 8.03/1.43  fof(f1507,plain,(
% 8.03/1.43    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 8.03/1.43    inference(superposition,[],[f105,f31])).
% 8.03/1.43  fof(f105,plain,(
% 8.03/1.43    ( ! [X10,X11,X9] : (k2_xboole_0(X11,k4_xboole_0(X9,X10)) = k5_xboole_0(X11,k4_xboole_0(X9,k2_xboole_0(X10,X11)))) )),
% 8.03/1.43    inference(superposition,[],[f35,f22])).
% 8.03/1.43  fof(f398,plain,(
% 8.03/1.43    ( ! [X14,X15] : (k5_xboole_0(X14,k5_xboole_0(X14,X15)) = k5_xboole_0(k4_xboole_0(X14,X14),X15)) )),
% 8.03/1.43    inference(superposition,[],[f32,f160])).
% 8.03/1.43  fof(f160,plain,(
% 8.03/1.43    ( ! [X4] : (k4_xboole_0(X4,X4) = k5_xboole_0(X4,X4)) )),
% 8.03/1.43    inference(superposition,[],[f34,f157])).
% 8.03/1.43  fof(f5410,plain,(
% 8.03/1.43    ( ! [X2,X1] : (k5_xboole_0(k2_xboole_0(X2,X1),X2) = k5_xboole_0(X2,k2_xboole_0(X2,X1))) )),
% 8.03/1.43    inference(superposition,[],[f395,f2166])).
% 8.03/1.43  fof(f2166,plain,(
% 8.03/1.43    ( ! [X10,X11] : (k2_xboole_0(X10,X11) = k5_xboole_0(k4_xboole_0(X11,X10),X10)) )),
% 8.03/1.43    inference(forward_demodulation,[],[f2165,f1541])).
% 8.03/1.43  fof(f2165,plain,(
% 8.03/1.43    ( ! [X10,X11] : (k2_xboole_0(X10,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X11,X10),X10)) )),
% 8.03/1.43    inference(forward_demodulation,[],[f2143,f30])).
% 8.03/1.43  fof(f2143,plain,(
% 8.03/1.43    ( ! [X10,X11] : (k2_xboole_0(k4_xboole_0(X11,X10),X10) = k5_xboole_0(k4_xboole_0(X11,X10),X10)) )),
% 8.03/1.43    inference(superposition,[],[f35,f2089])).
% 8.03/1.43  fof(f2089,plain,(
% 8.03/1.43    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X9,X8)) = X8) )),
% 8.03/1.43    inference(forward_demodulation,[],[f2088,f157])).
% 8.03/1.43  fof(f2088,plain,(
% 8.03/1.43    ( ! [X8,X9] : (k3_xboole_0(X8,X8) = k4_xboole_0(X8,k4_xboole_0(X9,X8))) )),
% 8.03/1.43    inference(forward_demodulation,[],[f2018,f25])).
% 8.03/1.43  fof(f2018,plain,(
% 8.03/1.43    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X9,X8)) = k4_xboole_0(X8,k4_xboole_0(X8,X8))) )),
% 8.03/1.43    inference(superposition,[],[f26,f1926])).
% 8.03/1.43  fof(f7225,plain,(
% 8.03/1.43    ( ! [X70,X69] : (k4_xboole_0(k5_xboole_0(X69,X70),k3_xboole_0(X69,X70)) = k4_xboole_0(k2_xboole_0(X69,X70),k3_xboole_0(X69,X70))) )),
% 8.03/1.43    inference(superposition,[],[f7040,f33])).
% 8.03/1.43  fof(f7040,plain,(
% 8.03/1.43    ( ! [X24,X25] : (k4_xboole_0(k2_xboole_0(X25,X24),X24) = k4_xboole_0(X25,X24)) )),
% 8.03/1.43    inference(backward_demodulation,[],[f1596,f6996])).
% 8.03/1.43  fof(f6996,plain,(
% 8.03/1.43    ( ! [X2,X1] : (k4_xboole_0(X2,X1) = k5_xboole_0(k2_xboole_0(X2,X1),X1)) )),
% 8.03/1.43    inference(superposition,[],[f5437,f30])).
% 8.03/1.43  fof(f1596,plain,(
% 8.03/1.43    ( ! [X24,X25] : (k4_xboole_0(k2_xboole_0(X25,X24),X24) = k5_xboole_0(k2_xboole_0(X25,X24),X24)) )),
% 8.03/1.43    inference(superposition,[],[f51,f1560])).
% 8.03/1.43  fof(f1560,plain,(
% 8.03/1.43    ( ! [X4,X3] : (k3_xboole_0(X3,k2_xboole_0(X4,X3)) = X3) )),
% 8.03/1.43    inference(forward_demodulation,[],[f1533,f62])).
% 8.03/1.43  fof(f1533,plain,(
% 8.03/1.43    ( ! [X4,X3] : (k3_xboole_0(X3,k2_xboole_0(X4,X3)) = k2_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 8.03/1.43    inference(superposition,[],[f105,f63])).
% 8.03/1.43  fof(f51,plain,(
% 8.03/1.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 8.03/1.43    inference(superposition,[],[f34,f29])).
% 8.03/1.43  fof(f39,plain,(
% 8.03/1.43    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) | spl2_1),
% 8.03/1.43    inference(avatar_component_clause,[],[f37])).
% 8.03/1.43  fof(f37,plain,(
% 8.03/1.43    spl2_1 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 8.03/1.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 8.03/1.43  fof(f40,plain,(
% 8.03/1.43    ~spl2_1),
% 8.03/1.43    inference(avatar_split_clause,[],[f21,f37])).
% 8.03/1.43  fof(f21,plain,(
% 8.03/1.43    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 8.03/1.43    inference(cnf_transformation,[],[f19])).
% 8.03/1.43  fof(f19,plain,(
% 8.03/1.43    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 8.03/1.43    inference(ennf_transformation,[],[f17])).
% 8.03/1.43  fof(f17,negated_conjecture,(
% 8.03/1.43    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 8.03/1.43    inference(negated_conjecture,[],[f16])).
% 8.03/1.43  fof(f16,conjecture,(
% 8.03/1.43    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 8.03/1.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 8.03/1.43  % SZS output end Proof for theBenchmark
% 8.03/1.43  % (3225)------------------------------
% 8.03/1.43  % (3225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.03/1.43  % (3225)Termination reason: Refutation
% 8.03/1.43  
% 8.03/1.43  % (3225)Memory used [KB]: 12792
% 8.03/1.43  % (3225)Time elapsed: 0.861 s
% 8.03/1.43  % (3225)------------------------------
% 8.03/1.43  % (3225)------------------------------
% 8.03/1.43  % (3140)Success in time 1.084 s
%------------------------------------------------------------------------------
