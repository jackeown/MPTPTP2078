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
% DateTime   : Thu Dec  3 12:32:24 EST 2020

% Result     : Theorem 5.45s
% Output     : Refutation 5.45s
% Verified   : 
% Statistics : Number of formulae       :   92 (2405 expanded)
%              Number of leaves         :   12 ( 737 expanded)
%              Depth                    :   30
%              Number of atoms          :   93 (2406 expanded)
%              Number of equality atoms :   92 (2405 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24670,plain,(
    $false ),
    inference(subsumption_resolution,[],[f18,f24669])).

fof(f24669,plain,(
    ! [X61,X62] : k5_xboole_0(X61,X62) = k4_xboole_0(k2_xboole_0(X61,X62),k3_xboole_0(X61,X62)) ),
    inference(forward_demodulation,[],[f24668,f1231])).

fof(f1231,plain,(
    ! [X26,X27] : k5_xboole_0(X26,X27) = k3_xboole_0(k2_xboole_0(X26,X27),k5_xboole_0(X26,X27)) ),
    inference(superposition,[],[f1172,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f1172,plain,(
    ! [X17,X16] : k3_xboole_0(k2_xboole_0(X16,X17),X16) = X16 ),
    inference(superposition,[],[f493,f627])).

fof(f627,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = X2 ),
    inference(forward_demodulation,[],[f626,f50])).

fof(f50,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f45,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f45,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k1_xboole_0) = k3_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f25,f21])).

fof(f21,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f626,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f609,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f609,plain,(
    ! [X2,X3] : k3_xboole_0(k2_xboole_0(X2,X3),X2) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) ),
    inference(superposition,[],[f25,f445])).

fof(f445,plain,(
    ! [X6,X5] : k4_xboole_0(k2_xboole_0(X5,X6),X5) = k4_xboole_0(X6,X5) ),
    inference(backward_demodulation,[],[f89,f429])).

fof(f429,plain,(
    ! [X6,X5] : k5_xboole_0(k2_xboole_0(X5,X6),X5) = k4_xboole_0(X6,X5) ),
    inference(superposition,[],[f249,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f249,plain,(
    ! [X10,X9] : k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9 ),
    inference(superposition,[],[f234,f234])).

fof(f234,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f221,f34])).

fof(f34,plain,(
    ! [X3] : k5_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(forward_demodulation,[],[f33,f20])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f33,plain,(
    ! [X3] : k2_xboole_0(X3,X3) = k5_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f23,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f21,f20])).

fof(f221,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f184,f172])).

fof(f172,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f27,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f60,f30])).

fof(f60,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f24,f49])).

fof(f49,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f44,f19])).

fof(f44,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f25,f30])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f184,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f165,f118])).

fof(f118,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f31,f117])).

fof(f117,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f116,f20])).

fof(f116,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f101,f49])).

fof(f101,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f26,f61])).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f23,f19])).

fof(f165,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f27,f61])).

fof(f89,plain,(
    ! [X6,X5] : k4_xboole_0(k2_xboole_0(X5,X6),X5) = k5_xboole_0(k2_xboole_0(X5,X6),X5) ),
    inference(superposition,[],[f40,f50])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f24,f22])).

fof(f493,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f304,f22])).

fof(f304,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k3_xboole_0(k4_xboole_0(X4,X5),X4) ),
    inference(superposition,[],[f50,f289])).

fof(f289,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(backward_demodulation,[],[f48,f272])).

fof(f272,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1 ),
    inference(superposition,[],[f248,f24])).

fof(f248,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X7,X8),X8) = X7 ),
    inference(superposition,[],[f234,f184])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f23,f25])).

fof(f24668,plain,(
    ! [X61,X62] : k4_xboole_0(k2_xboole_0(X61,X62),k3_xboole_0(X61,X62)) = k3_xboole_0(k2_xboole_0(X61,X62),k5_xboole_0(X61,X62)) ),
    inference(forward_demodulation,[],[f24667,f22])).

fof(f24667,plain,(
    ! [X61,X62] : k3_xboole_0(k5_xboole_0(X61,X62),k2_xboole_0(X61,X62)) = k4_xboole_0(k2_xboole_0(X61,X62),k3_xboole_0(X61,X62)) ),
    inference(forward_demodulation,[],[f24666,f188])).

fof(f188,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f184,f24])).

fof(f24666,plain,(
    ! [X61,X62] : k3_xboole_0(k5_xboole_0(X61,X62),k2_xboole_0(X61,X62)) = k4_xboole_0(k2_xboole_0(X61,X62),k5_xboole_0(X61,k4_xboole_0(X61,X62))) ),
    inference(forward_demodulation,[],[f24665,f255])).

fof(f255,plain,(
    ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(superposition,[],[f184,f234])).

fof(f24665,plain,(
    ! [X61,X62] : k3_xboole_0(k5_xboole_0(X61,X62),k2_xboole_0(X61,X62)) = k4_xboole_0(k2_xboole_0(X61,X62),k5_xboole_0(k4_xboole_0(X61,X62),X61)) ),
    inference(forward_demodulation,[],[f24664,f15545])).

fof(f15545,plain,(
    ! [X4,X5,X3] : k5_xboole_0(k4_xboole_0(X4,X3),X5) = k5_xboole_0(X3,k5_xboole_0(k2_xboole_0(X4,X3),X5)) ),
    inference(superposition,[],[f27,f14556])).

fof(f14556,plain,(
    ! [X21,X22] : k4_xboole_0(X21,X22) = k5_xboole_0(X22,k2_xboole_0(X21,X22)) ),
    inference(superposition,[],[f234,f14477])).

fof(f14477,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k5_xboole_0(k4_xboole_0(X2,X3),X3) ),
    inference(forward_demodulation,[],[f14336,f23])).

fof(f14336,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X2,X3),X3) = k5_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(superposition,[],[f166,f2120])).

fof(f2120,plain,(
    ! [X17,X16] : k4_xboole_0(X16,X17) = k5_xboole_0(k3_xboole_0(X17,X16),X16) ),
    inference(superposition,[],[f249,f189])).

fof(f189,plain,(
    ! [X4,X3] : k3_xboole_0(X4,X3) = k5_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f184,f40])).

fof(f166,plain,(
    ! [X4,X2,X3] : k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X3),X4)) = k5_xboole_0(k4_xboole_0(X2,X3),X4) ),
    inference(superposition,[],[f27,f24])).

fof(f24664,plain,(
    ! [X61,X62] : k3_xboole_0(k5_xboole_0(X61,X62),k2_xboole_0(X61,X62)) = k4_xboole_0(k2_xboole_0(X61,X62),k5_xboole_0(X62,k5_xboole_0(k2_xboole_0(X61,X62),X61))) ),
    inference(forward_demodulation,[],[f24474,f452])).

fof(f452,plain,(
    ! [X19,X17,X18] : k5_xboole_0(X17,k5_xboole_0(X18,X19)) = k5_xboole_0(X19,k5_xboole_0(X17,X18)) ),
    inference(superposition,[],[f255,f27])).

fof(f24474,plain,(
    ! [X61,X62] : k3_xboole_0(k5_xboole_0(X61,X62),k2_xboole_0(X61,X62)) = k4_xboole_0(k2_xboole_0(X61,X62),k5_xboole_0(k2_xboole_0(X61,X62),k5_xboole_0(X61,X62))) ),
    inference(superposition,[],[f7916,f113])).

fof(f113,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f35,f26])).

fof(f35,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(backward_demodulation,[],[f32,f34])).

fof(f32,plain,(
    ! [X2,X1] : k2_xboole_0(k2_xboole_0(X1,X2),X1) = k5_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0) ),
    inference(superposition,[],[f23,f21])).

fof(f7916,plain,(
    ! [X21,X20] : k4_xboole_0(k2_xboole_0(X20,X21),k5_xboole_0(X20,X21)) = k3_xboole_0(X21,X20) ),
    inference(backward_demodulation,[],[f623,f7915])).

fof(f7915,plain,(
    ! [X57,X56] : k3_xboole_0(X57,X56) = k3_xboole_0(X56,k4_xboole_0(X57,k5_xboole_0(X56,X57))) ),
    inference(forward_demodulation,[],[f7914,f188])).

fof(f7914,plain,(
    ! [X57,X56] : k3_xboole_0(X56,k4_xboole_0(X57,k5_xboole_0(X56,X57))) = k5_xboole_0(X57,k4_xboole_0(X57,X56)) ),
    inference(forward_demodulation,[],[f7913,f255])).

fof(f7913,plain,(
    ! [X57,X56] : k3_xboole_0(X56,k4_xboole_0(X57,k5_xboole_0(X56,X57))) = k5_xboole_0(k4_xboole_0(X57,X56),X57) ),
    inference(backward_demodulation,[],[f7906,f7868])).

fof(f7868,plain,(
    ! [X4,X2,X3] : k5_xboole_0(k4_xboole_0(X3,X2),X4) = k5_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X4)) ),
    inference(superposition,[],[f27,f429])).

fof(f7906,plain,(
    ! [X57,X56] : k5_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(X56,X57)) = k3_xboole_0(X56,k4_xboole_0(X57,k5_xboole_0(X56,X57))) ),
    inference(forward_demodulation,[],[f7861,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f7861,plain,(
    ! [X57,X56] : k4_xboole_0(k3_xboole_0(X56,X57),k5_xboole_0(X56,X57)) = k5_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(X56,X57)) ),
    inference(superposition,[],[f429,f26])).

fof(f623,plain,(
    ! [X21,X20] : k4_xboole_0(k2_xboole_0(X20,X21),k5_xboole_0(X20,X21)) = k3_xboole_0(X20,k4_xboole_0(X21,k5_xboole_0(X20,X21))) ),
    inference(forward_demodulation,[],[f606,f28])).

fof(f606,plain,(
    ! [X21,X20] : k4_xboole_0(k3_xboole_0(X20,X21),k5_xboole_0(X20,X21)) = k4_xboole_0(k2_xboole_0(X20,X21),k5_xboole_0(X20,X21)) ),
    inference(superposition,[],[f445,f26])).

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
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:02:01 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.40  % (3901)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.42  % (3909)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.45  % (3896)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.45  % (3898)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.45  % (3899)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.45  % (3900)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.45  % (3903)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.45  % (3911)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.45  % (3897)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.45  % (3906)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (3904)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (3908)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (3910)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (3902)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (3907)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (3907)Refutation not found, incomplete strategy% (3907)------------------------------
% 0.20/0.48  % (3907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (3907)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (3907)Memory used [KB]: 10490
% 0.20/0.48  % (3907)Time elapsed: 0.085 s
% 0.20/0.48  % (3907)------------------------------
% 0.20/0.48  % (3907)------------------------------
% 0.20/0.48  % (3905)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (3912)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % (3913)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 4.89/1.01  % (3900)Time limit reached!
% 4.89/1.01  % (3900)------------------------------
% 4.89/1.01  % (3900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.89/1.01  % (3900)Termination reason: Time limit
% 4.89/1.01  
% 4.89/1.01  % (3900)Memory used [KB]: 21620
% 4.89/1.01  % (3900)Time elapsed: 0.625 s
% 4.89/1.01  % (3900)------------------------------
% 4.89/1.01  % (3900)------------------------------
% 5.45/1.04  % (3912)Refutation found. Thanks to Tanya!
% 5.45/1.04  % SZS status Theorem for theBenchmark
% 5.45/1.04  % SZS output start Proof for theBenchmark
% 5.45/1.04  fof(f24670,plain,(
% 5.45/1.04    $false),
% 5.45/1.04    inference(subsumption_resolution,[],[f18,f24669])).
% 5.45/1.04  fof(f24669,plain,(
% 5.45/1.04    ( ! [X61,X62] : (k5_xboole_0(X61,X62) = k4_xboole_0(k2_xboole_0(X61,X62),k3_xboole_0(X61,X62))) )),
% 5.45/1.04    inference(forward_demodulation,[],[f24668,f1231])).
% 5.45/1.04  fof(f1231,plain,(
% 5.45/1.04    ( ! [X26,X27] : (k5_xboole_0(X26,X27) = k3_xboole_0(k2_xboole_0(X26,X27),k5_xboole_0(X26,X27))) )),
% 5.45/1.04    inference(superposition,[],[f1172,f26])).
% 5.45/1.04  fof(f26,plain,(
% 5.45/1.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 5.45/1.04    inference(cnf_transformation,[],[f10])).
% 5.45/1.04  fof(f10,axiom,(
% 5.45/1.04    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.45/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).
% 5.45/1.04  fof(f1172,plain,(
% 5.45/1.04    ( ! [X17,X16] : (k3_xboole_0(k2_xboole_0(X16,X17),X16) = X16) )),
% 5.45/1.04    inference(superposition,[],[f493,f627])).
% 5.45/1.04  fof(f627,plain,(
% 5.45/1.04    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = X2) )),
% 5.45/1.04    inference(forward_demodulation,[],[f626,f50])).
% 5.45/1.04  fof(f50,plain,(
% 5.45/1.04    ( ! [X2,X1] : (k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1) )),
% 5.45/1.04    inference(forward_demodulation,[],[f45,f19])).
% 5.45/1.04  fof(f19,plain,(
% 5.45/1.04    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.45/1.04    inference(cnf_transformation,[],[f5])).
% 5.45/1.04  fof(f5,axiom,(
% 5.45/1.04    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 5.45/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 5.45/1.04  fof(f45,plain,(
% 5.45/1.04    ( ! [X2,X1] : (k4_xboole_0(X1,k1_xboole_0) = k3_xboole_0(X1,k2_xboole_0(X1,X2))) )),
% 5.45/1.04    inference(superposition,[],[f25,f21])).
% 5.45/1.04  fof(f21,plain,(
% 5.45/1.04    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 5.45/1.04    inference(cnf_transformation,[],[f6])).
% 5.45/1.04  fof(f6,axiom,(
% 5.45/1.04    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 5.45/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 5.45/1.04  fof(f25,plain,(
% 5.45/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 5.45/1.04    inference(cnf_transformation,[],[f7])).
% 5.45/1.04  fof(f7,axiom,(
% 5.45/1.04    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.45/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.45/1.04  fof(f626,plain,(
% 5.45/1.04    ( ! [X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2))) )),
% 5.45/1.04    inference(forward_demodulation,[],[f609,f22])).
% 5.45/1.04  fof(f22,plain,(
% 5.45/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.45/1.04    inference(cnf_transformation,[],[f1])).
% 5.45/1.04  fof(f1,axiom,(
% 5.45/1.04    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.45/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.45/1.04  fof(f609,plain,(
% 5.45/1.04    ( ! [X2,X3] : (k3_xboole_0(k2_xboole_0(X2,X3),X2) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2))) )),
% 5.45/1.04    inference(superposition,[],[f25,f445])).
% 5.45/1.04  fof(f445,plain,(
% 5.45/1.04    ( ! [X6,X5] : (k4_xboole_0(k2_xboole_0(X5,X6),X5) = k4_xboole_0(X6,X5)) )),
% 5.45/1.04    inference(backward_demodulation,[],[f89,f429])).
% 5.45/1.04  fof(f429,plain,(
% 5.45/1.04    ( ! [X6,X5] : (k5_xboole_0(k2_xboole_0(X5,X6),X5) = k4_xboole_0(X6,X5)) )),
% 5.45/1.04    inference(superposition,[],[f249,f23])).
% 5.45/1.04  fof(f23,plain,(
% 5.45/1.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 5.45/1.04    inference(cnf_transformation,[],[f11])).
% 5.45/1.04  fof(f11,axiom,(
% 5.45/1.04    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 5.45/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 5.45/1.04  fof(f249,plain,(
% 5.45/1.04    ( ! [X10,X9] : (k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9) )),
% 5.45/1.04    inference(superposition,[],[f234,f234])).
% 5.45/1.04  fof(f234,plain,(
% 5.45/1.04    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 5.45/1.04    inference(forward_demodulation,[],[f221,f34])).
% 5.45/1.04  fof(f34,plain,(
% 5.45/1.04    ( ! [X3] : (k5_xboole_0(X3,k1_xboole_0) = X3) )),
% 5.45/1.04    inference(forward_demodulation,[],[f33,f20])).
% 5.45/1.04  fof(f20,plain,(
% 5.45/1.04    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 5.45/1.04    inference(cnf_transformation,[],[f14])).
% 5.45/1.04  fof(f14,plain,(
% 5.45/1.04    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 5.45/1.04    inference(rectify,[],[f2])).
% 5.45/1.04  fof(f2,axiom,(
% 5.45/1.04    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 5.45/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 5.45/1.04  fof(f33,plain,(
% 5.45/1.04    ( ! [X3] : (k2_xboole_0(X3,X3) = k5_xboole_0(X3,k1_xboole_0)) )),
% 5.45/1.04    inference(superposition,[],[f23,f30])).
% 5.45/1.04  fof(f30,plain,(
% 5.45/1.04    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 5.45/1.04    inference(superposition,[],[f21,f20])).
% 5.45/1.04  fof(f221,plain,(
% 5.45/1.04    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 5.45/1.04    inference(superposition,[],[f184,f172])).
% 5.45/1.04  fof(f172,plain,(
% 5.45/1.04    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 5.45/1.04    inference(superposition,[],[f27,f61])).
% 5.45/1.04  fof(f61,plain,(
% 5.45/1.04    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 5.45/1.04    inference(forward_demodulation,[],[f60,f30])).
% 5.45/1.04  fof(f60,plain,(
% 5.45/1.04    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 5.45/1.04    inference(superposition,[],[f24,f49])).
% 5.45/1.04  fof(f49,plain,(
% 5.45/1.04    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 5.45/1.04    inference(forward_demodulation,[],[f44,f19])).
% 5.45/1.04  fof(f44,plain,(
% 5.45/1.04    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 5.45/1.04    inference(superposition,[],[f25,f30])).
% 5.45/1.04  fof(f24,plain,(
% 5.45/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.45/1.04    inference(cnf_transformation,[],[f3])).
% 5.45/1.04  fof(f3,axiom,(
% 5.45/1.04    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.45/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 5.45/1.04  fof(f27,plain,(
% 5.45/1.04    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 5.45/1.04    inference(cnf_transformation,[],[f9])).
% 5.45/1.04  fof(f9,axiom,(
% 5.45/1.04    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 5.45/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 5.45/1.04  fof(f184,plain,(
% 5.45/1.04    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 5.45/1.04    inference(forward_demodulation,[],[f165,f118])).
% 5.45/1.04  fof(f118,plain,(
% 5.45/1.04    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 5.45/1.04    inference(backward_demodulation,[],[f31,f117])).
% 5.45/1.04  fof(f117,plain,(
% 5.45/1.04    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 5.45/1.04    inference(forward_demodulation,[],[f116,f20])).
% 5.45/1.04  fof(f116,plain,(
% 5.45/1.04    ( ! [X0] : (k2_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,X0)) )),
% 5.45/1.04    inference(forward_demodulation,[],[f101,f49])).
% 5.45/1.04  fof(f101,plain,(
% 5.45/1.04    ( ! [X0] : (k2_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0))) )),
% 5.45/1.04    inference(superposition,[],[f26,f61])).
% 5.45/1.04  fof(f31,plain,(
% 5.45/1.04    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 5.45/1.04    inference(superposition,[],[f23,f19])).
% 5.45/1.04  fof(f165,plain,(
% 5.45/1.04    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 5.45/1.04    inference(superposition,[],[f27,f61])).
% 5.45/1.04  fof(f89,plain,(
% 5.45/1.04    ( ! [X6,X5] : (k4_xboole_0(k2_xboole_0(X5,X6),X5) = k5_xboole_0(k2_xboole_0(X5,X6),X5)) )),
% 5.45/1.04    inference(superposition,[],[f40,f50])).
% 5.45/1.04  fof(f40,plain,(
% 5.45/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 5.45/1.04    inference(superposition,[],[f24,f22])).
% 5.45/1.04  fof(f493,plain,(
% 5.45/1.04    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 5.45/1.04    inference(superposition,[],[f304,f22])).
% 5.45/1.04  fof(f304,plain,(
% 5.45/1.04    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k3_xboole_0(k4_xboole_0(X4,X5),X4)) )),
% 5.45/1.04    inference(superposition,[],[f50,f289])).
% 5.45/1.04  fof(f289,plain,(
% 5.45/1.04    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 5.45/1.04    inference(backward_demodulation,[],[f48,f272])).
% 5.45/1.04  fof(f272,plain,(
% 5.45/1.04    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1) )),
% 5.45/1.04    inference(superposition,[],[f248,f24])).
% 5.45/1.04  fof(f248,plain,(
% 5.45/1.04    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X7,X8),X8) = X7) )),
% 5.45/1.04    inference(superposition,[],[f234,f184])).
% 5.45/1.04  fof(f48,plain,(
% 5.45/1.04    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 5.45/1.04    inference(superposition,[],[f23,f25])).
% 5.45/1.04  fof(f24668,plain,(
% 5.45/1.04    ( ! [X61,X62] : (k4_xboole_0(k2_xboole_0(X61,X62),k3_xboole_0(X61,X62)) = k3_xboole_0(k2_xboole_0(X61,X62),k5_xboole_0(X61,X62))) )),
% 5.45/1.04    inference(forward_demodulation,[],[f24667,f22])).
% 5.45/1.04  fof(f24667,plain,(
% 5.45/1.04    ( ! [X61,X62] : (k3_xboole_0(k5_xboole_0(X61,X62),k2_xboole_0(X61,X62)) = k4_xboole_0(k2_xboole_0(X61,X62),k3_xboole_0(X61,X62))) )),
% 5.45/1.04    inference(forward_demodulation,[],[f24666,f188])).
% 5.45/1.04  fof(f188,plain,(
% 5.45/1.04    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 5.45/1.04    inference(superposition,[],[f184,f24])).
% 5.45/1.04  fof(f24666,plain,(
% 5.45/1.04    ( ! [X61,X62] : (k3_xboole_0(k5_xboole_0(X61,X62),k2_xboole_0(X61,X62)) = k4_xboole_0(k2_xboole_0(X61,X62),k5_xboole_0(X61,k4_xboole_0(X61,X62)))) )),
% 5.45/1.04    inference(forward_demodulation,[],[f24665,f255])).
% 5.45/1.04  fof(f255,plain,(
% 5.45/1.04    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) )),
% 5.45/1.04    inference(superposition,[],[f184,f234])).
% 5.45/1.04  fof(f24665,plain,(
% 5.45/1.04    ( ! [X61,X62] : (k3_xboole_0(k5_xboole_0(X61,X62),k2_xboole_0(X61,X62)) = k4_xboole_0(k2_xboole_0(X61,X62),k5_xboole_0(k4_xboole_0(X61,X62),X61))) )),
% 5.45/1.04    inference(forward_demodulation,[],[f24664,f15545])).
% 5.45/1.04  fof(f15545,plain,(
% 5.45/1.04    ( ! [X4,X5,X3] : (k5_xboole_0(k4_xboole_0(X4,X3),X5) = k5_xboole_0(X3,k5_xboole_0(k2_xboole_0(X4,X3),X5))) )),
% 5.45/1.04    inference(superposition,[],[f27,f14556])).
% 5.45/1.04  fof(f14556,plain,(
% 5.45/1.04    ( ! [X21,X22] : (k4_xboole_0(X21,X22) = k5_xboole_0(X22,k2_xboole_0(X21,X22))) )),
% 5.45/1.04    inference(superposition,[],[f234,f14477])).
% 5.45/1.04  fof(f14477,plain,(
% 5.45/1.04    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k5_xboole_0(k4_xboole_0(X2,X3),X3)) )),
% 5.45/1.04    inference(forward_demodulation,[],[f14336,f23])).
% 5.45/1.04  fof(f14336,plain,(
% 5.45/1.04    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X2,X3),X3) = k5_xboole_0(X2,k4_xboole_0(X3,X2))) )),
% 5.45/1.04    inference(superposition,[],[f166,f2120])).
% 5.45/1.04  fof(f2120,plain,(
% 5.45/1.04    ( ! [X17,X16] : (k4_xboole_0(X16,X17) = k5_xboole_0(k3_xboole_0(X17,X16),X16)) )),
% 5.45/1.04    inference(superposition,[],[f249,f189])).
% 5.45/1.04  fof(f189,plain,(
% 5.45/1.04    ( ! [X4,X3] : (k3_xboole_0(X4,X3) = k5_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 5.45/1.04    inference(superposition,[],[f184,f40])).
% 5.45/1.04  fof(f166,plain,(
% 5.45/1.04    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X3),X4)) = k5_xboole_0(k4_xboole_0(X2,X3),X4)) )),
% 5.45/1.04    inference(superposition,[],[f27,f24])).
% 5.45/1.04  fof(f24664,plain,(
% 5.45/1.04    ( ! [X61,X62] : (k3_xboole_0(k5_xboole_0(X61,X62),k2_xboole_0(X61,X62)) = k4_xboole_0(k2_xboole_0(X61,X62),k5_xboole_0(X62,k5_xboole_0(k2_xboole_0(X61,X62),X61)))) )),
% 5.45/1.04    inference(forward_demodulation,[],[f24474,f452])).
% 5.45/1.04  fof(f452,plain,(
% 5.45/1.04    ( ! [X19,X17,X18] : (k5_xboole_0(X17,k5_xboole_0(X18,X19)) = k5_xboole_0(X19,k5_xboole_0(X17,X18))) )),
% 5.45/1.04    inference(superposition,[],[f255,f27])).
% 5.45/1.04  fof(f24474,plain,(
% 5.45/1.04    ( ! [X61,X62] : (k3_xboole_0(k5_xboole_0(X61,X62),k2_xboole_0(X61,X62)) = k4_xboole_0(k2_xboole_0(X61,X62),k5_xboole_0(k2_xboole_0(X61,X62),k5_xboole_0(X61,X62)))) )),
% 5.45/1.04    inference(superposition,[],[f7916,f113])).
% 5.45/1.04  fof(f113,plain,(
% 5.45/1.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 5.45/1.04    inference(superposition,[],[f35,f26])).
% 5.45/1.04  fof(f35,plain,(
% 5.45/1.04    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),X1)) )),
% 5.45/1.04    inference(backward_demodulation,[],[f32,f34])).
% 5.45/1.04  fof(f32,plain,(
% 5.45/1.04    ( ! [X2,X1] : (k2_xboole_0(k2_xboole_0(X1,X2),X1) = k5_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0)) )),
% 5.45/1.04    inference(superposition,[],[f23,f21])).
% 5.45/1.04  fof(f7916,plain,(
% 5.45/1.04    ( ! [X21,X20] : (k4_xboole_0(k2_xboole_0(X20,X21),k5_xboole_0(X20,X21)) = k3_xboole_0(X21,X20)) )),
% 5.45/1.04    inference(backward_demodulation,[],[f623,f7915])).
% 5.45/1.04  fof(f7915,plain,(
% 5.45/1.04    ( ! [X57,X56] : (k3_xboole_0(X57,X56) = k3_xboole_0(X56,k4_xboole_0(X57,k5_xboole_0(X56,X57)))) )),
% 5.45/1.04    inference(forward_demodulation,[],[f7914,f188])).
% 5.45/1.04  fof(f7914,plain,(
% 5.45/1.04    ( ! [X57,X56] : (k3_xboole_0(X56,k4_xboole_0(X57,k5_xboole_0(X56,X57))) = k5_xboole_0(X57,k4_xboole_0(X57,X56))) )),
% 5.45/1.04    inference(forward_demodulation,[],[f7913,f255])).
% 5.45/1.04  fof(f7913,plain,(
% 5.45/1.04    ( ! [X57,X56] : (k3_xboole_0(X56,k4_xboole_0(X57,k5_xboole_0(X56,X57))) = k5_xboole_0(k4_xboole_0(X57,X56),X57)) )),
% 5.45/1.04    inference(backward_demodulation,[],[f7906,f7868])).
% 5.45/1.04  fof(f7868,plain,(
% 5.45/1.04    ( ! [X4,X2,X3] : (k5_xboole_0(k4_xboole_0(X3,X2),X4) = k5_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X4))) )),
% 5.45/1.04    inference(superposition,[],[f27,f429])).
% 5.45/1.04  fof(f7906,plain,(
% 5.45/1.04    ( ! [X57,X56] : (k5_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(X56,X57)) = k3_xboole_0(X56,k4_xboole_0(X57,k5_xboole_0(X56,X57)))) )),
% 5.45/1.04    inference(forward_demodulation,[],[f7861,f28])).
% 5.45/1.04  fof(f28,plain,(
% 5.45/1.04    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 5.45/1.04    inference(cnf_transformation,[],[f8])).
% 5.45/1.04  fof(f8,axiom,(
% 5.45/1.04    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 5.45/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 5.45/1.04  fof(f7861,plain,(
% 5.45/1.04    ( ! [X57,X56] : (k4_xboole_0(k3_xboole_0(X56,X57),k5_xboole_0(X56,X57)) = k5_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(X56,X57))) )),
% 5.45/1.04    inference(superposition,[],[f429,f26])).
% 5.45/1.04  fof(f623,plain,(
% 5.45/1.04    ( ! [X21,X20] : (k4_xboole_0(k2_xboole_0(X20,X21),k5_xboole_0(X20,X21)) = k3_xboole_0(X20,k4_xboole_0(X21,k5_xboole_0(X20,X21)))) )),
% 5.45/1.04    inference(forward_demodulation,[],[f606,f28])).
% 5.45/1.04  fof(f606,plain,(
% 5.45/1.04    ( ! [X21,X20] : (k4_xboole_0(k3_xboole_0(X20,X21),k5_xboole_0(X20,X21)) = k4_xboole_0(k2_xboole_0(X20,X21),k5_xboole_0(X20,X21))) )),
% 5.45/1.04    inference(superposition,[],[f445,f26])).
% 5.45/1.04  fof(f18,plain,(
% 5.45/1.04    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 5.45/1.04    inference(cnf_transformation,[],[f17])).
% 5.45/1.04  fof(f17,plain,(
% 5.45/1.04    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 5.45/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 5.45/1.04  fof(f16,plain,(
% 5.45/1.04    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 5.45/1.04    introduced(choice_axiom,[])).
% 5.45/1.04  fof(f15,plain,(
% 5.45/1.04    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.45/1.04    inference(ennf_transformation,[],[f13])).
% 5.45/1.04  fof(f13,negated_conjecture,(
% 5.45/1.04    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.45/1.04    inference(negated_conjecture,[],[f12])).
% 5.45/1.04  fof(f12,conjecture,(
% 5.45/1.04    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.45/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 5.45/1.04  % SZS output end Proof for theBenchmark
% 5.45/1.04  % (3912)------------------------------
% 5.45/1.04  % (3912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.45/1.04  % (3912)Termination reason: Refutation
% 5.45/1.04  
% 5.45/1.04  % (3912)Memory used [KB]: 20852
% 5.45/1.04  % (3912)Time elapsed: 0.641 s
% 5.45/1.04  % (3912)------------------------------
% 5.45/1.04  % (3912)------------------------------
% 5.45/1.05  % (3895)Success in time 0.702 s
%------------------------------------------------------------------------------
