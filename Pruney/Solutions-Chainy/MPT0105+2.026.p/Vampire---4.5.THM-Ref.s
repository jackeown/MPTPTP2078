%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:07 EST 2020

% Result     : Theorem 5.17s
% Output     : Refutation 5.17s
% Verified   : 
% Statistics : Number of formulae       :  139 (1933 expanded)
%              Number of leaves         :   12 ( 644 expanded)
%              Depth                    :   31
%              Number of atoms          :  140 (1934 expanded)
%              Number of equality atoms :  139 (1933 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8020,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f8019])).

fof(f8019,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f4772,f7721])).

fof(f7721,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f7408,f19])).

fof(f19,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f7408,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k5_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f7404,f128])).

fof(f128,plain,(
    ! [X7] : k1_xboole_0 = k3_xboole_0(X7,k1_xboole_0) ),
    inference(superposition,[],[f67,f18])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f67,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
    inference(forward_demodulation,[],[f52,f20])).

fof(f20,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
    inference(superposition,[],[f25,f37])).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f23,f18])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f7404,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X2,X1),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f6395,f7401])).

fof(f7401,plain,(
    ! [X8,X7] : k1_xboole_0 = k3_xboole_0(X7,k4_xboole_0(X8,X7)) ),
    inference(forward_demodulation,[],[f7400,f17])).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f7400,plain,(
    ! [X8,X7] : k5_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,X8)) = k3_xboole_0(X7,k4_xboole_0(X8,X7)) ),
    inference(forward_demodulation,[],[f7365,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f7365,plain,(
    ! [X8,X7] : k3_xboole_0(X7,k4_xboole_0(X8,X7)) = k5_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,k4_xboole_0(X8,X7))) ),
    inference(backward_demodulation,[],[f1719,f7324])).

fof(f7324,plain,(
    ! [X15,X16] : k5_xboole_0(X16,k3_xboole_0(X15,X16)) = k4_xboole_0(X16,X15) ),
    inference(backward_demodulation,[],[f367,f7319])).

fof(f7319,plain,(
    ! [X6,X5] : k5_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(X6,X5) ),
    inference(backward_demodulation,[],[f5639,f7314])).

fof(f7314,plain,(
    ! [X10,X9] : k4_xboole_0(X10,X9) = k5_xboole_0(k3_xboole_0(X9,X10),X10) ),
    inference(backward_demodulation,[],[f5038,f7312])).

fof(f7312,plain,(
    ! [X19,X20] : k4_xboole_0(X20,X19) = k5_xboole_0(k2_xboole_0(X19,X20),X19) ),
    inference(forward_demodulation,[],[f7249,f6558])).

fof(f6558,plain,(
    ! [X33,X34] : k4_xboole_0(X34,X33) = k4_xboole_0(k2_xboole_0(X33,X34),X33) ),
    inference(forward_demodulation,[],[f6557,f2269])).

fof(f2269,plain,(
    ! [X35,X36] : k3_xboole_0(k2_xboole_0(X35,X36),X36) = X36 ),
    inference(forward_demodulation,[],[f2251,f391])).

fof(f391,plain,(
    ! [X10,X9] : k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9 ),
    inference(superposition,[],[f98,f98])).

fof(f98,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f94,f21])).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f94,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f76,f27])).

fof(f27,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f21,f19])).

fof(f76,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f26,f17])).

fof(f26,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f2251,plain,(
    ! [X35,X36] : k3_xboole_0(k2_xboole_0(X35,X36),X36) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X35,X36),X36),k2_xboole_0(X35,X36)) ),
    inference(superposition,[],[f102,f542])).

fof(f542,plain,(
    ! [X14,X13] : k2_xboole_0(X14,X13) = k2_xboole_0(k2_xboole_0(X14,X13),X13) ),
    inference(forward_demodulation,[],[f535,f146])).

fof(f146,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f144,f19])).

fof(f144,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f51,f135])).

fof(f135,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f37,f128])).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f48,f19])).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f24,f37])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f535,plain,(
    ! [X14,X13] : k2_xboole_0(k2_xboole_0(X14,X13),X13) = k2_xboole_0(k2_xboole_0(X14,X13),k1_xboole_0) ),
    inference(superposition,[],[f22,f142])).

fof(f142,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,X3)) ),
    inference(backward_demodulation,[],[f70,f128])).

fof(f70,plain,(
    ! [X4,X3] : k3_xboole_0(k4_xboole_0(X3,X4),k1_xboole_0) = k4_xboole_0(X3,k2_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f57,f22])).

fof(f57,plain,(
    ! [X4,X3] : k3_xboole_0(k4_xboole_0(X3,X4),k1_xboole_0) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X4))) ),
    inference(superposition,[],[f25,f37])).

fof(f102,plain,(
    ! [X10,X9] : k3_xboole_0(X9,X10) = k5_xboole_0(k5_xboole_0(X9,X10),k2_xboole_0(X9,X10)) ),
    inference(superposition,[],[f94,f24])).

fof(f6557,plain,(
    ! [X33,X34] : k4_xboole_0(k2_xboole_0(X33,X34),X33) = k4_xboole_0(k3_xboole_0(k2_xboole_0(X33,X34),X34),X33) ),
    inference(forward_demodulation,[],[f6458,f18])).

fof(f6458,plain,(
    ! [X33,X34] : k4_xboole_0(k3_xboole_0(k2_xboole_0(X33,X34),X34),X33) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X33,X34),X33),k1_xboole_0) ),
    inference(superposition,[],[f6237,f135])).

fof(f6237,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4))) = k4_xboole_0(k3_xboole_0(X2,X4),X3) ),
    inference(backward_demodulation,[],[f62,f6236])).

fof(f6236,plain,(
    ! [X8,X7,X9] : k3_xboole_0(k4_xboole_0(X7,X8),X9) = k4_xboole_0(k3_xboole_0(X7,X9),X8) ),
    inference(forward_demodulation,[],[f6235,f6098])).

fof(f6098,plain,(
    ! [X21,X19,X20] : k4_xboole_0(k3_xboole_0(X19,X20),X21) = k4_xboole_0(X19,k2_xboole_0(X21,k4_xboole_0(X19,X20))) ),
    inference(superposition,[],[f904,f53])).

fof(f53,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4)) = k4_xboole_0(k3_xboole_0(X2,X3),X4) ),
    inference(superposition,[],[f25,f23])).

fof(f904,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k2_xboole_0(X0,X1)) = k4_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f869,f859])).

fof(f859,plain,(
    ! [X6,X5] : k2_xboole_0(X6,X5) = k2_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f856,f98])).

fof(f856,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X5)) = k5_xboole_0(X5,k5_xboole_0(k2_xboole_0(X6,X5),X5)) ),
    inference(superposition,[],[f83,f540])).

fof(f540,plain,(
    ! [X12,X11] : k3_xboole_0(X11,k2_xboole_0(X12,X11)) = X11 ),
    inference(forward_demodulation,[],[f534,f18])).

fof(f534,plain,(
    ! [X12,X11] : k3_xboole_0(X11,k2_xboole_0(X12,X11)) = k4_xboole_0(X11,k1_xboole_0) ),
    inference(superposition,[],[f23,f142])).

fof(f83,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f26,f24])).

fof(f869,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k2_xboole_0(X0,X1)) = k4_xboole_0(X2,k2_xboole_0(X0,k2_xboole_0(X1,X0))) ),
    inference(superposition,[],[f69,f147])).

fof(f147,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(backward_demodulation,[],[f35,f146])).

fof(f35,plain,(
    ! [X2,X1] : k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0) ),
    inference(superposition,[],[f22,f20])).

fof(f69,plain,(
    ! [X12,X10,X13,X11] : k4_xboole_0(X10,k2_xboole_0(k2_xboole_0(X11,X12),X13)) = k4_xboole_0(X10,k2_xboole_0(X11,k2_xboole_0(X12,X13))) ),
    inference(forward_demodulation,[],[f68,f25])).

fof(f68,plain,(
    ! [X12,X10,X13,X11] : k4_xboole_0(k4_xboole_0(X10,X11),k2_xboole_0(X12,X13)) = k4_xboole_0(X10,k2_xboole_0(k2_xboole_0(X11,X12),X13)) ),
    inference(forward_demodulation,[],[f56,f25])).

fof(f56,plain,(
    ! [X12,X10,X13,X11] : k4_xboole_0(k4_xboole_0(X10,X11),k2_xboole_0(X12,X13)) = k4_xboole_0(k4_xboole_0(X10,k2_xboole_0(X11,X12)),X13) ),
    inference(superposition,[],[f25,f25])).

fof(f6235,plain,(
    ! [X8,X7,X9] : k3_xboole_0(k4_xboole_0(X7,X8),X9) = k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,X9))) ),
    inference(forward_demodulation,[],[f6142,f63])).

fof(f63,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7))) ),
    inference(superposition,[],[f22,f25])).

fof(f6142,plain,(
    ! [X8,X7,X9] : k3_xboole_0(k4_xboole_0(X7,X8),X9) = k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,k2_xboole_0(X9,X8)))) ),
    inference(superposition,[],[f71,f904])).

fof(f71,plain,(
    ! [X6,X7,X5] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,k2_xboole_0(X6,X7)))) ),
    inference(forward_demodulation,[],[f58,f25])).

fof(f58,plain,(
    ! [X6,X7,X5] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(k4_xboole_0(X5,X6),X7))) ),
    inference(superposition,[],[f25,f23])).

fof(f62,plain,(
    ! [X4,X2,X3] : k3_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(superposition,[],[f23,f25])).

fof(f7249,plain,(
    ! [X19,X20] : k5_xboole_0(k2_xboole_0(X19,X20),X19) = k4_xboole_0(k2_xboole_0(X19,X20),X19) ),
    inference(superposition,[],[f4649,f1790])).

fof(f1790,plain,(
    ! [X17,X18] : k3_xboole_0(k2_xboole_0(X17,X18),X17) = X17 ),
    inference(forward_demodulation,[],[f1745,f391])).

fof(f1745,plain,(
    ! [X17,X18] : k3_xboole_0(k2_xboole_0(X17,X18),X17) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X17,X18),X17),k2_xboole_0(X17,X18)) ),
    inference(superposition,[],[f102,f147])).

fof(f4649,plain,(
    ! [X28,X27] : k4_xboole_0(X27,X28) = k5_xboole_0(X27,k3_xboole_0(X27,X28)) ),
    inference(forward_demodulation,[],[f4648,f19])).

fof(f4648,plain,(
    ! [X28,X27] : k5_xboole_0(X27,k3_xboole_0(X27,X28)) = k5_xboole_0(k4_xboole_0(X27,X28),k1_xboole_0) ),
    inference(forward_demodulation,[],[f4647,f1160])).

fof(f1160,plain,(
    ! [X2,X1] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f827,f23])).

fof(f827,plain,(
    ! [X10,X9] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X10,X9),X9) ),
    inference(forward_demodulation,[],[f788,f135])).

fof(f788,plain,(
    ! [X10,X9] : k3_xboole_0(k4_xboole_0(X10,X9),X9) = k4_xboole_0(k4_xboole_0(X10,X9),k4_xboole_0(X10,X9)) ),
    inference(superposition,[],[f62,f149])).

fof(f149,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = X1 ),
    inference(forward_demodulation,[],[f137,f146])).

fof(f137,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f50,f128])).

fof(f50,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f22,f37])).

fof(f4647,plain,(
    ! [X28,X27] : k5_xboole_0(k4_xboole_0(X27,X28),k3_xboole_0(k3_xboole_0(X27,X28),k4_xboole_0(X27,X28))) = k5_xboole_0(X27,k3_xboole_0(X27,X28)) ),
    inference(forward_demodulation,[],[f4550,f21])).

fof(f4550,plain,(
    ! [X28,X27] : k5_xboole_0(k4_xboole_0(X27,X28),k3_xboole_0(k3_xboole_0(X27,X28),k4_xboole_0(X27,X28))) = k5_xboole_0(k3_xboole_0(X27,X28),X27) ),
    inference(superposition,[],[f367,f2492])).

fof(f2492,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(backward_demodulation,[],[f1831,f2490])).

fof(f2490,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(forward_demodulation,[],[f2480,f391])).

fof(f2480,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = k5_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),X0),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f24,f681])).

fof(f681,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f673,f18])).

fof(f673,plain,(
    ! [X2,X3] : k3_xboole_0(k3_xboole_0(X2,X3),X2) = k4_xboole_0(k3_xboole_0(X2,X3),k1_xboole_0) ),
    inference(superposition,[],[f23,f652])).

fof(f652,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f651,f135])).

fof(f651,plain,(
    ! [X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f623,f53])).

fof(f623,plain,(
    ! [X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(superposition,[],[f53,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f22,f23])).

fof(f1831,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f22,f1776])).

fof(f1776,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k4_xboole_0(X3,k3_xboole_0(X3,X4)) ),
    inference(backward_demodulation,[],[f39,f1775])).

fof(f1775,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k3_xboole_0(X6,k4_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f1739,f391])).

fof(f1739,plain,(
    ! [X6,X7] : k3_xboole_0(X6,k4_xboole_0(X6,X7)) = k5_xboole_0(k5_xboole_0(X6,k4_xboole_0(X6,X7)),X6) ),
    inference(superposition,[],[f102,f711])).

fof(f711,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k4_xboole_0(X5,X6)) = X5 ),
    inference(forward_demodulation,[],[f692,f146])).

fof(f692,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k1_xboole_0) = k2_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f63,f142])).

fof(f39,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f23,f23])).

fof(f5038,plain,(
    ! [X10,X9] : k5_xboole_0(k2_xboole_0(X9,X10),X9) = k5_xboole_0(k3_xboole_0(X9,X10),X10) ),
    inference(superposition,[],[f442,f81])).

fof(f81,plain,(
    ! [X14,X12,X13] : k5_xboole_0(k5_xboole_0(X12,X13),k5_xboole_0(k3_xboole_0(X12,X13),X14)) = k5_xboole_0(k2_xboole_0(X12,X13),X14) ),
    inference(superposition,[],[f26,f24])).

fof(f442,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X10,X9) = k5_xboole_0(k5_xboole_0(X8,X9),k5_xboole_0(X10,X8)) ),
    inference(superposition,[],[f86,f94])).

fof(f86,plain,(
    ! [X10,X11,X9] : k5_xboole_0(X11,k5_xboole_0(X9,X10)) = k5_xboole_0(X9,k5_xboole_0(X10,X11)) ),
    inference(superposition,[],[f26,f21])).

fof(f5639,plain,(
    ! [X6,X5] : k5_xboole_0(k3_xboole_0(X5,X6),X6) = k5_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f492,f83])).

fof(f492,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X10,X9) = k5_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f418,f26])).

fof(f418,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X10,X9) = k5_xboole_0(X8,k5_xboole_0(k5_xboole_0(X8,X9),X10)) ),
    inference(superposition,[],[f86,f94])).

fof(f367,plain,(
    ! [X15,X16] : k5_xboole_0(X16,k3_xboole_0(X15,X16)) = k5_xboole_0(X15,k2_xboole_0(X15,X16)) ),
    inference(superposition,[],[f94,f83])).

fof(f1719,plain,(
    ! [X8,X7] : k3_xboole_0(X7,k5_xboole_0(X8,k3_xboole_0(X7,X8))) = k5_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,k5_xboole_0(X8,k3_xboole_0(X7,X8)))) ),
    inference(superposition,[],[f102,f83])).

fof(f6395,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X2,X1),k3_xboole_0(X1,k4_xboole_0(X2,X1)))) ),
    inference(backward_demodulation,[],[f4675,f6394])).

fof(f6394,plain,(
    ! [X37,X38,X36] : k2_xboole_0(X38,X36) = k2_xboole_0(k2_xboole_0(X38,X36),k3_xboole_0(X36,X37)) ),
    inference(forward_demodulation,[],[f6372,f146])).

fof(f6372,plain,(
    ! [X37,X38,X36] : k2_xboole_0(k2_xboole_0(X38,X36),k3_xboole_0(X36,X37)) = k2_xboole_0(k2_xboole_0(X38,X36),k1_xboole_0) ),
    inference(superposition,[],[f22,f2788])).

fof(f2788,plain,(
    ! [X4,X5,X3] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X3,X4),k2_xboole_0(X5,X3)) ),
    inference(superposition,[],[f59,f2606])).

fof(f2606,plain,(
    ! [X14,X15,X13] : k2_xboole_0(k4_xboole_0(k3_xboole_0(X13,X14),X15),X13) = X13 ),
    inference(superposition,[],[f2562,f53])).

fof(f2562,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(backward_demodulation,[],[f40,f2561])).

fof(f2561,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f2513,f1775])).

fof(f2513,plain,(
    ! [X2,X1] : k2_xboole_0(k3_xboole_0(X1,k4_xboole_0(X1,X2)),k3_xboole_0(X1,X2)) = X1 ),
    inference(superposition,[],[f2492,f23])).

fof(f59,plain,(
    ! [X10,X8,X9] : k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,k2_xboole_0(k4_xboole_0(X8,X9),X10))) ),
    inference(superposition,[],[f25,f20])).

fof(f4675,plain,(
    ! [X2,X1] : k2_xboole_0(k2_xboole_0(X2,X1),k3_xboole_0(X1,k4_xboole_0(X2,X1))) = k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X2,X1),k3_xboole_0(X1,k4_xboole_0(X2,X1)))) ),
    inference(backward_demodulation,[],[f1374,f4650])).

fof(f4650,plain,(
    ! [X4,X3] : k2_xboole_0(X4,X3) = k5_xboole_0(X3,k4_xboole_0(X4,X3)) ),
    inference(backward_demodulation,[],[f237,f4649])).

fof(f237,plain,(
    ! [X4,X3] : k2_xboole_0(X4,X3) = k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))) ),
    inference(superposition,[],[f44,f26])).

fof(f44,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k5_xboole_0(k5_xboole_0(X3,X2),k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f24,f21])).

fof(f1374,plain,(
    ! [X2,X1] : k2_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k3_xboole_0(X1,k4_xboole_0(X2,X1))) = k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k3_xboole_0(X1,k4_xboole_0(X2,X1)))) ),
    inference(superposition,[],[f47,f22])).

fof(f47,plain,(
    ! [X8,X7] : k2_xboole_0(k5_xboole_0(X7,X8),k3_xboole_0(X7,X8)) = k5_xboole_0(k2_xboole_0(X7,X8),k3_xboole_0(k5_xboole_0(X7,X8),k3_xboole_0(X7,X8))) ),
    inference(superposition,[],[f24,f24])).

fof(f4772,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f16,f4650])).

fof(f16,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:52:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (5903)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (5919)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.46  % (5916)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (5910)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (5908)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (5912)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (5914)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (5906)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (5904)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (5909)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (5902)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (5911)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (5918)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  % (5907)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (5905)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.49  % (5915)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.51  % (5917)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.52  % (5913)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.52  % (5913)Refutation not found, incomplete strategy% (5913)------------------------------
% 0.20/0.52  % (5913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5913)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (5913)Memory used [KB]: 10490
% 0.20/0.52  % (5913)Time elapsed: 0.111 s
% 0.20/0.52  % (5913)------------------------------
% 0.20/0.52  % (5913)------------------------------
% 5.17/1.03  % (5905)Refutation found. Thanks to Tanya!
% 5.17/1.03  % SZS status Theorem for theBenchmark
% 5.17/1.03  % SZS output start Proof for theBenchmark
% 5.17/1.03  fof(f8020,plain,(
% 5.17/1.03    $false),
% 5.17/1.03    inference(trivial_inequality_removal,[],[f8019])).
% 5.17/1.03  fof(f8019,plain,(
% 5.17/1.03    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1)),
% 5.17/1.03    inference(superposition,[],[f4772,f7721])).
% 5.17/1.03  fof(f7721,plain,(
% 5.17/1.03    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 5.17/1.03    inference(superposition,[],[f7408,f19])).
% 5.17/1.03  fof(f19,plain,(
% 5.17/1.03    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.17/1.03    inference(cnf_transformation,[],[f7])).
% 5.17/1.03  fof(f7,axiom,(
% 5.17/1.03    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 5.17/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 5.17/1.03  fof(f7408,plain,(
% 5.17/1.03    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k5_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0)) )),
% 5.17/1.03    inference(forward_demodulation,[],[f7404,f128])).
% 5.17/1.03  fof(f128,plain,(
% 5.17/1.03    ( ! [X7] : (k1_xboole_0 = k3_xboole_0(X7,k1_xboole_0)) )),
% 5.17/1.03    inference(superposition,[],[f67,f18])).
% 5.17/1.03  fof(f18,plain,(
% 5.17/1.03    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.17/1.03    inference(cnf_transformation,[],[f3])).
% 5.17/1.03  fof(f3,axiom,(
% 5.17/1.03    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 5.17/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 5.17/1.03  fof(f67,plain,(
% 5.17/1.03    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) )),
% 5.17/1.03    inference(forward_demodulation,[],[f52,f20])).
% 5.17/1.03  fof(f20,plain,(
% 5.17/1.03    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 5.17/1.03    inference(cnf_transformation,[],[f5])).
% 5.17/1.03  fof(f5,axiom,(
% 5.17/1.03    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 5.17/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 5.17/1.03  fof(f52,plain,(
% 5.17/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) )),
% 5.17/1.03    inference(superposition,[],[f25,f37])).
% 5.17/1.03  fof(f37,plain,(
% 5.17/1.03    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 5.17/1.03    inference(superposition,[],[f23,f18])).
% 5.17/1.03  fof(f23,plain,(
% 5.17/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 5.17/1.03    inference(cnf_transformation,[],[f6])).
% 5.17/1.03  fof(f6,axiom,(
% 5.17/1.03    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 5.17/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.17/1.03  fof(f25,plain,(
% 5.17/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 5.17/1.03    inference(cnf_transformation,[],[f4])).
% 5.17/1.03  fof(f4,axiom,(
% 5.17/1.03    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 5.17/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 5.17/1.03  fof(f7404,plain,(
% 5.17/1.03    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X2,X1),k1_xboole_0))) )),
% 5.17/1.03    inference(backward_demodulation,[],[f6395,f7401])).
% 5.17/1.03  fof(f7401,plain,(
% 5.17/1.03    ( ! [X8,X7] : (k1_xboole_0 = k3_xboole_0(X7,k4_xboole_0(X8,X7))) )),
% 5.17/1.03    inference(forward_demodulation,[],[f7400,f17])).
% 5.17/1.03  fof(f17,plain,(
% 5.17/1.03    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 5.17/1.03    inference(cnf_transformation,[],[f9])).
% 5.17/1.03  fof(f9,axiom,(
% 5.17/1.03    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 5.17/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 5.17/1.03  fof(f7400,plain,(
% 5.17/1.03    ( ! [X8,X7] : (k5_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,X8)) = k3_xboole_0(X7,k4_xboole_0(X8,X7))) )),
% 5.17/1.03    inference(forward_demodulation,[],[f7365,f22])).
% 5.17/1.03  fof(f22,plain,(
% 5.17/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 5.17/1.03    inference(cnf_transformation,[],[f2])).
% 5.17/1.03  fof(f2,axiom,(
% 5.17/1.03    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 5.17/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 5.17/1.03  fof(f7365,plain,(
% 5.17/1.03    ( ! [X8,X7] : (k3_xboole_0(X7,k4_xboole_0(X8,X7)) = k5_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,k4_xboole_0(X8,X7)))) )),
% 5.17/1.03    inference(backward_demodulation,[],[f1719,f7324])).
% 5.17/1.03  fof(f7324,plain,(
% 5.17/1.03    ( ! [X15,X16] : (k5_xboole_0(X16,k3_xboole_0(X15,X16)) = k4_xboole_0(X16,X15)) )),
% 5.17/1.03    inference(backward_demodulation,[],[f367,f7319])).
% 5.17/1.03  fof(f7319,plain,(
% 5.17/1.03    ( ! [X6,X5] : (k5_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(X6,X5)) )),
% 5.17/1.03    inference(backward_demodulation,[],[f5639,f7314])).
% 5.17/1.03  fof(f7314,plain,(
% 5.17/1.03    ( ! [X10,X9] : (k4_xboole_0(X10,X9) = k5_xboole_0(k3_xboole_0(X9,X10),X10)) )),
% 5.17/1.03    inference(backward_demodulation,[],[f5038,f7312])).
% 5.17/1.03  fof(f7312,plain,(
% 5.17/1.03    ( ! [X19,X20] : (k4_xboole_0(X20,X19) = k5_xboole_0(k2_xboole_0(X19,X20),X19)) )),
% 5.17/1.03    inference(forward_demodulation,[],[f7249,f6558])).
% 5.17/1.03  fof(f6558,plain,(
% 5.17/1.03    ( ! [X33,X34] : (k4_xboole_0(X34,X33) = k4_xboole_0(k2_xboole_0(X33,X34),X33)) )),
% 5.17/1.03    inference(forward_demodulation,[],[f6557,f2269])).
% 5.17/1.03  fof(f2269,plain,(
% 5.17/1.03    ( ! [X35,X36] : (k3_xboole_0(k2_xboole_0(X35,X36),X36) = X36) )),
% 5.17/1.03    inference(forward_demodulation,[],[f2251,f391])).
% 5.17/1.03  fof(f391,plain,(
% 5.17/1.03    ( ! [X10,X9] : (k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9) )),
% 5.17/1.03    inference(superposition,[],[f98,f98])).
% 5.17/1.03  fof(f98,plain,(
% 5.17/1.03    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 5.17/1.03    inference(superposition,[],[f94,f21])).
% 5.17/1.03  fof(f21,plain,(
% 5.17/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 5.17/1.03    inference(cnf_transformation,[],[f1])).
% 5.17/1.03  fof(f1,axiom,(
% 5.17/1.03    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 5.17/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 5.17/1.03  fof(f94,plain,(
% 5.17/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 5.17/1.03    inference(forward_demodulation,[],[f76,f27])).
% 5.17/1.03  fof(f27,plain,(
% 5.17/1.03    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 5.17/1.03    inference(superposition,[],[f21,f19])).
% 5.17/1.03  fof(f76,plain,(
% 5.17/1.03    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 5.17/1.03    inference(superposition,[],[f26,f17])).
% 5.17/1.03  fof(f26,plain,(
% 5.17/1.03    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 5.17/1.03    inference(cnf_transformation,[],[f8])).
% 5.17/1.03  fof(f8,axiom,(
% 5.17/1.03    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 5.17/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 5.17/1.03  fof(f2251,plain,(
% 5.17/1.03    ( ! [X35,X36] : (k3_xboole_0(k2_xboole_0(X35,X36),X36) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X35,X36),X36),k2_xboole_0(X35,X36))) )),
% 5.17/1.03    inference(superposition,[],[f102,f542])).
% 5.17/1.03  fof(f542,plain,(
% 5.17/1.03    ( ! [X14,X13] : (k2_xboole_0(X14,X13) = k2_xboole_0(k2_xboole_0(X14,X13),X13)) )),
% 5.17/1.03    inference(forward_demodulation,[],[f535,f146])).
% 5.17/1.03  fof(f146,plain,(
% 5.17/1.03    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.17/1.03    inference(forward_demodulation,[],[f144,f19])).
% 5.17/1.03  fof(f144,plain,(
% 5.17/1.03    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0)) )),
% 5.17/1.03    inference(backward_demodulation,[],[f51,f135])).
% 5.17/1.03  fof(f135,plain,(
% 5.17/1.03    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 5.17/1.03    inference(backward_demodulation,[],[f37,f128])).
% 5.17/1.03  fof(f51,plain,(
% 5.17/1.03    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k4_xboole_0(X0,X0))) )),
% 5.17/1.03    inference(forward_demodulation,[],[f48,f19])).
% 5.17/1.03  fof(f48,plain,(
% 5.17/1.03    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0))) )),
% 5.17/1.03    inference(superposition,[],[f24,f37])).
% 5.17/1.03  fof(f24,plain,(
% 5.17/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 5.17/1.03    inference(cnf_transformation,[],[f10])).
% 5.17/1.03  fof(f10,axiom,(
% 5.17/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.17/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 5.17/1.03  fof(f535,plain,(
% 5.17/1.03    ( ! [X14,X13] : (k2_xboole_0(k2_xboole_0(X14,X13),X13) = k2_xboole_0(k2_xboole_0(X14,X13),k1_xboole_0)) )),
% 5.17/1.03    inference(superposition,[],[f22,f142])).
% 5.17/1.03  fof(f142,plain,(
% 5.17/1.03    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,X3))) )),
% 5.17/1.03    inference(backward_demodulation,[],[f70,f128])).
% 5.17/1.03  fof(f70,plain,(
% 5.17/1.03    ( ! [X4,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),k1_xboole_0) = k4_xboole_0(X3,k2_xboole_0(X4,X3))) )),
% 5.17/1.03    inference(forward_demodulation,[],[f57,f22])).
% 5.17/1.03  fof(f57,plain,(
% 5.17/1.03    ( ! [X4,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),k1_xboole_0) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X4)))) )),
% 5.17/1.03    inference(superposition,[],[f25,f37])).
% 5.17/1.03  fof(f102,plain,(
% 5.17/1.03    ( ! [X10,X9] : (k3_xboole_0(X9,X10) = k5_xboole_0(k5_xboole_0(X9,X10),k2_xboole_0(X9,X10))) )),
% 5.17/1.03    inference(superposition,[],[f94,f24])).
% 5.17/1.03  fof(f6557,plain,(
% 5.17/1.03    ( ! [X33,X34] : (k4_xboole_0(k2_xboole_0(X33,X34),X33) = k4_xboole_0(k3_xboole_0(k2_xboole_0(X33,X34),X34),X33)) )),
% 5.17/1.03    inference(forward_demodulation,[],[f6458,f18])).
% 5.17/1.03  fof(f6458,plain,(
% 5.17/1.03    ( ! [X33,X34] : (k4_xboole_0(k3_xboole_0(k2_xboole_0(X33,X34),X34),X33) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X33,X34),X33),k1_xboole_0)) )),
% 5.17/1.03    inference(superposition,[],[f6237,f135])).
% 5.17/1.03  fof(f6237,plain,(
% 5.17/1.03    ( ! [X4,X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4))) = k4_xboole_0(k3_xboole_0(X2,X4),X3)) )),
% 5.17/1.03    inference(backward_demodulation,[],[f62,f6236])).
% 5.17/1.03  fof(f6236,plain,(
% 5.17/1.03    ( ! [X8,X7,X9] : (k3_xboole_0(k4_xboole_0(X7,X8),X9) = k4_xboole_0(k3_xboole_0(X7,X9),X8)) )),
% 5.17/1.03    inference(forward_demodulation,[],[f6235,f6098])).
% 5.17/1.03  fof(f6098,plain,(
% 5.17/1.03    ( ! [X21,X19,X20] : (k4_xboole_0(k3_xboole_0(X19,X20),X21) = k4_xboole_0(X19,k2_xboole_0(X21,k4_xboole_0(X19,X20)))) )),
% 5.17/1.03    inference(superposition,[],[f904,f53])).
% 5.17/1.03  fof(f53,plain,(
% 5.17/1.03    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4)) = k4_xboole_0(k3_xboole_0(X2,X3),X4)) )),
% 5.17/1.03    inference(superposition,[],[f25,f23])).
% 5.17/1.03  fof(f904,plain,(
% 5.17/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_xboole_0(X0,X1)) = k4_xboole_0(X2,k2_xboole_0(X1,X0))) )),
% 5.17/1.03    inference(forward_demodulation,[],[f869,f859])).
% 5.17/1.03  fof(f859,plain,(
% 5.17/1.03    ( ! [X6,X5] : (k2_xboole_0(X6,X5) = k2_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 5.17/1.03    inference(forward_demodulation,[],[f856,f98])).
% 5.17/1.03  fof(f856,plain,(
% 5.17/1.03    ( ! [X6,X5] : (k2_xboole_0(X5,k2_xboole_0(X6,X5)) = k5_xboole_0(X5,k5_xboole_0(k2_xboole_0(X6,X5),X5))) )),
% 5.17/1.03    inference(superposition,[],[f83,f540])).
% 5.17/1.03  fof(f540,plain,(
% 5.17/1.03    ( ! [X12,X11] : (k3_xboole_0(X11,k2_xboole_0(X12,X11)) = X11) )),
% 5.17/1.03    inference(forward_demodulation,[],[f534,f18])).
% 5.17/1.03  fof(f534,plain,(
% 5.17/1.03    ( ! [X12,X11] : (k3_xboole_0(X11,k2_xboole_0(X12,X11)) = k4_xboole_0(X11,k1_xboole_0)) )),
% 5.17/1.03    inference(superposition,[],[f23,f142])).
% 5.17/1.03  fof(f83,plain,(
% 5.17/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 5.17/1.03    inference(superposition,[],[f26,f24])).
% 5.17/1.03  fof(f869,plain,(
% 5.17/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_xboole_0(X0,X1)) = k4_xboole_0(X2,k2_xboole_0(X0,k2_xboole_0(X1,X0)))) )),
% 5.17/1.03    inference(superposition,[],[f69,f147])).
% 5.17/1.03  fof(f147,plain,(
% 5.17/1.03    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),X1)) )),
% 5.17/1.03    inference(backward_demodulation,[],[f35,f146])).
% 5.17/1.03  fof(f35,plain,(
% 5.17/1.03    ( ! [X2,X1] : (k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0)) )),
% 5.17/1.03    inference(superposition,[],[f22,f20])).
% 5.17/1.03  fof(f69,plain,(
% 5.17/1.03    ( ! [X12,X10,X13,X11] : (k4_xboole_0(X10,k2_xboole_0(k2_xboole_0(X11,X12),X13)) = k4_xboole_0(X10,k2_xboole_0(X11,k2_xboole_0(X12,X13)))) )),
% 5.17/1.03    inference(forward_demodulation,[],[f68,f25])).
% 5.17/1.03  fof(f68,plain,(
% 5.17/1.03    ( ! [X12,X10,X13,X11] : (k4_xboole_0(k4_xboole_0(X10,X11),k2_xboole_0(X12,X13)) = k4_xboole_0(X10,k2_xboole_0(k2_xboole_0(X11,X12),X13))) )),
% 5.17/1.03    inference(forward_demodulation,[],[f56,f25])).
% 5.17/1.03  fof(f56,plain,(
% 5.17/1.03    ( ! [X12,X10,X13,X11] : (k4_xboole_0(k4_xboole_0(X10,X11),k2_xboole_0(X12,X13)) = k4_xboole_0(k4_xboole_0(X10,k2_xboole_0(X11,X12)),X13)) )),
% 5.17/1.03    inference(superposition,[],[f25,f25])).
% 5.17/1.03  fof(f6235,plain,(
% 5.17/1.03    ( ! [X8,X7,X9] : (k3_xboole_0(k4_xboole_0(X7,X8),X9) = k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,X9)))) )),
% 5.17/1.03    inference(forward_demodulation,[],[f6142,f63])).
% 5.17/1.03  fof(f63,plain,(
% 5.17/1.03    ( ! [X6,X7,X5] : (k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))) )),
% 5.17/1.03    inference(superposition,[],[f22,f25])).
% 5.17/1.03  fof(f6142,plain,(
% 5.17/1.03    ( ! [X8,X7,X9] : (k3_xboole_0(k4_xboole_0(X7,X8),X9) = k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,k2_xboole_0(X9,X8))))) )),
% 5.17/1.03    inference(superposition,[],[f71,f904])).
% 5.17/1.03  fof(f71,plain,(
% 5.17/1.03    ( ! [X6,X7,X5] : (k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,k2_xboole_0(X6,X7))))) )),
% 5.17/1.03    inference(forward_demodulation,[],[f58,f25])).
% 5.17/1.03  fof(f58,plain,(
% 5.17/1.03    ( ! [X6,X7,X5] : (k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(k4_xboole_0(X5,X6),X7)))) )),
% 5.17/1.03    inference(superposition,[],[f25,f23])).
% 5.17/1.03  fof(f62,plain,(
% 5.17/1.03    ( ! [X4,X2,X3] : (k3_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4)))) )),
% 5.17/1.03    inference(superposition,[],[f23,f25])).
% 5.17/1.03  fof(f7249,plain,(
% 5.17/1.03    ( ! [X19,X20] : (k5_xboole_0(k2_xboole_0(X19,X20),X19) = k4_xboole_0(k2_xboole_0(X19,X20),X19)) )),
% 5.17/1.03    inference(superposition,[],[f4649,f1790])).
% 5.17/1.03  fof(f1790,plain,(
% 5.17/1.03    ( ! [X17,X18] : (k3_xboole_0(k2_xboole_0(X17,X18),X17) = X17) )),
% 5.17/1.03    inference(forward_demodulation,[],[f1745,f391])).
% 5.17/1.03  fof(f1745,plain,(
% 5.17/1.03    ( ! [X17,X18] : (k3_xboole_0(k2_xboole_0(X17,X18),X17) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X17,X18),X17),k2_xboole_0(X17,X18))) )),
% 5.17/1.03    inference(superposition,[],[f102,f147])).
% 5.17/1.03  fof(f4649,plain,(
% 5.17/1.03    ( ! [X28,X27] : (k4_xboole_0(X27,X28) = k5_xboole_0(X27,k3_xboole_0(X27,X28))) )),
% 5.17/1.03    inference(forward_demodulation,[],[f4648,f19])).
% 5.17/1.03  fof(f4648,plain,(
% 5.17/1.03    ( ! [X28,X27] : (k5_xboole_0(X27,k3_xboole_0(X27,X28)) = k5_xboole_0(k4_xboole_0(X27,X28),k1_xboole_0)) )),
% 5.17/1.03    inference(forward_demodulation,[],[f4647,f1160])).
% 5.17/1.03  fof(f1160,plain,(
% 5.17/1.03    ( ! [X2,X1] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))) )),
% 5.17/1.03    inference(superposition,[],[f827,f23])).
% 5.17/1.03  fof(f827,plain,(
% 5.17/1.03    ( ! [X10,X9] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X10,X9),X9)) )),
% 5.17/1.03    inference(forward_demodulation,[],[f788,f135])).
% 5.17/1.03  fof(f788,plain,(
% 5.17/1.03    ( ! [X10,X9] : (k3_xboole_0(k4_xboole_0(X10,X9),X9) = k4_xboole_0(k4_xboole_0(X10,X9),k4_xboole_0(X10,X9))) )),
% 5.17/1.03    inference(superposition,[],[f62,f149])).
% 5.17/1.03  fof(f149,plain,(
% 5.17/1.03    ( ! [X1] : (k2_xboole_0(X1,X1) = X1) )),
% 5.17/1.03    inference(forward_demodulation,[],[f137,f146])).
% 5.17/1.03  fof(f137,plain,(
% 5.17/1.03    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,X1)) )),
% 5.17/1.03    inference(backward_demodulation,[],[f50,f128])).
% 5.17/1.03  fof(f50,plain,(
% 5.17/1.03    ( ! [X1] : (k2_xboole_0(X1,X1) = k2_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) )),
% 5.17/1.03    inference(superposition,[],[f22,f37])).
% 5.17/1.03  fof(f4647,plain,(
% 5.17/1.03    ( ! [X28,X27] : (k5_xboole_0(k4_xboole_0(X27,X28),k3_xboole_0(k3_xboole_0(X27,X28),k4_xboole_0(X27,X28))) = k5_xboole_0(X27,k3_xboole_0(X27,X28))) )),
% 5.17/1.03    inference(forward_demodulation,[],[f4550,f21])).
% 5.17/1.03  fof(f4550,plain,(
% 5.17/1.03    ( ! [X28,X27] : (k5_xboole_0(k4_xboole_0(X27,X28),k3_xboole_0(k3_xboole_0(X27,X28),k4_xboole_0(X27,X28))) = k5_xboole_0(k3_xboole_0(X27,X28),X27)) )),
% 5.17/1.03    inference(superposition,[],[f367,f2492])).
% 5.17/1.03  fof(f2492,plain,(
% 5.17/1.03    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 5.17/1.03    inference(backward_demodulation,[],[f1831,f2490])).
% 5.17/1.03  fof(f2490,plain,(
% 5.17/1.03    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0) )),
% 5.17/1.03    inference(forward_demodulation,[],[f2480,f391])).
% 5.17/1.03  fof(f2480,plain,(
% 5.17/1.03    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = k5_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),X0),k3_xboole_0(X0,X1))) )),
% 5.17/1.03    inference(superposition,[],[f24,f681])).
% 5.17/1.03  fof(f681,plain,(
% 5.17/1.03    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X2)) )),
% 5.17/1.03    inference(forward_demodulation,[],[f673,f18])).
% 5.17/1.03  fof(f673,plain,(
% 5.17/1.03    ( ! [X2,X3] : (k3_xboole_0(k3_xboole_0(X2,X3),X2) = k4_xboole_0(k3_xboole_0(X2,X3),k1_xboole_0)) )),
% 5.17/1.03    inference(superposition,[],[f23,f652])).
% 5.17/1.03  fof(f652,plain,(
% 5.17/1.03    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 5.17/1.03    inference(forward_demodulation,[],[f651,f135])).
% 5.17/1.03  fof(f651,plain,(
% 5.17/1.03    ( ! [X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 5.17/1.03    inference(forward_demodulation,[],[f623,f53])).
% 5.17/1.03  fof(f623,plain,(
% 5.17/1.03    ( ! [X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X0))) )),
% 5.17/1.03    inference(superposition,[],[f53,f40])).
% 5.17/1.03  fof(f40,plain,(
% 5.17/1.03    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 5.17/1.03    inference(superposition,[],[f22,f23])).
% 5.17/1.03  fof(f1831,plain,(
% 5.17/1.03    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 5.17/1.03    inference(superposition,[],[f22,f1776])).
% 5.17/1.03  fof(f1776,plain,(
% 5.17/1.03    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 5.17/1.03    inference(backward_demodulation,[],[f39,f1775])).
% 5.17/1.03  fof(f1775,plain,(
% 5.17/1.03    ( ! [X6,X7] : (k4_xboole_0(X6,X7) = k3_xboole_0(X6,k4_xboole_0(X6,X7))) )),
% 5.17/1.03    inference(forward_demodulation,[],[f1739,f391])).
% 5.17/1.03  fof(f1739,plain,(
% 5.17/1.03    ( ! [X6,X7] : (k3_xboole_0(X6,k4_xboole_0(X6,X7)) = k5_xboole_0(k5_xboole_0(X6,k4_xboole_0(X6,X7)),X6)) )),
% 5.17/1.03    inference(superposition,[],[f102,f711])).
% 5.17/1.03  fof(f711,plain,(
% 5.17/1.03    ( ! [X6,X5] : (k2_xboole_0(X5,k4_xboole_0(X5,X6)) = X5) )),
% 5.17/1.03    inference(forward_demodulation,[],[f692,f146])).
% 5.17/1.03  fof(f692,plain,(
% 5.17/1.03    ( ! [X6,X5] : (k2_xboole_0(X5,k1_xboole_0) = k2_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 5.17/1.03    inference(superposition,[],[f63,f142])).
% 5.17/1.03  fof(f39,plain,(
% 5.17/1.03    ( ! [X4,X3] : (k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 5.17/1.03    inference(superposition,[],[f23,f23])).
% 5.17/1.03  fof(f5038,plain,(
% 5.17/1.03    ( ! [X10,X9] : (k5_xboole_0(k2_xboole_0(X9,X10),X9) = k5_xboole_0(k3_xboole_0(X9,X10),X10)) )),
% 5.17/1.03    inference(superposition,[],[f442,f81])).
% 5.17/1.03  fof(f81,plain,(
% 5.17/1.03    ( ! [X14,X12,X13] : (k5_xboole_0(k5_xboole_0(X12,X13),k5_xboole_0(k3_xboole_0(X12,X13),X14)) = k5_xboole_0(k2_xboole_0(X12,X13),X14)) )),
% 5.17/1.03    inference(superposition,[],[f26,f24])).
% 5.17/1.03  fof(f442,plain,(
% 5.17/1.03    ( ! [X10,X8,X9] : (k5_xboole_0(X10,X9) = k5_xboole_0(k5_xboole_0(X8,X9),k5_xboole_0(X10,X8))) )),
% 5.17/1.03    inference(superposition,[],[f86,f94])).
% 5.17/1.03  fof(f86,plain,(
% 5.17/1.03    ( ! [X10,X11,X9] : (k5_xboole_0(X11,k5_xboole_0(X9,X10)) = k5_xboole_0(X9,k5_xboole_0(X10,X11))) )),
% 5.17/1.03    inference(superposition,[],[f26,f21])).
% 5.17/1.03  fof(f5639,plain,(
% 5.17/1.03    ( ! [X6,X5] : (k5_xboole_0(k3_xboole_0(X5,X6),X6) = k5_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 5.17/1.03    inference(superposition,[],[f492,f83])).
% 5.17/1.03  fof(f492,plain,(
% 5.17/1.03    ( ! [X10,X8,X9] : (k5_xboole_0(X10,X9) = k5_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(X9,X10)))) )),
% 5.17/1.03    inference(forward_demodulation,[],[f418,f26])).
% 5.17/1.03  fof(f418,plain,(
% 5.17/1.03    ( ! [X10,X8,X9] : (k5_xboole_0(X10,X9) = k5_xboole_0(X8,k5_xboole_0(k5_xboole_0(X8,X9),X10))) )),
% 5.17/1.03    inference(superposition,[],[f86,f94])).
% 5.17/1.03  fof(f367,plain,(
% 5.17/1.03    ( ! [X15,X16] : (k5_xboole_0(X16,k3_xboole_0(X15,X16)) = k5_xboole_0(X15,k2_xboole_0(X15,X16))) )),
% 5.17/1.03    inference(superposition,[],[f94,f83])).
% 5.17/1.03  fof(f1719,plain,(
% 5.17/1.03    ( ! [X8,X7] : (k3_xboole_0(X7,k5_xboole_0(X8,k3_xboole_0(X7,X8))) = k5_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,k5_xboole_0(X8,k3_xboole_0(X7,X8))))) )),
% 5.17/1.03    inference(superposition,[],[f102,f83])).
% 5.17/1.03  fof(f6395,plain,(
% 5.17/1.03    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X2,X1),k3_xboole_0(X1,k4_xboole_0(X2,X1))))) )),
% 5.17/1.03    inference(backward_demodulation,[],[f4675,f6394])).
% 5.17/1.03  fof(f6394,plain,(
% 5.17/1.03    ( ! [X37,X38,X36] : (k2_xboole_0(X38,X36) = k2_xboole_0(k2_xboole_0(X38,X36),k3_xboole_0(X36,X37))) )),
% 5.17/1.03    inference(forward_demodulation,[],[f6372,f146])).
% 5.17/1.03  fof(f6372,plain,(
% 5.17/1.03    ( ! [X37,X38,X36] : (k2_xboole_0(k2_xboole_0(X38,X36),k3_xboole_0(X36,X37)) = k2_xboole_0(k2_xboole_0(X38,X36),k1_xboole_0)) )),
% 5.17/1.03    inference(superposition,[],[f22,f2788])).
% 5.17/1.03  fof(f2788,plain,(
% 5.17/1.03    ( ! [X4,X5,X3] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X3,X4),k2_xboole_0(X5,X3))) )),
% 5.17/1.03    inference(superposition,[],[f59,f2606])).
% 5.17/1.03  fof(f2606,plain,(
% 5.17/1.03    ( ! [X14,X15,X13] : (k2_xboole_0(k4_xboole_0(k3_xboole_0(X13,X14),X15),X13) = X13) )),
% 5.17/1.03    inference(superposition,[],[f2562,f53])).
% 5.17/1.03  fof(f2562,plain,(
% 5.17/1.03    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 5.17/1.03    inference(backward_demodulation,[],[f40,f2561])).
% 5.17/1.03  fof(f2561,plain,(
% 5.17/1.03    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1) )),
% 5.17/1.03    inference(forward_demodulation,[],[f2513,f1775])).
% 5.17/1.03  fof(f2513,plain,(
% 5.17/1.03    ( ! [X2,X1] : (k2_xboole_0(k3_xboole_0(X1,k4_xboole_0(X1,X2)),k3_xboole_0(X1,X2)) = X1) )),
% 5.17/1.03    inference(superposition,[],[f2492,f23])).
% 5.17/1.03  fof(f59,plain,(
% 5.17/1.03    ( ! [X10,X8,X9] : (k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,k2_xboole_0(k4_xboole_0(X8,X9),X10)))) )),
% 5.17/1.03    inference(superposition,[],[f25,f20])).
% 5.17/1.03  fof(f4675,plain,(
% 5.17/1.03    ( ! [X2,X1] : (k2_xboole_0(k2_xboole_0(X2,X1),k3_xboole_0(X1,k4_xboole_0(X2,X1))) = k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X2,X1),k3_xboole_0(X1,k4_xboole_0(X2,X1))))) )),
% 5.17/1.03    inference(backward_demodulation,[],[f1374,f4650])).
% 5.17/1.03  fof(f4650,plain,(
% 5.17/1.03    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k5_xboole_0(X3,k4_xboole_0(X4,X3))) )),
% 5.17/1.03    inference(backward_demodulation,[],[f237,f4649])).
% 5.17/1.03  fof(f237,plain,(
% 5.17/1.03    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3)))) )),
% 5.17/1.03    inference(superposition,[],[f44,f26])).
% 5.17/1.03  fof(f44,plain,(
% 5.17/1.03    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k5_xboole_0(k5_xboole_0(X3,X2),k3_xboole_0(X2,X3))) )),
% 5.17/1.03    inference(superposition,[],[f24,f21])).
% 5.17/1.03  fof(f1374,plain,(
% 5.17/1.03    ( ! [X2,X1] : (k2_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k3_xboole_0(X1,k4_xboole_0(X2,X1))) = k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k3_xboole_0(X1,k4_xboole_0(X2,X1))))) )),
% 5.17/1.03    inference(superposition,[],[f47,f22])).
% 5.17/1.03  fof(f47,plain,(
% 5.17/1.03    ( ! [X8,X7] : (k2_xboole_0(k5_xboole_0(X7,X8),k3_xboole_0(X7,X8)) = k5_xboole_0(k2_xboole_0(X7,X8),k3_xboole_0(k5_xboole_0(X7,X8),k3_xboole_0(X7,X8)))) )),
% 5.17/1.03    inference(superposition,[],[f24,f24])).
% 5.17/1.03  fof(f4772,plain,(
% 5.17/1.03    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK0)),
% 5.17/1.03    inference(superposition,[],[f16,f4650])).
% 5.17/1.03  fof(f16,plain,(
% 5.17/1.03    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 5.17/1.03    inference(cnf_transformation,[],[f15])).
% 5.17/1.03  fof(f15,plain,(
% 5.17/1.03    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 5.17/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 5.17/1.03  fof(f14,plain,(
% 5.17/1.03    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 5.17/1.03    introduced(choice_axiom,[])).
% 5.17/1.03  fof(f13,plain,(
% 5.17/1.03    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 5.17/1.03    inference(ennf_transformation,[],[f12])).
% 5.17/1.03  fof(f12,negated_conjecture,(
% 5.17/1.03    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 5.17/1.03    inference(negated_conjecture,[],[f11])).
% 5.17/1.03  fof(f11,conjecture,(
% 5.17/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 5.17/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 5.17/1.03  % SZS output end Proof for theBenchmark
% 5.17/1.03  % (5905)------------------------------
% 5.17/1.03  % (5905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.17/1.03  % (5905)Termination reason: Refutation
% 5.17/1.03  
% 5.17/1.03  % (5905)Memory used [KB]: 12153
% 5.17/1.03  % (5905)Time elapsed: 0.612 s
% 5.17/1.03  % (5905)------------------------------
% 5.17/1.03  % (5905)------------------------------
% 5.17/1.03  % (5901)Success in time 0.672 s
%------------------------------------------------------------------------------
