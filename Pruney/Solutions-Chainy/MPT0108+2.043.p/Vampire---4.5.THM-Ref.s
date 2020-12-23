%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:24 EST 2020

% Result     : Theorem 5.71s
% Output     : Refutation 5.71s
% Verified   : 
% Statistics : Number of formulae       :   94 (5962 expanded)
%              Number of leaves         :   12 (1942 expanded)
%              Depth                    :   31
%              Number of atoms          :   95 (5963 expanded)
%              Number of equality atoms :   94 (5962 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20825,plain,(
    $false ),
    inference(subsumption_resolution,[],[f18,f20824])).

fof(f20824,plain,(
    ! [X59,X60] : k5_xboole_0(X59,X60) = k4_xboole_0(k2_xboole_0(X59,X60),k3_xboole_0(X59,X60)) ),
    inference(backward_demodulation,[],[f15863,f20655])).

fof(f20655,plain,(
    ! [X10,X11] : k5_xboole_0(X11,X10) = k5_xboole_0(k2_xboole_0(X11,X10),k3_xboole_0(X11,X10)) ),
    inference(superposition,[],[f982,f1386])).

fof(f1386,plain,(
    ! [X4,X3] : k5_xboole_0(k4_xboole_0(X3,X4),k3_xboole_0(X4,X3)) = X3 ),
    inference(superposition,[],[f1252,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f25,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1252,plain,(
    ! [X10,X9] : k5_xboole_0(k5_xboole_0(X9,X10),X10) = X9 ),
    inference(superposition,[],[f1237,f1002])).

fof(f1002,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f979,f621])).

fof(f621,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(backward_demodulation,[],[f80,f620])).

fof(f620,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f619,f20])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f619,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f592,f76])).

fof(f76,plain,(
    ! [X2] : k3_xboole_0(X2,X2) = X2 ),
    inference(backward_demodulation,[],[f37,f74])).

fof(f74,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f70,f34])).

fof(f34,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f33,f20])).

fof(f33,plain,(
    ! [X2] : k2_xboole_0(X2,X2) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f23,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f21,f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f21,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f70,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f25,f65])).

fof(f65,plain,(
    ! [X4] : k1_xboole_0 = k3_xboole_0(X4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f64,f30])).

fof(f64,plain,(
    ! [X4] : k4_xboole_0(X4,X4) = k3_xboole_0(X4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f61,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f61,plain,(
    ! [X4] : k4_xboole_0(X4,X4) = k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)) ),
    inference(superposition,[],[f26,f37])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f37,plain,(
    ! [X2] : k3_xboole_0(X2,X2) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f24,f30])).

fof(f592,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f27,f75])).

fof(f75,plain,(
    ! [X4] : k1_xboole_0 = k5_xboole_0(X4,X4) ),
    inference(backward_demodulation,[],[f49,f74])).

fof(f49,plain,(
    ! [X4] : k1_xboole_0 = k5_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f47,f30])).

fof(f47,plain,(
    ! [X4] : k4_xboole_0(X4,X4) = k5_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)) ),
    inference(superposition,[],[f25,f37])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f80,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f44,f76])).

fof(f44,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X1)) ),
    inference(superposition,[],[f23,f37])).

fof(f979,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f28,f75])).

fof(f28,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1237,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f1219,f34])).

fof(f1219,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f1002,f988])).

fof(f988,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f28,f75])).

fof(f982,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X8,k5_xboole_0(k4_xboole_0(X9,X8),X10)) = k5_xboole_0(k2_xboole_0(X8,X9),X10) ),
    inference(superposition,[],[f28,f23])).

fof(f15863,plain,(
    ! [X59,X60] : k5_xboole_0(k2_xboole_0(X59,X60),k3_xboole_0(X59,X60)) = k4_xboole_0(k2_xboole_0(X59,X60),k3_xboole_0(X59,X60)) ),
    inference(backward_demodulation,[],[f13742,f15765])).

fof(f15765,plain,(
    ! [X87,X86] : k4_xboole_0(k5_xboole_0(X86,X87),k3_xboole_0(X86,X87)) = k4_xboole_0(k2_xboole_0(X86,X87),k3_xboole_0(X86,X87)) ),
    inference(superposition,[],[f12806,f27])).

fof(f12806,plain,(
    ! [X26,X25] : k4_xboole_0(X26,X25) = k4_xboole_0(k2_xboole_0(X26,X25),X25) ),
    inference(superposition,[],[f1430,f12646])).

fof(f12646,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(superposition,[],[f12133,f1592])).

fof(f1592,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k5_xboole_0(k4_xboole_0(X2,X1),X1) ),
    inference(forward_demodulation,[],[f1579,f1335])).

fof(f1335,plain,(
    ! [X12,X11] : k2_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X12,X11),X11) ),
    inference(backward_demodulation,[],[f1022,f1323])).

fof(f1323,plain,(
    ! [X21,X20] : k2_xboole_0(X20,X21) = k2_xboole_0(X20,k2_xboole_0(X20,X21)) ),
    inference(superposition,[],[f1266,f335])).

fof(f335,plain,(
    ! [X12,X11] : k3_xboole_0(k2_xboole_0(X11,X12),X11) = X11 ),
    inference(superposition,[],[f249,f77])).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(backward_demodulation,[],[f36,f74])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f24,f21])).

fof(f249,plain,(
    ! [X2,X1] : k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f67,f22])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f62,f24])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f24,f26])).

fof(f1266,plain,(
    ! [X2,X3] : k2_xboole_0(k3_xboole_0(X2,X3),X2) = X2 ),
    inference(backward_demodulation,[],[f63,f1248])).

fof(f1248,plain,(
    ! [X2,X1] : k5_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(superposition,[],[f1237,f25])).

fof(f63,plain,(
    ! [X2,X3] : k2_xboole_0(k3_xboole_0(X2,X3),X2) = k5_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f23,f26])).

fof(f1022,plain,(
    ! [X12,X11] : k2_xboole_0(X11,k2_xboole_0(X11,X12)) = k2_xboole_0(k4_xboole_0(X12,X11),X11) ),
    inference(backward_demodulation,[],[f606,f1009])).

fof(f1009,plain,(
    ! [X6,X5] : k4_xboole_0(X6,X5) = k5_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f1002,f23])).

fof(f606,plain,(
    ! [X12,X11] : k2_xboole_0(X11,k2_xboole_0(X11,X12)) = k2_xboole_0(k5_xboole_0(X11,k2_xboole_0(X11,X12)),X11) ),
    inference(superposition,[],[f27,f77])).

fof(f1579,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X2,X1),X1) = k5_xboole_0(k4_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f23,f1553])).

fof(f1553,plain,(
    ! [X24,X25] : k4_xboole_0(X25,k4_xboole_0(X24,X25)) = X25 ),
    inference(backward_demodulation,[],[f1522,f1552])).

fof(f1552,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = X2 ),
    inference(forward_demodulation,[],[f1551,f77])).

fof(f1551,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f1526,f22])).

fof(f1526,plain,(
    ! [X2,X3] : k3_xboole_0(k2_xboole_0(X2,X3),X2) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) ),
    inference(superposition,[],[f24,f1430])).

fof(f1522,plain,(
    ! [X24,X25] : k4_xboole_0(X25,k4_xboole_0(X24,X25)) = k4_xboole_0(k2_xboole_0(X25,X24),k4_xboole_0(X24,X25)) ),
    inference(superposition,[],[f1430,f1335])).

fof(f12133,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k5_xboole_0(k4_xboole_0(X2,X3),X3) ),
    inference(forward_demodulation,[],[f11994,f23])).

fof(f11994,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X2,X3),X3) = k5_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(superposition,[],[f980,f2178])).

fof(f2178,plain,(
    ! [X17,X16] : k4_xboole_0(X16,X17) = k5_xboole_0(k3_xboole_0(X17,X16),X16) ),
    inference(superposition,[],[f1253,f1008])).

fof(f1008,plain,(
    ! [X4,X3] : k3_xboole_0(X4,X3) = k5_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f1002,f45])).

fof(f1253,plain,(
    ! [X12,X11] : k5_xboole_0(k5_xboole_0(X12,X11),X12) = X11 ),
    inference(superposition,[],[f1237,f1237])).

fof(f980,plain,(
    ! [X4,X2,X3] : k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X3),X4)) = k5_xboole_0(k4_xboole_0(X2,X3),X4) ),
    inference(superposition,[],[f28,f25])).

fof(f1430,plain,(
    ! [X6,X5] : k4_xboole_0(k2_xboole_0(X5,X6),X5) = k4_xboole_0(X6,X5) ),
    inference(backward_demodulation,[],[f138,f1412])).

fof(f1412,plain,(
    ! [X6,X5] : k5_xboole_0(k2_xboole_0(X5,X6),X5) = k4_xboole_0(X6,X5) ),
    inference(superposition,[],[f1253,f23])).

fof(f138,plain,(
    ! [X6,X5] : k4_xboole_0(k2_xboole_0(X5,X6),X5) = k5_xboole_0(k2_xboole_0(X5,X6),X5) ),
    inference(superposition,[],[f45,f77])).

fof(f13742,plain,(
    ! [X59,X60] : k4_xboole_0(k5_xboole_0(X59,X60),k3_xboole_0(X59,X60)) = k5_xboole_0(k2_xboole_0(X59,X60),k3_xboole_0(X59,X60)) ),
    inference(superposition,[],[f12662,f27])).

fof(f12662,plain,(
    ! [X24,X23] : k4_xboole_0(X23,X24) = k5_xboole_0(k2_xboole_0(X23,X24),X24) ),
    inference(superposition,[],[f1252,f12133])).

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
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:48:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (13729)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (13730)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (13739)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (13736)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (13731)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (13728)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (13737)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (13735)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (13738)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (13735)Refutation not found, incomplete strategy% (13735)------------------------------
% 0.20/0.48  % (13735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (13735)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (13735)Memory used [KB]: 10490
% 0.20/0.48  % (13735)Time elapsed: 0.029 s
% 0.20/0.48  % (13735)------------------------------
% 0.20/0.48  % (13735)------------------------------
% 0.20/0.49  % (13726)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (13732)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (13725)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.50  % (13734)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (13741)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (13727)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.51  % (13733)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.52  % (13724)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.52  % (13740)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 4.83/1.03  % (13728)Time limit reached!
% 4.83/1.03  % (13728)------------------------------
% 4.83/1.03  % (13728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.83/1.03  % (13728)Termination reason: Time limit
% 4.83/1.03  % (13728)Termination phase: Saturation
% 4.83/1.03  
% 4.83/1.03  % (13728)Memory used [KB]: 16502
% 4.83/1.03  % (13728)Time elapsed: 0.600 s
% 4.83/1.03  % (13728)------------------------------
% 4.83/1.03  % (13728)------------------------------
% 5.71/1.09  % (13740)Refutation found. Thanks to Tanya!
% 5.71/1.09  % SZS status Theorem for theBenchmark
% 5.71/1.09  % SZS output start Proof for theBenchmark
% 5.71/1.09  fof(f20825,plain,(
% 5.71/1.09    $false),
% 5.71/1.09    inference(subsumption_resolution,[],[f18,f20824])).
% 5.71/1.09  fof(f20824,plain,(
% 5.71/1.09    ( ! [X59,X60] : (k5_xboole_0(X59,X60) = k4_xboole_0(k2_xboole_0(X59,X60),k3_xboole_0(X59,X60))) )),
% 5.71/1.09    inference(backward_demodulation,[],[f15863,f20655])).
% 5.71/1.09  fof(f20655,plain,(
% 5.71/1.09    ( ! [X10,X11] : (k5_xboole_0(X11,X10) = k5_xboole_0(k2_xboole_0(X11,X10),k3_xboole_0(X11,X10))) )),
% 5.71/1.09    inference(superposition,[],[f982,f1386])).
% 5.71/1.09  fof(f1386,plain,(
% 5.71/1.09    ( ! [X4,X3] : (k5_xboole_0(k4_xboole_0(X3,X4),k3_xboole_0(X4,X3)) = X3) )),
% 5.71/1.09    inference(superposition,[],[f1252,f45])).
% 5.71/1.09  fof(f45,plain,(
% 5.71/1.09    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 5.71/1.09    inference(superposition,[],[f25,f22])).
% 5.71/1.09  fof(f22,plain,(
% 5.71/1.09    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.71/1.09    inference(cnf_transformation,[],[f1])).
% 5.71/1.09  fof(f1,axiom,(
% 5.71/1.09    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.71/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.71/1.09  fof(f25,plain,(
% 5.71/1.09    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.71/1.09    inference(cnf_transformation,[],[f3])).
% 5.71/1.09  fof(f3,axiom,(
% 5.71/1.09    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.71/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 5.71/1.09  fof(f1252,plain,(
% 5.71/1.09    ( ! [X10,X9] : (k5_xboole_0(k5_xboole_0(X9,X10),X10) = X9) )),
% 5.71/1.09    inference(superposition,[],[f1237,f1002])).
% 5.71/1.09  fof(f1002,plain,(
% 5.71/1.09    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 5.71/1.09    inference(forward_demodulation,[],[f979,f621])).
% 5.71/1.09  fof(f621,plain,(
% 5.71/1.09    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 5.71/1.09    inference(backward_demodulation,[],[f80,f620])).
% 5.71/1.09  fof(f620,plain,(
% 5.71/1.09    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 5.71/1.09    inference(forward_demodulation,[],[f619,f20])).
% 5.71/1.09  fof(f20,plain,(
% 5.71/1.09    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 5.71/1.09    inference(cnf_transformation,[],[f14])).
% 5.71/1.09  fof(f14,plain,(
% 5.71/1.09    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 5.71/1.09    inference(rectify,[],[f2])).
% 5.71/1.09  fof(f2,axiom,(
% 5.71/1.09    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 5.71/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 5.71/1.09  fof(f619,plain,(
% 5.71/1.09    ( ! [X0] : (k2_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,X0)) )),
% 5.71/1.09    inference(forward_demodulation,[],[f592,f76])).
% 5.71/1.09  fof(f76,plain,(
% 5.71/1.09    ( ! [X2] : (k3_xboole_0(X2,X2) = X2) )),
% 5.71/1.09    inference(backward_demodulation,[],[f37,f74])).
% 5.71/1.09  fof(f74,plain,(
% 5.71/1.09    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 5.71/1.09    inference(forward_demodulation,[],[f70,f34])).
% 5.71/1.09  fof(f34,plain,(
% 5.71/1.09    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = X2) )),
% 5.71/1.09    inference(forward_demodulation,[],[f33,f20])).
% 5.71/1.09  fof(f33,plain,(
% 5.71/1.09    ( ! [X2] : (k2_xboole_0(X2,X2) = k5_xboole_0(X2,k1_xboole_0)) )),
% 5.71/1.09    inference(superposition,[],[f23,f30])).
% 5.71/1.09  fof(f30,plain,(
% 5.71/1.09    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 5.71/1.09    inference(superposition,[],[f21,f19])).
% 5.71/1.09  fof(f19,plain,(
% 5.71/1.09    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.71/1.09    inference(cnf_transformation,[],[f4])).
% 5.71/1.09  fof(f4,axiom,(
% 5.71/1.09    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 5.71/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 5.71/1.09  fof(f21,plain,(
% 5.71/1.09    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 5.71/1.09    inference(cnf_transformation,[],[f5])).
% 5.71/1.09  fof(f5,axiom,(
% 5.71/1.09    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 5.71/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 5.71/1.09  fof(f23,plain,(
% 5.71/1.09    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 5.71/1.09    inference(cnf_transformation,[],[f11])).
% 5.71/1.09  fof(f11,axiom,(
% 5.71/1.09    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 5.71/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 5.71/1.09  fof(f70,plain,(
% 5.71/1.09    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k1_xboole_0)) )),
% 5.71/1.09    inference(superposition,[],[f25,f65])).
% 5.71/1.09  fof(f65,plain,(
% 5.71/1.09    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(X4,k1_xboole_0)) )),
% 5.71/1.09    inference(forward_demodulation,[],[f64,f30])).
% 5.71/1.09  fof(f64,plain,(
% 5.71/1.09    ( ! [X4] : (k4_xboole_0(X4,X4) = k3_xboole_0(X4,k1_xboole_0)) )),
% 5.71/1.09    inference(forward_demodulation,[],[f61,f24])).
% 5.71/1.09  fof(f24,plain,(
% 5.71/1.09    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 5.71/1.09    inference(cnf_transformation,[],[f7])).
% 5.71/1.09  fof(f7,axiom,(
% 5.71/1.09    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.71/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.71/1.09  fof(f61,plain,(
% 5.71/1.09    ( ! [X4] : (k4_xboole_0(X4,X4) = k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0))) )),
% 5.71/1.09    inference(superposition,[],[f26,f37])).
% 5.71/1.09  fof(f26,plain,(
% 5.71/1.09    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.71/1.09    inference(cnf_transformation,[],[f6])).
% 5.71/1.09  fof(f6,axiom,(
% 5.71/1.09    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.71/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 5.71/1.09  fof(f37,plain,(
% 5.71/1.09    ( ! [X2] : (k3_xboole_0(X2,X2) = k4_xboole_0(X2,k1_xboole_0)) )),
% 5.71/1.09    inference(superposition,[],[f24,f30])).
% 5.71/1.09  fof(f592,plain,(
% 5.71/1.09    ( ! [X0] : (k2_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0))) )),
% 5.71/1.09    inference(superposition,[],[f27,f75])).
% 5.71/1.09  fof(f75,plain,(
% 5.71/1.09    ( ! [X4] : (k1_xboole_0 = k5_xboole_0(X4,X4)) )),
% 5.71/1.09    inference(backward_demodulation,[],[f49,f74])).
% 5.71/1.09  fof(f49,plain,(
% 5.71/1.09    ( ! [X4] : (k1_xboole_0 = k5_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0))) )),
% 5.71/1.09    inference(forward_demodulation,[],[f47,f30])).
% 5.71/1.09  fof(f47,plain,(
% 5.71/1.09    ( ! [X4] : (k4_xboole_0(X4,X4) = k5_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0))) )),
% 5.71/1.09    inference(superposition,[],[f25,f37])).
% 5.71/1.09  fof(f27,plain,(
% 5.71/1.09    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 5.71/1.09    inference(cnf_transformation,[],[f10])).
% 5.71/1.09  fof(f10,axiom,(
% 5.71/1.09    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.71/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).
% 5.71/1.09  fof(f80,plain,(
% 5.71/1.09    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,X1)) )),
% 5.71/1.09    inference(backward_demodulation,[],[f44,f76])).
% 5.71/1.09  fof(f44,plain,(
% 5.71/1.09    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X1))) )),
% 5.71/1.09    inference(superposition,[],[f23,f37])).
% 5.71/1.09  fof(f979,plain,(
% 5.71/1.09    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 5.71/1.09    inference(superposition,[],[f28,f75])).
% 5.71/1.09  fof(f28,plain,(
% 5.71/1.09    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 5.71/1.09    inference(cnf_transformation,[],[f9])).
% 5.71/1.09  fof(f9,axiom,(
% 5.71/1.09    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 5.71/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 5.71/1.09  fof(f1237,plain,(
% 5.71/1.09    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 5.71/1.09    inference(forward_demodulation,[],[f1219,f34])).
% 5.71/1.09  fof(f1219,plain,(
% 5.71/1.09    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 5.71/1.09    inference(superposition,[],[f1002,f988])).
% 5.71/1.09  fof(f988,plain,(
% 5.71/1.09    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 5.71/1.09    inference(superposition,[],[f28,f75])).
% 5.71/1.09  fof(f982,plain,(
% 5.71/1.09    ( ! [X10,X8,X9] : (k5_xboole_0(X8,k5_xboole_0(k4_xboole_0(X9,X8),X10)) = k5_xboole_0(k2_xboole_0(X8,X9),X10)) )),
% 5.71/1.09    inference(superposition,[],[f28,f23])).
% 5.71/1.09  fof(f15863,plain,(
% 5.71/1.09    ( ! [X59,X60] : (k5_xboole_0(k2_xboole_0(X59,X60),k3_xboole_0(X59,X60)) = k4_xboole_0(k2_xboole_0(X59,X60),k3_xboole_0(X59,X60))) )),
% 5.71/1.09    inference(backward_demodulation,[],[f13742,f15765])).
% 5.71/1.09  fof(f15765,plain,(
% 5.71/1.09    ( ! [X87,X86] : (k4_xboole_0(k5_xboole_0(X86,X87),k3_xboole_0(X86,X87)) = k4_xboole_0(k2_xboole_0(X86,X87),k3_xboole_0(X86,X87))) )),
% 5.71/1.09    inference(superposition,[],[f12806,f27])).
% 5.71/1.09  fof(f12806,plain,(
% 5.71/1.09    ( ! [X26,X25] : (k4_xboole_0(X26,X25) = k4_xboole_0(k2_xboole_0(X26,X25),X25)) )),
% 5.71/1.09    inference(superposition,[],[f1430,f12646])).
% 5.71/1.09  fof(f12646,plain,(
% 5.71/1.09    ( ! [X4,X5] : (k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4)) )),
% 5.71/1.09    inference(superposition,[],[f12133,f1592])).
% 5.71/1.09  fof(f1592,plain,(
% 5.71/1.09    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k5_xboole_0(k4_xboole_0(X2,X1),X1)) )),
% 5.71/1.09    inference(forward_demodulation,[],[f1579,f1335])).
% 5.71/1.09  fof(f1335,plain,(
% 5.71/1.09    ( ! [X12,X11] : (k2_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X12,X11),X11)) )),
% 5.71/1.09    inference(backward_demodulation,[],[f1022,f1323])).
% 5.71/1.09  fof(f1323,plain,(
% 5.71/1.09    ( ! [X21,X20] : (k2_xboole_0(X20,X21) = k2_xboole_0(X20,k2_xboole_0(X20,X21))) )),
% 5.71/1.09    inference(superposition,[],[f1266,f335])).
% 5.71/1.09  fof(f335,plain,(
% 5.71/1.09    ( ! [X12,X11] : (k3_xboole_0(k2_xboole_0(X11,X12),X11) = X11) )),
% 5.71/1.09    inference(superposition,[],[f249,f77])).
% 5.71/1.09  fof(f77,plain,(
% 5.71/1.09    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 5.71/1.09    inference(backward_demodulation,[],[f36,f74])).
% 5.71/1.09  fof(f36,plain,(
% 5.71/1.09    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k1_xboole_0)) )),
% 5.71/1.09    inference(superposition,[],[f24,f21])).
% 5.71/1.09  fof(f249,plain,(
% 5.71/1.09    ( ! [X2,X1] : (k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 5.71/1.09    inference(superposition,[],[f67,f22])).
% 5.71/1.09  fof(f67,plain,(
% 5.71/1.09    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.71/1.09    inference(forward_demodulation,[],[f62,f24])).
% 5.71/1.09  fof(f62,plain,(
% 5.71/1.09    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.71/1.09    inference(superposition,[],[f24,f26])).
% 5.71/1.09  fof(f1266,plain,(
% 5.71/1.09    ( ! [X2,X3] : (k2_xboole_0(k3_xboole_0(X2,X3),X2) = X2) )),
% 5.71/1.09    inference(backward_demodulation,[],[f63,f1248])).
% 5.71/1.09  fof(f1248,plain,(
% 5.71/1.09    ( ! [X2,X1] : (k5_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1) )),
% 5.71/1.09    inference(superposition,[],[f1237,f25])).
% 5.71/1.09  fof(f63,plain,(
% 5.71/1.09    ( ! [X2,X3] : (k2_xboole_0(k3_xboole_0(X2,X3),X2) = k5_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3))) )),
% 5.71/1.09    inference(superposition,[],[f23,f26])).
% 5.71/1.09  fof(f1022,plain,(
% 5.71/1.09    ( ! [X12,X11] : (k2_xboole_0(X11,k2_xboole_0(X11,X12)) = k2_xboole_0(k4_xboole_0(X12,X11),X11)) )),
% 5.71/1.09    inference(backward_demodulation,[],[f606,f1009])).
% 5.71/1.09  fof(f1009,plain,(
% 5.71/1.09    ( ! [X6,X5] : (k4_xboole_0(X6,X5) = k5_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 5.71/1.09    inference(superposition,[],[f1002,f23])).
% 5.71/1.09  fof(f606,plain,(
% 5.71/1.09    ( ! [X12,X11] : (k2_xboole_0(X11,k2_xboole_0(X11,X12)) = k2_xboole_0(k5_xboole_0(X11,k2_xboole_0(X11,X12)),X11)) )),
% 5.71/1.09    inference(superposition,[],[f27,f77])).
% 5.71/1.09  fof(f1579,plain,(
% 5.71/1.09    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X2,X1),X1) = k5_xboole_0(k4_xboole_0(X2,X1),X1)) )),
% 5.71/1.09    inference(superposition,[],[f23,f1553])).
% 5.71/1.09  fof(f1553,plain,(
% 5.71/1.09    ( ! [X24,X25] : (k4_xboole_0(X25,k4_xboole_0(X24,X25)) = X25) )),
% 5.71/1.09    inference(backward_demodulation,[],[f1522,f1552])).
% 5.71/1.09  fof(f1552,plain,(
% 5.71/1.09    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = X2) )),
% 5.71/1.09    inference(forward_demodulation,[],[f1551,f77])).
% 5.71/1.09  fof(f1551,plain,(
% 5.71/1.09    ( ! [X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2))) )),
% 5.71/1.09    inference(forward_demodulation,[],[f1526,f22])).
% 5.71/1.09  fof(f1526,plain,(
% 5.71/1.09    ( ! [X2,X3] : (k3_xboole_0(k2_xboole_0(X2,X3),X2) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2))) )),
% 5.71/1.09    inference(superposition,[],[f24,f1430])).
% 5.71/1.09  fof(f1522,plain,(
% 5.71/1.09    ( ! [X24,X25] : (k4_xboole_0(X25,k4_xboole_0(X24,X25)) = k4_xboole_0(k2_xboole_0(X25,X24),k4_xboole_0(X24,X25))) )),
% 5.71/1.09    inference(superposition,[],[f1430,f1335])).
% 5.71/1.09  fof(f12133,plain,(
% 5.71/1.09    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k5_xboole_0(k4_xboole_0(X2,X3),X3)) )),
% 5.71/1.09    inference(forward_demodulation,[],[f11994,f23])).
% 5.71/1.09  fof(f11994,plain,(
% 5.71/1.09    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X2,X3),X3) = k5_xboole_0(X2,k4_xboole_0(X3,X2))) )),
% 5.71/1.09    inference(superposition,[],[f980,f2178])).
% 5.71/1.09  fof(f2178,plain,(
% 5.71/1.09    ( ! [X17,X16] : (k4_xboole_0(X16,X17) = k5_xboole_0(k3_xboole_0(X17,X16),X16)) )),
% 5.71/1.09    inference(superposition,[],[f1253,f1008])).
% 5.71/1.09  fof(f1008,plain,(
% 5.71/1.09    ( ! [X4,X3] : (k3_xboole_0(X4,X3) = k5_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 5.71/1.09    inference(superposition,[],[f1002,f45])).
% 5.71/1.09  fof(f1253,plain,(
% 5.71/1.09    ( ! [X12,X11] : (k5_xboole_0(k5_xboole_0(X12,X11),X12) = X11) )),
% 5.71/1.09    inference(superposition,[],[f1237,f1237])).
% 5.71/1.09  fof(f980,plain,(
% 5.71/1.09    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X3),X4)) = k5_xboole_0(k4_xboole_0(X2,X3),X4)) )),
% 5.71/1.09    inference(superposition,[],[f28,f25])).
% 5.71/1.09  fof(f1430,plain,(
% 5.71/1.09    ( ! [X6,X5] : (k4_xboole_0(k2_xboole_0(X5,X6),X5) = k4_xboole_0(X6,X5)) )),
% 5.71/1.09    inference(backward_demodulation,[],[f138,f1412])).
% 5.71/1.09  fof(f1412,plain,(
% 5.71/1.09    ( ! [X6,X5] : (k5_xboole_0(k2_xboole_0(X5,X6),X5) = k4_xboole_0(X6,X5)) )),
% 5.71/1.09    inference(superposition,[],[f1253,f23])).
% 5.71/1.09  fof(f138,plain,(
% 5.71/1.09    ( ! [X6,X5] : (k4_xboole_0(k2_xboole_0(X5,X6),X5) = k5_xboole_0(k2_xboole_0(X5,X6),X5)) )),
% 5.71/1.09    inference(superposition,[],[f45,f77])).
% 5.71/1.09  fof(f13742,plain,(
% 5.71/1.09    ( ! [X59,X60] : (k4_xboole_0(k5_xboole_0(X59,X60),k3_xboole_0(X59,X60)) = k5_xboole_0(k2_xboole_0(X59,X60),k3_xboole_0(X59,X60))) )),
% 5.71/1.09    inference(superposition,[],[f12662,f27])).
% 5.71/1.09  fof(f12662,plain,(
% 5.71/1.09    ( ! [X24,X23] : (k4_xboole_0(X23,X24) = k5_xboole_0(k2_xboole_0(X23,X24),X24)) )),
% 5.71/1.09    inference(superposition,[],[f1252,f12133])).
% 5.71/1.09  fof(f18,plain,(
% 5.71/1.09    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 5.71/1.09    inference(cnf_transformation,[],[f17])).
% 5.71/1.09  fof(f17,plain,(
% 5.71/1.09    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 5.71/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 5.71/1.09  fof(f16,plain,(
% 5.71/1.09    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 5.71/1.09    introduced(choice_axiom,[])).
% 5.71/1.09  fof(f15,plain,(
% 5.71/1.09    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.71/1.09    inference(ennf_transformation,[],[f13])).
% 5.71/1.09  fof(f13,negated_conjecture,(
% 5.71/1.09    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.71/1.09    inference(negated_conjecture,[],[f12])).
% 5.71/1.09  fof(f12,conjecture,(
% 5.71/1.09    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.71/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 5.71/1.09  % SZS output end Proof for theBenchmark
% 5.71/1.09  % (13740)------------------------------
% 5.71/1.09  % (13740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.71/1.09  % (13740)Termination reason: Refutation
% 5.71/1.09  
% 5.71/1.09  % (13740)Memory used [KB]: 18038
% 5.71/1.09  % (13740)Time elapsed: 0.679 s
% 5.71/1.09  % (13740)------------------------------
% 5.71/1.09  % (13740)------------------------------
% 5.71/1.11  % (13723)Success in time 0.744 s
%------------------------------------------------------------------------------
