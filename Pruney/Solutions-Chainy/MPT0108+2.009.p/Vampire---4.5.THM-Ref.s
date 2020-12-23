%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:18 EST 2020

% Result     : Theorem 8.97s
% Output     : Refutation 8.97s
% Verified   : 
% Statistics : Number of formulae       :   94 (2277 expanded)
%              Number of leaves         :   14 ( 759 expanded)
%              Depth                    :   22
%              Number of atoms          :   95 (2278 expanded)
%              Number of equality atoms :   94 (2277 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f33233,plain,(
    $false ),
    inference(subsumption_resolution,[],[f18,f33232])).

fof(f33232,plain,(
    ! [X33,X32] : k5_xboole_0(X32,X33) = k4_xboole_0(k2_xboole_0(X32,X33),k3_xboole_0(X32,X33)) ),
    inference(backward_demodulation,[],[f7416,f32972])).

fof(f32972,plain,(
    ! [X14,X15] : k5_xboole_0(X15,X14) = k5_xboole_0(k2_xboole_0(X15,X14),k3_xboole_0(X15,X14)) ),
    inference(superposition,[],[f1443,f682])).

fof(f682,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = X1 ),
    inference(superposition,[],[f567,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f567,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1 ),
    inference(backward_demodulation,[],[f49,f566])).

fof(f566,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(forward_demodulation,[],[f558,f425])).

fof(f425,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f67,f421])).

fof(f421,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2) ),
    inference(backward_demodulation,[],[f191,f402])).

fof(f402,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f39,f401])).

fof(f401,plain,(
    ! [X23] : k1_xboole_0 = k3_xboole_0(X23,k1_xboole_0) ),
    inference(forward_demodulation,[],[f390,f307])).

fof(f307,plain,(
    ! [X11] : k1_xboole_0 = k2_xboole_0(k3_xboole_0(X11,k1_xboole_0),k3_xboole_0(k1_xboole_0,X11)) ),
    inference(superposition,[],[f94,f57])).

fof(f57,plain,(
    ! [X2] : k3_xboole_0(k1_xboole_0,X2) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f25,f48])).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f45,f31])).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f22,f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f24,f20])).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f94,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[],[f27,f21])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f390,plain,(
    ! [X23] : k3_xboole_0(X23,k1_xboole_0) = k2_xboole_0(k3_xboole_0(X23,k1_xboole_0),k3_xboole_0(k1_xboole_0,X23)) ),
    inference(superposition,[],[f118,f268])).

fof(f268,plain,(
    ! [X8,X9] : k3_xboole_0(X8,k3_xboole_0(X9,X8)) = k3_xboole_0(X8,X9) ),
    inference(forward_demodulation,[],[f260,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f260,plain,(
    ! [X8,X9] : k3_xboole_0(X8,k3_xboole_0(X9,X8)) = k4_xboole_0(X8,k4_xboole_0(X8,X9)) ),
    inference(superposition,[],[f23,f84])).

fof(f84,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f26,f21])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f118,plain,(
    ! [X1] : k2_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(superposition,[],[f105,f22])).

fof(f105,plain,(
    ! [X0] : k2_xboole_0(k3_xboole_0(k1_xboole_0,X0),X0) = X0 ),
    inference(superposition,[],[f100,f21])).

fof(f100,plain,(
    ! [X5] : k2_xboole_0(k3_xboole_0(X5,k1_xboole_0),X5) = X5 ),
    inference(superposition,[],[f27,f20])).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f23,f20])).

fof(f191,plain,(
    ! [X2] : k3_xboole_0(k1_xboole_0,X2) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X2),k3_xboole_0(k1_xboole_0,X2)) ),
    inference(forward_demodulation,[],[f181,f57])).

fof(f181,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),k4_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f158,f41])).

fof(f41,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k3_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f40,f26])).

fof(f40,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f23,f23])).

fof(f158,plain,(
    ! [X0] : k4_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f144,f21])).

fof(f144,plain,(
    ! [X0] : k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(backward_demodulation,[],[f43,f136])).

fof(f136,plain,(
    ! [X5] : k3_xboole_0(X5,X5) = X5 ),
    inference(superposition,[],[f41,f20])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f23,f39])).

fof(f67,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(forward_demodulation,[],[f62,f19])).

fof(f62,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f24,f57])).

fof(f558,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f24,f433])).

fof(f433,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),X4) ),
    inference(backward_demodulation,[],[f220,f421])).

fof(f220,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X4,X5),X4) = k3_xboole_0(k1_xboole_0,k4_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f219,f21])).

fof(f219,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X4,X5),X4) = k3_xboole_0(k4_xboole_0(X4,X5),k1_xboole_0) ),
    inference(forward_demodulation,[],[f210,f157])).

fof(f157,plain,(
    ! [X2] : k3_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,X2) ),
    inference(forward_demodulation,[],[f149,f39])).

fof(f149,plain,(
    ! [X2] : k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2) ),
    inference(superposition,[],[f25,f136])).

fof(f210,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X4,X5),X4) = k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f54,f41])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f25,f21])).

fof(f49,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f46,f22])).

fof(f46,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f24,f23])).

fof(f1443,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X8,k5_xboole_0(k4_xboole_0(X9,X8),X10)) = k5_xboole_0(k2_xboole_0(X8,X9),X10) ),
    inference(superposition,[],[f29,f24])).

fof(f29,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f7416,plain,(
    ! [X33,X32] : k5_xboole_0(k2_xboole_0(X32,X33),k3_xboole_0(X32,X33)) = k4_xboole_0(k2_xboole_0(X32,X33),k3_xboole_0(X32,X33)) ),
    inference(backward_demodulation,[],[f3285,f7359])).

fof(f7359,plain,(
    ! [X80,X81] : k4_xboole_0(k5_xboole_0(X80,X81),k3_xboole_0(X80,X81)) = k4_xboole_0(k2_xboole_0(X80,X81),k3_xboole_0(X80,X81)) ),
    inference(superposition,[],[f2502,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f2502,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k4_xboole_0(k2_xboole_0(X4,X5),X5) ),
    inference(forward_demodulation,[],[f2467,f2207])).

fof(f2207,plain,(
    ! [X2,X1] : k4_xboole_0(X2,X1) = k5_xboole_0(k2_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f1620,f22])).

fof(f1620,plain,(
    ! [X6,X5] : k4_xboole_0(X6,X5) = k5_xboole_0(k2_xboole_0(X5,X6),X5) ),
    inference(superposition,[],[f1562,f24])).

fof(f1562,plain,(
    ! [X12,X11] : k5_xboole_0(k5_xboole_0(X12,X11),X12) = X11 ),
    inference(superposition,[],[f1546,f1546])).

fof(f1546,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f1525,f425])).

fof(f1525,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f1468,f1455])).

fof(f1455,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f29,f407])).

fof(f407,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2) ),
    inference(backward_demodulation,[],[f157,f401])).

fof(f1468,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f1440,f48])).

fof(f1440,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f29,f407])).

fof(f2467,plain,(
    ! [X4,X5] : k4_xboole_0(k2_xboole_0(X4,X5),X5) = k5_xboole_0(k2_xboole_0(X4,X5),X5) ),
    inference(superposition,[],[f25,f2400])).

fof(f2400,plain,(
    ! [X2,X3] : k3_xboole_0(k2_xboole_0(X3,X2),X2) = X2 ),
    inference(superposition,[],[f2079,f1484])).

fof(f1484,plain,(
    ! [X23,X22] : k3_xboole_0(X23,X22) = k5_xboole_0(k4_xboole_0(X22,X23),X22) ),
    inference(superposition,[],[f1468,f682])).

fof(f2079,plain,(
    ! [X10,X9] : k5_xboole_0(k4_xboole_0(X9,k2_xboole_0(X10,X9)),X9) = X9 ),
    inference(forward_demodulation,[],[f2039,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f2039,plain,(
    ! [X10,X9] : k5_xboole_0(k4_xboole_0(k4_xboole_0(X9,X10),X9),X9) = X9 ),
    inference(superposition,[],[f1559,f566])).

fof(f1559,plain,(
    ! [X6,X5] : k5_xboole_0(k4_xboole_0(X6,X5),k2_xboole_0(X5,X6)) = X5 ),
    inference(superposition,[],[f1546,f24])).

fof(f3285,plain,(
    ! [X33,X32] : k4_xboole_0(k5_xboole_0(X32,X33),k3_xboole_0(X32,X33)) = k5_xboole_0(k2_xboole_0(X32,X33),k3_xboole_0(X32,X33)) ),
    inference(superposition,[],[f2207,f28])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:24:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.41  % (28610)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.45  % (28605)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (28600)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (28598)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (28607)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (28615)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (28608)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (28611)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (28599)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (28609)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (28609)Refutation not found, incomplete strategy% (28609)------------------------------
% 0.21/0.50  % (28609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28609)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (28609)Memory used [KB]: 10490
% 0.21/0.50  % (28609)Time elapsed: 0.092 s
% 0.21/0.50  % (28609)------------------------------
% 0.21/0.50  % (28609)------------------------------
% 0.21/0.50  % (28603)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (28602)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (28614)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (28601)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (28606)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  % (28613)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (28604)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (28612)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 5.20/1.04  % (28602)Time limit reached!
% 5.20/1.04  % (28602)------------------------------
% 5.20/1.04  % (28602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.20/1.04  % (28602)Termination reason: Time limit
% 5.20/1.04  
% 5.20/1.04  % (28602)Memory used [KB]: 14839
% 5.20/1.04  % (28602)Time elapsed: 0.632 s
% 5.20/1.04  % (28602)------------------------------
% 5.20/1.04  % (28602)------------------------------
% 8.97/1.49  % (28614)Refutation found. Thanks to Tanya!
% 8.97/1.49  % SZS status Theorem for theBenchmark
% 8.97/1.49  % SZS output start Proof for theBenchmark
% 8.97/1.49  fof(f33233,plain,(
% 8.97/1.49    $false),
% 8.97/1.49    inference(subsumption_resolution,[],[f18,f33232])).
% 8.97/1.49  fof(f33232,plain,(
% 8.97/1.49    ( ! [X33,X32] : (k5_xboole_0(X32,X33) = k4_xboole_0(k2_xboole_0(X32,X33),k3_xboole_0(X32,X33))) )),
% 8.97/1.49    inference(backward_demodulation,[],[f7416,f32972])).
% 8.97/1.49  fof(f32972,plain,(
% 8.97/1.49    ( ! [X14,X15] : (k5_xboole_0(X15,X14) = k5_xboole_0(k2_xboole_0(X15,X14),k3_xboole_0(X15,X14))) )),
% 8.97/1.49    inference(superposition,[],[f1443,f682])).
% 8.97/1.49  fof(f682,plain,(
% 8.97/1.49    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = X1) )),
% 8.97/1.49    inference(superposition,[],[f567,f21])).
% 8.97/1.49  fof(f21,plain,(
% 8.97/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 8.97/1.49    inference(cnf_transformation,[],[f2])).
% 8.97/1.49  fof(f2,axiom,(
% 8.97/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 8.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 8.97/1.49  fof(f567,plain,(
% 8.97/1.49    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1) )),
% 8.97/1.49    inference(backward_demodulation,[],[f49,f566])).
% 8.97/1.49  fof(f566,plain,(
% 8.97/1.49    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 8.97/1.49    inference(forward_demodulation,[],[f558,f425])).
% 8.97/1.49  fof(f425,plain,(
% 8.97/1.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.97/1.49    inference(backward_demodulation,[],[f67,f421])).
% 8.97/1.49  fof(f421,plain,(
% 8.97/1.49    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) )),
% 8.97/1.49    inference(backward_demodulation,[],[f191,f402])).
% 8.97/1.49  fof(f402,plain,(
% 8.97/1.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 8.97/1.49    inference(backward_demodulation,[],[f39,f401])).
% 8.97/1.49  fof(f401,plain,(
% 8.97/1.49    ( ! [X23] : (k1_xboole_0 = k3_xboole_0(X23,k1_xboole_0)) )),
% 8.97/1.49    inference(forward_demodulation,[],[f390,f307])).
% 8.97/1.49  fof(f307,plain,(
% 8.97/1.49    ( ! [X11] : (k1_xboole_0 = k2_xboole_0(k3_xboole_0(X11,k1_xboole_0),k3_xboole_0(k1_xboole_0,X11))) )),
% 8.97/1.49    inference(superposition,[],[f94,f57])).
% 8.97/1.49  fof(f57,plain,(
% 8.97/1.49    ( ! [X2] : (k3_xboole_0(k1_xboole_0,X2) = k4_xboole_0(k1_xboole_0,X2)) )),
% 8.97/1.49    inference(superposition,[],[f25,f48])).
% 8.97/1.49  fof(f48,plain,(
% 8.97/1.49    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 8.97/1.49    inference(forward_demodulation,[],[f45,f31])).
% 8.97/1.49  fof(f31,plain,(
% 8.97/1.49    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 8.97/1.49    inference(superposition,[],[f22,f19])).
% 8.97/1.49  fof(f19,plain,(
% 8.97/1.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.97/1.49    inference(cnf_transformation,[],[f4])).
% 8.97/1.49  fof(f4,axiom,(
% 8.97/1.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 8.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 8.97/1.49  fof(f22,plain,(
% 8.97/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 8.97/1.49    inference(cnf_transformation,[],[f1])).
% 8.97/1.49  fof(f1,axiom,(
% 8.97/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 8.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 8.97/1.49  fof(f45,plain,(
% 8.97/1.49    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 8.97/1.49    inference(superposition,[],[f24,f20])).
% 8.97/1.49  fof(f20,plain,(
% 8.97/1.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.97/1.49    inference(cnf_transformation,[],[f5])).
% 8.97/1.49  fof(f5,axiom,(
% 8.97/1.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 8.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 8.97/1.49  fof(f24,plain,(
% 8.97/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 8.97/1.49    inference(cnf_transformation,[],[f12])).
% 8.97/1.49  fof(f12,axiom,(
% 8.97/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 8.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 8.97/1.49  fof(f25,plain,(
% 8.97/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.97/1.49    inference(cnf_transformation,[],[f3])).
% 8.97/1.49  fof(f3,axiom,(
% 8.97/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 8.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 8.97/1.49  fof(f94,plain,(
% 8.97/1.49    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1)) = X0) )),
% 8.97/1.49    inference(superposition,[],[f27,f21])).
% 8.97/1.49  fof(f27,plain,(
% 8.97/1.49    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 8.97/1.49    inference(cnf_transformation,[],[f9])).
% 8.97/1.49  fof(f9,axiom,(
% 8.97/1.49    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 8.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 8.97/1.49  fof(f390,plain,(
% 8.97/1.49    ( ! [X23] : (k3_xboole_0(X23,k1_xboole_0) = k2_xboole_0(k3_xboole_0(X23,k1_xboole_0),k3_xboole_0(k1_xboole_0,X23))) )),
% 8.97/1.49    inference(superposition,[],[f118,f268])).
% 8.97/1.49  fof(f268,plain,(
% 8.97/1.49    ( ! [X8,X9] : (k3_xboole_0(X8,k3_xboole_0(X9,X8)) = k3_xboole_0(X8,X9)) )),
% 8.97/1.49    inference(forward_demodulation,[],[f260,f23])).
% 8.97/1.49  fof(f23,plain,(
% 8.97/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 8.97/1.49    inference(cnf_transformation,[],[f8])).
% 8.97/1.49  fof(f8,axiom,(
% 8.97/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 8.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 8.97/1.49  fof(f260,plain,(
% 8.97/1.49    ( ! [X8,X9] : (k3_xboole_0(X8,k3_xboole_0(X9,X8)) = k4_xboole_0(X8,k4_xboole_0(X8,X9))) )),
% 8.97/1.49    inference(superposition,[],[f23,f84])).
% 8.97/1.49  fof(f84,plain,(
% 8.97/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 8.97/1.49    inference(superposition,[],[f26,f21])).
% 8.97/1.49  fof(f26,plain,(
% 8.97/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.97/1.49    inference(cnf_transformation,[],[f7])).
% 8.97/1.49  fof(f7,axiom,(
% 8.97/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 8.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 8.97/1.49  fof(f118,plain,(
% 8.97/1.49    ( ! [X1] : (k2_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) = X1) )),
% 8.97/1.49    inference(superposition,[],[f105,f22])).
% 8.97/1.49  fof(f105,plain,(
% 8.97/1.49    ( ! [X0] : (k2_xboole_0(k3_xboole_0(k1_xboole_0,X0),X0) = X0) )),
% 8.97/1.49    inference(superposition,[],[f100,f21])).
% 8.97/1.49  fof(f100,plain,(
% 8.97/1.49    ( ! [X5] : (k2_xboole_0(k3_xboole_0(X5,k1_xboole_0),X5) = X5) )),
% 8.97/1.49    inference(superposition,[],[f27,f20])).
% 8.97/1.49  fof(f39,plain,(
% 8.97/1.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 8.97/1.49    inference(superposition,[],[f23,f20])).
% 8.97/1.49  fof(f191,plain,(
% 8.97/1.49    ( ! [X2] : (k3_xboole_0(k1_xboole_0,X2) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X2),k3_xboole_0(k1_xboole_0,X2))) )),
% 8.97/1.49    inference(forward_demodulation,[],[f181,f57])).
% 8.97/1.49  fof(f181,plain,(
% 8.97/1.49    ( ! [X2] : (k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),k4_xboole_0(k1_xboole_0,X2))) )),
% 8.97/1.49    inference(superposition,[],[f158,f41])).
% 8.97/1.49  fof(f41,plain,(
% 8.97/1.49    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k3_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 8.97/1.49    inference(forward_demodulation,[],[f40,f26])).
% 8.97/1.49  fof(f40,plain,(
% 8.97/1.49    ( ! [X2,X1] : (k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 8.97/1.49    inference(superposition,[],[f23,f23])).
% 8.97/1.49  fof(f158,plain,(
% 8.97/1.49    ( ! [X0] : (k4_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0) )),
% 8.97/1.49    inference(superposition,[],[f144,f21])).
% 8.97/1.49  fof(f144,plain,(
% 8.97/1.49    ( ! [X0] : (k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 8.97/1.49    inference(backward_demodulation,[],[f43,f136])).
% 8.97/1.49  fof(f136,plain,(
% 8.97/1.49    ( ! [X5] : (k3_xboole_0(X5,X5) = X5) )),
% 8.97/1.49    inference(superposition,[],[f41,f20])).
% 8.97/1.49  fof(f43,plain,(
% 8.97/1.49    ( ! [X0] : (k3_xboole_0(X0,X0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 8.97/1.49    inference(superposition,[],[f23,f39])).
% 8.97/1.49  fof(f67,plain,(
% 8.97/1.49    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0) )),
% 8.97/1.49    inference(forward_demodulation,[],[f62,f19])).
% 8.97/1.49  fof(f62,plain,(
% 8.97/1.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) )),
% 8.97/1.49    inference(superposition,[],[f24,f57])).
% 8.97/1.49  fof(f558,plain,(
% 8.97/1.49    ( ! [X2,X3] : (k5_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 8.97/1.49    inference(superposition,[],[f24,f433])).
% 8.97/1.49  fof(f433,plain,(
% 8.97/1.49    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),X4)) )),
% 8.97/1.49    inference(backward_demodulation,[],[f220,f421])).
% 8.97/1.49  fof(f220,plain,(
% 8.97/1.49    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),X4) = k3_xboole_0(k1_xboole_0,k4_xboole_0(X4,X5))) )),
% 8.97/1.49    inference(forward_demodulation,[],[f219,f21])).
% 8.97/1.49  fof(f219,plain,(
% 8.97/1.49    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),X4) = k3_xboole_0(k4_xboole_0(X4,X5),k1_xboole_0)) )),
% 8.97/1.49    inference(forward_demodulation,[],[f210,f157])).
% 8.97/1.49  fof(f157,plain,(
% 8.97/1.49    ( ! [X2] : (k3_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,X2)) )),
% 8.97/1.49    inference(forward_demodulation,[],[f149,f39])).
% 8.97/1.49  fof(f149,plain,(
% 8.97/1.49    ( ! [X2] : (k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2)) )),
% 8.97/1.49    inference(superposition,[],[f25,f136])).
% 8.97/1.49  fof(f210,plain,(
% 8.97/1.49    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),X4) = k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5))) )),
% 8.97/1.49    inference(superposition,[],[f54,f41])).
% 8.97/1.49  fof(f54,plain,(
% 8.97/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 8.97/1.49    inference(superposition,[],[f25,f21])).
% 8.97/1.49  fof(f49,plain,(
% 8.97/1.49    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 8.97/1.49    inference(forward_demodulation,[],[f46,f22])).
% 8.97/1.49  fof(f46,plain,(
% 8.97/1.49    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2))) )),
% 8.97/1.49    inference(superposition,[],[f24,f23])).
% 8.97/1.49  fof(f1443,plain,(
% 8.97/1.49    ( ! [X10,X8,X9] : (k5_xboole_0(X8,k5_xboole_0(k4_xboole_0(X9,X8),X10)) = k5_xboole_0(k2_xboole_0(X8,X9),X10)) )),
% 8.97/1.49    inference(superposition,[],[f29,f24])).
% 8.97/1.49  fof(f29,plain,(
% 8.97/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 8.97/1.49    inference(cnf_transformation,[],[f10])).
% 8.97/1.49  fof(f10,axiom,(
% 8.97/1.49    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 8.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 8.97/1.49  fof(f7416,plain,(
% 8.97/1.49    ( ! [X33,X32] : (k5_xboole_0(k2_xboole_0(X32,X33),k3_xboole_0(X32,X33)) = k4_xboole_0(k2_xboole_0(X32,X33),k3_xboole_0(X32,X33))) )),
% 8.97/1.49    inference(backward_demodulation,[],[f3285,f7359])).
% 8.97/1.49  fof(f7359,plain,(
% 8.97/1.49    ( ! [X80,X81] : (k4_xboole_0(k5_xboole_0(X80,X81),k3_xboole_0(X80,X81)) = k4_xboole_0(k2_xboole_0(X80,X81),k3_xboole_0(X80,X81))) )),
% 8.97/1.49    inference(superposition,[],[f2502,f28])).
% 8.97/1.49  fof(f28,plain,(
% 8.97/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 8.97/1.49    inference(cnf_transformation,[],[f11])).
% 8.97/1.49  fof(f11,axiom,(
% 8.97/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 8.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 8.97/1.49  fof(f2502,plain,(
% 8.97/1.49    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k4_xboole_0(k2_xboole_0(X4,X5),X5)) )),
% 8.97/1.49    inference(forward_demodulation,[],[f2467,f2207])).
% 8.97/1.49  fof(f2207,plain,(
% 8.97/1.49    ( ! [X2,X1] : (k4_xboole_0(X2,X1) = k5_xboole_0(k2_xboole_0(X2,X1),X1)) )),
% 8.97/1.49    inference(superposition,[],[f1620,f22])).
% 8.97/1.49  fof(f1620,plain,(
% 8.97/1.49    ( ! [X6,X5] : (k4_xboole_0(X6,X5) = k5_xboole_0(k2_xboole_0(X5,X6),X5)) )),
% 8.97/1.49    inference(superposition,[],[f1562,f24])).
% 8.97/1.49  fof(f1562,plain,(
% 8.97/1.49    ( ! [X12,X11] : (k5_xboole_0(k5_xboole_0(X12,X11),X12) = X11) )),
% 8.97/1.49    inference(superposition,[],[f1546,f1546])).
% 8.97/1.49  fof(f1546,plain,(
% 8.97/1.49    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 8.97/1.49    inference(forward_demodulation,[],[f1525,f425])).
% 8.97/1.49  fof(f1525,plain,(
% 8.97/1.49    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 8.97/1.49    inference(superposition,[],[f1468,f1455])).
% 8.97/1.49  fof(f1455,plain,(
% 8.97/1.49    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 8.97/1.49    inference(superposition,[],[f29,f407])).
% 8.97/1.49  fof(f407,plain,(
% 8.97/1.49    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,X2)) )),
% 8.97/1.49    inference(backward_demodulation,[],[f157,f401])).
% 8.97/1.49  fof(f1468,plain,(
% 8.97/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 8.97/1.49    inference(forward_demodulation,[],[f1440,f48])).
% 8.97/1.49  fof(f1440,plain,(
% 8.97/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 8.97/1.49    inference(superposition,[],[f29,f407])).
% 8.97/1.49  fof(f2467,plain,(
% 8.97/1.49    ( ! [X4,X5] : (k4_xboole_0(k2_xboole_0(X4,X5),X5) = k5_xboole_0(k2_xboole_0(X4,X5),X5)) )),
% 8.97/1.49    inference(superposition,[],[f25,f2400])).
% 8.97/1.49  fof(f2400,plain,(
% 8.97/1.49    ( ! [X2,X3] : (k3_xboole_0(k2_xboole_0(X3,X2),X2) = X2) )),
% 8.97/1.49    inference(superposition,[],[f2079,f1484])).
% 8.97/1.49  fof(f1484,plain,(
% 8.97/1.49    ( ! [X23,X22] : (k3_xboole_0(X23,X22) = k5_xboole_0(k4_xboole_0(X22,X23),X22)) )),
% 8.97/1.49    inference(superposition,[],[f1468,f682])).
% 8.97/1.49  fof(f2079,plain,(
% 8.97/1.49    ( ! [X10,X9] : (k5_xboole_0(k4_xboole_0(X9,k2_xboole_0(X10,X9)),X9) = X9) )),
% 8.97/1.49    inference(forward_demodulation,[],[f2039,f30])).
% 8.97/1.49  fof(f30,plain,(
% 8.97/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 8.97/1.49    inference(cnf_transformation,[],[f6])).
% 8.97/1.49  fof(f6,axiom,(
% 8.97/1.49    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 8.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 8.97/1.49  fof(f2039,plain,(
% 8.97/1.49    ( ! [X10,X9] : (k5_xboole_0(k4_xboole_0(k4_xboole_0(X9,X10),X9),X9) = X9) )),
% 8.97/1.49    inference(superposition,[],[f1559,f566])).
% 8.97/1.49  fof(f1559,plain,(
% 8.97/1.49    ( ! [X6,X5] : (k5_xboole_0(k4_xboole_0(X6,X5),k2_xboole_0(X5,X6)) = X5) )),
% 8.97/1.49    inference(superposition,[],[f1546,f24])).
% 8.97/1.49  fof(f3285,plain,(
% 8.97/1.49    ( ! [X33,X32] : (k4_xboole_0(k5_xboole_0(X32,X33),k3_xboole_0(X32,X33)) = k5_xboole_0(k2_xboole_0(X32,X33),k3_xboole_0(X32,X33))) )),
% 8.97/1.49    inference(superposition,[],[f2207,f28])).
% 8.97/1.49  fof(f18,plain,(
% 8.97/1.49    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 8.97/1.49    inference(cnf_transformation,[],[f17])).
% 8.97/1.49  fof(f17,plain,(
% 8.97/1.49    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 8.97/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 8.97/1.49  fof(f16,plain,(
% 8.97/1.49    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 8.97/1.49    introduced(choice_axiom,[])).
% 8.97/1.49  fof(f15,plain,(
% 8.97/1.49    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 8.97/1.49    inference(ennf_transformation,[],[f14])).
% 8.97/1.49  fof(f14,negated_conjecture,(
% 8.97/1.49    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 8.97/1.49    inference(negated_conjecture,[],[f13])).
% 8.97/1.49  fof(f13,conjecture,(
% 8.97/1.49    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 8.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 8.97/1.49  % SZS output end Proof for theBenchmark
% 8.97/1.49  % (28614)------------------------------
% 8.97/1.49  % (28614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.97/1.49  % (28614)Termination reason: Refutation
% 8.97/1.49  
% 8.97/1.49  % (28614)Memory used [KB]: 24178
% 8.97/1.49  % (28614)Time elapsed: 1.074 s
% 8.97/1.49  % (28614)------------------------------
% 8.97/1.49  % (28614)------------------------------
% 8.97/1.49  % (28597)Success in time 1.133 s
%------------------------------------------------------------------------------
