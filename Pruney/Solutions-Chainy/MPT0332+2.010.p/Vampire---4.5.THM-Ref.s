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
% DateTime   : Thu Dec  3 12:43:10 EST 2020

% Result     : Theorem 2.38s
% Output     : Refutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :  129 (6324 expanded)
%              Number of leaves         :   12 (2107 expanded)
%              Depth                    :   29
%              Number of atoms          :  149 (6370 expanded)
%              Number of equality atoms :  127 (6324 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3900,plain,(
    $false ),
    inference(subsumption_resolution,[],[f22,f3899])).

fof(f3899,plain,(
    sK2 = k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    inference(forward_demodulation,[],[f3847,f2709])).

fof(f2709,plain,(
    ! [X14,X15] : k3_xboole_0(k2_xboole_0(X14,X15),X14) = X14 ),
    inference(backward_demodulation,[],[f1224,f2671])).

fof(f2671,plain,(
    ! [X14,X13] : k5_xboole_0(k5_xboole_0(X14,X13),X14) = X13 ),
    inference(superposition,[],[f2649,f2649])).

fof(f2649,plain,(
    ! [X4,X3] : k5_xboole_0(X4,k5_xboole_0(X3,X4)) = X3 ),
    inference(forward_demodulation,[],[f2605,f1906])).

fof(f1906,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f75,f1903])).

fof(f1903,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4) ),
    inference(backward_demodulation,[],[f493,f1873])).

fof(f1873,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5) ),
    inference(backward_demodulation,[],[f55,f1854])).

fof(f1854,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f367,f1805])).

fof(f1805,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f1686,f133])).

fof(f133,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),k1_xboole_0) ),
    inference(superposition,[],[f124,f75])).

fof(f124,plain,(
    ! [X7] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(X7,k1_xboole_0),X7) ),
    inference(forward_demodulation,[],[f123,f23])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f123,plain,(
    ! [X7] : k3_xboole_0(X7,k1_xboole_0) = k5_xboole_0(k4_xboole_0(X7,k1_xboole_0),X7) ),
    inference(forward_demodulation,[],[f115,f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f115,plain,(
    ! [X7] : k3_xboole_0(X7,k1_xboole_0) = k5_xboole_0(k4_xboole_0(X7,k1_xboole_0),k2_xboole_0(X7,k1_xboole_0)) ),
    inference(superposition,[],[f31,f52])).

fof(f52,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f29,f23])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f1686,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(forward_demodulation,[],[f1685,f55])).

fof(f1685,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X0) = k4_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(forward_demodulation,[],[f1616,f410])).

fof(f410,plain,(
    ! [X5] : k2_xboole_0(X5,X5) = X5 ),
    inference(forward_demodulation,[],[f395,f75])).

fof(f395,plain,(
    ! [X5] : k2_xboole_0(X5,X5) = k5_xboole_0(X5,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f30,f367])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f1616,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,X0),X1) = k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f34,f58])).

fof(f58,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f53,f55])).

fof(f53,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f29,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_xboole_1)).

fof(f367,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f364,f36])).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f25,f24])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f364,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X2)) ),
    inference(forward_demodulation,[],[f363,f52])).

fof(f363,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X2)) ),
    inference(superposition,[],[f30,f350])).

fof(f350,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X1),k1_xboole_0) ),
    inference(superposition,[],[f325,f52])).

fof(f325,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(X1,X1),k1_xboole_0) ),
    inference(superposition,[],[f312,f240])).

fof(f240,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(X2,X2)) ),
    inference(forward_demodulation,[],[f220,f55])).

fof(f220,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X2)) ),
    inference(superposition,[],[f33,f130])).

fof(f130,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X5),X5) ),
    inference(forward_demodulation,[],[f121,f47])).

fof(f47,plain,(
    ! [X5] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X5) ),
    inference(superposition,[],[f26,f36])).

fof(f121,plain,(
    ! [X5] : k3_xboole_0(k1_xboole_0,X5) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X5),X5) ),
    inference(superposition,[],[f31,f36])).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f312,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f300,f23])).

fof(f300,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f219,f24])).

fof(f219,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f33,f31])).

fof(f55,plain,(
    ! [X5] : k4_xboole_0(X5,X5) = k5_xboole_0(X5,X5) ),
    inference(superposition,[],[f29,f44])).

fof(f44,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f26,f24])).

fof(f493,plain,(
    ! [X4,X3] : k5_xboole_0(X3,X3) = k4_xboole_0(k1_xboole_0,X4) ),
    inference(superposition,[],[f487,f75])).

fof(f487,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f206,f460])).

fof(f460,plain,(
    ! [X10,X11] : k5_xboole_0(k4_xboole_0(X11,X11),X10) = X10 ),
    inference(superposition,[],[f414,f387])).

fof(f387,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X1) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f367,f367])).

fof(f414,plain,(
    ! [X0] : k5_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
    inference(backward_demodulation,[],[f122,f410])).

fof(f122,plain,(
    ! [X0] : k5_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f111,f44])).

fof(f111,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f31,f55])).

fof(f206,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[],[f33,f55])).

fof(f75,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = X0 ),
    inference(forward_demodulation,[],[f72,f24])).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f30,f59])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f56,f56])).

fof(f56,plain,(
    ! [X6] : k4_xboole_0(k1_xboole_0,X6) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f29,f47])).

fof(f2605,plain,(
    ! [X4,X3] : k5_xboole_0(X4,k5_xboole_0(X3,X4)) = k5_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f487,f1939])).

fof(f1939,plain,(
    ! [X14,X15] : k1_xboole_0 = k5_xboole_0(X14,k5_xboole_0(X15,k5_xboole_0(X14,X15))) ),
    inference(backward_demodulation,[],[f242,f1921])).

fof(f1921,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f52,f1906])).

fof(f242,plain,(
    ! [X14,X15] : k1_xboole_0 = k5_xboole_0(X14,k4_xboole_0(k5_xboole_0(X15,k5_xboole_0(X14,X15)),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f224,f241])).

fof(f241,plain,(
    ! [X19,X20] : k4_xboole_0(k5_xboole_0(X19,X20),k1_xboole_0) = k5_xboole_0(X19,k4_xboole_0(X20,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f226,f52])).

fof(f226,plain,(
    ! [X19,X20] : k4_xboole_0(k5_xboole_0(X19,X20),k1_xboole_0) = k5_xboole_0(X19,k5_xboole_0(X20,k1_xboole_0)) ),
    inference(superposition,[],[f33,f52])).

fof(f224,plain,(
    ! [X14,X15] : k1_xboole_0 = k5_xboole_0(X14,k5_xboole_0(X15,k4_xboole_0(k5_xboole_0(X14,X15),k1_xboole_0))) ),
    inference(superposition,[],[f33,f150])).

fof(f150,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f141,f36])).

fof(f141,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f130,f30])).

fof(f1224,plain,(
    ! [X14,X15] : k3_xboole_0(k2_xboole_0(X14,X15),X14) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X14,X15),X14),k2_xboole_0(X14,X15)) ),
    inference(superposition,[],[f119,f415])).

fof(f415,plain,(
    ! [X8,X7] : k2_xboole_0(X7,X8) = k2_xboole_0(X7,k2_xboole_0(X7,X8)) ),
    inference(backward_demodulation,[],[f98,f398])).

fof(f398,plain,(
    ! [X6,X5] : k5_xboole_0(X6,k4_xboole_0(X5,X5)) = X6 ),
    inference(superposition,[],[f75,f367])).

fof(f98,plain,(
    ! [X8,X7] : k5_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X7,X7)) = k2_xboole_0(X7,k2_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f97,f25])).

fof(f97,plain,(
    ! [X8,X7] : k2_xboole_0(k2_xboole_0(X7,X8),X7) = k5_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X7,X7)) ),
    inference(superposition,[],[f30,f58])).

fof(f119,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f31,f25])).

fof(f3847,plain,(
    k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) = k3_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2) ),
    inference(superposition,[],[f2362,f2690])).

fof(f2690,plain,(
    sK2 = k5_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    inference(superposition,[],[f2649,f1122])).

fof(f1122,plain,(
    k2_tarski(sK0,sK1) = k5_xboole_0(sK2,k2_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1121,f45])).

fof(f45,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(superposition,[],[f26,f25])).

fof(f1121,plain,(
    k5_xboole_0(sK2,k2_xboole_0(sK2,k2_tarski(sK0,sK1))) = k3_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1120,f416])).

fof(f416,plain,(
    ! [X8,X9] : k2_xboole_0(X9,X8) = k2_xboole_0(X8,k2_xboole_0(X9,X8)) ),
    inference(backward_demodulation,[],[f110,f398])).

fof(f110,plain,(
    ! [X8,X9] : k5_xboole_0(k2_xboole_0(X9,X8),k4_xboole_0(X8,X8)) = k2_xboole_0(X8,k2_xboole_0(X9,X8)) ),
    inference(forward_demodulation,[],[f109,f25])).

fof(f109,plain,(
    ! [X8,X9] : k2_xboole_0(k2_xboole_0(X9,X8),X8) = k5_xboole_0(k2_xboole_0(X9,X8),k4_xboole_0(X8,X8)) ),
    inference(superposition,[],[f30,f57])).

fof(f57,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k2_xboole_0(X4,X3)) = k4_xboole_0(X3,X3) ),
    inference(backward_demodulation,[],[f54,f55])).

fof(f54,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k2_xboole_0(X4,X3)) = k5_xboole_0(X3,X3) ),
    inference(superposition,[],[f29,f45])).

fof(f1120,plain,(
    k3_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(sK2,k2_tarski(sK0,sK1))) = k5_xboole_0(sK2,k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(sK2,k2_tarski(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f1117,f25])).

fof(f1117,plain,(
    k3_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(sK2,k2_tarski(sK0,sK1))) = k5_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))) ),
    inference(superposition,[],[f119,f1086])).

fof(f1086,plain,(
    sK2 = k5_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    inference(superposition,[],[f487,f828])).

fof(f828,plain,(
    k2_xboole_0(sK2,k2_tarski(sK0,sK1)) = k5_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(forward_demodulation,[],[f827,f25])).

fof(f827,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),sK2) = k5_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(superposition,[],[f30,f825])).

fof(f825,plain,(
    sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    inference(resolution,[],[f818,f20])).

fof(f20,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_zfmisc_1)).

fof(f818,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | sK2 = k4_xboole_0(sK2,k2_tarski(X1,sK1)) ) ),
    inference(resolution,[],[f35,f21])).

fof(f21,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f2362,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k5_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(forward_demodulation,[],[f2361,f522])).

fof(f522,plain,(
    ! [X8,X9] : k5_xboole_0(X9,k2_xboole_0(X8,X9)) = k4_xboole_0(X8,X9) ),
    inference(forward_demodulation,[],[f496,f29])).

fof(f496,plain,(
    ! [X8,X9] : k5_xboole_0(X9,k2_xboole_0(X8,X9)) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(superposition,[],[f487,f219])).

fof(f2361,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k2_xboole_0(X1,X2)) = k3_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(backward_demodulation,[],[f547,f2360])).

fof(f2360,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f2342,f30])).

fof(f2342,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f30,f1934])).

fof(f1934,plain,(
    ! [X2,X3] : k4_xboole_0(X3,X2) = k4_xboole_0(k5_xboole_0(X2,X3),X2) ),
    inference(backward_demodulation,[],[f1719,f1921])).

fof(f1719,plain,(
    ! [X2,X3] : k4_xboole_0(k5_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X3,k1_xboole_0),X2) ),
    inference(backward_demodulation,[],[f1690,f1718])).

fof(f1718,plain,(
    ! [X21,X22,X20] : k2_xboole_0(k4_xboole_0(X22,X22),k4_xboole_0(X20,X21)) = k4_xboole_0(k4_xboole_0(X20,k1_xboole_0),X21) ),
    inference(forward_demodulation,[],[f1717,f526])).

fof(f526,plain,(
    ! [X10] : k5_xboole_0(k1_xboole_0,X10) = k4_xboole_0(X10,k1_xboole_0) ),
    inference(forward_demodulation,[],[f497,f52])).

fof(f497,plain,(
    ! [X10] : k5_xboole_0(k1_xboole_0,X10) = k5_xboole_0(X10,k1_xboole_0) ),
    inference(superposition,[],[f487,f312])).

fof(f1717,plain,(
    ! [X21,X22,X20] : k4_xboole_0(k5_xboole_0(k1_xboole_0,X20),X21) = k2_xboole_0(k4_xboole_0(X22,X22),k4_xboole_0(X20,X21)) ),
    inference(forward_demodulation,[],[f1624,f36])).

fof(f1624,plain,(
    ! [X21,X22,X20] : k4_xboole_0(k5_xboole_0(k1_xboole_0,X20),X21) = k2_xboole_0(k4_xboole_0(X22,X22),k4_xboole_0(X20,k2_xboole_0(k1_xboole_0,X21))) ),
    inference(superposition,[],[f34,f388])).

fof(f388,plain,(
    ! [X2,X3] : k4_xboole_0(X3,X3) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f367,f59])).

fof(f1690,plain,(
    ! [X2,X3] : k4_xboole_0(k5_xboole_0(X2,X3),X2) = k2_xboole_0(k4_xboole_0(X2,X2),k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f1617,f410])).

fof(f1617,plain,(
    ! [X2,X3] : k4_xboole_0(k5_xboole_0(X2,X3),X2) = k2_xboole_0(k4_xboole_0(X2,X2),k4_xboole_0(X3,k2_xboole_0(X2,X2))) ),
    inference(superposition,[],[f34,f57])).

fof(f547,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k2_xboole_0(X1,k5_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f512,f25])).

fof(f512,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k2_xboole_0(k5_xboole_0(X1,X2),X1)) ),
    inference(superposition,[],[f119,f487])).

fof(f22,plain,(
    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:06:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (3806)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (3815)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (3814)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (3810)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (3805)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (3807)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (3819)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (3812)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  % (3820)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (3813)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.52  % (3821)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.52  % (3817)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.52  % (3816)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.53  % (3809)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.53  % (3808)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.54  % (3804)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.55  % (3811)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.56  % (3818)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 2.38/0.68  % (3820)Refutation found. Thanks to Tanya!
% 2.38/0.68  % SZS status Theorem for theBenchmark
% 2.38/0.68  % SZS output start Proof for theBenchmark
% 2.38/0.68  fof(f3900,plain,(
% 2.38/0.68    $false),
% 2.38/0.68    inference(subsumption_resolution,[],[f22,f3899])).
% 2.38/0.68  fof(f3899,plain,(
% 2.38/0.68    sK2 = k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))),
% 2.38/0.68    inference(forward_demodulation,[],[f3847,f2709])).
% 2.38/0.68  fof(f2709,plain,(
% 2.38/0.68    ( ! [X14,X15] : (k3_xboole_0(k2_xboole_0(X14,X15),X14) = X14) )),
% 2.38/0.68    inference(backward_demodulation,[],[f1224,f2671])).
% 2.38/0.68  fof(f2671,plain,(
% 2.38/0.68    ( ! [X14,X13] : (k5_xboole_0(k5_xboole_0(X14,X13),X14) = X13) )),
% 2.38/0.68    inference(superposition,[],[f2649,f2649])).
% 2.38/0.68  fof(f2649,plain,(
% 2.38/0.68    ( ! [X4,X3] : (k5_xboole_0(X4,k5_xboole_0(X3,X4)) = X3) )),
% 2.38/0.68    inference(forward_demodulation,[],[f2605,f1906])).
% 2.38/0.68  fof(f1906,plain,(
% 2.38/0.68    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.38/0.68    inference(backward_demodulation,[],[f75,f1903])).
% 2.38/0.68  fof(f1903,plain,(
% 2.38/0.68    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4)) )),
% 2.38/0.68    inference(backward_demodulation,[],[f493,f1873])).
% 2.38/0.68  fof(f1873,plain,(
% 2.38/0.68    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,X5)) )),
% 2.38/0.68    inference(backward_demodulation,[],[f55,f1854])).
% 2.38/0.68  fof(f1854,plain,(
% 2.38/0.68    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 2.38/0.68    inference(backward_demodulation,[],[f367,f1805])).
% 2.38/0.68  fof(f1805,plain,(
% 2.38/0.68    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.38/0.68    inference(superposition,[],[f1686,f133])).
% 2.38/0.68  fof(f133,plain,(
% 2.38/0.68    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),k1_xboole_0)) )),
% 2.38/0.68    inference(superposition,[],[f124,f75])).
% 2.38/0.68  fof(f124,plain,(
% 2.38/0.68    ( ! [X7] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(X7,k1_xboole_0),X7)) )),
% 2.38/0.68    inference(forward_demodulation,[],[f123,f23])).
% 2.38/0.68  fof(f23,plain,(
% 2.38/0.68    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.38/0.68    inference(cnf_transformation,[],[f5])).
% 2.38/0.68  fof(f5,axiom,(
% 2.38/0.68    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.38/0.68  fof(f123,plain,(
% 2.38/0.68    ( ! [X7] : (k3_xboole_0(X7,k1_xboole_0) = k5_xboole_0(k4_xboole_0(X7,k1_xboole_0),X7)) )),
% 2.38/0.68    inference(forward_demodulation,[],[f115,f24])).
% 2.38/0.68  fof(f24,plain,(
% 2.38/0.68    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.38/0.68    inference(cnf_transformation,[],[f3])).
% 2.38/0.68  fof(f3,axiom,(
% 2.38/0.68    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.38/0.68  fof(f115,plain,(
% 2.38/0.68    ( ! [X7] : (k3_xboole_0(X7,k1_xboole_0) = k5_xboole_0(k4_xboole_0(X7,k1_xboole_0),k2_xboole_0(X7,k1_xboole_0))) )),
% 2.38/0.68    inference(superposition,[],[f31,f52])).
% 2.38/0.68  fof(f52,plain,(
% 2.38/0.68    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 2.38/0.68    inference(superposition,[],[f29,f23])).
% 2.38/0.68  fof(f29,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.38/0.68    inference(cnf_transformation,[],[f2])).
% 2.38/0.68  fof(f2,axiom,(
% 2.38/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.38/0.68  fof(f31,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.38/0.68    inference(cnf_transformation,[],[f7])).
% 2.38/0.68  fof(f7,axiom,(
% 2.38/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.38/0.68  fof(f1686,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X0,X0),X1)) )),
% 2.38/0.68    inference(forward_demodulation,[],[f1685,f55])).
% 2.38/0.68  fof(f1685,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = k4_xboole_0(k5_xboole_0(X0,X0),X1)) )),
% 2.38/0.68    inference(forward_demodulation,[],[f1616,f410])).
% 2.38/0.68  fof(f410,plain,(
% 2.38/0.68    ( ! [X5] : (k2_xboole_0(X5,X5) = X5) )),
% 2.38/0.68    inference(forward_demodulation,[],[f395,f75])).
% 2.38/0.68  fof(f395,plain,(
% 2.38/0.68    ( ! [X5] : (k2_xboole_0(X5,X5) = k5_xboole_0(X5,k4_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 2.38/0.68    inference(superposition,[],[f30,f367])).
% 2.38/0.68  fof(f30,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.38/0.68    inference(cnf_transformation,[],[f8])).
% 2.38/0.68  fof(f8,axiom,(
% 2.38/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.38/0.68  fof(f1616,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X0),X1) = k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) )),
% 2.38/0.68    inference(superposition,[],[f34,f58])).
% 2.38/0.68  fof(f58,plain,(
% 2.38/0.68    ( ! [X2,X1] : (k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X1,X1)) )),
% 2.38/0.68    inference(backward_demodulation,[],[f53,f55])).
% 2.38/0.68  fof(f53,plain,(
% 2.38/0.68    ( ! [X2,X1] : (k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k5_xboole_0(X1,X1)) )),
% 2.38/0.68    inference(superposition,[],[f29,f26])).
% 2.38/0.68  fof(f26,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.38/0.68    inference(cnf_transformation,[],[f4])).
% 2.38/0.68  fof(f4,axiom,(
% 2.38/0.68    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 2.38/0.68  fof(f34,plain,(
% 2.38/0.68    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))) )),
% 2.38/0.68    inference(cnf_transformation,[],[f9])).
% 2.38/0.68  fof(f9,axiom,(
% 2.38/0.68    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_xboole_1)).
% 2.38/0.68  fof(f367,plain,(
% 2.38/0.68    ( ! [X1] : (k4_xboole_0(X1,X1) = k4_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 2.38/0.68    inference(superposition,[],[f364,f36])).
% 2.38/0.68  fof(f36,plain,(
% 2.38/0.68    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.38/0.68    inference(superposition,[],[f25,f24])).
% 2.38/0.68  fof(f25,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.38/0.68    inference(cnf_transformation,[],[f1])).
% 2.38/0.68  fof(f1,axiom,(
% 2.38/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.38/0.68  fof(f364,plain,(
% 2.38/0.68    ( ! [X2] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X2))) )),
% 2.38/0.68    inference(forward_demodulation,[],[f363,f52])).
% 2.38/0.68  fof(f363,plain,(
% 2.38/0.68    ( ! [X2] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X2))) )),
% 2.38/0.68    inference(superposition,[],[f30,f350])).
% 2.38/0.68  fof(f350,plain,(
% 2.38/0.68    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X1),k1_xboole_0)) )),
% 2.38/0.68    inference(superposition,[],[f325,f52])).
% 2.38/0.68  fof(f325,plain,(
% 2.38/0.68    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(X1,X1),k1_xboole_0)) )),
% 2.38/0.68    inference(superposition,[],[f312,f240])).
% 2.38/0.68  fof(f240,plain,(
% 2.38/0.68    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(X2,X2))) )),
% 2.38/0.68    inference(forward_demodulation,[],[f220,f55])).
% 2.38/0.68  fof(f220,plain,(
% 2.38/0.68    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X2))) )),
% 2.38/0.68    inference(superposition,[],[f33,f130])).
% 2.38/0.68  fof(f130,plain,(
% 2.38/0.68    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X5),X5)) )),
% 2.38/0.68    inference(forward_demodulation,[],[f121,f47])).
% 2.38/0.68  fof(f47,plain,(
% 2.38/0.68    ( ! [X5] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X5)) )),
% 2.38/0.68    inference(superposition,[],[f26,f36])).
% 2.38/0.68  fof(f121,plain,(
% 2.38/0.68    ( ! [X5] : (k3_xboole_0(k1_xboole_0,X5) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X5),X5)) )),
% 2.38/0.68    inference(superposition,[],[f31,f36])).
% 2.38/0.68  fof(f33,plain,(
% 2.38/0.68    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.38/0.68    inference(cnf_transformation,[],[f6])).
% 2.38/0.68  fof(f6,axiom,(
% 2.38/0.68    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.38/0.68  fof(f312,plain,(
% 2.38/0.68    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))) )),
% 2.38/0.68    inference(forward_demodulation,[],[f300,f23])).
% 2.38/0.68  fof(f300,plain,(
% 2.38/0.68    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))) )),
% 2.38/0.68    inference(superposition,[],[f219,f24])).
% 2.38/0.68  fof(f219,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))) )),
% 2.38/0.68    inference(superposition,[],[f33,f31])).
% 2.38/0.68  fof(f55,plain,(
% 2.38/0.68    ( ! [X5] : (k4_xboole_0(X5,X5) = k5_xboole_0(X5,X5)) )),
% 2.38/0.68    inference(superposition,[],[f29,f44])).
% 2.38/0.68  fof(f44,plain,(
% 2.38/0.68    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.38/0.68    inference(superposition,[],[f26,f24])).
% 2.38/0.68  fof(f493,plain,(
% 2.38/0.68    ( ! [X4,X3] : (k5_xboole_0(X3,X3) = k4_xboole_0(k1_xboole_0,X4)) )),
% 2.38/0.68    inference(superposition,[],[f487,f75])).
% 2.38/0.68  fof(f487,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.38/0.68    inference(backward_demodulation,[],[f206,f460])).
% 2.38/0.68  fof(f460,plain,(
% 2.38/0.68    ( ! [X10,X11] : (k5_xboole_0(k4_xboole_0(X11,X11),X10) = X10) )),
% 2.38/0.68    inference(superposition,[],[f414,f387])).
% 2.38/0.68  fof(f387,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k4_xboole_0(X1,X1) = k4_xboole_0(X0,X0)) )),
% 2.38/0.68    inference(superposition,[],[f367,f367])).
% 2.38/0.68  fof(f414,plain,(
% 2.38/0.68    ( ! [X0] : (k5_xboole_0(k4_xboole_0(X0,X0),X0) = X0) )),
% 2.38/0.68    inference(backward_demodulation,[],[f122,f410])).
% 2.38/0.68  fof(f122,plain,(
% 2.38/0.68    ( ! [X0] : (k5_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X0)) = X0) )),
% 2.38/0.68    inference(forward_demodulation,[],[f111,f44])).
% 2.38/0.68  fof(f111,plain,(
% 2.38/0.68    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X0))) )),
% 2.38/0.68    inference(superposition,[],[f31,f55])).
% 2.38/0.68  fof(f206,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k4_xboole_0(X0,X0),X1)) )),
% 2.38/0.68    inference(superposition,[],[f33,f55])).
% 2.38/0.68  fof(f75,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = X0) )),
% 2.38/0.68    inference(forward_demodulation,[],[f72,f24])).
% 2.38/0.68  fof(f72,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) )),
% 2.38/0.68    inference(superposition,[],[f30,f59])).
% 2.38/0.68  fof(f59,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,X1)) )),
% 2.38/0.68    inference(superposition,[],[f56,f56])).
% 2.38/0.68  fof(f56,plain,(
% 2.38/0.68    ( ! [X6] : (k4_xboole_0(k1_xboole_0,X6) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 2.38/0.68    inference(superposition,[],[f29,f47])).
% 2.38/0.68  fof(f2605,plain,(
% 2.38/0.68    ( ! [X4,X3] : (k5_xboole_0(X4,k5_xboole_0(X3,X4)) = k5_xboole_0(X3,k1_xboole_0)) )),
% 2.38/0.68    inference(superposition,[],[f487,f1939])).
% 2.38/0.68  fof(f1939,plain,(
% 2.38/0.68    ( ! [X14,X15] : (k1_xboole_0 = k5_xboole_0(X14,k5_xboole_0(X15,k5_xboole_0(X14,X15)))) )),
% 2.38/0.68    inference(backward_demodulation,[],[f242,f1921])).
% 2.38/0.68  fof(f1921,plain,(
% 2.38/0.68    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.38/0.68    inference(backward_demodulation,[],[f52,f1906])).
% 2.38/0.68  fof(f242,plain,(
% 2.38/0.68    ( ! [X14,X15] : (k1_xboole_0 = k5_xboole_0(X14,k4_xboole_0(k5_xboole_0(X15,k5_xboole_0(X14,X15)),k1_xboole_0))) )),
% 2.38/0.68    inference(backward_demodulation,[],[f224,f241])).
% 2.38/0.68  fof(f241,plain,(
% 2.38/0.68    ( ! [X19,X20] : (k4_xboole_0(k5_xboole_0(X19,X20),k1_xboole_0) = k5_xboole_0(X19,k4_xboole_0(X20,k1_xboole_0))) )),
% 2.38/0.68    inference(forward_demodulation,[],[f226,f52])).
% 2.38/0.68  fof(f226,plain,(
% 2.38/0.68    ( ! [X19,X20] : (k4_xboole_0(k5_xboole_0(X19,X20),k1_xboole_0) = k5_xboole_0(X19,k5_xboole_0(X20,k1_xboole_0))) )),
% 2.38/0.68    inference(superposition,[],[f33,f52])).
% 2.38/0.68  fof(f224,plain,(
% 2.38/0.68    ( ! [X14,X15] : (k1_xboole_0 = k5_xboole_0(X14,k5_xboole_0(X15,k4_xboole_0(k5_xboole_0(X14,X15),k1_xboole_0)))) )),
% 2.38/0.68    inference(superposition,[],[f33,f150])).
% 2.38/0.68  fof(f150,plain,(
% 2.38/0.68    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 2.38/0.68    inference(forward_demodulation,[],[f141,f36])).
% 2.38/0.68  fof(f141,plain,(
% 2.38/0.68    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(k2_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,k1_xboole_0))) )),
% 2.38/0.68    inference(superposition,[],[f130,f30])).
% 2.38/0.68  fof(f1224,plain,(
% 2.38/0.68    ( ! [X14,X15] : (k3_xboole_0(k2_xboole_0(X14,X15),X14) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X14,X15),X14),k2_xboole_0(X14,X15))) )),
% 2.38/0.68    inference(superposition,[],[f119,f415])).
% 2.38/0.68  fof(f415,plain,(
% 2.38/0.68    ( ! [X8,X7] : (k2_xboole_0(X7,X8) = k2_xboole_0(X7,k2_xboole_0(X7,X8))) )),
% 2.38/0.68    inference(backward_demodulation,[],[f98,f398])).
% 2.38/0.68  fof(f398,plain,(
% 2.38/0.68    ( ! [X6,X5] : (k5_xboole_0(X6,k4_xboole_0(X5,X5)) = X6) )),
% 2.38/0.68    inference(superposition,[],[f75,f367])).
% 2.38/0.68  fof(f98,plain,(
% 2.38/0.68    ( ! [X8,X7] : (k5_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X7,X7)) = k2_xboole_0(X7,k2_xboole_0(X7,X8))) )),
% 2.38/0.68    inference(forward_demodulation,[],[f97,f25])).
% 2.38/0.68  fof(f97,plain,(
% 2.38/0.68    ( ! [X8,X7] : (k2_xboole_0(k2_xboole_0(X7,X8),X7) = k5_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X7,X7))) )),
% 2.38/0.68    inference(superposition,[],[f30,f58])).
% 2.38/0.68  fof(f119,plain,(
% 2.38/0.68    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X2,X1))) )),
% 2.38/0.68    inference(superposition,[],[f31,f25])).
% 2.38/0.68  fof(f3847,plain,(
% 2.38/0.68    k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) = k3_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2)),
% 2.38/0.68    inference(superposition,[],[f2362,f2690])).
% 2.38/0.68  fof(f2690,plain,(
% 2.38/0.68    sK2 = k5_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))),
% 2.38/0.68    inference(superposition,[],[f2649,f1122])).
% 2.38/0.68  fof(f1122,plain,(
% 2.38/0.68    k2_tarski(sK0,sK1) = k5_xboole_0(sK2,k2_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 2.38/0.68    inference(forward_demodulation,[],[f1121,f45])).
% 2.38/0.68  fof(f45,plain,(
% 2.38/0.68    ( ! [X2,X1] : (k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1) )),
% 2.38/0.68    inference(superposition,[],[f26,f25])).
% 2.38/0.68  fof(f1121,plain,(
% 2.38/0.68    k5_xboole_0(sK2,k2_xboole_0(sK2,k2_tarski(sK0,sK1))) = k3_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 2.38/0.68    inference(forward_demodulation,[],[f1120,f416])).
% 2.38/0.68  fof(f416,plain,(
% 2.38/0.68    ( ! [X8,X9] : (k2_xboole_0(X9,X8) = k2_xboole_0(X8,k2_xboole_0(X9,X8))) )),
% 2.38/0.68    inference(backward_demodulation,[],[f110,f398])).
% 2.38/0.68  fof(f110,plain,(
% 2.38/0.68    ( ! [X8,X9] : (k5_xboole_0(k2_xboole_0(X9,X8),k4_xboole_0(X8,X8)) = k2_xboole_0(X8,k2_xboole_0(X9,X8))) )),
% 2.38/0.68    inference(forward_demodulation,[],[f109,f25])).
% 2.38/0.68  fof(f109,plain,(
% 2.38/0.68    ( ! [X8,X9] : (k2_xboole_0(k2_xboole_0(X9,X8),X8) = k5_xboole_0(k2_xboole_0(X9,X8),k4_xboole_0(X8,X8))) )),
% 2.38/0.68    inference(superposition,[],[f30,f57])).
% 2.38/0.68  fof(f57,plain,(
% 2.38/0.68    ( ! [X4,X3] : (k4_xboole_0(X3,k2_xboole_0(X4,X3)) = k4_xboole_0(X3,X3)) )),
% 2.38/0.68    inference(backward_demodulation,[],[f54,f55])).
% 2.38/0.68  fof(f54,plain,(
% 2.38/0.68    ( ! [X4,X3] : (k4_xboole_0(X3,k2_xboole_0(X4,X3)) = k5_xboole_0(X3,X3)) )),
% 2.38/0.68    inference(superposition,[],[f29,f45])).
% 2.38/0.68  fof(f1120,plain,(
% 2.38/0.68    k3_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(sK2,k2_tarski(sK0,sK1))) = k5_xboole_0(sK2,k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(sK2,k2_tarski(sK0,sK1))))),
% 2.38/0.68    inference(forward_demodulation,[],[f1117,f25])).
% 2.38/0.68  fof(f1117,plain,(
% 2.38/0.68    k3_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(sK2,k2_tarski(sK0,sK1))) = k5_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)))),
% 2.38/0.68    inference(superposition,[],[f119,f1086])).
% 2.38/0.68  fof(f1086,plain,(
% 2.38/0.68    sK2 = k5_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 2.38/0.68    inference(superposition,[],[f487,f828])).
% 2.38/0.68  fof(f828,plain,(
% 2.38/0.68    k2_xboole_0(sK2,k2_tarski(sK0,sK1)) = k5_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.38/0.68    inference(forward_demodulation,[],[f827,f25])).
% 2.38/0.68  fof(f827,plain,(
% 2.38/0.68    k2_xboole_0(k2_tarski(sK0,sK1),sK2) = k5_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.38/0.68    inference(superposition,[],[f30,f825])).
% 2.38/0.68  fof(f825,plain,(
% 2.38/0.68    sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 2.38/0.68    inference(resolution,[],[f818,f20])).
% 2.38/0.68  fof(f20,plain,(
% 2.38/0.68    ~r2_hidden(sK0,sK2)),
% 2.38/0.68    inference(cnf_transformation,[],[f19])).
% 2.38/0.68  fof(f19,plain,(
% 2.38/0.68    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 2.38/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).
% 2.38/0.68  fof(f18,plain,(
% 2.38/0.68    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 2.38/0.68    introduced(choice_axiom,[])).
% 2.38/0.68  fof(f16,plain,(
% 2.38/0.68    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.38/0.68    inference(ennf_transformation,[],[f15])).
% 2.38/0.68  fof(f15,negated_conjecture,(
% 2.38/0.68    ~! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.38/0.68    inference(negated_conjecture,[],[f14])).
% 2.38/0.68  fof(f14,conjecture,(
% 2.38/0.68    ! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_zfmisc_1)).
% 2.38/0.68  fof(f818,plain,(
% 2.38/0.68    ( ! [X1] : (r2_hidden(X1,sK2) | sK2 = k4_xboole_0(sK2,k2_tarski(X1,sK1))) )),
% 2.38/0.68    inference(resolution,[],[f35,f21])).
% 2.38/0.68  fof(f21,plain,(
% 2.38/0.68    ~r2_hidden(sK1,sK2)),
% 2.38/0.68    inference(cnf_transformation,[],[f19])).
% 2.38/0.68  fof(f35,plain,(
% 2.38/0.68    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X0,X2)) )),
% 2.38/0.68    inference(cnf_transformation,[],[f17])).
% 2.38/0.68  fof(f17,plain,(
% 2.38/0.68    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 2.38/0.68    inference(ennf_transformation,[],[f13])).
% 2.38/0.68  fof(f13,axiom,(
% 2.38/0.68    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 2.38/0.68  fof(f2362,plain,(
% 2.38/0.68    ( ! [X2,X1] : (k3_xboole_0(X1,k5_xboole_0(X1,X2)) = k4_xboole_0(X1,X2)) )),
% 2.38/0.68    inference(forward_demodulation,[],[f2361,f522])).
% 2.38/0.68  fof(f522,plain,(
% 2.38/0.68    ( ! [X8,X9] : (k5_xboole_0(X9,k2_xboole_0(X8,X9)) = k4_xboole_0(X8,X9)) )),
% 2.38/0.68    inference(forward_demodulation,[],[f496,f29])).
% 2.38/0.68  fof(f496,plain,(
% 2.38/0.68    ( ! [X8,X9] : (k5_xboole_0(X9,k2_xboole_0(X8,X9)) = k5_xboole_0(X8,k3_xboole_0(X8,X9))) )),
% 2.38/0.68    inference(superposition,[],[f487,f219])).
% 2.38/0.68  fof(f2361,plain,(
% 2.38/0.68    ( ! [X2,X1] : (k5_xboole_0(X2,k2_xboole_0(X1,X2)) = k3_xboole_0(X1,k5_xboole_0(X1,X2))) )),
% 2.38/0.68    inference(backward_demodulation,[],[f547,f2360])).
% 2.38/0.68  fof(f2360,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.38/0.68    inference(forward_demodulation,[],[f2342,f30])).
% 2.38/0.68  fof(f2342,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.38/0.68    inference(superposition,[],[f30,f1934])).
% 2.38/0.68  fof(f1934,plain,(
% 2.38/0.68    ( ! [X2,X3] : (k4_xboole_0(X3,X2) = k4_xboole_0(k5_xboole_0(X2,X3),X2)) )),
% 2.38/0.68    inference(backward_demodulation,[],[f1719,f1921])).
% 2.38/0.68  fof(f1719,plain,(
% 2.38/0.68    ( ! [X2,X3] : (k4_xboole_0(k5_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X3,k1_xboole_0),X2)) )),
% 2.38/0.68    inference(backward_demodulation,[],[f1690,f1718])).
% 2.38/0.68  fof(f1718,plain,(
% 2.38/0.68    ( ! [X21,X22,X20] : (k2_xboole_0(k4_xboole_0(X22,X22),k4_xboole_0(X20,X21)) = k4_xboole_0(k4_xboole_0(X20,k1_xboole_0),X21)) )),
% 2.38/0.68    inference(forward_demodulation,[],[f1717,f526])).
% 2.38/0.68  fof(f526,plain,(
% 2.38/0.68    ( ! [X10] : (k5_xboole_0(k1_xboole_0,X10) = k4_xboole_0(X10,k1_xboole_0)) )),
% 2.38/0.68    inference(forward_demodulation,[],[f497,f52])).
% 2.38/0.68  fof(f497,plain,(
% 2.38/0.68    ( ! [X10] : (k5_xboole_0(k1_xboole_0,X10) = k5_xboole_0(X10,k1_xboole_0)) )),
% 2.38/0.68    inference(superposition,[],[f487,f312])).
% 2.38/0.68  fof(f1717,plain,(
% 2.38/0.68    ( ! [X21,X22,X20] : (k4_xboole_0(k5_xboole_0(k1_xboole_0,X20),X21) = k2_xboole_0(k4_xboole_0(X22,X22),k4_xboole_0(X20,X21))) )),
% 2.38/0.68    inference(forward_demodulation,[],[f1624,f36])).
% 2.38/0.68  fof(f1624,plain,(
% 2.38/0.68    ( ! [X21,X22,X20] : (k4_xboole_0(k5_xboole_0(k1_xboole_0,X20),X21) = k2_xboole_0(k4_xboole_0(X22,X22),k4_xboole_0(X20,k2_xboole_0(k1_xboole_0,X21)))) )),
% 2.38/0.68    inference(superposition,[],[f34,f388])).
% 2.38/0.68  fof(f388,plain,(
% 2.38/0.68    ( ! [X2,X3] : (k4_xboole_0(X3,X3) = k4_xboole_0(k1_xboole_0,X2)) )),
% 2.38/0.68    inference(superposition,[],[f367,f59])).
% 2.38/0.68  fof(f1690,plain,(
% 2.38/0.68    ( ! [X2,X3] : (k4_xboole_0(k5_xboole_0(X2,X3),X2) = k2_xboole_0(k4_xboole_0(X2,X2),k4_xboole_0(X3,X2))) )),
% 2.38/0.68    inference(forward_demodulation,[],[f1617,f410])).
% 2.38/0.68  fof(f1617,plain,(
% 2.38/0.68    ( ! [X2,X3] : (k4_xboole_0(k5_xboole_0(X2,X3),X2) = k2_xboole_0(k4_xboole_0(X2,X2),k4_xboole_0(X3,k2_xboole_0(X2,X2)))) )),
% 2.38/0.68    inference(superposition,[],[f34,f57])).
% 2.38/0.68  fof(f547,plain,(
% 2.38/0.68    ( ! [X2,X1] : (k3_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k2_xboole_0(X1,k5_xboole_0(X1,X2)))) )),
% 2.38/0.68    inference(forward_demodulation,[],[f512,f25])).
% 2.38/0.68  fof(f512,plain,(
% 2.38/0.68    ( ! [X2,X1] : (k3_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k2_xboole_0(k5_xboole_0(X1,X2),X1))) )),
% 2.38/0.68    inference(superposition,[],[f119,f487])).
% 2.38/0.68  fof(f22,plain,(
% 2.38/0.68    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))),
% 2.38/0.68    inference(cnf_transformation,[],[f19])).
% 2.38/0.68  % SZS output end Proof for theBenchmark
% 2.38/0.68  % (3820)------------------------------
% 2.38/0.68  % (3820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.38/0.68  % (3820)Termination reason: Refutation
% 2.38/0.68  
% 2.38/0.68  % (3820)Memory used [KB]: 7931
% 2.38/0.68  % (3820)Time elapsed: 0.233 s
% 2.38/0.68  % (3820)------------------------------
% 2.38/0.68  % (3820)------------------------------
% 2.38/0.68  % (3803)Success in time 0.318 s
%------------------------------------------------------------------------------
