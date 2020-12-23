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
% DateTime   : Thu Dec  3 12:32:28 EST 2020

% Result     : Theorem 32.88s
% Output     : Refutation 32.88s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 988 expanded)
%              Number of leaves         :   21 ( 329 expanded)
%              Depth                    :   26
%              Number of atoms          :  109 ( 989 expanded)
%              Number of equality atoms :  108 ( 988 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f116051,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f116050])).

fof(f116050,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f116047,f53])).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f116047,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f115699,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f115699,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f115698,f20900])).

fof(f20900,plain,(
    ! [X4,X2,X3] : k3_xboole_0(X3,k3_xboole_0(X2,X4)) = k3_xboole_0(X3,k3_xboole_0(X4,X2)) ),
    inference(forward_demodulation,[],[f20899,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20899,plain,(
    ! [X4,X2,X3] : k3_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X4))) = k3_xboole_0(X3,k3_xboole_0(X4,X2)) ),
    inference(forward_demodulation,[],[f20699,f9787])).

fof(f9787,plain,(
    ! [X19,X20,X18] : k3_xboole_0(X18,k4_xboole_0(X19,k4_xboole_0(X18,X20))) = k3_xboole_0(X18,k3_xboole_0(X20,X19)) ),
    inference(backward_demodulation,[],[f855,f9778])).

fof(f9778,plain,(
    ! [X43,X44,X42] : k3_xboole_0(k3_xboole_0(X42,X44),X43) = k3_xboole_0(X42,k3_xboole_0(X43,X44)) ),
    inference(backward_demodulation,[],[f2929,f9777])).

fof(f9777,plain,(
    ! [X17,X18,X16] : k5_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X16,k4_xboole_0(X17,X18))) = k3_xboole_0(X16,k3_xboole_0(X17,X18)) ),
    inference(forward_demodulation,[],[f9776,f45])).

fof(f9776,plain,(
    ! [X17,X18,X16] : k5_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X16,k4_xboole_0(X17,X18))) = k3_xboole_0(X16,k4_xboole_0(X17,k4_xboole_0(X17,X18))) ),
    inference(forward_demodulation,[],[f9775,f102])).

fof(f102,plain,(
    ! [X3] : k2_xboole_0(k1_xboole_0,X3) = X3 ),
    inference(forward_demodulation,[],[f96,f66])).

fof(f66,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f42,f39])).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f96,plain,(
    ! [X3] : k2_xboole_0(k1_xboole_0,X3) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f46,f40])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f9775,plain,(
    ! [X17,X18,X16] : k5_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X16,k4_xboole_0(X17,X18))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X16,k4_xboole_0(X17,k4_xboole_0(X17,X18)))) ),
    inference(forward_demodulation,[],[f9774,f6207])).

fof(f6207,plain,(
    ! [X14,X15,X13] : k3_xboole_0(X13,k4_xboole_0(X14,X15)) = k4_xboole_0(X13,k2_xboole_0(X15,k4_xboole_0(X13,X14))) ),
    inference(backward_demodulation,[],[f2989,f6183])).

fof(f6183,plain,(
    ! [X47,X48,X46] : k3_xboole_0(X46,k4_xboole_0(X48,X47)) = k3_xboole_0(k4_xboole_0(X46,X47),X48) ),
    inference(forward_demodulation,[],[f6182,f968])).

fof(f968,plain,(
    ! [X14,X15,X13] : k3_xboole_0(X13,k4_xboole_0(X14,X15)) = k3_xboole_0(k3_xboole_0(X13,X14),k4_xboole_0(X13,X15)) ),
    inference(forward_demodulation,[],[f921,f584])).

fof(f584,plain,(
    ! [X14,X15,X13] : k3_xboole_0(X13,k4_xboole_0(X14,X15)) = k4_xboole_0(X13,k2_xboole_0(k4_xboole_0(X13,X14),X15)) ),
    inference(forward_demodulation,[],[f553,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f553,plain,(
    ! [X14,X15,X13] : k4_xboole_0(k3_xboole_0(X13,X14),X15) = k4_xboole_0(X13,k2_xboole_0(k4_xboole_0(X13,X14),X15)) ),
    inference(superposition,[],[f57,f45])).

fof(f57,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f921,plain,(
    ! [X14,X15,X13] : k4_xboole_0(X13,k2_xboole_0(k4_xboole_0(X13,X14),X15)) = k3_xboole_0(k3_xboole_0(X13,X14),k4_xboole_0(X13,X15)) ),
    inference(superposition,[],[f61,f45])).

fof(f61,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

fof(f6182,plain,(
    ! [X47,X48,X46] : k3_xboole_0(k3_xboole_0(X46,X48),k4_xboole_0(X46,X47)) = k3_xboole_0(k4_xboole_0(X46,X47),X48) ),
    inference(forward_demodulation,[],[f6071,f5860])).

fof(f5860,plain,(
    ! [X47,X48,X46] : k3_xboole_0(k4_xboole_0(X46,X47),X48) = k5_xboole_0(k5_xboole_0(k3_xboole_0(X46,X48),k4_xboole_0(X46,X47)),k4_xboole_0(X46,k4_xboole_0(X47,X48))) ),
    inference(forward_demodulation,[],[f5755,f2988])).

fof(f2988,plain,(
    ! [X12,X10,X11] : k3_xboole_0(k4_xboole_0(X10,X11),k3_xboole_0(X10,X12)) = k3_xboole_0(k4_xboole_0(X10,X11),X12) ),
    inference(backward_demodulation,[],[f1001,f2955])).

fof(f2955,plain,(
    ! [X35,X33,X34] : k3_xboole_0(k4_xboole_0(X33,X34),X35) = k5_xboole_0(k4_xboole_0(X33,X34),k4_xboole_0(X33,k2_xboole_0(X34,X35))) ),
    inference(superposition,[],[f258,f57])).

fof(f258,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k5_xboole_0(X8,k4_xboole_0(X8,X9)) ),
    inference(forward_demodulation,[],[f257,f102])).

fof(f257,plain,(
    ! [X8,X9] : k5_xboole_0(X8,k4_xboole_0(X8,X9)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X8,X9)) ),
    inference(forward_demodulation,[],[f256,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f256,plain,(
    ! [X8,X9] : k5_xboole_0(X8,k4_xboole_0(X8,X9)) = k2_xboole_0(k3_xboole_0(X8,X9),k1_xboole_0) ),
    inference(forward_demodulation,[],[f255,f83])).

fof(f83,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f41,f44])).

fof(f41,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f255,plain,(
    ! [X8,X9] : k5_xboole_0(X8,k4_xboole_0(X8,X9)) = k2_xboole_0(k3_xboole_0(X8,X9),k4_xboole_0(X8,k2_xboole_0(X9,X8))) ),
    inference(forward_demodulation,[],[f226,f57])).

fof(f226,plain,(
    ! [X8,X9] : k5_xboole_0(X8,k4_xboole_0(X8,X9)) = k2_xboole_0(k3_xboole_0(X8,X9),k4_xboole_0(k4_xboole_0(X8,X9),X8)) ),
    inference(superposition,[],[f52,f45])).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f1001,plain,(
    ! [X12,X10,X11] : k5_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X10,k2_xboole_0(X11,X12))) = k3_xboole_0(k4_xboole_0(X10,X11),k3_xboole_0(X10,X12)) ),
    inference(forward_demodulation,[],[f1000,f935])).

fof(f935,plain,(
    ! [X14,X15,X13] : k4_xboole_0(X13,k2_xboole_0(X15,k4_xboole_0(X13,X14))) = k3_xboole_0(k4_xboole_0(X13,X15),k3_xboole_0(X13,X14)) ),
    inference(superposition,[],[f61,f45])).

fof(f1000,plain,(
    ! [X12,X10,X11] : k5_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X10,k2_xboole_0(X11,X12))) = k4_xboole_0(X10,k2_xboole_0(X11,k4_xboole_0(X10,X12))) ),
    inference(forward_demodulation,[],[f952,f57])).

fof(f952,plain,(
    ! [X12,X10,X11] : k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X10,X12)) = k5_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X10,k2_xboole_0(X11,X12))) ),
    inference(superposition,[],[f48,f61])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f5755,plain,(
    ! [X47,X48,X46] : k3_xboole_0(k4_xboole_0(X46,X47),k3_xboole_0(X46,X48)) = k5_xboole_0(k5_xboole_0(k3_xboole_0(X46,X48),k4_xboole_0(X46,X47)),k4_xboole_0(X46,k4_xboole_0(X47,X48))) ),
    inference(superposition,[],[f361,f62])).

fof(f361,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f54,f42])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f6071,plain,(
    ! [X47,X48,X46] : k3_xboole_0(k3_xboole_0(X46,X48),k4_xboole_0(X46,X47)) = k5_xboole_0(k5_xboole_0(k3_xboole_0(X46,X48),k4_xboole_0(X46,X47)),k4_xboole_0(X46,k4_xboole_0(X47,X48))) ),
    inference(superposition,[],[f369,f62])).

fof(f369,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f54,f44])).

fof(f2989,plain,(
    ! [X14,X15,X13] : k4_xboole_0(X13,k2_xboole_0(X15,k4_xboole_0(X13,X14))) = k3_xboole_0(k4_xboole_0(X13,X15),X14) ),
    inference(backward_demodulation,[],[f935,f2988])).

fof(f9774,plain,(
    ! [X17,X18,X16] : k5_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X16,k4_xboole_0(X17,X18))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X16,k2_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X16,X17)))) ),
    inference(forward_demodulation,[],[f9650,f57])).

fof(f9650,plain,(
    ! [X17,X18,X16] : k5_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X16,k4_xboole_0(X17,X18))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X17,X18)),k4_xboole_0(X16,X17))) ),
    inference(superposition,[],[f52,f1061])).

fof(f1061,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X3,X4))) ),
    inference(superposition,[],[f41,f62])).

fof(f2929,plain,(
    ! [X43,X44,X42] : k5_xboole_0(k4_xboole_0(X42,X43),k4_xboole_0(X42,k4_xboole_0(X43,X44))) = k3_xboole_0(k3_xboole_0(X42,X44),X43) ),
    inference(forward_demodulation,[],[f2928,f855])).

fof(f2928,plain,(
    ! [X43,X44,X42] : k5_xboole_0(k4_xboole_0(X42,X43),k4_xboole_0(X42,k4_xboole_0(X43,X44))) = k3_xboole_0(X42,k4_xboole_0(X44,k4_xboole_0(X42,X43))) ),
    inference(forward_demodulation,[],[f2884,f56])).

fof(f2884,plain,(
    ! [X43,X44,X42] : k4_xboole_0(k3_xboole_0(X42,X44),k4_xboole_0(X42,X43)) = k5_xboole_0(k4_xboole_0(X42,X43),k4_xboole_0(X42,k4_xboole_0(X43,X44))) ),
    inference(superposition,[],[f248,f62])).

fof(f248,plain,(
    ! [X2,X1] : k4_xboole_0(X2,X1) = k5_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f247,f102])).

fof(f247,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f222,f153])).

fof(f153,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f50,f44])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f222,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X1,X2),X1)) ),
    inference(superposition,[],[f52,f41])).

fof(f855,plain,(
    ! [X19,X20,X18] : k3_xboole_0(k3_xboole_0(X18,X19),X20) = k3_xboole_0(X18,k4_xboole_0(X19,k4_xboole_0(X18,X20))) ),
    inference(backward_demodulation,[],[f518,f854])).

fof(f854,plain,(
    ! [X14,X15,X13] : k4_xboole_0(X13,k3_xboole_0(X15,k4_xboole_0(X13,X14))) = k4_xboole_0(X13,k4_xboole_0(X15,X14)) ),
    inference(forward_demodulation,[],[f802,f62])).

fof(f802,plain,(
    ! [X14,X15,X13] : k4_xboole_0(X13,k3_xboole_0(X15,k4_xboole_0(X13,X14))) = k2_xboole_0(k4_xboole_0(X13,X15),k3_xboole_0(X13,X14)) ),
    inference(superposition,[],[f60,f45])).

fof(f60,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f518,plain,(
    ! [X19,X20,X18] : k3_xboole_0(k3_xboole_0(X18,X19),X20) = k3_xboole_0(X18,k4_xboole_0(X19,k3_xboole_0(X18,k4_xboole_0(X19,X20)))) ),
    inference(forward_demodulation,[],[f499,f56])).

fof(f499,plain,(
    ! [X19,X20,X18] : k3_xboole_0(k3_xboole_0(X18,X19),X20) = k3_xboole_0(X18,k4_xboole_0(X19,k4_xboole_0(k3_xboole_0(X18,X19),X20))) ),
    inference(superposition,[],[f56,f45])).

fof(f20699,plain,(
    ! [X4,X2,X3] : k3_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X4))) = k3_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X3,X4))) ),
    inference(superposition,[],[f709,f854])).

fof(f709,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,k4_xboole_0(X4,k3_xboole_0(X3,X5))) = k3_xboole_0(X3,k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f59,f56])).

fof(f59,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f115698,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k3_xboole_0(sK2,sK1))) ),
    inference(forward_demodulation,[],[f115697,f115691])).

fof(f115691,plain,(
    ! [X19,X17,X18] : k3_xboole_0(X17,k3_xboole_0(X19,X18)) = k3_xboole_0(X18,k3_xboole_0(X17,X19)) ),
    inference(forward_demodulation,[],[f115218,f45])).

fof(f115218,plain,(
    ! [X19,X17,X18] : k3_xboole_0(X18,k4_xboole_0(X17,k4_xboole_0(X17,X19))) = k3_xboole_0(X17,k3_xboole_0(X19,X18)) ),
    inference(superposition,[],[f7626,f9787])).

fof(f7626,plain,(
    ! [X8,X7,X9] : k3_xboole_0(X7,k4_xboole_0(X8,X9)) = k3_xboole_0(X8,k4_xboole_0(X7,X9)) ),
    inference(superposition,[],[f488,f56])).

fof(f488,plain,(
    ! [X4,X2,X3] : k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(k3_xboole_0(X3,X2),X4) ),
    inference(superposition,[],[f56,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f115697,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK1,k3_xboole_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f115693,f20900])).

fof(f115693,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK1,k3_xboole_0(sK2,sK0))) ),
    inference(backward_demodulation,[],[f65,f115691])).

fof(f65,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK2,k3_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f35,f43])).

fof(f35,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2))
   => k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:31:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (22455)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.47  % (22442)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (22448)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (22452)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (22437)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (22441)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (22445)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (22451)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (22440)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (22453)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (22439)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (22438)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.52  % (22446)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (22449)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.52  % (22449)Refutation not found, incomplete strategy% (22449)------------------------------
% 0.21/0.52  % (22449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22449)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22449)Memory used [KB]: 10618
% 0.21/0.52  % (22449)Time elapsed: 0.096 s
% 0.21/0.52  % (22449)------------------------------
% 0.21/0.52  % (22449)------------------------------
% 0.21/0.53  % (22450)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.53  % (22443)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (22447)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.55  % (22454)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 5.32/1.04  % (22441)Time limit reached!
% 5.32/1.04  % (22441)------------------------------
% 5.32/1.04  % (22441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.32/1.04  % (22441)Termination reason: Time limit
% 5.32/1.04  % (22441)Termination phase: Saturation
% 5.32/1.04  
% 5.32/1.04  % (22441)Memory used [KB]: 16502
% 5.32/1.04  % (22441)Time elapsed: 0.600 s
% 5.32/1.04  % (22441)------------------------------
% 5.32/1.04  % (22441)------------------------------
% 12.42/1.93  % (22442)Time limit reached!
% 12.42/1.93  % (22442)------------------------------
% 12.42/1.93  % (22442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.42/1.94  % (22442)Termination reason: Time limit
% 12.42/1.94  % (22442)Termination phase: Saturation
% 12.42/1.94  
% 12.42/1.94  % (22442)Memory used [KB]: 39658
% 12.42/1.94  % (22442)Time elapsed: 1.500 s
% 12.42/1.94  % (22442)------------------------------
% 12.42/1.94  % (22442)------------------------------
% 12.76/1.96  % (22443)Time limit reached!
% 12.76/1.96  % (22443)------------------------------
% 12.76/1.96  % (22443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.76/1.96  % (22443)Termination reason: Time limit
% 12.76/1.96  % (22443)Termination phase: Saturation
% 12.76/1.96  
% 12.76/1.96  % (22443)Memory used [KB]: 37483
% 12.76/1.96  % (22443)Time elapsed: 1.500 s
% 12.76/1.96  % (22443)------------------------------
% 12.76/1.96  % (22443)------------------------------
% 14.46/2.22  % (22439)Time limit reached!
% 14.46/2.22  % (22439)------------------------------
% 14.46/2.22  % (22439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.46/2.22  % (22439)Termination reason: Time limit
% 14.46/2.22  % (22439)Termination phase: Saturation
% 14.46/2.22  
% 14.46/2.22  % (22439)Memory used [KB]: 44775
% 14.46/2.22  % (22439)Time elapsed: 1.800 s
% 14.46/2.22  % (22439)------------------------------
% 14.46/2.22  % (22439)------------------------------
% 18.21/2.64  % (22450)Time limit reached!
% 18.21/2.64  % (22450)------------------------------
% 18.21/2.64  % (22450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.21/2.64  % (22450)Termination reason: Time limit
% 18.21/2.64  % (22450)Termination phase: Saturation
% 18.21/2.64  
% 18.21/2.64  % (22450)Memory used [KB]: 44903
% 18.21/2.64  % (22450)Time elapsed: 2.200 s
% 18.21/2.64  % (22450)------------------------------
% 18.21/2.64  % (22450)------------------------------
% 32.88/4.49  % (22440)Refutation found. Thanks to Tanya!
% 32.88/4.49  % SZS status Theorem for theBenchmark
% 32.88/4.49  % SZS output start Proof for theBenchmark
% 32.88/4.49  fof(f116051,plain,(
% 32.88/4.49    $false),
% 32.88/4.49    inference(trivial_inequality_removal,[],[f116050])).
% 32.88/4.49  fof(f116050,plain,(
% 32.88/4.49    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k5_xboole_0(sK1,sK2))),
% 32.88/4.49    inference(forward_demodulation,[],[f116047,f53])).
% 32.88/4.49  fof(f53,plain,(
% 32.88/4.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 32.88/4.49    inference(cnf_transformation,[],[f7])).
% 32.88/4.49  fof(f7,axiom,(
% 32.88/4.49    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 32.88/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).
% 32.88/4.49  fof(f116047,plain,(
% 32.88/4.49    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))),
% 32.88/4.49    inference(superposition,[],[f115699,f62])).
% 32.88/4.49  fof(f62,plain,(
% 32.88/4.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 32.88/4.49    inference(cnf_transformation,[],[f22])).
% 32.88/4.49  fof(f22,axiom,(
% 32.88/4.49    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 32.88/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 32.88/4.49  fof(f115699,plain,(
% 32.88/4.49    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))),
% 32.88/4.49    inference(forward_demodulation,[],[f115698,f20900])).
% 32.88/4.49  fof(f20900,plain,(
% 32.88/4.49    ( ! [X4,X2,X3] : (k3_xboole_0(X3,k3_xboole_0(X2,X4)) = k3_xboole_0(X3,k3_xboole_0(X4,X2))) )),
% 32.88/4.49    inference(forward_demodulation,[],[f20899,f45])).
% 32.88/4.49  fof(f45,plain,(
% 32.88/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 32.88/4.49    inference(cnf_transformation,[],[f18])).
% 32.88/4.49  fof(f18,axiom,(
% 32.88/4.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 32.88/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 32.88/4.49  fof(f20899,plain,(
% 32.88/4.49    ( ! [X4,X2,X3] : (k3_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X4))) = k3_xboole_0(X3,k3_xboole_0(X4,X2))) )),
% 32.88/4.49    inference(forward_demodulation,[],[f20699,f9787])).
% 32.88/4.49  fof(f9787,plain,(
% 32.88/4.49    ( ! [X19,X20,X18] : (k3_xboole_0(X18,k4_xboole_0(X19,k4_xboole_0(X18,X20))) = k3_xboole_0(X18,k3_xboole_0(X20,X19))) )),
% 32.88/4.49    inference(backward_demodulation,[],[f855,f9778])).
% 32.88/4.49  fof(f9778,plain,(
% 32.88/4.49    ( ! [X43,X44,X42] : (k3_xboole_0(k3_xboole_0(X42,X44),X43) = k3_xboole_0(X42,k3_xboole_0(X43,X44))) )),
% 32.88/4.49    inference(backward_demodulation,[],[f2929,f9777])).
% 32.88/4.49  fof(f9777,plain,(
% 32.88/4.49    ( ! [X17,X18,X16] : (k5_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X16,k4_xboole_0(X17,X18))) = k3_xboole_0(X16,k3_xboole_0(X17,X18))) )),
% 32.88/4.49    inference(forward_demodulation,[],[f9776,f45])).
% 32.88/4.49  fof(f9776,plain,(
% 32.88/4.49    ( ! [X17,X18,X16] : (k5_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X16,k4_xboole_0(X17,X18))) = k3_xboole_0(X16,k4_xboole_0(X17,k4_xboole_0(X17,X18)))) )),
% 32.88/4.49    inference(forward_demodulation,[],[f9775,f102])).
% 32.88/4.49  fof(f102,plain,(
% 32.88/4.49    ( ! [X3] : (k2_xboole_0(k1_xboole_0,X3) = X3) )),
% 32.88/4.49    inference(forward_demodulation,[],[f96,f66])).
% 32.88/4.49  fof(f66,plain,(
% 32.88/4.49    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 32.88/4.49    inference(superposition,[],[f42,f39])).
% 32.88/4.49  fof(f39,plain,(
% 32.88/4.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 32.88/4.49    inference(cnf_transformation,[],[f24])).
% 32.88/4.49  fof(f24,axiom,(
% 32.88/4.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 32.88/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 32.88/4.49  fof(f42,plain,(
% 32.88/4.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 32.88/4.49    inference(cnf_transformation,[],[f3])).
% 32.88/4.49  fof(f3,axiom,(
% 32.88/4.49    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 32.88/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 32.88/4.49  fof(f96,plain,(
% 32.88/4.49    ( ! [X3] : (k2_xboole_0(k1_xboole_0,X3) = k5_xboole_0(k1_xboole_0,X3)) )),
% 32.88/4.49    inference(superposition,[],[f46,f40])).
% 32.88/4.49  fof(f40,plain,(
% 32.88/4.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 32.88/4.49    inference(cnf_transformation,[],[f12])).
% 32.88/4.49  fof(f12,axiom,(
% 32.88/4.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 32.88/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 32.88/4.49  fof(f46,plain,(
% 32.88/4.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 32.88/4.49    inference(cnf_transformation,[],[f28])).
% 32.88/4.49  fof(f28,axiom,(
% 32.88/4.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 32.88/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 32.88/4.49  fof(f9775,plain,(
% 32.88/4.49    ( ! [X17,X18,X16] : (k5_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X16,k4_xboole_0(X17,X18))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X16,k4_xboole_0(X17,k4_xboole_0(X17,X18))))) )),
% 32.88/4.49    inference(forward_demodulation,[],[f9774,f6207])).
% 32.88/4.49  fof(f6207,plain,(
% 32.88/4.49    ( ! [X14,X15,X13] : (k3_xboole_0(X13,k4_xboole_0(X14,X15)) = k4_xboole_0(X13,k2_xboole_0(X15,k4_xboole_0(X13,X14)))) )),
% 32.88/4.49    inference(backward_demodulation,[],[f2989,f6183])).
% 32.88/4.49  fof(f6183,plain,(
% 32.88/4.49    ( ! [X47,X48,X46] : (k3_xboole_0(X46,k4_xboole_0(X48,X47)) = k3_xboole_0(k4_xboole_0(X46,X47),X48)) )),
% 32.88/4.49    inference(forward_demodulation,[],[f6182,f968])).
% 32.88/4.49  fof(f968,plain,(
% 32.88/4.49    ( ! [X14,X15,X13] : (k3_xboole_0(X13,k4_xboole_0(X14,X15)) = k3_xboole_0(k3_xboole_0(X13,X14),k4_xboole_0(X13,X15))) )),
% 32.88/4.49    inference(forward_demodulation,[],[f921,f584])).
% 32.88/4.49  fof(f584,plain,(
% 32.88/4.49    ( ! [X14,X15,X13] : (k3_xboole_0(X13,k4_xboole_0(X14,X15)) = k4_xboole_0(X13,k2_xboole_0(k4_xboole_0(X13,X14),X15))) )),
% 32.88/4.49    inference(forward_demodulation,[],[f553,f56])).
% 32.88/4.49  fof(f56,plain,(
% 32.88/4.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 32.88/4.49    inference(cnf_transformation,[],[f19])).
% 32.88/4.49  fof(f19,axiom,(
% 32.88/4.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 32.88/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 32.88/4.49  fof(f553,plain,(
% 32.88/4.49    ( ! [X14,X15,X13] : (k4_xboole_0(k3_xboole_0(X13,X14),X15) = k4_xboole_0(X13,k2_xboole_0(k4_xboole_0(X13,X14),X15))) )),
% 32.88/4.49    inference(superposition,[],[f57,f45])).
% 32.88/4.49  fof(f57,plain,(
% 32.88/4.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 32.88/4.49    inference(cnf_transformation,[],[f14])).
% 32.88/4.49  fof(f14,axiom,(
% 32.88/4.49    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 32.88/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 32.88/4.49  fof(f921,plain,(
% 32.88/4.49    ( ! [X14,X15,X13] : (k4_xboole_0(X13,k2_xboole_0(k4_xboole_0(X13,X14),X15)) = k3_xboole_0(k3_xboole_0(X13,X14),k4_xboole_0(X13,X15))) )),
% 32.88/4.49    inference(superposition,[],[f61,f45])).
% 32.88/4.49  fof(f61,plain,(
% 32.88/4.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 32.88/4.49    inference(cnf_transformation,[],[f23])).
% 32.88/4.49  fof(f23,axiom,(
% 32.88/4.49    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 32.88/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).
% 32.88/4.49  fof(f6182,plain,(
% 32.88/4.49    ( ! [X47,X48,X46] : (k3_xboole_0(k3_xboole_0(X46,X48),k4_xboole_0(X46,X47)) = k3_xboole_0(k4_xboole_0(X46,X47),X48)) )),
% 32.88/4.49    inference(forward_demodulation,[],[f6071,f5860])).
% 32.88/4.49  fof(f5860,plain,(
% 32.88/4.49    ( ! [X47,X48,X46] : (k3_xboole_0(k4_xboole_0(X46,X47),X48) = k5_xboole_0(k5_xboole_0(k3_xboole_0(X46,X48),k4_xboole_0(X46,X47)),k4_xboole_0(X46,k4_xboole_0(X47,X48)))) )),
% 32.88/4.49    inference(forward_demodulation,[],[f5755,f2988])).
% 32.88/4.49  fof(f2988,plain,(
% 32.88/4.49    ( ! [X12,X10,X11] : (k3_xboole_0(k4_xboole_0(X10,X11),k3_xboole_0(X10,X12)) = k3_xboole_0(k4_xboole_0(X10,X11),X12)) )),
% 32.88/4.49    inference(backward_demodulation,[],[f1001,f2955])).
% 32.88/4.49  fof(f2955,plain,(
% 32.88/4.49    ( ! [X35,X33,X34] : (k3_xboole_0(k4_xboole_0(X33,X34),X35) = k5_xboole_0(k4_xboole_0(X33,X34),k4_xboole_0(X33,k2_xboole_0(X34,X35)))) )),
% 32.88/4.49    inference(superposition,[],[f258,f57])).
% 32.88/4.49  fof(f258,plain,(
% 32.88/4.49    ( ! [X8,X9] : (k3_xboole_0(X8,X9) = k5_xboole_0(X8,k4_xboole_0(X8,X9))) )),
% 32.88/4.49    inference(forward_demodulation,[],[f257,f102])).
% 32.88/4.49  fof(f257,plain,(
% 32.88/4.49    ( ! [X8,X9] : (k5_xboole_0(X8,k4_xboole_0(X8,X9)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X8,X9))) )),
% 32.88/4.49    inference(forward_demodulation,[],[f256,f44])).
% 32.88/4.49  fof(f44,plain,(
% 32.88/4.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 32.88/4.49    inference(cnf_transformation,[],[f1])).
% 32.88/4.49  fof(f1,axiom,(
% 32.88/4.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 32.88/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 32.88/4.49  fof(f256,plain,(
% 32.88/4.49    ( ! [X8,X9] : (k5_xboole_0(X8,k4_xboole_0(X8,X9)) = k2_xboole_0(k3_xboole_0(X8,X9),k1_xboole_0)) )),
% 32.88/4.49    inference(forward_demodulation,[],[f255,f83])).
% 32.88/4.49  fof(f83,plain,(
% 32.88/4.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 32.88/4.49    inference(superposition,[],[f41,f44])).
% 32.88/4.49  fof(f41,plain,(
% 32.88/4.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 32.88/4.49    inference(cnf_transformation,[],[f16])).
% 32.88/4.49  fof(f16,axiom,(
% 32.88/4.49    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 32.88/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 32.88/4.49  fof(f255,plain,(
% 32.88/4.49    ( ! [X8,X9] : (k5_xboole_0(X8,k4_xboole_0(X8,X9)) = k2_xboole_0(k3_xboole_0(X8,X9),k4_xboole_0(X8,k2_xboole_0(X9,X8)))) )),
% 32.88/4.49    inference(forward_demodulation,[],[f226,f57])).
% 32.88/4.49  fof(f226,plain,(
% 32.88/4.49    ( ! [X8,X9] : (k5_xboole_0(X8,k4_xboole_0(X8,X9)) = k2_xboole_0(k3_xboole_0(X8,X9),k4_xboole_0(k4_xboole_0(X8,X9),X8))) )),
% 32.88/4.49    inference(superposition,[],[f52,f45])).
% 32.88/4.49  fof(f52,plain,(
% 32.88/4.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 32.88/4.49    inference(cnf_transformation,[],[f5])).
% 32.88/4.49  fof(f5,axiom,(
% 32.88/4.49    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 32.88/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 32.88/4.49  fof(f1001,plain,(
% 32.88/4.49    ( ! [X12,X10,X11] : (k5_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X10,k2_xboole_0(X11,X12))) = k3_xboole_0(k4_xboole_0(X10,X11),k3_xboole_0(X10,X12))) )),
% 32.88/4.49    inference(forward_demodulation,[],[f1000,f935])).
% 32.88/4.49  fof(f935,plain,(
% 32.88/4.49    ( ! [X14,X15,X13] : (k4_xboole_0(X13,k2_xboole_0(X15,k4_xboole_0(X13,X14))) = k3_xboole_0(k4_xboole_0(X13,X15),k3_xboole_0(X13,X14))) )),
% 32.88/4.49    inference(superposition,[],[f61,f45])).
% 32.88/4.49  fof(f1000,plain,(
% 32.88/4.49    ( ! [X12,X10,X11] : (k5_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X10,k2_xboole_0(X11,X12))) = k4_xboole_0(X10,k2_xboole_0(X11,k4_xboole_0(X10,X12)))) )),
% 32.88/4.49    inference(forward_demodulation,[],[f952,f57])).
% 32.88/4.49  fof(f952,plain,(
% 32.88/4.49    ( ! [X12,X10,X11] : (k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X10,X12)) = k5_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X10,k2_xboole_0(X11,X12)))) )),
% 32.88/4.49    inference(superposition,[],[f48,f61])).
% 32.88/4.49  fof(f48,plain,(
% 32.88/4.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 32.88/4.49    inference(cnf_transformation,[],[f8])).
% 32.88/4.49  fof(f8,axiom,(
% 32.88/4.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 32.88/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 32.88/4.49  fof(f5755,plain,(
% 32.88/4.49    ( ! [X47,X48,X46] : (k3_xboole_0(k4_xboole_0(X46,X47),k3_xboole_0(X46,X48)) = k5_xboole_0(k5_xboole_0(k3_xboole_0(X46,X48),k4_xboole_0(X46,X47)),k4_xboole_0(X46,k4_xboole_0(X47,X48)))) )),
% 32.88/4.49    inference(superposition,[],[f361,f62])).
% 32.88/4.49  fof(f361,plain,(
% 32.88/4.49    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X1,X2))) )),
% 32.88/4.49    inference(superposition,[],[f54,f42])).
% 32.88/4.49  fof(f54,plain,(
% 32.88/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 32.88/4.49    inference(cnf_transformation,[],[f27])).
% 32.88/4.49  fof(f27,axiom,(
% 32.88/4.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 32.88/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 32.88/4.49  fof(f6071,plain,(
% 32.88/4.49    ( ! [X47,X48,X46] : (k3_xboole_0(k3_xboole_0(X46,X48),k4_xboole_0(X46,X47)) = k5_xboole_0(k5_xboole_0(k3_xboole_0(X46,X48),k4_xboole_0(X46,X47)),k4_xboole_0(X46,k4_xboole_0(X47,X48)))) )),
% 32.88/4.49    inference(superposition,[],[f369,f62])).
% 32.88/4.49  fof(f369,plain,(
% 32.88/4.49    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X2,X1))) )),
% 32.88/4.49    inference(superposition,[],[f54,f44])).
% 32.88/4.49  fof(f2989,plain,(
% 32.88/4.49    ( ! [X14,X15,X13] : (k4_xboole_0(X13,k2_xboole_0(X15,k4_xboole_0(X13,X14))) = k3_xboole_0(k4_xboole_0(X13,X15),X14)) )),
% 32.88/4.49    inference(backward_demodulation,[],[f935,f2988])).
% 32.88/4.49  fof(f9774,plain,(
% 32.88/4.49    ( ! [X17,X18,X16] : (k5_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X16,k4_xboole_0(X17,X18))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X16,k2_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X16,X17))))) )),
% 32.88/4.49    inference(forward_demodulation,[],[f9650,f57])).
% 32.88/4.49  fof(f9650,plain,(
% 32.88/4.49    ( ! [X17,X18,X16] : (k5_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X16,k4_xboole_0(X17,X18))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X17,X18)),k4_xboole_0(X16,X17)))) )),
% 32.88/4.49    inference(superposition,[],[f52,f1061])).
% 32.88/4.49  fof(f1061,plain,(
% 32.88/4.49    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X3,X4)))) )),
% 32.88/4.49    inference(superposition,[],[f41,f62])).
% 32.88/4.49  fof(f2929,plain,(
% 32.88/4.49    ( ! [X43,X44,X42] : (k5_xboole_0(k4_xboole_0(X42,X43),k4_xboole_0(X42,k4_xboole_0(X43,X44))) = k3_xboole_0(k3_xboole_0(X42,X44),X43)) )),
% 32.88/4.49    inference(forward_demodulation,[],[f2928,f855])).
% 32.88/4.49  fof(f2928,plain,(
% 32.88/4.49    ( ! [X43,X44,X42] : (k5_xboole_0(k4_xboole_0(X42,X43),k4_xboole_0(X42,k4_xboole_0(X43,X44))) = k3_xboole_0(X42,k4_xboole_0(X44,k4_xboole_0(X42,X43)))) )),
% 32.88/4.49    inference(forward_demodulation,[],[f2884,f56])).
% 32.88/4.49  fof(f2884,plain,(
% 32.88/4.49    ( ! [X43,X44,X42] : (k4_xboole_0(k3_xboole_0(X42,X44),k4_xboole_0(X42,X43)) = k5_xboole_0(k4_xboole_0(X42,X43),k4_xboole_0(X42,k4_xboole_0(X43,X44)))) )),
% 32.88/4.49    inference(superposition,[],[f248,f62])).
% 32.88/4.49  fof(f248,plain,(
% 32.88/4.49    ( ! [X2,X1] : (k4_xboole_0(X2,X1) = k5_xboole_0(X1,k2_xboole_0(X1,X2))) )),
% 32.88/4.49    inference(forward_demodulation,[],[f247,f102])).
% 32.88/4.49  fof(f247,plain,(
% 32.88/4.49    ( ! [X2,X1] : (k5_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1))) )),
% 32.88/4.49    inference(forward_demodulation,[],[f222,f153])).
% 32.88/4.49  fof(f153,plain,(
% 32.88/4.49    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 32.88/4.49    inference(superposition,[],[f50,f44])).
% 32.88/4.49  fof(f50,plain,(
% 32.88/4.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 32.88/4.49    inference(cnf_transformation,[],[f13])).
% 32.88/4.49  fof(f13,axiom,(
% 32.88/4.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 32.88/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 32.88/4.49  fof(f222,plain,(
% 32.88/4.49    ( ! [X2,X1] : (k5_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X1,X2),X1))) )),
% 32.88/4.49    inference(superposition,[],[f52,f41])).
% 32.88/4.49  fof(f855,plain,(
% 32.88/4.49    ( ! [X19,X20,X18] : (k3_xboole_0(k3_xboole_0(X18,X19),X20) = k3_xboole_0(X18,k4_xboole_0(X19,k4_xboole_0(X18,X20)))) )),
% 32.88/4.49    inference(backward_demodulation,[],[f518,f854])).
% 32.88/4.49  fof(f854,plain,(
% 32.88/4.49    ( ! [X14,X15,X13] : (k4_xboole_0(X13,k3_xboole_0(X15,k4_xboole_0(X13,X14))) = k4_xboole_0(X13,k4_xboole_0(X15,X14))) )),
% 32.88/4.49    inference(forward_demodulation,[],[f802,f62])).
% 32.88/4.49  fof(f802,plain,(
% 32.88/4.49    ( ! [X14,X15,X13] : (k4_xboole_0(X13,k3_xboole_0(X15,k4_xboole_0(X13,X14))) = k2_xboole_0(k4_xboole_0(X13,X15),k3_xboole_0(X13,X14))) )),
% 32.88/4.49    inference(superposition,[],[f60,f45])).
% 32.88/4.49  fof(f60,plain,(
% 32.88/4.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 32.88/4.49    inference(cnf_transformation,[],[f6])).
% 32.88/4.49  fof(f6,axiom,(
% 32.88/4.49    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 32.88/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).
% 32.88/4.49  fof(f518,plain,(
% 32.88/4.49    ( ! [X19,X20,X18] : (k3_xboole_0(k3_xboole_0(X18,X19),X20) = k3_xboole_0(X18,k4_xboole_0(X19,k3_xboole_0(X18,k4_xboole_0(X19,X20))))) )),
% 32.88/4.49    inference(forward_demodulation,[],[f499,f56])).
% 32.88/4.49  fof(f499,plain,(
% 32.88/4.49    ( ! [X19,X20,X18] : (k3_xboole_0(k3_xboole_0(X18,X19),X20) = k3_xboole_0(X18,k4_xboole_0(X19,k4_xboole_0(k3_xboole_0(X18,X19),X20)))) )),
% 32.88/4.49    inference(superposition,[],[f56,f45])).
% 32.88/4.49  fof(f20699,plain,(
% 32.88/4.49    ( ! [X4,X2,X3] : (k3_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X4))) = k3_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X3,X4)))) )),
% 32.88/4.49    inference(superposition,[],[f709,f854])).
% 32.88/4.49  fof(f709,plain,(
% 32.88/4.49    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k4_xboole_0(X4,k3_xboole_0(X3,X5))) = k3_xboole_0(X3,k4_xboole_0(X4,X5))) )),
% 32.88/4.49    inference(superposition,[],[f59,f56])).
% 32.88/4.49  fof(f59,plain,(
% 32.88/4.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 32.88/4.49    inference(cnf_transformation,[],[f20])).
% 32.88/4.49  fof(f20,axiom,(
% 32.88/4.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 32.88/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).
% 32.88/4.49  fof(f115698,plain,(
% 32.88/4.49    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k3_xboole_0(sK2,sK1)))),
% 32.88/4.49    inference(forward_demodulation,[],[f115697,f115691])).
% 32.88/4.49  fof(f115691,plain,(
% 32.88/4.49    ( ! [X19,X17,X18] : (k3_xboole_0(X17,k3_xboole_0(X19,X18)) = k3_xboole_0(X18,k3_xboole_0(X17,X19))) )),
% 32.88/4.49    inference(forward_demodulation,[],[f115218,f45])).
% 32.88/4.49  fof(f115218,plain,(
% 32.88/4.49    ( ! [X19,X17,X18] : (k3_xboole_0(X18,k4_xboole_0(X17,k4_xboole_0(X17,X19))) = k3_xboole_0(X17,k3_xboole_0(X19,X18))) )),
% 32.88/4.49    inference(superposition,[],[f7626,f9787])).
% 32.88/4.49  fof(f7626,plain,(
% 32.88/4.49    ( ! [X8,X7,X9] : (k3_xboole_0(X7,k4_xboole_0(X8,X9)) = k3_xboole_0(X8,k4_xboole_0(X7,X9))) )),
% 32.88/4.49    inference(superposition,[],[f488,f56])).
% 32.88/4.49  fof(f488,plain,(
% 32.88/4.49    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(k3_xboole_0(X3,X2),X4)) )),
% 32.88/4.49    inference(superposition,[],[f56,f43])).
% 32.88/4.49  fof(f43,plain,(
% 32.88/4.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 32.88/4.49    inference(cnf_transformation,[],[f2])).
% 32.88/4.49  fof(f2,axiom,(
% 32.88/4.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 32.88/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 32.88/4.49  fof(f115697,plain,(
% 32.88/4.49    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK1,k3_xboole_0(sK0,sK2)))),
% 32.88/4.49    inference(forward_demodulation,[],[f115693,f20900])).
% 32.88/4.49  fof(f115693,plain,(
% 32.88/4.49    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK1,k3_xboole_0(sK2,sK0)))),
% 32.88/4.49    inference(backward_demodulation,[],[f65,f115691])).
% 32.88/4.49  fof(f65,plain,(
% 32.88/4.49    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK2,k3_xboole_0(sK0,sK1)))),
% 32.88/4.49    inference(backward_demodulation,[],[f35,f43])).
% 32.88/4.49  fof(f35,plain,(
% 32.88/4.49    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),
% 32.88/4.49    inference(cnf_transformation,[],[f34])).
% 32.88/4.49  fof(f34,plain,(
% 32.88/4.49    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),
% 32.88/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f33])).
% 32.88/4.49  fof(f33,plain,(
% 32.88/4.49    ? [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2)) => k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),
% 32.88/4.49    introduced(choice_axiom,[])).
% 32.88/4.49  fof(f32,plain,(
% 32.88/4.49    ? [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2))),
% 32.88/4.49    inference(ennf_transformation,[],[f31])).
% 32.88/4.49  fof(f31,negated_conjecture,(
% 32.88/4.49    ~! [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2))),
% 32.88/4.49    inference(negated_conjecture,[],[f30])).
% 32.88/4.49  fof(f30,conjecture,(
% 32.88/4.49    ! [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2))),
% 32.88/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_xboole_1)).
% 32.88/4.49  % SZS output end Proof for theBenchmark
% 32.88/4.49  % (22440)------------------------------
% 32.88/4.49  % (22440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 32.88/4.49  % (22440)Termination reason: Refutation
% 32.88/4.49  
% 32.88/4.49  % (22440)Memory used [KB]: 86992
% 32.88/4.49  % (22440)Time elapsed: 4.060 s
% 32.88/4.49  % (22440)------------------------------
% 32.88/4.49  % (22440)------------------------------
% 32.88/4.49  % (22433)Success in time 4.122 s
%------------------------------------------------------------------------------
