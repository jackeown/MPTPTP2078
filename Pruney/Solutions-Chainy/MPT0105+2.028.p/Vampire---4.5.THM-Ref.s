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
% DateTime   : Thu Dec  3 12:32:07 EST 2020

% Result     : Theorem 10.48s
% Output     : Refutation 10.48s
% Verified   : 
% Statistics : Number of formulae       :  181 (3661 expanded)
%              Number of leaves         :   13 (1204 expanded)
%              Depth                    :   31
%              Number of atoms          :  182 (3662 expanded)
%              Number of equality atoms :  181 (3661 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25823,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f25822])).

fof(f25822,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f19,f25545])).

fof(f25545,plain,(
    ! [X10,X9] : k2_xboole_0(X9,X10) = k5_xboole_0(X9,k4_xboole_0(X10,X9)) ),
    inference(forward_demodulation,[],[f25544,f4957])).

fof(f4957,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k5_xboole_0(k4_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X3)),k5_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f4923,f4924])).

fof(f4924,plain,(
    ! [X4,X5] : k5_xboole_0(k2_xboole_0(X4,X5),k5_xboole_0(X4,X5)) = k4_xboole_0(k2_xboole_0(X4,X5),k5_xboole_0(X4,X5)) ),
    inference(backward_demodulation,[],[f3787,f4922])).

fof(f4922,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f4921,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f4921,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f4920,f3844])).

fof(f3844,plain,(
    ! [X19,X18] : k2_xboole_0(k2_xboole_0(X18,X19),k5_xboole_0(X18,X19)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X18,X19),k5_xboole_0(X18,X19)),k3_xboole_0(k5_xboole_0(X18,X19),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f3829,f3843])).

fof(f3843,plain,(
    ! [X47,X46] : k2_xboole_0(k2_xboole_0(X46,X47),k5_xboole_0(X46,X47)) = k5_xboole_0(k2_xboole_0(X46,X47),k3_xboole_0(k5_xboole_0(X46,X47),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f3842,f105])).

fof(f105,plain,(
    ! [X8,X7] : k5_xboole_0(X7,k5_xboole_0(X8,k5_xboole_0(X7,X8))) = k3_xboole_0(k5_xboole_0(X7,X8),k1_xboole_0) ),
    inference(forward_demodulation,[],[f98,f31])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f23,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f98,plain,(
    ! [X8,X7] : k4_xboole_0(k5_xboole_0(X7,X8),k5_xboole_0(X7,X8)) = k5_xboole_0(X7,k5_xboole_0(X8,k5_xboole_0(X7,X8))) ),
    inference(superposition,[],[f29,f62])).

fof(f62,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f55,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f55,plain,(
    ! [X0] : k4_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f27,f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f3842,plain,(
    ! [X47,X46] : k2_xboole_0(k2_xboole_0(X46,X47),k5_xboole_0(X46,X47)) = k5_xboole_0(k2_xboole_0(X46,X47),k5_xboole_0(X46,k5_xboole_0(X47,k5_xboole_0(X46,X47)))) ),
    inference(forward_demodulation,[],[f3802,f29])).

fof(f3802,plain,(
    ! [X47,X46] : k2_xboole_0(k2_xboole_0(X46,X47),k5_xboole_0(X46,X47)) = k5_xboole_0(k2_xboole_0(X46,X47),k5_xboole_0(k5_xboole_0(X46,X47),k5_xboole_0(X46,X47))) ),
    inference(superposition,[],[f96,f168])).

fof(f168,plain,(
    ! [X8,X7] : k5_xboole_0(X7,X8) = k3_xboole_0(k2_xboole_0(X7,X8),k5_xboole_0(X7,X8)) ),
    inference(superposition,[],[f33,f27])).

fof(f33,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k3_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f32,f25])).

fof(f32,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f23,f23])).

fof(f96,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f29,f26])).

fof(f3829,plain,(
    ! [X19,X18] : k5_xboole_0(k2_xboole_0(X18,X19),k3_xboole_0(k5_xboole_0(X18,X19),k1_xboole_0)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X18,X19),k5_xboole_0(X18,X19)),k3_xboole_0(k5_xboole_0(X18,X19),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f3794,f1632])).

fof(f1632,plain,(
    ! [X2,X3] : k3_xboole_0(k5_xboole_0(X2,X3),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f1631,f31])).

fof(f1631,plain,(
    ! [X2,X3] : k4_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X2,X3)) = k4_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f1590,f118])).

fof(f118,plain,(
    ! [X14,X12,X13] : k4_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(k3_xboole_0(X12,X13),X14)) = k4_xboole_0(k5_xboole_0(X12,X13),X14) ),
    inference(superposition,[],[f30,f27])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1590,plain,(
    ! [X2,X3] : k4_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(k3_xboole_0(X2,X3),k2_xboole_0(X2,X3))) ),
    inference(superposition,[],[f118,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f24,f27])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f3794,plain,(
    ! [X19,X18] : k5_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(k5_xboole_0(X18,X19),k2_xboole_0(X18,X19))) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X18,X19),k5_xboole_0(X18,X19)),k4_xboole_0(k5_xboole_0(X18,X19),k2_xboole_0(X18,X19))) ),
    inference(superposition,[],[f64,f168])).

fof(f64,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(k3_xboole_0(X1,X2),X1)) ),
    inference(forward_demodulation,[],[f56,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f56,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(superposition,[],[f27,f24])).

fof(f4920,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f4825,f4629])).

fof(f4629,plain,(
    ! [X0,X1] : k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f4590,f31])).

fof(f4590,plain,(
    ! [X0,X1] : k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f23,f1633])).

fof(f1633,plain,(
    ! [X4,X5] : k5_xboole_0(X4,X5) = k4_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f1591,f27])).

fof(f1591,plain,(
    ! [X4,X5] : k4_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = k4_xboole_0(k2_xboole_0(X4,X5),k3_xboole_0(X4,X5)) ),
    inference(superposition,[],[f118,f22])).

fof(f4825,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f27,f4642])).

fof(f4642,plain,(
    ! [X2,X1] : k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f4630,f3843])).

fof(f4630,plain,(
    ! [X2,X1] : k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f48,f4629])).

fof(f48,plain,(
    ! [X2,X1] : k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))) ),
    inference(superposition,[],[f26,f26])).

fof(f3787,plain,(
    ! [X4,X5] : k5_xboole_0(k2_xboole_0(X4,X5),k5_xboole_0(X4,X5)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X4,X5),k5_xboole_0(X4,X5)),k5_xboole_0(X4,X5)) ),
    inference(superposition,[],[f27,f168])).

fof(f4923,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X3)),k5_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f3786,f4922])).

fof(f3786,plain,(
    ! [X2,X3] : k2_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X3)),k5_xboole_0(X2,X3)) ),
    inference(superposition,[],[f26,f168])).

fof(f25544,plain,(
    ! [X10,X9] : k5_xboole_0(X9,k4_xboole_0(X10,X9)) = k5_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k5_xboole_0(X9,X10)) ),
    inference(forward_demodulation,[],[f25543,f168])).

fof(f25543,plain,(
    ! [X10,X9] : k5_xboole_0(X9,k4_xboole_0(X10,X9)) = k5_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k3_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f25542,f23])).

fof(f25542,plain,(
    ! [X10,X9] : k5_xboole_0(X9,k4_xboole_0(X10,X9)) = k5_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)))) ),
    inference(forward_demodulation,[],[f25541,f11455])).

fof(f11455,plain,(
    ! [X15,X16] : k5_xboole_0(X15,k4_xboole_0(X16,X15)) = k4_xboole_0(k2_xboole_0(X15,X16),k3_xboole_0(X15,k3_xboole_0(X16,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f11449,f24])).

fof(f11449,plain,(
    ! [X15,X16] : k5_xboole_0(X15,k4_xboole_0(X16,X15)) = k4_xboole_0(k2_xboole_0(X15,k4_xboole_0(X16,X15)),k3_xboole_0(X15,k3_xboole_0(X16,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f6675,f11448])).

fof(f11448,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k4_xboole_0(X5,k3_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f11384,f25])).

fof(f11384,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k3_xboole_0(X5,X6)) = k4_xboole_0(X5,k3_xboole_0(X6,X5)) ),
    inference(superposition,[],[f25,f6752])).

fof(f6752,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X3,k3_xboole_0(X4,X3)) ),
    inference(superposition,[],[f6628,f4676])).

fof(f4676,plain,(
    ! [X28,X29] : k3_xboole_0(X28,X29) = k3_xboole_0(k3_xboole_0(X28,X29),X28) ),
    inference(superposition,[],[f3674,f23])).

fof(f3674,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k3_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(forward_demodulation,[],[f3563,f139])).

fof(f139,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k4_xboole_0(X8,k2_xboole_0(X9,k3_xboole_0(k4_xboole_0(X8,X9),k1_xboole_0))) ),
    inference(forward_demodulation,[],[f122,f31])).

fof(f122,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X8,X9)))) ),
    inference(superposition,[],[f30,f43])).

fof(f43,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f40,f21])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f25,f31])).

fof(f3563,plain,(
    ! [X2,X1] : k3_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0))) ),
    inference(superposition,[],[f138,f137])).

fof(f137,plain,(
    ! [X4,X3] : k3_xboole_0(k4_xboole_0(X3,X4),k1_xboole_0) = k4_xboole_0(X3,k2_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f120,f24])).

fof(f120,plain,(
    ! [X4,X3] : k3_xboole_0(k4_xboole_0(X3,X4),k1_xboole_0) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X4))) ),
    inference(superposition,[],[f30,f31])).

fof(f138,plain,(
    ! [X6,X7,X5] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,k2_xboole_0(X6,X7)))) ),
    inference(forward_demodulation,[],[f121,f30])).

fof(f121,plain,(
    ! [X6,X7,X5] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(k4_xboole_0(X5,X6),X7))) ),
    inference(superposition,[],[f30,f23])).

fof(f6628,plain,(
    ! [X10,X11,X9] : k3_xboole_0(k3_xboole_0(X9,X10),X11) = k3_xboole_0(X9,k3_xboole_0(X10,X11)) ),
    inference(backward_demodulation,[],[f562,f6627])).

fof(f6627,plain,(
    ! [X24,X23,X25] : k3_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X24,X25)) = k3_xboole_0(X23,k3_xboole_0(X24,X25)) ),
    inference(forward_demodulation,[],[f6590,f77])).

fof(f77,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k3_xboole_0(X4,X2),k4_xboole_0(X2,X3)) = k3_xboole_0(X4,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f28,f23])).

fof(f6590,plain,(
    ! [X24,X23,X25] : k3_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X24,X25)) = k4_xboole_0(k3_xboole_0(X23,X24),k4_xboole_0(X24,X25)) ),
    inference(superposition,[],[f77,f6396])).

fof(f6396,plain,(
    ! [X78,X77] : k3_xboole_0(X77,X78) = k3_xboole_0(k3_xboole_0(X77,X78),X78) ),
    inference(forward_demodulation,[],[f6395,f21])).

fof(f6395,plain,(
    ! [X78,X77] : k3_xboole_0(k3_xboole_0(X77,X78),X78) = k4_xboole_0(k3_xboole_0(X77,X78),k1_xboole_0) ),
    inference(backward_demodulation,[],[f5710,f6389])).

fof(f6389,plain,(
    ! [X70,X71,X69] : k4_xboole_0(k3_xboole_0(X69,X70),X71) = k4_xboole_0(k3_xboole_0(X69,X70),k2_xboole_0(k1_xboole_0,k3_xboole_0(X69,k3_xboole_0(X70,X71)))) ),
    inference(backward_demodulation,[],[f5804,f6388])).

fof(f6388,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k4_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X1),X2) ),
    inference(forward_demodulation,[],[f6386,f86])).

fof(f86,plain,(
    ! [X8,X7,X9] : k4_xboole_0(k3_xboole_0(X9,X7),k3_xboole_0(X7,X8)) = k4_xboole_0(k3_xboole_0(X9,X7),X8) ),
    inference(forward_demodulation,[],[f79,f28])).

fof(f79,plain,(
    ! [X8,X7,X9] : k4_xboole_0(k3_xboole_0(X9,X7),k3_xboole_0(X7,X8)) = k3_xboole_0(X9,k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f28,f25])).

fof(f6386,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X1),X2) ),
    inference(backward_demodulation,[],[f422,f6352])).

fof(f6352,plain,(
    ! [X39,X41,X40] : k4_xboole_0(k3_xboole_0(X39,X40),k3_xboole_0(X39,X41)) = k4_xboole_0(k3_xboole_0(X39,X40),X41) ),
    inference(superposition,[],[f86,f4676])).

fof(f422,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k4_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X1),X2) ),
    inference(forward_demodulation,[],[f397,f28])).

fof(f397,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) ),
    inference(superposition,[],[f23,f77])).

fof(f5804,plain,(
    ! [X70,X71,X69] : k4_xboole_0(k3_xboole_0(X69,X70),k2_xboole_0(k1_xboole_0,k3_xboole_0(X69,k3_xboole_0(X70,X71)))) = k4_xboole_0(k3_xboole_0(k3_xboole_0(X69,X70),X70),X71) ),
    inference(forward_demodulation,[],[f5707,f28])).

fof(f5707,plain,(
    ! [X70,X71,X69] : k3_xboole_0(k3_xboole_0(X69,X70),k4_xboole_0(X70,X71)) = k4_xboole_0(k3_xboole_0(X69,X70),k2_xboole_0(k1_xboole_0,k3_xboole_0(X69,k3_xboole_0(X70,X71)))) ),
    inference(superposition,[],[f2218,f77])).

fof(f2218,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k4_xboole_0(X12,k2_xboole_0(k1_xboole_0,k4_xboole_0(X12,X13))) ),
    inference(forward_demodulation,[],[f2162,f21])).

fof(f2162,plain,(
    ! [X12,X13] : k3_xboole_0(k4_xboole_0(X12,k1_xboole_0),X13) = k4_xboole_0(X12,k2_xboole_0(k1_xboole_0,k4_xboole_0(X12,X13))) ),
    inference(superposition,[],[f138,f116])).

fof(f116,plain,(
    ! [X8,X7] : k4_xboole_0(X7,X8) = k4_xboole_0(X7,k2_xboole_0(k1_xboole_0,X8)) ),
    inference(superposition,[],[f30,f21])).

fof(f5710,plain,(
    ! [X78,X77] : k3_xboole_0(k3_xboole_0(X77,X78),X78) = k4_xboole_0(k3_xboole_0(X77,X78),k2_xboole_0(k1_xboole_0,k3_xboole_0(X77,k3_xboole_0(X78,k1_xboole_0)))) ),
    inference(superposition,[],[f2218,f76])).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(k3_xboole_0(X1,X0),X0) = k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f28,f31])).

fof(f562,plain,(
    ! [X10,X11,X9] : k3_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X10,X11)) = k3_xboole_0(k3_xboole_0(X9,X10),X11) ),
    inference(forward_demodulation,[],[f542,f23])).

fof(f542,plain,(
    ! [X10,X11,X9] : k3_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X10,X11)) = k4_xboole_0(k3_xboole_0(X9,X10),k4_xboole_0(k3_xboole_0(X9,X10),X11)) ),
    inference(superposition,[],[f23,f86])).

fof(f6675,plain,(
    ! [X15,X16] : k5_xboole_0(X15,k4_xboole_0(X16,k3_xboole_0(X15,X16))) = k4_xboole_0(k2_xboole_0(X15,k4_xboole_0(X16,k3_xboole_0(X15,X16))),k3_xboole_0(X15,k3_xboole_0(X16,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f2736,f6628])).

fof(f2736,plain,(
    ! [X15,X16] : k5_xboole_0(X15,k4_xboole_0(X16,k3_xboole_0(X15,X16))) = k4_xboole_0(k2_xboole_0(X15,k4_xboole_0(X16,k3_xboole_0(X15,X16))),k3_xboole_0(k3_xboole_0(X15,X16),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f2645,f869])).

fof(f869,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f797,f31])).

fof(f797,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k3_xboole_0(k4_xboole_0(X1,X1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f796,f62])).

fof(f796,plain,(
    ! [X1] : k5_xboole_0(X1,X1) = k3_xboole_0(k4_xboole_0(X1,X1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f795,f69])).

fof(f69,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(backward_demodulation,[],[f51,f68])).

fof(f68,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f47,f67])).

fof(f67,plain,(
    ! [X3] : k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) = X3 ),
    inference(forward_demodulation,[],[f66,f21])).

fof(f66,plain,(
    ! [X3] : k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) = k4_xboole_0(X3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f65,f25])).

fof(f65,plain,(
    ! [X3] : k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) = k4_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f57,f25])).

fof(f57,plain,(
    ! [X3] : k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) = k4_xboole_0(X3,k3_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0))) ),
    inference(superposition,[],[f27,f37])).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(forward_demodulation,[],[f35,f22])).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k2_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f24,f31])).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f26,f20])).

fof(f20,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f49,f20])).

fof(f49,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f26,f31])).

fof(f795,plain,(
    ! [X1] : k5_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X1,X1))) = k3_xboole_0(k4_xboole_0(X1,X1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f760,f31])).

fof(f760,plain,(
    ! [X1] : k5_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X1,X1))) = k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)) ),
    inference(superposition,[],[f62,f93])).

fof(f93,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k4_xboole_0(X2,X2),X3) ),
    inference(superposition,[],[f29,f62])).

fof(f2645,plain,(
    ! [X15,X16] : k5_xboole_0(X15,k4_xboole_0(X16,k3_xboole_0(X15,X16))) = k4_xboole_0(k2_xboole_0(X15,k4_xboole_0(X16,k3_xboole_0(X15,X16))),k3_xboole_0(k3_xboole_0(k3_xboole_0(X15,X16),k1_xboole_0),k1_xboole_0)) ),
    inference(superposition,[],[f83,f1146])).

fof(f1146,plain,(
    ! [X7] : k4_xboole_0(X7,X7) = k3_xboole_0(k3_xboole_0(X7,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1088,f37])).

fof(f1088,plain,(
    ! [X7] : k3_xboole_0(k3_xboole_0(X7,k1_xboole_0),k1_xboole_0) = k4_xboole_0(X7,k2_xboole_0(X7,k3_xboole_0(X7,k1_xboole_0))) ),
    inference(superposition,[],[f113,f31])).

fof(f113,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
    inference(superposition,[],[f30,f31])).

fof(f83,plain,(
    ! [X4,X2,X3] : k5_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(k2_xboole_0(X2,k4_xboole_0(X3,X4)),k4_xboole_0(k3_xboole_0(X2,X3),X4)) ),
    inference(superposition,[],[f27,f28])).

fof(f25541,plain,(
    ! [X10,X9] : k5_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)))) = k4_xboole_0(k2_xboole_0(X9,X10),k3_xboole_0(X9,k3_xboole_0(X10,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f25540,f11513])).

fof(f11513,plain,(
    ! [X28,X26,X27] : k4_xboole_0(X28,k4_xboole_0(k3_xboole_0(X26,X27),X28)) = k4_xboole_0(X28,k3_xboole_0(X26,k3_xboole_0(X27,k1_xboole_0))) ),
    inference(superposition,[],[f11452,f6628])).

fof(f11452,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k3_xboole_0(X4,k1_xboole_0)) = k4_xboole_0(X3,k4_xboole_0(X4,X3)) ),
    inference(backward_demodulation,[],[f6709,f11448])).

fof(f6709,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k4_xboole_0(X4,k3_xboole_0(X3,X4))) = k4_xboole_0(X3,k3_xboole_0(X4,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f6663,f25])).

fof(f6663,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k4_xboole_0(X4,k3_xboole_0(X3,X4))) = k4_xboole_0(X3,k3_xboole_0(X3,k3_xboole_0(X4,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f457,f6628])).

fof(f457,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k4_xboole_0(X4,k3_xboole_0(X3,X4))) = k4_xboole_0(X3,k3_xboole_0(k3_xboole_0(X3,X4),k1_xboole_0)) ),
    inference(superposition,[],[f85,f31])).

fof(f85,plain,(
    ! [X10,X8,X9] : k4_xboole_0(X8,k4_xboole_0(X9,X10)) = k4_xboole_0(X8,k4_xboole_0(k3_xboole_0(X8,X9),X10)) ),
    inference(superposition,[],[f25,f28])).

fof(f25540,plain,(
    ! [X10,X9] : k5_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)))) = k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(k3_xboole_0(X9,X10),k2_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f25539,f9900])).

fof(f9900,plain,(
    ! [X92,X90,X91] : k4_xboole_0(k2_xboole_0(X90,X91),k4_xboole_0(k3_xboole_0(X90,X91),X92)) = k3_xboole_0(k2_xboole_0(X90,X91),k2_xboole_0(k5_xboole_0(X90,X91),X92)) ),
    inference(superposition,[],[f662,f27])).

fof(f662,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k3_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(forward_demodulation,[],[f624,f85])).

fof(f624,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(superposition,[],[f23,f114])).

fof(f114,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k3_xboole_0(X2,X3),X4) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4)) ),
    inference(superposition,[],[f30,f23])).

fof(f25539,plain,(
    ! [X10,X9] : k5_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)))) = k3_xboole_0(k2_xboole_0(X9,X10),k2_xboole_0(k5_xboole_0(X9,X10),k2_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f25538,f5470])).

fof(f5470,plain,(
    ! [X19,X18] : k3_xboole_0(X18,k2_xboole_0(X19,X18)) = k4_xboole_0(X18,k3_xboole_0(k4_xboole_0(X18,X19),X19)) ),
    inference(superposition,[],[f23,f2205])).

fof(f2205,plain,(
    ! [X0,X1] : k3_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f2149,f24])).

fof(f2149,plain,(
    ! [X0,X1] : k3_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f138,f22])).

fof(f25538,plain,(
    ! [X10,X9] : k5_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)))) = k4_xboole_0(k2_xboole_0(X9,X10),k3_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k5_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f25537,f11469])).

fof(f11469,plain,(
    ! [X10,X8,X9] : k4_xboole_0(X8,k3_xboole_0(X9,X10)) = k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X8,X10))) ),
    inference(backward_demodulation,[],[f6704,f11466])).

fof(f11466,plain,(
    ! [X39,X37,X38] : k4_xboole_0(X37,k4_xboole_0(X38,X39)) = k4_xboole_0(X37,k4_xboole_0(k3_xboole_0(X38,X37),X39)) ),
    inference(forward_demodulation,[],[f11398,f85])).

fof(f11398,plain,(
    ! [X39,X37,X38] : k4_xboole_0(X37,k4_xboole_0(k3_xboole_0(X38,X37),X39)) = k4_xboole_0(X37,k4_xboole_0(k3_xboole_0(X37,X38),X39)) ),
    inference(superposition,[],[f85,f6752])).

fof(f6704,plain,(
    ! [X10,X8,X9] : k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(k3_xboole_0(X8,X9),X10))) = k4_xboole_0(X8,k3_xboole_0(X9,X10)) ),
    inference(forward_demodulation,[],[f6631,f25])).

fof(f6631,plain,(
    ! [X10,X8,X9] : k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(k3_xboole_0(X8,X9),X10))) = k4_xboole_0(X8,k3_xboole_0(X8,k3_xboole_0(X9,X10))) ),
    inference(backward_demodulation,[],[f459,f6628])).

fof(f459,plain,(
    ! [X10,X8,X9] : k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(k3_xboole_0(X8,X9),X10))) = k4_xboole_0(X8,k3_xboole_0(k3_xboole_0(X8,X9),X10)) ),
    inference(superposition,[],[f85,f23])).

fof(f25537,plain,(
    ! [X10,X9] : k5_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)))) = k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)))) ),
    inference(forward_demodulation,[],[f25388,f11466])).

fof(f25388,plain,(
    ! [X10,X9] : k5_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)))) = k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(k3_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k2_xboole_0(X9,X10)),k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)))) ),
    inference(superposition,[],[f64,f5231])).

fof(f5231,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X10,X11),k5_xboole_0(X10,X11)),k2_xboole_0(X10,X11)) ),
    inference(backward_demodulation,[],[f4963,f5230])).

fof(f5230,plain,(
    ! [X12,X13] : k2_xboole_0(X12,X13) = k2_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13))) ),
    inference(backward_demodulation,[],[f4962,f5229])).

fof(f5229,plain,(
    ! [X17,X16] : k2_xboole_0(X16,X17) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X16,X17),k5_xboole_0(X16,X17)),k5_xboole_0(X16,X17)) ),
    inference(forward_demodulation,[],[f5228,f4922])).

fof(f5228,plain,(
    ! [X17,X16] : k2_xboole_0(k2_xboole_0(X16,X17),k5_xboole_0(X16,X17)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X16,X17),k5_xboole_0(X16,X17)),k5_xboole_0(X16,X17)) ),
    inference(forward_demodulation,[],[f5157,f4924])).

fof(f5157,plain,(
    ! [X17,X16] : k2_xboole_0(k2_xboole_0(X16,X17),k5_xboole_0(X16,X17)) = k2_xboole_0(k5_xboole_0(k2_xboole_0(X16,X17),k5_xboole_0(X16,X17)),k5_xboole_0(X16,X17)) ),
    inference(superposition,[],[f4932,f168])).

fof(f4932,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(backward_demodulation,[],[f4642,f4922])).

fof(f4962,plain,(
    ! [X12,X13] : k2_xboole_0(k4_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)),k5_xboole_0(X12,X13)) = k2_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13))) ),
    inference(forward_demodulation,[],[f4961,f279])).

fof(f279,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k3_xboole_0(k4_xboole_0(X4,X5),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f278,f31])).

fof(f278,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5))) ),
    inference(forward_demodulation,[],[f264,f62])).

fof(f264,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5))) ),
    inference(superposition,[],[f96,f33])).

fof(f4961,plain,(
    ! [X12,X13] : k2_xboole_0(k4_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)),k5_xboole_0(X12,X13)) = k5_xboole_0(k2_xboole_0(X12,X13),k3_xboole_0(k4_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f4960,f137])).

fof(f4960,plain,(
    ! [X12,X13] : k2_xboole_0(k4_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)),k5_xboole_0(X12,X13)) = k5_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(k5_xboole_0(X12,X13),k2_xboole_0(X12,X13)))) ),
    inference(forward_demodulation,[],[f4959,f2205])).

fof(f4959,plain,(
    ! [X12,X13] : k2_xboole_0(k4_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)),k5_xboole_0(X12,X13)) = k5_xboole_0(k2_xboole_0(X12,X13),k3_xboole_0(k4_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)),k5_xboole_0(X12,X13))) ),
    inference(forward_demodulation,[],[f4925,f4924])).

fof(f4925,plain,(
    ! [X12,X13] : k2_xboole_0(k5_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)),k5_xboole_0(X12,X13)) = k5_xboole_0(k2_xboole_0(X12,X13),k3_xboole_0(k5_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)),k5_xboole_0(X12,X13))) ),
    inference(backward_demodulation,[],[f3791,f4922])).

fof(f3791,plain,(
    ! [X12,X13] : k2_xboole_0(k5_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)),k5_xboole_0(X12,X13)) = k5_xboole_0(k2_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)),k3_xboole_0(k5_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)),k5_xboole_0(X12,X13))) ),
    inference(superposition,[],[f48,f168])).

fof(f4963,plain,(
    ! [X10,X11] : k2_xboole_0(k4_xboole_0(k2_xboole_0(X10,X11),k5_xboole_0(X10,X11)),k2_xboole_0(X10,X11)) = k2_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(k2_xboole_0(X10,X11),k5_xboole_0(X10,X11))) ),
    inference(backward_demodulation,[],[f357,f4962])).

fof(f357,plain,(
    ! [X10,X11] : k2_xboole_0(k4_xboole_0(k2_xboole_0(X10,X11),k5_xboole_0(X10,X11)),k2_xboole_0(X10,X11)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X10,X11),k5_xboole_0(X10,X11)),k5_xboole_0(X10,X11)) ),
    inference(forward_demodulation,[],[f347,f61])).

fof(f61,plain,(
    ! [X2,X3] : k3_xboole_0(k2_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X3)) ),
    inference(superposition,[],[f23,f27])).

fof(f347,plain,(
    ! [X10,X11] : k2_xboole_0(k3_xboole_0(k2_xboole_0(X10,X11),k3_xboole_0(X10,X11)),k2_xboole_0(X10,X11)) = k2_xboole_0(k3_xboole_0(k2_xboole_0(X10,X11),k3_xboole_0(X10,X11)),k5_xboole_0(X10,X11)) ),
    inference(superposition,[],[f41,f27])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f24,f25])).

fof(f19,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:31:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (21280)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.46  % (21284)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  % (21281)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (21279)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (21276)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (21289)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (21290)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (21275)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (21282)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (21278)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (21287)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.50  % (21291)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (21288)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (21286)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (21277)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.52  % (21283)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.52  % (21285)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.52  % (21286)Refutation not found, incomplete strategy% (21286)------------------------------
% 0.22/0.52  % (21286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21286)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21286)Memory used [KB]: 10490
% 0.22/0.52  % (21286)Time elapsed: 0.102 s
% 0.22/0.52  % (21286)------------------------------
% 0.22/0.52  % (21286)------------------------------
% 0.22/0.53  % (21292)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 5.19/1.05  % (21279)Time limit reached!
% 5.19/1.05  % (21279)------------------------------
% 5.19/1.05  % (21279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.19/1.05  % (21279)Termination reason: Time limit
% 5.19/1.05  
% 5.19/1.05  % (21279)Memory used [KB]: 17014
% 5.19/1.05  % (21279)Time elapsed: 0.631 s
% 5.19/1.05  % (21279)------------------------------
% 5.19/1.05  % (21279)------------------------------
% 10.48/1.74  % (21278)Refutation found. Thanks to Tanya!
% 10.48/1.74  % SZS status Theorem for theBenchmark
% 10.48/1.74  % SZS output start Proof for theBenchmark
% 10.48/1.74  fof(f25823,plain,(
% 10.48/1.74    $false),
% 10.48/1.74    inference(trivial_inequality_removal,[],[f25822])).
% 10.48/1.74  fof(f25822,plain,(
% 10.48/1.74    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1)),
% 10.48/1.74    inference(superposition,[],[f19,f25545])).
% 10.48/1.74  fof(f25545,plain,(
% 10.48/1.74    ( ! [X10,X9] : (k2_xboole_0(X9,X10) = k5_xboole_0(X9,k4_xboole_0(X10,X9))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f25544,f4957])).
% 10.48/1.74  fof(f4957,plain,(
% 10.48/1.74    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k5_xboole_0(k4_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X3)),k5_xboole_0(X2,X3))) )),
% 10.48/1.74    inference(backward_demodulation,[],[f4923,f4924])).
% 10.48/1.74  fof(f4924,plain,(
% 10.48/1.74    ( ! [X4,X5] : (k5_xboole_0(k2_xboole_0(X4,X5),k5_xboole_0(X4,X5)) = k4_xboole_0(k2_xboole_0(X4,X5),k5_xboole_0(X4,X5))) )),
% 10.48/1.74    inference(backward_demodulation,[],[f3787,f4922])).
% 10.48/1.74  fof(f4922,plain,(
% 10.48/1.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f4921,f26])).
% 10.48/1.74  fof(f26,plain,(
% 10.48/1.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 10.48/1.74    inference(cnf_transformation,[],[f12])).
% 10.48/1.74  fof(f12,axiom,(
% 10.48/1.74    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 10.48/1.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 10.48/1.74  fof(f4921,plain,(
% 10.48/1.74    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f4920,f3844])).
% 10.48/1.74  fof(f3844,plain,(
% 10.48/1.74    ( ! [X19,X18] : (k2_xboole_0(k2_xboole_0(X18,X19),k5_xboole_0(X18,X19)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X18,X19),k5_xboole_0(X18,X19)),k3_xboole_0(k5_xboole_0(X18,X19),k1_xboole_0))) )),
% 10.48/1.74    inference(backward_demodulation,[],[f3829,f3843])).
% 10.48/1.74  fof(f3843,plain,(
% 10.48/1.74    ( ! [X47,X46] : (k2_xboole_0(k2_xboole_0(X46,X47),k5_xboole_0(X46,X47)) = k5_xboole_0(k2_xboole_0(X46,X47),k3_xboole_0(k5_xboole_0(X46,X47),k1_xboole_0))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f3842,f105])).
% 10.48/1.74  fof(f105,plain,(
% 10.48/1.74    ( ! [X8,X7] : (k5_xboole_0(X7,k5_xboole_0(X8,k5_xboole_0(X7,X8))) = k3_xboole_0(k5_xboole_0(X7,X8),k1_xboole_0)) )),
% 10.48/1.74    inference(forward_demodulation,[],[f98,f31])).
% 10.48/1.74  fof(f31,plain,(
% 10.48/1.74    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 10.48/1.74    inference(superposition,[],[f23,f21])).
% 10.48/1.74  fof(f21,plain,(
% 10.48/1.74    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 10.48/1.74    inference(cnf_transformation,[],[f5])).
% 10.48/1.74  fof(f5,axiom,(
% 10.48/1.74    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 10.48/1.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 10.48/1.74  fof(f23,plain,(
% 10.48/1.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 10.48/1.74    inference(cnf_transformation,[],[f8])).
% 10.48/1.74  fof(f8,axiom,(
% 10.48/1.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 10.48/1.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 10.48/1.74  fof(f98,plain,(
% 10.48/1.74    ( ! [X8,X7] : (k4_xboole_0(k5_xboole_0(X7,X8),k5_xboole_0(X7,X8)) = k5_xboole_0(X7,k5_xboole_0(X8,k5_xboole_0(X7,X8)))) )),
% 10.48/1.74    inference(superposition,[],[f29,f62])).
% 10.48/1.74  fof(f62,plain,(
% 10.48/1.74    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 10.48/1.74    inference(forward_demodulation,[],[f55,f25])).
% 10.48/1.74  fof(f25,plain,(
% 10.48/1.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 10.48/1.74    inference(cnf_transformation,[],[f7])).
% 10.48/1.74  fof(f7,axiom,(
% 10.48/1.74    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 10.48/1.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 10.48/1.74  fof(f55,plain,(
% 10.48/1.74    ( ! [X0] : (k4_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(X0,X0)) )),
% 10.48/1.74    inference(superposition,[],[f27,f22])).
% 10.48/1.74  fof(f22,plain,(
% 10.48/1.74    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 10.48/1.74    inference(cnf_transformation,[],[f15])).
% 10.48/1.74  fof(f15,plain,(
% 10.48/1.74    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 10.48/1.74    inference(rectify,[],[f1])).
% 10.48/1.74  fof(f1,axiom,(
% 10.48/1.74    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 10.48/1.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 10.48/1.74  fof(f27,plain,(
% 10.48/1.74    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 10.48/1.74    inference(cnf_transformation,[],[f3])).
% 10.48/1.74  fof(f3,axiom,(
% 10.48/1.74    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 10.48/1.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).
% 10.48/1.74  fof(f29,plain,(
% 10.48/1.74    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 10.48/1.74    inference(cnf_transformation,[],[f11])).
% 10.48/1.74  fof(f11,axiom,(
% 10.48/1.74    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 10.48/1.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 10.48/1.74  fof(f3842,plain,(
% 10.48/1.74    ( ! [X47,X46] : (k2_xboole_0(k2_xboole_0(X46,X47),k5_xboole_0(X46,X47)) = k5_xboole_0(k2_xboole_0(X46,X47),k5_xboole_0(X46,k5_xboole_0(X47,k5_xboole_0(X46,X47))))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f3802,f29])).
% 10.48/1.74  fof(f3802,plain,(
% 10.48/1.74    ( ! [X47,X46] : (k2_xboole_0(k2_xboole_0(X46,X47),k5_xboole_0(X46,X47)) = k5_xboole_0(k2_xboole_0(X46,X47),k5_xboole_0(k5_xboole_0(X46,X47),k5_xboole_0(X46,X47)))) )),
% 10.48/1.74    inference(superposition,[],[f96,f168])).
% 10.48/1.74  fof(f168,plain,(
% 10.48/1.74    ( ! [X8,X7] : (k5_xboole_0(X7,X8) = k3_xboole_0(k2_xboole_0(X7,X8),k5_xboole_0(X7,X8))) )),
% 10.48/1.74    inference(superposition,[],[f33,f27])).
% 10.48/1.74  fof(f33,plain,(
% 10.48/1.74    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k3_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f32,f25])).
% 10.48/1.74  fof(f32,plain,(
% 10.48/1.74    ( ! [X2,X1] : (k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 10.48/1.74    inference(superposition,[],[f23,f23])).
% 10.48/1.74  fof(f96,plain,(
% 10.48/1.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 10.48/1.74    inference(superposition,[],[f29,f26])).
% 10.48/1.74  fof(f3829,plain,(
% 10.48/1.74    ( ! [X19,X18] : (k5_xboole_0(k2_xboole_0(X18,X19),k3_xboole_0(k5_xboole_0(X18,X19),k1_xboole_0)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X18,X19),k5_xboole_0(X18,X19)),k3_xboole_0(k5_xboole_0(X18,X19),k1_xboole_0))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f3794,f1632])).
% 10.48/1.74  fof(f1632,plain,(
% 10.48/1.74    ( ! [X2,X3] : (k3_xboole_0(k5_xboole_0(X2,X3),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f1631,f31])).
% 10.48/1.74  fof(f1631,plain,(
% 10.48/1.74    ( ! [X2,X3] : (k4_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X2,X3)) = k4_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f1590,f118])).
% 10.48/1.74  fof(f118,plain,(
% 10.48/1.74    ( ! [X14,X12,X13] : (k4_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(k3_xboole_0(X12,X13),X14)) = k4_xboole_0(k5_xboole_0(X12,X13),X14)) )),
% 10.48/1.74    inference(superposition,[],[f30,f27])).
% 10.48/1.74  fof(f30,plain,(
% 10.48/1.74    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 10.48/1.74    inference(cnf_transformation,[],[f6])).
% 10.48/1.74  fof(f6,axiom,(
% 10.48/1.74    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 10.48/1.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 10.48/1.74  fof(f1590,plain,(
% 10.48/1.74    ( ! [X2,X3] : (k4_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(k3_xboole_0(X2,X3),k2_xboole_0(X2,X3)))) )),
% 10.48/1.74    inference(superposition,[],[f118,f60])).
% 10.48/1.74  fof(f60,plain,(
% 10.48/1.74    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 10.48/1.74    inference(superposition,[],[f24,f27])).
% 10.48/1.74  fof(f24,plain,(
% 10.48/1.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 10.48/1.74    inference(cnf_transformation,[],[f4])).
% 10.48/1.74  fof(f4,axiom,(
% 10.48/1.74    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 10.48/1.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 10.48/1.74  fof(f3794,plain,(
% 10.48/1.74    ( ! [X19,X18] : (k5_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(k5_xboole_0(X18,X19),k2_xboole_0(X18,X19))) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X18,X19),k5_xboole_0(X18,X19)),k4_xboole_0(k5_xboole_0(X18,X19),k2_xboole_0(X18,X19)))) )),
% 10.48/1.74    inference(superposition,[],[f64,f168])).
% 10.48/1.74  fof(f64,plain,(
% 10.48/1.74    ( ! [X2,X1] : (k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(k3_xboole_0(X1,X2),X1))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f56,f28])).
% 10.48/1.74  fof(f28,plain,(
% 10.48/1.74    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 10.48/1.74    inference(cnf_transformation,[],[f9])).
% 10.48/1.74  fof(f9,axiom,(
% 10.48/1.74    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 10.48/1.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 10.48/1.74  fof(f56,plain,(
% 10.48/1.74    ( ! [X2,X1] : (k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 10.48/1.74    inference(superposition,[],[f27,f24])).
% 10.48/1.74  fof(f4920,plain,(
% 10.48/1.74    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f4825,f4629])).
% 10.48/1.74  fof(f4629,plain,(
% 10.48/1.74    ( ! [X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0)) )),
% 10.48/1.74    inference(forward_demodulation,[],[f4590,f31])).
% 10.48/1.74  fof(f4590,plain,(
% 10.48/1.74    ( ! [X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 10.48/1.74    inference(superposition,[],[f23,f1633])).
% 10.48/1.74  fof(f1633,plain,(
% 10.48/1.74    ( ! [X4,X5] : (k5_xboole_0(X4,X5) = k4_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f1591,f27])).
% 10.48/1.74  fof(f1591,plain,(
% 10.48/1.74    ( ! [X4,X5] : (k4_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = k4_xboole_0(k2_xboole_0(X4,X5),k3_xboole_0(X4,X5))) )),
% 10.48/1.74    inference(superposition,[],[f118,f22])).
% 10.48/1.74  fof(f4825,plain,(
% 10.48/1.74    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) )),
% 10.48/1.74    inference(superposition,[],[f27,f4642])).
% 10.48/1.74  fof(f4642,plain,(
% 10.48/1.74    ( ! [X2,X1] : (k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f4630,f3843])).
% 10.48/1.74  fof(f4630,plain,(
% 10.48/1.74    ( ! [X2,X1] : (k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),k1_xboole_0))) )),
% 10.48/1.74    inference(backward_demodulation,[],[f48,f4629])).
% 10.48/1.74  fof(f48,plain,(
% 10.48/1.74    ( ! [X2,X1] : (k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))) )),
% 10.48/1.74    inference(superposition,[],[f26,f26])).
% 10.48/1.74  fof(f3787,plain,(
% 10.48/1.74    ( ! [X4,X5] : (k5_xboole_0(k2_xboole_0(X4,X5),k5_xboole_0(X4,X5)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X4,X5),k5_xboole_0(X4,X5)),k5_xboole_0(X4,X5))) )),
% 10.48/1.74    inference(superposition,[],[f27,f168])).
% 10.48/1.74  fof(f4923,plain,(
% 10.48/1.74    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X3)),k5_xboole_0(X2,X3))) )),
% 10.48/1.74    inference(backward_demodulation,[],[f3786,f4922])).
% 10.48/1.74  fof(f3786,plain,(
% 10.48/1.74    ( ! [X2,X3] : (k2_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X3)),k5_xboole_0(X2,X3))) )),
% 10.48/1.74    inference(superposition,[],[f26,f168])).
% 10.48/1.74  fof(f25544,plain,(
% 10.48/1.74    ( ! [X10,X9] : (k5_xboole_0(X9,k4_xboole_0(X10,X9)) = k5_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k5_xboole_0(X9,X10))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f25543,f168])).
% 10.48/1.74  fof(f25543,plain,(
% 10.48/1.74    ( ! [X10,X9] : (k5_xboole_0(X9,k4_xboole_0(X10,X9)) = k5_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k3_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f25542,f23])).
% 10.48/1.74  fof(f25542,plain,(
% 10.48/1.74    ( ! [X10,X9] : (k5_xboole_0(X9,k4_xboole_0(X10,X9)) = k5_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10))))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f25541,f11455])).
% 10.48/1.74  fof(f11455,plain,(
% 10.48/1.74    ( ! [X15,X16] : (k5_xboole_0(X15,k4_xboole_0(X16,X15)) = k4_xboole_0(k2_xboole_0(X15,X16),k3_xboole_0(X15,k3_xboole_0(X16,k1_xboole_0)))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f11449,f24])).
% 10.48/1.74  fof(f11449,plain,(
% 10.48/1.74    ( ! [X15,X16] : (k5_xboole_0(X15,k4_xboole_0(X16,X15)) = k4_xboole_0(k2_xboole_0(X15,k4_xboole_0(X16,X15)),k3_xboole_0(X15,k3_xboole_0(X16,k1_xboole_0)))) )),
% 10.48/1.74    inference(backward_demodulation,[],[f6675,f11448])).
% 10.48/1.74  fof(f11448,plain,(
% 10.48/1.74    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k4_xboole_0(X5,k3_xboole_0(X6,X5))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f11384,f25])).
% 10.48/1.74  fof(f11384,plain,(
% 10.48/1.74    ( ! [X6,X5] : (k4_xboole_0(X5,k3_xboole_0(X5,X6)) = k4_xboole_0(X5,k3_xboole_0(X6,X5))) )),
% 10.48/1.74    inference(superposition,[],[f25,f6752])).
% 10.48/1.74  fof(f6752,plain,(
% 10.48/1.74    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X3,k3_xboole_0(X4,X3))) )),
% 10.48/1.74    inference(superposition,[],[f6628,f4676])).
% 10.48/1.74  fof(f4676,plain,(
% 10.48/1.74    ( ! [X28,X29] : (k3_xboole_0(X28,X29) = k3_xboole_0(k3_xboole_0(X28,X29),X28)) )),
% 10.48/1.74    inference(superposition,[],[f3674,f23])).
% 10.48/1.74  fof(f3674,plain,(
% 10.48/1.74    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k3_xboole_0(k4_xboole_0(X1,X2),X1)) )),
% 10.48/1.74    inference(forward_demodulation,[],[f3563,f139])).
% 10.48/1.74  fof(f139,plain,(
% 10.48/1.74    ( ! [X8,X9] : (k4_xboole_0(X8,X9) = k4_xboole_0(X8,k2_xboole_0(X9,k3_xboole_0(k4_xboole_0(X8,X9),k1_xboole_0)))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f122,f31])).
% 10.48/1.74  fof(f122,plain,(
% 10.48/1.74    ( ! [X8,X9] : (k4_xboole_0(X8,X9) = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X8,X9))))) )),
% 10.48/1.74    inference(superposition,[],[f30,f43])).
% 10.48/1.74  fof(f43,plain,(
% 10.48/1.74    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 10.48/1.74    inference(forward_demodulation,[],[f40,f21])).
% 10.48/1.74  fof(f40,plain,(
% 10.48/1.74    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X0,X0))) )),
% 10.48/1.74    inference(superposition,[],[f25,f31])).
% 10.48/1.74  fof(f3563,plain,(
% 10.48/1.74    ( ! [X2,X1] : (k3_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0)))) )),
% 10.48/1.74    inference(superposition,[],[f138,f137])).
% 10.48/1.74  fof(f137,plain,(
% 10.48/1.74    ( ! [X4,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),k1_xboole_0) = k4_xboole_0(X3,k2_xboole_0(X4,X3))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f120,f24])).
% 10.48/1.74  fof(f120,plain,(
% 10.48/1.74    ( ! [X4,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),k1_xboole_0) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X4)))) )),
% 10.48/1.74    inference(superposition,[],[f30,f31])).
% 10.48/1.74  fof(f138,plain,(
% 10.48/1.74    ( ! [X6,X7,X5] : (k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,k2_xboole_0(X6,X7))))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f121,f30])).
% 10.48/1.74  fof(f121,plain,(
% 10.48/1.74    ( ! [X6,X7,X5] : (k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(k4_xboole_0(X5,X6),X7)))) )),
% 10.48/1.74    inference(superposition,[],[f30,f23])).
% 10.48/1.74  fof(f6628,plain,(
% 10.48/1.74    ( ! [X10,X11,X9] : (k3_xboole_0(k3_xboole_0(X9,X10),X11) = k3_xboole_0(X9,k3_xboole_0(X10,X11))) )),
% 10.48/1.74    inference(backward_demodulation,[],[f562,f6627])).
% 10.48/1.74  fof(f6627,plain,(
% 10.48/1.74    ( ! [X24,X23,X25] : (k3_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X24,X25)) = k3_xboole_0(X23,k3_xboole_0(X24,X25))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f6590,f77])).
% 10.48/1.74  fof(f77,plain,(
% 10.48/1.74    ( ! [X4,X2,X3] : (k4_xboole_0(k3_xboole_0(X4,X2),k4_xboole_0(X2,X3)) = k3_xboole_0(X4,k3_xboole_0(X2,X3))) )),
% 10.48/1.74    inference(superposition,[],[f28,f23])).
% 10.48/1.74  fof(f6590,plain,(
% 10.48/1.74    ( ! [X24,X23,X25] : (k3_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X24,X25)) = k4_xboole_0(k3_xboole_0(X23,X24),k4_xboole_0(X24,X25))) )),
% 10.48/1.74    inference(superposition,[],[f77,f6396])).
% 10.48/1.74  fof(f6396,plain,(
% 10.48/1.74    ( ! [X78,X77] : (k3_xboole_0(X77,X78) = k3_xboole_0(k3_xboole_0(X77,X78),X78)) )),
% 10.48/1.74    inference(forward_demodulation,[],[f6395,f21])).
% 10.48/1.74  fof(f6395,plain,(
% 10.48/1.74    ( ! [X78,X77] : (k3_xboole_0(k3_xboole_0(X77,X78),X78) = k4_xboole_0(k3_xboole_0(X77,X78),k1_xboole_0)) )),
% 10.48/1.74    inference(backward_demodulation,[],[f5710,f6389])).
% 10.48/1.74  fof(f6389,plain,(
% 10.48/1.74    ( ! [X70,X71,X69] : (k4_xboole_0(k3_xboole_0(X69,X70),X71) = k4_xboole_0(k3_xboole_0(X69,X70),k2_xboole_0(k1_xboole_0,k3_xboole_0(X69,k3_xboole_0(X70,X71))))) )),
% 10.48/1.74    inference(backward_demodulation,[],[f5804,f6388])).
% 10.48/1.74  fof(f6388,plain,(
% 10.48/1.74    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X2) = k4_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X1),X2)) )),
% 10.48/1.74    inference(forward_demodulation,[],[f6386,f86])).
% 10.48/1.74  fof(f86,plain,(
% 10.48/1.74    ( ! [X8,X7,X9] : (k4_xboole_0(k3_xboole_0(X9,X7),k3_xboole_0(X7,X8)) = k4_xboole_0(k3_xboole_0(X9,X7),X8)) )),
% 10.48/1.74    inference(forward_demodulation,[],[f79,f28])).
% 10.48/1.74  fof(f79,plain,(
% 10.48/1.74    ( ! [X8,X7,X9] : (k4_xboole_0(k3_xboole_0(X9,X7),k3_xboole_0(X7,X8)) = k3_xboole_0(X9,k4_xboole_0(X7,X8))) )),
% 10.48/1.74    inference(superposition,[],[f28,f25])).
% 10.48/1.74  fof(f6386,plain,(
% 10.48/1.74    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X1),X2)) )),
% 10.48/1.74    inference(backward_demodulation,[],[f422,f6352])).
% 10.48/1.74  fof(f6352,plain,(
% 10.48/1.74    ( ! [X39,X41,X40] : (k4_xboole_0(k3_xboole_0(X39,X40),k3_xboole_0(X39,X41)) = k4_xboole_0(k3_xboole_0(X39,X40),X41)) )),
% 10.48/1.74    inference(superposition,[],[f86,f4676])).
% 10.48/1.74  fof(f422,plain,(
% 10.48/1.74    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k4_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X1),X2)) )),
% 10.48/1.74    inference(forward_demodulation,[],[f397,f28])).
% 10.48/1.74  fof(f397,plain,(
% 10.48/1.74    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))) )),
% 10.48/1.74    inference(superposition,[],[f23,f77])).
% 10.48/1.74  fof(f5804,plain,(
% 10.48/1.74    ( ! [X70,X71,X69] : (k4_xboole_0(k3_xboole_0(X69,X70),k2_xboole_0(k1_xboole_0,k3_xboole_0(X69,k3_xboole_0(X70,X71)))) = k4_xboole_0(k3_xboole_0(k3_xboole_0(X69,X70),X70),X71)) )),
% 10.48/1.74    inference(forward_demodulation,[],[f5707,f28])).
% 10.48/1.74  fof(f5707,plain,(
% 10.48/1.74    ( ! [X70,X71,X69] : (k3_xboole_0(k3_xboole_0(X69,X70),k4_xboole_0(X70,X71)) = k4_xboole_0(k3_xboole_0(X69,X70),k2_xboole_0(k1_xboole_0,k3_xboole_0(X69,k3_xboole_0(X70,X71))))) )),
% 10.48/1.74    inference(superposition,[],[f2218,f77])).
% 10.48/1.74  fof(f2218,plain,(
% 10.48/1.74    ( ! [X12,X13] : (k3_xboole_0(X12,X13) = k4_xboole_0(X12,k2_xboole_0(k1_xboole_0,k4_xboole_0(X12,X13)))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f2162,f21])).
% 10.48/1.74  fof(f2162,plain,(
% 10.48/1.74    ( ! [X12,X13] : (k3_xboole_0(k4_xboole_0(X12,k1_xboole_0),X13) = k4_xboole_0(X12,k2_xboole_0(k1_xboole_0,k4_xboole_0(X12,X13)))) )),
% 10.48/1.74    inference(superposition,[],[f138,f116])).
% 10.48/1.74  fof(f116,plain,(
% 10.48/1.74    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k4_xboole_0(X7,k2_xboole_0(k1_xboole_0,X8))) )),
% 10.48/1.74    inference(superposition,[],[f30,f21])).
% 10.48/1.74  fof(f5710,plain,(
% 10.48/1.74    ( ! [X78,X77] : (k3_xboole_0(k3_xboole_0(X77,X78),X78) = k4_xboole_0(k3_xboole_0(X77,X78),k2_xboole_0(k1_xboole_0,k3_xboole_0(X77,k3_xboole_0(X78,k1_xboole_0))))) )),
% 10.48/1.74    inference(superposition,[],[f2218,f76])).
% 10.48/1.74  fof(f76,plain,(
% 10.48/1.74    ( ! [X0,X1] : (k4_xboole_0(k3_xboole_0(X1,X0),X0) = k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0))) )),
% 10.48/1.74    inference(superposition,[],[f28,f31])).
% 10.48/1.74  fof(f562,plain,(
% 10.48/1.74    ( ! [X10,X11,X9] : (k3_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X10,X11)) = k3_xboole_0(k3_xboole_0(X9,X10),X11)) )),
% 10.48/1.74    inference(forward_demodulation,[],[f542,f23])).
% 10.48/1.74  fof(f542,plain,(
% 10.48/1.74    ( ! [X10,X11,X9] : (k3_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X10,X11)) = k4_xboole_0(k3_xboole_0(X9,X10),k4_xboole_0(k3_xboole_0(X9,X10),X11))) )),
% 10.48/1.74    inference(superposition,[],[f23,f86])).
% 10.48/1.74  fof(f6675,plain,(
% 10.48/1.74    ( ! [X15,X16] : (k5_xboole_0(X15,k4_xboole_0(X16,k3_xboole_0(X15,X16))) = k4_xboole_0(k2_xboole_0(X15,k4_xboole_0(X16,k3_xboole_0(X15,X16))),k3_xboole_0(X15,k3_xboole_0(X16,k1_xboole_0)))) )),
% 10.48/1.74    inference(backward_demodulation,[],[f2736,f6628])).
% 10.48/1.74  fof(f2736,plain,(
% 10.48/1.74    ( ! [X15,X16] : (k5_xboole_0(X15,k4_xboole_0(X16,k3_xboole_0(X15,X16))) = k4_xboole_0(k2_xboole_0(X15,k4_xboole_0(X16,k3_xboole_0(X15,X16))),k3_xboole_0(k3_xboole_0(X15,X16),k1_xboole_0))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f2645,f869])).
% 10.48/1.74  fof(f869,plain,(
% 10.48/1.74    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0)) )),
% 10.48/1.74    inference(superposition,[],[f797,f31])).
% 10.48/1.74  fof(f797,plain,(
% 10.48/1.74    ( ! [X1] : (k4_xboole_0(X1,X1) = k3_xboole_0(k4_xboole_0(X1,X1),k1_xboole_0)) )),
% 10.48/1.74    inference(forward_demodulation,[],[f796,f62])).
% 10.48/1.74  fof(f796,plain,(
% 10.48/1.74    ( ! [X1] : (k5_xboole_0(X1,X1) = k3_xboole_0(k4_xboole_0(X1,X1),k1_xboole_0)) )),
% 10.48/1.74    inference(forward_demodulation,[],[f795,f69])).
% 10.48/1.74  fof(f69,plain,(
% 10.48/1.74    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 10.48/1.74    inference(backward_demodulation,[],[f51,f68])).
% 10.48/1.74  fof(f68,plain,(
% 10.48/1.74    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 10.48/1.74    inference(backward_demodulation,[],[f47,f67])).
% 10.48/1.74  fof(f67,plain,(
% 10.48/1.74    ( ! [X3] : (k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) = X3) )),
% 10.48/1.74    inference(forward_demodulation,[],[f66,f21])).
% 10.48/1.74  fof(f66,plain,(
% 10.48/1.74    ( ! [X3] : (k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) = k4_xboole_0(X3,k1_xboole_0)) )),
% 10.48/1.74    inference(forward_demodulation,[],[f65,f25])).
% 10.48/1.74  fof(f65,plain,(
% 10.48/1.74    ( ! [X3] : (k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) = k4_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f57,f25])).
% 10.48/1.74  fof(f57,plain,(
% 10.48/1.74    ( ! [X3] : (k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) = k4_xboole_0(X3,k3_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)))) )),
% 10.48/1.74    inference(superposition,[],[f27,f37])).
% 10.48/1.74  fof(f37,plain,(
% 10.48/1.74    ( ! [X0] : (k2_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 10.48/1.74    inference(forward_demodulation,[],[f35,f22])).
% 10.48/1.74  fof(f35,plain,(
% 10.48/1.74    ( ! [X0] : (k2_xboole_0(X0,X0) = k2_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 10.48/1.74    inference(superposition,[],[f24,f31])).
% 10.48/1.74  fof(f47,plain,(
% 10.48/1.74    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 10.48/1.74    inference(superposition,[],[f26,f20])).
% 10.48/1.74  fof(f20,plain,(
% 10.48/1.74    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 10.48/1.74    inference(cnf_transformation,[],[f10])).
% 10.48/1.74  fof(f10,axiom,(
% 10.48/1.74    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 10.48/1.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 10.48/1.74  fof(f51,plain,(
% 10.48/1.74    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k4_xboole_0(X0,X0))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f49,f20])).
% 10.48/1.74  fof(f49,plain,(
% 10.48/1.74    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0))) )),
% 10.48/1.74    inference(superposition,[],[f26,f31])).
% 10.48/1.74  fof(f795,plain,(
% 10.48/1.74    ( ! [X1] : (k5_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X1,X1))) = k3_xboole_0(k4_xboole_0(X1,X1),k1_xboole_0)) )),
% 10.48/1.74    inference(forward_demodulation,[],[f760,f31])).
% 10.48/1.74  fof(f760,plain,(
% 10.48/1.74    ( ! [X1] : (k5_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X1,X1))) = k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1))) )),
% 10.48/1.74    inference(superposition,[],[f62,f93])).
% 10.48/1.74  fof(f93,plain,(
% 10.48/1.74    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k4_xboole_0(X2,X2),X3)) )),
% 10.48/1.74    inference(superposition,[],[f29,f62])).
% 10.48/1.74  fof(f2645,plain,(
% 10.48/1.74    ( ! [X15,X16] : (k5_xboole_0(X15,k4_xboole_0(X16,k3_xboole_0(X15,X16))) = k4_xboole_0(k2_xboole_0(X15,k4_xboole_0(X16,k3_xboole_0(X15,X16))),k3_xboole_0(k3_xboole_0(k3_xboole_0(X15,X16),k1_xboole_0),k1_xboole_0))) )),
% 10.48/1.74    inference(superposition,[],[f83,f1146])).
% 10.48/1.74  fof(f1146,plain,(
% 10.48/1.74    ( ! [X7] : (k4_xboole_0(X7,X7) = k3_xboole_0(k3_xboole_0(X7,k1_xboole_0),k1_xboole_0)) )),
% 10.48/1.74    inference(forward_demodulation,[],[f1088,f37])).
% 10.48/1.74  fof(f1088,plain,(
% 10.48/1.74    ( ! [X7] : (k3_xboole_0(k3_xboole_0(X7,k1_xboole_0),k1_xboole_0) = k4_xboole_0(X7,k2_xboole_0(X7,k3_xboole_0(X7,k1_xboole_0)))) )),
% 10.48/1.74    inference(superposition,[],[f113,f31])).
% 10.48/1.74  fof(f113,plain,(
% 10.48/1.74    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) )),
% 10.48/1.74    inference(superposition,[],[f30,f31])).
% 10.48/1.74  fof(f83,plain,(
% 10.48/1.74    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(k2_xboole_0(X2,k4_xboole_0(X3,X4)),k4_xboole_0(k3_xboole_0(X2,X3),X4))) )),
% 10.48/1.74    inference(superposition,[],[f27,f28])).
% 10.48/1.74  fof(f25541,plain,(
% 10.48/1.74    ( ! [X10,X9] : (k5_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)))) = k4_xboole_0(k2_xboole_0(X9,X10),k3_xboole_0(X9,k3_xboole_0(X10,k1_xboole_0)))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f25540,f11513])).
% 10.48/1.74  fof(f11513,plain,(
% 10.48/1.74    ( ! [X28,X26,X27] : (k4_xboole_0(X28,k4_xboole_0(k3_xboole_0(X26,X27),X28)) = k4_xboole_0(X28,k3_xboole_0(X26,k3_xboole_0(X27,k1_xboole_0)))) )),
% 10.48/1.74    inference(superposition,[],[f11452,f6628])).
% 10.48/1.74  fof(f11452,plain,(
% 10.48/1.74    ( ! [X4,X3] : (k4_xboole_0(X3,k3_xboole_0(X4,k1_xboole_0)) = k4_xboole_0(X3,k4_xboole_0(X4,X3))) )),
% 10.48/1.74    inference(backward_demodulation,[],[f6709,f11448])).
% 10.48/1.74  fof(f6709,plain,(
% 10.48/1.74    ( ! [X4,X3] : (k4_xboole_0(X3,k4_xboole_0(X4,k3_xboole_0(X3,X4))) = k4_xboole_0(X3,k3_xboole_0(X4,k1_xboole_0))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f6663,f25])).
% 10.48/1.74  fof(f6663,plain,(
% 10.48/1.74    ( ! [X4,X3] : (k4_xboole_0(X3,k4_xboole_0(X4,k3_xboole_0(X3,X4))) = k4_xboole_0(X3,k3_xboole_0(X3,k3_xboole_0(X4,k1_xboole_0)))) )),
% 10.48/1.74    inference(backward_demodulation,[],[f457,f6628])).
% 10.48/1.74  fof(f457,plain,(
% 10.48/1.74    ( ! [X4,X3] : (k4_xboole_0(X3,k4_xboole_0(X4,k3_xboole_0(X3,X4))) = k4_xboole_0(X3,k3_xboole_0(k3_xboole_0(X3,X4),k1_xboole_0))) )),
% 10.48/1.74    inference(superposition,[],[f85,f31])).
% 10.48/1.74  fof(f85,plain,(
% 10.48/1.74    ( ! [X10,X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X9,X10)) = k4_xboole_0(X8,k4_xboole_0(k3_xboole_0(X8,X9),X10))) )),
% 10.48/1.74    inference(superposition,[],[f25,f28])).
% 10.48/1.74  fof(f25540,plain,(
% 10.48/1.74    ( ! [X10,X9] : (k5_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)))) = k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(k3_xboole_0(X9,X10),k2_xboole_0(X9,X10)))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f25539,f9900])).
% 10.48/1.74  fof(f9900,plain,(
% 10.48/1.74    ( ! [X92,X90,X91] : (k4_xboole_0(k2_xboole_0(X90,X91),k4_xboole_0(k3_xboole_0(X90,X91),X92)) = k3_xboole_0(k2_xboole_0(X90,X91),k2_xboole_0(k5_xboole_0(X90,X91),X92))) )),
% 10.48/1.74    inference(superposition,[],[f662,f27])).
% 10.48/1.74  fof(f662,plain,(
% 10.48/1.74    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k3_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f624,f85])).
% 10.48/1.74  fof(f624,plain,(
% 10.48/1.74    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 10.48/1.74    inference(superposition,[],[f23,f114])).
% 10.48/1.74  fof(f114,plain,(
% 10.48/1.74    ( ! [X4,X2,X3] : (k4_xboole_0(k3_xboole_0(X2,X3),X4) = k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4))) )),
% 10.48/1.74    inference(superposition,[],[f30,f23])).
% 10.48/1.74  fof(f25539,plain,(
% 10.48/1.74    ( ! [X10,X9] : (k5_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)))) = k3_xboole_0(k2_xboole_0(X9,X10),k2_xboole_0(k5_xboole_0(X9,X10),k2_xboole_0(X9,X10)))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f25538,f5470])).
% 10.48/1.74  fof(f5470,plain,(
% 10.48/1.74    ( ! [X19,X18] : (k3_xboole_0(X18,k2_xboole_0(X19,X18)) = k4_xboole_0(X18,k3_xboole_0(k4_xboole_0(X18,X19),X19))) )),
% 10.48/1.74    inference(superposition,[],[f23,f2205])).
% 10.48/1.74  fof(f2205,plain,(
% 10.48/1.74    ( ! [X0,X1] : (k3_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(X1,k2_xboole_0(X0,X1))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f2149,f24])).
% 10.48/1.74  fof(f2149,plain,(
% 10.48/1.74    ( ! [X0,X1] : (k3_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 10.48/1.74    inference(superposition,[],[f138,f22])).
% 10.48/1.74  fof(f25538,plain,(
% 10.48/1.74    ( ! [X10,X9] : (k5_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)))) = k4_xboole_0(k2_xboole_0(X9,X10),k3_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k5_xboole_0(X9,X10)))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f25537,f11469])).
% 10.48/1.74  fof(f11469,plain,(
% 10.48/1.74    ( ! [X10,X8,X9] : (k4_xboole_0(X8,k3_xboole_0(X9,X10)) = k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X8,X10)))) )),
% 10.48/1.74    inference(backward_demodulation,[],[f6704,f11466])).
% 10.48/1.74  fof(f11466,plain,(
% 10.48/1.74    ( ! [X39,X37,X38] : (k4_xboole_0(X37,k4_xboole_0(X38,X39)) = k4_xboole_0(X37,k4_xboole_0(k3_xboole_0(X38,X37),X39))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f11398,f85])).
% 10.48/1.74  fof(f11398,plain,(
% 10.48/1.74    ( ! [X39,X37,X38] : (k4_xboole_0(X37,k4_xboole_0(k3_xboole_0(X38,X37),X39)) = k4_xboole_0(X37,k4_xboole_0(k3_xboole_0(X37,X38),X39))) )),
% 10.48/1.74    inference(superposition,[],[f85,f6752])).
% 10.48/1.74  fof(f6704,plain,(
% 10.48/1.74    ( ! [X10,X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(k3_xboole_0(X8,X9),X10))) = k4_xboole_0(X8,k3_xboole_0(X9,X10))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f6631,f25])).
% 10.48/1.74  fof(f6631,plain,(
% 10.48/1.74    ( ! [X10,X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(k3_xboole_0(X8,X9),X10))) = k4_xboole_0(X8,k3_xboole_0(X8,k3_xboole_0(X9,X10)))) )),
% 10.48/1.74    inference(backward_demodulation,[],[f459,f6628])).
% 10.48/1.74  fof(f459,plain,(
% 10.48/1.74    ( ! [X10,X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(k3_xboole_0(X8,X9),X10))) = k4_xboole_0(X8,k3_xboole_0(k3_xboole_0(X8,X9),X10))) )),
% 10.48/1.74    inference(superposition,[],[f85,f23])).
% 10.48/1.74  fof(f25537,plain,(
% 10.48/1.74    ( ! [X10,X9] : (k5_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)))) = k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10))))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f25388,f11466])).
% 10.48/1.74  fof(f25388,plain,(
% 10.48/1.74    ( ! [X10,X9] : (k5_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)))) = k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(k3_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10)),k2_xboole_0(X9,X10)),k4_xboole_0(k2_xboole_0(X9,X10),k5_xboole_0(X9,X10))))) )),
% 10.48/1.74    inference(superposition,[],[f64,f5231])).
% 10.48/1.74  fof(f5231,plain,(
% 10.48/1.74    ( ! [X10,X11] : (k2_xboole_0(X10,X11) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X10,X11),k5_xboole_0(X10,X11)),k2_xboole_0(X10,X11))) )),
% 10.48/1.74    inference(backward_demodulation,[],[f4963,f5230])).
% 10.48/1.74  fof(f5230,plain,(
% 10.48/1.74    ( ! [X12,X13] : (k2_xboole_0(X12,X13) = k2_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)))) )),
% 10.48/1.74    inference(backward_demodulation,[],[f4962,f5229])).
% 10.48/1.74  fof(f5229,plain,(
% 10.48/1.74    ( ! [X17,X16] : (k2_xboole_0(X16,X17) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X16,X17),k5_xboole_0(X16,X17)),k5_xboole_0(X16,X17))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f5228,f4922])).
% 10.48/1.74  fof(f5228,plain,(
% 10.48/1.74    ( ! [X17,X16] : (k2_xboole_0(k2_xboole_0(X16,X17),k5_xboole_0(X16,X17)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X16,X17),k5_xboole_0(X16,X17)),k5_xboole_0(X16,X17))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f5157,f4924])).
% 10.48/1.74  fof(f5157,plain,(
% 10.48/1.74    ( ! [X17,X16] : (k2_xboole_0(k2_xboole_0(X16,X17),k5_xboole_0(X16,X17)) = k2_xboole_0(k5_xboole_0(k2_xboole_0(X16,X17),k5_xboole_0(X16,X17)),k5_xboole_0(X16,X17))) )),
% 10.48/1.74    inference(superposition,[],[f4932,f168])).
% 10.48/1.74  fof(f4932,plain,(
% 10.48/1.74    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))) )),
% 10.48/1.74    inference(backward_demodulation,[],[f4642,f4922])).
% 10.48/1.74  fof(f4962,plain,(
% 10.48/1.74    ( ! [X12,X13] : (k2_xboole_0(k4_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)),k5_xboole_0(X12,X13)) = k2_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f4961,f279])).
% 10.48/1.74  fof(f279,plain,(
% 10.48/1.74    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k3_xboole_0(k4_xboole_0(X4,X5),k1_xboole_0))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f278,f31])).
% 10.48/1.74  fof(f278,plain,(
% 10.48/1.74    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f264,f62])).
% 10.48/1.74  fof(f264,plain,(
% 10.48/1.74    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)))) )),
% 10.48/1.74    inference(superposition,[],[f96,f33])).
% 10.48/1.74  fof(f4961,plain,(
% 10.48/1.74    ( ! [X12,X13] : (k2_xboole_0(k4_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)),k5_xboole_0(X12,X13)) = k5_xboole_0(k2_xboole_0(X12,X13),k3_xboole_0(k4_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)),k1_xboole_0))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f4960,f137])).
% 10.48/1.74  fof(f4960,plain,(
% 10.48/1.74    ( ! [X12,X13] : (k2_xboole_0(k4_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)),k5_xboole_0(X12,X13)) = k5_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(k5_xboole_0(X12,X13),k2_xboole_0(X12,X13))))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f4959,f2205])).
% 10.48/1.74  fof(f4959,plain,(
% 10.48/1.74    ( ! [X12,X13] : (k2_xboole_0(k4_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)),k5_xboole_0(X12,X13)) = k5_xboole_0(k2_xboole_0(X12,X13),k3_xboole_0(k4_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)),k5_xboole_0(X12,X13)))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f4925,f4924])).
% 10.48/1.74  fof(f4925,plain,(
% 10.48/1.74    ( ! [X12,X13] : (k2_xboole_0(k5_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)),k5_xboole_0(X12,X13)) = k5_xboole_0(k2_xboole_0(X12,X13),k3_xboole_0(k5_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)),k5_xboole_0(X12,X13)))) )),
% 10.48/1.74    inference(backward_demodulation,[],[f3791,f4922])).
% 10.48/1.74  fof(f3791,plain,(
% 10.48/1.74    ( ! [X12,X13] : (k2_xboole_0(k5_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)),k5_xboole_0(X12,X13)) = k5_xboole_0(k2_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)),k3_xboole_0(k5_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,X13)),k5_xboole_0(X12,X13)))) )),
% 10.48/1.74    inference(superposition,[],[f48,f168])).
% 10.48/1.74  fof(f4963,plain,(
% 10.48/1.74    ( ! [X10,X11] : (k2_xboole_0(k4_xboole_0(k2_xboole_0(X10,X11),k5_xboole_0(X10,X11)),k2_xboole_0(X10,X11)) = k2_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(k2_xboole_0(X10,X11),k5_xboole_0(X10,X11)))) )),
% 10.48/1.74    inference(backward_demodulation,[],[f357,f4962])).
% 10.48/1.74  fof(f357,plain,(
% 10.48/1.74    ( ! [X10,X11] : (k2_xboole_0(k4_xboole_0(k2_xboole_0(X10,X11),k5_xboole_0(X10,X11)),k2_xboole_0(X10,X11)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X10,X11),k5_xboole_0(X10,X11)),k5_xboole_0(X10,X11))) )),
% 10.48/1.74    inference(forward_demodulation,[],[f347,f61])).
% 10.48/1.74  fof(f61,plain,(
% 10.48/1.74    ( ! [X2,X3] : (k3_xboole_0(k2_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X3))) )),
% 10.48/1.74    inference(superposition,[],[f23,f27])).
% 10.48/1.74  fof(f347,plain,(
% 10.48/1.74    ( ! [X10,X11] : (k2_xboole_0(k3_xboole_0(k2_xboole_0(X10,X11),k3_xboole_0(X10,X11)),k2_xboole_0(X10,X11)) = k2_xboole_0(k3_xboole_0(k2_xboole_0(X10,X11),k3_xboole_0(X10,X11)),k5_xboole_0(X10,X11))) )),
% 10.48/1.74    inference(superposition,[],[f41,f27])).
% 10.48/1.74  fof(f41,plain,(
% 10.48/1.74    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 10.48/1.74    inference(superposition,[],[f24,f25])).
% 10.48/1.74  fof(f19,plain,(
% 10.48/1.74    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 10.48/1.74    inference(cnf_transformation,[],[f18])).
% 10.48/1.74  fof(f18,plain,(
% 10.48/1.74    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 10.48/1.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 10.48/1.74  fof(f17,plain,(
% 10.48/1.74    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 10.48/1.74    introduced(choice_axiom,[])).
% 10.48/1.74  fof(f16,plain,(
% 10.48/1.74    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 10.48/1.74    inference(ennf_transformation,[],[f14])).
% 10.48/1.74  fof(f14,negated_conjecture,(
% 10.48/1.74    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 10.48/1.74    inference(negated_conjecture,[],[f13])).
% 10.48/1.74  fof(f13,conjecture,(
% 10.48/1.74    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 10.48/1.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 10.48/1.74  % SZS output end Proof for theBenchmark
% 10.48/1.74  % (21278)------------------------------
% 10.48/1.74  % (21278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.48/1.74  % (21278)Termination reason: Refutation
% 10.48/1.74  
% 10.48/1.74  % (21278)Memory used [KB]: 22131
% 10.48/1.74  % (21278)Time elapsed: 1.317 s
% 10.48/1.74  % (21278)------------------------------
% 10.48/1.74  % (21278)------------------------------
% 10.48/1.76  % (21274)Success in time 1.393 s
%------------------------------------------------------------------------------
