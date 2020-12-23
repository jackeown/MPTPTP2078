%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:19 EST 2020

% Result     : Theorem 3.26s
% Output     : Refutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :  126 (20443 expanded)
%              Number of leaves         :   15 (6159 expanded)
%              Depth                    :   47
%              Number of atoms          :  127 (20444 expanded)
%              Number of equality atoms :  126 (20443 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13701,plain,(
    $false ),
    inference(subsumption_resolution,[],[f22,f13697])).

fof(f13697,plain,(
    ! [X17,X16] : k5_xboole_0(X16,X17) = k4_xboole_0(k2_xboole_0(X16,X17),k3_xboole_0(X16,X17)) ),
    inference(backward_demodulation,[],[f3401,f13696])).

fof(f13696,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k3_xboole_0(X12,k4_xboole_0(X13,k5_xboole_0(X12,X13))) ),
    inference(forward_demodulation,[],[f13693,f695])).

fof(f695,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k5_xboole_0(X12,k4_xboole_0(X12,X13)) ),
    inference(forward_demodulation,[],[f688,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f688,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k4_xboole_0(X12,X13)) = k5_xboole_0(X12,k4_xboole_0(X12,X13)) ),
    inference(superposition,[],[f44,f400])).

fof(f400,plain,(
    ! [X8,X7] : k4_xboole_0(X7,X8) = k3_xboole_0(k4_xboole_0(X7,X8),X7) ),
    inference(forward_demodulation,[],[f395,f211])).

fof(f211,plain,(
    ! [X3] : k4_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(forward_demodulation,[],[f207,f201])).

fof(f201,plain,(
    ! [X3] : k5_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(forward_demodulation,[],[f197,f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f197,plain,(
    ! [X3] : k2_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f29,f178])).

fof(f178,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3) ),
    inference(backward_demodulation,[],[f141,f174])).

fof(f174,plain,(
    ! [X5] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X5) ),
    inference(forward_demodulation,[],[f173,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f173,plain,(
    ! [X5] : k3_xboole_0(k1_xboole_0,X5) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5)) ),
    inference(forward_demodulation,[],[f172,f141])).

fof(f172,plain,(
    ! [X5] : k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5)) = k4_xboole_0(k1_xboole_0,X5) ),
    inference(forward_demodulation,[],[f171,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f171,plain,(
    ! [X5] : k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5)) ),
    inference(forward_demodulation,[],[f166,f23])).

fof(f166,plain,(
    ! [X5] : k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5)) = k2_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5)),k1_xboole_0) ),
    inference(superposition,[],[f32,f138])).

fof(f138,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(forward_demodulation,[],[f137,f57])).

fof(f57,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f56,f23])).

fof(f56,plain,(
    ! [X1] : k2_xboole_0(k5_xboole_0(X1,X1),X1) = X1 ),
    inference(forward_demodulation,[],[f55,f47])).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f46,f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k5_xboole_0(X0,k5_xboole_0(X0,X0)) ),
    inference(superposition,[],[f29,f43])).

fof(f43,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f30,f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f55,plain,(
    ! [X1] : k5_xboole_0(X1,k5_xboole_0(X1,X1)) = k2_xboole_0(k5_xboole_0(X1,X1),X1) ),
    inference(forward_demodulation,[],[f53,f26])).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f53,plain,(
    ! [X1] : k5_xboole_0(k5_xboole_0(X1,X1),X1) = k2_xboole_0(k5_xboole_0(X1,X1),X1) ),
    inference(superposition,[],[f29,f51])).

fof(f51,plain,(
    ! [X0] : k4_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f48,f25])).

fof(f48,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k4_xboole_0(X0,k5_xboole_0(X0,X0)) ),
    inference(superposition,[],[f31,f43])).

fof(f137,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(forward_demodulation,[],[f135,f43])).

fof(f135,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f31,f122])).

fof(f122,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f121,f57])).

fof(f121,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f115,f43])).

fof(f115,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f97,f28])).

fof(f97,plain,(
    ! [X7] : k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X7)) = k4_xboole_0(k1_xboole_0,X7) ),
    inference(superposition,[],[f33,f60])).

fof(f60,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f51,f57])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f141,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k3_xboole_0(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f140,f23])).

fof(f140,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X3),k1_xboole_0) ),
    inference(forward_demodulation,[],[f139,f30])).

fof(f139,plain,(
    ! [X3] : k2_xboole_0(k3_xboole_0(k1_xboole_0,X3),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3)) ),
    inference(forward_demodulation,[],[f136,f26])).

fof(f136,plain,(
    ! [X3] : k2_xboole_0(k3_xboole_0(k1_xboole_0,X3),k1_xboole_0) = k5_xboole_0(k3_xboole_0(k1_xboole_0,X3),k1_xboole_0) ),
    inference(superposition,[],[f29,f122])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f207,plain,(
    ! [X3] : k5_xboole_0(X3,k1_xboole_0) = k4_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f30,f184])).

fof(f184,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(X3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f157,f178])).

fof(f157,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k3_xboole_0(X3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f156,f23])).

fof(f156,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k2_xboole_0(k3_xboole_0(X3,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f155,f44])).

fof(f155,plain,(
    ! [X3] : k2_xboole_0(k3_xboole_0(X3,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X3,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f151,f26])).

fof(f151,plain,(
    ! [X3] : k2_xboole_0(k3_xboole_0(X3,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k3_xboole_0(X3,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f29,f124])).

fof(f124,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f123,f57])).

fof(f123,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f116,f43])).

fof(f116,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f97,f38])).

fof(f38,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(superposition,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f395,plain,(
    ! [X8,X7] : k3_xboole_0(k4_xboole_0(X7,X8),X7) = k4_xboole_0(k4_xboole_0(X7,X8),k1_xboole_0) ),
    inference(superposition,[],[f31,f366])).

fof(f366,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5) ),
    inference(forward_demodulation,[],[f350,f28])).

fof(f350,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,k3_xboole_0(X5,X6))) ),
    inference(superposition,[],[f300,f30])).

fof(f300,plain,(
    ! [X6,X7] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X6,X7),k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f261,f32])).

fof(f261,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f256,f178])).

fof(f256,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f94,f250])).

fof(f250,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f43,f249])).

fof(f249,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(forward_demodulation,[],[f246,f184])).

fof(f246,plain,(
    ! [X2] : k3_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,X2) ),
    inference(superposition,[],[f31,f211])).

fof(f94,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(superposition,[],[f33,f43])).

fof(f44,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f30,f27])).

fof(f13693,plain,(
    ! [X12,X13] : k5_xboole_0(X12,k4_xboole_0(X12,X13)) = k3_xboole_0(X12,k4_xboole_0(X13,k5_xboole_0(X12,X13))) ),
    inference(backward_demodulation,[],[f1332,f13555])).

fof(f13555,plain,(
    ! [X39,X38] : k4_xboole_0(X39,X38) = k5_xboole_0(X38,k2_xboole_0(X39,X38)) ),
    inference(superposition,[],[f737,f13428])).

fof(f13428,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(X4,X3) ),
    inference(superposition,[],[f13368,f201])).

fof(f13368,plain,(
    ! [X39,X40] : k5_xboole_0(k2_xboole_0(X40,X39),k1_xboole_0) = k2_xboole_0(X39,X40) ),
    inference(forward_demodulation,[],[f13279,f13361])).

fof(f13361,plain,(
    ! [X15,X16] : k2_xboole_0(X15,X16) = k3_xboole_0(k2_xboole_0(X15,X16),k2_xboole_0(X16,X15)) ),
    inference(forward_demodulation,[],[f13268,f211])).

fof(f13268,plain,(
    ! [X15,X16] : k3_xboole_0(k2_xboole_0(X15,X16),k2_xboole_0(X16,X15)) = k4_xboole_0(k2_xboole_0(X15,X16),k1_xboole_0) ),
    inference(superposition,[],[f31,f13180])).

fof(f13180,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f13179,f29])).

fof(f13179,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),k2_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f13178,f26])).

fof(f13178,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X4,X3),X3),k2_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f13177,f701])).

fof(f701,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X10)) = k5_xboole_0(k4_xboole_0(X8,X9),X10) ),
    inference(superposition,[],[f34,f30])).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f13177,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X3),X3)),k2_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f13176,f709])).

fof(f709,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f34,f26])).

fof(f13176,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(k3_xboole_0(X4,X3),k5_xboole_0(X3,X4)),k2_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f12992,f26])).

fof(f12992,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(k5_xboole_0(X3,X4),k3_xboole_0(X4,X3)),k2_xboole_0(X4,X3)) ),
    inference(superposition,[],[f300,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f32,f26])).

fof(f13279,plain,(
    ! [X39,X40] : k2_xboole_0(X39,X40) = k5_xboole_0(k3_xboole_0(k2_xboole_0(X40,X39),k2_xboole_0(X39,X40)),k1_xboole_0) ),
    inference(superposition,[],[f762,f13180])).

fof(f762,plain,(
    ! [X8,X7] : k5_xboole_0(k3_xboole_0(X8,X7),k4_xboole_0(X7,X8)) = X7 ),
    inference(superposition,[],[f733,f44])).

fof(f733,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f725,f26])).

fof(f725,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f698,f230])).

fof(f230,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f201,f26])).

fof(f698,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f34,f250])).

fof(f737,plain,(
    ! [X12,X11] : k4_xboole_0(X12,X11) = k5_xboole_0(X11,k2_xboole_0(X11,X12)) ),
    inference(superposition,[],[f725,f29])).

fof(f1332,plain,(
    ! [X12,X13] : k5_xboole_0(X12,k5_xboole_0(X13,k2_xboole_0(X12,X13))) = k3_xboole_0(X12,k4_xboole_0(X13,k5_xboole_0(X12,X13))) ),
    inference(forward_demodulation,[],[f1331,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f1331,plain,(
    ! [X12,X13] : k4_xboole_0(k3_xboole_0(X12,X13),k5_xboole_0(X12,X13)) = k5_xboole_0(X12,k5_xboole_0(X13,k2_xboole_0(X12,X13))) ),
    inference(forward_demodulation,[],[f1305,f34])).

fof(f1305,plain,(
    ! [X12,X13] : k4_xboole_0(k3_xboole_0(X12,X13),k5_xboole_0(X12,X13)) = k5_xboole_0(k5_xboole_0(X12,X13),k2_xboole_0(X12,X13)) ),
    inference(superposition,[],[f737,f32])).

fof(f3401,plain,(
    ! [X17,X16] : k5_xboole_0(X16,X17) = k4_xboole_0(k2_xboole_0(X16,X17),k3_xboole_0(X16,k4_xboole_0(X17,k5_xboole_0(X16,X17)))) ),
    inference(forward_demodulation,[],[f3340,f35])).

fof(f3340,plain,(
    ! [X17,X16] : k5_xboole_0(X16,X17) = k4_xboole_0(k2_xboole_0(X16,X17),k4_xboole_0(k3_xboole_0(X16,X17),k5_xboole_0(X16,X17))) ),
    inference(superposition,[],[f1579,f32])).

fof(f1579,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = X2 ),
    inference(forward_demodulation,[],[f1578,f308])).

fof(f308,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k2_xboole_0(X3,X4)) = X3 ),
    inference(forward_demodulation,[],[f304,f211])).

fof(f304,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k1_xboole_0) = k3_xboole_0(X3,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f31,f261])).

fof(f1578,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f1554,f27])).

fof(f1554,plain,(
    ! [X2,X3] : k3_xboole_0(k2_xboole_0(X2,X3),X2) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) ),
    inference(superposition,[],[f31,f752])).

fof(f752,plain,(
    ! [X12,X13] : k4_xboole_0(k2_xboole_0(X12,X13),X12) = k4_xboole_0(X13,X12) ),
    inference(backward_demodulation,[],[f323,f737])).

fof(f323,plain,(
    ! [X12,X13] : k4_xboole_0(k2_xboole_0(X12,X13),X12) = k5_xboole_0(X12,k2_xboole_0(X12,X13)) ),
    inference(forward_demodulation,[],[f321,f26])).

fof(f321,plain,(
    ! [X12,X13] : k4_xboole_0(k2_xboole_0(X12,X13),X12) = k5_xboole_0(k2_xboole_0(X12,X13),X12) ),
    inference(superposition,[],[f44,f308])).

fof(f22,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:07:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (20039)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (20037)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (20046)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (20045)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (20045)Refutation not found, incomplete strategy% (20045)------------------------------
% 0.22/0.48  % (20045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (20045)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (20045)Memory used [KB]: 10618
% 0.22/0.48  % (20045)Time elapsed: 0.060 s
% 0.22/0.48  % (20045)------------------------------
% 0.22/0.48  % (20045)------------------------------
% 0.22/0.48  % (20035)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (20044)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (20049)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (20043)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (20036)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (20034)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (20038)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (20042)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (20041)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (20040)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (20048)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (20050)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.51  % (20047)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.52  % (20051)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 3.26/0.85  % (20050)Refutation found. Thanks to Tanya!
% 3.26/0.85  % SZS status Theorem for theBenchmark
% 3.95/0.86  % SZS output start Proof for theBenchmark
% 3.95/0.86  fof(f13701,plain,(
% 3.95/0.86    $false),
% 3.95/0.86    inference(subsumption_resolution,[],[f22,f13697])).
% 3.95/0.86  fof(f13697,plain,(
% 3.95/0.86    ( ! [X17,X16] : (k5_xboole_0(X16,X17) = k4_xboole_0(k2_xboole_0(X16,X17),k3_xboole_0(X16,X17))) )),
% 3.95/0.86    inference(backward_demodulation,[],[f3401,f13696])).
% 3.95/0.86  fof(f13696,plain,(
% 3.95/0.86    ( ! [X12,X13] : (k3_xboole_0(X12,X13) = k3_xboole_0(X12,k4_xboole_0(X13,k5_xboole_0(X12,X13)))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f13693,f695])).
% 3.95/0.86  fof(f695,plain,(
% 3.95/0.86    ( ! [X12,X13] : (k3_xboole_0(X12,X13) = k5_xboole_0(X12,k4_xboole_0(X12,X13))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f688,f31])).
% 3.95/0.86  fof(f31,plain,(
% 3.95/0.86    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.95/0.86    inference(cnf_transformation,[],[f10])).
% 3.95/0.86  fof(f10,axiom,(
% 3.95/0.86    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.95/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.95/0.86  fof(f688,plain,(
% 3.95/0.86    ( ! [X12,X13] : (k4_xboole_0(X12,k4_xboole_0(X12,X13)) = k5_xboole_0(X12,k4_xboole_0(X12,X13))) )),
% 3.95/0.86    inference(superposition,[],[f44,f400])).
% 3.95/0.86  fof(f400,plain,(
% 3.95/0.86    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k3_xboole_0(k4_xboole_0(X7,X8),X7)) )),
% 3.95/0.86    inference(forward_demodulation,[],[f395,f211])).
% 3.95/0.86  fof(f211,plain,(
% 3.95/0.86    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = X3) )),
% 3.95/0.86    inference(forward_demodulation,[],[f207,f201])).
% 3.95/0.86  fof(f201,plain,(
% 3.95/0.86    ( ! [X3] : (k5_xboole_0(X3,k1_xboole_0) = X3) )),
% 3.95/0.86    inference(forward_demodulation,[],[f197,f23])).
% 3.95/0.86  fof(f23,plain,(
% 3.95/0.86    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.95/0.86    inference(cnf_transformation,[],[f7])).
% 3.95/0.86  fof(f7,axiom,(
% 3.95/0.86    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.95/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 3.95/0.86  fof(f197,plain,(
% 3.95/0.86    ( ! [X3] : (k2_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X3,k1_xboole_0)) )),
% 3.95/0.86    inference(superposition,[],[f29,f178])).
% 3.95/0.86  fof(f178,plain,(
% 3.95/0.86    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3)) )),
% 3.95/0.86    inference(backward_demodulation,[],[f141,f174])).
% 3.95/0.86  fof(f174,plain,(
% 3.95/0.86    ( ! [X5] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X5)) )),
% 3.95/0.86    inference(forward_demodulation,[],[f173,f28])).
% 3.95/0.86  fof(f28,plain,(
% 3.95/0.86    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.95/0.86    inference(cnf_transformation,[],[f8])).
% 3.95/0.86  fof(f8,axiom,(
% 3.95/0.86    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.95/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 3.95/0.86  fof(f173,plain,(
% 3.95/0.86    ( ! [X5] : (k3_xboole_0(k1_xboole_0,X5) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f172,f141])).
% 3.95/0.86  fof(f172,plain,(
% 3.95/0.86    ( ! [X5] : (k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5)) = k4_xboole_0(k1_xboole_0,X5)) )),
% 3.95/0.86    inference(forward_demodulation,[],[f171,f30])).
% 3.95/0.86  fof(f30,plain,(
% 3.95/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.95/0.86    inference(cnf_transformation,[],[f5])).
% 3.95/0.86  fof(f5,axiom,(
% 3.95/0.86    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.95/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.95/0.86  fof(f171,plain,(
% 3.95/0.86    ( ! [X5] : (k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f166,f23])).
% 3.95/0.86  fof(f166,plain,(
% 3.95/0.86    ( ! [X5] : (k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5)) = k2_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5)),k1_xboole_0)) )),
% 3.95/0.86    inference(superposition,[],[f32,f138])).
% 3.95/0.86  fof(f138,plain,(
% 3.95/0.86    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f137,f57])).
% 3.95/0.86  fof(f57,plain,(
% 3.95/0.86    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.95/0.86    inference(superposition,[],[f56,f23])).
% 3.95/0.86  fof(f56,plain,(
% 3.95/0.86    ( ! [X1] : (k2_xboole_0(k5_xboole_0(X1,X1),X1) = X1) )),
% 3.95/0.86    inference(forward_demodulation,[],[f55,f47])).
% 3.95/0.86  fof(f47,plain,(
% 3.95/0.86    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 3.95/0.86    inference(forward_demodulation,[],[f46,f24])).
% 3.95/0.86  fof(f24,plain,(
% 3.95/0.86    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 3.95/0.86    inference(cnf_transformation,[],[f17])).
% 3.95/0.86  fof(f17,plain,(
% 3.95/0.86    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 3.95/0.86    inference(rectify,[],[f3])).
% 3.95/0.86  fof(f3,axiom,(
% 3.95/0.86    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 3.95/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 3.95/0.86  fof(f46,plain,(
% 3.95/0.86    ( ! [X0] : (k2_xboole_0(X0,X0) = k5_xboole_0(X0,k5_xboole_0(X0,X0))) )),
% 3.95/0.86    inference(superposition,[],[f29,f43])).
% 3.95/0.86  fof(f43,plain,(
% 3.95/0.86    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 3.95/0.86    inference(superposition,[],[f30,f25])).
% 3.95/0.86  fof(f25,plain,(
% 3.95/0.86    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.95/0.86    inference(cnf_transformation,[],[f18])).
% 3.95/0.86  fof(f18,plain,(
% 3.95/0.86    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.95/0.86    inference(rectify,[],[f4])).
% 3.95/0.86  fof(f4,axiom,(
% 3.95/0.86    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.95/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 3.95/0.86  fof(f55,plain,(
% 3.95/0.86    ( ! [X1] : (k5_xboole_0(X1,k5_xboole_0(X1,X1)) = k2_xboole_0(k5_xboole_0(X1,X1),X1)) )),
% 3.95/0.86    inference(forward_demodulation,[],[f53,f26])).
% 3.95/0.86  fof(f26,plain,(
% 3.95/0.86    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.95/0.86    inference(cnf_transformation,[],[f2])).
% 3.95/0.86  fof(f2,axiom,(
% 3.95/0.86    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.95/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 3.95/0.86  fof(f53,plain,(
% 3.95/0.86    ( ! [X1] : (k5_xboole_0(k5_xboole_0(X1,X1),X1) = k2_xboole_0(k5_xboole_0(X1,X1),X1)) )),
% 3.95/0.86    inference(superposition,[],[f29,f51])).
% 3.95/0.86  fof(f51,plain,(
% 3.95/0.86    ( ! [X0] : (k4_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 3.95/0.86    inference(forward_demodulation,[],[f48,f25])).
% 3.95/0.86  fof(f48,plain,(
% 3.95/0.86    ( ! [X0] : (k3_xboole_0(X0,X0) = k4_xboole_0(X0,k5_xboole_0(X0,X0))) )),
% 3.95/0.86    inference(superposition,[],[f31,f43])).
% 3.95/0.86  fof(f137,plain,(
% 3.95/0.86    ( ! [X2] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f135,f43])).
% 3.95/0.86  fof(f135,plain,(
% 3.95/0.86    ( ! [X2] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2))) )),
% 3.95/0.86    inference(superposition,[],[f31,f122])).
% 3.95/0.86  fof(f122,plain,(
% 3.95/0.86    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f121,f57])).
% 3.95/0.86  fof(f121,plain,(
% 3.95/0.86    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f115,f43])).
% 3.95/0.86  fof(f115,plain,(
% 3.95/0.86    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 3.95/0.86    inference(superposition,[],[f97,f28])).
% 3.95/0.86  fof(f97,plain,(
% 3.95/0.86    ( ! [X7] : (k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X7)) = k4_xboole_0(k1_xboole_0,X7)) )),
% 3.95/0.86    inference(superposition,[],[f33,f60])).
% 3.95/0.86  fof(f60,plain,(
% 3.95/0.86    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.95/0.86    inference(superposition,[],[f51,f57])).
% 3.95/0.86  fof(f33,plain,(
% 3.95/0.86    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.95/0.86    inference(cnf_transformation,[],[f9])).
% 3.95/0.86  fof(f9,axiom,(
% 3.95/0.86    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.95/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 3.95/0.86  fof(f32,plain,(
% 3.95/0.86    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 3.95/0.86    inference(cnf_transformation,[],[f13])).
% 3.95/0.86  fof(f13,axiom,(
% 3.95/0.86    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.95/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 3.95/0.86  fof(f141,plain,(
% 3.95/0.86    ( ! [X3] : (k4_xboole_0(k1_xboole_0,X3) = k3_xboole_0(k1_xboole_0,X3)) )),
% 3.95/0.86    inference(forward_demodulation,[],[f140,f23])).
% 3.95/0.86  fof(f140,plain,(
% 3.95/0.86    ( ! [X3] : (k4_xboole_0(k1_xboole_0,X3) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X3),k1_xboole_0)) )),
% 3.95/0.86    inference(forward_demodulation,[],[f139,f30])).
% 3.95/0.86  fof(f139,plain,(
% 3.95/0.86    ( ! [X3] : (k2_xboole_0(k3_xboole_0(k1_xboole_0,X3),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f136,f26])).
% 3.95/0.86  fof(f136,plain,(
% 3.95/0.86    ( ! [X3] : (k2_xboole_0(k3_xboole_0(k1_xboole_0,X3),k1_xboole_0) = k5_xboole_0(k3_xboole_0(k1_xboole_0,X3),k1_xboole_0)) )),
% 3.95/0.86    inference(superposition,[],[f29,f122])).
% 3.95/0.86  fof(f29,plain,(
% 3.95/0.86    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.95/0.86    inference(cnf_transformation,[],[f14])).
% 3.95/0.86  fof(f14,axiom,(
% 3.95/0.86    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.95/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 3.95/0.86  fof(f207,plain,(
% 3.95/0.86    ( ! [X3] : (k5_xboole_0(X3,k1_xboole_0) = k4_xboole_0(X3,k1_xboole_0)) )),
% 3.95/0.86    inference(superposition,[],[f30,f184])).
% 3.95/0.86  fof(f184,plain,(
% 3.95/0.86    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(X3,k1_xboole_0)) )),
% 3.95/0.86    inference(backward_demodulation,[],[f157,f178])).
% 3.95/0.86  fof(f157,plain,(
% 3.95/0.86    ( ! [X3] : (k4_xboole_0(k1_xboole_0,X3) = k3_xboole_0(X3,k1_xboole_0)) )),
% 3.95/0.86    inference(forward_demodulation,[],[f156,f23])).
% 3.95/0.86  fof(f156,plain,(
% 3.95/0.86    ( ! [X3] : (k4_xboole_0(k1_xboole_0,X3) = k2_xboole_0(k3_xboole_0(X3,k1_xboole_0),k1_xboole_0)) )),
% 3.95/0.86    inference(forward_demodulation,[],[f155,f44])).
% 3.95/0.86  fof(f155,plain,(
% 3.95/0.86    ( ! [X3] : (k2_xboole_0(k3_xboole_0(X3,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X3,k1_xboole_0))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f151,f26])).
% 3.95/0.86  fof(f151,plain,(
% 3.95/0.86    ( ! [X3] : (k2_xboole_0(k3_xboole_0(X3,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k3_xboole_0(X3,k1_xboole_0),k1_xboole_0)) )),
% 3.95/0.86    inference(superposition,[],[f29,f124])).
% 3.95/0.86  fof(f124,plain,(
% 3.95/0.86    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f123,f57])).
% 3.95/0.86  fof(f123,plain,(
% 3.95/0.86    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f116,f43])).
% 3.95/0.86  fof(f116,plain,(
% 3.95/0.86    ( ! [X1] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0))) )),
% 3.95/0.86    inference(superposition,[],[f97,f38])).
% 3.95/0.86  fof(f38,plain,(
% 3.95/0.86    ( ! [X2,X1] : (k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1) )),
% 3.95/0.86    inference(superposition,[],[f28,f27])).
% 3.95/0.86  fof(f27,plain,(
% 3.95/0.86    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.95/0.86    inference(cnf_transformation,[],[f1])).
% 3.95/0.86  fof(f1,axiom,(
% 3.95/0.86    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.95/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.95/0.86  fof(f395,plain,(
% 3.95/0.86    ( ! [X8,X7] : (k3_xboole_0(k4_xboole_0(X7,X8),X7) = k4_xboole_0(k4_xboole_0(X7,X8),k1_xboole_0)) )),
% 3.95/0.86    inference(superposition,[],[f31,f366])).
% 3.95/0.86  fof(f366,plain,(
% 3.95/0.86    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5)) )),
% 3.95/0.86    inference(forward_demodulation,[],[f350,f28])).
% 3.95/0.86  fof(f350,plain,(
% 3.95/0.86    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,k3_xboole_0(X5,X6)))) )),
% 3.95/0.86    inference(superposition,[],[f300,f30])).
% 3.95/0.86  fof(f300,plain,(
% 3.95/0.86    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X6,X7),k2_xboole_0(X6,X7))) )),
% 3.95/0.86    inference(superposition,[],[f261,f32])).
% 3.95/0.86  fof(f261,plain,(
% 3.95/0.86    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f256,f178])).
% 3.95/0.86  fof(f256,plain,(
% 3.95/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1)) )),
% 3.95/0.86    inference(backward_demodulation,[],[f94,f250])).
% 3.95/0.86  fof(f250,plain,(
% 3.95/0.86    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.95/0.86    inference(backward_demodulation,[],[f43,f249])).
% 3.95/0.86  fof(f249,plain,(
% 3.95/0.86    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 3.95/0.86    inference(forward_demodulation,[],[f246,f184])).
% 3.95/0.86  fof(f246,plain,(
% 3.95/0.86    ( ! [X2] : (k3_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,X2)) )),
% 3.95/0.86    inference(superposition,[],[f31,f211])).
% 3.95/0.86  fof(f94,plain,(
% 3.95/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k5_xboole_0(X0,X0),X1)) )),
% 3.95/0.86    inference(superposition,[],[f33,f43])).
% 3.95/0.86  fof(f44,plain,(
% 3.95/0.86    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 3.95/0.86    inference(superposition,[],[f30,f27])).
% 3.95/0.86  fof(f13693,plain,(
% 3.95/0.86    ( ! [X12,X13] : (k5_xboole_0(X12,k4_xboole_0(X12,X13)) = k3_xboole_0(X12,k4_xboole_0(X13,k5_xboole_0(X12,X13)))) )),
% 3.95/0.86    inference(backward_demodulation,[],[f1332,f13555])).
% 3.95/0.86  fof(f13555,plain,(
% 3.95/0.86    ( ! [X39,X38] : (k4_xboole_0(X39,X38) = k5_xboole_0(X38,k2_xboole_0(X39,X38))) )),
% 3.95/0.86    inference(superposition,[],[f737,f13428])).
% 3.95/0.86  fof(f13428,plain,(
% 3.95/0.86    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(X4,X3)) )),
% 3.95/0.86    inference(superposition,[],[f13368,f201])).
% 3.95/0.86  fof(f13368,plain,(
% 3.95/0.86    ( ! [X39,X40] : (k5_xboole_0(k2_xboole_0(X40,X39),k1_xboole_0) = k2_xboole_0(X39,X40)) )),
% 3.95/0.86    inference(forward_demodulation,[],[f13279,f13361])).
% 3.95/0.86  fof(f13361,plain,(
% 3.95/0.86    ( ! [X15,X16] : (k2_xboole_0(X15,X16) = k3_xboole_0(k2_xboole_0(X15,X16),k2_xboole_0(X16,X15))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f13268,f211])).
% 3.95/0.86  fof(f13268,plain,(
% 3.95/0.86    ( ! [X15,X16] : (k3_xboole_0(k2_xboole_0(X15,X16),k2_xboole_0(X16,X15)) = k4_xboole_0(k2_xboole_0(X15,X16),k1_xboole_0)) )),
% 3.95/0.86    inference(superposition,[],[f31,f13180])).
% 3.95/0.86  fof(f13180,plain,(
% 3.95/0.86    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X4,X3))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f13179,f29])).
% 3.95/0.86  fof(f13179,plain,(
% 3.95/0.86    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),k2_xboole_0(X4,X3))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f13178,f26])).
% 3.95/0.86  fof(f13178,plain,(
% 3.95/0.86    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X4,X3),X3),k2_xboole_0(X4,X3))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f13177,f701])).
% 3.95/0.86  fof(f701,plain,(
% 3.95/0.86    ( ! [X10,X8,X9] : (k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X10)) = k5_xboole_0(k4_xboole_0(X8,X9),X10)) )),
% 3.95/0.86    inference(superposition,[],[f34,f30])).
% 3.95/0.86  fof(f34,plain,(
% 3.95/0.86    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 3.95/0.86    inference(cnf_transformation,[],[f12])).
% 3.95/0.86  fof(f12,axiom,(
% 3.95/0.86    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 3.95/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 3.95/0.86  fof(f13177,plain,(
% 3.95/0.86    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X3),X3)),k2_xboole_0(X4,X3))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f13176,f709])).
% 3.95/0.86  fof(f709,plain,(
% 3.95/0.86    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))) )),
% 3.95/0.86    inference(superposition,[],[f34,f26])).
% 3.95/0.86  fof(f13176,plain,(
% 3.95/0.86    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(k3_xboole_0(X4,X3),k5_xboole_0(X3,X4)),k2_xboole_0(X4,X3))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f12992,f26])).
% 3.95/0.86  fof(f12992,plain,(
% 3.95/0.86    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(k5_xboole_0(X3,X4),k3_xboole_0(X4,X3)),k2_xboole_0(X4,X3))) )),
% 3.95/0.86    inference(superposition,[],[f300,f78])).
% 3.95/0.86  fof(f78,plain,(
% 3.95/0.86    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(X0,X1))) )),
% 3.95/0.86    inference(superposition,[],[f32,f26])).
% 3.95/0.86  fof(f13279,plain,(
% 3.95/0.86    ( ! [X39,X40] : (k2_xboole_0(X39,X40) = k5_xboole_0(k3_xboole_0(k2_xboole_0(X40,X39),k2_xboole_0(X39,X40)),k1_xboole_0)) )),
% 3.95/0.86    inference(superposition,[],[f762,f13180])).
% 3.95/0.86  fof(f762,plain,(
% 3.95/0.86    ( ! [X8,X7] : (k5_xboole_0(k3_xboole_0(X8,X7),k4_xboole_0(X7,X8)) = X7) )),
% 3.95/0.86    inference(superposition,[],[f733,f44])).
% 3.95/0.86  fof(f733,plain,(
% 3.95/0.86    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 3.95/0.86    inference(superposition,[],[f725,f26])).
% 3.95/0.86  fof(f725,plain,(
% 3.95/0.86    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 3.95/0.86    inference(forward_demodulation,[],[f698,f230])).
% 3.95/0.86  fof(f230,plain,(
% 3.95/0.86    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 3.95/0.86    inference(superposition,[],[f201,f26])).
% 3.95/0.86  fof(f698,plain,(
% 3.95/0.86    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 3.95/0.86    inference(superposition,[],[f34,f250])).
% 3.95/0.86  fof(f737,plain,(
% 3.95/0.86    ( ! [X12,X11] : (k4_xboole_0(X12,X11) = k5_xboole_0(X11,k2_xboole_0(X11,X12))) )),
% 3.95/0.86    inference(superposition,[],[f725,f29])).
% 3.95/0.86  fof(f1332,plain,(
% 3.95/0.86    ( ! [X12,X13] : (k5_xboole_0(X12,k5_xboole_0(X13,k2_xboole_0(X12,X13))) = k3_xboole_0(X12,k4_xboole_0(X13,k5_xboole_0(X12,X13)))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f1331,f35])).
% 3.95/0.86  fof(f35,plain,(
% 3.95/0.86    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.95/0.86    inference(cnf_transformation,[],[f11])).
% 3.95/0.86  fof(f11,axiom,(
% 3.95/0.86    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.95/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 3.95/0.86  fof(f1331,plain,(
% 3.95/0.86    ( ! [X12,X13] : (k4_xboole_0(k3_xboole_0(X12,X13),k5_xboole_0(X12,X13)) = k5_xboole_0(X12,k5_xboole_0(X13,k2_xboole_0(X12,X13)))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f1305,f34])).
% 3.95/0.86  fof(f1305,plain,(
% 3.95/0.86    ( ! [X12,X13] : (k4_xboole_0(k3_xboole_0(X12,X13),k5_xboole_0(X12,X13)) = k5_xboole_0(k5_xboole_0(X12,X13),k2_xboole_0(X12,X13))) )),
% 3.95/0.86    inference(superposition,[],[f737,f32])).
% 3.95/0.86  fof(f3401,plain,(
% 3.95/0.86    ( ! [X17,X16] : (k5_xboole_0(X16,X17) = k4_xboole_0(k2_xboole_0(X16,X17),k3_xboole_0(X16,k4_xboole_0(X17,k5_xboole_0(X16,X17))))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f3340,f35])).
% 3.95/0.86  fof(f3340,plain,(
% 3.95/0.86    ( ! [X17,X16] : (k5_xboole_0(X16,X17) = k4_xboole_0(k2_xboole_0(X16,X17),k4_xboole_0(k3_xboole_0(X16,X17),k5_xboole_0(X16,X17)))) )),
% 3.95/0.86    inference(superposition,[],[f1579,f32])).
% 3.95/0.86  fof(f1579,plain,(
% 3.95/0.86    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = X2) )),
% 3.95/0.86    inference(forward_demodulation,[],[f1578,f308])).
% 3.95/0.86  fof(f308,plain,(
% 3.95/0.86    ( ! [X4,X3] : (k3_xboole_0(X3,k2_xboole_0(X3,X4)) = X3) )),
% 3.95/0.86    inference(forward_demodulation,[],[f304,f211])).
% 3.95/0.86  fof(f304,plain,(
% 3.95/0.86    ( ! [X4,X3] : (k4_xboole_0(X3,k1_xboole_0) = k3_xboole_0(X3,k2_xboole_0(X3,X4))) )),
% 3.95/0.86    inference(superposition,[],[f31,f261])).
% 3.95/0.86  fof(f1578,plain,(
% 3.95/0.86    ( ! [X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f1554,f27])).
% 3.95/0.86  fof(f1554,plain,(
% 3.95/0.86    ( ! [X2,X3] : (k3_xboole_0(k2_xboole_0(X2,X3),X2) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2))) )),
% 3.95/0.86    inference(superposition,[],[f31,f752])).
% 3.95/0.86  fof(f752,plain,(
% 3.95/0.86    ( ! [X12,X13] : (k4_xboole_0(k2_xboole_0(X12,X13),X12) = k4_xboole_0(X13,X12)) )),
% 3.95/0.86    inference(backward_demodulation,[],[f323,f737])).
% 3.95/0.86  fof(f323,plain,(
% 3.95/0.86    ( ! [X12,X13] : (k4_xboole_0(k2_xboole_0(X12,X13),X12) = k5_xboole_0(X12,k2_xboole_0(X12,X13))) )),
% 3.95/0.86    inference(forward_demodulation,[],[f321,f26])).
% 3.95/0.86  fof(f321,plain,(
% 3.95/0.86    ( ! [X12,X13] : (k4_xboole_0(k2_xboole_0(X12,X13),X12) = k5_xboole_0(k2_xboole_0(X12,X13),X12)) )),
% 3.95/0.86    inference(superposition,[],[f44,f308])).
% 3.95/0.86  fof(f22,plain,(
% 3.95/0.86    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 3.95/0.86    inference(cnf_transformation,[],[f21])).
% 3.95/0.86  fof(f21,plain,(
% 3.95/0.86    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 3.95/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 3.95/0.86  fof(f20,plain,(
% 3.95/0.86    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 3.95/0.86    introduced(choice_axiom,[])).
% 3.95/0.86  fof(f19,plain,(
% 3.95/0.86    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.95/0.86    inference(ennf_transformation,[],[f16])).
% 3.95/0.86  fof(f16,negated_conjecture,(
% 3.95/0.86    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.95/0.86    inference(negated_conjecture,[],[f15])).
% 3.95/0.86  fof(f15,conjecture,(
% 3.95/0.86    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.95/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 3.95/0.86  % SZS output end Proof for theBenchmark
% 3.95/0.86  % (20050)------------------------------
% 3.95/0.86  % (20050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.95/0.86  % (20050)Termination reason: Refutation
% 3.95/0.86  
% 3.95/0.86  % (20050)Memory used [KB]: 14200
% 3.95/0.86  % (20050)Time elapsed: 0.433 s
% 3.95/0.86  % (20050)------------------------------
% 3.95/0.86  % (20050)------------------------------
% 3.95/0.86  % (20033)Success in time 0.501 s
%------------------------------------------------------------------------------
