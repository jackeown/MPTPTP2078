%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:51 EST 2020

% Result     : Theorem 5.80s
% Output     : Refutation 5.80s
% Verified   : 
% Statistics : Number of formulae       :  109 (1953 expanded)
%              Number of leaves         :   16 ( 658 expanded)
%              Depth                    :   33
%              Number of atoms          :  110 (1954 expanded)
%              Number of equality atoms :  109 (1953 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14961,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f14960])).

fof(f14960,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f14600,f12795])).

fof(f12795,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k5_xboole_0(X6,k4_xboole_0(X7,X6)) ),
    inference(forward_demodulation,[],[f12794,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f12794,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k4_xboole_0(X7,X6)) = k5_xboole_0(X6,k4_xboole_0(X7,X6)) ),
    inference(forward_demodulation,[],[f12793,f7212])).

fof(f7212,plain,(
    ! [X8,X7] : k2_xboole_0(X8,X7) = k2_xboole_0(k5_xboole_0(X8,X7),X8) ),
    inference(forward_demodulation,[],[f7149,f6195])).

fof(f6195,plain,(
    ! [X8,X7] : k2_xboole_0(X8,X7) = k2_xboole_0(X7,k5_xboole_0(X8,X7)) ),
    inference(backward_demodulation,[],[f626,f6194])).

fof(f6194,plain,(
    ! [X24,X23,X25] : k2_xboole_0(X24,X25) = k2_xboole_0(X24,k4_xboole_0(X25,k4_xboole_0(X23,k5_xboole_0(X24,X23)))) ),
    inference(forward_demodulation,[],[f6160,f33])).

fof(f6160,plain,(
    ! [X24,X23,X25] : k2_xboole_0(X24,k4_xboole_0(X25,k4_xboole_0(X23,k5_xboole_0(X24,X23)))) = k2_xboole_0(X24,k4_xboole_0(X25,X24)) ),
    inference(superposition,[],[f205,f4494])).

fof(f4494,plain,(
    ! [X21,X22] : k2_xboole_0(k4_xboole_0(X22,k5_xboole_0(X21,X22)),X21) = X21 ),
    inference(superposition,[],[f122,f3767])).

fof(f3767,plain,(
    ! [X19,X20] : k2_xboole_0(X19,k4_xboole_0(X20,k5_xboole_0(X19,X20))) = X19 ),
    inference(superposition,[],[f3637,f340])).

fof(f340,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f322,f322])).

fof(f322,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f318,f30])).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f318,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f303,f44])).

fof(f44,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f30,f25])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f303,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f37,f23])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f3637,plain,(
    ! [X33,X32] : k2_xboole_0(X33,k4_xboole_0(k5_xboole_0(X32,X33),X32)) = X33 ),
    inference(forward_demodulation,[],[f3567,f26])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f3567,plain,(
    ! [X33,X32] : k2_xboole_0(X33,k1_xboole_0) = k2_xboole_0(X33,k4_xboole_0(k5_xboole_0(X32,X33),X32)) ),
    inference(superposition,[],[f205,f651])).

fof(f651,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f28,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f122,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(X4,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f76,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f76,plain,(
    ! [X4,X3] : k2_xboole_0(X4,X3) = k2_xboole_0(k2_xboole_0(X4,X3),X3) ),
    inference(forward_demodulation,[],[f69,f26])).

fof(f69,plain,(
    ! [X4,X3] : k2_xboole_0(k2_xboole_0(X4,X3),X3) = k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0) ),
    inference(superposition,[],[f33,f55])).

fof(f55,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f28,f31])).

fof(f205,plain,(
    ! [X14,X12,X13] : k2_xboole_0(X14,k4_xboole_0(X12,X13)) = k2_xboole_0(X14,k4_xboole_0(X12,k2_xboole_0(X13,X14))) ),
    inference(superposition,[],[f33,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f626,plain,(
    ! [X8,X7] : k2_xboole_0(X7,k5_xboole_0(X8,X7)) = k2_xboole_0(X8,k4_xboole_0(X7,k4_xboole_0(X7,k5_xboole_0(X8,X7)))) ),
    inference(superposition,[],[f41,f322])).

fof(f7149,plain,(
    ! [X8,X7] : k2_xboole_0(X7,k5_xboole_0(X8,X7)) = k2_xboole_0(k5_xboole_0(X8,X7),X8) ),
    inference(superposition,[],[f6195,f322])).

fof(f12793,plain,(
    ! [X6,X7] : k5_xboole_0(X6,k4_xboole_0(X7,X6)) = k2_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6) ),
    inference(forward_demodulation,[],[f12713,f26])).

fof(f12713,plain,(
    ! [X6,X7] : k2_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6) = k2_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),k1_xboole_0) ),
    inference(superposition,[],[f33,f8910])).

fof(f8910,plain,(
    ! [X103,X104] : k1_xboole_0 = k4_xboole_0(X103,k5_xboole_0(X103,k4_xboole_0(X104,X103))) ),
    inference(forward_demodulation,[],[f8840,f30])).

fof(f8840,plain,(
    ! [X103,X104] : k1_xboole_0 = k4_xboole_0(X103,k5_xboole_0(k4_xboole_0(X104,X103),X103)) ),
    inference(superposition,[],[f4286,f8699])).

fof(f8699,plain,(
    ! [X6,X7] : k4_xboole_0(X7,k4_xboole_0(X6,X7)) = X7 ),
    inference(forward_demodulation,[],[f8698,f24])).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f8698,plain,(
    ! [X6,X7] : k4_xboole_0(X7,k1_xboole_0) = k4_xboole_0(X7,k4_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f8697,f55])).

fof(f8697,plain,(
    ! [X6,X7] : k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(X6,X7))) = k4_xboole_0(X7,k4_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f8537,f8501])).

fof(f8501,plain,(
    ! [X21,X20] : k4_xboole_0(X20,k4_xboole_0(X21,X20)) = k4_xboole_0(k2_xboole_0(X21,X20),k4_xboole_0(X21,X20)) ),
    inference(superposition,[],[f6512,f6514])).

fof(f6514,plain,(
    ! [X4,X3] : k2_xboole_0(X4,X3) = k2_xboole_0(X3,k4_xboole_0(X4,X3)) ),
    inference(backward_demodulation,[],[f2370,f6512])).

fof(f2370,plain,(
    ! [X4,X3] : k2_xboole_0(X4,X3) = k2_xboole_0(X3,k4_xboole_0(k2_xboole_0(X4,X3),X3)) ),
    inference(forward_demodulation,[],[f2293,f24])).

fof(f2293,plain,(
    ! [X4,X3] : k2_xboole_0(X4,X3) = k2_xboole_0(k4_xboole_0(X3,k1_xboole_0),k4_xboole_0(k2_xboole_0(X4,X3),X3)) ),
    inference(superposition,[],[f469,f55])).

fof(f469,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f29,f32,f32])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f34,f32])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f6512,plain,(
    ! [X17,X16] : k4_xboole_0(X16,X17) = k4_xboole_0(k2_xboole_0(X16,X17),X17) ),
    inference(forward_demodulation,[],[f6511,f52])).

fof(f52,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f31,f26])).

fof(f6511,plain,(
    ! [X17,X16] : k4_xboole_0(k2_xboole_0(X16,X17),X17) = k4_xboole_0(X16,k2_xboole_0(k1_xboole_0,X17)) ),
    inference(forward_demodulation,[],[f6510,f36])).

fof(f6510,plain,(
    ! [X17,X16] : k4_xboole_0(k2_xboole_0(X16,X17),X17) = k4_xboole_0(k4_xboole_0(X16,k1_xboole_0),X17) ),
    inference(forward_demodulation,[],[f6237,f28])).

fof(f6237,plain,(
    ! [X17,X16] : k4_xboole_0(k2_xboole_0(X16,X17),X17) = k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,k2_xboole_0(X16,X17))),X17) ),
    inference(superposition,[],[f435,f3712])).

fof(f3712,plain,(
    ! [X24,X23] : k2_xboole_0(k4_xboole_0(k2_xboole_0(X24,X23),X24),X23) = X23 ),
    inference(superposition,[],[f122,f3636])).

fof(f3636,plain,(
    ! [X30,X31] : k2_xboole_0(X31,k4_xboole_0(k2_xboole_0(X30,X31),X30)) = X31 ),
    inference(forward_demodulation,[],[f3566,f26])).

fof(f3566,plain,(
    ! [X30,X31] : k2_xboole_0(X31,k4_xboole_0(k2_xboole_0(X30,X31),X30)) = k2_xboole_0(X31,k1_xboole_0) ),
    inference(superposition,[],[f205,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f28,f26])).

fof(f435,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[],[f36,f39])).

fof(f8537,plain,(
    ! [X6,X7] : k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(X6,X7))) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f39,f6512])).

fof(f4286,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X6,X5),k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f3784,f318])).

fof(f3784,plain,(
    ! [X12,X11] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X12,X11),X12),X11) ),
    inference(superposition,[],[f55,f3637])).

fof(f14600,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f14599,f14026])).

fof(f14026,plain,(
    ! [X2,X1] : k4_xboole_0(X2,X1) = k5_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f13818,f31])).

fof(f13818,plain,(
    ! [X21,X22] : k4_xboole_0(X22,X21) = k5_xboole_0(X21,k2_xboole_0(X21,X22)) ),
    inference(superposition,[],[f318,f12795])).

fof(f14599,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK0,k2_xboole_0(sK1,sK0))) ),
    inference(forward_demodulation,[],[f14598,f12795])).

fof(f14598,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f14597,f30])).

fof(f14597,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK0,sK1),sK1))) ),
    inference(forward_demodulation,[],[f14523,f311])).

fof(f311,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8)) ),
    inference(superposition,[],[f37,f30])).

fof(f14523,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    inference(backward_demodulation,[],[f313,f14178])).

fof(f14178,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k4_xboole_0(X5,X6)) = k5_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(backward_demodulation,[],[f1504,f14174])).

fof(f14174,plain,(
    ! [X54,X53] : k4_xboole_0(X53,X54) = k4_xboole_0(X53,k5_xboole_0(X53,k4_xboole_0(X53,X54))) ),
    inference(forward_demodulation,[],[f14173,f318])).

fof(f14173,plain,(
    ! [X54,X53] : k4_xboole_0(X53,k5_xboole_0(X53,k4_xboole_0(X53,X54))) = k5_xboole_0(X53,k5_xboole_0(X53,k4_xboole_0(X53,X54))) ),
    inference(forward_demodulation,[],[f14052,f30])).

fof(f14052,plain,(
    ! [X54,X53] : k4_xboole_0(X53,k5_xboole_0(X53,k4_xboole_0(X53,X54))) = k5_xboole_0(k5_xboole_0(X53,k4_xboole_0(X53,X54)),X53) ),
    inference(superposition,[],[f13818,f1588])).

fof(f1588,plain,(
    ! [X33,X34] : k2_xboole_0(k5_xboole_0(X33,k4_xboole_0(X33,X34)),X33) = X33 ),
    inference(forward_demodulation,[],[f1530,f24])).

fof(f1530,plain,(
    ! [X33,X34] : k2_xboole_0(k4_xboole_0(k5_xboole_0(X33,k4_xboole_0(X33,X34)),k1_xboole_0),X33) = X33 ),
    inference(superposition,[],[f594,f764])).

fof(f764,plain,(
    ! [X12,X13] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(X12,X13)),X12) ),
    inference(superposition,[],[f651,f495])).

fof(f495,plain,(
    ! [X12,X13] : k2_xboole_0(X12,k4_xboole_0(X12,X13)) = X12 ),
    inference(superposition,[],[f76,f40])).

fof(f594,plain,(
    ! [X19,X18] : k2_xboole_0(k4_xboole_0(X19,k4_xboole_0(X19,X18)),X18) = X18 ),
    inference(superposition,[],[f498,f39])).

fof(f498,plain,(
    ! [X19,X18] : k2_xboole_0(k4_xboole_0(X18,X19),X18) = X18 ),
    inference(superposition,[],[f122,f40])).

fof(f1504,plain,(
    ! [X6,X5] : k5_xboole_0(X5,k4_xboole_0(X5,X6)) = k4_xboole_0(X5,k4_xboole_0(X5,k5_xboole_0(X5,k4_xboole_0(X5,X6)))) ),
    inference(forward_demodulation,[],[f1461,f24])).

fof(f1461,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k4_xboole_0(X5,k5_xboole_0(X5,k4_xboole_0(X5,X6)))) = k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X5,X6)),k1_xboole_0) ),
    inference(superposition,[],[f39,f764])).

fof(f313,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f38,f37])).

fof(f38,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f22,f32])).

fof(f22,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.40  % (12289)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.45  % (12280)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.45  % (12293)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.45  % (12281)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.45  % (12291)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (12290)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (12285)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.46  % (12290)Refutation not found, incomplete strategy% (12290)------------------------------
% 0.20/0.46  % (12290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (12290)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (12290)Memory used [KB]: 10618
% 0.20/0.46  % (12290)Time elapsed: 0.044 s
% 0.20/0.46  % (12290)------------------------------
% 0.20/0.46  % (12290)------------------------------
% 0.20/0.46  % (12282)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (12294)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (12292)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (12284)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (12287)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (12279)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (12295)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.49  % (12288)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (12296)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.51  % (12286)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.51  % (12283)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 5.13/1.01  % (12283)Time limit reached!
% 5.13/1.01  % (12283)------------------------------
% 5.13/1.01  % (12283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.13/1.01  % (12283)Termination reason: Time limit
% 5.13/1.01  
% 5.13/1.01  % (12283)Memory used [KB]: 15863
% 5.13/1.01  % (12283)Time elapsed: 0.613 s
% 5.13/1.01  % (12283)------------------------------
% 5.13/1.01  % (12283)------------------------------
% 5.80/1.10  % (12280)Refutation found. Thanks to Tanya!
% 5.80/1.10  % SZS status Theorem for theBenchmark
% 5.80/1.10  % SZS output start Proof for theBenchmark
% 5.80/1.12  fof(f14961,plain,(
% 5.80/1.12    $false),
% 5.80/1.12    inference(trivial_inequality_removal,[],[f14960])).
% 5.80/1.12  fof(f14960,plain,(
% 5.80/1.12    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1)),
% 5.80/1.12    inference(superposition,[],[f14600,f12795])).
% 5.80/1.12  fof(f12795,plain,(
% 5.80/1.12    ( ! [X6,X7] : (k2_xboole_0(X6,X7) = k5_xboole_0(X6,k4_xboole_0(X7,X6))) )),
% 5.80/1.12    inference(forward_demodulation,[],[f12794,f33])).
% 5.80/1.12  fof(f33,plain,(
% 5.80/1.12    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 5.80/1.12    inference(cnf_transformation,[],[f6])).
% 5.80/1.12  fof(f6,axiom,(
% 5.80/1.12    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 5.80/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 5.80/1.12  fof(f12794,plain,(
% 5.80/1.12    ( ! [X6,X7] : (k2_xboole_0(X6,k4_xboole_0(X7,X6)) = k5_xboole_0(X6,k4_xboole_0(X7,X6))) )),
% 5.80/1.12    inference(forward_demodulation,[],[f12793,f7212])).
% 5.80/1.12  fof(f7212,plain,(
% 5.80/1.12    ( ! [X8,X7] : (k2_xboole_0(X8,X7) = k2_xboole_0(k5_xboole_0(X8,X7),X8)) )),
% 5.80/1.12    inference(forward_demodulation,[],[f7149,f6195])).
% 5.80/1.12  fof(f6195,plain,(
% 5.80/1.12    ( ! [X8,X7] : (k2_xboole_0(X8,X7) = k2_xboole_0(X7,k5_xboole_0(X8,X7))) )),
% 5.80/1.12    inference(backward_demodulation,[],[f626,f6194])).
% 5.80/1.12  fof(f6194,plain,(
% 5.80/1.12    ( ! [X24,X23,X25] : (k2_xboole_0(X24,X25) = k2_xboole_0(X24,k4_xboole_0(X25,k4_xboole_0(X23,k5_xboole_0(X24,X23))))) )),
% 5.80/1.12    inference(forward_demodulation,[],[f6160,f33])).
% 5.80/1.12  fof(f6160,plain,(
% 5.80/1.12    ( ! [X24,X23,X25] : (k2_xboole_0(X24,k4_xboole_0(X25,k4_xboole_0(X23,k5_xboole_0(X24,X23)))) = k2_xboole_0(X24,k4_xboole_0(X25,X24))) )),
% 5.80/1.12    inference(superposition,[],[f205,f4494])).
% 5.80/1.12  fof(f4494,plain,(
% 5.80/1.12    ( ! [X21,X22] : (k2_xboole_0(k4_xboole_0(X22,k5_xboole_0(X21,X22)),X21) = X21) )),
% 5.80/1.12    inference(superposition,[],[f122,f3767])).
% 5.80/1.12  fof(f3767,plain,(
% 5.80/1.12    ( ! [X19,X20] : (k2_xboole_0(X19,k4_xboole_0(X20,k5_xboole_0(X19,X20))) = X19) )),
% 5.80/1.12    inference(superposition,[],[f3637,f340])).
% 5.80/1.12  fof(f340,plain,(
% 5.80/1.12    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 5.80/1.12    inference(superposition,[],[f322,f322])).
% 5.80/1.12  fof(f322,plain,(
% 5.80/1.12    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 5.80/1.12    inference(superposition,[],[f318,f30])).
% 5.80/1.12  fof(f30,plain,(
% 5.80/1.12    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 5.80/1.12    inference(cnf_transformation,[],[f3])).
% 5.80/1.12  fof(f3,axiom,(
% 5.80/1.12    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 5.80/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 5.80/1.12  fof(f318,plain,(
% 5.80/1.12    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 5.80/1.12    inference(forward_demodulation,[],[f303,f44])).
% 5.80/1.12  fof(f44,plain,(
% 5.80/1.12    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 5.80/1.12    inference(superposition,[],[f30,f25])).
% 5.80/1.12  fof(f25,plain,(
% 5.80/1.12    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.80/1.12    inference(cnf_transformation,[],[f12])).
% 5.80/1.12  fof(f12,axiom,(
% 5.80/1.12    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 5.80/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 5.80/1.12  fof(f303,plain,(
% 5.80/1.12    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 5.80/1.12    inference(superposition,[],[f37,f23])).
% 5.80/1.12  fof(f23,plain,(
% 5.80/1.12    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 5.80/1.12    inference(cnf_transformation,[],[f14])).
% 5.80/1.12  fof(f14,axiom,(
% 5.80/1.12    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 5.80/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 5.80/1.12  fof(f37,plain,(
% 5.80/1.12    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 5.80/1.12    inference(cnf_transformation,[],[f13])).
% 5.80/1.12  fof(f13,axiom,(
% 5.80/1.12    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 5.80/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 5.80/1.12  fof(f3637,plain,(
% 5.80/1.12    ( ! [X33,X32] : (k2_xboole_0(X33,k4_xboole_0(k5_xboole_0(X32,X33),X32)) = X33) )),
% 5.80/1.12    inference(forward_demodulation,[],[f3567,f26])).
% 5.80/1.12  fof(f26,plain,(
% 5.80/1.12    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.80/1.12    inference(cnf_transformation,[],[f5])).
% 5.80/1.12  fof(f5,axiom,(
% 5.80/1.12    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 5.80/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 5.80/1.12  fof(f3567,plain,(
% 5.80/1.12    ( ! [X33,X32] : (k2_xboole_0(X33,k1_xboole_0) = k2_xboole_0(X33,k4_xboole_0(k5_xboole_0(X32,X33),X32))) )),
% 5.80/1.12    inference(superposition,[],[f205,f651])).
% 5.80/1.12  fof(f651,plain,(
% 5.80/1.12    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 5.80/1.12    inference(superposition,[],[f28,f41])).
% 5.80/1.12  fof(f41,plain,(
% 5.80/1.12    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 5.80/1.12    inference(definition_unfolding,[],[f35,f32])).
% 5.80/1.12  fof(f32,plain,(
% 5.80/1.12    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 5.80/1.12    inference(cnf_transformation,[],[f10])).
% 5.80/1.12  fof(f10,axiom,(
% 5.80/1.12    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.80/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.80/1.12  fof(f35,plain,(
% 5.80/1.12    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 5.80/1.12    inference(cnf_transformation,[],[f15])).
% 5.80/1.12  fof(f15,axiom,(
% 5.80/1.12    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.80/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 5.80/1.12  fof(f28,plain,(
% 5.80/1.12    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 5.80/1.12    inference(cnf_transformation,[],[f9])).
% 5.80/1.12  fof(f9,axiom,(
% 5.80/1.12    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 5.80/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 5.80/1.12  fof(f122,plain,(
% 5.80/1.12    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(X4,k2_xboole_0(X3,X4))) )),
% 5.80/1.12    inference(superposition,[],[f76,f31])).
% 5.80/1.12  fof(f31,plain,(
% 5.80/1.12    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 5.80/1.12    inference(cnf_transformation,[],[f1])).
% 5.80/1.12  fof(f1,axiom,(
% 5.80/1.12    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 5.80/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 5.80/1.12  fof(f76,plain,(
% 5.80/1.12    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k2_xboole_0(k2_xboole_0(X4,X3),X3)) )),
% 5.80/1.12    inference(forward_demodulation,[],[f69,f26])).
% 5.80/1.12  fof(f69,plain,(
% 5.80/1.12    ( ! [X4,X3] : (k2_xboole_0(k2_xboole_0(X4,X3),X3) = k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0)) )),
% 5.80/1.12    inference(superposition,[],[f33,f55])).
% 5.80/1.12  fof(f55,plain,(
% 5.80/1.12    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))) )),
% 5.80/1.12    inference(superposition,[],[f28,f31])).
% 5.80/1.12  fof(f205,plain,(
% 5.80/1.12    ( ! [X14,X12,X13] : (k2_xboole_0(X14,k4_xboole_0(X12,X13)) = k2_xboole_0(X14,k4_xboole_0(X12,k2_xboole_0(X13,X14)))) )),
% 5.80/1.12    inference(superposition,[],[f33,f36])).
% 5.80/1.12  fof(f36,plain,(
% 5.80/1.12    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 5.80/1.12    inference(cnf_transformation,[],[f8])).
% 5.80/1.12  fof(f8,axiom,(
% 5.80/1.12    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 5.80/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 5.80/1.12  fof(f626,plain,(
% 5.80/1.12    ( ! [X8,X7] : (k2_xboole_0(X7,k5_xboole_0(X8,X7)) = k2_xboole_0(X8,k4_xboole_0(X7,k4_xboole_0(X7,k5_xboole_0(X8,X7))))) )),
% 5.80/1.12    inference(superposition,[],[f41,f322])).
% 5.80/1.12  fof(f7149,plain,(
% 5.80/1.12    ( ! [X8,X7] : (k2_xboole_0(X7,k5_xboole_0(X8,X7)) = k2_xboole_0(k5_xboole_0(X8,X7),X8)) )),
% 5.80/1.12    inference(superposition,[],[f6195,f322])).
% 5.80/1.12  fof(f12793,plain,(
% 5.80/1.12    ( ! [X6,X7] : (k5_xboole_0(X6,k4_xboole_0(X7,X6)) = k2_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6)) )),
% 5.80/1.12    inference(forward_demodulation,[],[f12713,f26])).
% 5.80/1.12  fof(f12713,plain,(
% 5.80/1.12    ( ! [X6,X7] : (k2_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6) = k2_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),k1_xboole_0)) )),
% 5.80/1.12    inference(superposition,[],[f33,f8910])).
% 5.80/1.12  fof(f8910,plain,(
% 5.80/1.12    ( ! [X103,X104] : (k1_xboole_0 = k4_xboole_0(X103,k5_xboole_0(X103,k4_xboole_0(X104,X103)))) )),
% 5.80/1.12    inference(forward_demodulation,[],[f8840,f30])).
% 5.80/1.12  fof(f8840,plain,(
% 5.80/1.12    ( ! [X103,X104] : (k1_xboole_0 = k4_xboole_0(X103,k5_xboole_0(k4_xboole_0(X104,X103),X103))) )),
% 5.80/1.12    inference(superposition,[],[f4286,f8699])).
% 5.80/1.12  fof(f8699,plain,(
% 5.80/1.12    ( ! [X6,X7] : (k4_xboole_0(X7,k4_xboole_0(X6,X7)) = X7) )),
% 5.80/1.12    inference(forward_demodulation,[],[f8698,f24])).
% 5.80/1.12  fof(f24,plain,(
% 5.80/1.12    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.80/1.12    inference(cnf_transformation,[],[f7])).
% 5.80/1.12  fof(f7,axiom,(
% 5.80/1.12    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 5.80/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 5.80/1.12  fof(f8698,plain,(
% 5.80/1.12    ( ! [X6,X7] : (k4_xboole_0(X7,k1_xboole_0) = k4_xboole_0(X7,k4_xboole_0(X6,X7))) )),
% 5.80/1.12    inference(forward_demodulation,[],[f8697,f55])).
% 5.80/1.12  fof(f8697,plain,(
% 5.80/1.12    ( ! [X6,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(X6,X7))) = k4_xboole_0(X7,k4_xboole_0(X6,X7))) )),
% 5.80/1.12    inference(forward_demodulation,[],[f8537,f8501])).
% 5.80/1.12  fof(f8501,plain,(
% 5.80/1.12    ( ! [X21,X20] : (k4_xboole_0(X20,k4_xboole_0(X21,X20)) = k4_xboole_0(k2_xboole_0(X21,X20),k4_xboole_0(X21,X20))) )),
% 5.80/1.12    inference(superposition,[],[f6512,f6514])).
% 5.80/1.12  fof(f6514,plain,(
% 5.80/1.12    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k2_xboole_0(X3,k4_xboole_0(X4,X3))) )),
% 5.80/1.12    inference(backward_demodulation,[],[f2370,f6512])).
% 5.80/1.12  fof(f2370,plain,(
% 5.80/1.12    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k2_xboole_0(X3,k4_xboole_0(k2_xboole_0(X4,X3),X3))) )),
% 5.80/1.12    inference(forward_demodulation,[],[f2293,f24])).
% 5.80/1.12  fof(f2293,plain,(
% 5.80/1.12    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k2_xboole_0(k4_xboole_0(X3,k1_xboole_0),k4_xboole_0(k2_xboole_0(X4,X3),X3))) )),
% 5.80/1.12    inference(superposition,[],[f469,f55])).
% 5.80/1.12  fof(f469,plain,(
% 5.80/1.12    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0) )),
% 5.80/1.12    inference(superposition,[],[f40,f39])).
% 5.80/1.12  fof(f39,plain,(
% 5.80/1.12    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 5.80/1.12    inference(definition_unfolding,[],[f29,f32,f32])).
% 5.80/1.12  fof(f29,plain,(
% 5.80/1.12    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.80/1.12    inference(cnf_transformation,[],[f2])).
% 5.80/1.12  fof(f2,axiom,(
% 5.80/1.12    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.80/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.80/1.12  fof(f40,plain,(
% 5.80/1.12    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 5.80/1.12    inference(definition_unfolding,[],[f34,f32])).
% 5.80/1.12  fof(f34,plain,(
% 5.80/1.12    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 5.80/1.12    inference(cnf_transformation,[],[f11])).
% 5.80/1.12  fof(f11,axiom,(
% 5.80/1.12    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 5.80/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 5.80/1.12  fof(f6512,plain,(
% 5.80/1.12    ( ! [X17,X16] : (k4_xboole_0(X16,X17) = k4_xboole_0(k2_xboole_0(X16,X17),X17)) )),
% 5.80/1.12    inference(forward_demodulation,[],[f6511,f52])).
% 5.80/1.12  fof(f52,plain,(
% 5.80/1.12    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 5.80/1.12    inference(superposition,[],[f31,f26])).
% 5.80/1.12  fof(f6511,plain,(
% 5.80/1.12    ( ! [X17,X16] : (k4_xboole_0(k2_xboole_0(X16,X17),X17) = k4_xboole_0(X16,k2_xboole_0(k1_xboole_0,X17))) )),
% 5.80/1.12    inference(forward_demodulation,[],[f6510,f36])).
% 5.80/1.12  fof(f6510,plain,(
% 5.80/1.12    ( ! [X17,X16] : (k4_xboole_0(k2_xboole_0(X16,X17),X17) = k4_xboole_0(k4_xboole_0(X16,k1_xboole_0),X17)) )),
% 5.80/1.12    inference(forward_demodulation,[],[f6237,f28])).
% 5.80/1.12  fof(f6237,plain,(
% 5.80/1.12    ( ! [X17,X16] : (k4_xboole_0(k2_xboole_0(X16,X17),X17) = k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,k2_xboole_0(X16,X17))),X17)) )),
% 5.80/1.12    inference(superposition,[],[f435,f3712])).
% 5.80/1.12  fof(f3712,plain,(
% 5.80/1.12    ( ! [X24,X23] : (k2_xboole_0(k4_xboole_0(k2_xboole_0(X24,X23),X24),X23) = X23) )),
% 5.80/1.12    inference(superposition,[],[f122,f3636])).
% 5.80/1.12  fof(f3636,plain,(
% 5.80/1.12    ( ! [X30,X31] : (k2_xboole_0(X31,k4_xboole_0(k2_xboole_0(X30,X31),X30)) = X31) )),
% 5.80/1.12    inference(forward_demodulation,[],[f3566,f26])).
% 5.80/1.12  fof(f3566,plain,(
% 5.80/1.12    ( ! [X30,X31] : (k2_xboole_0(X31,k4_xboole_0(k2_xboole_0(X30,X31),X30)) = k2_xboole_0(X31,k1_xboole_0)) )),
% 5.80/1.12    inference(superposition,[],[f205,f42])).
% 5.80/1.12  fof(f42,plain,(
% 5.80/1.12    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 5.80/1.12    inference(superposition,[],[f28,f26])).
% 5.80/1.12  fof(f435,plain,(
% 5.80/1.12    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) )),
% 5.80/1.12    inference(superposition,[],[f36,f39])).
% 5.80/1.12  fof(f8537,plain,(
% 5.80/1.12    ( ! [X6,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(X6,X7))) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7))) )),
% 5.80/1.12    inference(superposition,[],[f39,f6512])).
% 5.80/1.12  fof(f4286,plain,(
% 5.80/1.12    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X6,X5),k5_xboole_0(X5,X6))) )),
% 5.80/1.12    inference(superposition,[],[f3784,f318])).
% 5.80/1.12  fof(f3784,plain,(
% 5.80/1.12    ( ! [X12,X11] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X12,X11),X12),X11)) )),
% 5.80/1.12    inference(superposition,[],[f55,f3637])).
% 5.80/1.12  fof(f14600,plain,(
% 5.80/1.12    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 5.80/1.12    inference(forward_demodulation,[],[f14599,f14026])).
% 5.80/1.12  fof(f14026,plain,(
% 5.80/1.12    ( ! [X2,X1] : (k4_xboole_0(X2,X1) = k5_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 5.80/1.12    inference(superposition,[],[f13818,f31])).
% 5.80/1.12  fof(f13818,plain,(
% 5.80/1.12    ( ! [X21,X22] : (k4_xboole_0(X22,X21) = k5_xboole_0(X21,k2_xboole_0(X21,X22))) )),
% 5.80/1.12    inference(superposition,[],[f318,f12795])).
% 5.80/1.12  fof(f14599,plain,(
% 5.80/1.12    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK0,k2_xboole_0(sK1,sK0)))),
% 5.80/1.12    inference(forward_demodulation,[],[f14598,f12795])).
% 5.80/1.12  fof(f14598,plain,(
% 5.80/1.12    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))))),
% 5.80/1.12    inference(forward_demodulation,[],[f14597,f30])).
% 5.80/1.12  fof(f14597,plain,(
% 5.80/1.12    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK0,sK1),sK1)))),
% 5.80/1.12    inference(forward_demodulation,[],[f14523,f311])).
% 5.80/1.12  fof(f311,plain,(
% 5.80/1.12    ( ! [X8,X7,X9] : (k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8))) )),
% 5.80/1.12    inference(superposition,[],[f37,f30])).
% 5.80/1.12  fof(f14523,plain,(
% 5.80/1.12    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 5.80/1.12    inference(backward_demodulation,[],[f313,f14178])).
% 5.80/1.12  fof(f14178,plain,(
% 5.80/1.12    ( ! [X6,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,X6)) = k5_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 5.80/1.12    inference(backward_demodulation,[],[f1504,f14174])).
% 5.80/1.12  fof(f14174,plain,(
% 5.80/1.12    ( ! [X54,X53] : (k4_xboole_0(X53,X54) = k4_xboole_0(X53,k5_xboole_0(X53,k4_xboole_0(X53,X54)))) )),
% 5.80/1.12    inference(forward_demodulation,[],[f14173,f318])).
% 5.80/1.12  fof(f14173,plain,(
% 5.80/1.12    ( ! [X54,X53] : (k4_xboole_0(X53,k5_xboole_0(X53,k4_xboole_0(X53,X54))) = k5_xboole_0(X53,k5_xboole_0(X53,k4_xboole_0(X53,X54)))) )),
% 5.80/1.12    inference(forward_demodulation,[],[f14052,f30])).
% 5.80/1.12  fof(f14052,plain,(
% 5.80/1.12    ( ! [X54,X53] : (k4_xboole_0(X53,k5_xboole_0(X53,k4_xboole_0(X53,X54))) = k5_xboole_0(k5_xboole_0(X53,k4_xboole_0(X53,X54)),X53)) )),
% 5.80/1.12    inference(superposition,[],[f13818,f1588])).
% 5.80/1.12  fof(f1588,plain,(
% 5.80/1.12    ( ! [X33,X34] : (k2_xboole_0(k5_xboole_0(X33,k4_xboole_0(X33,X34)),X33) = X33) )),
% 5.80/1.12    inference(forward_demodulation,[],[f1530,f24])).
% 5.80/1.12  fof(f1530,plain,(
% 5.80/1.12    ( ! [X33,X34] : (k2_xboole_0(k4_xboole_0(k5_xboole_0(X33,k4_xboole_0(X33,X34)),k1_xboole_0),X33) = X33) )),
% 5.80/1.12    inference(superposition,[],[f594,f764])).
% 5.80/1.12  fof(f764,plain,(
% 5.80/1.12    ( ! [X12,X13] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X12,k4_xboole_0(X12,X13)),X12)) )),
% 5.80/1.12    inference(superposition,[],[f651,f495])).
% 5.80/1.12  fof(f495,plain,(
% 5.80/1.12    ( ! [X12,X13] : (k2_xboole_0(X12,k4_xboole_0(X12,X13)) = X12) )),
% 5.80/1.12    inference(superposition,[],[f76,f40])).
% 5.80/1.12  fof(f594,plain,(
% 5.80/1.12    ( ! [X19,X18] : (k2_xboole_0(k4_xboole_0(X19,k4_xboole_0(X19,X18)),X18) = X18) )),
% 5.80/1.12    inference(superposition,[],[f498,f39])).
% 5.80/1.12  fof(f498,plain,(
% 5.80/1.12    ( ! [X19,X18] : (k2_xboole_0(k4_xboole_0(X18,X19),X18) = X18) )),
% 5.80/1.12    inference(superposition,[],[f122,f40])).
% 5.80/1.12  fof(f1504,plain,(
% 5.80/1.12    ( ! [X6,X5] : (k5_xboole_0(X5,k4_xboole_0(X5,X6)) = k4_xboole_0(X5,k4_xboole_0(X5,k5_xboole_0(X5,k4_xboole_0(X5,X6))))) )),
% 5.80/1.12    inference(forward_demodulation,[],[f1461,f24])).
% 5.80/1.12  fof(f1461,plain,(
% 5.80/1.12    ( ! [X6,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,k5_xboole_0(X5,k4_xboole_0(X5,X6)))) = k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X5,X6)),k1_xboole_0)) )),
% 5.80/1.12    inference(superposition,[],[f39,f764])).
% 5.80/1.12  fof(f313,plain,(
% 5.80/1.12    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 5.80/1.12    inference(superposition,[],[f38,f37])).
% 5.80/1.12  fof(f38,plain,(
% 5.80/1.12    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 5.80/1.12    inference(definition_unfolding,[],[f22,f32])).
% 5.80/1.12  fof(f22,plain,(
% 5.80/1.12    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 5.80/1.12    inference(cnf_transformation,[],[f21])).
% 5.80/1.12  fof(f21,plain,(
% 5.80/1.12    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 5.80/1.12    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 5.80/1.12  fof(f20,plain,(
% 5.80/1.12    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 5.80/1.12    introduced(choice_axiom,[])).
% 5.80/1.12  fof(f19,plain,(
% 5.80/1.12    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.80/1.12    inference(ennf_transformation,[],[f17])).
% 5.80/1.12  fof(f17,negated_conjecture,(
% 5.80/1.12    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.80/1.12    inference(negated_conjecture,[],[f16])).
% 5.80/1.12  fof(f16,conjecture,(
% 5.80/1.12    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.80/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 5.80/1.12  % SZS output end Proof for theBenchmark
% 5.80/1.12  % (12280)------------------------------
% 5.80/1.12  % (12280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.80/1.12  % (12280)Termination reason: Refutation
% 5.80/1.12  
% 5.80/1.12  % (12280)Memory used [KB]: 13432
% 5.80/1.12  % (12280)Time elapsed: 0.686 s
% 5.80/1.12  % (12280)------------------------------
% 5.80/1.12  % (12280)------------------------------
% 5.80/1.12  % (12278)Success in time 0.768 s
%------------------------------------------------------------------------------
