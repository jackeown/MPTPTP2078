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
% DateTime   : Thu Dec  3 12:31:52 EST 2020

% Result     : Theorem 6.20s
% Output     : Refutation 6.20s
% Verified   : 
% Statistics : Number of formulae       :  132 (1226 expanded)
%              Number of leaves         :   16 ( 424 expanded)
%              Depth                    :   23
%              Number of atoms          :  133 (1227 expanded)
%              Number of equality atoms :  132 (1226 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15220,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f15216])).

fof(f15216,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f15191,f3407])).

fof(f3407,plain,(
    ! [X48,X49] : k2_xboole_0(X48,X49) = k2_xboole_0(k4_xboole_0(X49,X48),X48) ),
    inference(forward_demodulation,[],[f3343,f1314])).

fof(f1314,plain,(
    ! [X33,X32] : k2_xboole_0(X32,X33) = k2_xboole_0(k2_xboole_0(X32,X33),k4_xboole_0(X33,X32)) ),
    inference(superposition,[],[f900,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f28,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f900,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3 ),
    inference(superposition,[],[f508,f22])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f508,plain,(
    ! [X14,X13] : k4_xboole_0(k2_xboole_0(X13,k4_xboole_0(X13,X14)),k1_xboole_0) = X13 ),
    inference(forward_demodulation,[],[f500,f24])).

fof(f500,plain,(
    ! [X14,X13] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X13,X14),X13),k1_xboole_0) = X13 ),
    inference(superposition,[],[f137,f445])).

fof(f445,plain,(
    ! [X19,X20] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X19,X20),X19) ),
    inference(forward_demodulation,[],[f444,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f36,f22])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f21,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f444,plain,(
    ! [X19,X20] : k4_xboole_0(k4_xboole_0(X19,X20),X19) = k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X19,X20)) ),
    inference(forward_demodulation,[],[f418,f308])).

fof(f308,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f38,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f25,f25])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f25])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f418,plain,(
    ! [X19,X20] : k4_xboole_0(k4_xboole_0(X19,X20),X19) = k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X19,k4_xboole_0(X20,k4_xboole_0(X20,X19)))) ),
    inference(superposition,[],[f308,f37])).

fof(f137,plain,(
    ! [X10,X11] : k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,X11)) = X11 ),
    inference(forward_demodulation,[],[f136,f22])).

fof(f136,plain,(
    ! [X10,X11] : k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,X11)) = k4_xboole_0(X11,k1_xboole_0) ),
    inference(forward_demodulation,[],[f118,f86])).

fof(f86,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f55,f24])).

fof(f55,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f52,f42])).

fof(f52,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k2_xboole_0(X4,X5)) = k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X4,X5)) ),
    inference(superposition,[],[f28,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f118,plain,(
    ! [X10,X11] : k4_xboole_0(X11,k4_xboole_0(X11,k2_xboole_0(X10,X11))) = k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,X11)) ),
    inference(superposition,[],[f37,f28])).

fof(f3343,plain,(
    ! [X48,X49] : k2_xboole_0(k4_xboole_0(X49,X48),X48) = k2_xboole_0(k2_xboole_0(X48,X49),k4_xboole_0(X49,X48)) ),
    inference(superposition,[],[f2995,f164])).

fof(f164,plain,(
    ! [X2,X1] : k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X1 ),
    inference(forward_demodulation,[],[f163,f22])).

fof(f163,plain,(
    ! [X2,X1] : k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f157,f55])).

fof(f157,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(superposition,[],[f37,f50])).

fof(f2995,plain,(
    ! [X26,X27] : k2_xboole_0(X26,X27) = k2_xboole_0(X27,k4_xboole_0(X26,X27)) ),
    inference(forward_demodulation,[],[f2994,f1386])).

fof(f1386,plain,(
    ! [X14,X15,X13,X16] : k4_xboole_0(X13,k2_xboole_0(k4_xboole_0(X14,k2_xboole_0(X13,X15)),X16)) = k4_xboole_0(X13,X16) ),
    inference(superposition,[],[f31,f1098])).

fof(f1098,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = X2 ),
    inference(forward_demodulation,[],[f1097,f900])).

fof(f1097,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(X2,k4_xboole_0(X2,X4)) ),
    inference(forward_demodulation,[],[f1096,f24])).

fof(f1096,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X2,X4),X2) ),
    inference(forward_demodulation,[],[f995,f22])).

fof(f995,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X2,X4),k4_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f41,f55])).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f33,f25])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f2994,plain,(
    ! [X26,X27] : k2_xboole_0(X26,X27) = k2_xboole_0(X27,k4_xboole_0(X26,k2_xboole_0(k4_xboole_0(X26,k2_xboole_0(X26,X27)),X27))) ),
    inference(forward_demodulation,[],[f2993,f31])).

fof(f2993,plain,(
    ! [X26,X27] : k2_xboole_0(X26,X27) = k2_xboole_0(X27,k4_xboole_0(k4_xboole_0(X26,k4_xboole_0(X26,k2_xboole_0(X26,X27))),X27)) ),
    inference(forward_demodulation,[],[f2992,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[],[f31,f37])).

fof(f2992,plain,(
    ! [X26,X27] : k2_xboole_0(X26,X27) = k2_xboole_0(X27,k4_xboole_0(k2_xboole_0(X26,X27),k2_xboole_0(k4_xboole_0(k2_xboole_0(X26,X27),X26),X27))) ),
    inference(forward_demodulation,[],[f2991,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(backward_demodulation,[],[f39,f31])).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f30,f25,f25])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f2991,plain,(
    ! [X26,X27] : k2_xboole_0(X26,X27) = k2_xboole_0(X27,k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(X26,X27)))) ),
    inference(forward_demodulation,[],[f2990,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f26,f24])).

fof(f2990,plain,(
    ! [X26,X27] : k2_xboole_0(X27,k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(X26,X27)))) = k2_xboole_0(X27,k2_xboole_0(X26,X27)) ),
    inference(forward_demodulation,[],[f2825,f22])).

fof(f2825,plain,(
    ! [X26,X27] : k2_xboole_0(X27,k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(X26,X27)))) = k4_xboole_0(k2_xboole_0(X27,k2_xboole_0(X26,X27)),k1_xboole_0) ),
    inference(superposition,[],[f168,f177])).

fof(f177,plain,(
    ! [X12,X13] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X13,k4_xboole_0(X12,X13))) ),
    inference(superposition,[],[f75,f28])).

fof(f75,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f31,f42])).

fof(f168,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(backward_demodulation,[],[f40,f167])).

fof(f167,plain,(
    ! [X6,X7,X5] : k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X7)) = k4_xboole_0(X6,k2_xboole_0(X5,X7)) ),
    inference(forward_demodulation,[],[f159,f31])).

fof(f159,plain,(
    ! [X6,X7,X5] : k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X7)) = k4_xboole_0(k4_xboole_0(X6,X5),X7) ),
    inference(superposition,[],[f31,f50])).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f32,f25,f25])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f15191,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) ),
    inference(forward_demodulation,[],[f15190,f900])).

fof(f15190,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f15189,f24])).

fof(f15189,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) ),
    inference(forward_demodulation,[],[f15042,f2918])).

fof(f2918,plain,(
    ! [X4,X5] : k2_xboole_0(X5,X4) = k2_xboole_0(X5,k4_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f2917,f38])).

fof(f2917,plain,(
    ! [X4,X5] : k2_xboole_0(X5,X4) = k2_xboole_0(X5,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X4,X5)))) ),
    inference(forward_demodulation,[],[f2817,f22])).

fof(f2817,plain,(
    ! [X4,X5] : k2_xboole_0(X5,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X4,X5)))) = k4_xboole_0(k2_xboole_0(X5,X4),k1_xboole_0) ),
    inference(superposition,[],[f168,f75])).

fof(f15042,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f1293,f5552])).

fof(f5552,plain,(
    ! [X17,X18,X16] : k2_xboole_0(k2_xboole_0(X17,X16),X18) = k2_xboole_0(X16,k2_xboole_0(X17,X18)) ),
    inference(backward_demodulation,[],[f1630,f5551])).

fof(f5551,plain,(
    ! [X127,X128,X126] : k2_xboole_0(X127,k2_xboole_0(k2_xboole_0(X126,X127),X128)) = k2_xboole_0(X127,k2_xboole_0(X126,X128)) ),
    inference(forward_demodulation,[],[f5479,f2918])).

fof(f5479,plain,(
    ! [X127,X128,X126] : k2_xboole_0(X127,k2_xboole_0(k2_xboole_0(X126,X127),X128)) = k2_xboole_0(X127,k4_xboole_0(k2_xboole_0(X126,X128),X127)) ),
    inference(superposition,[],[f2918,f578])).

fof(f578,plain,(
    ! [X43,X41,X42] : k4_xboole_0(k2_xboole_0(k2_xboole_0(X41,X42),X43),X42) = k4_xboole_0(k2_xboole_0(X41,X43),X42) ),
    inference(forward_demodulation,[],[f522,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f522,plain,(
    ! [X43,X41,X42] : k4_xboole_0(k2_xboole_0(k2_xboole_0(X41,X42),X43),X42) = k2_xboole_0(k4_xboole_0(X41,X42),k4_xboole_0(X43,X42)) ),
    inference(superposition,[],[f34,f28])).

fof(f1630,plain,(
    ! [X17,X18,X16] : k2_xboole_0(k2_xboole_0(X17,X16),X18) = k2_xboole_0(X16,k2_xboole_0(k2_xboole_0(X17,X16),X18)) ),
    inference(forward_demodulation,[],[f1564,f22])).

fof(f1564,plain,(
    ! [X17,X18,X16] : k2_xboole_0(k2_xboole_0(X17,X16),X18) = k2_xboole_0(k4_xboole_0(X16,k1_xboole_0),k2_xboole_0(k2_xboole_0(X17,X16),X18)) ),
    inference(superposition,[],[f1250,f104])).

fof(f104,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3)) ),
    inference(forward_demodulation,[],[f102,f69])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f65,f42])).

fof(f65,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f28,f58])).

fof(f58,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f56,f24])).

fof(f56,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f53,f22])).

fof(f53,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f28,f22])).

fof(f102,plain,(
    ! [X2,X3,X1] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3)) ),
    inference(superposition,[],[f31,f86])).

fof(f1250,plain,(
    ! [X19,X20] : k2_xboole_0(k4_xboole_0(X20,k4_xboole_0(X20,X19)),X19) = X19 ),
    inference(superposition,[],[f1229,f37])).

fof(f1229,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(forward_demodulation,[],[f1211,f1095])).

fof(f1095,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(forward_demodulation,[],[f1094,f900])).

fof(f1094,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f1093,f24])).

fof(f1093,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f994,f22])).

fof(f994,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f41,f42])).

fof(f1211,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f41,f1095])).

fof(f1293,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f1132,f1291])).

fof(f1291,plain,(
    ! [X59,X57,X58] : k4_xboole_0(X57,X58) = k4_xboole_0(X57,k2_xboole_0(X58,k4_xboole_0(X59,X57))) ),
    inference(backward_demodulation,[],[f1143,f1260])).

fof(f1260,plain,(
    ! [X39,X38,X40] : k4_xboole_0(X38,X39) = k2_xboole_0(k4_xboole_0(X38,k2_xboole_0(X39,X40)),k4_xboole_0(X38,X39)) ),
    inference(superposition,[],[f1229,f31])).

fof(f1143,plain,(
    ! [X59,X57,X58] : k2_xboole_0(k4_xboole_0(X57,k2_xboole_0(X58,X59)),k4_xboole_0(X57,X58)) = k4_xboole_0(X57,k2_xboole_0(X58,k4_xboole_0(X59,X57))) ),
    inference(forward_demodulation,[],[f1142,f31])).

fof(f1142,plain,(
    ! [X59,X57,X58] : k4_xboole_0(k4_xboole_0(X57,X58),k4_xboole_0(X59,X57)) = k2_xboole_0(k4_xboole_0(X57,k2_xboole_0(X58,X59)),k4_xboole_0(X57,X58)) ),
    inference(forward_demodulation,[],[f1141,f31])).

fof(f1141,plain,(
    ! [X59,X57,X58] : k4_xboole_0(k4_xboole_0(X57,X58),k4_xboole_0(X59,X57)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X57,X58),X59),k4_xboole_0(X57,X58)) ),
    inference(forward_demodulation,[],[f1012,f22])).

fof(f1012,plain,(
    ! [X59,X57,X58] : k4_xboole_0(k4_xboole_0(X57,X58),k4_xboole_0(X59,X57)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X57,X58),X59),k4_xboole_0(k4_xboole_0(X57,X58),k1_xboole_0)) ),
    inference(superposition,[],[f41,f445])).

fof(f1132,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(forward_demodulation,[],[f1131,f60])).

fof(f60,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = X1 ),
    inference(superposition,[],[f26,f56])).

fof(f1131,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k2_xboole_0(sK0,sK0))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(forward_demodulation,[],[f1130,f31])).

fof(f1130,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK1,sK0),sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(forward_demodulation,[],[f1129,f580])).

fof(f580,plain,(
    ! [X59,X57,X58] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X57,X58),X59),X57) = k4_xboole_0(X59,X57) ),
    inference(forward_demodulation,[],[f527,f58])).

fof(f527,plain,(
    ! [X59,X57,X58] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X57,X58),X59),X57) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X59,X57)) ),
    inference(superposition,[],[f34,f445])).

fof(f1129,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(backward_demodulation,[],[f46,f1128])).

fof(f1128,plain,(
    ! [X45,X46,X44] : k4_xboole_0(k2_xboole_0(X44,X45),k4_xboole_0(X46,X44)) = k2_xboole_0(X44,k4_xboole_0(k2_xboole_0(X44,X45),X46)) ),
    inference(forward_demodulation,[],[f1127,f24])).

fof(f1127,plain,(
    ! [X45,X46,X44] : k4_xboole_0(k2_xboole_0(X44,X45),k4_xboole_0(X46,X44)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X44,X45),X46),X44) ),
    inference(forward_demodulation,[],[f1008,f164])).

fof(f1008,plain,(
    ! [X45,X46,X44] : k4_xboole_0(k2_xboole_0(X44,X45),k4_xboole_0(X46,X44)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X44,X45),X46),k4_xboole_0(k2_xboole_0(X44,X45),k4_xboole_0(X45,X44))) ),
    inference(superposition,[],[f41,f50])).

fof(f46,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(forward_demodulation,[],[f45,f26])).

fof(f45,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f43,f44])).

fof(f43,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))) ),
    inference(backward_demodulation,[],[f35,f39])).

fof(f35,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f20,f29,f29,f25])).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f20,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : run_vampire %s %d
% 0.11/0.30  % Computer   : n009.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % WCLimit    : 600
% 0.11/0.30  % DateTime   : Tue Dec  1 12:22:41 EST 2020
% 0.11/0.30  % CPUTime    : 
% 0.17/0.41  % (31426)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.17/0.41  % (31435)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.17/0.41  % (31434)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.17/0.42  % (31429)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.17/0.42  % (31422)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.17/0.42  % (31436)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.17/0.43  % (31428)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.17/0.43  % (31439)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.17/0.43  % (31425)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.17/0.43  % (31437)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.17/0.43  % (31432)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.17/0.43  % (31424)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.17/0.43  % (31431)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.17/0.44  % (31427)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.17/0.44  % (31430)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.17/0.45  % (31438)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.17/0.46  % (31423)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.17/0.46  % (31433)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.17/0.46  % (31433)Refutation not found, incomplete strategy% (31433)------------------------------
% 0.17/0.46  % (31433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.46  % (31433)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.46  
% 0.17/0.46  % (31433)Memory used [KB]: 10490
% 0.17/0.46  % (31433)Time elapsed: 0.104 s
% 0.17/0.46  % (31433)------------------------------
% 0.17/0.46  % (31433)------------------------------
% 4.83/0.97  % (31426)Time limit reached!
% 4.83/0.97  % (31426)------------------------------
% 4.83/0.97  % (31426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.83/0.97  % (31426)Termination reason: Time limit
% 4.83/0.97  % (31426)Termination phase: Saturation
% 4.83/0.97  
% 4.83/0.97  % (31426)Memory used [KB]: 22643
% 4.83/0.97  % (31426)Time elapsed: 0.600 s
% 4.83/0.97  % (31426)------------------------------
% 4.83/0.97  % (31426)------------------------------
% 6.20/1.13  % (31423)Refutation found. Thanks to Tanya!
% 6.20/1.13  % SZS status Theorem for theBenchmark
% 6.20/1.14  % SZS output start Proof for theBenchmark
% 6.20/1.14  fof(f15220,plain,(
% 6.20/1.14    $false),
% 6.20/1.14    inference(trivial_inequality_removal,[],[f15216])).
% 6.20/1.14  fof(f15216,plain,(
% 6.20/1.14    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1)),
% 6.20/1.14    inference(superposition,[],[f15191,f3407])).
% 6.20/1.14  fof(f3407,plain,(
% 6.20/1.14    ( ! [X48,X49] : (k2_xboole_0(X48,X49) = k2_xboole_0(k4_xboole_0(X49,X48),X48)) )),
% 6.20/1.14    inference(forward_demodulation,[],[f3343,f1314])).
% 6.20/1.14  fof(f1314,plain,(
% 6.20/1.14    ( ! [X33,X32] : (k2_xboole_0(X32,X33) = k2_xboole_0(k2_xboole_0(X32,X33),k4_xboole_0(X33,X32))) )),
% 6.20/1.14    inference(superposition,[],[f900,f50])).
% 6.20/1.14  fof(f50,plain,(
% 6.20/1.14    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 6.20/1.14    inference(superposition,[],[f28,f24])).
% 6.20/1.14  fof(f24,plain,(
% 6.20/1.14    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 6.20/1.14    inference(cnf_transformation,[],[f1])).
% 6.20/1.14  fof(f1,axiom,(
% 6.20/1.14    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 6.20/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 6.20/1.14  fof(f28,plain,(
% 6.20/1.14    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 6.20/1.14    inference(cnf_transformation,[],[f7])).
% 6.20/1.14  fof(f7,axiom,(
% 6.20/1.14    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 6.20/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 6.20/1.14  fof(f900,plain,(
% 6.20/1.14    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3) )),
% 6.20/1.14    inference(superposition,[],[f508,f22])).
% 6.20/1.14  fof(f22,plain,(
% 6.20/1.14    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.20/1.14    inference(cnf_transformation,[],[f6])).
% 6.20/1.14  fof(f6,axiom,(
% 6.20/1.14    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 6.20/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 6.20/1.14  fof(f508,plain,(
% 6.20/1.14    ( ! [X14,X13] : (k4_xboole_0(k2_xboole_0(X13,k4_xboole_0(X13,X14)),k1_xboole_0) = X13) )),
% 6.20/1.14    inference(forward_demodulation,[],[f500,f24])).
% 6.20/1.14  fof(f500,plain,(
% 6.20/1.14    ( ! [X14,X13] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X13,X14),X13),k1_xboole_0) = X13) )),
% 6.20/1.14    inference(superposition,[],[f137,f445])).
% 6.20/1.14  fof(f445,plain,(
% 6.20/1.14    ( ! [X19,X20] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X19,X20),X19)) )),
% 6.20/1.14    inference(forward_demodulation,[],[f444,f42])).
% 6.20/1.14  fof(f42,plain,(
% 6.20/1.14    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 6.20/1.14    inference(backward_demodulation,[],[f36,f22])).
% 6.20/1.14  fof(f36,plain,(
% 6.20/1.14    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 6.20/1.14    inference(definition_unfolding,[],[f21,f25])).
% 6.20/1.14  fof(f25,plain,(
% 6.20/1.14    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.20/1.14    inference(cnf_transformation,[],[f11])).
% 6.20/1.14  fof(f11,axiom,(
% 6.20/1.14    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.20/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 6.20/1.14  fof(f21,plain,(
% 6.20/1.14    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 6.20/1.14    inference(cnf_transformation,[],[f5])).
% 6.20/1.14  fof(f5,axiom,(
% 6.20/1.14    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 6.20/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 6.20/1.14  fof(f444,plain,(
% 6.20/1.14    ( ! [X19,X20] : (k4_xboole_0(k4_xboole_0(X19,X20),X19) = k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X19,X20))) )),
% 6.20/1.14    inference(forward_demodulation,[],[f418,f308])).
% 6.20/1.14  fof(f308,plain,(
% 6.20/1.14    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 6.20/1.14    inference(superposition,[],[f38,f37])).
% 6.20/1.14  fof(f37,plain,(
% 6.20/1.14    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 6.20/1.14    inference(definition_unfolding,[],[f23,f25,f25])).
% 6.20/1.14  fof(f23,plain,(
% 6.20/1.14    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.20/1.14    inference(cnf_transformation,[],[f2])).
% 6.20/1.14  fof(f2,axiom,(
% 6.20/1.14    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.20/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 6.20/1.14  fof(f38,plain,(
% 6.20/1.14    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 6.20/1.14    inference(definition_unfolding,[],[f27,f25])).
% 6.20/1.14  fof(f27,plain,(
% 6.20/1.14    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.20/1.14    inference(cnf_transformation,[],[f10])).
% 6.20/1.14  fof(f10,axiom,(
% 6.20/1.14    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.20/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 6.20/1.14  fof(f418,plain,(
% 6.20/1.14    ( ! [X19,X20] : (k4_xboole_0(k4_xboole_0(X19,X20),X19) = k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X19,k4_xboole_0(X20,k4_xboole_0(X20,X19))))) )),
% 6.20/1.14    inference(superposition,[],[f308,f37])).
% 6.20/1.14  fof(f137,plain,(
% 6.20/1.14    ( ! [X10,X11] : (k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,X11)) = X11) )),
% 6.20/1.14    inference(forward_demodulation,[],[f136,f22])).
% 6.20/1.14  fof(f136,plain,(
% 6.20/1.14    ( ! [X10,X11] : (k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,X11)) = k4_xboole_0(X11,k1_xboole_0)) )),
% 6.20/1.14    inference(forward_demodulation,[],[f118,f86])).
% 6.20/1.14  fof(f86,plain,(
% 6.20/1.14    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 6.20/1.14    inference(superposition,[],[f55,f24])).
% 6.20/1.14  fof(f55,plain,(
% 6.20/1.14    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X4,X5))) )),
% 6.20/1.14    inference(forward_demodulation,[],[f52,f42])).
% 6.20/1.14  fof(f52,plain,(
% 6.20/1.14    ( ! [X4,X5] : (k4_xboole_0(X4,k2_xboole_0(X4,X5)) = k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X4,X5))) )),
% 6.20/1.14    inference(superposition,[],[f28,f26])).
% 6.20/1.14  fof(f26,plain,(
% 6.20/1.14    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 6.20/1.14    inference(cnf_transformation,[],[f14])).
% 6.20/1.14  fof(f14,axiom,(
% 6.20/1.14    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 6.20/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).
% 6.20/1.14  fof(f118,plain,(
% 6.20/1.14    ( ! [X10,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,k2_xboole_0(X10,X11))) = k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,X11))) )),
% 6.20/1.14    inference(superposition,[],[f37,f28])).
% 6.20/1.14  fof(f3343,plain,(
% 6.20/1.14    ( ! [X48,X49] : (k2_xboole_0(k4_xboole_0(X49,X48),X48) = k2_xboole_0(k2_xboole_0(X48,X49),k4_xboole_0(X49,X48))) )),
% 6.20/1.14    inference(superposition,[],[f2995,f164])).
% 6.20/1.14  fof(f164,plain,(
% 6.20/1.14    ( ! [X2,X1] : (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X1) )),
% 6.20/1.14    inference(forward_demodulation,[],[f163,f22])).
% 6.20/1.14  fof(f163,plain,(
% 6.20/1.14    ( ! [X2,X1] : (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k1_xboole_0)) )),
% 6.20/1.14    inference(forward_demodulation,[],[f157,f55])).
% 6.20/1.14  fof(f157,plain,(
% 6.20/1.14    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))) )),
% 6.20/1.14    inference(superposition,[],[f37,f50])).
% 6.20/1.14  fof(f2995,plain,(
% 6.20/1.14    ( ! [X26,X27] : (k2_xboole_0(X26,X27) = k2_xboole_0(X27,k4_xboole_0(X26,X27))) )),
% 6.20/1.14    inference(forward_demodulation,[],[f2994,f1386])).
% 6.20/1.14  fof(f1386,plain,(
% 6.20/1.14    ( ! [X14,X15,X13,X16] : (k4_xboole_0(X13,k2_xboole_0(k4_xboole_0(X14,k2_xboole_0(X13,X15)),X16)) = k4_xboole_0(X13,X16)) )),
% 6.20/1.14    inference(superposition,[],[f31,f1098])).
% 6.20/1.14  fof(f1098,plain,(
% 6.20/1.14    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = X2) )),
% 6.20/1.14    inference(forward_demodulation,[],[f1097,f900])).
% 6.20/1.14  fof(f1097,plain,(
% 6.20/1.14    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(X2,k4_xboole_0(X2,X4))) )),
% 6.20/1.14    inference(forward_demodulation,[],[f1096,f24])).
% 6.20/1.14  fof(f1096,plain,(
% 6.20/1.14    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X2,X4),X2)) )),
% 6.20/1.14    inference(forward_demodulation,[],[f995,f22])).
% 6.20/1.14  fof(f995,plain,(
% 6.20/1.14    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X2,X4),k4_xboole_0(X2,k1_xboole_0))) )),
% 6.20/1.14    inference(superposition,[],[f41,f55])).
% 6.20/1.14  fof(f41,plain,(
% 6.20/1.14    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 6.20/1.14    inference(definition_unfolding,[],[f33,f25])).
% 6.20/1.14  fof(f33,plain,(
% 6.20/1.14    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 6.20/1.14    inference(cnf_transformation,[],[f13])).
% 6.20/1.14  fof(f13,axiom,(
% 6.20/1.14    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 6.20/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 6.20/1.14  fof(f31,plain,(
% 6.20/1.14    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 6.20/1.14    inference(cnf_transformation,[],[f8])).
% 6.20/1.14  fof(f8,axiom,(
% 6.20/1.14    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 6.20/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 6.20/1.14  fof(f2994,plain,(
% 6.20/1.14    ( ! [X26,X27] : (k2_xboole_0(X26,X27) = k2_xboole_0(X27,k4_xboole_0(X26,k2_xboole_0(k4_xboole_0(X26,k2_xboole_0(X26,X27)),X27)))) )),
% 6.20/1.14    inference(forward_demodulation,[],[f2993,f31])).
% 6.20/1.14  fof(f2993,plain,(
% 6.20/1.14    ( ! [X26,X27] : (k2_xboole_0(X26,X27) = k2_xboole_0(X27,k4_xboole_0(k4_xboole_0(X26,k4_xboole_0(X26,k2_xboole_0(X26,X27))),X27))) )),
% 6.20/1.14    inference(forward_demodulation,[],[f2992,f129])).
% 6.20/1.14  fof(f129,plain,(
% 6.20/1.14    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) )),
% 6.20/1.14    inference(superposition,[],[f31,f37])).
% 6.20/1.14  fof(f2992,plain,(
% 6.20/1.14    ( ! [X26,X27] : (k2_xboole_0(X26,X27) = k2_xboole_0(X27,k4_xboole_0(k2_xboole_0(X26,X27),k2_xboole_0(k4_xboole_0(k2_xboole_0(X26,X27),X26),X27)))) )),
% 6.20/1.14    inference(forward_demodulation,[],[f2991,f44])).
% 6.20/1.14  fof(f44,plain,(
% 6.20/1.14    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 6.20/1.14    inference(backward_demodulation,[],[f39,f31])).
% 6.20/1.14  fof(f39,plain,(
% 6.20/1.14    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 6.20/1.14    inference(definition_unfolding,[],[f30,f25,f25])).
% 6.20/1.14  fof(f30,plain,(
% 6.20/1.14    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 6.20/1.14    inference(cnf_transformation,[],[f12])).
% 6.20/1.14  fof(f12,axiom,(
% 6.20/1.14    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 6.20/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 6.20/1.14  fof(f2991,plain,(
% 6.20/1.14    ( ! [X26,X27] : (k2_xboole_0(X26,X27) = k2_xboole_0(X27,k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(X26,X27))))) )),
% 6.20/1.14    inference(forward_demodulation,[],[f2990,f47])).
% 6.20/1.14  fof(f47,plain,(
% 6.20/1.14    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 6.20/1.14    inference(superposition,[],[f26,f24])).
% 6.20/1.14  fof(f2990,plain,(
% 6.20/1.14    ( ! [X26,X27] : (k2_xboole_0(X27,k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(X26,X27)))) = k2_xboole_0(X27,k2_xboole_0(X26,X27))) )),
% 6.20/1.14    inference(forward_demodulation,[],[f2825,f22])).
% 6.20/1.14  fof(f2825,plain,(
% 6.20/1.14    ( ! [X26,X27] : (k2_xboole_0(X27,k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(X26,X27)))) = k4_xboole_0(k2_xboole_0(X27,k2_xboole_0(X26,X27)),k1_xboole_0)) )),
% 6.20/1.14    inference(superposition,[],[f168,f177])).
% 6.20/1.14  fof(f177,plain,(
% 6.20/1.14    ( ! [X12,X13] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X13,k4_xboole_0(X12,X13)))) )),
% 6.20/1.14    inference(superposition,[],[f75,f28])).
% 6.20/1.14  fof(f75,plain,(
% 6.20/1.14    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 6.20/1.14    inference(superposition,[],[f31,f42])).
% 6.20/1.14  fof(f168,plain,(
% 6.20/1.14    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X0,X2)))) )),
% 6.20/1.14    inference(backward_demodulation,[],[f40,f167])).
% 6.20/1.14  fof(f167,plain,(
% 6.20/1.14    ( ! [X6,X7,X5] : (k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X7)) = k4_xboole_0(X6,k2_xboole_0(X5,X7))) )),
% 6.20/1.14    inference(forward_demodulation,[],[f159,f31])).
% 6.20/1.14  fof(f159,plain,(
% 6.20/1.14    ( ! [X6,X7,X5] : (k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X7)) = k4_xboole_0(k4_xboole_0(X6,X5),X7)) )),
% 6.20/1.14    inference(superposition,[],[f31,f50])).
% 6.20/1.14  fof(f40,plain,(
% 6.20/1.14    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)))) )),
% 6.20/1.14    inference(definition_unfolding,[],[f32,f25,f25])).
% 6.20/1.14  fof(f32,plain,(
% 6.20/1.14    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 6.20/1.14    inference(cnf_transformation,[],[f4])).
% 6.20/1.14  fof(f4,axiom,(
% 6.20/1.14    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 6.20/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).
% 6.20/1.14  fof(f15191,plain,(
% 6.20/1.14    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)),
% 6.20/1.14    inference(forward_demodulation,[],[f15190,f900])).
% 6.20/1.14  fof(f15190,plain,(
% 6.20/1.14    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 6.20/1.14    inference(forward_demodulation,[],[f15189,f24])).
% 6.20/1.14  fof(f15189,plain,(
% 6.20/1.14    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0))),
% 6.20/1.14    inference(forward_demodulation,[],[f15042,f2918])).
% 6.20/1.14  fof(f2918,plain,(
% 6.20/1.14    ( ! [X4,X5] : (k2_xboole_0(X5,X4) = k2_xboole_0(X5,k4_xboole_0(X4,X5))) )),
% 6.20/1.14    inference(forward_demodulation,[],[f2917,f38])).
% 6.20/1.14  fof(f2917,plain,(
% 6.20/1.14    ( ! [X4,X5] : (k2_xboole_0(X5,X4) = k2_xboole_0(X5,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X4,X5))))) )),
% 6.20/1.14    inference(forward_demodulation,[],[f2817,f22])).
% 6.20/1.14  fof(f2817,plain,(
% 6.20/1.14    ( ! [X4,X5] : (k2_xboole_0(X5,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X4,X5)))) = k4_xboole_0(k2_xboole_0(X5,X4),k1_xboole_0)) )),
% 6.20/1.14    inference(superposition,[],[f168,f75])).
% 6.20/1.14  fof(f15042,plain,(
% 6.20/1.14    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 6.20/1.14    inference(superposition,[],[f1293,f5552])).
% 6.20/1.14  fof(f5552,plain,(
% 6.20/1.14    ( ! [X17,X18,X16] : (k2_xboole_0(k2_xboole_0(X17,X16),X18) = k2_xboole_0(X16,k2_xboole_0(X17,X18))) )),
% 6.20/1.14    inference(backward_demodulation,[],[f1630,f5551])).
% 6.20/1.14  fof(f5551,plain,(
% 6.20/1.14    ( ! [X127,X128,X126] : (k2_xboole_0(X127,k2_xboole_0(k2_xboole_0(X126,X127),X128)) = k2_xboole_0(X127,k2_xboole_0(X126,X128))) )),
% 6.20/1.14    inference(forward_demodulation,[],[f5479,f2918])).
% 6.20/1.14  fof(f5479,plain,(
% 6.20/1.14    ( ! [X127,X128,X126] : (k2_xboole_0(X127,k2_xboole_0(k2_xboole_0(X126,X127),X128)) = k2_xboole_0(X127,k4_xboole_0(k2_xboole_0(X126,X128),X127))) )),
% 6.20/1.14    inference(superposition,[],[f2918,f578])).
% 6.20/1.14  fof(f578,plain,(
% 6.20/1.14    ( ! [X43,X41,X42] : (k4_xboole_0(k2_xboole_0(k2_xboole_0(X41,X42),X43),X42) = k4_xboole_0(k2_xboole_0(X41,X43),X42)) )),
% 6.20/1.14    inference(forward_demodulation,[],[f522,f34])).
% 6.20/1.14  fof(f34,plain,(
% 6.20/1.14    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 6.20/1.14    inference(cnf_transformation,[],[f9])).
% 6.20/1.14  fof(f9,axiom,(
% 6.20/1.14    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 6.20/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).
% 6.20/1.14  fof(f522,plain,(
% 6.20/1.14    ( ! [X43,X41,X42] : (k4_xboole_0(k2_xboole_0(k2_xboole_0(X41,X42),X43),X42) = k2_xboole_0(k4_xboole_0(X41,X42),k4_xboole_0(X43,X42))) )),
% 6.20/1.14    inference(superposition,[],[f34,f28])).
% 6.20/1.14  fof(f1630,plain,(
% 6.20/1.14    ( ! [X17,X18,X16] : (k2_xboole_0(k2_xboole_0(X17,X16),X18) = k2_xboole_0(X16,k2_xboole_0(k2_xboole_0(X17,X16),X18))) )),
% 6.20/1.14    inference(forward_demodulation,[],[f1564,f22])).
% 6.20/1.14  fof(f1564,plain,(
% 6.20/1.14    ( ! [X17,X18,X16] : (k2_xboole_0(k2_xboole_0(X17,X16),X18) = k2_xboole_0(k4_xboole_0(X16,k1_xboole_0),k2_xboole_0(k2_xboole_0(X17,X16),X18))) )),
% 6.20/1.14    inference(superposition,[],[f1250,f104])).
% 6.20/1.14  fof(f104,plain,(
% 6.20/1.14    ( ! [X2,X3,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3))) )),
% 6.20/1.14    inference(forward_demodulation,[],[f102,f69])).
% 6.20/1.14  fof(f69,plain,(
% 6.20/1.14    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 6.20/1.14    inference(forward_demodulation,[],[f65,f42])).
% 6.20/1.14  fof(f65,plain,(
% 6.20/1.14    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0)) )),
% 6.20/1.14    inference(superposition,[],[f28,f58])).
% 6.20/1.14  fof(f58,plain,(
% 6.20/1.14    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 6.20/1.14    inference(superposition,[],[f56,f24])).
% 6.20/1.14  fof(f56,plain,(
% 6.20/1.14    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 6.20/1.14    inference(forward_demodulation,[],[f53,f22])).
% 6.20/1.14  fof(f53,plain,(
% 6.20/1.14    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 6.20/1.14    inference(superposition,[],[f28,f22])).
% 6.20/1.14  fof(f102,plain,(
% 6.20/1.14    ( ! [X2,X3,X1] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3))) )),
% 6.20/1.14    inference(superposition,[],[f31,f86])).
% 6.20/1.14  fof(f1250,plain,(
% 6.20/1.14    ( ! [X19,X20] : (k2_xboole_0(k4_xboole_0(X20,k4_xboole_0(X20,X19)),X19) = X19) )),
% 6.20/1.14    inference(superposition,[],[f1229,f37])).
% 6.20/1.14  fof(f1229,plain,(
% 6.20/1.14    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 6.20/1.14    inference(forward_demodulation,[],[f1211,f1095])).
% 6.20/1.14  fof(f1095,plain,(
% 6.20/1.14    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 6.20/1.14    inference(forward_demodulation,[],[f1094,f900])).
% 6.20/1.14  fof(f1094,plain,(
% 6.20/1.14    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 6.20/1.14    inference(forward_demodulation,[],[f1093,f24])).
% 6.20/1.14  fof(f1093,plain,(
% 6.20/1.14    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 6.20/1.14    inference(forward_demodulation,[],[f994,f22])).
% 6.20/1.14  fof(f994,plain,(
% 6.20/1.14    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0))) )),
% 6.20/1.14    inference(superposition,[],[f41,f42])).
% 6.20/1.14  fof(f1211,plain,(
% 6.20/1.14    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 6.20/1.14    inference(superposition,[],[f41,f1095])).
% 6.20/1.14  fof(f1293,plain,(
% 6.20/1.14    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 6.20/1.14    inference(backward_demodulation,[],[f1132,f1291])).
% 6.20/1.14  fof(f1291,plain,(
% 6.20/1.14    ( ! [X59,X57,X58] : (k4_xboole_0(X57,X58) = k4_xboole_0(X57,k2_xboole_0(X58,k4_xboole_0(X59,X57)))) )),
% 6.20/1.14    inference(backward_demodulation,[],[f1143,f1260])).
% 6.20/1.14  fof(f1260,plain,(
% 6.20/1.14    ( ! [X39,X38,X40] : (k4_xboole_0(X38,X39) = k2_xboole_0(k4_xboole_0(X38,k2_xboole_0(X39,X40)),k4_xboole_0(X38,X39))) )),
% 6.20/1.14    inference(superposition,[],[f1229,f31])).
% 6.20/1.14  fof(f1143,plain,(
% 6.20/1.14    ( ! [X59,X57,X58] : (k2_xboole_0(k4_xboole_0(X57,k2_xboole_0(X58,X59)),k4_xboole_0(X57,X58)) = k4_xboole_0(X57,k2_xboole_0(X58,k4_xboole_0(X59,X57)))) )),
% 6.20/1.14    inference(forward_demodulation,[],[f1142,f31])).
% 6.20/1.14  fof(f1142,plain,(
% 6.20/1.14    ( ! [X59,X57,X58] : (k4_xboole_0(k4_xboole_0(X57,X58),k4_xboole_0(X59,X57)) = k2_xboole_0(k4_xboole_0(X57,k2_xboole_0(X58,X59)),k4_xboole_0(X57,X58))) )),
% 6.20/1.14    inference(forward_demodulation,[],[f1141,f31])).
% 6.20/1.14  fof(f1141,plain,(
% 6.20/1.14    ( ! [X59,X57,X58] : (k4_xboole_0(k4_xboole_0(X57,X58),k4_xboole_0(X59,X57)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X57,X58),X59),k4_xboole_0(X57,X58))) )),
% 6.20/1.14    inference(forward_demodulation,[],[f1012,f22])).
% 6.20/1.14  fof(f1012,plain,(
% 6.20/1.14    ( ! [X59,X57,X58] : (k4_xboole_0(k4_xboole_0(X57,X58),k4_xboole_0(X59,X57)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X57,X58),X59),k4_xboole_0(k4_xboole_0(X57,X58),k1_xboole_0))) )),
% 6.20/1.14    inference(superposition,[],[f41,f445])).
% 6.20/1.14  fof(f1132,plain,(
% 6.20/1.14    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 6.20/1.14    inference(forward_demodulation,[],[f1131,f60])).
% 6.20/1.14  fof(f60,plain,(
% 6.20/1.14    ( ! [X1] : (k2_xboole_0(X1,X1) = X1) )),
% 6.20/1.14    inference(superposition,[],[f26,f56])).
% 6.20/1.14  fof(f1131,plain,(
% 6.20/1.14    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k2_xboole_0(sK0,sK0))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 6.20/1.14    inference(forward_demodulation,[],[f1130,f31])).
% 6.20/1.14  fof(f1130,plain,(
% 6.20/1.14    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK1,sK0),sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 6.20/1.14    inference(forward_demodulation,[],[f1129,f580])).
% 6.20/1.14  fof(f580,plain,(
% 6.20/1.14    ( ! [X59,X57,X58] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X57,X58),X59),X57) = k4_xboole_0(X59,X57)) )),
% 6.20/1.14    inference(forward_demodulation,[],[f527,f58])).
% 6.20/1.14  fof(f527,plain,(
% 6.20/1.14    ( ! [X59,X57,X58] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X57,X58),X59),X57) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X59,X57))) )),
% 6.20/1.14    inference(superposition,[],[f34,f445])).
% 6.20/1.14  fof(f1129,plain,(
% 6.20/1.14    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK0)),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 6.20/1.14    inference(backward_demodulation,[],[f46,f1128])).
% 6.20/1.14  fof(f1128,plain,(
% 6.20/1.14    ( ! [X45,X46,X44] : (k4_xboole_0(k2_xboole_0(X44,X45),k4_xboole_0(X46,X44)) = k2_xboole_0(X44,k4_xboole_0(k2_xboole_0(X44,X45),X46))) )),
% 6.20/1.14    inference(forward_demodulation,[],[f1127,f24])).
% 6.20/1.14  fof(f1127,plain,(
% 6.20/1.14    ( ! [X45,X46,X44] : (k4_xboole_0(k2_xboole_0(X44,X45),k4_xboole_0(X46,X44)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X44,X45),X46),X44)) )),
% 6.20/1.14    inference(forward_demodulation,[],[f1008,f164])).
% 6.20/1.14  fof(f1008,plain,(
% 6.20/1.14    ( ! [X45,X46,X44] : (k4_xboole_0(k2_xboole_0(X44,X45),k4_xboole_0(X46,X44)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X44,X45),X46),k4_xboole_0(k2_xboole_0(X44,X45),k4_xboole_0(X45,X44)))) )),
% 6.20/1.14    inference(superposition,[],[f41,f50])).
% 6.20/1.14  fof(f46,plain,(
% 6.20/1.14    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 6.20/1.14    inference(forward_demodulation,[],[f45,f26])).
% 6.20/1.14  fof(f45,plain,(
% 6.20/1.14    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 6.20/1.14    inference(backward_demodulation,[],[f43,f44])).
% 6.20/1.14  fof(f43,plain,(
% 6.20/1.14    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))))),
% 6.20/1.14    inference(backward_demodulation,[],[f35,f39])).
% 6.20/1.14  fof(f35,plain,(
% 6.20/1.14    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 6.20/1.14    inference(definition_unfolding,[],[f20,f29,f29,f25])).
% 6.20/1.14  fof(f29,plain,(
% 6.20/1.14    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 6.20/1.14    inference(cnf_transformation,[],[f3])).
% 6.20/1.14  fof(f3,axiom,(
% 6.20/1.14    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 6.20/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 6.20/1.14  fof(f20,plain,(
% 6.20/1.14    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 6.20/1.14    inference(cnf_transformation,[],[f19])).
% 6.20/1.14  fof(f19,plain,(
% 6.20/1.14    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 6.20/1.14    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 6.20/1.14  fof(f18,plain,(
% 6.20/1.14    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 6.20/1.14    introduced(choice_axiom,[])).
% 6.20/1.14  fof(f17,plain,(
% 6.20/1.14    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 6.20/1.14    inference(ennf_transformation,[],[f16])).
% 6.20/1.14  fof(f16,negated_conjecture,(
% 6.20/1.14    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 6.20/1.14    inference(negated_conjecture,[],[f15])).
% 6.20/1.14  fof(f15,conjecture,(
% 6.20/1.14    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 6.20/1.14    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 6.20/1.14  % SZS output end Proof for theBenchmark
% 6.20/1.14  % (31423)------------------------------
% 6.20/1.14  % (31423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.20/1.14  % (31423)Termination reason: Refutation
% 6.20/1.14  
% 6.20/1.14  % (31423)Memory used [KB]: 13176
% 6.20/1.14  % (31423)Time elapsed: 0.755 s
% 6.20/1.14  % (31423)------------------------------
% 6.20/1.14  % (31423)------------------------------
% 6.20/1.14  % (31421)Success in time 0.827 s
%------------------------------------------------------------------------------
