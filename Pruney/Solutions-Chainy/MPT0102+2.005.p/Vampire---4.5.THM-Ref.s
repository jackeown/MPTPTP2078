%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:56 EST 2020

% Result     : Theorem 8.66s
% Output     : Refutation 8.66s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 701 expanded)
%              Number of leaves         :   16 ( 239 expanded)
%              Depth                    :   24
%              Number of atoms          :  101 ( 702 expanded)
%              Number of equality atoms :  100 ( 701 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20078,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f20077])).

fof(f20077,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f18920,f48])).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f28,f25])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f18920,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f1952,f18917])).

fof(f18917,plain,(
    ! [X101,X102] : k4_xboole_0(X101,k4_xboole_0(X101,X102)) = k4_xboole_0(k2_xboole_0(X101,X102),k2_xboole_0(k4_xboole_0(X101,X102),k4_xboole_0(X102,X101))) ),
    inference(forward_demodulation,[],[f18916,f1483])).

fof(f1483,plain,(
    ! [X28,X29,X27] : k4_xboole_0(X29,k2_xboole_0(k4_xboole_0(X29,X27),k4_xboole_0(X28,X27))) = k4_xboole_0(X29,k4_xboole_0(X29,X27)) ),
    inference(superposition,[],[f47,f1425])).

fof(f1425,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k4_xboole_0(X10,X9)) = X9 ),
    inference(forward_demodulation,[],[f1372,f24])).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f1372,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k1_xboole_0) = k4_xboole_0(X9,k4_xboole_0(X10,X9)) ),
    inference(superposition,[],[f42,f1328])).

fof(f1328,plain,(
    ! [X10,X11] : k1_xboole_0 = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X10,X11))) ),
    inference(forward_demodulation,[],[f1309,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f39,f24])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f23,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f1309,plain,(
    ! [X10,X11] : k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X10,X11))) = k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X10,X11)) ),
    inference(superposition,[],[f40,f1234])).

fof(f1234,plain,(
    ! [X10,X9] : k4_xboole_0(X9,X10) = k4_xboole_0(k4_xboole_0(X9,X10),X10) ),
    inference(forward_demodulation,[],[f1233,f24])).

fof(f1233,plain,(
    ! [X10,X9] : k4_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X9,X10),X10) ),
    inference(forward_demodulation,[],[f1232,f25])).

fof(f1232,plain,(
    ! [X10,X9] : k4_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X10,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1231,f97])).

fof(f97,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f83,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f82,f46])).

fof(f82,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f63,f26])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f63,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f36,f46])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f83,plain,(
    ! [X2,X1] : k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f63,f28])).

fof(f1231,plain,(
    ! [X10,X9] : k4_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X10,k4_xboole_0(X9,k2_xboole_0(X10,X9)))) ),
    inference(forward_demodulation,[],[f1230,f36])).

fof(f1230,plain,(
    ! [X10,X9] : k4_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X10,k4_xboole_0(k4_xboole_0(X9,X10),X9))) ),
    inference(forward_demodulation,[],[f1144,f28])).

fof(f1144,plain,(
    ! [X10,X9] : k4_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(k4_xboole_0(k4_xboole_0(X9,X10),X9),X10)) ),
    inference(superposition,[],[f47,f46])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f30,f30])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f47,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(backward_demodulation,[],[f45,f36])).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f35,f30,f30])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f18916,plain,(
    ! [X101,X102] : k4_xboole_0(k2_xboole_0(X101,X102),k2_xboole_0(k4_xboole_0(X101,X102),k4_xboole_0(X102,X101))) = k4_xboole_0(X101,k2_xboole_0(k4_xboole_0(X101,X102),k4_xboole_0(X101,X102))) ),
    inference(forward_demodulation,[],[f18783,f16582])).

fof(f16582,plain,(
    ! [X163,X161,X164,X162] : k4_xboole_0(k4_xboole_0(X162,X163),k2_xboole_0(X164,k4_xboole_0(X161,X162))) = k4_xboole_0(X162,k2_xboole_0(X163,X164)) ),
    inference(forward_demodulation,[],[f16443,f36])).

fof(f16443,plain,(
    ! [X163,X161,X164,X162] : k4_xboole_0(k4_xboole_0(X162,X163),X164) = k4_xboole_0(k4_xboole_0(X162,X163),k2_xboole_0(X164,k4_xboole_0(X161,X162))) ),
    inference(superposition,[],[f5671,f11861])).

fof(f11861,plain,(
    ! [X111,X112,X110] : k4_xboole_0(X110,X111) = k4_xboole_0(k4_xboole_0(X110,X111),k4_xboole_0(X111,X112)) ),
    inference(forward_demodulation,[],[f11646,f1513])).

fof(f1513,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2))) = X3 ),
    inference(superposition,[],[f1464,f28])).

fof(f1464,plain,(
    ! [X39,X37,X38] : k4_xboole_0(X39,k4_xboole_0(X37,k2_xboole_0(X38,X39))) = X39 ),
    inference(superposition,[],[f1425,f36])).

fof(f11646,plain,(
    ! [X111,X112,X110] : k4_xboole_0(k4_xboole_0(X110,X111),k4_xboole_0(X111,X112)) = k4_xboole_0(k4_xboole_0(X110,X111),k4_xboole_0(k4_xboole_0(X110,X111),k2_xboole_0(k4_xboole_0(X110,X111),X112))) ),
    inference(superposition,[],[f1229,f1234])).

fof(f1229,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X6,k4_xboole_0(X7,X8)) = k4_xboole_0(X6,k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X6,X7),X8))) ),
    inference(forward_demodulation,[],[f1228,f48])).

fof(f1228,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X6,k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X6,X7),X8))) = k4_xboole_0(X6,k2_xboole_0(k1_xboole_0,k4_xboole_0(X7,X8))) ),
    inference(forward_demodulation,[],[f1143,f46])).

fof(f1143,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X6,X6),k4_xboole_0(X7,X8))) = k4_xboole_0(X6,k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X6,X7),X8))) ),
    inference(superposition,[],[f47,f47])).

fof(f5671,plain,(
    ! [X35,X33,X34] : k4_xboole_0(X33,X35) = k4_xboole_0(X33,k2_xboole_0(X35,k4_xboole_0(X34,X33))) ),
    inference(superposition,[],[f3130,f1425])).

fof(f3130,plain,(
    ! [X17,X15,X16] : k4_xboole_0(k4_xboole_0(X15,X16),X17) = k4_xboole_0(X15,k2_xboole_0(X17,X16)) ),
    inference(forward_demodulation,[],[f3071,f3125])).

fof(f3125,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X6,k2_xboole_0(X7,X8)) = k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X6)),X7)) ),
    inference(forward_demodulation,[],[f3124,f36])).

fof(f3124,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k4_xboole_0(X6,X7),X8) = k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X6)),X7)) ),
    inference(forward_demodulation,[],[f3123,f2063])).

fof(f2063,plain,(
    ! [X43,X41,X42] : k2_xboole_0(k4_xboole_0(X41,X42),X43) = k2_xboole_0(X43,k4_xboole_0(X41,k2_xboole_0(X42,X43))) ),
    inference(superposition,[],[f1984,f36])).

fof(f1984,plain,(
    ! [X6,X5] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f1949,f28])).

fof(f1949,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X2,X3),X3) ),
    inference(forward_demodulation,[],[f1706,f771])).

fof(f771,plain,(
    ! [X14,X13] : k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X14,k4_xboole_0(X14,X13))) = X13 ),
    inference(forward_demodulation,[],[f742,f521])).

fof(f521,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f42,f40])).

fof(f742,plain,(
    ! [X14,X13] : k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(X14,X13))),k4_xboole_0(X14,k4_xboole_0(X14,X13))) = X13 ),
    inference(superposition,[],[f43,f40])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f1706,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X2,X3),k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(superposition,[],[f44,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f34,f33,f30])).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f3123,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k4_xboole_0(X6,X7),X8) = k4_xboole_0(X6,k2_xboole_0(X7,k4_xboole_0(X8,k2_xboole_0(k4_xboole_0(X8,X6),X7)))) ),
    inference(forward_demodulation,[],[f3059,f47])).

fof(f3059,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k4_xboole_0(X6,X7),X8) = k4_xboole_0(X6,k2_xboole_0(X7,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,X7))))) ),
    inference(superposition,[],[f521,f36])).

fof(f3071,plain,(
    ! [X17,X15,X16] : k4_xboole_0(k4_xboole_0(X15,X16),X17) = k4_xboole_0(X15,k2_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X15)),X17)) ),
    inference(superposition,[],[f36,f521])).

fof(f18783,plain,(
    ! [X101,X102] : k4_xboole_0(k4_xboole_0(X101,k4_xboole_0(X101,X102)),k2_xboole_0(k4_xboole_0(X101,X102),k4_xboole_0(X102,X101))) = k4_xboole_0(k2_xboole_0(X101,X102),k2_xboole_0(k4_xboole_0(X101,X102),k4_xboole_0(X102,X101))) ),
    inference(superposition,[],[f18237,f44])).

fof(f18237,plain,(
    ! [X39,X40] : k4_xboole_0(X40,X39) = k4_xboole_0(k2_xboole_0(X39,X40),X39) ),
    inference(forward_demodulation,[],[f18236,f42])).

fof(f18236,plain,(
    ! [X39,X40] : k4_xboole_0(X40,k4_xboole_0(X40,k4_xboole_0(X40,X39))) = k4_xboole_0(k2_xboole_0(X39,X40),X39) ),
    inference(forward_demodulation,[],[f18235,f11798])).

fof(f11798,plain,(
    ! [X6,X7,X5] : k4_xboole_0(X5,k4_xboole_0(X5,X7)) = k4_xboole_0(X5,k4_xboole_0(k2_xboole_0(X6,X5),X7)) ),
    inference(forward_demodulation,[],[f11617,f48])).

fof(f11617,plain,(
    ! [X6,X7,X5] : k4_xboole_0(X5,k4_xboole_0(k2_xboole_0(X6,X5),X7)) = k4_xboole_0(X5,k4_xboole_0(X5,k2_xboole_0(k1_xboole_0,X7))) ),
    inference(superposition,[],[f1229,f97])).

fof(f18235,plain,(
    ! [X39,X40] : k4_xboole_0(k2_xboole_0(X39,X40),X39) = k4_xboole_0(X40,k4_xboole_0(X40,k4_xboole_0(k2_xboole_0(X39,X40),X39))) ),
    inference(forward_demodulation,[],[f17839,f24])).

fof(f17839,plain,(
    ! [X39,X40] : k4_xboole_0(X40,k4_xboole_0(X40,k4_xboole_0(k2_xboole_0(X39,X40),X39))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X39,X40),X39),k1_xboole_0) ),
    inference(superposition,[],[f278,f46])).

fof(f278,plain,(
    ! [X17,X15,X16] : k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X15,X16))) = k4_xboole_0(k4_xboole_0(X15,X16),k4_xboole_0(X15,k2_xboole_0(X16,X17))) ),
    inference(superposition,[],[f40,f36])).

fof(f1952,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(backward_demodulation,[],[f38,f1713])).

fof(f1713,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X10,X9)),k2_xboole_0(X9,X10)) ),
    inference(superposition,[],[f94,f44])).

fof(f94,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f63,f92])).

fof(f38,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f22,f30,f33,f33])).

fof(f22,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (26807)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.43  % (26809)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (26802)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (26801)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (26814)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (26800)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (26808)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (26806)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (26812)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (26803)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (26805)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (26796)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (26797)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (26810)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (26811)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (26813)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (26804)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (26799)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (26808)Refutation not found, incomplete strategy% (26808)------------------------------
% 0.21/0.50  % (26808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26808)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (26808)Memory used [KB]: 10490
% 0.21/0.50  % (26808)Time elapsed: 0.105 s
% 0.21/0.50  % (26808)------------------------------
% 0.21/0.50  % (26808)------------------------------
% 4.93/1.02  % (26801)Time limit reached!
% 4.93/1.02  % (26801)------------------------------
% 4.93/1.02  % (26801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.93/1.03  % (26801)Termination reason: Time limit
% 4.93/1.03  % (26801)Termination phase: Saturation
% 4.93/1.03  
% 4.93/1.03  % (26801)Memory used [KB]: 16247
% 4.93/1.03  % (26801)Time elapsed: 0.600 s
% 4.93/1.03  % (26801)------------------------------
% 4.93/1.03  % (26801)------------------------------
% 8.66/1.50  % (26797)Refutation found. Thanks to Tanya!
% 8.66/1.50  % SZS status Theorem for theBenchmark
% 8.66/1.50  % SZS output start Proof for theBenchmark
% 8.66/1.50  fof(f20078,plain,(
% 8.66/1.50    $false),
% 8.66/1.50    inference(trivial_inequality_removal,[],[f20077])).
% 8.66/1.50  fof(f20077,plain,(
% 8.66/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 8.66/1.50    inference(superposition,[],[f18920,f48])).
% 8.66/1.50  fof(f48,plain,(
% 8.66/1.50    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 8.66/1.50    inference(superposition,[],[f28,f25])).
% 8.66/1.50  fof(f25,plain,(
% 8.66/1.50    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.66/1.50    inference(cnf_transformation,[],[f5])).
% 8.66/1.50  fof(f5,axiom,(
% 8.66/1.50    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 8.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 8.66/1.50  fof(f28,plain,(
% 8.66/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 8.66/1.50    inference(cnf_transformation,[],[f1])).
% 8.66/1.50  fof(f1,axiom,(
% 8.66/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 8.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 8.66/1.50  fof(f18920,plain,(
% 8.66/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 8.66/1.50    inference(backward_demodulation,[],[f1952,f18917])).
% 8.66/1.50  fof(f18917,plain,(
% 8.66/1.50    ( ! [X101,X102] : (k4_xboole_0(X101,k4_xboole_0(X101,X102)) = k4_xboole_0(k2_xboole_0(X101,X102),k2_xboole_0(k4_xboole_0(X101,X102),k4_xboole_0(X102,X101)))) )),
% 8.66/1.50    inference(forward_demodulation,[],[f18916,f1483])).
% 8.66/1.50  fof(f1483,plain,(
% 8.66/1.50    ( ! [X28,X29,X27] : (k4_xboole_0(X29,k2_xboole_0(k4_xboole_0(X29,X27),k4_xboole_0(X28,X27))) = k4_xboole_0(X29,k4_xboole_0(X29,X27))) )),
% 8.66/1.50    inference(superposition,[],[f47,f1425])).
% 8.66/1.50  fof(f1425,plain,(
% 8.66/1.50    ( ! [X10,X9] : (k4_xboole_0(X9,k4_xboole_0(X10,X9)) = X9) )),
% 8.66/1.50    inference(forward_demodulation,[],[f1372,f24])).
% 8.66/1.50  fof(f24,plain,(
% 8.66/1.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.66/1.50    inference(cnf_transformation,[],[f8])).
% 8.66/1.50  fof(f8,axiom,(
% 8.66/1.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 8.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 8.66/1.50  fof(f1372,plain,(
% 8.66/1.50    ( ! [X10,X9] : (k4_xboole_0(X9,k1_xboole_0) = k4_xboole_0(X9,k4_xboole_0(X10,X9))) )),
% 8.66/1.50    inference(superposition,[],[f42,f1328])).
% 8.66/1.50  fof(f1328,plain,(
% 8.66/1.50    ( ! [X10,X11] : (k1_xboole_0 = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X10,X11)))) )),
% 8.66/1.50    inference(forward_demodulation,[],[f1309,f46])).
% 8.66/1.50  fof(f46,plain,(
% 8.66/1.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 8.66/1.50    inference(backward_demodulation,[],[f39,f24])).
% 8.66/1.50  fof(f39,plain,(
% 8.66/1.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 8.66/1.50    inference(definition_unfolding,[],[f23,f30])).
% 8.66/1.50  fof(f30,plain,(
% 8.66/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 8.66/1.50    inference(cnf_transformation,[],[f11])).
% 8.66/1.50  fof(f11,axiom,(
% 8.66/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 8.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 8.66/1.50  fof(f23,plain,(
% 8.66/1.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 8.66/1.50    inference(cnf_transformation,[],[f7])).
% 8.66/1.50  fof(f7,axiom,(
% 8.66/1.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 8.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 8.66/1.50  fof(f1309,plain,(
% 8.66/1.50    ( ! [X10,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X10,X11))) = k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X10,X11))) )),
% 8.66/1.50    inference(superposition,[],[f40,f1234])).
% 8.66/1.50  fof(f1234,plain,(
% 8.66/1.50    ( ! [X10,X9] : (k4_xboole_0(X9,X10) = k4_xboole_0(k4_xboole_0(X9,X10),X10)) )),
% 8.66/1.50    inference(forward_demodulation,[],[f1233,f24])).
% 8.66/1.50  fof(f1233,plain,(
% 8.66/1.50    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X9,X10),X10)) )),
% 8.66/1.50    inference(forward_demodulation,[],[f1232,f25])).
% 8.66/1.50  fof(f1232,plain,(
% 8.66/1.50    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X10,k1_xboole_0))) )),
% 8.66/1.50    inference(forward_demodulation,[],[f1231,f97])).
% 8.66/1.50  fof(f97,plain,(
% 8.66/1.50    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 8.66/1.50    inference(forward_demodulation,[],[f83,f92])).
% 8.66/1.50  fof(f92,plain,(
% 8.66/1.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 8.66/1.50    inference(forward_demodulation,[],[f82,f46])).
% 8.66/1.50  fof(f82,plain,(
% 8.66/1.50    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0)) )),
% 8.66/1.50    inference(superposition,[],[f63,f26])).
% 8.66/1.50  fof(f26,plain,(
% 8.66/1.50    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 8.66/1.50    inference(cnf_transformation,[],[f18])).
% 8.66/1.50  fof(f18,plain,(
% 8.66/1.50    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 8.66/1.50    inference(rectify,[],[f4])).
% 8.66/1.50  fof(f4,axiom,(
% 8.66/1.50    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 8.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 8.66/1.50  fof(f63,plain,(
% 8.66/1.50    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) )),
% 8.66/1.50    inference(superposition,[],[f36,f46])).
% 8.66/1.50  fof(f36,plain,(
% 8.66/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 8.66/1.50    inference(cnf_transformation,[],[f9])).
% 8.66/1.50  fof(f9,axiom,(
% 8.66/1.50    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 8.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 8.66/1.50  fof(f83,plain,(
% 8.66/1.50    ( ! [X2,X1] : (k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 8.66/1.50    inference(superposition,[],[f63,f28])).
% 8.66/1.50  fof(f1231,plain,(
% 8.66/1.50    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X10,k4_xboole_0(X9,k2_xboole_0(X10,X9))))) )),
% 8.66/1.50    inference(forward_demodulation,[],[f1230,f36])).
% 8.66/1.50  fof(f1230,plain,(
% 8.66/1.50    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X10,k4_xboole_0(k4_xboole_0(X9,X10),X9)))) )),
% 8.66/1.50    inference(forward_demodulation,[],[f1144,f28])).
% 8.66/1.50  fof(f1144,plain,(
% 8.66/1.50    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(k4_xboole_0(k4_xboole_0(X9,X10),X9),X10))) )),
% 8.66/1.50    inference(superposition,[],[f47,f46])).
% 8.66/1.50  fof(f40,plain,(
% 8.66/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 8.66/1.50    inference(definition_unfolding,[],[f27,f30,f30])).
% 8.66/1.50  fof(f27,plain,(
% 8.66/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 8.66/1.50    inference(cnf_transformation,[],[f2])).
% 8.66/1.50  fof(f2,axiom,(
% 8.66/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 8.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 8.66/1.50  fof(f42,plain,(
% 8.66/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 8.66/1.50    inference(definition_unfolding,[],[f31,f30])).
% 8.66/1.50  fof(f31,plain,(
% 8.66/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.66/1.50    inference(cnf_transformation,[],[f10])).
% 8.66/1.50  fof(f10,axiom,(
% 8.66/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 8.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 8.66/1.50  fof(f47,plain,(
% 8.66/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 8.66/1.50    inference(backward_demodulation,[],[f45,f36])).
% 8.66/1.50  fof(f45,plain,(
% 8.66/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 8.66/1.50    inference(definition_unfolding,[],[f35,f30,f30])).
% 8.66/1.50  fof(f35,plain,(
% 8.66/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 8.66/1.50    inference(cnf_transformation,[],[f12])).
% 8.66/1.50  fof(f12,axiom,(
% 8.66/1.50    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 8.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 8.66/1.50  fof(f18916,plain,(
% 8.66/1.50    ( ! [X101,X102] : (k4_xboole_0(k2_xboole_0(X101,X102),k2_xboole_0(k4_xboole_0(X101,X102),k4_xboole_0(X102,X101))) = k4_xboole_0(X101,k2_xboole_0(k4_xboole_0(X101,X102),k4_xboole_0(X101,X102)))) )),
% 8.66/1.50    inference(forward_demodulation,[],[f18783,f16582])).
% 8.66/1.50  fof(f16582,plain,(
% 8.66/1.50    ( ! [X163,X161,X164,X162] : (k4_xboole_0(k4_xboole_0(X162,X163),k2_xboole_0(X164,k4_xboole_0(X161,X162))) = k4_xboole_0(X162,k2_xboole_0(X163,X164))) )),
% 8.66/1.50    inference(forward_demodulation,[],[f16443,f36])).
% 8.66/1.50  fof(f16443,plain,(
% 8.66/1.50    ( ! [X163,X161,X164,X162] : (k4_xboole_0(k4_xboole_0(X162,X163),X164) = k4_xboole_0(k4_xboole_0(X162,X163),k2_xboole_0(X164,k4_xboole_0(X161,X162)))) )),
% 8.66/1.50    inference(superposition,[],[f5671,f11861])).
% 8.66/1.50  fof(f11861,plain,(
% 8.66/1.50    ( ! [X111,X112,X110] : (k4_xboole_0(X110,X111) = k4_xboole_0(k4_xboole_0(X110,X111),k4_xboole_0(X111,X112))) )),
% 8.66/1.50    inference(forward_demodulation,[],[f11646,f1513])).
% 8.66/1.50  fof(f1513,plain,(
% 8.66/1.50    ( ! [X4,X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2))) = X3) )),
% 8.66/1.50    inference(superposition,[],[f1464,f28])).
% 8.66/1.50  fof(f1464,plain,(
% 8.66/1.50    ( ! [X39,X37,X38] : (k4_xboole_0(X39,k4_xboole_0(X37,k2_xboole_0(X38,X39))) = X39) )),
% 8.66/1.50    inference(superposition,[],[f1425,f36])).
% 8.66/1.50  fof(f11646,plain,(
% 8.66/1.50    ( ! [X111,X112,X110] : (k4_xboole_0(k4_xboole_0(X110,X111),k4_xboole_0(X111,X112)) = k4_xboole_0(k4_xboole_0(X110,X111),k4_xboole_0(k4_xboole_0(X110,X111),k2_xboole_0(k4_xboole_0(X110,X111),X112)))) )),
% 8.66/1.50    inference(superposition,[],[f1229,f1234])).
% 8.66/1.50  fof(f1229,plain,(
% 8.66/1.50    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k4_xboole_0(X7,X8)) = k4_xboole_0(X6,k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X6,X7),X8)))) )),
% 8.66/1.50    inference(forward_demodulation,[],[f1228,f48])).
% 8.66/1.50  fof(f1228,plain,(
% 8.66/1.50    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X6,X7),X8))) = k4_xboole_0(X6,k2_xboole_0(k1_xboole_0,k4_xboole_0(X7,X8)))) )),
% 8.66/1.50    inference(forward_demodulation,[],[f1143,f46])).
% 8.66/1.50  fof(f1143,plain,(
% 8.66/1.50    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X6,X6),k4_xboole_0(X7,X8))) = k4_xboole_0(X6,k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X6,X7),X8)))) )),
% 8.66/1.50    inference(superposition,[],[f47,f47])).
% 8.66/1.50  fof(f5671,plain,(
% 8.66/1.50    ( ! [X35,X33,X34] : (k4_xboole_0(X33,X35) = k4_xboole_0(X33,k2_xboole_0(X35,k4_xboole_0(X34,X33)))) )),
% 8.66/1.50    inference(superposition,[],[f3130,f1425])).
% 8.66/1.50  fof(f3130,plain,(
% 8.66/1.50    ( ! [X17,X15,X16] : (k4_xboole_0(k4_xboole_0(X15,X16),X17) = k4_xboole_0(X15,k2_xboole_0(X17,X16))) )),
% 8.66/1.50    inference(forward_demodulation,[],[f3071,f3125])).
% 8.66/1.50  fof(f3125,plain,(
% 8.66/1.50    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k2_xboole_0(X7,X8)) = k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X6)),X7))) )),
% 8.66/1.50    inference(forward_demodulation,[],[f3124,f36])).
% 8.66/1.50  fof(f3124,plain,(
% 8.66/1.50    ( ! [X6,X8,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),X8) = k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X6)),X7))) )),
% 8.66/1.50    inference(forward_demodulation,[],[f3123,f2063])).
% 8.66/1.50  fof(f2063,plain,(
% 8.66/1.50    ( ! [X43,X41,X42] : (k2_xboole_0(k4_xboole_0(X41,X42),X43) = k2_xboole_0(X43,k4_xboole_0(X41,k2_xboole_0(X42,X43)))) )),
% 8.66/1.50    inference(superposition,[],[f1984,f36])).
% 8.66/1.50  fof(f1984,plain,(
% 8.66/1.50    ( ! [X6,X5] : (k2_xboole_0(X5,X6) = k2_xboole_0(X6,k4_xboole_0(X5,X6))) )),
% 8.66/1.50    inference(superposition,[],[f1949,f28])).
% 8.66/1.50  fof(f1949,plain,(
% 8.66/1.50    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X2,X3),X3)) )),
% 8.66/1.50    inference(forward_demodulation,[],[f1706,f771])).
% 8.66/1.50  fof(f771,plain,(
% 8.66/1.50    ( ! [X14,X13] : (k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X14,k4_xboole_0(X14,X13))) = X13) )),
% 8.66/1.50    inference(forward_demodulation,[],[f742,f521])).
% 8.66/1.50  fof(f521,plain,(
% 8.66/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 8.66/1.50    inference(superposition,[],[f42,f40])).
% 8.66/1.50  fof(f742,plain,(
% 8.66/1.50    ( ! [X14,X13] : (k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(X14,X13))),k4_xboole_0(X14,k4_xboole_0(X14,X13))) = X13) )),
% 8.66/1.50    inference(superposition,[],[f43,f40])).
% 8.66/1.50  fof(f43,plain,(
% 8.66/1.50    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 8.66/1.50    inference(definition_unfolding,[],[f32,f30])).
% 8.66/1.50  fof(f32,plain,(
% 8.66/1.50    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 8.66/1.50    inference(cnf_transformation,[],[f14])).
% 8.66/1.50  fof(f14,axiom,(
% 8.66/1.50    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 8.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 8.66/1.50  fof(f1706,plain,(
% 8.66/1.50    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X2,X3),k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,k4_xboole_0(X2,X3))))) )),
% 8.66/1.50    inference(superposition,[],[f44,f37])).
% 8.66/1.50  fof(f37,plain,(
% 8.66/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 8.66/1.50    inference(cnf_transformation,[],[f13])).
% 8.66/1.50  fof(f13,axiom,(
% 8.66/1.50    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 8.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 8.66/1.50  fof(f44,plain,(
% 8.66/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 8.66/1.50    inference(definition_unfolding,[],[f34,f33,f30])).
% 8.66/1.50  fof(f33,plain,(
% 8.66/1.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 8.66/1.50    inference(cnf_transformation,[],[f3])).
% 8.66/1.50  fof(f3,axiom,(
% 8.66/1.50    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 8.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 8.66/1.50  fof(f34,plain,(
% 8.66/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 8.66/1.50    inference(cnf_transformation,[],[f15])).
% 8.66/1.50  fof(f15,axiom,(
% 8.66/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 8.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 8.66/1.50  fof(f3123,plain,(
% 8.66/1.50    ( ! [X6,X8,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),X8) = k4_xboole_0(X6,k2_xboole_0(X7,k4_xboole_0(X8,k2_xboole_0(k4_xboole_0(X8,X6),X7))))) )),
% 8.66/1.50    inference(forward_demodulation,[],[f3059,f47])).
% 8.66/1.50  fof(f3059,plain,(
% 8.66/1.50    ( ! [X6,X8,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),X8) = k4_xboole_0(X6,k2_xboole_0(X7,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,X7)))))) )),
% 8.66/1.50    inference(superposition,[],[f521,f36])).
% 8.66/1.50  fof(f3071,plain,(
% 8.66/1.50    ( ! [X17,X15,X16] : (k4_xboole_0(k4_xboole_0(X15,X16),X17) = k4_xboole_0(X15,k2_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X15)),X17))) )),
% 8.66/1.50    inference(superposition,[],[f36,f521])).
% 8.66/1.50  fof(f18783,plain,(
% 8.66/1.50    ( ! [X101,X102] : (k4_xboole_0(k4_xboole_0(X101,k4_xboole_0(X101,X102)),k2_xboole_0(k4_xboole_0(X101,X102),k4_xboole_0(X102,X101))) = k4_xboole_0(k2_xboole_0(X101,X102),k2_xboole_0(k4_xboole_0(X101,X102),k4_xboole_0(X102,X101)))) )),
% 8.66/1.50    inference(superposition,[],[f18237,f44])).
% 8.66/1.50  fof(f18237,plain,(
% 8.66/1.50    ( ! [X39,X40] : (k4_xboole_0(X40,X39) = k4_xboole_0(k2_xboole_0(X39,X40),X39)) )),
% 8.66/1.50    inference(forward_demodulation,[],[f18236,f42])).
% 8.66/1.50  fof(f18236,plain,(
% 8.66/1.50    ( ! [X39,X40] : (k4_xboole_0(X40,k4_xboole_0(X40,k4_xboole_0(X40,X39))) = k4_xboole_0(k2_xboole_0(X39,X40),X39)) )),
% 8.66/1.50    inference(forward_demodulation,[],[f18235,f11798])).
% 8.66/1.50  fof(f11798,plain,(
% 8.66/1.50    ( ! [X6,X7,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,X7)) = k4_xboole_0(X5,k4_xboole_0(k2_xboole_0(X6,X5),X7))) )),
% 8.66/1.50    inference(forward_demodulation,[],[f11617,f48])).
% 8.66/1.50  fof(f11617,plain,(
% 8.66/1.50    ( ! [X6,X7,X5] : (k4_xboole_0(X5,k4_xboole_0(k2_xboole_0(X6,X5),X7)) = k4_xboole_0(X5,k4_xboole_0(X5,k2_xboole_0(k1_xboole_0,X7)))) )),
% 8.66/1.50    inference(superposition,[],[f1229,f97])).
% 8.66/1.50  fof(f18235,plain,(
% 8.66/1.50    ( ! [X39,X40] : (k4_xboole_0(k2_xboole_0(X39,X40),X39) = k4_xboole_0(X40,k4_xboole_0(X40,k4_xboole_0(k2_xboole_0(X39,X40),X39)))) )),
% 8.66/1.50    inference(forward_demodulation,[],[f17839,f24])).
% 8.66/1.50  fof(f17839,plain,(
% 8.66/1.50    ( ! [X39,X40] : (k4_xboole_0(X40,k4_xboole_0(X40,k4_xboole_0(k2_xboole_0(X39,X40),X39))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X39,X40),X39),k1_xboole_0)) )),
% 8.66/1.50    inference(superposition,[],[f278,f46])).
% 8.66/1.50  fof(f278,plain,(
% 8.66/1.50    ( ! [X17,X15,X16] : (k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X15,X16))) = k4_xboole_0(k4_xboole_0(X15,X16),k4_xboole_0(X15,k2_xboole_0(X16,X17)))) )),
% 8.66/1.50    inference(superposition,[],[f40,f36])).
% 8.66/1.50  fof(f1952,plain,(
% 8.66/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 8.66/1.50    inference(backward_demodulation,[],[f38,f1713])).
% 8.66/1.50  fof(f1713,plain,(
% 8.66/1.50    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X10,X9)),k2_xboole_0(X9,X10))) )),
% 8.66/1.50    inference(superposition,[],[f94,f44])).
% 8.66/1.50  fof(f94,plain,(
% 8.66/1.50    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 8.66/1.50    inference(backward_demodulation,[],[f63,f92])).
% 8.66/1.50  fof(f38,plain,(
% 8.66/1.50    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 8.66/1.50    inference(definition_unfolding,[],[f22,f30,f33,f33])).
% 8.66/1.50  fof(f22,plain,(
% 8.66/1.50    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 8.66/1.50    inference(cnf_transformation,[],[f21])).
% 8.66/1.50  fof(f21,plain,(
% 8.66/1.50    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 8.66/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 8.66/1.50  fof(f20,plain,(
% 8.66/1.50    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 8.66/1.50    introduced(choice_axiom,[])).
% 8.66/1.50  fof(f19,plain,(
% 8.66/1.50    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 8.66/1.50    inference(ennf_transformation,[],[f17])).
% 8.66/1.50  fof(f17,negated_conjecture,(
% 8.66/1.50    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 8.66/1.50    inference(negated_conjecture,[],[f16])).
% 8.66/1.50  fof(f16,conjecture,(
% 8.66/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 8.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 8.66/1.50  % SZS output end Proof for theBenchmark
% 8.66/1.50  % (26797)------------------------------
% 8.66/1.50  % (26797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.66/1.50  % (26797)Termination reason: Refutation
% 8.66/1.50  
% 8.66/1.50  % (26797)Memory used [KB]: 21620
% 8.66/1.50  % (26797)Time elapsed: 1.054 s
% 8.66/1.50  % (26797)------------------------------
% 8.66/1.50  % (26797)------------------------------
% 8.66/1.51  % (26795)Success in time 1.139 s
%------------------------------------------------------------------------------
