%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:00 EST 2020

% Result     : Theorem 17.78s
% Output     : Refutation 17.78s
% Verified   : 
% Statistics : Number of formulae       :  144 (4569 expanded)
%              Number of leaves         :   22 (1523 expanded)
%              Depth                    :   31
%              Number of atoms          :  146 (4571 expanded)
%              Number of equality atoms :  145 (4570 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23549,plain,(
    $false ),
    inference(subsumption_resolution,[],[f23548,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f23548,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(forward_demodulation,[],[f23547,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f23547,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) ),
    inference(superposition,[],[f23247,f1346])).

fof(f1346,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5)) ),
    inference(forward_demodulation,[],[f1333,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f1333,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5)) ),
    inference(superposition,[],[f164,f35])).

fof(f164,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f158,f35])).

fof(f158,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(superposition,[],[f40,f35])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f23247,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(superposition,[],[f27,f20048])).

fof(f20048,plain,(
    ! [X111,X114,X112,X113] : k2_enumset1(X114,X112,X111,X113) = k2_enumset1(X114,X111,X112,X113) ),
    inference(superposition,[],[f19143,f6785])).

fof(f6785,plain,(
    ! [X37,X35,X38,X36] : k2_enumset1(X35,X36,X37,X38) = k2_enumset1(X38,X35,X36,X37) ),
    inference(superposition,[],[f3289,f3529])).

fof(f3529,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X1,X2,X3,X0,X0) ),
    inference(forward_demodulation,[],[f3515,f3272])).

fof(f3272,plain,(
    ! [X17,X15,X18,X16] : k2_xboole_0(k1_tarski(X15),k1_enumset1(X16,X17,X18)) = k2_enumset1(X16,X17,X18,X15) ),
    inference(forward_demodulation,[],[f3271,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f3271,plain,(
    ! [X17,X15,X18,X16] : k2_xboole_0(k1_tarski(X15),k2_enumset1(X16,X16,X17,X18)) = k2_enumset1(X16,X17,X18,X15) ),
    inference(forward_demodulation,[],[f3249,f1414])).

fof(f1414,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X1,X2,X3,X0,X0) ),
    inference(forward_demodulation,[],[f1399,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f1399,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k4_enumset1(X0,X1,X2,X3,X0,X0) ),
    inference(superposition,[],[f1374,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f1374,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X1,X2,X3,X4,X0,X0) ),
    inference(forward_demodulation,[],[f1350,f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f1350,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k5_enumset1(X0,X1,X2,X3,X4,X0,X0) ),
    inference(superposition,[],[f796,f42])).

fof(f796,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X5,X0,X0,X1,X2,X3,X4) = k5_enumset1(X0,X1,X2,X3,X4,X5,X5) ),
    inference(superposition,[],[f258,f205])).

fof(f205,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(forward_demodulation,[],[f194,f43])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

fof(f194,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(superposition,[],[f44,f28])).

fof(f28,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

fof(f258,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X0) ),
    inference(forward_demodulation,[],[f246,f140])).

fof(f140,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k2_xboole_0(k4_enumset1(X8,X9,X10,X11,X12,X13),k1_tarski(X7)) = k5_enumset1(X7,X8,X9,X10,X11,X12,X13) ),
    inference(superposition,[],[f43,f56])).

fof(f56,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f51,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f51,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f30,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f246,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0)) = k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X0) ),
    inference(superposition,[],[f45,f28])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

fof(f3249,plain,(
    ! [X17,X15,X18,X16] : k2_xboole_0(k1_tarski(X15),k2_enumset1(X16,X16,X17,X18)) = k4_enumset1(X16,X17,X18,X15,X16,X16) ),
    inference(superposition,[],[f3169,f782])).

fof(f782,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X4,X0,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f139,f39])).

fof(f139,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X5,X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(superposition,[],[f43,f41])).

fof(f3169,plain,(
    ! [X6,X10,X8,X7,X11,X9] : k5_enumset1(X8,X9,X10,X11,X11,X6,X7) = k4_enumset1(X11,X6,X7,X8,X9,X10) ),
    inference(backward_demodulation,[],[f832,f3168])).

fof(f3168,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X3,X3,X4,X5) ),
    inference(forward_demodulation,[],[f3152,f42])).

fof(f3152,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X3,X3,X4,X5) ),
    inference(superposition,[],[f853,f205])).

fof(f853,plain,(
    ! [X21,X19,X17,X15,X20,X18,X16] : k6_enumset1(X15,X16,X17,X18,X19,X19,X20,X21) = k5_enumset1(X15,X16,X17,X18,X19,X20,X21) ),
    inference(forward_demodulation,[],[f851,f205])).

fof(f851,plain,(
    ! [X21,X19,X17,X15,X20,X18,X16] : k6_enumset1(X15,X16,X17,X18,X19,X19,X20,X21) = k6_enumset1(X15,X15,X16,X17,X18,X19,X20,X21) ),
    inference(superposition,[],[f450,f446])).

fof(f446,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(forward_demodulation,[],[f434,f45])).

fof(f434,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(superposition,[],[f49,f42])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).

fof(f450,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X3,X4,X5,X6,X7,X0,X0,X1,X2) = k6_enumset1(X3,X4,X5,X6,X7,X0,X1,X2) ),
    inference(backward_demodulation,[],[f329,f447])).

fof(f447,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(backward_demodulation,[],[f369,f446])).

fof(f369,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(superposition,[],[f48,f41])).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).

fof(f329,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k1_enumset1(X0,X1,X2)) = k7_enumset1(X3,X4,X5,X6,X7,X0,X0,X1,X2) ),
    inference(superposition,[],[f47,f36])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

fof(f832,plain,(
    ! [X6,X10,X8,X7,X11,X9] : k5_enumset1(X11,X6,X7,X8,X8,X9,X10) = k5_enumset1(X8,X9,X10,X11,X11,X6,X7) ),
    inference(superposition,[],[f820,f258])).

fof(f820,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X5,X6,X0,X0,X1,X2,X3,X4) ),
    inference(backward_demodulation,[],[f200,f815])).

fof(f815,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k5_enumset1(X7,X8,X9,X10,X11,X12,X13) = k2_xboole_0(k2_tarski(X12,X13),k3_enumset1(X7,X8,X9,X10,X11)) ),
    inference(superposition,[],[f257,f56])).

fof(f257,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(forward_demodulation,[],[f245,f205])).

fof(f245,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(superposition,[],[f45,f41])).

fof(f200,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X5,X6,X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X5,X6),k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(superposition,[],[f44,f41])).

fof(f3515,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X1,X2,X3,X0,X0) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f3455,f36])).

fof(f3455,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3)) = k3_enumset1(X2,X3,X4,X0,X1) ),
    inference(backward_demodulation,[],[f3421,f3449])).

fof(f3449,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X2,X3,X4,X0,X0,X1) = k3_enumset1(X2,X3,X4,X0,X1) ),
    inference(backward_demodulation,[],[f3246,f3426])).

fof(f3426,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X3,X4,X0,X0,X1,X2) ),
    inference(superposition,[],[f3360,f789])).

fof(f789,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(forward_demodulation,[],[f781,f41])).

fof(f781,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(superposition,[],[f139,f42])).

fof(f3360,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X5),k3_enumset1(X0,X1,X2,X3,X4)) = k4_enumset1(X3,X4,X5,X0,X1,X2) ),
    inference(backward_demodulation,[],[f139,f3358])).

fof(f3358,plain,(
    ! [X30,X28,X26,X29,X27,X25] : k4_enumset1(X25,X26,X27,X28,X29,X30) = k5_enumset1(X27,X28,X28,X29,X30,X25,X26) ),
    inference(backward_demodulation,[],[f3154,f3357])).

fof(f3357,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X2,X3,X4,X5) ),
    inference(forward_demodulation,[],[f3339,f42])).

fof(f3339,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X2,X3,X4,X5) ),
    inference(superposition,[],[f866,f205])).

fof(f866,plain,(
    ! [X28,X26,X24,X23,X27,X25,X22] : k6_enumset1(X22,X23,X24,X25,X25,X26,X27,X28) = k5_enumset1(X22,X23,X24,X25,X26,X27,X28) ),
    inference(forward_demodulation,[],[f862,f205])).

fof(f862,plain,(
    ! [X28,X26,X24,X23,X27,X25,X22] : k6_enumset1(X22,X23,X24,X25,X25,X26,X27,X28) = k6_enumset1(X22,X22,X23,X24,X25,X26,X27,X28) ),
    inference(superposition,[],[f451,f446])).

fof(f451,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X4,X5,X6,X7,X0,X0,X1,X2,X3) = k6_enumset1(X4,X5,X6,X7,X0,X1,X2,X3) ),
    inference(backward_demodulation,[],[f283,f448])).

fof(f448,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(backward_demodulation,[],[f328,f446])).

fof(f328,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(superposition,[],[f47,f39])).

fof(f283,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X4,X5,X6,X7,X0,X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X4,X5,X6,X7),k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f46,f39])).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l142_enumset1)).

fof(f3154,plain,(
    ! [X30,X28,X26,X29,X27,X25] : k5_enumset1(X27,X28,X28,X29,X30,X25,X26) = k5_enumset1(X25,X26,X27,X27,X28,X29,X30) ),
    inference(superposition,[],[f853,f820])).

fof(f3246,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X1,X2,X2,X3,X4) = k4_enumset1(X2,X3,X4,X0,X0,X1) ),
    inference(superposition,[],[f3169,f42])).

fof(f3421,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3)) = k4_enumset1(X2,X3,X4,X0,X0,X1) ),
    inference(superposition,[],[f3360,f39])).

fof(f3289,plain,(
    ! [X21,X19,X22,X20] : k3_enumset1(X19,X20,X21,X22,X22) = k2_enumset1(X19,X20,X21,X22) ),
    inference(backward_demodulation,[],[f1359,f3274])).

fof(f3274,plain,(
    ! [X19,X17,X20,X18] : k5_enumset1(X20,X17,X17,X17,X17,X18,X19) = k2_enumset1(X17,X18,X19,X20) ),
    inference(backward_demodulation,[],[f1608,f3272])).

fof(f1608,plain,(
    ! [X19,X17,X20,X18] : k5_enumset1(X20,X17,X17,X17,X17,X18,X19) = k2_xboole_0(k1_tarski(X20),k1_enumset1(X17,X18,X19)) ),
    inference(superposition,[],[f139,f1418])).

fof(f1418,plain,(
    ! [X6,X4,X5] : k1_enumset1(X4,X5,X6) = k3_enumset1(X4,X4,X4,X5,X6) ),
    inference(forward_demodulation,[],[f1406,f1416])).

fof(f1416,plain,(
    ! [X17,X15,X16] : k1_enumset1(X15,X16,X17) = k3_enumset1(X15,X16,X17,X15,X15) ),
    inference(forward_demodulation,[],[f1415,f36])).

fof(f1415,plain,(
    ! [X17,X15,X16] : k3_enumset1(X15,X16,X17,X15,X15) = k2_enumset1(X15,X15,X16,X17) ),
    inference(forward_demodulation,[],[f1403,f39])).

fof(f1403,plain,(
    ! [X17,X15,X16] : k3_enumset1(X15,X16,X17,X15,X15) = k3_enumset1(X15,X15,X15,X16,X17) ),
    inference(superposition,[],[f1374,f792])).

fof(f792,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(superposition,[],[f789,f139])).

fof(f1406,plain,(
    ! [X6,X4,X5] : k3_enumset1(X4,X4,X4,X5,X6) = k3_enumset1(X4,X5,X6,X4,X4) ),
    inference(superposition,[],[f792,f1374])).

fof(f1359,plain,(
    ! [X21,X19,X22,X20] : k3_enumset1(X19,X20,X21,X22,X22) = k5_enumset1(X22,X19,X19,X19,X19,X20,X21) ),
    inference(superposition,[],[f796,f792])).

fof(f19143,plain,(
    ! [X121,X122,X120,X119] : k2_enumset1(X121,X122,X119,X120) = k2_enumset1(X119,X122,X120,X121) ),
    inference(superposition,[],[f18382,f7799])).

fof(f7799,plain,(
    ! [X57,X58,X56,X55] : k2_enumset1(X58,X55,X56,X57) = k2_enumset1(X56,X57,X58,X55) ),
    inference(superposition,[],[f6785,f6785])).

fof(f18382,plain,(
    ! [X57,X58,X56,X55] : k2_enumset1(X55,X56,X57,X58) = k2_enumset1(X55,X58,X56,X57) ),
    inference(superposition,[],[f7184,f3289])).

fof(f7184,plain,(
    ! [X70,X72,X71,X69] : k3_enumset1(X70,X71,X72,X69,X69) = k2_enumset1(X70,X69,X71,X72) ),
    inference(forward_demodulation,[],[f7152,f3272])).

fof(f7152,plain,(
    ! [X70,X72,X71,X69] : k3_enumset1(X70,X71,X72,X69,X69) = k2_xboole_0(k1_tarski(X72),k1_enumset1(X70,X69,X71)) ),
    inference(superposition,[],[f3455,f6821])).

fof(f6821,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(forward_demodulation,[],[f6772,f3982])).

fof(f3982,plain,(
    ! [X2,X0,X1] : k1_enumset1(X1,X0,X2) = k2_enumset1(X0,X1,X2,X2) ),
    inference(superposition,[],[f3530,f39])).

fof(f3530,plain,(
    ! [X6,X4,X5] : k1_enumset1(X6,X5,X4) = k3_enumset1(X5,X5,X6,X4,X4) ),
    inference(forward_demodulation,[],[f3516,f2282])).

fof(f2282,plain,(
    ! [X4,X2,X3] : k1_enumset1(X2,X3,X4) = k2_xboole_0(k1_tarski(X2),k2_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f2272,f1793])).

fof(f1793,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(forward_demodulation,[],[f1765,f1416])).

fof(f1765,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X1,X2,X0,X0) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(superposition,[],[f1359,f42])).

fof(f2272,plain,(
    ! [X4,X2,X3] : k4_enumset1(X2,X2,X2,X2,X3,X4) = k2_xboole_0(k1_tarski(X2),k2_tarski(X3,X4)) ),
    inference(superposition,[],[f819,f2176])).

fof(f2176,plain,(
    ! [X2] : k1_tarski(X2) = k2_enumset1(X2,X2,X2,X2) ),
    inference(superposition,[],[f1925,f1414])).

fof(f1925,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(forward_demodulation,[],[f1904,f28])).

fof(f1904,plain,(
    ! [X0] : k2_tarski(X0,X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(superposition,[],[f1792,f42])).

fof(f1792,plain,(
    ! [X4,X3] : k2_tarski(X4,X3) = k5_enumset1(X4,X3,X3,X3,X3,X3,X3) ),
    inference(forward_demodulation,[],[f1764,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[],[f33,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

fof(f1764,plain,(
    ! [X4,X3] : k1_enumset1(X3,X4,X4) = k5_enumset1(X4,X3,X3,X3,X3,X3,X3) ),
    inference(superposition,[],[f1359,f1418])).

fof(f819,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(forward_demodulation,[],[f804,f42])).

fof(f804,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f257,f39])).

fof(f3516,plain,(
    ! [X6,X4,X5] : k3_enumset1(X5,X5,X6,X4,X4) = k2_xboole_0(k1_tarski(X6),k2_tarski(X5,X4)) ),
    inference(superposition,[],[f3455,f2061])).

fof(f2061,plain,(
    ! [X0,X1] : k2_tarski(X1,X0) = k2_enumset1(X0,X0,X1,X1) ),
    inference(superposition,[],[f1908,f39])).

fof(f1908,plain,(
    ! [X8,X7] : k2_tarski(X7,X8) = k3_enumset1(X8,X8,X8,X7,X7) ),
    inference(superposition,[],[f1792,f1359])).

fof(f6772,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X1,X2,X2) ),
    inference(superposition,[],[f3289,f39])).

fof(f27,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f24,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))
   => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:06:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.44  % (6126)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (6134)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (6121)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (6123)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (6133)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (6132)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (6136)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (6127)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (6132)Refutation not found, incomplete strategy% (6132)------------------------------
% 0.20/0.47  % (6132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (6132)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (6132)Memory used [KB]: 10618
% 0.20/0.47  % (6132)Time elapsed: 0.052 s
% 0.20/0.47  % (6132)------------------------------
% 0.20/0.47  % (6132)------------------------------
% 0.20/0.47  % (6125)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (6135)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (6128)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (6138)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  % (6130)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (6124)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (6122)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (6137)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % (6131)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (6129)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 4.91/1.01  % (6125)Time limit reached!
% 4.91/1.01  % (6125)------------------------------
% 4.91/1.01  % (6125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.91/1.02  % (6125)Termination reason: Time limit
% 4.91/1.02  
% 4.91/1.02  % (6125)Memory used [KB]: 11257
% 4.91/1.02  % (6125)Time elapsed: 0.603 s
% 4.91/1.02  % (6125)------------------------------
% 4.91/1.02  % (6125)------------------------------
% 11.97/1.90  % (6126)Time limit reached!
% 11.97/1.90  % (6126)------------------------------
% 11.97/1.90  % (6126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.97/1.91  % (6126)Termination reason: Time limit
% 11.97/1.91  % (6126)Termination phase: Saturation
% 11.97/1.91  
% 11.97/1.91  % (6126)Memory used [KB]: 50020
% 11.97/1.91  % (6126)Time elapsed: 1.500 s
% 11.97/1.91  % (6126)------------------------------
% 11.97/1.91  % (6126)------------------------------
% 12.56/1.94  % (6127)Time limit reached!
% 12.56/1.94  % (6127)------------------------------
% 12.56/1.94  % (6127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.56/1.94  % (6127)Termination reason: Time limit
% 12.56/1.94  % (6127)Termination phase: Saturation
% 12.56/1.94  
% 12.56/1.94  % (6127)Memory used [KB]: 23666
% 12.56/1.94  % (6127)Time elapsed: 1.500 s
% 12.56/1.94  % (6127)------------------------------
% 12.56/1.94  % (6127)------------------------------
% 14.42/2.23  % (6123)Time limit reached!
% 14.42/2.23  % (6123)------------------------------
% 14.42/2.23  % (6123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.42/2.23  % (6123)Termination reason: Time limit
% 14.42/2.23  % (6123)Termination phase: Saturation
% 14.42/2.23  
% 14.42/2.23  % (6123)Memory used [KB]: 24434
% 14.42/2.23  % (6123)Time elapsed: 1.800 s
% 14.42/2.23  % (6123)------------------------------
% 14.42/2.23  % (6123)------------------------------
% 17.78/2.62  % (6133)Time limit reached!
% 17.78/2.62  % (6133)------------------------------
% 17.78/2.62  % (6133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.78/2.62  % (6133)Termination reason: Time limit
% 17.78/2.62  % (6133)Termination phase: Saturation
% 17.78/2.62  
% 17.78/2.62  % (6133)Memory used [KB]: 20980
% 17.78/2.62  % (6133)Time elapsed: 2.200 s
% 17.78/2.62  % (6133)------------------------------
% 17.78/2.62  % (6133)------------------------------
% 17.78/2.62  % (6124)Refutation found. Thanks to Tanya!
% 17.78/2.62  % SZS status Theorem for theBenchmark
% 17.78/2.62  % SZS output start Proof for theBenchmark
% 17.78/2.62  fof(f23549,plain,(
% 17.78/2.62    $false),
% 17.78/2.62    inference(subsumption_resolution,[],[f23548,f34])).
% 17.78/2.62  fof(f34,plain,(
% 17.78/2.62    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 17.78/2.62    inference(cnf_transformation,[],[f21])).
% 17.78/2.62  fof(f21,axiom,(
% 17.78/2.62    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 17.78/2.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 17.78/2.62  fof(f23548,plain,(
% 17.78/2.62    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4))),
% 17.78/2.62    inference(forward_demodulation,[],[f23547,f37])).
% 17.78/2.62  fof(f37,plain,(
% 17.78/2.62    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 17.78/2.62    inference(cnf_transformation,[],[f19])).
% 17.78/2.62  fof(f19,axiom,(
% 17.78/2.62    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 17.78/2.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 17.78/2.62  fof(f23547,plain,(
% 17.78/2.62    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4))),
% 17.78/2.62    inference(superposition,[],[f23247,f1346])).
% 17.78/2.62  fof(f1346,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5))) )),
% 17.78/2.62    inference(forward_demodulation,[],[f1333,f35])).
% 17.78/2.62  fof(f35,plain,(
% 17.78/2.62    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 17.78/2.62    inference(cnf_transformation,[],[f20])).
% 17.78/2.62  fof(f20,axiom,(
% 17.78/2.62    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 17.78/2.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 17.78/2.62  fof(f1333,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5))) )),
% 17.78/2.62    inference(superposition,[],[f164,f35])).
% 17.78/2.62  fof(f164,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 17.78/2.62    inference(forward_demodulation,[],[f158,f35])).
% 17.78/2.62  fof(f158,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 17.78/2.62    inference(superposition,[],[f40,f35])).
% 17.78/2.62  fof(f40,plain,(
% 17.78/2.62    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 17.78/2.62    inference(cnf_transformation,[],[f18])).
% 17.78/2.62  fof(f18,axiom,(
% 17.78/2.62    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 17.78/2.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 17.78/2.62  fof(f23247,plain,(
% 17.78/2.62    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4))),
% 17.78/2.62    inference(superposition,[],[f27,f20048])).
% 17.78/2.62  fof(f20048,plain,(
% 17.78/2.62    ( ! [X111,X114,X112,X113] : (k2_enumset1(X114,X112,X111,X113) = k2_enumset1(X114,X111,X112,X113)) )),
% 17.78/2.62    inference(superposition,[],[f19143,f6785])).
% 17.78/2.62  fof(f6785,plain,(
% 17.78/2.62    ( ! [X37,X35,X38,X36] : (k2_enumset1(X35,X36,X37,X38) = k2_enumset1(X38,X35,X36,X37)) )),
% 17.78/2.62    inference(superposition,[],[f3289,f3529])).
% 17.78/2.62  fof(f3529,plain,(
% 17.78/2.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X1,X2,X3,X0,X0)) )),
% 17.78/2.62    inference(forward_demodulation,[],[f3515,f3272])).
% 17.78/2.62  fof(f3272,plain,(
% 17.78/2.62    ( ! [X17,X15,X18,X16] : (k2_xboole_0(k1_tarski(X15),k1_enumset1(X16,X17,X18)) = k2_enumset1(X16,X17,X18,X15)) )),
% 17.78/2.62    inference(forward_demodulation,[],[f3271,f36])).
% 17.78/2.62  fof(f36,plain,(
% 17.78/2.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 17.78/2.62    inference(cnf_transformation,[],[f13])).
% 17.78/2.62  fof(f13,axiom,(
% 17.78/2.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 17.78/2.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 17.78/2.62  fof(f3271,plain,(
% 17.78/2.62    ( ! [X17,X15,X18,X16] : (k2_xboole_0(k1_tarski(X15),k2_enumset1(X16,X16,X17,X18)) = k2_enumset1(X16,X17,X18,X15)) )),
% 17.78/2.62    inference(forward_demodulation,[],[f3249,f1414])).
% 17.78/2.62  fof(f1414,plain,(
% 17.78/2.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X1,X2,X3,X0,X0)) )),
% 17.78/2.62    inference(forward_demodulation,[],[f1399,f39])).
% 17.78/2.62  fof(f39,plain,(
% 17.78/2.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 17.78/2.62    inference(cnf_transformation,[],[f14])).
% 17.78/2.62  fof(f14,axiom,(
% 17.78/2.62    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 17.78/2.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 17.78/2.62  fof(f1399,plain,(
% 17.78/2.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k4_enumset1(X0,X1,X2,X3,X0,X0)) )),
% 17.78/2.62    inference(superposition,[],[f1374,f42])).
% 17.78/2.62  fof(f42,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 17.78/2.62    inference(cnf_transformation,[],[f16])).
% 17.78/2.62  fof(f16,axiom,(
% 17.78/2.62    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 17.78/2.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 17.78/2.62  fof(f1374,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X1,X2,X3,X4,X0,X0)) )),
% 17.78/2.62    inference(forward_demodulation,[],[f1350,f41])).
% 17.78/2.62  fof(f41,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 17.78/2.62    inference(cnf_transformation,[],[f15])).
% 17.78/2.62  fof(f15,axiom,(
% 17.78/2.62    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 17.78/2.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 17.78/2.62  fof(f1350,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k5_enumset1(X0,X1,X2,X3,X4,X0,X0)) )),
% 17.78/2.62    inference(superposition,[],[f796,f42])).
% 17.78/2.62  fof(f796,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X5,X0,X0,X1,X2,X3,X4) = k5_enumset1(X0,X1,X2,X3,X4,X5,X5)) )),
% 17.78/2.62    inference(superposition,[],[f258,f205])).
% 17.78/2.62  fof(f205,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 17.78/2.62    inference(forward_demodulation,[],[f194,f43])).
% 17.78/2.62  fof(f43,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 17.78/2.62    inference(cnf_transformation,[],[f8])).
% 17.78/2.62  fof(f8,axiom,(
% 17.78/2.62    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 17.78/2.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).
% 17.78/2.62  fof(f194,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 17.78/2.62    inference(superposition,[],[f44,f28])).
% 17.78/2.62  fof(f28,plain,(
% 17.78/2.62    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 17.78/2.62    inference(cnf_transformation,[],[f11])).
% 17.78/2.62  fof(f11,axiom,(
% 17.78/2.62    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 17.78/2.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 17.78/2.62  fof(f44,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) )),
% 17.78/2.62    inference(cnf_transformation,[],[f9])).
% 17.78/2.62  fof(f9,axiom,(
% 17.78/2.62    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 17.78/2.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).
% 17.78/2.62  fof(f258,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X0)) )),
% 17.78/2.62    inference(forward_demodulation,[],[f246,f140])).
% 17.78/2.62  fof(f140,plain,(
% 17.78/2.62    ( ! [X12,X10,X8,X7,X13,X11,X9] : (k2_xboole_0(k4_enumset1(X8,X9,X10,X11,X12,X13),k1_tarski(X7)) = k5_enumset1(X7,X8,X9,X10,X11,X12,X13)) )),
% 17.78/2.62    inference(superposition,[],[f43,f56])).
% 17.78/2.62  fof(f56,plain,(
% 17.78/2.62    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 17.78/2.62    inference(superposition,[],[f51,f30])).
% 17.78/2.62  fof(f30,plain,(
% 17.78/2.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 17.78/2.62    inference(cnf_transformation,[],[f17])).
% 17.78/2.62  fof(f17,axiom,(
% 17.78/2.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 17.78/2.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 17.78/2.62  fof(f51,plain,(
% 17.78/2.62    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 17.78/2.62    inference(superposition,[],[f30,f29])).
% 17.78/2.62  fof(f29,plain,(
% 17.78/2.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 17.78/2.62    inference(cnf_transformation,[],[f2])).
% 17.78/2.62  fof(f2,axiom,(
% 17.78/2.62    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 17.78/2.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 17.78/2.62  fof(f246,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0)) = k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X0)) )),
% 17.78/2.62    inference(superposition,[],[f45,f28])).
% 17.78/2.62  fof(f45,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 17.78/2.62    inference(cnf_transformation,[],[f10])).
% 17.78/2.62  fof(f10,axiom,(
% 17.78/2.62    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 17.78/2.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).
% 17.78/2.62  fof(f3249,plain,(
% 17.78/2.62    ( ! [X17,X15,X18,X16] : (k2_xboole_0(k1_tarski(X15),k2_enumset1(X16,X16,X17,X18)) = k4_enumset1(X16,X17,X18,X15,X16,X16)) )),
% 17.78/2.62    inference(superposition,[],[f3169,f782])).
% 17.78/2.62  fof(f782,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X4,X0,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3))) )),
% 17.78/2.62    inference(superposition,[],[f139,f39])).
% 17.78/2.62  fof(f139,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X5,X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X5),k3_enumset1(X0,X1,X2,X3,X4))) )),
% 17.78/2.62    inference(superposition,[],[f43,f41])).
% 17.78/2.62  fof(f3169,plain,(
% 17.78/2.62    ( ! [X6,X10,X8,X7,X11,X9] : (k5_enumset1(X8,X9,X10,X11,X11,X6,X7) = k4_enumset1(X11,X6,X7,X8,X9,X10)) )),
% 17.78/2.62    inference(backward_demodulation,[],[f832,f3168])).
% 17.78/2.62  fof(f3168,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X3,X3,X4,X5)) )),
% 17.78/2.62    inference(forward_demodulation,[],[f3152,f42])).
% 17.78/2.62  fof(f3152,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X3,X3,X4,X5)) )),
% 17.78/2.62    inference(superposition,[],[f853,f205])).
% 17.78/2.62  fof(f853,plain,(
% 17.78/2.62    ( ! [X21,X19,X17,X15,X20,X18,X16] : (k6_enumset1(X15,X16,X17,X18,X19,X19,X20,X21) = k5_enumset1(X15,X16,X17,X18,X19,X20,X21)) )),
% 17.78/2.62    inference(forward_demodulation,[],[f851,f205])).
% 17.78/2.62  fof(f851,plain,(
% 17.78/2.62    ( ! [X21,X19,X17,X15,X20,X18,X16] : (k6_enumset1(X15,X16,X17,X18,X19,X19,X20,X21) = k6_enumset1(X15,X15,X16,X17,X18,X19,X20,X21)) )),
% 17.78/2.62    inference(superposition,[],[f450,f446])).
% 17.78/2.62  fof(f446,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 17.78/2.62    inference(forward_demodulation,[],[f434,f45])).
% 17.78/2.62  fof(f434,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 17.78/2.62    inference(superposition,[],[f49,f42])).
% 17.78/2.62  fof(f49,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) )),
% 17.78/2.62    inference(cnf_transformation,[],[f7])).
% 17.78/2.62  fof(f7,axiom,(
% 17.78/2.62    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 17.78/2.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).
% 17.78/2.62  fof(f450,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X3,X4,X5,X6,X7,X0,X0,X1,X2) = k6_enumset1(X3,X4,X5,X6,X7,X0,X1,X2)) )),
% 17.78/2.62    inference(backward_demodulation,[],[f329,f447])).
% 17.78/2.62  fof(f447,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 17.78/2.62    inference(backward_demodulation,[],[f369,f446])).
% 17.78/2.62  fof(f369,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 17.78/2.62    inference(superposition,[],[f48,f41])).
% 17.78/2.62  fof(f48,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))) )),
% 17.78/2.62    inference(cnf_transformation,[],[f6])).
% 17.78/2.62  fof(f6,axiom,(
% 17.78/2.62    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 17.78/2.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).
% 17.78/2.62  fof(f329,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k1_enumset1(X0,X1,X2)) = k7_enumset1(X3,X4,X5,X6,X7,X0,X0,X1,X2)) )),
% 17.78/2.62    inference(superposition,[],[f47,f36])).
% 17.78/2.62  fof(f47,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 17.78/2.62    inference(cnf_transformation,[],[f5])).
% 17.78/2.62  fof(f5,axiom,(
% 17.78/2.62    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 17.78/2.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).
% 17.78/2.62  fof(f832,plain,(
% 17.78/2.62    ( ! [X6,X10,X8,X7,X11,X9] : (k5_enumset1(X11,X6,X7,X8,X8,X9,X10) = k5_enumset1(X8,X9,X10,X11,X11,X6,X7)) )),
% 17.78/2.62    inference(superposition,[],[f820,f258])).
% 17.78/2.62  fof(f820,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X5,X6,X0,X0,X1,X2,X3,X4)) )),
% 17.78/2.62    inference(backward_demodulation,[],[f200,f815])).
% 17.78/2.62  fof(f815,plain,(
% 17.78/2.62    ( ! [X12,X10,X8,X7,X13,X11,X9] : (k5_enumset1(X7,X8,X9,X10,X11,X12,X13) = k2_xboole_0(k2_tarski(X12,X13),k3_enumset1(X7,X8,X9,X10,X11))) )),
% 17.78/2.62    inference(superposition,[],[f257,f56])).
% 17.78/2.62  fof(f257,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 17.78/2.62    inference(forward_demodulation,[],[f245,f205])).
% 17.78/2.62  fof(f245,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 17.78/2.62    inference(superposition,[],[f45,f41])).
% 17.78/2.62  fof(f200,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X5,X6,X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X5,X6),k3_enumset1(X0,X1,X2,X3,X4))) )),
% 17.78/2.62    inference(superposition,[],[f44,f41])).
% 17.78/2.62  fof(f3515,plain,(
% 17.78/2.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X1,X2,X3,X0,X0) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))) )),
% 17.78/2.62    inference(superposition,[],[f3455,f36])).
% 17.78/2.62  fof(f3455,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3)) = k3_enumset1(X2,X3,X4,X0,X1)) )),
% 17.78/2.62    inference(backward_demodulation,[],[f3421,f3449])).
% 17.78/2.62  fof(f3449,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X2,X3,X4,X0,X0,X1) = k3_enumset1(X2,X3,X4,X0,X1)) )),
% 17.78/2.62    inference(backward_demodulation,[],[f3246,f3426])).
% 17.78/2.62  fof(f3426,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X3,X4,X0,X0,X1,X2)) )),
% 17.78/2.62    inference(superposition,[],[f3360,f789])).
% 17.78/2.62  fof(f789,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X0,X1,X2,X3,X4))) )),
% 17.78/2.62    inference(forward_demodulation,[],[f781,f41])).
% 17.78/2.62  fof(f781,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X0,X1,X2,X3,X4))) )),
% 17.78/2.62    inference(superposition,[],[f139,f42])).
% 17.78/2.62  fof(f3360,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X5),k3_enumset1(X0,X1,X2,X3,X4)) = k4_enumset1(X3,X4,X5,X0,X1,X2)) )),
% 17.78/2.62    inference(backward_demodulation,[],[f139,f3358])).
% 17.78/2.62  fof(f3358,plain,(
% 17.78/2.62    ( ! [X30,X28,X26,X29,X27,X25] : (k4_enumset1(X25,X26,X27,X28,X29,X30) = k5_enumset1(X27,X28,X28,X29,X30,X25,X26)) )),
% 17.78/2.62    inference(backward_demodulation,[],[f3154,f3357])).
% 17.78/2.62  fof(f3357,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X2,X3,X4,X5)) )),
% 17.78/2.62    inference(forward_demodulation,[],[f3339,f42])).
% 17.78/2.62  fof(f3339,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X2,X3,X4,X5)) )),
% 17.78/2.62    inference(superposition,[],[f866,f205])).
% 17.78/2.62  fof(f866,plain,(
% 17.78/2.62    ( ! [X28,X26,X24,X23,X27,X25,X22] : (k6_enumset1(X22,X23,X24,X25,X25,X26,X27,X28) = k5_enumset1(X22,X23,X24,X25,X26,X27,X28)) )),
% 17.78/2.62    inference(forward_demodulation,[],[f862,f205])).
% 17.78/2.62  fof(f862,plain,(
% 17.78/2.62    ( ! [X28,X26,X24,X23,X27,X25,X22] : (k6_enumset1(X22,X23,X24,X25,X25,X26,X27,X28) = k6_enumset1(X22,X22,X23,X24,X25,X26,X27,X28)) )),
% 17.78/2.62    inference(superposition,[],[f451,f446])).
% 17.78/2.62  fof(f451,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X4,X5,X6,X7,X0,X0,X1,X2,X3) = k6_enumset1(X4,X5,X6,X7,X0,X1,X2,X3)) )),
% 17.78/2.62    inference(backward_demodulation,[],[f283,f448])).
% 17.78/2.62  fof(f448,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 17.78/2.62    inference(backward_demodulation,[],[f328,f446])).
% 17.78/2.62  fof(f328,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 17.78/2.62    inference(superposition,[],[f47,f39])).
% 17.78/2.62  fof(f283,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X4,X5,X6,X7,X0,X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X4,X5,X6,X7),k2_enumset1(X0,X1,X2,X3))) )),
% 17.78/2.62    inference(superposition,[],[f46,f39])).
% 17.78/2.62  fof(f46,plain,(
% 17.78/2.62    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))) )),
% 17.78/2.62    inference(cnf_transformation,[],[f3])).
% 17.78/2.62  fof(f3,axiom,(
% 17.78/2.62    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))),
% 17.78/2.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l142_enumset1)).
% 17.78/2.62  fof(f3154,plain,(
% 17.78/2.62    ( ! [X30,X28,X26,X29,X27,X25] : (k5_enumset1(X27,X28,X28,X29,X30,X25,X26) = k5_enumset1(X25,X26,X27,X27,X28,X29,X30)) )),
% 17.78/2.62    inference(superposition,[],[f853,f820])).
% 17.78/2.62  fof(f3246,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X1,X2,X2,X3,X4) = k4_enumset1(X2,X3,X4,X0,X0,X1)) )),
% 17.78/2.62    inference(superposition,[],[f3169,f42])).
% 17.78/2.62  fof(f3421,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3)) = k4_enumset1(X2,X3,X4,X0,X0,X1)) )),
% 17.78/2.62    inference(superposition,[],[f3360,f39])).
% 17.78/2.62  fof(f3289,plain,(
% 17.78/2.62    ( ! [X21,X19,X22,X20] : (k3_enumset1(X19,X20,X21,X22,X22) = k2_enumset1(X19,X20,X21,X22)) )),
% 17.78/2.62    inference(backward_demodulation,[],[f1359,f3274])).
% 17.78/2.62  fof(f3274,plain,(
% 17.78/2.62    ( ! [X19,X17,X20,X18] : (k5_enumset1(X20,X17,X17,X17,X17,X18,X19) = k2_enumset1(X17,X18,X19,X20)) )),
% 17.78/2.62    inference(backward_demodulation,[],[f1608,f3272])).
% 17.78/2.62  fof(f1608,plain,(
% 17.78/2.62    ( ! [X19,X17,X20,X18] : (k5_enumset1(X20,X17,X17,X17,X17,X18,X19) = k2_xboole_0(k1_tarski(X20),k1_enumset1(X17,X18,X19))) )),
% 17.78/2.62    inference(superposition,[],[f139,f1418])).
% 17.78/2.62  fof(f1418,plain,(
% 17.78/2.62    ( ! [X6,X4,X5] : (k1_enumset1(X4,X5,X6) = k3_enumset1(X4,X4,X4,X5,X6)) )),
% 17.78/2.62    inference(forward_demodulation,[],[f1406,f1416])).
% 17.78/2.62  fof(f1416,plain,(
% 17.78/2.62    ( ! [X17,X15,X16] : (k1_enumset1(X15,X16,X17) = k3_enumset1(X15,X16,X17,X15,X15)) )),
% 17.78/2.62    inference(forward_demodulation,[],[f1415,f36])).
% 17.78/2.62  fof(f1415,plain,(
% 17.78/2.62    ( ! [X17,X15,X16] : (k3_enumset1(X15,X16,X17,X15,X15) = k2_enumset1(X15,X15,X16,X17)) )),
% 17.78/2.62    inference(forward_demodulation,[],[f1403,f39])).
% 17.78/2.62  fof(f1403,plain,(
% 17.78/2.62    ( ! [X17,X15,X16] : (k3_enumset1(X15,X16,X17,X15,X15) = k3_enumset1(X15,X15,X15,X16,X17)) )),
% 17.78/2.62    inference(superposition,[],[f1374,f792])).
% 17.78/2.62  fof(f792,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 17.78/2.62    inference(superposition,[],[f789,f139])).
% 17.78/2.62  fof(f1406,plain,(
% 17.78/2.62    ( ! [X6,X4,X5] : (k3_enumset1(X4,X4,X4,X5,X6) = k3_enumset1(X4,X5,X6,X4,X4)) )),
% 17.78/2.62    inference(superposition,[],[f792,f1374])).
% 17.78/2.62  fof(f1359,plain,(
% 17.78/2.62    ( ! [X21,X19,X22,X20] : (k3_enumset1(X19,X20,X21,X22,X22) = k5_enumset1(X22,X19,X19,X19,X19,X20,X21)) )),
% 17.78/2.62    inference(superposition,[],[f796,f792])).
% 17.78/2.62  fof(f19143,plain,(
% 17.78/2.62    ( ! [X121,X122,X120,X119] : (k2_enumset1(X121,X122,X119,X120) = k2_enumset1(X119,X122,X120,X121)) )),
% 17.78/2.62    inference(superposition,[],[f18382,f7799])).
% 17.78/2.62  fof(f7799,plain,(
% 17.78/2.62    ( ! [X57,X58,X56,X55] : (k2_enumset1(X58,X55,X56,X57) = k2_enumset1(X56,X57,X58,X55)) )),
% 17.78/2.62    inference(superposition,[],[f6785,f6785])).
% 17.78/2.62  fof(f18382,plain,(
% 17.78/2.62    ( ! [X57,X58,X56,X55] : (k2_enumset1(X55,X56,X57,X58) = k2_enumset1(X55,X58,X56,X57)) )),
% 17.78/2.62    inference(superposition,[],[f7184,f3289])).
% 17.78/2.62  fof(f7184,plain,(
% 17.78/2.62    ( ! [X70,X72,X71,X69] : (k3_enumset1(X70,X71,X72,X69,X69) = k2_enumset1(X70,X69,X71,X72)) )),
% 17.78/2.62    inference(forward_demodulation,[],[f7152,f3272])).
% 17.78/2.62  fof(f7152,plain,(
% 17.78/2.62    ( ! [X70,X72,X71,X69] : (k3_enumset1(X70,X71,X72,X69,X69) = k2_xboole_0(k1_tarski(X72),k1_enumset1(X70,X69,X71))) )),
% 17.78/2.62    inference(superposition,[],[f3455,f6821])).
% 17.78/2.62  fof(f6821,plain,(
% 17.78/2.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X1,X0,X2)) )),
% 17.78/2.62    inference(forward_demodulation,[],[f6772,f3982])).
% 17.78/2.62  fof(f3982,plain,(
% 17.78/2.62    ( ! [X2,X0,X1] : (k1_enumset1(X1,X0,X2) = k2_enumset1(X0,X1,X2,X2)) )),
% 17.78/2.62    inference(superposition,[],[f3530,f39])).
% 17.78/2.62  fof(f3530,plain,(
% 17.78/2.62    ( ! [X6,X4,X5] : (k1_enumset1(X6,X5,X4) = k3_enumset1(X5,X5,X6,X4,X4)) )),
% 17.78/2.62    inference(forward_demodulation,[],[f3516,f2282])).
% 17.78/2.62  fof(f2282,plain,(
% 17.78/2.62    ( ! [X4,X2,X3] : (k1_enumset1(X2,X3,X4) = k2_xboole_0(k1_tarski(X2),k2_tarski(X3,X4))) )),
% 17.78/2.62    inference(forward_demodulation,[],[f2272,f1793])).
% 17.78/2.62  fof(f1793,plain,(
% 17.78/2.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 17.78/2.62    inference(forward_demodulation,[],[f1765,f1416])).
% 17.78/2.62  fof(f1765,plain,(
% 17.78/2.62    ( ! [X2,X0,X1] : (k3_enumset1(X0,X1,X2,X0,X0) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 17.78/2.62    inference(superposition,[],[f1359,f42])).
% 17.78/2.62  fof(f2272,plain,(
% 17.78/2.62    ( ! [X4,X2,X3] : (k4_enumset1(X2,X2,X2,X2,X3,X4) = k2_xboole_0(k1_tarski(X2),k2_tarski(X3,X4))) )),
% 17.78/2.62    inference(superposition,[],[f819,f2176])).
% 17.78/2.62  fof(f2176,plain,(
% 17.78/2.62    ( ! [X2] : (k1_tarski(X2) = k2_enumset1(X2,X2,X2,X2)) )),
% 17.78/2.62    inference(superposition,[],[f1925,f1414])).
% 17.78/2.62  fof(f1925,plain,(
% 17.78/2.62    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 17.78/2.62    inference(forward_demodulation,[],[f1904,f28])).
% 17.78/2.62  fof(f1904,plain,(
% 17.78/2.62    ( ! [X0] : (k2_tarski(X0,X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 17.78/2.62    inference(superposition,[],[f1792,f42])).
% 17.78/2.62  fof(f1792,plain,(
% 17.78/2.62    ( ! [X4,X3] : (k2_tarski(X4,X3) = k5_enumset1(X4,X3,X3,X3,X3,X3,X3)) )),
% 17.78/2.62    inference(forward_demodulation,[],[f1764,f60])).
% 17.78/2.62  fof(f60,plain,(
% 17.78/2.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)) )),
% 17.78/2.62    inference(superposition,[],[f33,f31])).
% 17.78/2.62  fof(f31,plain,(
% 17.78/2.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 17.78/2.62    inference(cnf_transformation,[],[f12])).
% 17.78/2.62  fof(f12,axiom,(
% 17.78/2.62    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 17.78/2.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 17.78/2.62  fof(f33,plain,(
% 17.78/2.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 17.78/2.62    inference(cnf_transformation,[],[f4])).
% 17.78/2.62  fof(f4,axiom,(
% 17.78/2.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 17.78/2.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).
% 17.78/2.62  fof(f1764,plain,(
% 17.78/2.62    ( ! [X4,X3] : (k1_enumset1(X3,X4,X4) = k5_enumset1(X4,X3,X3,X3,X3,X3,X3)) )),
% 17.78/2.62    inference(superposition,[],[f1359,f1418])).
% 17.78/2.62  fof(f819,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 17.78/2.62    inference(forward_demodulation,[],[f804,f42])).
% 17.78/2.62  fof(f804,plain,(
% 17.78/2.62    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 17.78/2.62    inference(superposition,[],[f257,f39])).
% 17.78/2.62  fof(f3516,plain,(
% 17.78/2.62    ( ! [X6,X4,X5] : (k3_enumset1(X5,X5,X6,X4,X4) = k2_xboole_0(k1_tarski(X6),k2_tarski(X5,X4))) )),
% 17.78/2.62    inference(superposition,[],[f3455,f2061])).
% 17.78/2.62  fof(f2061,plain,(
% 17.78/2.62    ( ! [X0,X1] : (k2_tarski(X1,X0) = k2_enumset1(X0,X0,X1,X1)) )),
% 17.78/2.62    inference(superposition,[],[f1908,f39])).
% 17.78/2.62  fof(f1908,plain,(
% 17.78/2.62    ( ! [X8,X7] : (k2_tarski(X7,X8) = k3_enumset1(X8,X8,X8,X7,X7)) )),
% 17.78/2.62    inference(superposition,[],[f1792,f1359])).
% 17.78/2.62  fof(f6772,plain,(
% 17.78/2.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)) )),
% 17.78/2.62    inference(superposition,[],[f3289,f39])).
% 17.78/2.62  fof(f27,plain,(
% 17.78/2.62    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 17.78/2.62    inference(cnf_transformation,[],[f26])).
% 17.78/2.62  fof(f26,plain,(
% 17.78/2.62    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 17.78/2.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f24,f25])).
% 17.78/2.62  fof(f25,plain,(
% 17.78/2.62    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 17.78/2.62    introduced(choice_axiom,[])).
% 17.78/2.62  fof(f24,plain,(
% 17.78/2.62    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 17.78/2.62    inference(ennf_transformation,[],[f23])).
% 17.78/2.62  fof(f23,negated_conjecture,(
% 17.78/2.62    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 17.78/2.62    inference(negated_conjecture,[],[f22])).
% 17.78/2.62  fof(f22,conjecture,(
% 17.78/2.62    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 17.78/2.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_mcart_1)).
% 17.78/2.62  % SZS output end Proof for theBenchmark
% 17.78/2.62  % (6124)------------------------------
% 17.78/2.62  % (6124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.78/2.62  % (6124)Termination reason: Refutation
% 17.78/2.62  
% 17.78/2.62  % (6124)Memory used [KB]: 42216
% 17.78/2.62  % (6124)Time elapsed: 2.198 s
% 17.78/2.62  % (6124)------------------------------
% 17.78/2.62  % (6124)------------------------------
% 17.78/2.63  % (6120)Success in time 2.277 s
%------------------------------------------------------------------------------
