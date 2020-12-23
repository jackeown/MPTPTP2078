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
% DateTime   : Thu Dec  3 12:58:59 EST 2020

% Result     : Theorem 7.71s
% Output     : Refutation 7.71s
% Verified   : 
% Statistics : Number of formulae       :  126 (1863 expanded)
%              Number of leaves         :   19 ( 621 expanded)
%              Depth                    :   37
%              Number of atoms          :  128 (1865 expanded)
%              Number of equality atoms :  127 (1864 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10680,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10679,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f10679,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(sK3,sK4)) ),
    inference(forward_demodulation,[],[f10678,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f10678,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(superposition,[],[f10558,f413])).

fof(f413,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5)) ),
    inference(forward_demodulation,[],[f401,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f401,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5)) ),
    inference(superposition,[],[f96,f31])).

fof(f96,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f90,f31])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(superposition,[],[f36,f31])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f10558,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(superposition,[],[f24,f9946])).

fof(f9946,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X5,X7) ),
    inference(superposition,[],[f8919,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f8919,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(forward_demodulation,[],[f8896,f35])).

fof(f8896,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X1,X3) ),
    inference(superposition,[],[f3434,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f3434,plain,(
    ! [X26,X24,X23,X25,X22] : k3_enumset1(X23,X22,X24,X25,X26) = k4_enumset1(X23,X22,X22,X25,X24,X26) ),
    inference(backward_demodulation,[],[f2326,f3424])).

fof(f3424,plain,(
    ! [X14,X12,X15,X13,X11] : k6_enumset1(X11,X12,X11,X11,X11,X13,X14,X15) = k3_enumset1(X12,X11,X13,X14,X15) ),
    inference(backward_demodulation,[],[f1657,f3420])).

fof(f3420,plain,(
    ! [X19,X17,X15,X18,X16] : k3_enumset1(X15,X16,X17,X18,X19) = k2_xboole_0(k2_xboole_0(k1_tarski(X15),k1_tarski(X16)),k1_enumset1(X17,X18,X19)) ),
    inference(backward_demodulation,[],[f2004,f3418])).

fof(f3418,plain,(
    ! [X14,X17,X15,X13,X16] : k3_enumset1(X13,X14,X15,X16,X17) = k5_enumset1(X13,X14,X13,X14,X15,X16,X17) ),
    inference(forward_demodulation,[],[f3396,f272])).

fof(f272,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f264,f37])).

fof(f264,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(superposition,[],[f254,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f254,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(forward_demodulation,[],[f247,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f247,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f130,f35])).

fof(f130,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(forward_demodulation,[],[f126,f39])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f126,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(superposition,[],[f40,f37])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

fof(f3396,plain,(
    ! [X14,X17,X15,X13,X16] : k2_xboole_0(k1_enumset1(X13,X14,X15),k2_tarski(X16,X17)) = k5_enumset1(X13,X14,X13,X14,X15,X16,X17) ),
    inference(superposition,[],[f130,f3029])).

fof(f3029,plain,(
    ! [X14,X15,X16] : k1_enumset1(X15,X14,X16) = k3_enumset1(X15,X14,X15,X14,X16) ),
    inference(superposition,[],[f2966,f1255])).

fof(f1255,plain,(
    ! [X6,X8,X7,X5,X9] : k3_enumset1(X5,X6,X7,X8,X9) = k3_enumset1(X6,X5,X7,X8,X9) ),
    inference(superposition,[],[f274,f272])).

fof(f274,plain,(
    ! [X6,X4,X8,X7,X5] : k3_enumset1(X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X5,X4,X6),k2_tarski(X7,X8)) ),
    inference(superposition,[],[f272,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

fof(f2966,plain,(
    ! [X2,X0,X1] : k1_enumset1(X1,X0,X2) = k3_enumset1(X0,X1,X1,X0,X2) ),
    inference(superposition,[],[f2546,f1551])).

fof(f1551,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X3,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f740,f32])).

fof(f740,plain,(
    ! [X6,X10,X8,X7,X9] : k2_xboole_0(k1_tarski(X6),k2_enumset1(X7,X8,X9,X10)) = k3_enumset1(X6,X7,X8,X9,X10) ),
    inference(backward_demodulation,[],[f347,f739])).

fof(f739,plain,(
    ! [X35,X33,X31,X34,X32] : k6_enumset1(X31,X31,X31,X31,X32,X33,X34,X35) = k3_enumset1(X31,X32,X33,X34,X35) ),
    inference(forward_demodulation,[],[f738,f272])).

fof(f738,plain,(
    ! [X35,X33,X31,X34,X32] : k6_enumset1(X31,X31,X31,X31,X32,X33,X34,X35) = k2_xboole_0(k1_enumset1(X31,X32,X33),k2_tarski(X34,X35)) ),
    inference(superposition,[],[f40,f355])).

fof(f355,plain,(
    ! [X12,X13,X11] : k4_enumset1(X11,X11,X11,X11,X12,X13) = k1_enumset1(X11,X12,X13) ),
    inference(forward_demodulation,[],[f348,f303])).

fof(f303,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(forward_demodulation,[],[f289,f32])).

fof(f289,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(superposition,[],[f284,f25])).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f284,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f273,f35])).

fof(f273,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(superposition,[],[f272,f27])).

fof(f27,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f348,plain,(
    ! [X12,X13,X11] : k4_enumset1(X11,X11,X11,X11,X12,X13) = k2_xboole_0(k1_tarski(X11),k2_tarski(X12,X13)) ),
    inference(superposition,[],[f254,f317])).

fof(f317,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(backward_demodulation,[],[f308,f316])).

fof(f316,plain,(
    ! [X0] : k1_tarski(X0) = k3_tarski(k1_tarski(k1_tarski(X0))) ),
    inference(forward_demodulation,[],[f315,f25])).

fof(f315,plain,(
    ! [X0] : k2_tarski(X0,X0) = k3_tarski(k1_tarski(k2_tarski(X0,X0))) ),
    inference(forward_demodulation,[],[f309,f27])).

fof(f309,plain,(
    ! [X0] : k3_tarski(k1_tarski(k2_tarski(X0,X0))) = k1_enumset1(X0,X0,X0) ),
    inference(superposition,[],[f301,f32])).

fof(f301,plain,(
    ! [X4,X5] : k3_tarski(k1_tarski(k2_tarski(X4,X5))) = k2_enumset1(X4,X5,X4,X5) ),
    inference(superposition,[],[f284,f44])).

fof(f44,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0)) ),
    inference(superposition,[],[f26,f25])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f308,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0))) ),
    inference(superposition,[],[f301,f25])).

fof(f347,plain,(
    ! [X6,X10,X8,X7,X9] : k6_enumset1(X6,X6,X6,X6,X7,X8,X9,X10) = k2_xboole_0(k1_tarski(X6),k2_enumset1(X7,X8,X9,X10)) ),
    inference(superposition,[],[f212,f317])).

fof(f212,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(backward_demodulation,[],[f155,f210])).

fof(f210,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(forward_demodulation,[],[f204,f40])).

fof(f204,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(superposition,[],[f43,f38])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).

fof(f155,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(superposition,[],[f41,f35])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

fof(f2546,plain,(
    ! [X4,X5,X3] : k1_enumset1(X4,X3,X5) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X4,X3,X5)) ),
    inference(superposition,[],[f1823,f29])).

fof(f1823,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2)) ),
    inference(forward_demodulation,[],[f1784,f32])).

fof(f1784,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f1551,f35])).

fof(f2004,plain,(
    ! [X19,X17,X15,X18,X16] : k5_enumset1(X15,X16,X15,X16,X17,X18,X19) = k2_xboole_0(k2_xboole_0(k1_tarski(X15),k1_tarski(X16)),k1_enumset1(X17,X18,X19)) ),
    inference(backward_demodulation,[],[f1262,f1955])).

fof(f1955,plain,(
    ! [X10,X9] : k2_xboole_0(k1_tarski(X10),k1_tarski(X9)) = k3_tarski(k1_tarski(k2_tarski(X10,X9))) ),
    inference(superposition,[],[f1884,f419])).

fof(f419,plain,(
    ! [X2,X3] : k1_enumset1(X3,X2,X3) = k2_xboole_0(k1_tarski(X2),k1_tarski(X3)) ),
    inference(superposition,[],[f393,f29])).

fof(f393,plain,(
    ! [X0,X1] : k1_enumset1(X1,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(superposition,[],[f303,f25])).

fof(f1884,plain,(
    ! [X23,X22] : k3_tarski(k1_tarski(k2_tarski(X23,X22))) = k1_enumset1(X22,X23,X22) ),
    inference(superposition,[],[f1830,f1282])).

fof(f1282,plain,(
    ! [X39,X38] : k3_tarski(k1_tarski(k2_tarski(X38,X39))) = k3_enumset1(X39,X38,X38,X38,X39) ),
    inference(superposition,[],[f1255,f1110])).

fof(f1110,plain,(
    ! [X0,X1] : k3_tarski(k1_tarski(k2_tarski(X0,X1))) = k3_enumset1(X0,X1,X0,X0,X1) ),
    inference(forward_demodulation,[],[f1098,f27])).

fof(f1098,plain,(
    ! [X0,X1] : k3_tarski(k1_tarski(k1_enumset1(X0,X0,X1))) = k3_enumset1(X0,X1,X0,X0,X1) ),
    inference(superposition,[],[f1059,f37])).

fof(f1059,plain,(
    ! [X2,X0,X1] : k3_tarski(k1_tarski(k1_enumset1(X0,X1,X2))) = k4_enumset1(X0,X1,X2,X0,X1,X2) ),
    inference(superposition,[],[f1014,f38])).

fof(f1014,plain,(
    ! [X43,X41,X42] : k5_enumset1(X41,X41,X42,X43,X41,X42,X43) = k3_tarski(k1_tarski(k1_enumset1(X41,X42,X43))) ),
    inference(forward_demodulation,[],[f1004,f32])).

fof(f1004,plain,(
    ! [X43,X41,X42] : k3_tarski(k1_tarski(k2_enumset1(X41,X41,X42,X43))) = k5_enumset1(X41,X41,X42,X43,X41,X42,X43) ),
    inference(superposition,[],[f306,f338])).

fof(f338,plain,(
    ! [X10,X8,X11,X9] : k3_tarski(k1_tarski(k2_enumset1(X8,X9,X10,X11))) = k6_enumset1(X8,X9,X10,X11,X8,X9,X10,X11) ),
    inference(superposition,[],[f212,f44])).

fof(f306,plain,(
    ! [X21,X19,X17,X15,X20,X18,X16] : k6_enumset1(X15,X16,X17,X18,X19,X19,X20,X21) = k5_enumset1(X15,X16,X17,X18,X19,X20,X21) ),
    inference(forward_demodulation,[],[f304,f39])).

fof(f304,plain,(
    ! [X21,X19,X17,X15,X20,X18,X16] : k6_enumset1(X15,X16,X17,X18,X19,X19,X20,X21) = k6_enumset1(X15,X15,X16,X17,X18,X19,X20,X21) ),
    inference(superposition,[],[f213,f210])).

fof(f213,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X3,X4,X5,X6,X7,X0,X0,X1,X2) = k6_enumset1(X3,X4,X5,X6,X7,X0,X1,X2) ),
    inference(backward_demodulation,[],[f156,f211])).

fof(f211,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(backward_demodulation,[],[f190,f210])).

fof(f190,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(superposition,[],[f42,f37])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).

fof(f156,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X3,X4,X5,X6,X7,X0,X0,X1,X2) = k2_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f41,f32])).

fof(f1830,plain,(
    ! [X2,X0,X1] : k3_enumset1(X2,X0,X0,X0,X1) = k1_enumset1(X2,X0,X1) ),
    inference(forward_demodulation,[],[f1798,f303])).

fof(f1798,plain,(
    ! [X2,X0,X1] : k3_enumset1(X2,X0,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f1551,f27])).

fof(f1262,plain,(
    ! [X19,X17,X15,X18,X16] : k5_enumset1(X15,X16,X15,X16,X17,X18,X19) = k2_xboole_0(k3_tarski(k1_tarski(k2_tarski(X15,X16))),k1_enumset1(X17,X18,X19)) ),
    inference(superposition,[],[f330,f301])).

fof(f330,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(forward_demodulation,[],[f324,f39])).

fof(f324,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(superposition,[],[f211,f35])).

fof(f1657,plain,(
    ! [X14,X12,X15,X13,X11] : k6_enumset1(X11,X12,X11,X11,X11,X13,X14,X15) = k2_xboole_0(k2_xboole_0(k1_tarski(X12),k1_tarski(X11)),k1_enumset1(X13,X14,X15)) ),
    inference(superposition,[],[f211,f1588])).

fof(f1588,plain,(
    ! [X4,X5] : k2_xboole_0(k1_tarski(X4),k1_tarski(X5)) = k3_enumset1(X5,X4,X5,X5,X5) ),
    inference(superposition,[],[f1553,f929])).

fof(f929,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X5,X6,X7,X7) = k3_enumset1(X5,X4,X6,X7,X7) ),
    inference(superposition,[],[f755,f278])).

fof(f278,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X1,X2,X3,X0,X0) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)) ),
    inference(superposition,[],[f272,f25])).

fof(f755,plain,(
    ! [X6,X8,X7,X5] : k3_enumset1(X5,X6,X7,X8,X8) = k2_xboole_0(k1_enumset1(X6,X5,X7),k1_tarski(X8)) ),
    inference(superposition,[],[f278,f29])).

fof(f1553,plain,(
    ! [X8,X7] : k2_xboole_0(k1_tarski(X8),k1_tarski(X7)) = k3_enumset1(X8,X7,X7,X7,X7) ),
    inference(superposition,[],[f740,f317])).

fof(f2326,plain,(
    ! [X26,X24,X23,X25,X22] : k6_enumset1(X22,X23,X22,X22,X22,X24,X25,X26) = k4_enumset1(X23,X22,X22,X25,X24,X26) ),
    inference(forward_demodulation,[],[f2311,f1275])).

fof(f1275,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(forward_demodulation,[],[f1259,f38])).

fof(f1259,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(superposition,[],[f330,f32])).

fof(f2311,plain,(
    ! [X26,X24,X23,X25,X22] : k6_enumset1(X22,X23,X22,X22,X22,X24,X25,X26) = k2_xboole_0(k1_enumset1(X23,X22,X22),k1_enumset1(X25,X24,X26)) ),
    inference(superposition,[],[f326,f1876])).

fof(f1876,plain,(
    ! [X6,X7] : k1_enumset1(X6,X7,X7) = k3_enumset1(X7,X6,X7,X7,X7) ),
    inference(superposition,[],[f1830,f929])).

fof(f326,plain,(
    ! [X14,X12,X10,X8,X7,X13,X11,X9] : k6_enumset1(X10,X11,X12,X13,X14,X7,X8,X9) = k2_xboole_0(k3_enumset1(X10,X11,X12,X13,X14),k1_enumset1(X8,X7,X9)) ),
    inference(superposition,[],[f211,f29])).

fof(f24,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:23:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (9733)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (9747)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (9738)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (9748)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.52  % (9737)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.52  % (9740)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (9734)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.52  % (9746)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.53  % (9742)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.53  % (9736)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.53  % (9750)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.54  % (9741)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.54  % (9732)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.55  % (9744)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.56  % (9749)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.56  % (9735)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.57  % (9744)Refutation not found, incomplete strategy% (9744)------------------------------
% 0.21/0.57  % (9744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (9744)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (9744)Memory used [KB]: 10618
% 0.21/0.57  % (9744)Time elapsed: 0.131 s
% 0.21/0.57  % (9744)------------------------------
% 0.21/0.57  % (9744)------------------------------
% 0.21/0.57  % (9739)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.58  % (9751)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 5.70/1.13  % (9736)Time limit reached!
% 5.70/1.13  % (9736)------------------------------
% 5.70/1.13  % (9736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.70/1.13  % (9736)Termination reason: Time limit
% 5.70/1.13  % (9736)Termination phase: Saturation
% 5.70/1.13  
% 5.70/1.13  % (9736)Memory used [KB]: 11513
% 5.70/1.13  % (9736)Time elapsed: 0.600 s
% 5.70/1.13  % (9736)------------------------------
% 5.70/1.13  % (9736)------------------------------
% 7.71/1.34  % (9735)Refutation found. Thanks to Tanya!
% 7.71/1.34  % SZS status Theorem for theBenchmark
% 7.71/1.35  % SZS output start Proof for theBenchmark
% 7.71/1.35  fof(f10680,plain,(
% 7.71/1.35    $false),
% 7.71/1.35    inference(subsumption_resolution,[],[f10679,f30])).
% 7.71/1.35  fof(f30,plain,(
% 7.71/1.35    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 7.71/1.35    inference(cnf_transformation,[],[f18])).
% 7.71/1.35  fof(f18,axiom,(
% 7.71/1.35    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 7.71/1.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 7.71/1.35  fof(f10679,plain,(
% 7.71/1.35    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(sK3,sK4))),
% 7.71/1.35    inference(forward_demodulation,[],[f10678,f34])).
% 7.71/1.35  fof(f34,plain,(
% 7.71/1.35    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 7.71/1.35    inference(cnf_transformation,[],[f16])).
% 7.71/1.35  fof(f16,axiom,(
% 7.71/1.35    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 7.71/1.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 7.71/1.35  fof(f10678,plain,(
% 7.71/1.35    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(sK3,sK4))),
% 7.71/1.35    inference(superposition,[],[f10558,f413])).
% 7.71/1.35  fof(f413,plain,(
% 7.71/1.35    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5))) )),
% 7.71/1.35    inference(forward_demodulation,[],[f401,f31])).
% 7.71/1.35  fof(f31,plain,(
% 7.71/1.35    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 7.71/1.35    inference(cnf_transformation,[],[f17])).
% 7.71/1.35  fof(f17,axiom,(
% 7.71/1.35    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 7.71/1.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 7.71/1.35  fof(f401,plain,(
% 7.71/1.35    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5))) )),
% 7.71/1.35    inference(superposition,[],[f96,f31])).
% 7.71/1.35  fof(f96,plain,(
% 7.71/1.35    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 7.71/1.35    inference(forward_demodulation,[],[f90,f31])).
% 7.71/1.35  fof(f90,plain,(
% 7.71/1.35    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 7.71/1.35    inference(superposition,[],[f36,f31])).
% 7.71/1.35  fof(f36,plain,(
% 7.71/1.35    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 7.71/1.35    inference(cnf_transformation,[],[f15])).
% 7.71/1.35  fof(f15,axiom,(
% 7.71/1.35    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 7.71/1.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 7.71/1.35  fof(f10558,plain,(
% 7.71/1.35    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK1,sK2,sK4))),
% 7.71/1.35    inference(superposition,[],[f24,f9946])).
% 7.71/1.35  fof(f9946,plain,(
% 7.71/1.35    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X6,X5,X7)) )),
% 7.71/1.35    inference(superposition,[],[f8919,f35])).
% 7.71/1.35  fof(f35,plain,(
% 7.71/1.35    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.71/1.35    inference(cnf_transformation,[],[f9])).
% 7.71/1.35  fof(f9,axiom,(
% 7.71/1.35    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 7.71/1.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 7.71/1.35  fof(f8919,plain,(
% 7.71/1.35    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)) )),
% 7.71/1.35    inference(forward_demodulation,[],[f8896,f35])).
% 7.71/1.35  fof(f8896,plain,(
% 7.71/1.35    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X1,X3)) )),
% 7.71/1.35    inference(superposition,[],[f3434,f37])).
% 7.71/1.35  fof(f37,plain,(
% 7.71/1.35    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.71/1.35    inference(cnf_transformation,[],[f10])).
% 7.71/1.35  fof(f10,axiom,(
% 7.71/1.35    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.71/1.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 7.71/1.35  fof(f3434,plain,(
% 7.71/1.35    ( ! [X26,X24,X23,X25,X22] : (k3_enumset1(X23,X22,X24,X25,X26) = k4_enumset1(X23,X22,X22,X25,X24,X26)) )),
% 7.71/1.35    inference(backward_demodulation,[],[f2326,f3424])).
% 7.71/1.35  fof(f3424,plain,(
% 7.71/1.35    ( ! [X14,X12,X15,X13,X11] : (k6_enumset1(X11,X12,X11,X11,X11,X13,X14,X15) = k3_enumset1(X12,X11,X13,X14,X15)) )),
% 7.71/1.35    inference(backward_demodulation,[],[f1657,f3420])).
% 7.71/1.35  fof(f3420,plain,(
% 7.71/1.35    ( ! [X19,X17,X15,X18,X16] : (k3_enumset1(X15,X16,X17,X18,X19) = k2_xboole_0(k2_xboole_0(k1_tarski(X15),k1_tarski(X16)),k1_enumset1(X17,X18,X19))) )),
% 7.71/1.35    inference(backward_demodulation,[],[f2004,f3418])).
% 7.71/1.35  fof(f3418,plain,(
% 7.71/1.35    ( ! [X14,X17,X15,X13,X16] : (k3_enumset1(X13,X14,X15,X16,X17) = k5_enumset1(X13,X14,X13,X14,X15,X16,X17)) )),
% 7.71/1.35    inference(forward_demodulation,[],[f3396,f272])).
% 7.71/1.35  fof(f272,plain,(
% 7.71/1.35    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 7.71/1.35    inference(forward_demodulation,[],[f264,f37])).
% 7.71/1.35  fof(f264,plain,(
% 7.71/1.35    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 7.71/1.35    inference(superposition,[],[f254,f32])).
% 7.71/1.35  fof(f32,plain,(
% 7.71/1.35    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.71/1.35    inference(cnf_transformation,[],[f8])).
% 7.71/1.35  fof(f8,axiom,(
% 7.71/1.35    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 7.71/1.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 7.71/1.35  fof(f254,plain,(
% 7.71/1.35    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 7.71/1.35    inference(forward_demodulation,[],[f247,f38])).
% 7.71/1.35  fof(f38,plain,(
% 7.71/1.35    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.71/1.35    inference(cnf_transformation,[],[f11])).
% 7.71/1.35  fof(f11,axiom,(
% 7.71/1.35    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.71/1.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 7.71/1.35  fof(f247,plain,(
% 7.71/1.35    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 7.71/1.35    inference(superposition,[],[f130,f35])).
% 7.71/1.35  fof(f130,plain,(
% 7.71/1.35    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 7.71/1.35    inference(forward_demodulation,[],[f126,f39])).
% 7.71/1.35  fof(f39,plain,(
% 7.71/1.35    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.71/1.35    inference(cnf_transformation,[],[f12])).
% 7.71/1.35  fof(f12,axiom,(
% 7.71/1.35    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.71/1.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 7.71/1.35  fof(f126,plain,(
% 7.71/1.35    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 7.71/1.35    inference(superposition,[],[f40,f37])).
% 7.71/1.35  fof(f40,plain,(
% 7.71/1.35    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 7.71/1.35    inference(cnf_transformation,[],[f5])).
% 7.71/1.35  fof(f5,axiom,(
% 7.71/1.35    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 7.71/1.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).
% 7.71/1.35  fof(f3396,plain,(
% 7.71/1.35    ( ! [X14,X17,X15,X13,X16] : (k2_xboole_0(k1_enumset1(X13,X14,X15),k2_tarski(X16,X17)) = k5_enumset1(X13,X14,X13,X14,X15,X16,X17)) )),
% 7.71/1.35    inference(superposition,[],[f130,f3029])).
% 7.71/1.35  fof(f3029,plain,(
% 7.71/1.35    ( ! [X14,X15,X16] : (k1_enumset1(X15,X14,X16) = k3_enumset1(X15,X14,X15,X14,X16)) )),
% 7.71/1.35    inference(superposition,[],[f2966,f1255])).
% 7.71/1.35  fof(f1255,plain,(
% 7.71/1.35    ( ! [X6,X8,X7,X5,X9] : (k3_enumset1(X5,X6,X7,X8,X9) = k3_enumset1(X6,X5,X7,X8,X9)) )),
% 7.71/1.35    inference(superposition,[],[f274,f272])).
% 7.71/1.35  fof(f274,plain,(
% 7.71/1.35    ( ! [X6,X4,X8,X7,X5] : (k3_enumset1(X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X5,X4,X6),k2_tarski(X7,X8))) )),
% 7.71/1.35    inference(superposition,[],[f272,f29])).
% 7.71/1.35  fof(f29,plain,(
% 7.71/1.35    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)) )),
% 7.71/1.35    inference(cnf_transformation,[],[f13])).
% 7.71/1.35  fof(f13,axiom,(
% 7.71/1.35    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 7.71/1.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).
% 7.71/1.35  fof(f2966,plain,(
% 7.71/1.35    ( ! [X2,X0,X1] : (k1_enumset1(X1,X0,X2) = k3_enumset1(X0,X1,X1,X0,X2)) )),
% 7.71/1.35    inference(superposition,[],[f2546,f1551])).
% 7.71/1.35  fof(f1551,plain,(
% 7.71/1.35    ( ! [X2,X0,X3,X1] : (k3_enumset1(X3,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))) )),
% 7.71/1.35    inference(superposition,[],[f740,f32])).
% 7.71/1.35  fof(f740,plain,(
% 7.71/1.35    ( ! [X6,X10,X8,X7,X9] : (k2_xboole_0(k1_tarski(X6),k2_enumset1(X7,X8,X9,X10)) = k3_enumset1(X6,X7,X8,X9,X10)) )),
% 7.71/1.35    inference(backward_demodulation,[],[f347,f739])).
% 7.71/1.35  fof(f739,plain,(
% 7.71/1.35    ( ! [X35,X33,X31,X34,X32] : (k6_enumset1(X31,X31,X31,X31,X32,X33,X34,X35) = k3_enumset1(X31,X32,X33,X34,X35)) )),
% 7.71/1.35    inference(forward_demodulation,[],[f738,f272])).
% 7.71/1.35  fof(f738,plain,(
% 7.71/1.35    ( ! [X35,X33,X31,X34,X32] : (k6_enumset1(X31,X31,X31,X31,X32,X33,X34,X35) = k2_xboole_0(k1_enumset1(X31,X32,X33),k2_tarski(X34,X35))) )),
% 7.71/1.35    inference(superposition,[],[f40,f355])).
% 7.71/1.35  fof(f355,plain,(
% 7.71/1.35    ( ! [X12,X13,X11] : (k4_enumset1(X11,X11,X11,X11,X12,X13) = k1_enumset1(X11,X12,X13)) )),
% 7.71/1.35    inference(forward_demodulation,[],[f348,f303])).
% 7.71/1.35  fof(f303,plain,(
% 7.71/1.35    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 7.71/1.35    inference(forward_demodulation,[],[f289,f32])).
% 7.71/1.35  fof(f289,plain,(
% 7.71/1.35    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 7.71/1.35    inference(superposition,[],[f284,f25])).
% 7.71/1.35  fof(f25,plain,(
% 7.71/1.35    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.71/1.35    inference(cnf_transformation,[],[f6])).
% 7.71/1.35  fof(f6,axiom,(
% 7.71/1.35    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.71/1.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 7.71/1.35  fof(f284,plain,(
% 7.71/1.35    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 7.71/1.35    inference(forward_demodulation,[],[f273,f35])).
% 7.71/1.35  fof(f273,plain,(
% 7.71/1.35    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 7.71/1.35    inference(superposition,[],[f272,f27])).
% 7.71/1.35  fof(f27,plain,(
% 7.71/1.35    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.71/1.35    inference(cnf_transformation,[],[f7])).
% 7.71/1.35  fof(f7,axiom,(
% 7.71/1.35    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.71/1.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 7.71/1.35  fof(f348,plain,(
% 7.71/1.35    ( ! [X12,X13,X11] : (k4_enumset1(X11,X11,X11,X11,X12,X13) = k2_xboole_0(k1_tarski(X11),k2_tarski(X12,X13))) )),
% 7.71/1.35    inference(superposition,[],[f254,f317])).
% 7.71/1.35  fof(f317,plain,(
% 7.71/1.35    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.71/1.35    inference(backward_demodulation,[],[f308,f316])).
% 7.71/1.35  fof(f316,plain,(
% 7.71/1.35    ( ! [X0] : (k1_tarski(X0) = k3_tarski(k1_tarski(k1_tarski(X0)))) )),
% 7.71/1.35    inference(forward_demodulation,[],[f315,f25])).
% 7.71/1.35  fof(f315,plain,(
% 7.71/1.35    ( ! [X0] : (k2_tarski(X0,X0) = k3_tarski(k1_tarski(k2_tarski(X0,X0)))) )),
% 7.71/1.35    inference(forward_demodulation,[],[f309,f27])).
% 7.71/1.35  fof(f309,plain,(
% 7.71/1.35    ( ! [X0] : (k3_tarski(k1_tarski(k2_tarski(X0,X0))) = k1_enumset1(X0,X0,X0)) )),
% 7.71/1.35    inference(superposition,[],[f301,f32])).
% 7.71/1.35  fof(f301,plain,(
% 7.71/1.35    ( ! [X4,X5] : (k3_tarski(k1_tarski(k2_tarski(X4,X5))) = k2_enumset1(X4,X5,X4,X5)) )),
% 7.71/1.35    inference(superposition,[],[f284,f44])).
% 7.71/1.35  fof(f44,plain,(
% 7.71/1.35    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))) )),
% 7.71/1.35    inference(superposition,[],[f26,f25])).
% 7.71/1.35  fof(f26,plain,(
% 7.71/1.35    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.71/1.35    inference(cnf_transformation,[],[f14])).
% 7.71/1.35  fof(f14,axiom,(
% 7.71/1.35    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.71/1.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 7.71/1.35  fof(f308,plain,(
% 7.71/1.35    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0)))) )),
% 7.71/1.35    inference(superposition,[],[f301,f25])).
% 7.71/1.35  fof(f347,plain,(
% 7.71/1.35    ( ! [X6,X10,X8,X7,X9] : (k6_enumset1(X6,X6,X6,X6,X7,X8,X9,X10) = k2_xboole_0(k1_tarski(X6),k2_enumset1(X7,X8,X9,X10))) )),
% 7.71/1.35    inference(superposition,[],[f212,f317])).
% 7.71/1.35  fof(f212,plain,(
% 7.71/1.35    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 7.71/1.35    inference(backward_demodulation,[],[f155,f210])).
% 7.71/1.35  fof(f210,plain,(
% 7.71/1.35    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.71/1.35    inference(forward_demodulation,[],[f204,f40])).
% 7.71/1.35  fof(f204,plain,(
% 7.71/1.35    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.71/1.35    inference(superposition,[],[f43,f38])).
% 7.71/1.35  fof(f43,plain,(
% 7.71/1.35    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) )),
% 7.71/1.35    inference(cnf_transformation,[],[f4])).
% 7.71/1.35  fof(f4,axiom,(
% 7.71/1.35    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 7.71/1.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).
% 7.71/1.35  fof(f155,plain,(
% 7.71/1.35    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 7.71/1.35    inference(superposition,[],[f41,f35])).
% 7.71/1.35  fof(f41,plain,(
% 7.71/1.35    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 7.71/1.35    inference(cnf_transformation,[],[f2])).
% 7.71/1.35  fof(f2,axiom,(
% 7.71/1.35    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 7.71/1.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).
% 7.71/1.35  fof(f2546,plain,(
% 7.71/1.35    ( ! [X4,X5,X3] : (k1_enumset1(X4,X3,X5) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X4,X3,X5))) )),
% 7.71/1.35    inference(superposition,[],[f1823,f29])).
% 7.71/1.35  fof(f1823,plain,(
% 7.71/1.35    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2))) )),
% 7.71/1.35    inference(forward_demodulation,[],[f1784,f32])).
% 7.71/1.35  fof(f1784,plain,(
% 7.71/1.35    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2))) )),
% 7.71/1.35    inference(superposition,[],[f1551,f35])).
% 7.71/1.35  fof(f2004,plain,(
% 7.71/1.35    ( ! [X19,X17,X15,X18,X16] : (k5_enumset1(X15,X16,X15,X16,X17,X18,X19) = k2_xboole_0(k2_xboole_0(k1_tarski(X15),k1_tarski(X16)),k1_enumset1(X17,X18,X19))) )),
% 7.71/1.35    inference(backward_demodulation,[],[f1262,f1955])).
% 7.71/1.35  fof(f1955,plain,(
% 7.71/1.35    ( ! [X10,X9] : (k2_xboole_0(k1_tarski(X10),k1_tarski(X9)) = k3_tarski(k1_tarski(k2_tarski(X10,X9)))) )),
% 7.71/1.35    inference(superposition,[],[f1884,f419])).
% 7.71/1.35  fof(f419,plain,(
% 7.71/1.35    ( ! [X2,X3] : (k1_enumset1(X3,X2,X3) = k2_xboole_0(k1_tarski(X2),k1_tarski(X3))) )),
% 7.71/1.35    inference(superposition,[],[f393,f29])).
% 7.71/1.35  fof(f393,plain,(
% 7.71/1.35    ( ! [X0,X1] : (k1_enumset1(X1,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) )),
% 7.71/1.35    inference(superposition,[],[f303,f25])).
% 7.71/1.35  fof(f1884,plain,(
% 7.71/1.35    ( ! [X23,X22] : (k3_tarski(k1_tarski(k2_tarski(X23,X22))) = k1_enumset1(X22,X23,X22)) )),
% 7.71/1.35    inference(superposition,[],[f1830,f1282])).
% 7.71/1.35  fof(f1282,plain,(
% 7.71/1.35    ( ! [X39,X38] : (k3_tarski(k1_tarski(k2_tarski(X38,X39))) = k3_enumset1(X39,X38,X38,X38,X39)) )),
% 7.71/1.35    inference(superposition,[],[f1255,f1110])).
% 7.71/1.35  fof(f1110,plain,(
% 7.71/1.35    ( ! [X0,X1] : (k3_tarski(k1_tarski(k2_tarski(X0,X1))) = k3_enumset1(X0,X1,X0,X0,X1)) )),
% 7.71/1.35    inference(forward_demodulation,[],[f1098,f27])).
% 7.71/1.35  fof(f1098,plain,(
% 7.71/1.35    ( ! [X0,X1] : (k3_tarski(k1_tarski(k1_enumset1(X0,X0,X1))) = k3_enumset1(X0,X1,X0,X0,X1)) )),
% 7.71/1.35    inference(superposition,[],[f1059,f37])).
% 7.71/1.35  fof(f1059,plain,(
% 7.71/1.35    ( ! [X2,X0,X1] : (k3_tarski(k1_tarski(k1_enumset1(X0,X1,X2))) = k4_enumset1(X0,X1,X2,X0,X1,X2)) )),
% 7.71/1.35    inference(superposition,[],[f1014,f38])).
% 7.71/1.35  fof(f1014,plain,(
% 7.71/1.35    ( ! [X43,X41,X42] : (k5_enumset1(X41,X41,X42,X43,X41,X42,X43) = k3_tarski(k1_tarski(k1_enumset1(X41,X42,X43)))) )),
% 7.71/1.35    inference(forward_demodulation,[],[f1004,f32])).
% 7.71/1.35  fof(f1004,plain,(
% 7.71/1.35    ( ! [X43,X41,X42] : (k3_tarski(k1_tarski(k2_enumset1(X41,X41,X42,X43))) = k5_enumset1(X41,X41,X42,X43,X41,X42,X43)) )),
% 7.71/1.35    inference(superposition,[],[f306,f338])).
% 7.71/1.35  fof(f338,plain,(
% 7.71/1.35    ( ! [X10,X8,X11,X9] : (k3_tarski(k1_tarski(k2_enumset1(X8,X9,X10,X11))) = k6_enumset1(X8,X9,X10,X11,X8,X9,X10,X11)) )),
% 7.71/1.35    inference(superposition,[],[f212,f44])).
% 7.71/1.35  fof(f306,plain,(
% 7.71/1.35    ( ! [X21,X19,X17,X15,X20,X18,X16] : (k6_enumset1(X15,X16,X17,X18,X19,X19,X20,X21) = k5_enumset1(X15,X16,X17,X18,X19,X20,X21)) )),
% 7.71/1.35    inference(forward_demodulation,[],[f304,f39])).
% 7.71/1.35  fof(f304,plain,(
% 7.71/1.35    ( ! [X21,X19,X17,X15,X20,X18,X16] : (k6_enumset1(X15,X16,X17,X18,X19,X19,X20,X21) = k6_enumset1(X15,X15,X16,X17,X18,X19,X20,X21)) )),
% 7.71/1.35    inference(superposition,[],[f213,f210])).
% 7.71/1.35  fof(f213,plain,(
% 7.71/1.35    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X3,X4,X5,X6,X7,X0,X0,X1,X2) = k6_enumset1(X3,X4,X5,X6,X7,X0,X1,X2)) )),
% 7.71/1.35    inference(backward_demodulation,[],[f156,f211])).
% 7.71/1.35  fof(f211,plain,(
% 7.71/1.35    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 7.71/1.35    inference(backward_demodulation,[],[f190,f210])).
% 7.71/1.35  fof(f190,plain,(
% 7.71/1.35    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 7.71/1.35    inference(superposition,[],[f42,f37])).
% 7.71/1.35  fof(f42,plain,(
% 7.71/1.35    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))) )),
% 7.71/1.35    inference(cnf_transformation,[],[f3])).
% 7.71/1.35  fof(f3,axiom,(
% 7.71/1.35    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 7.71/1.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).
% 7.71/1.35  fof(f156,plain,(
% 7.71/1.35    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X3,X4,X5,X6,X7,X0,X0,X1,X2) = k2_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k1_enumset1(X0,X1,X2))) )),
% 7.71/1.35    inference(superposition,[],[f41,f32])).
% 7.71/1.35  fof(f1830,plain,(
% 7.71/1.35    ( ! [X2,X0,X1] : (k3_enumset1(X2,X0,X0,X0,X1) = k1_enumset1(X2,X0,X1)) )),
% 7.71/1.35    inference(forward_demodulation,[],[f1798,f303])).
% 7.71/1.35  fof(f1798,plain,(
% 7.71/1.35    ( ! [X2,X0,X1] : (k3_enumset1(X2,X0,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))) )),
% 7.71/1.35    inference(superposition,[],[f1551,f27])).
% 7.71/1.35  fof(f1262,plain,(
% 7.71/1.35    ( ! [X19,X17,X15,X18,X16] : (k5_enumset1(X15,X16,X15,X16,X17,X18,X19) = k2_xboole_0(k3_tarski(k1_tarski(k2_tarski(X15,X16))),k1_enumset1(X17,X18,X19))) )),
% 7.71/1.35    inference(superposition,[],[f330,f301])).
% 7.71/1.35  fof(f330,plain,(
% 7.71/1.35    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 7.71/1.35    inference(forward_demodulation,[],[f324,f39])).
% 7.71/1.35  fof(f324,plain,(
% 7.71/1.35    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 7.71/1.35    inference(superposition,[],[f211,f35])).
% 7.71/1.35  fof(f1657,plain,(
% 7.71/1.35    ( ! [X14,X12,X15,X13,X11] : (k6_enumset1(X11,X12,X11,X11,X11,X13,X14,X15) = k2_xboole_0(k2_xboole_0(k1_tarski(X12),k1_tarski(X11)),k1_enumset1(X13,X14,X15))) )),
% 7.71/1.35    inference(superposition,[],[f211,f1588])).
% 7.71/1.35  fof(f1588,plain,(
% 7.71/1.35    ( ! [X4,X5] : (k2_xboole_0(k1_tarski(X4),k1_tarski(X5)) = k3_enumset1(X5,X4,X5,X5,X5)) )),
% 7.71/1.35    inference(superposition,[],[f1553,f929])).
% 7.71/1.35  fof(f929,plain,(
% 7.71/1.35    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X5,X6,X7,X7) = k3_enumset1(X5,X4,X6,X7,X7)) )),
% 7.71/1.35    inference(superposition,[],[f755,f278])).
% 7.71/1.35  fof(f278,plain,(
% 7.71/1.35    ( ! [X2,X0,X3,X1] : (k3_enumset1(X1,X2,X3,X0,X0) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))) )),
% 7.71/1.35    inference(superposition,[],[f272,f25])).
% 7.71/1.35  fof(f755,plain,(
% 7.71/1.35    ( ! [X6,X8,X7,X5] : (k3_enumset1(X5,X6,X7,X8,X8) = k2_xboole_0(k1_enumset1(X6,X5,X7),k1_tarski(X8))) )),
% 7.71/1.35    inference(superposition,[],[f278,f29])).
% 7.71/1.35  fof(f1553,plain,(
% 7.71/1.35    ( ! [X8,X7] : (k2_xboole_0(k1_tarski(X8),k1_tarski(X7)) = k3_enumset1(X8,X7,X7,X7,X7)) )),
% 7.71/1.35    inference(superposition,[],[f740,f317])).
% 7.71/1.35  fof(f2326,plain,(
% 7.71/1.35    ( ! [X26,X24,X23,X25,X22] : (k6_enumset1(X22,X23,X22,X22,X22,X24,X25,X26) = k4_enumset1(X23,X22,X22,X25,X24,X26)) )),
% 7.71/1.35    inference(forward_demodulation,[],[f2311,f1275])).
% 7.71/1.35  fof(f1275,plain,(
% 7.71/1.35    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 7.71/1.35    inference(forward_demodulation,[],[f1259,f38])).
% 7.71/1.35  fof(f1259,plain,(
% 7.71/1.35    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 7.71/1.35    inference(superposition,[],[f330,f32])).
% 7.71/1.35  fof(f2311,plain,(
% 7.71/1.35    ( ! [X26,X24,X23,X25,X22] : (k6_enumset1(X22,X23,X22,X22,X22,X24,X25,X26) = k2_xboole_0(k1_enumset1(X23,X22,X22),k1_enumset1(X25,X24,X26))) )),
% 7.71/1.35    inference(superposition,[],[f326,f1876])).
% 7.71/1.35  fof(f1876,plain,(
% 7.71/1.35    ( ! [X6,X7] : (k1_enumset1(X6,X7,X7) = k3_enumset1(X7,X6,X7,X7,X7)) )),
% 7.71/1.35    inference(superposition,[],[f1830,f929])).
% 7.71/1.35  fof(f326,plain,(
% 7.71/1.35    ( ! [X14,X12,X10,X8,X7,X13,X11,X9] : (k6_enumset1(X10,X11,X12,X13,X14,X7,X8,X9) = k2_xboole_0(k3_enumset1(X10,X11,X12,X13,X14),k1_enumset1(X8,X7,X9))) )),
% 7.71/1.35    inference(superposition,[],[f211,f29])).
% 7.71/1.35  fof(f24,plain,(
% 7.71/1.35    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 7.71/1.35    inference(cnf_transformation,[],[f23])).
% 7.71/1.35  fof(f23,plain,(
% 7.71/1.35    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 7.71/1.35    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f22])).
% 7.71/1.35  fof(f22,plain,(
% 7.71/1.35    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 7.71/1.35    introduced(choice_axiom,[])).
% 7.71/1.35  fof(f21,plain,(
% 7.71/1.35    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 7.71/1.35    inference(ennf_transformation,[],[f20])).
% 7.71/1.35  fof(f20,negated_conjecture,(
% 7.71/1.35    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 7.71/1.35    inference(negated_conjecture,[],[f19])).
% 7.71/1.35  fof(f19,conjecture,(
% 7.71/1.35    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 7.71/1.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).
% 7.71/1.35  % SZS output end Proof for theBenchmark
% 7.71/1.35  % (9735)------------------------------
% 7.71/1.35  % (9735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.71/1.35  % (9735)Termination reason: Refutation
% 7.71/1.35  
% 7.71/1.35  % (9735)Memory used [KB]: 13048
% 7.71/1.35  % (9735)Time elapsed: 0.911 s
% 7.71/1.35  % (9735)------------------------------
% 7.71/1.35  % (9735)------------------------------
% 7.71/1.35  % (9725)Success in time 0.996 s
%------------------------------------------------------------------------------
