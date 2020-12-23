%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:01 EST 2020

% Result     : Theorem 30.34s
% Output     : Refutation 30.34s
% Verified   : 
% Statistics : Number of formulae       :  160 (12153 expanded)
%              Number of leaves         :   20 (4051 expanded)
%              Depth                    :   41
%              Number of atoms          :  162 (12155 expanded)
%              Number of equality atoms :  161 (12154 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f38448,plain,(
    $false ),
    inference(subsumption_resolution,[],[f38447,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f38447,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(forward_demodulation,[],[f38446,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f38446,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) ),
    inference(superposition,[],[f38256,f1233])).

fof(f1233,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5)) ),
    inference(forward_demodulation,[],[f1220,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f1220,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5)) ),
    inference(superposition,[],[f155,f33])).

fof(f155,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f149,f33])).

fof(f149,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(superposition,[],[f38,f33])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f38256,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(superposition,[],[f37918,f32830])).

fof(f32830,plain,(
    ! [X123,X121,X122,X120] : k2_enumset1(X120,X121,X123,X122) = k2_enumset1(X120,X121,X122,X123) ),
    inference(superposition,[],[f21128,f1084])).

fof(f1084,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(forward_demodulation,[],[f1078,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f1078,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X3) = k3_enumset1(X0,X0,X1,X3,X2) ),
    inference(superposition,[],[f1063,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f1063,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X4) = k3_enumset1(X0,X1,X2,X4,X3) ),
    inference(forward_demodulation,[],[f1060,f39])).

fof(f1060,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X4) = k4_enumset1(X0,X0,X1,X2,X4,X3) ),
    inference(superposition,[],[f1059,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f1059,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X0,X5) ),
    inference(backward_demodulation,[],[f673,f1057])).

fof(f1057,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X5,X4) ),
    inference(forward_demodulation,[],[f1052,f40])).

fof(f1052,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k5_enumset1(X0,X0,X1,X2,X3,X5,X4) ),
    inference(superposition,[],[f955,f39])).

fof(f955,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0)) = k5_enumset1(X1,X2,X3,X4,X5,X0,X6) ),
    inference(backward_demodulation,[],[f186,f953])).

fof(f953,plain,(
    ! [X30,X35,X33,X31,X36,X34,X32] : k6_enumset1(X32,X33,X34,X35,X36,X30,X31,X31) = k5_enumset1(X32,X33,X34,X35,X36,X31,X30) ),
    inference(forward_demodulation,[],[f944,f196])).

fof(f196,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(forward_demodulation,[],[f185,f41])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f185,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(superposition,[],[f42,f39])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

fof(f944,plain,(
    ! [X30,X35,X33,X31,X36,X34,X32] : k6_enumset1(X32,X33,X34,X35,X36,X30,X31,X31) = k2_xboole_0(k3_enumset1(X32,X33,X34,X35,X36),k2_tarski(X31,X30)) ),
    inference(superposition,[],[f331,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[],[f31,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

fof(f331,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(backward_demodulation,[],[f265,f330])).

fof(f330,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(forward_demodulation,[],[f318,f42])).

fof(f318,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(superposition,[],[f45,f40])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).

fof(f265,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(superposition,[],[f44,f39])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).

fof(f186,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X0) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0)) ),
    inference(superposition,[],[f42,f26])).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f673,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0)) ),
    inference(superposition,[],[f196,f26])).

fof(f21128,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X1,X2,X3,X0,X0) = k2_enumset1(X1,X2,X3,X0) ),
    inference(forward_demodulation,[],[f21001,f21033])).

fof(f21033,plain,(
    ! [X47,X45,X48,X46] : k2_enumset1(X45,X46,X47,X48) = k2_xboole_0(k1_enumset1(X45,X46,X47),k1_tarski(X48)) ),
    inference(backward_demodulation,[],[f5459,f21026])).

fof(f21026,plain,(
    ! [X24,X23,X21,X22] : k2_xboole_0(k1_tarski(X21),k1_enumset1(X22,X23,X24)) = k2_enumset1(X21,X22,X24,X23) ),
    inference(backward_demodulation,[],[f12127,f21025])).

fof(f21025,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f20981,f37])).

fof(f20981,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X3)) ),
    inference(superposition,[],[f1746,f1163])).

fof(f1163,plain,(
    ! [X2,X1] : k2_tarski(X2,X1) = k1_enumset1(X1,X1,X2) ),
    inference(superposition,[],[f1134,f31])).

fof(f1134,plain,(
    ! [X0,X1] : k2_tarski(X1,X0) = k1_enumset1(X0,X1,X0) ),
    inference(forward_demodulation,[],[f1127,f56])).

fof(f1127,plain,(
    ! [X0,X1] : k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1) ),
    inference(superposition,[],[f1103,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f1103,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X1,X2,X2) = k1_enumset1(X0,X2,X1) ),
    inference(forward_demodulation,[],[f1098,f34])).

fof(f1098,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X1,X2,X2) = k2_enumset1(X0,X0,X2,X1) ),
    inference(superposition,[],[f1084,f37])).

fof(f1746,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f1719,f39])).

fof(f1719,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(superposition,[],[f687,f34])).

fof(f687,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(forward_demodulation,[],[f672,f40])).

fof(f672,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f196,f37])).

fof(f12127,plain,(
    ! [X24,X23,X21,X22] : k2_xboole_0(k2_tarski(X22,X21),k2_tarski(X24,X23)) = k2_xboole_0(k1_tarski(X21),k1_enumset1(X22,X23,X24)) ),
    inference(forward_demodulation,[],[f12096,f5478])).

fof(f5478,plain,(
    ! [X4,X2,X5,X3] : k6_enumset1(X2,X2,X2,X2,X3,X2,X4,X5) = k2_xboole_0(k1_tarski(X2),k1_enumset1(X3,X4,X5)) ),
    inference(backward_demodulation,[],[f3006,f5468])).

fof(f5468,plain,(
    ! [X17,X15,X18,X16] : k2_xboole_0(k2_tarski(X15,X16),k2_tarski(X18,X17)) = k2_xboole_0(k1_tarski(X15),k1_enumset1(X16,X18,X17)) ),
    inference(backward_demodulation,[],[f4342,f5459])).

fof(f4342,plain,(
    ! [X17,X15,X18,X16] : k2_xboole_0(k1_enumset1(X15,X16,X17),k1_tarski(X18)) = k2_xboole_0(k2_tarski(X15,X16),k2_tarski(X18,X17)) ),
    inference(forward_demodulation,[],[f4315,f1723])).

fof(f1723,plain,(
    ! [X23,X21,X22,X20] : k4_enumset1(X20,X21,X20,X21,X22,X23) = k2_xboole_0(k2_tarski(X20,X21),k2_tarski(X22,X23)) ),
    inference(superposition,[],[f687,f1572])).

fof(f1572,plain,(
    ! [X2,X3] : k2_tarski(X2,X3) = k2_enumset1(X2,X3,X2,X3) ),
    inference(forward_demodulation,[],[f1556,f29])).

fof(f1556,plain,(
    ! [X2,X3] : k1_enumset1(X2,X2,X3) = k2_enumset1(X2,X3,X2,X3) ),
    inference(superposition,[],[f1415,f1103])).

fof(f1415,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X1,X2,X1) = k2_enumset1(X0,X1,X2,X0) ),
    inference(superposition,[],[f1333,f37])).

fof(f1333,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X2) = k2_enumset1(X0,X2,X3,X1) ),
    inference(forward_demodulation,[],[f1322,f37])).

fof(f1322,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X2) = k3_enumset1(X0,X0,X2,X3,X1) ),
    inference(superposition,[],[f1285,f39])).

fof(f1285,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X3) = k3_enumset1(X0,X1,X3,X4,X2) ),
    inference(forward_demodulation,[],[f1278,f39])).

fof(f1278,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X3) = k4_enumset1(X0,X0,X1,X3,X4,X2) ),
    inference(superposition,[],[f1086,f40])).

fof(f1086,plain,(
    ! [X6,X4,X8,X7,X5,X9] : k5_enumset1(X4,X5,X6,X7,X8,X9,X8) = k4_enumset1(X4,X5,X6,X8,X9,X7) ),
    inference(forward_demodulation,[],[f1080,f1057])).

fof(f1080,plain,(
    ! [X6,X4,X8,X7,X5,X9] : k5_enumset1(X4,X5,X6,X7,X8,X9,X8) = k2_xboole_0(k3_enumset1(X4,X5,X6,X8,X7),k1_tarski(X9)) ),
    inference(superposition,[],[f955,f1063])).

fof(f4315,plain,(
    ! [X17,X15,X18,X16] : k4_enumset1(X15,X16,X15,X16,X18,X17) = k2_xboole_0(k1_enumset1(X15,X16,X17),k1_tarski(X18)) ),
    inference(superposition,[],[f1057,f4096])).

fof(f4096,plain,(
    ! [X17,X18,X16] : k1_enumset1(X16,X17,X18) = k3_enumset1(X16,X17,X16,X17,X18) ),
    inference(forward_demodulation,[],[f4064,f1422])).

fof(f1422,plain,(
    ! [X4,X5,X3] : k2_enumset1(X3,X5,X5,X4) = k1_enumset1(X3,X5,X4) ),
    inference(forward_demodulation,[],[f1416,f1103])).

fof(f1416,plain,(
    ! [X4,X5,X3] : k2_enumset1(X3,X4,X5,X5) = k2_enumset1(X3,X5,X5,X4) ),
    inference(superposition,[],[f1333,f1084])).

fof(f4064,plain,(
    ! [X17,X18,X16] : k2_enumset1(X16,X17,X17,X18) = k3_enumset1(X16,X17,X16,X17,X18) ),
    inference(superposition,[],[f3536,f1334])).

fof(f1334,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X5,X7,X7,X6) = k2_enumset1(X4,X5,X7,X6) ),
    inference(forward_demodulation,[],[f1323,f1084])).

fof(f1323,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X5,X6,X7,X7) = k3_enumset1(X4,X5,X7,X7,X6) ),
    inference(superposition,[],[f1285,f1063])).

fof(f3536,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X1,X1,X2,X3) = k3_enumset1(X0,X1,X0,X2,X3) ),
    inference(superposition,[],[f1747,f39])).

fof(f1747,plain,(
    ! [X6,X8,X7,X5,X9] : k4_enumset1(X5,X6,X7,X7,X8,X9) = k3_enumset1(X5,X7,X6,X8,X9) ),
    inference(forward_demodulation,[],[f1720,f1746])).

fof(f1720,plain,(
    ! [X6,X8,X7,X5,X9] : k4_enumset1(X5,X6,X7,X7,X8,X9) = k2_xboole_0(k1_enumset1(X5,X7,X6),k2_tarski(X8,X9)) ),
    inference(superposition,[],[f687,f1103])).

fof(f3006,plain,(
    ! [X4,X2,X5,X3] : k6_enumset1(X2,X2,X2,X2,X3,X2,X4,X5) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X4,X5)) ),
    inference(backward_demodulation,[],[f2802,f3003])).

fof(f3003,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(forward_demodulation,[],[f2977,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0) ),
    inference(superposition,[],[f31,f29])).

fof(f2977,plain,(
    ! [X0,X1] : k1_enumset1(X0,X1,X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(superposition,[],[f2918,f34])).

fof(f2918,plain,(
    ! [X4,X5] : k2_enumset1(X4,X4,X5,X4) = k2_xboole_0(k1_tarski(X4),k1_tarski(X5)) ),
    inference(superposition,[],[f2797,f1333])).

fof(f2797,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k3_enumset1(X0,X0,X0,X1,X0) ),
    inference(superposition,[],[f2097,f39])).

fof(f2097,plain,(
    ! [X2,X1] : k4_enumset1(X1,X1,X1,X1,X2,X1) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(backward_demodulation,[],[f2012,f2094])).

fof(f2094,plain,(
    ! [X4] : k1_tarski(X4) = k3_tarski(k1_tarski(k1_tarski(X4))) ),
    inference(forward_demodulation,[],[f2073,f26])).

fof(f2073,plain,(
    ! [X4] : k2_tarski(X4,X4) = k3_tarski(k1_tarski(k1_tarski(X4))) ),
    inference(superposition,[],[f2007,f1572])).

fof(f2007,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0))) ),
    inference(superposition,[],[f1959,f37])).

fof(f1959,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0))) ),
    inference(forward_demodulation,[],[f1945,f26])).

fof(f1945,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k3_tarski(k1_tarski(k2_tarski(X0,X0))) ),
    inference(superposition,[],[f1858,f39])).

fof(f1858,plain,(
    ! [X4,X3] : k4_enumset1(X3,X4,X4,X3,X4,X3) = k3_tarski(k1_tarski(k2_tarski(X4,X3))) ),
    inference(forward_demodulation,[],[f1857,f56])).

fof(f1857,plain,(
    ! [X4,X3] : k4_enumset1(X3,X4,X4,X3,X4,X3) = k3_tarski(k1_tarski(k1_enumset1(X3,X4,X4))) ),
    inference(forward_demodulation,[],[f1849,f34])).

fof(f1849,plain,(
    ! [X4,X3] : k4_enumset1(X3,X4,X4,X3,X4,X3) = k3_tarski(k1_tarski(k2_enumset1(X3,X3,X4,X4))) ),
    inference(superposition,[],[f1070,f1058])).

fof(f1058,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X5) = k4_enumset1(X0,X1,X2,X3,X5,X4) ),
    inference(backward_demodulation,[],[f725,f1057])).

fof(f725,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X5) ),
    inference(superposition,[],[f186,f39])).

fof(f1070,plain,(
    ! [X10,X8,X11,X9] : k3_tarski(k1_tarski(k2_enumset1(X8,X9,X10,X11))) = k6_enumset1(X8,X9,X10,X11,X8,X9,X10,X11) ),
    inference(superposition,[],[f332,f46])).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0)) ),
    inference(superposition,[],[f28,f26])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f332,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(backward_demodulation,[],[f236,f330])).

fof(f236,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(superposition,[],[f43,f37])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

fof(f2012,plain,(
    ! [X2,X1] : k4_enumset1(X1,X1,X1,X1,X2,X1) = k2_xboole_0(k3_tarski(k1_tarski(k1_tarski(X1))),k1_tarski(X2)) ),
    inference(superposition,[],[f1057,f1959])).

fof(f2802,plain,(
    ! [X4,X2,X5,X3] : k6_enumset1(X2,X2,X2,X2,X3,X2,X4,X5) = k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f42,f2097])).

fof(f12096,plain,(
    ! [X24,X23,X21,X22] : k2_xboole_0(k2_tarski(X22,X21),k2_tarski(X24,X23)) = k6_enumset1(X21,X21,X21,X21,X22,X21,X23,X24) ),
    inference(superposition,[],[f187,f11861])).

fof(f11861,plain,(
    ! [X14,X13] : k2_tarski(X14,X13) = k4_enumset1(X13,X13,X13,X13,X14,X13) ),
    inference(forward_demodulation,[],[f11829,f56])).

fof(f11829,plain,(
    ! [X14,X13] : k4_enumset1(X13,X13,X13,X13,X14,X13) = k1_enumset1(X13,X14,X14) ),
    inference(superposition,[],[f5451,f1059])).

fof(f5451,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X2,X1) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(backward_demodulation,[],[f3387,f5448])).

fof(f5448,plain,(
    ! [X30,X31,X32] : k1_enumset1(X30,X31,X32) = k2_xboole_0(k1_tarski(X30),k2_tarski(X31,X32)) ),
    inference(forward_demodulation,[],[f5404,f34])).

fof(f5404,plain,(
    ! [X30,X31,X32] : k2_enumset1(X30,X30,X31,X32) = k2_xboole_0(k1_tarski(X30),k2_tarski(X31,X32)) ),
    inference(superposition,[],[f5039,f37])).

fof(f5039,plain,(
    ! [X10,X8,X9] : k3_enumset1(X8,X8,X8,X9,X10) = k2_xboole_0(k1_tarski(X8),k2_tarski(X9,X10)) ),
    inference(superposition,[],[f2112,f39])).

fof(f2112,plain,(
    ! [X6,X4,X5] : k4_enumset1(X4,X4,X4,X4,X5,X6) = k2_xboole_0(k1_tarski(X4),k2_tarski(X5,X6)) ),
    inference(forward_demodulation,[],[f2082,f2094])).

fof(f2082,plain,(
    ! [X6,X4,X5] : k4_enumset1(X4,X4,X4,X4,X5,X6) = k2_xboole_0(k3_tarski(k1_tarski(k1_tarski(X4))),k2_tarski(X5,X6)) ),
    inference(superposition,[],[f687,f2007])).

fof(f3387,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X2,X1)) ),
    inference(superposition,[],[f674,f2095])).

fof(f2095,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(backward_demodulation,[],[f1959,f2094])).

fof(f674,plain,(
    ! [X6,X12,X10,X8,X7,X11,X9] : k5_enumset1(X8,X9,X10,X11,X12,X6,X7) = k2_xboole_0(k3_enumset1(X8,X9,X10,X11,X12),k2_tarski(X7,X6)) ),
    inference(superposition,[],[f196,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f187,plain,(
    ! [X14,X12,X10,X8,X7,X13,X11,X9] : k6_enumset1(X9,X10,X11,X12,X13,X14,X7,X8) = k2_xboole_0(k4_enumset1(X9,X10,X11,X12,X13,X14),k2_tarski(X8,X7)) ),
    inference(superposition,[],[f42,f27])).

fof(f5459,plain,(
    ! [X47,X45,X48,X46] : k2_xboole_0(k1_enumset1(X45,X46,X47),k1_tarski(X48)) = k2_xboole_0(k1_tarski(X45),k1_enumset1(X46,X48,X47)) ),
    inference(backward_demodulation,[],[f5064,f5448])).

fof(f5064,plain,(
    ! [X47,X45,X48,X46] : k2_xboole_0(k2_xboole_0(k1_tarski(X45),k2_tarski(X46,X47)),k1_tarski(X48)) = k2_xboole_0(k1_tarski(X45),k1_enumset1(X46,X48,X47)) ),
    inference(forward_demodulation,[],[f5052,f3505])).

fof(f3505,plain,(
    ! [X61,X62,X60,X63] : k5_enumset1(X60,X60,X60,X60,X61,X62,X63) = k2_xboole_0(k1_tarski(X60),k1_enumset1(X61,X62,X63)) ),
    inference(superposition,[],[f950,f2096])).

fof(f2096,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(backward_demodulation,[],[f2007,f2094])).

fof(f950,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(forward_demodulation,[],[f939,f41])).

fof(f939,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(superposition,[],[f331,f37])).

fof(f5052,plain,(
    ! [X47,X45,X48,X46] : k5_enumset1(X45,X45,X45,X45,X46,X48,X47) = k2_xboole_0(k2_xboole_0(k1_tarski(X45),k2_tarski(X46,X47)),k1_tarski(X48)) ),
    inference(superposition,[],[f955,f2112])).

fof(f21001,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X1,X2,X3,X0,X0) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)) ),
    inference(superposition,[],[f1746,f26])).

fof(f37918,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK0,sK2,sK3)) ),
    inference(superposition,[],[f25,f32829])).

fof(f32829,plain,(
    ! [X118,X116,X119,X117] : k2_enumset1(X116,X117,X118,X119) = k2_enumset1(X116,X118,X119,X117) ),
    inference(superposition,[],[f21128,f16284])).

fof(f16284,plain,(
    ! [X30,X31,X29,X32] : k3_enumset1(X29,X30,X31,X32,X32) = k2_enumset1(X29,X31,X32,X30) ),
    inference(forward_demodulation,[],[f16246,f1333])).

fof(f16246,plain,(
    ! [X30,X31,X29,X32] : k3_enumset1(X29,X30,X31,X32,X32) = k3_enumset1(X29,X30,X31,X32,X31) ),
    inference(superposition,[],[f1063,f1873])).

fof(f1873,plain,(
    ! [X6,X4,X7,X5,X3] : k4_enumset1(X3,X4,X5,X5,X7,X6) = k3_enumset1(X3,X4,X5,X7,X6) ),
    inference(forward_demodulation,[],[f1865,f1749])).

fof(f1749,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0)) = k3_enumset1(X1,X2,X3,X0,X4) ),
    inference(forward_demodulation,[],[f1730,f1063])).

fof(f1730,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X1,X2,X3,X4,X0,X0) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0)) ),
    inference(superposition,[],[f687,f26])).

fof(f1865,plain,(
    ! [X6,X4,X7,X5,X3] : k4_enumset1(X3,X4,X5,X5,X7,X6) = k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(superposition,[],[f1057,f1334])).

fof(f25,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))
   => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (8747)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  % (8743)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (8744)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (8738)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (8754)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.47  % (8750)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (8740)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (8749)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (8755)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  % (8739)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (8752)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (8741)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (8742)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (8746)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (8748)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (8751)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (8745)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.50  % (8753)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (8749)Refutation not found, incomplete strategy% (8749)------------------------------
% 0.20/0.50  % (8749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (8749)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (8749)Memory used [KB]: 10618
% 0.20/0.50  % (8749)Time elapsed: 0.073 s
% 0.20/0.50  % (8749)------------------------------
% 0.20/0.50  % (8749)------------------------------
% 5.37/1.04  % (8742)Time limit reached!
% 5.37/1.04  % (8742)------------------------------
% 5.37/1.04  % (8742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.37/1.04  % (8742)Termination reason: Time limit
% 5.37/1.04  % (8742)Termination phase: Saturation
% 5.37/1.04  
% 5.37/1.04  % (8742)Memory used [KB]: 10874
% 5.37/1.04  % (8742)Time elapsed: 0.600 s
% 5.37/1.04  % (8742)------------------------------
% 5.37/1.04  % (8742)------------------------------
% 11.85/1.92  % (8743)Time limit reached!
% 11.85/1.92  % (8743)------------------------------
% 11.85/1.92  % (8743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.85/1.92  % (8743)Termination reason: Time limit
% 11.85/1.92  % (8743)Termination phase: Saturation
% 11.85/1.92  
% 11.85/1.92  % (8743)Memory used [KB]: 35052
% 11.85/1.92  % (8743)Time elapsed: 1.500 s
% 11.85/1.92  % (8743)------------------------------
% 11.85/1.92  % (8743)------------------------------
% 12.50/1.95  % (8744)Time limit reached!
% 12.50/1.95  % (8744)------------------------------
% 12.50/1.95  % (8744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.50/1.95  % (8744)Termination reason: Time limit
% 12.50/1.95  % (8744)Termination phase: Saturation
% 12.50/1.95  
% 12.50/1.95  % (8744)Memory used [KB]: 18677
% 12.50/1.95  % (8744)Time elapsed: 1.500 s
% 12.50/1.95  % (8744)------------------------------
% 12.50/1.95  % (8744)------------------------------
% 14.98/2.24  % (8740)Time limit reached!
% 14.98/2.24  % (8740)------------------------------
% 14.98/2.24  % (8740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.98/2.24  % (8740)Termination reason: Time limit
% 14.98/2.24  
% 14.98/2.24  % (8740)Memory used [KB]: 17910
% 14.98/2.24  % (8740)Time elapsed: 1.822 s
% 14.98/2.24  % (8740)------------------------------
% 14.98/2.24  % (8740)------------------------------
% 17.79/2.64  % (8750)Time limit reached!
% 17.79/2.64  % (8750)------------------------------
% 17.79/2.64  % (8750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.79/2.64  % (8750)Termination reason: Time limit
% 17.79/2.64  % (8750)Termination phase: Saturation
% 17.79/2.64  
% 17.79/2.64  % (8750)Memory used [KB]: 15351
% 17.79/2.64  % (8750)Time elapsed: 2.200 s
% 17.79/2.64  % (8750)------------------------------
% 17.79/2.64  % (8750)------------------------------
% 30.34/4.16  % (8741)Refutation found. Thanks to Tanya!
% 30.34/4.16  % SZS status Theorem for theBenchmark
% 30.34/4.16  % SZS output start Proof for theBenchmark
% 30.34/4.16  fof(f38448,plain,(
% 30.34/4.16    $false),
% 30.34/4.16    inference(subsumption_resolution,[],[f38447,f32])).
% 30.34/4.16  fof(f32,plain,(
% 30.34/4.16    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 30.34/4.16    inference(cnf_transformation,[],[f19])).
% 30.34/4.16  fof(f19,axiom,(
% 30.34/4.16    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 30.34/4.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 30.34/4.16  fof(f38447,plain,(
% 30.34/4.16    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4))),
% 30.34/4.16    inference(forward_demodulation,[],[f38446,f35])).
% 30.34/4.16  fof(f35,plain,(
% 30.34/4.16    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 30.34/4.16    inference(cnf_transformation,[],[f17])).
% 30.34/4.16  fof(f17,axiom,(
% 30.34/4.16    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 30.34/4.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 30.34/4.16  fof(f38446,plain,(
% 30.34/4.16    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4))),
% 30.34/4.16    inference(superposition,[],[f38256,f1233])).
% 30.34/4.16  fof(f1233,plain,(
% 30.34/4.16    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5))) )),
% 30.34/4.16    inference(forward_demodulation,[],[f1220,f33])).
% 30.34/4.16  fof(f33,plain,(
% 30.34/4.16    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 30.34/4.16    inference(cnf_transformation,[],[f18])).
% 30.34/4.16  fof(f18,axiom,(
% 30.34/4.16    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 30.34/4.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 30.34/4.16  fof(f1220,plain,(
% 30.34/4.16    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5))) )),
% 30.34/4.16    inference(superposition,[],[f155,f33])).
% 30.34/4.16  fof(f155,plain,(
% 30.34/4.16    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 30.34/4.16    inference(forward_demodulation,[],[f149,f33])).
% 30.34/4.16  fof(f149,plain,(
% 30.34/4.16    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 30.34/4.16    inference(superposition,[],[f38,f33])).
% 30.34/4.16  fof(f38,plain,(
% 30.34/4.16    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 30.34/4.16    inference(cnf_transformation,[],[f16])).
% 30.34/4.16  fof(f16,axiom,(
% 30.34/4.16    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 30.34/4.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 30.34/4.16  fof(f38256,plain,(
% 30.34/4.16    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4))),
% 30.34/4.16    inference(superposition,[],[f37918,f32830])).
% 30.34/4.16  fof(f32830,plain,(
% 30.34/4.16    ( ! [X123,X121,X122,X120] : (k2_enumset1(X120,X121,X123,X122) = k2_enumset1(X120,X121,X122,X123)) )),
% 30.34/4.16    inference(superposition,[],[f21128,f1084])).
% 30.34/4.16  fof(f1084,plain,(
% 30.34/4.16    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 30.34/4.16    inference(forward_demodulation,[],[f1078,f37])).
% 30.34/4.16  fof(f37,plain,(
% 30.34/4.16    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 30.34/4.16    inference(cnf_transformation,[],[f11])).
% 30.34/4.16  fof(f11,axiom,(
% 30.34/4.16    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 30.34/4.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 30.34/4.16  fof(f1078,plain,(
% 30.34/4.16    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X3) = k3_enumset1(X0,X0,X1,X3,X2)) )),
% 30.34/4.16    inference(superposition,[],[f1063,f39])).
% 30.34/4.16  fof(f39,plain,(
% 30.34/4.16    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 30.34/4.16    inference(cnf_transformation,[],[f12])).
% 30.34/4.16  fof(f12,axiom,(
% 30.34/4.16    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 30.34/4.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 30.34/4.16  fof(f1063,plain,(
% 30.34/4.16    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X4) = k3_enumset1(X0,X1,X2,X4,X3)) )),
% 30.34/4.16    inference(forward_demodulation,[],[f1060,f39])).
% 30.34/4.16  fof(f1060,plain,(
% 30.34/4.16    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X4) = k4_enumset1(X0,X0,X1,X2,X4,X3)) )),
% 30.34/4.16    inference(superposition,[],[f1059,f40])).
% 30.34/4.16  fof(f40,plain,(
% 30.34/4.16    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 30.34/4.16    inference(cnf_transformation,[],[f13])).
% 30.34/4.16  fof(f13,axiom,(
% 30.34/4.16    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 30.34/4.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 30.34/4.16  fof(f1059,plain,(
% 30.34/4.16    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X0,X5)) )),
% 30.34/4.16    inference(backward_demodulation,[],[f673,f1057])).
% 30.34/4.16  fof(f1057,plain,(
% 30.34/4.16    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X5,X4)) )),
% 30.34/4.16    inference(forward_demodulation,[],[f1052,f40])).
% 30.34/4.16  fof(f1052,plain,(
% 30.34/4.16    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k5_enumset1(X0,X0,X1,X2,X3,X5,X4)) )),
% 30.34/4.16    inference(superposition,[],[f955,f39])).
% 30.34/4.16  fof(f955,plain,(
% 30.34/4.16    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0)) = k5_enumset1(X1,X2,X3,X4,X5,X0,X6)) )),
% 30.34/4.16    inference(backward_demodulation,[],[f186,f953])).
% 30.34/4.16  fof(f953,plain,(
% 30.34/4.16    ( ! [X30,X35,X33,X31,X36,X34,X32] : (k6_enumset1(X32,X33,X34,X35,X36,X30,X31,X31) = k5_enumset1(X32,X33,X34,X35,X36,X31,X30)) )),
% 30.34/4.16    inference(forward_demodulation,[],[f944,f196])).
% 30.34/4.16  fof(f196,plain,(
% 30.34/4.16    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 30.34/4.16    inference(forward_demodulation,[],[f185,f41])).
% 30.34/4.16  fof(f41,plain,(
% 30.34/4.16    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 30.34/4.16    inference(cnf_transformation,[],[f14])).
% 30.34/4.16  fof(f14,axiom,(
% 30.34/4.16    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 30.34/4.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 30.34/4.16  fof(f185,plain,(
% 30.34/4.16    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 30.34/4.16    inference(superposition,[],[f42,f39])).
% 30.34/4.16  fof(f42,plain,(
% 30.34/4.16    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 30.34/4.16    inference(cnf_transformation,[],[f7])).
% 30.34/4.16  fof(f7,axiom,(
% 30.34/4.16    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 30.34/4.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).
% 30.34/4.16  fof(f944,plain,(
% 30.34/4.16    ( ! [X30,X35,X33,X31,X36,X34,X32] : (k6_enumset1(X32,X33,X34,X35,X36,X30,X31,X31) = k2_xboole_0(k3_enumset1(X32,X33,X34,X35,X36),k2_tarski(X31,X30))) )),
% 30.34/4.16    inference(superposition,[],[f331,f56])).
% 30.34/4.16  fof(f56,plain,(
% 30.34/4.16    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)) )),
% 30.34/4.16    inference(superposition,[],[f31,f29])).
% 30.34/4.16  fof(f29,plain,(
% 30.34/4.16    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 30.34/4.16    inference(cnf_transformation,[],[f9])).
% 30.34/4.16  fof(f9,axiom,(
% 30.34/4.16    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 30.34/4.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 30.34/4.16  fof(f31,plain,(
% 30.34/4.16    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 30.34/4.16    inference(cnf_transformation,[],[f3])).
% 30.34/4.16  fof(f3,axiom,(
% 30.34/4.16    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 30.34/4.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).
% 30.34/4.16  fof(f331,plain,(
% 30.34/4.16    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 30.34/4.16    inference(backward_demodulation,[],[f265,f330])).
% 30.34/4.16  fof(f330,plain,(
% 30.34/4.16    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 30.34/4.16    inference(forward_demodulation,[],[f318,f42])).
% 30.34/4.16  fof(f318,plain,(
% 30.34/4.16    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 30.34/4.16    inference(superposition,[],[f45,f40])).
% 30.34/4.16  fof(f45,plain,(
% 30.34/4.16    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) )),
% 30.34/4.16    inference(cnf_transformation,[],[f6])).
% 30.34/4.16  fof(f6,axiom,(
% 30.34/4.16    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 30.34/4.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).
% 30.34/4.16  fof(f265,plain,(
% 30.34/4.16    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 30.34/4.16    inference(superposition,[],[f44,f39])).
% 30.34/4.16  fof(f44,plain,(
% 30.34/4.16    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))) )),
% 30.34/4.16    inference(cnf_transformation,[],[f5])).
% 30.34/4.16  fof(f5,axiom,(
% 30.34/4.16    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 30.34/4.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).
% 30.34/4.16  fof(f186,plain,(
% 30.34/4.16    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X1,X2,X3,X4,X5,X6,X0,X0) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0))) )),
% 30.34/4.16    inference(superposition,[],[f42,f26])).
% 30.34/4.16  fof(f26,plain,(
% 30.34/4.16    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 30.34/4.16    inference(cnf_transformation,[],[f8])).
% 30.34/4.16  fof(f8,axiom,(
% 30.34/4.16    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 30.34/4.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 30.34/4.16  fof(f673,plain,(
% 30.34/4.16    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) )),
% 30.34/4.16    inference(superposition,[],[f196,f26])).
% 30.34/4.16  fof(f21128,plain,(
% 30.34/4.16    ( ! [X2,X0,X3,X1] : (k3_enumset1(X1,X2,X3,X0,X0) = k2_enumset1(X1,X2,X3,X0)) )),
% 30.34/4.16    inference(forward_demodulation,[],[f21001,f21033])).
% 30.34/4.16  fof(f21033,plain,(
% 30.34/4.16    ( ! [X47,X45,X48,X46] : (k2_enumset1(X45,X46,X47,X48) = k2_xboole_0(k1_enumset1(X45,X46,X47),k1_tarski(X48))) )),
% 30.34/4.16    inference(backward_demodulation,[],[f5459,f21026])).
% 30.34/4.16  fof(f21026,plain,(
% 30.34/4.16    ( ! [X24,X23,X21,X22] : (k2_xboole_0(k1_tarski(X21),k1_enumset1(X22,X23,X24)) = k2_enumset1(X21,X22,X24,X23)) )),
% 30.34/4.16    inference(backward_demodulation,[],[f12127,f21025])).
% 30.34/4.16  fof(f21025,plain,(
% 30.34/4.16    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X3))) )),
% 30.34/4.16    inference(forward_demodulation,[],[f20981,f37])).
% 30.34/4.16  fof(f20981,plain,(
% 30.34/4.16    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X3))) )),
% 30.34/4.16    inference(superposition,[],[f1746,f1163])).
% 30.34/4.16  fof(f1163,plain,(
% 30.34/4.16    ( ! [X2,X1] : (k2_tarski(X2,X1) = k1_enumset1(X1,X1,X2)) )),
% 30.34/4.16    inference(superposition,[],[f1134,f31])).
% 30.34/4.16  fof(f1134,plain,(
% 30.34/4.16    ( ! [X0,X1] : (k2_tarski(X1,X0) = k1_enumset1(X0,X1,X0)) )),
% 30.34/4.16    inference(forward_demodulation,[],[f1127,f56])).
% 30.34/4.16  fof(f1127,plain,(
% 30.34/4.16    ( ! [X0,X1] : (k1_enumset1(X0,X1,X0) = k1_enumset1(X0,X1,X1)) )),
% 30.34/4.16    inference(superposition,[],[f1103,f34])).
% 30.34/4.16  fof(f34,plain,(
% 30.34/4.16    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 30.34/4.16    inference(cnf_transformation,[],[f10])).
% 30.34/4.16  fof(f10,axiom,(
% 30.34/4.16    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 30.34/4.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 30.34/4.16  fof(f1103,plain,(
% 30.34/4.16    ( ! [X2,X0,X1] : (k2_enumset1(X0,X1,X2,X2) = k1_enumset1(X0,X2,X1)) )),
% 30.34/4.16    inference(forward_demodulation,[],[f1098,f34])).
% 30.34/4.16  fof(f1098,plain,(
% 30.34/4.16    ( ! [X2,X0,X1] : (k2_enumset1(X0,X1,X2,X2) = k2_enumset1(X0,X0,X2,X1)) )),
% 30.34/4.16    inference(superposition,[],[f1084,f37])).
% 30.34/4.16  fof(f1746,plain,(
% 30.34/4.16    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 30.34/4.16    inference(forward_demodulation,[],[f1719,f39])).
% 30.34/4.16  fof(f1719,plain,(
% 30.34/4.16    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 30.34/4.16    inference(superposition,[],[f687,f34])).
% 30.34/4.16  fof(f687,plain,(
% 30.34/4.16    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 30.34/4.16    inference(forward_demodulation,[],[f672,f40])).
% 30.34/4.16  fof(f672,plain,(
% 30.34/4.16    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 30.34/4.16    inference(superposition,[],[f196,f37])).
% 30.34/4.16  fof(f12127,plain,(
% 30.34/4.16    ( ! [X24,X23,X21,X22] : (k2_xboole_0(k2_tarski(X22,X21),k2_tarski(X24,X23)) = k2_xboole_0(k1_tarski(X21),k1_enumset1(X22,X23,X24))) )),
% 30.34/4.16    inference(forward_demodulation,[],[f12096,f5478])).
% 30.34/4.16  fof(f5478,plain,(
% 30.34/4.16    ( ! [X4,X2,X5,X3] : (k6_enumset1(X2,X2,X2,X2,X3,X2,X4,X5) = k2_xboole_0(k1_tarski(X2),k1_enumset1(X3,X4,X5))) )),
% 30.34/4.16    inference(backward_demodulation,[],[f3006,f5468])).
% 30.34/4.16  fof(f5468,plain,(
% 30.34/4.16    ( ! [X17,X15,X18,X16] : (k2_xboole_0(k2_tarski(X15,X16),k2_tarski(X18,X17)) = k2_xboole_0(k1_tarski(X15),k1_enumset1(X16,X18,X17))) )),
% 30.34/4.16    inference(backward_demodulation,[],[f4342,f5459])).
% 30.34/4.16  fof(f4342,plain,(
% 30.34/4.16    ( ! [X17,X15,X18,X16] : (k2_xboole_0(k1_enumset1(X15,X16,X17),k1_tarski(X18)) = k2_xboole_0(k2_tarski(X15,X16),k2_tarski(X18,X17))) )),
% 30.34/4.16    inference(forward_demodulation,[],[f4315,f1723])).
% 30.34/4.16  fof(f1723,plain,(
% 30.34/4.16    ( ! [X23,X21,X22,X20] : (k4_enumset1(X20,X21,X20,X21,X22,X23) = k2_xboole_0(k2_tarski(X20,X21),k2_tarski(X22,X23))) )),
% 30.34/4.16    inference(superposition,[],[f687,f1572])).
% 30.34/4.16  fof(f1572,plain,(
% 30.34/4.16    ( ! [X2,X3] : (k2_tarski(X2,X3) = k2_enumset1(X2,X3,X2,X3)) )),
% 30.34/4.16    inference(forward_demodulation,[],[f1556,f29])).
% 30.34/4.16  fof(f1556,plain,(
% 30.34/4.16    ( ! [X2,X3] : (k1_enumset1(X2,X2,X3) = k2_enumset1(X2,X3,X2,X3)) )),
% 30.34/4.16    inference(superposition,[],[f1415,f1103])).
% 30.34/4.16  fof(f1415,plain,(
% 30.34/4.16    ( ! [X2,X0,X1] : (k2_enumset1(X0,X1,X2,X1) = k2_enumset1(X0,X1,X2,X0)) )),
% 30.34/4.16    inference(superposition,[],[f1333,f37])).
% 30.34/4.16  fof(f1333,plain,(
% 30.34/4.16    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X2) = k2_enumset1(X0,X2,X3,X1)) )),
% 30.34/4.16    inference(forward_demodulation,[],[f1322,f37])).
% 30.34/4.16  fof(f1322,plain,(
% 30.34/4.16    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X2) = k3_enumset1(X0,X0,X2,X3,X1)) )),
% 30.34/4.16    inference(superposition,[],[f1285,f39])).
% 30.34/4.16  fof(f1285,plain,(
% 30.34/4.16    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X3) = k3_enumset1(X0,X1,X3,X4,X2)) )),
% 30.34/4.16    inference(forward_demodulation,[],[f1278,f39])).
% 30.34/4.16  fof(f1278,plain,(
% 30.34/4.16    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X3) = k4_enumset1(X0,X0,X1,X3,X4,X2)) )),
% 30.34/4.16    inference(superposition,[],[f1086,f40])).
% 30.34/4.16  fof(f1086,plain,(
% 30.34/4.16    ( ! [X6,X4,X8,X7,X5,X9] : (k5_enumset1(X4,X5,X6,X7,X8,X9,X8) = k4_enumset1(X4,X5,X6,X8,X9,X7)) )),
% 30.34/4.16    inference(forward_demodulation,[],[f1080,f1057])).
% 30.34/4.16  fof(f1080,plain,(
% 30.34/4.16    ( ! [X6,X4,X8,X7,X5,X9] : (k5_enumset1(X4,X5,X6,X7,X8,X9,X8) = k2_xboole_0(k3_enumset1(X4,X5,X6,X8,X7),k1_tarski(X9))) )),
% 30.34/4.16    inference(superposition,[],[f955,f1063])).
% 30.34/4.16  fof(f4315,plain,(
% 30.34/4.16    ( ! [X17,X15,X18,X16] : (k4_enumset1(X15,X16,X15,X16,X18,X17) = k2_xboole_0(k1_enumset1(X15,X16,X17),k1_tarski(X18))) )),
% 30.34/4.16    inference(superposition,[],[f1057,f4096])).
% 30.34/4.16  fof(f4096,plain,(
% 30.34/4.16    ( ! [X17,X18,X16] : (k1_enumset1(X16,X17,X18) = k3_enumset1(X16,X17,X16,X17,X18)) )),
% 30.34/4.16    inference(forward_demodulation,[],[f4064,f1422])).
% 30.34/4.16  fof(f1422,plain,(
% 30.34/4.16    ( ! [X4,X5,X3] : (k2_enumset1(X3,X5,X5,X4) = k1_enumset1(X3,X5,X4)) )),
% 30.34/4.16    inference(forward_demodulation,[],[f1416,f1103])).
% 30.34/4.16  fof(f1416,plain,(
% 30.34/4.16    ( ! [X4,X5,X3] : (k2_enumset1(X3,X4,X5,X5) = k2_enumset1(X3,X5,X5,X4)) )),
% 30.34/4.16    inference(superposition,[],[f1333,f1084])).
% 30.34/4.16  fof(f4064,plain,(
% 30.34/4.16    ( ! [X17,X18,X16] : (k2_enumset1(X16,X17,X17,X18) = k3_enumset1(X16,X17,X16,X17,X18)) )),
% 30.34/4.16    inference(superposition,[],[f3536,f1334])).
% 30.34/4.16  fof(f1334,plain,(
% 30.34/4.16    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X5,X7,X7,X6) = k2_enumset1(X4,X5,X7,X6)) )),
% 30.34/4.16    inference(forward_demodulation,[],[f1323,f1084])).
% 30.34/4.16  fof(f1323,plain,(
% 30.34/4.16    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X5,X6,X7,X7) = k3_enumset1(X4,X5,X7,X7,X6)) )),
% 30.34/4.16    inference(superposition,[],[f1285,f1063])).
% 30.34/4.16  fof(f3536,plain,(
% 30.34/4.16    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X1,X1,X2,X3) = k3_enumset1(X0,X1,X0,X2,X3)) )),
% 30.34/4.16    inference(superposition,[],[f1747,f39])).
% 30.34/4.16  fof(f1747,plain,(
% 30.34/4.16    ( ! [X6,X8,X7,X5,X9] : (k4_enumset1(X5,X6,X7,X7,X8,X9) = k3_enumset1(X5,X7,X6,X8,X9)) )),
% 30.34/4.16    inference(forward_demodulation,[],[f1720,f1746])).
% 30.34/4.16  fof(f1720,plain,(
% 30.34/4.16    ( ! [X6,X8,X7,X5,X9] : (k4_enumset1(X5,X6,X7,X7,X8,X9) = k2_xboole_0(k1_enumset1(X5,X7,X6),k2_tarski(X8,X9))) )),
% 30.34/4.16    inference(superposition,[],[f687,f1103])).
% 30.34/4.16  fof(f3006,plain,(
% 30.34/4.16    ( ! [X4,X2,X5,X3] : (k6_enumset1(X2,X2,X2,X2,X3,X2,X4,X5) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X4,X5))) )),
% 30.34/4.16    inference(backward_demodulation,[],[f2802,f3003])).
% 30.34/4.16  fof(f3003,plain,(
% 30.34/4.16    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 30.34/4.16    inference(forward_demodulation,[],[f2977,f54])).
% 30.34/4.16  fof(f54,plain,(
% 30.34/4.16    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 30.34/4.16    inference(superposition,[],[f31,f29])).
% 30.34/4.16  fof(f2977,plain,(
% 30.34/4.16    ( ! [X0,X1] : (k1_enumset1(X0,X1,X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 30.34/4.16    inference(superposition,[],[f2918,f34])).
% 30.34/4.16  fof(f2918,plain,(
% 30.34/4.16    ( ! [X4,X5] : (k2_enumset1(X4,X4,X5,X4) = k2_xboole_0(k1_tarski(X4),k1_tarski(X5))) )),
% 30.34/4.16    inference(superposition,[],[f2797,f1333])).
% 30.34/4.16  fof(f2797,plain,(
% 30.34/4.16    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k3_enumset1(X0,X0,X0,X1,X0)) )),
% 30.34/4.16    inference(superposition,[],[f2097,f39])).
% 30.34/4.16  fof(f2097,plain,(
% 30.34/4.16    ( ! [X2,X1] : (k4_enumset1(X1,X1,X1,X1,X2,X1) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) )),
% 30.34/4.16    inference(backward_demodulation,[],[f2012,f2094])).
% 30.34/4.16  fof(f2094,plain,(
% 30.34/4.16    ( ! [X4] : (k1_tarski(X4) = k3_tarski(k1_tarski(k1_tarski(X4)))) )),
% 30.34/4.16    inference(forward_demodulation,[],[f2073,f26])).
% 30.34/4.16  fof(f2073,plain,(
% 30.34/4.16    ( ! [X4] : (k2_tarski(X4,X4) = k3_tarski(k1_tarski(k1_tarski(X4)))) )),
% 30.34/4.16    inference(superposition,[],[f2007,f1572])).
% 30.34/4.16  fof(f2007,plain,(
% 30.34/4.16    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0)))) )),
% 30.34/4.16    inference(superposition,[],[f1959,f37])).
% 30.34/4.16  fof(f1959,plain,(
% 30.34/4.16    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0)))) )),
% 30.34/4.16    inference(forward_demodulation,[],[f1945,f26])).
% 30.34/4.16  fof(f1945,plain,(
% 30.34/4.16    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k3_tarski(k1_tarski(k2_tarski(X0,X0)))) )),
% 30.34/4.16    inference(superposition,[],[f1858,f39])).
% 30.34/4.16  fof(f1858,plain,(
% 30.34/4.16    ( ! [X4,X3] : (k4_enumset1(X3,X4,X4,X3,X4,X3) = k3_tarski(k1_tarski(k2_tarski(X4,X3)))) )),
% 30.34/4.16    inference(forward_demodulation,[],[f1857,f56])).
% 30.34/4.16  fof(f1857,plain,(
% 30.34/4.16    ( ! [X4,X3] : (k4_enumset1(X3,X4,X4,X3,X4,X3) = k3_tarski(k1_tarski(k1_enumset1(X3,X4,X4)))) )),
% 30.34/4.16    inference(forward_demodulation,[],[f1849,f34])).
% 30.34/4.16  fof(f1849,plain,(
% 30.34/4.16    ( ! [X4,X3] : (k4_enumset1(X3,X4,X4,X3,X4,X3) = k3_tarski(k1_tarski(k2_enumset1(X3,X3,X4,X4)))) )),
% 30.34/4.16    inference(superposition,[],[f1070,f1058])).
% 30.34/4.16  fof(f1058,plain,(
% 30.34/4.16    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X5) = k4_enumset1(X0,X1,X2,X3,X5,X4)) )),
% 30.34/4.16    inference(backward_demodulation,[],[f725,f1057])).
% 30.34/4.16  fof(f725,plain,(
% 30.34/4.16    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X5)) )),
% 30.34/4.16    inference(superposition,[],[f186,f39])).
% 30.34/4.16  fof(f1070,plain,(
% 30.34/4.16    ( ! [X10,X8,X11,X9] : (k3_tarski(k1_tarski(k2_enumset1(X8,X9,X10,X11))) = k6_enumset1(X8,X9,X10,X11,X8,X9,X10,X11)) )),
% 30.34/4.16    inference(superposition,[],[f332,f46])).
% 30.34/4.16  fof(f46,plain,(
% 30.34/4.16    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))) )),
% 30.34/4.16    inference(superposition,[],[f28,f26])).
% 30.34/4.16  fof(f28,plain,(
% 30.34/4.16    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 30.34/4.16    inference(cnf_transformation,[],[f15])).
% 30.34/4.16  fof(f15,axiom,(
% 30.34/4.16    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 30.34/4.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 30.34/4.16  fof(f332,plain,(
% 30.34/4.16    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 30.34/4.16    inference(backward_demodulation,[],[f236,f330])).
% 30.34/4.16  fof(f236,plain,(
% 30.34/4.16    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 30.34/4.16    inference(superposition,[],[f43,f37])).
% 30.34/4.16  fof(f43,plain,(
% 30.34/4.16    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 30.34/4.16    inference(cnf_transformation,[],[f4])).
% 30.34/4.16  fof(f4,axiom,(
% 30.34/4.16    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 30.34/4.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).
% 30.34/4.16  fof(f2012,plain,(
% 30.34/4.16    ( ! [X2,X1] : (k4_enumset1(X1,X1,X1,X1,X2,X1) = k2_xboole_0(k3_tarski(k1_tarski(k1_tarski(X1))),k1_tarski(X2))) )),
% 30.34/4.16    inference(superposition,[],[f1057,f1959])).
% 30.34/4.16  fof(f2802,plain,(
% 30.34/4.16    ( ! [X4,X2,X5,X3] : (k6_enumset1(X2,X2,X2,X2,X3,X2,X4,X5) = k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k2_tarski(X4,X5))) )),
% 30.34/4.16    inference(superposition,[],[f42,f2097])).
% 30.34/4.16  fof(f12096,plain,(
% 30.34/4.16    ( ! [X24,X23,X21,X22] : (k2_xboole_0(k2_tarski(X22,X21),k2_tarski(X24,X23)) = k6_enumset1(X21,X21,X21,X21,X22,X21,X23,X24)) )),
% 30.34/4.16    inference(superposition,[],[f187,f11861])).
% 30.34/4.16  fof(f11861,plain,(
% 30.34/4.16    ( ! [X14,X13] : (k2_tarski(X14,X13) = k4_enumset1(X13,X13,X13,X13,X14,X13)) )),
% 30.34/4.16    inference(forward_demodulation,[],[f11829,f56])).
% 30.34/4.16  fof(f11829,plain,(
% 30.34/4.16    ( ! [X14,X13] : (k4_enumset1(X13,X13,X13,X13,X14,X13) = k1_enumset1(X13,X14,X14)) )),
% 30.34/4.16    inference(superposition,[],[f5451,f1059])).
% 30.34/4.16  fof(f5451,plain,(
% 30.34/4.16    ( ! [X2,X0,X1] : (k1_enumset1(X0,X2,X1) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 30.34/4.16    inference(backward_demodulation,[],[f3387,f5448])).
% 30.34/4.16  fof(f5448,plain,(
% 30.34/4.16    ( ! [X30,X31,X32] : (k1_enumset1(X30,X31,X32) = k2_xboole_0(k1_tarski(X30),k2_tarski(X31,X32))) )),
% 30.34/4.16    inference(forward_demodulation,[],[f5404,f34])).
% 30.34/4.16  fof(f5404,plain,(
% 30.34/4.16    ( ! [X30,X31,X32] : (k2_enumset1(X30,X30,X31,X32) = k2_xboole_0(k1_tarski(X30),k2_tarski(X31,X32))) )),
% 30.34/4.16    inference(superposition,[],[f5039,f37])).
% 30.34/4.16  fof(f5039,plain,(
% 30.34/4.16    ( ! [X10,X8,X9] : (k3_enumset1(X8,X8,X8,X9,X10) = k2_xboole_0(k1_tarski(X8),k2_tarski(X9,X10))) )),
% 30.34/4.16    inference(superposition,[],[f2112,f39])).
% 30.34/4.16  fof(f2112,plain,(
% 30.34/4.16    ( ! [X6,X4,X5] : (k4_enumset1(X4,X4,X4,X4,X5,X6) = k2_xboole_0(k1_tarski(X4),k2_tarski(X5,X6))) )),
% 30.34/4.16    inference(forward_demodulation,[],[f2082,f2094])).
% 30.34/4.16  fof(f2082,plain,(
% 30.34/4.16    ( ! [X6,X4,X5] : (k4_enumset1(X4,X4,X4,X4,X5,X6) = k2_xboole_0(k3_tarski(k1_tarski(k1_tarski(X4))),k2_tarski(X5,X6))) )),
% 30.34/4.16    inference(superposition,[],[f687,f2007])).
% 30.34/4.16  fof(f3387,plain,(
% 30.34/4.16    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X2,X1))) )),
% 30.34/4.16    inference(superposition,[],[f674,f2095])).
% 30.34/4.16  fof(f2095,plain,(
% 30.34/4.16    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 30.34/4.16    inference(backward_demodulation,[],[f1959,f2094])).
% 30.34/4.16  fof(f674,plain,(
% 30.34/4.16    ( ! [X6,X12,X10,X8,X7,X11,X9] : (k5_enumset1(X8,X9,X10,X11,X12,X6,X7) = k2_xboole_0(k3_enumset1(X8,X9,X10,X11,X12),k2_tarski(X7,X6))) )),
% 30.34/4.16    inference(superposition,[],[f196,f27])).
% 30.34/4.16  fof(f27,plain,(
% 30.34/4.16    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 30.34/4.16    inference(cnf_transformation,[],[f2])).
% 30.34/4.16  fof(f2,axiom,(
% 30.34/4.16    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 30.34/4.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 30.34/4.16  fof(f187,plain,(
% 30.34/4.16    ( ! [X14,X12,X10,X8,X7,X13,X11,X9] : (k6_enumset1(X9,X10,X11,X12,X13,X14,X7,X8) = k2_xboole_0(k4_enumset1(X9,X10,X11,X12,X13,X14),k2_tarski(X8,X7))) )),
% 30.34/4.16    inference(superposition,[],[f42,f27])).
% 30.34/4.16  fof(f5459,plain,(
% 30.34/4.16    ( ! [X47,X45,X48,X46] : (k2_xboole_0(k1_enumset1(X45,X46,X47),k1_tarski(X48)) = k2_xboole_0(k1_tarski(X45),k1_enumset1(X46,X48,X47))) )),
% 30.34/4.16    inference(backward_demodulation,[],[f5064,f5448])).
% 30.34/4.16  fof(f5064,plain,(
% 30.34/4.16    ( ! [X47,X45,X48,X46] : (k2_xboole_0(k2_xboole_0(k1_tarski(X45),k2_tarski(X46,X47)),k1_tarski(X48)) = k2_xboole_0(k1_tarski(X45),k1_enumset1(X46,X48,X47))) )),
% 30.34/4.16    inference(forward_demodulation,[],[f5052,f3505])).
% 30.34/4.16  fof(f3505,plain,(
% 30.34/4.16    ( ! [X61,X62,X60,X63] : (k5_enumset1(X60,X60,X60,X60,X61,X62,X63) = k2_xboole_0(k1_tarski(X60),k1_enumset1(X61,X62,X63))) )),
% 30.34/4.16    inference(superposition,[],[f950,f2096])).
% 30.34/4.16  fof(f2096,plain,(
% 30.34/4.16    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 30.34/4.16    inference(backward_demodulation,[],[f2007,f2094])).
% 30.34/4.16  fof(f950,plain,(
% 30.34/4.16    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 30.34/4.16    inference(forward_demodulation,[],[f939,f41])).
% 30.34/4.16  fof(f939,plain,(
% 30.34/4.16    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 30.34/4.16    inference(superposition,[],[f331,f37])).
% 30.34/4.16  fof(f5052,plain,(
% 30.34/4.16    ( ! [X47,X45,X48,X46] : (k5_enumset1(X45,X45,X45,X45,X46,X48,X47) = k2_xboole_0(k2_xboole_0(k1_tarski(X45),k2_tarski(X46,X47)),k1_tarski(X48))) )),
% 30.34/4.16    inference(superposition,[],[f955,f2112])).
% 30.34/4.16  fof(f21001,plain,(
% 30.34/4.16    ( ! [X2,X0,X3,X1] : (k3_enumset1(X1,X2,X3,X0,X0) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))) )),
% 30.34/4.16    inference(superposition,[],[f1746,f26])).
% 30.34/4.16  fof(f37918,plain,(
% 30.34/4.16    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK0,sK2,sK3))),
% 30.34/4.16    inference(superposition,[],[f25,f32829])).
% 30.34/4.16  fof(f32829,plain,(
% 30.34/4.16    ( ! [X118,X116,X119,X117] : (k2_enumset1(X116,X117,X118,X119) = k2_enumset1(X116,X118,X119,X117)) )),
% 30.34/4.16    inference(superposition,[],[f21128,f16284])).
% 30.34/4.16  fof(f16284,plain,(
% 30.34/4.16    ( ! [X30,X31,X29,X32] : (k3_enumset1(X29,X30,X31,X32,X32) = k2_enumset1(X29,X31,X32,X30)) )),
% 30.34/4.16    inference(forward_demodulation,[],[f16246,f1333])).
% 30.34/4.16  fof(f16246,plain,(
% 30.34/4.16    ( ! [X30,X31,X29,X32] : (k3_enumset1(X29,X30,X31,X32,X32) = k3_enumset1(X29,X30,X31,X32,X31)) )),
% 30.34/4.16    inference(superposition,[],[f1063,f1873])).
% 30.34/4.16  fof(f1873,plain,(
% 30.34/4.16    ( ! [X6,X4,X7,X5,X3] : (k4_enumset1(X3,X4,X5,X5,X7,X6) = k3_enumset1(X3,X4,X5,X7,X6)) )),
% 30.34/4.16    inference(forward_demodulation,[],[f1865,f1749])).
% 30.34/4.16  fof(f1749,plain,(
% 30.34/4.16    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0)) = k3_enumset1(X1,X2,X3,X0,X4)) )),
% 30.34/4.16    inference(forward_demodulation,[],[f1730,f1063])).
% 30.34/4.16  fof(f1730,plain,(
% 30.34/4.16    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X1,X2,X3,X4,X0,X0) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))) )),
% 30.34/4.16    inference(superposition,[],[f687,f26])).
% 30.34/4.16  fof(f1865,plain,(
% 30.34/4.16    ( ! [X6,X4,X7,X5,X3] : (k4_enumset1(X3,X4,X5,X5,X7,X6) = k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X7))) )),
% 30.34/4.16    inference(superposition,[],[f1057,f1334])).
% 30.34/4.16  fof(f25,plain,(
% 30.34/4.16    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 30.34/4.16    inference(cnf_transformation,[],[f24])).
% 30.34/4.16  fof(f24,plain,(
% 30.34/4.16    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 30.34/4.16    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f23])).
% 30.34/4.16  fof(f23,plain,(
% 30.34/4.16    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 30.34/4.16    introduced(choice_axiom,[])).
% 30.34/4.16  fof(f22,plain,(
% 30.34/4.16    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 30.34/4.16    inference(ennf_transformation,[],[f21])).
% 30.34/4.16  fof(f21,negated_conjecture,(
% 30.34/4.16    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 30.34/4.16    inference(negated_conjecture,[],[f20])).
% 30.34/4.16  fof(f20,conjecture,(
% 30.34/4.16    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 30.34/4.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_mcart_1)).
% 30.34/4.16  % SZS output end Proof for theBenchmark
% 30.34/4.16  % (8741)------------------------------
% 30.34/4.16  % (8741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 30.34/4.16  % (8741)Termination reason: Refutation
% 30.34/4.16  
% 30.34/4.16  % (8741)Memory used [KB]: 61790
% 30.34/4.16  % (8741)Time elapsed: 3.748 s
% 30.34/4.16  % (8741)------------------------------
% 30.34/4.16  % (8741)------------------------------
% 30.34/4.17  % (8735)Success in time 3.804 s
%------------------------------------------------------------------------------
