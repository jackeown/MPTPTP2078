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
% DateTime   : Thu Dec  3 12:58:55 EST 2020

% Result     : Theorem 18.18s
% Output     : Refutation 18.18s
% Verified   : 
% Statistics : Number of formulae       :  115 (4656 expanded)
%              Number of leaves         :   18 (1552 expanded)
%              Depth                    :   35
%              Number of atoms          :  117 (4658 expanded)
%              Number of equality atoms :  116 (4657 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19080,plain,(
    $false ),
    inference(subsumption_resolution,[],[f19079,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f19079,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(sK3,sK4)) ),
    inference(forward_demodulation,[],[f18970,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f18970,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(superposition,[],[f12632,f1037])).

fof(f1037,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5)) ),
    inference(forward_demodulation,[],[f1024,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f1024,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5)) ),
    inference(superposition,[],[f167,f33])).

fof(f167,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f161,f33])).

fof(f161,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(superposition,[],[f38,f33])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f12632,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(superposition,[],[f25,f12224])).

fof(f12224,plain,(
    ! [X47,X45,X46,X44] : k2_enumset1(X45,X44,X46,X47) = k2_enumset1(X45,X46,X44,X47) ),
    inference(superposition,[],[f10592,f10269])).

fof(f10269,plain,(
    ! [X54,X52,X53,X51] : k2_enumset1(X53,X52,X51,X54) = k2_enumset1(X52,X53,X51,X54) ),
    inference(superposition,[],[f3511,f2105])).

fof(f2105,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X1,X2,X0,X0,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(backward_demodulation,[],[f2087,f2104])).

fof(f2104,plain,(
    ! [X21,X19,X20,X18] : k2_xboole_0(k1_enumset1(X20,X18,X19),k1_tarski(X21)) = k2_enumset1(X20,X19,X18,X21) ),
    inference(forward_demodulation,[],[f2093,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f2093,plain,(
    ! [X21,X19,X20,X18] : k3_enumset1(X20,X20,X19,X18,X21) = k2_xboole_0(k1_enumset1(X20,X18,X19),k1_tarski(X21)) ),
    inference(superposition,[],[f2060,f928])).

fof(f928,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X2,X0,X0) ),
    inference(backward_demodulation,[],[f676,f923])).

fof(f923,plain,(
    ! [X4,X5,X3] : k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k1_enumset1(X3,X4,X5) ),
    inference(superposition,[],[f692,f52])).

fof(f52,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f47,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f47,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f692,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(forward_demodulation,[],[f666,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f666,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(superposition,[],[f565,f26])).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f565,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f547,f37])).

fof(f547,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(superposition,[],[f546,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f546,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f531,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f531,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(superposition,[],[f146,f34])).

fof(f146,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(forward_demodulation,[],[f135,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f135,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f41,f37])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

fof(f676,plain,(
    ! [X2,X0,X1] : k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) ),
    inference(superposition,[],[f565,f26])).

fof(f2060,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0)) = k3_enumset1(X3,X4,X2,X1,X0) ),
    inference(backward_demodulation,[],[f533,f2058])).

fof(f2058,plain,(
    ! [X6,X8,X7,X5,X9] : k4_enumset1(X5,X6,X7,X8,X9,X9) = k3_enumset1(X7,X8,X6,X5,X9) ),
    inference(backward_demodulation,[],[f1623,f2057])).

fof(f2057,plain,(
    ! [X6,X10,X8,X7,X9] : k2_xboole_0(k1_tarski(X6),k2_enumset1(X7,X8,X9,X10)) = k3_enumset1(X9,X10,X8,X7,X6) ),
    inference(backward_demodulation,[],[f868,f2056])).

fof(f2056,plain,(
    ! [X6,X4,X2,X5,X3] : k7_enumset1(X2,X2,X2,X2,X3,X3,X4,X5,X6) = k3_enumset1(X5,X6,X4,X3,X2) ),
    inference(forward_demodulation,[],[f2047,f561])).

fof(f561,plain,(
    ! [X6,X8,X7,X5,X9] : k2_xboole_0(k2_tarski(X8,X9),k1_enumset1(X5,X6,X7)) = k3_enumset1(X5,X6,X7,X8,X9) ),
    inference(superposition,[],[f546,f52])).

fof(f2047,plain,(
    ! [X6,X4,X2,X5,X3] : k7_enumset1(X2,X2,X2,X2,X3,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X3,X2),k1_enumset1(X5,X6,X4)) ),
    inference(superposition,[],[f246,f1634])).

fof(f1634,plain,(
    ! [X4,X5] : k2_tarski(X5,X4) = k4_enumset1(X4,X4,X4,X4,X5,X5) ),
    inference(forward_demodulation,[],[f1616,f927])).

fof(f927,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(forward_demodulation,[],[f913,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[],[f31,f29])).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

fof(f913,plain,(
    ! [X0,X1] : k1_enumset1(X1,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(superposition,[],[f692,f26])).

fof(f1616,plain,(
    ! [X4,X5] : k4_enumset1(X4,X4,X4,X4,X5,X5) = k2_xboole_0(k1_tarski(X4),k1_tarski(X5)) ),
    inference(superposition,[],[f533,f751])).

fof(f751,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(backward_demodulation,[],[f708,f749])).

fof(f749,plain,(
    ! [X0] : k1_tarski(X0) = k3_tarski(k1_tarski(k1_tarski(X0))) ),
    inference(forward_demodulation,[],[f738,f26])).

fof(f738,plain,(
    ! [X0] : k2_tarski(X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0))) ),
    inference(superposition,[],[f717,f29])).

fof(f717,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0))) ),
    inference(forward_demodulation,[],[f711,f26])).

fof(f711,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k3_tarski(k1_tarski(k2_tarski(X0,X0))) ),
    inference(superposition,[],[f686,f34])).

fof(f686,plain,(
    ! [X4,X5] : k3_tarski(k1_tarski(k2_tarski(X4,X5))) = k2_enumset1(X4,X5,X4,X5) ),
    inference(superposition,[],[f565,f46])).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0)) ),
    inference(superposition,[],[f28,f26])).

fof(f708,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0))) ),
    inference(superposition,[],[f686,f26])).

fof(f246,plain,(
    ! [X24,X23,X21,X19,X17,X25,X22,X20,X18] : k7_enumset1(X20,X21,X22,X23,X24,X25,X17,X18,X19) = k2_xboole_0(k4_enumset1(X20,X21,X22,X23,X24,X25),k1_enumset1(X18,X19,X17)) ),
    inference(superposition,[],[f44,f31])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).

fof(f868,plain,(
    ! [X6,X10,X8,X7,X9] : k7_enumset1(X6,X6,X6,X6,X7,X7,X8,X9,X10) = k2_xboole_0(k1_tarski(X6),k2_enumset1(X7,X8,X9,X10)) ),
    inference(superposition,[],[f199,f751])).

fof(f199,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X4,X5,X6,X7,X0,X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X4,X5,X6,X7),k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f43,f37])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l142_enumset1)).

fof(f1623,plain,(
    ! [X6,X8,X7,X5,X9] : k4_enumset1(X5,X6,X7,X8,X9,X9) = k2_xboole_0(k1_tarski(X9),k2_enumset1(X5,X6,X7,X8)) ),
    inference(superposition,[],[f533,f52])).

fof(f533,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X1,X2,X3,X4,X0,X0) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0)) ),
    inference(superposition,[],[f146,f26])).

fof(f2087,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k3_enumset1(X1,X2,X0,X0,X3) ),
    inference(superposition,[],[f2060,f34])).

fof(f3511,plain,(
    ! [X14,X12,X15,X13] : k3_enumset1(X13,X14,X12,X12,X15) = k2_enumset1(X14,X12,X13,X15) ),
    inference(forward_demodulation,[],[f3491,f2104])).

fof(f3491,plain,(
    ! [X14,X12,X15,X13] : k3_enumset1(X13,X14,X12,X12,X15) = k2_xboole_0(k1_enumset1(X14,X13,X12),k1_tarski(X15)) ),
    inference(superposition,[],[f2060,f3335])).

fof(f3335,plain,(
    ! [X70,X72,X71] : k2_enumset1(X71,X71,X70,X72) = k1_enumset1(X72,X70,X71) ),
    inference(forward_demodulation,[],[f3324,f2383])).

fof(f2383,plain,(
    ! [X4,X2,X3] : k1_enumset1(X4,X3,X2) = k2_enumset1(X2,X3,X2,X4) ),
    inference(superposition,[],[f2189,f566])).

fof(f566,plain,(
    ! [X14,X17,X15,X16] : k3_enumset1(X14,X15,X14,X16,X17) = k2_enumset1(X14,X15,X16,X17) ),
    inference(forward_demodulation,[],[f550,f565])).

fof(f550,plain,(
    ! [X14,X17,X15,X16] : k3_enumset1(X14,X15,X14,X16,X17) = k2_xboole_0(k2_tarski(X14,X15),k2_tarski(X16,X17)) ),
    inference(superposition,[],[f546,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0) ),
    inference(superposition,[],[f31,f29])).

fof(f2189,plain,(
    ! [X4,X5,X3] : k1_enumset1(X5,X4,X3) = k3_enumset1(X3,X4,X3,X3,X5) ),
    inference(forward_demodulation,[],[f2176,f923])).

fof(f2176,plain,(
    ! [X4,X5,X3] : k3_enumset1(X3,X4,X3,X3,X5) = k2_xboole_0(k2_tarski(X4,X3),k1_tarski(X5)) ),
    inference(superposition,[],[f2060,f2115])).

fof(f2115,plain,(
    ! [X0,X1] : k2_tarski(X1,X0) = k2_enumset1(X0,X0,X0,X1) ),
    inference(superposition,[],[f2101,f37])).

fof(f2101,plain,(
    ! [X4,X5] : k2_tarski(X5,X4) = k3_enumset1(X4,X4,X4,X4,X5) ),
    inference(forward_demodulation,[],[f2088,f927])).

fof(f2088,plain,(
    ! [X4,X5] : k2_xboole_0(k1_tarski(X4),k1_tarski(X5)) = k3_enumset1(X4,X4,X4,X4,X5) ),
    inference(superposition,[],[f2060,f751])).

fof(f3324,plain,(
    ! [X70,X72,X71] : k2_enumset1(X71,X71,X70,X72) = k2_enumset1(X71,X70,X71,X72) ),
    inference(superposition,[],[f567,f2105])).

fof(f567,plain,(
    ! [X21,X19,X20,X18] : k3_enumset1(X18,X19,X19,X20,X21) = k2_enumset1(X19,X18,X20,X21) ),
    inference(forward_demodulation,[],[f551,f565])).

fof(f551,plain,(
    ! [X21,X19,X20,X18] : k3_enumset1(X18,X19,X19,X20,X21) = k2_xboole_0(k2_tarski(X19,X18),k2_tarski(X20,X21)) ),
    inference(superposition,[],[f546,f56])).

fof(f10592,plain,(
    ! [X24,X23,X25,X22] : k2_enumset1(X22,X23,X24,X25) = k2_enumset1(X23,X24,X22,X25) ),
    inference(superposition,[],[f3806,f3431])).

fof(f3431,plain,(
    ! [X6,X8,X7,X9] : k3_enumset1(X6,X8,X7,X6,X9) = k2_enumset1(X6,X8,X7,X9) ),
    inference(forward_demodulation,[],[f3417,f2104])).

fof(f3417,plain,(
    ! [X6,X8,X7,X9] : k3_enumset1(X6,X8,X7,X6,X9) = k2_xboole_0(k1_enumset1(X6,X7,X8),k1_tarski(X9)) ),
    inference(superposition,[],[f2060,f3328])).

fof(f3328,plain,(
    ! [X6,X8,X7] : k1_enumset1(X7,X6,X8) = k2_enumset1(X7,X6,X7,X8) ),
    inference(forward_demodulation,[],[f3302,f34])).

fof(f3302,plain,(
    ! [X6,X8,X7] : k2_enumset1(X7,X6,X7,X8) = k2_enumset1(X7,X7,X6,X8) ),
    inference(superposition,[],[f2105,f567])).

fof(f3806,plain,(
    ! [X10,X8,X11,X9] : k3_enumset1(X8,X10,X9,X8,X11) = k2_enumset1(X10,X9,X8,X11) ),
    inference(forward_demodulation,[],[f3792,f2104])).

fof(f3792,plain,(
    ! [X10,X8,X11,X9] : k3_enumset1(X8,X10,X9,X8,X11) = k2_xboole_0(k1_enumset1(X10,X8,X9),k1_tarski(X11)) ),
    inference(superposition,[],[f2060,f3593])).

fof(f3593,plain,(
    ! [X14,X15,X13] : k1_enumset1(X15,X13,X14) = k2_enumset1(X13,X14,X13,X15) ),
    inference(forward_demodulation,[],[f3568,f928])).

fof(f3568,plain,(
    ! [X14,X15,X13] : k2_enumset1(X13,X14,X13,X15) = k2_enumset1(X13,X14,X15,X15) ),
    inference(superposition,[],[f2109,f37])).

fof(f2109,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X1,X2,X3,X0,X0) = k2_enumset1(X1,X3,X2,X0) ),
    inference(backward_demodulation,[],[f552,f2104])).

fof(f552,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X1,X2,X3,X0,X0) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)) ),
    inference(superposition,[],[f546,f26])).

fof(f25,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:28:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (22338)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (22339)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (22331)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (22328)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (22326)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (22330)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (22325)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (22337)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (22327)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (22332)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (22334)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (22335)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (22342)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (22333)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (22336)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (22336)Refutation not found, incomplete strategy% (22336)------------------------------
% 0.21/0.50  % (22336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (22336)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (22336)Memory used [KB]: 10618
% 0.21/0.50  % (22336)Time elapsed: 0.093 s
% 0.21/0.50  % (22336)------------------------------
% 0.21/0.50  % (22336)------------------------------
% 0.21/0.50  % (22329)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (22341)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.32/0.53  % (22340)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 5.09/1.03  % (22329)Time limit reached!
% 5.09/1.03  % (22329)------------------------------
% 5.09/1.03  % (22329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.09/1.04  % (22329)Termination reason: Time limit
% 5.09/1.04  
% 5.09/1.04  % (22329)Memory used [KB]: 10874
% 5.09/1.04  % (22329)Time elapsed: 0.613 s
% 5.09/1.04  % (22329)------------------------------
% 5.09/1.04  % (22329)------------------------------
% 12.12/1.90  % (22330)Time limit reached!
% 12.12/1.90  % (22330)------------------------------
% 12.12/1.90  % (22330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.12/1.90  % (22330)Termination reason: Time limit
% 12.12/1.90  % (22330)Termination phase: Saturation
% 12.12/1.90  
% 12.12/1.90  % (22330)Memory used [KB]: 33389
% 12.12/1.90  % (22330)Time elapsed: 1.500 s
% 12.12/1.90  % (22330)------------------------------
% 12.12/1.90  % (22330)------------------------------
% 12.78/1.97  % (22331)Time limit reached!
% 12.78/1.97  % (22331)------------------------------
% 12.78/1.97  % (22331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.78/1.97  % (22331)Termination reason: Time limit
% 12.78/1.97  % (22331)Termination phase: Saturation
% 12.78/1.97  
% 12.78/1.97  % (22331)Memory used [KB]: 17910
% 12.78/1.97  % (22331)Time elapsed: 1.500 s
% 12.78/1.97  % (22331)------------------------------
% 12.78/1.97  % (22331)------------------------------
% 14.57/2.24  % (22327)Time limit reached!
% 14.57/2.24  % (22327)------------------------------
% 14.57/2.24  % (22327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.57/2.24  % (22327)Termination reason: Time limit
% 14.57/2.24  
% 14.57/2.24  % (22327)Memory used [KB]: 18421
% 14.57/2.24  % (22327)Time elapsed: 1.834 s
% 14.57/2.24  % (22327)------------------------------
% 14.57/2.24  % (22327)------------------------------
% 17.84/2.61  % (22337)Time limit reached!
% 17.84/2.61  % (22337)------------------------------
% 17.84/2.61  % (22337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.84/2.61  % (22337)Termination reason: Time limit
% 17.84/2.61  % (22337)Termination phase: Saturation
% 17.84/2.61  
% 17.84/2.61  % (22337)Memory used [KB]: 20340
% 17.84/2.61  % (22337)Time elapsed: 2.200 s
% 17.84/2.61  % (22337)------------------------------
% 17.84/2.61  % (22337)------------------------------
% 18.18/2.68  % (22328)Refutation found. Thanks to Tanya!
% 18.18/2.68  % SZS status Theorem for theBenchmark
% 18.18/2.68  % SZS output start Proof for theBenchmark
% 18.18/2.68  fof(f19080,plain,(
% 18.18/2.68    $false),
% 18.18/2.68    inference(subsumption_resolution,[],[f19079,f32])).
% 18.18/2.68  fof(f32,plain,(
% 18.18/2.68    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 18.18/2.68    inference(cnf_transformation,[],[f19])).
% 18.18/2.68  fof(f19,axiom,(
% 18.18/2.68    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 18.18/2.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 18.18/2.68  fof(f19079,plain,(
% 18.18/2.68    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(sK3,sK4))),
% 18.18/2.68    inference(forward_demodulation,[],[f18970,f36])).
% 18.18/2.68  fof(f36,plain,(
% 18.18/2.68    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 18.18/2.68    inference(cnf_transformation,[],[f17])).
% 18.18/2.68  fof(f17,axiom,(
% 18.18/2.68    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 18.18/2.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 18.18/2.68  fof(f18970,plain,(
% 18.18/2.68    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(sK3,sK4))),
% 18.18/2.68    inference(superposition,[],[f12632,f1037])).
% 18.18/2.68  fof(f1037,plain,(
% 18.18/2.68    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5))) )),
% 18.18/2.68    inference(forward_demodulation,[],[f1024,f33])).
% 18.18/2.68  fof(f33,plain,(
% 18.18/2.68    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 18.18/2.68    inference(cnf_transformation,[],[f18])).
% 18.18/2.68  fof(f18,axiom,(
% 18.18/2.68    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 18.18/2.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 18.18/2.68  fof(f1024,plain,(
% 18.18/2.68    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5))) )),
% 18.18/2.68    inference(superposition,[],[f167,f33])).
% 18.18/2.68  fof(f167,plain,(
% 18.18/2.68    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 18.18/2.68    inference(forward_demodulation,[],[f161,f33])).
% 18.18/2.68  fof(f161,plain,(
% 18.18/2.68    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 18.18/2.68    inference(superposition,[],[f38,f33])).
% 18.18/2.68  fof(f38,plain,(
% 18.18/2.68    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 18.18/2.68    inference(cnf_transformation,[],[f16])).
% 18.18/2.69  fof(f16,axiom,(
% 18.18/2.69    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 18.18/2.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 18.18/2.69  fof(f12632,plain,(
% 18.18/2.69    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK1,sK2,sK4))),
% 18.18/2.69    inference(superposition,[],[f25,f12224])).
% 18.18/2.69  fof(f12224,plain,(
% 18.18/2.69    ( ! [X47,X45,X46,X44] : (k2_enumset1(X45,X44,X46,X47) = k2_enumset1(X45,X46,X44,X47)) )),
% 18.18/2.69    inference(superposition,[],[f10592,f10269])).
% 18.18/2.69  fof(f10269,plain,(
% 18.18/2.69    ( ! [X54,X52,X53,X51] : (k2_enumset1(X53,X52,X51,X54) = k2_enumset1(X52,X53,X51,X54)) )),
% 18.18/2.69    inference(superposition,[],[f3511,f2105])).
% 18.18/2.69  fof(f2105,plain,(
% 18.18/2.69    ( ! [X2,X0,X3,X1] : (k3_enumset1(X1,X2,X0,X0,X3) = k2_enumset1(X0,X2,X1,X3)) )),
% 18.18/2.69    inference(backward_demodulation,[],[f2087,f2104])).
% 18.18/2.69  fof(f2104,plain,(
% 18.18/2.69    ( ! [X21,X19,X20,X18] : (k2_xboole_0(k1_enumset1(X20,X18,X19),k1_tarski(X21)) = k2_enumset1(X20,X19,X18,X21)) )),
% 18.18/2.69    inference(forward_demodulation,[],[f2093,f37])).
% 18.18/2.69  fof(f37,plain,(
% 18.18/2.69    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 18.18/2.69    inference(cnf_transformation,[],[f12])).
% 18.18/2.69  fof(f12,axiom,(
% 18.18/2.69    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 18.18/2.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 18.18/2.69  fof(f2093,plain,(
% 18.18/2.69    ( ! [X21,X19,X20,X18] : (k3_enumset1(X20,X20,X19,X18,X21) = k2_xboole_0(k1_enumset1(X20,X18,X19),k1_tarski(X21))) )),
% 18.18/2.69    inference(superposition,[],[f2060,f928])).
% 18.18/2.69  fof(f928,plain,(
% 18.18/2.69    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X2,X0,X0)) )),
% 18.18/2.69    inference(backward_demodulation,[],[f676,f923])).
% 18.18/2.69  fof(f923,plain,(
% 18.18/2.69    ( ! [X4,X5,X3] : (k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k1_enumset1(X3,X4,X5)) )),
% 18.18/2.69    inference(superposition,[],[f692,f52])).
% 18.18/2.69  fof(f52,plain,(
% 18.18/2.69    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 18.18/2.69    inference(superposition,[],[f47,f28])).
% 18.18/2.69  fof(f28,plain,(
% 18.18/2.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 18.18/2.69    inference(cnf_transformation,[],[f15])).
% 18.18/2.69  fof(f15,axiom,(
% 18.18/2.69    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 18.18/2.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 18.18/2.69  fof(f47,plain,(
% 18.18/2.69    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 18.18/2.69    inference(superposition,[],[f28,f27])).
% 18.18/2.69  fof(f27,plain,(
% 18.18/2.69    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 18.18/2.69    inference(cnf_transformation,[],[f2])).
% 18.18/2.69  fof(f2,axiom,(
% 18.18/2.69    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 18.18/2.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 18.18/2.69  fof(f692,plain,(
% 18.18/2.69    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 18.18/2.69    inference(forward_demodulation,[],[f666,f34])).
% 18.18/2.69  fof(f34,plain,(
% 18.18/2.69    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 18.18/2.69    inference(cnf_transformation,[],[f11])).
% 18.18/2.69  fof(f11,axiom,(
% 18.18/2.69    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 18.18/2.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 18.18/2.69  fof(f666,plain,(
% 18.18/2.69    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 18.18/2.69    inference(superposition,[],[f565,f26])).
% 18.18/2.69  fof(f26,plain,(
% 18.18/2.69    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 18.18/2.69    inference(cnf_transformation,[],[f9])).
% 18.18/2.69  fof(f9,axiom,(
% 18.18/2.69    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 18.18/2.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 18.18/2.69  fof(f565,plain,(
% 18.18/2.69    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 18.18/2.69    inference(forward_demodulation,[],[f547,f37])).
% 18.18/2.69  fof(f547,plain,(
% 18.18/2.69    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 18.18/2.69    inference(superposition,[],[f546,f29])).
% 18.18/2.69  fof(f29,plain,(
% 18.18/2.69    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 18.18/2.69    inference(cnf_transformation,[],[f10])).
% 18.18/2.69  fof(f10,axiom,(
% 18.18/2.69    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 18.18/2.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 18.18/2.69  fof(f546,plain,(
% 18.18/2.69    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 18.18/2.69    inference(forward_demodulation,[],[f531,f39])).
% 18.18/2.69  fof(f39,plain,(
% 18.18/2.69    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 18.18/2.69    inference(cnf_transformation,[],[f13])).
% 18.18/2.69  fof(f13,axiom,(
% 18.18/2.69    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 18.18/2.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 18.18/2.69  fof(f531,plain,(
% 18.18/2.69    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 18.18/2.69    inference(superposition,[],[f146,f34])).
% 18.18/2.69  fof(f146,plain,(
% 18.18/2.69    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 18.18/2.69    inference(forward_demodulation,[],[f135,f40])).
% 18.18/2.69  fof(f40,plain,(
% 18.18/2.69    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 18.18/2.69    inference(cnf_transformation,[],[f14])).
% 18.18/2.69  fof(f14,axiom,(
% 18.18/2.69    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 18.18/2.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 18.18/2.69  fof(f135,plain,(
% 18.18/2.69    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 18.18/2.69    inference(superposition,[],[f41,f37])).
% 18.18/2.69  fof(f41,plain,(
% 18.18/2.69    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 18.18/2.69    inference(cnf_transformation,[],[f7])).
% 18.18/2.69  fof(f7,axiom,(
% 18.18/2.69    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 18.18/2.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).
% 18.18/2.69  fof(f676,plain,(
% 18.18/2.69    ( ! [X2,X0,X1] : (k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))) )),
% 18.18/2.69    inference(superposition,[],[f565,f26])).
% 18.18/2.69  fof(f2060,plain,(
% 18.18/2.69    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0)) = k3_enumset1(X3,X4,X2,X1,X0)) )),
% 18.18/2.69    inference(backward_demodulation,[],[f533,f2058])).
% 18.18/2.69  fof(f2058,plain,(
% 18.18/2.69    ( ! [X6,X8,X7,X5,X9] : (k4_enumset1(X5,X6,X7,X8,X9,X9) = k3_enumset1(X7,X8,X6,X5,X9)) )),
% 18.18/2.69    inference(backward_demodulation,[],[f1623,f2057])).
% 18.18/2.69  fof(f2057,plain,(
% 18.18/2.69    ( ! [X6,X10,X8,X7,X9] : (k2_xboole_0(k1_tarski(X6),k2_enumset1(X7,X8,X9,X10)) = k3_enumset1(X9,X10,X8,X7,X6)) )),
% 18.18/2.69    inference(backward_demodulation,[],[f868,f2056])).
% 18.18/2.69  fof(f2056,plain,(
% 18.18/2.69    ( ! [X6,X4,X2,X5,X3] : (k7_enumset1(X2,X2,X2,X2,X3,X3,X4,X5,X6) = k3_enumset1(X5,X6,X4,X3,X2)) )),
% 18.18/2.69    inference(forward_demodulation,[],[f2047,f561])).
% 18.18/2.69  fof(f561,plain,(
% 18.18/2.69    ( ! [X6,X8,X7,X5,X9] : (k2_xboole_0(k2_tarski(X8,X9),k1_enumset1(X5,X6,X7)) = k3_enumset1(X5,X6,X7,X8,X9)) )),
% 18.18/2.69    inference(superposition,[],[f546,f52])).
% 18.18/2.69  fof(f2047,plain,(
% 18.18/2.69    ( ! [X6,X4,X2,X5,X3] : (k7_enumset1(X2,X2,X2,X2,X3,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X3,X2),k1_enumset1(X5,X6,X4))) )),
% 18.18/2.69    inference(superposition,[],[f246,f1634])).
% 18.18/2.69  fof(f1634,plain,(
% 18.18/2.69    ( ! [X4,X5] : (k2_tarski(X5,X4) = k4_enumset1(X4,X4,X4,X4,X5,X5)) )),
% 18.18/2.69    inference(forward_demodulation,[],[f1616,f927])).
% 18.18/2.69  fof(f927,plain,(
% 18.18/2.69    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) )),
% 18.18/2.69    inference(forward_demodulation,[],[f913,f56])).
% 18.18/2.69  fof(f56,plain,(
% 18.18/2.69    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)) )),
% 18.18/2.69    inference(superposition,[],[f31,f29])).
% 18.18/2.69  fof(f31,plain,(
% 18.18/2.69    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 18.18/2.69    inference(cnf_transformation,[],[f4])).
% 18.18/2.69  fof(f4,axiom,(
% 18.18/2.69    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 18.18/2.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).
% 18.18/2.69  fof(f913,plain,(
% 18.18/2.69    ( ! [X0,X1] : (k1_enumset1(X1,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) )),
% 18.18/2.69    inference(superposition,[],[f692,f26])).
% 18.18/2.69  fof(f1616,plain,(
% 18.18/2.69    ( ! [X4,X5] : (k4_enumset1(X4,X4,X4,X4,X5,X5) = k2_xboole_0(k1_tarski(X4),k1_tarski(X5))) )),
% 18.18/2.69    inference(superposition,[],[f533,f751])).
% 18.18/2.69  fof(f751,plain,(
% 18.18/2.69    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 18.18/2.69    inference(backward_demodulation,[],[f708,f749])).
% 18.18/2.69  fof(f749,plain,(
% 18.18/2.69    ( ! [X0] : (k1_tarski(X0) = k3_tarski(k1_tarski(k1_tarski(X0)))) )),
% 18.18/2.69    inference(forward_demodulation,[],[f738,f26])).
% 18.18/2.69  fof(f738,plain,(
% 18.18/2.69    ( ! [X0] : (k2_tarski(X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0)))) )),
% 18.18/2.69    inference(superposition,[],[f717,f29])).
% 18.18/2.69  fof(f717,plain,(
% 18.18/2.69    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0)))) )),
% 18.18/2.69    inference(forward_demodulation,[],[f711,f26])).
% 18.18/2.69  fof(f711,plain,(
% 18.18/2.69    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k3_tarski(k1_tarski(k2_tarski(X0,X0)))) )),
% 18.18/2.69    inference(superposition,[],[f686,f34])).
% 18.18/2.69  fof(f686,plain,(
% 18.18/2.69    ( ! [X4,X5] : (k3_tarski(k1_tarski(k2_tarski(X4,X5))) = k2_enumset1(X4,X5,X4,X5)) )),
% 18.18/2.69    inference(superposition,[],[f565,f46])).
% 18.18/2.69  fof(f46,plain,(
% 18.18/2.69    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))) )),
% 18.18/2.69    inference(superposition,[],[f28,f26])).
% 18.18/2.69  fof(f708,plain,(
% 18.18/2.69    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0)))) )),
% 18.18/2.69    inference(superposition,[],[f686,f26])).
% 18.18/2.69  fof(f246,plain,(
% 18.18/2.69    ( ! [X24,X23,X21,X19,X17,X25,X22,X20,X18] : (k7_enumset1(X20,X21,X22,X23,X24,X25,X17,X18,X19) = k2_xboole_0(k4_enumset1(X20,X21,X22,X23,X24,X25),k1_enumset1(X18,X19,X17))) )),
% 18.18/2.69    inference(superposition,[],[f44,f31])).
% 18.18/2.69  fof(f44,plain,(
% 18.18/2.69    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))) )),
% 18.18/2.69    inference(cnf_transformation,[],[f5])).
% 18.18/2.69  fof(f5,axiom,(
% 18.18/2.69    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 18.18/2.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).
% 18.18/2.69  fof(f868,plain,(
% 18.18/2.69    ( ! [X6,X10,X8,X7,X9] : (k7_enumset1(X6,X6,X6,X6,X7,X7,X8,X9,X10) = k2_xboole_0(k1_tarski(X6),k2_enumset1(X7,X8,X9,X10))) )),
% 18.18/2.69    inference(superposition,[],[f199,f751])).
% 18.18/2.69  fof(f199,plain,(
% 18.18/2.69    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X4,X5,X6,X7,X0,X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X4,X5,X6,X7),k2_enumset1(X0,X1,X2,X3))) )),
% 18.18/2.69    inference(superposition,[],[f43,f37])).
% 18.18/2.69  fof(f43,plain,(
% 18.18/2.69    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))) )),
% 18.18/2.69    inference(cnf_transformation,[],[f3])).
% 18.18/2.69  fof(f3,axiom,(
% 18.18/2.69    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))),
% 18.18/2.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l142_enumset1)).
% 18.18/2.69  fof(f1623,plain,(
% 18.18/2.69    ( ! [X6,X8,X7,X5,X9] : (k4_enumset1(X5,X6,X7,X8,X9,X9) = k2_xboole_0(k1_tarski(X9),k2_enumset1(X5,X6,X7,X8))) )),
% 18.18/2.69    inference(superposition,[],[f533,f52])).
% 18.18/2.69  fof(f533,plain,(
% 18.18/2.69    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X1,X2,X3,X4,X0,X0) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))) )),
% 18.18/2.69    inference(superposition,[],[f146,f26])).
% 18.18/2.69  fof(f2087,plain,(
% 18.18/2.69    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k3_enumset1(X1,X2,X0,X0,X3)) )),
% 18.18/2.69    inference(superposition,[],[f2060,f34])).
% 18.18/2.69  fof(f3511,plain,(
% 18.18/2.69    ( ! [X14,X12,X15,X13] : (k3_enumset1(X13,X14,X12,X12,X15) = k2_enumset1(X14,X12,X13,X15)) )),
% 18.18/2.69    inference(forward_demodulation,[],[f3491,f2104])).
% 18.18/2.69  fof(f3491,plain,(
% 18.18/2.69    ( ! [X14,X12,X15,X13] : (k3_enumset1(X13,X14,X12,X12,X15) = k2_xboole_0(k1_enumset1(X14,X13,X12),k1_tarski(X15))) )),
% 18.18/2.69    inference(superposition,[],[f2060,f3335])).
% 18.18/2.69  fof(f3335,plain,(
% 18.18/2.69    ( ! [X70,X72,X71] : (k2_enumset1(X71,X71,X70,X72) = k1_enumset1(X72,X70,X71)) )),
% 18.18/2.69    inference(forward_demodulation,[],[f3324,f2383])).
% 18.18/2.69  fof(f2383,plain,(
% 18.18/2.69    ( ! [X4,X2,X3] : (k1_enumset1(X4,X3,X2) = k2_enumset1(X2,X3,X2,X4)) )),
% 18.18/2.69    inference(superposition,[],[f2189,f566])).
% 18.18/2.69  fof(f566,plain,(
% 18.18/2.69    ( ! [X14,X17,X15,X16] : (k3_enumset1(X14,X15,X14,X16,X17) = k2_enumset1(X14,X15,X16,X17)) )),
% 18.18/2.69    inference(forward_demodulation,[],[f550,f565])).
% 18.18/2.69  fof(f550,plain,(
% 18.18/2.69    ( ! [X14,X17,X15,X16] : (k3_enumset1(X14,X15,X14,X16,X17) = k2_xboole_0(k2_tarski(X14,X15),k2_tarski(X16,X17))) )),
% 18.18/2.69    inference(superposition,[],[f546,f54])).
% 18.18/2.69  fof(f54,plain,(
% 18.18/2.69    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 18.18/2.69    inference(superposition,[],[f31,f29])).
% 18.18/2.69  fof(f2189,plain,(
% 18.18/2.69    ( ! [X4,X5,X3] : (k1_enumset1(X5,X4,X3) = k3_enumset1(X3,X4,X3,X3,X5)) )),
% 18.18/2.69    inference(forward_demodulation,[],[f2176,f923])).
% 18.18/2.69  fof(f2176,plain,(
% 18.18/2.69    ( ! [X4,X5,X3] : (k3_enumset1(X3,X4,X3,X3,X5) = k2_xboole_0(k2_tarski(X4,X3),k1_tarski(X5))) )),
% 18.18/2.69    inference(superposition,[],[f2060,f2115])).
% 18.18/2.69  fof(f2115,plain,(
% 18.18/2.69    ( ! [X0,X1] : (k2_tarski(X1,X0) = k2_enumset1(X0,X0,X0,X1)) )),
% 18.18/2.69    inference(superposition,[],[f2101,f37])).
% 18.18/2.69  fof(f2101,plain,(
% 18.18/2.69    ( ! [X4,X5] : (k2_tarski(X5,X4) = k3_enumset1(X4,X4,X4,X4,X5)) )),
% 18.18/2.69    inference(forward_demodulation,[],[f2088,f927])).
% 18.18/2.69  fof(f2088,plain,(
% 18.18/2.69    ( ! [X4,X5] : (k2_xboole_0(k1_tarski(X4),k1_tarski(X5)) = k3_enumset1(X4,X4,X4,X4,X5)) )),
% 18.18/2.69    inference(superposition,[],[f2060,f751])).
% 18.18/2.69  fof(f3324,plain,(
% 18.18/2.69    ( ! [X70,X72,X71] : (k2_enumset1(X71,X71,X70,X72) = k2_enumset1(X71,X70,X71,X72)) )),
% 18.18/2.69    inference(superposition,[],[f567,f2105])).
% 18.18/2.69  fof(f567,plain,(
% 18.18/2.69    ( ! [X21,X19,X20,X18] : (k3_enumset1(X18,X19,X19,X20,X21) = k2_enumset1(X19,X18,X20,X21)) )),
% 18.18/2.69    inference(forward_demodulation,[],[f551,f565])).
% 18.18/2.69  fof(f551,plain,(
% 18.18/2.69    ( ! [X21,X19,X20,X18] : (k3_enumset1(X18,X19,X19,X20,X21) = k2_xboole_0(k2_tarski(X19,X18),k2_tarski(X20,X21))) )),
% 18.18/2.69    inference(superposition,[],[f546,f56])).
% 18.18/2.69  fof(f10592,plain,(
% 18.18/2.69    ( ! [X24,X23,X25,X22] : (k2_enumset1(X22,X23,X24,X25) = k2_enumset1(X23,X24,X22,X25)) )),
% 18.18/2.69    inference(superposition,[],[f3806,f3431])).
% 18.18/2.69  fof(f3431,plain,(
% 18.18/2.69    ( ! [X6,X8,X7,X9] : (k3_enumset1(X6,X8,X7,X6,X9) = k2_enumset1(X6,X8,X7,X9)) )),
% 18.18/2.69    inference(forward_demodulation,[],[f3417,f2104])).
% 18.18/2.69  fof(f3417,plain,(
% 18.18/2.69    ( ! [X6,X8,X7,X9] : (k3_enumset1(X6,X8,X7,X6,X9) = k2_xboole_0(k1_enumset1(X6,X7,X8),k1_tarski(X9))) )),
% 18.18/2.69    inference(superposition,[],[f2060,f3328])).
% 18.18/2.69  fof(f3328,plain,(
% 18.18/2.69    ( ! [X6,X8,X7] : (k1_enumset1(X7,X6,X8) = k2_enumset1(X7,X6,X7,X8)) )),
% 18.18/2.69    inference(forward_demodulation,[],[f3302,f34])).
% 18.18/2.69  fof(f3302,plain,(
% 18.18/2.69    ( ! [X6,X8,X7] : (k2_enumset1(X7,X6,X7,X8) = k2_enumset1(X7,X7,X6,X8)) )),
% 18.18/2.69    inference(superposition,[],[f2105,f567])).
% 18.18/2.69  fof(f3806,plain,(
% 18.18/2.69    ( ! [X10,X8,X11,X9] : (k3_enumset1(X8,X10,X9,X8,X11) = k2_enumset1(X10,X9,X8,X11)) )),
% 18.18/2.69    inference(forward_demodulation,[],[f3792,f2104])).
% 18.18/2.69  fof(f3792,plain,(
% 18.18/2.69    ( ! [X10,X8,X11,X9] : (k3_enumset1(X8,X10,X9,X8,X11) = k2_xboole_0(k1_enumset1(X10,X8,X9),k1_tarski(X11))) )),
% 18.18/2.69    inference(superposition,[],[f2060,f3593])).
% 18.18/2.69  fof(f3593,plain,(
% 18.18/2.69    ( ! [X14,X15,X13] : (k1_enumset1(X15,X13,X14) = k2_enumset1(X13,X14,X13,X15)) )),
% 18.18/2.69    inference(forward_demodulation,[],[f3568,f928])).
% 18.18/2.69  fof(f3568,plain,(
% 18.18/2.69    ( ! [X14,X15,X13] : (k2_enumset1(X13,X14,X13,X15) = k2_enumset1(X13,X14,X15,X15)) )),
% 18.18/2.69    inference(superposition,[],[f2109,f37])).
% 18.18/2.69  fof(f2109,plain,(
% 18.18/2.69    ( ! [X2,X0,X3,X1] : (k3_enumset1(X1,X2,X3,X0,X0) = k2_enumset1(X1,X3,X2,X0)) )),
% 18.18/2.69    inference(backward_demodulation,[],[f552,f2104])).
% 18.18/2.69  fof(f552,plain,(
% 18.18/2.69    ( ! [X2,X0,X3,X1] : (k3_enumset1(X1,X2,X3,X0,X0) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))) )),
% 18.18/2.69    inference(superposition,[],[f546,f26])).
% 18.18/2.69  fof(f25,plain,(
% 18.18/2.69    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 18.18/2.69    inference(cnf_transformation,[],[f24])).
% 18.18/2.69  fof(f24,plain,(
% 18.18/2.69    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 18.18/2.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f23])).
% 18.18/2.69  fof(f23,plain,(
% 18.18/2.69    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 18.18/2.69    introduced(choice_axiom,[])).
% 18.18/2.69  fof(f22,plain,(
% 18.18/2.69    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 18.18/2.69    inference(ennf_transformation,[],[f21])).
% 18.18/2.69  fof(f21,negated_conjecture,(
% 18.18/2.69    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 18.18/2.69    inference(negated_conjecture,[],[f20])).
% 18.18/2.69  fof(f20,conjecture,(
% 18.18/2.69    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 18.18/2.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).
% 18.18/2.69  % SZS output end Proof for theBenchmark
% 18.18/2.69  % (22328)------------------------------
% 18.18/2.69  % (22328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.18/2.69  % (22328)Termination reason: Refutation
% 18.18/2.69  
% 18.18/2.69  % (22328)Memory used [KB]: 31214
% 18.18/2.69  % (22328)Time elapsed: 2.280 s
% 18.18/2.69  % (22328)------------------------------
% 18.18/2.69  % (22328)------------------------------
% 18.18/2.69  % (22322)Success in time 2.337 s
%------------------------------------------------------------------------------
