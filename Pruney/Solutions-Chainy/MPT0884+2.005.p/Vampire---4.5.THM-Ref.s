%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:56 EST 2020

% Result     : Theorem 33.25s
% Output     : Refutation 33.25s
% Verified   : 
% Statistics : Number of formulae       :  157 (12960 expanded)
%              Number of leaves         :   20 (4320 expanded)
%              Depth                    :   35
%              Number of atoms          :  159 (12962 expanded)
%              Number of equality atoms :  158 (12961 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f50616,plain,(
    $false ),
    inference(subsumption_resolution,[],[f50615,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f50615,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(sK3,sK4)) ),
    inference(forward_demodulation,[],[f50614,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f50614,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(superposition,[],[f50162,f970])).

fof(f970,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5)) ),
    inference(forward_demodulation,[],[f958,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f958,plain,(
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

fof(f50162,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(superposition,[],[f49632,f45757])).

fof(f45757,plain,(
    ! [X127,X130,X128,X129] : k2_enumset1(X130,X129,X128,X127) = k2_enumset1(X130,X129,X127,X128) ),
    inference(superposition,[],[f45170,f44473])).

fof(f44473,plain,(
    ! [X127,X130,X128,X129] : k2_enumset1(X127,X128,X129,X130) = k2_enumset1(X130,X129,X128,X127) ),
    inference(superposition,[],[f16753,f16236])).

fof(f16236,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X1,X2,X3) ),
    inference(backward_demodulation,[],[f4151,f16235])).

fof(f16235,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X3,X1,X2,X0,X0) ),
    inference(forward_demodulation,[],[f16207,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f16207,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X3,X1,X2,X0,X0) ),
    inference(superposition,[],[f3430,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f3430,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X4,X2,X3,X0,X1) = k4_enumset1(X0,X1,X0,X2,X3,X4) ),
    inference(forward_demodulation,[],[f3415,f3334])).

fof(f3334,plain,(
    ! [X14,X12,X10,X13,X11] : k4_enumset1(X11,X10,X12,X12,X13,X14) = k3_enumset1(X14,X12,X13,X11,X10) ),
    inference(backward_demodulation,[],[f1599,f3329])).

fof(f3329,plain,(
    ! [X14,X12,X15,X13,X16] : k5_enumset1(X14,X15,X16,X12,X12,X13,X13) = k3_enumset1(X16,X14,X15,X13,X12) ),
    inference(backward_demodulation,[],[f3232,f3328])).

fof(f3328,plain,(
    ! [X12,X10,X13,X11,X9] : k3_enumset1(X9,X10,X11,X12,X13) = k2_xboole_0(k1_enumset1(X11,X9,X10),k2_tarski(X12,X13)) ),
    inference(forward_demodulation,[],[f3293,f1586])).

fof(f1586,plain,(
    ! [X14,X12,X10,X13,X11] : k3_enumset1(X10,X11,X12,X13,X14) = k5_enumset1(X10,X10,X10,X11,X12,X13,X14) ),
    inference(backward_demodulation,[],[f1036,f1585])).

fof(f1585,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(forward_demodulation,[],[f1564,f39])).

fof(f1564,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(superposition,[],[f679,f26])).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f679,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(forward_demodulation,[],[f667,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f667,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(superposition,[],[f195,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f195,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(forward_demodulation,[],[f185,f41])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f185,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(superposition,[],[f42,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(f1036,plain,(
    ! [X14,X12,X10,X13,X11] : k5_enumset1(X10,X10,X10,X11,X12,X13,X14) = k2_xboole_0(k1_tarski(X10),k2_enumset1(X11,X12,X13,X14)) ),
    inference(forward_demodulation,[],[f1012,f1019])).

fof(f1019,plain,(
    ! [X0] : k1_tarski(X0) = k3_tarski(k1_tarski(k1_tarski(X0))) ),
    inference(forward_demodulation,[],[f1006,f26])).

fof(f1006,plain,(
    ! [X0] : k2_tarski(X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0))) ),
    inference(superposition,[],[f974,f29])).

fof(f974,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0))) ),
    inference(superposition,[],[f952,f34])).

fof(f952,plain,(
    ! [X0] : k3_tarski(k1_tarski(k1_tarski(X0))) = k2_enumset1(X0,X0,X0,X0) ),
    inference(superposition,[],[f926,f37])).

fof(f926,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0))) ),
    inference(forward_demodulation,[],[f920,f26])).

fof(f920,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k3_tarski(k1_tarski(k2_tarski(X0,X0))) ),
    inference(superposition,[],[f895,f39])).

fof(f895,plain,(
    ! [X0,X1] : k4_enumset1(X0,X1,X0,X0,X0,X1) = k3_tarski(k1_tarski(k2_tarski(X0,X1))) ),
    inference(forward_demodulation,[],[f887,f29])).

fof(f887,plain,(
    ! [X0,X1] : k4_enumset1(X0,X1,X0,X0,X0,X1) = k3_tarski(k1_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(superposition,[],[f866,f40])).

fof(f866,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X1,X2,X0,X0,X1,X2) = k3_tarski(k1_tarski(k1_enumset1(X0,X1,X2))) ),
    inference(forward_demodulation,[],[f862,f34])).

fof(f862,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X1,X2,X0,X0,X1,X2) = k3_tarski(k1_tarski(k2_enumset1(X0,X0,X1,X2))) ),
    inference(superposition,[],[f189,f41])).

fof(f189,plain,(
    ! [X10,X8,X11,X9] : k3_tarski(k1_tarski(k2_enumset1(X8,X9,X10,X11))) = k6_enumset1(X8,X9,X10,X11,X8,X9,X10,X11) ),
    inference(superposition,[],[f42,f46])).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0)) ),
    inference(superposition,[],[f28,f26])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f1012,plain,(
    ! [X14,X12,X10,X13,X11] : k5_enumset1(X10,X10,X10,X11,X12,X13,X14) = k2_xboole_0(k3_tarski(k1_tarski(k1_tarski(X10))),k2_enumset1(X11,X12,X13,X14)) ),
    inference(superposition,[],[f195,f974])).

fof(f3293,plain,(
    ! [X12,X10,X13,X11,X9] : k5_enumset1(X9,X9,X9,X10,X11,X12,X13) = k2_xboole_0(k1_enumset1(X11,X9,X10),k2_tarski(X12,X13)) ),
    inference(superposition,[],[f808,f2715])).

fof(f2715,plain,(
    ! [X12,X13,X11] : k1_enumset1(X12,X11,X13) = k3_enumset1(X11,X11,X11,X13,X12) ),
    inference(superposition,[],[f1748,f1824])).

fof(f1824,plain,(
    ! [X4,X5,X3] : k1_enumset1(X5,X3,X4) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X5,X3,X4)) ),
    inference(superposition,[],[f1761,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

fof(f1761,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2)) ),
    inference(forward_demodulation,[],[f1743,f34])).

fof(f1743,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f1687,f37])).

fof(f1687,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X3,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f1585,f34])).

fof(f1748,plain,(
    ! [X6,X8,X7,X5] : k3_enumset1(X8,X5,X5,X6,X7) = k2_xboole_0(k1_tarski(X8),k1_enumset1(X7,X5,X6)) ),
    inference(superposition,[],[f1687,f31])).

fof(f808,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k2_tarski(X0,X1)) = k5_enumset1(X2,X3,X4,X5,X6,X0,X1) ),
    inference(forward_demodulation,[],[f797,f769])).

fof(f769,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X1,X2,X3,X4,X5,X5,X6) ),
    inference(forward_demodulation,[],[f767,f41])).

fof(f767,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X1,X2,X3,X4,X5,X5,X6) ),
    inference(superposition,[],[f331,f241])).

fof(f241,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(forward_demodulation,[],[f234,f42])).

fof(f234,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(superposition,[],[f43,f37])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

fof(f331,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X2,X3,X4,X5,X6,X7,X0,X0,X1) = k6_enumset1(X2,X3,X4,X5,X6,X7,X0,X1) ),
    inference(backward_demodulation,[],[f265,f328])).

fof(f328,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(forward_demodulation,[],[f316,f241])).

fof(f316,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(superposition,[],[f45,f40])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).

fof(f265,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X2,X3,X4,X5,X6,X7,X0,X0,X1) = k2_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f44,f29])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).

fof(f797,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X2,X3,X4,X5,X6,X0,X0,X1) = k2_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f274,f29])).

fof(f274,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(forward_demodulation,[],[f264,f241])).

fof(f264,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(superposition,[],[f44,f39])).

fof(f3232,plain,(
    ! [X14,X12,X15,X13,X16] : k5_enumset1(X14,X15,X16,X12,X12,X13,X13) = k2_xboole_0(k1_enumset1(X15,X16,X14),k2_tarski(X13,X12)) ),
    inference(superposition,[],[f669,f2550])).

fof(f2550,plain,(
    ! [X0,X1] : k2_tarski(X1,X0) = k2_enumset1(X0,X0,X1,X1) ),
    inference(forward_demodulation,[],[f2534,f1827])).

fof(f1827,plain,(
    ! [X12,X11] : k2_tarski(X12,X11) = k2_xboole_0(k1_tarski(X11),k2_tarski(X12,X11)) ),
    inference(superposition,[],[f1761,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[],[f31,f29])).

fof(f2534,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X0)) = k2_enumset1(X0,X0,X1,X1) ),
    inference(superposition,[],[f1751,f37])).

fof(f1751,plain,(
    ! [X17,X18,X16] : k3_enumset1(X18,X16,X16,X17,X17) = k2_xboole_0(k1_tarski(X18),k2_tarski(X17,X16)) ),
    inference(superposition,[],[f1687,f56])).

fof(f669,plain,(
    ! [X14,X19,X17,X15,X13,X18,X16] : k5_enumset1(X13,X14,X15,X16,X17,X18,X19) = k2_xboole_0(k1_enumset1(X14,X15,X13),k2_enumset1(X16,X17,X18,X19)) ),
    inference(superposition,[],[f195,f31])).

fof(f1599,plain,(
    ! [X14,X12,X10,X13,X11] : k4_enumset1(X11,X10,X12,X12,X13,X14) = k5_enumset1(X12,X13,X14,X10,X10,X11,X11) ),
    inference(superposition,[],[f719,f681])).

fof(f681,plain,(
    ! [X30,X28,X26,X31,X29,X27] : k5_enumset1(X26,X27,X27,X28,X29,X30,X31) = k4_enumset1(X27,X26,X28,X29,X30,X31) ),
    inference(forward_demodulation,[],[f671,f679])).

fof(f671,plain,(
    ! [X30,X28,X26,X31,X29,X27] : k5_enumset1(X26,X27,X27,X28,X29,X30,X31) = k2_xboole_0(k2_tarski(X27,X26),k2_enumset1(X28,X29,X30,X31)) ),
    inference(superposition,[],[f195,f56])).

fof(f719,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X3,X4,X5,X0,X0,X1,X2) = k5_enumset1(X0,X1,X2,X3,X3,X4,X5) ),
    inference(superposition,[],[f682,f41])).

fof(f682,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X3,X4,X5,X6,X0,X0,X1,X2) ),
    inference(backward_demodulation,[],[f187,f675])).

fof(f675,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k2_xboole_0(k2_enumset1(X10,X11,X12,X13),k1_enumset1(X7,X8,X9)) = k5_enumset1(X7,X8,X9,X10,X11,X12,X13) ),
    inference(superposition,[],[f195,f52])).

fof(f52,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f47,f28])).

fof(f47,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f187,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X3,X4,X5,X6,X0,X0,X1,X2) = k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f42,f34])).

fof(f3415,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X1,X2,X2,X3,X4) = k4_enumset1(X0,X1,X0,X2,X3,X4) ),
    inference(superposition,[],[f3376,f40])).

fof(f3376,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X3,X4,X5,X0,X0,X1,X2) = k4_enumset1(X4,X5,X3,X0,X1,X2) ),
    inference(backward_demodulation,[],[f673,f3374])).

fof(f3374,plain,(
    ! [X12,X10,X8,X7,X11,X9] : k4_enumset1(X7,X8,X9,X10,X11,X12) = k2_xboole_0(k1_enumset1(X9,X7,X8),k1_enumset1(X10,X11,X12)) ),
    inference(backward_demodulation,[],[f3148,f3373])).

fof(f3373,plain,(
    ! [X6,X10,X8,X7,X11,X9] : k4_enumset1(X6,X7,X8,X9,X10,X11) = k6_enumset1(X6,X6,X6,X7,X8,X9,X10,X11) ),
    inference(forward_demodulation,[],[f3363,f679])).

fof(f3363,plain,(
    ! [X6,X10,X8,X7,X11,X9] : k2_xboole_0(k2_tarski(X6,X7),k2_enumset1(X8,X9,X10,X11)) = k6_enumset1(X6,X6,X6,X7,X8,X9,X10,X11) ),
    inference(superposition,[],[f42,f3279])).

fof(f3279,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(forward_demodulation,[],[f3249,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0) ),
    inference(superposition,[],[f31,f29])).

fof(f3249,plain,(
    ! [X0,X1] : k1_enumset1(X0,X1,X0) = k2_enumset1(X0,X0,X0,X1) ),
    inference(superposition,[],[f3203,f37])).

fof(f3203,plain,(
    ! [X4,X5,X3] : k3_enumset1(X3,X4,X4,X3,X5) = k1_enumset1(X3,X5,X4) ),
    inference(superposition,[],[f2699,f1687])).

fof(f2699,plain,(
    ! [X6,X4,X5] : k1_enumset1(X4,X5,X6) = k2_xboole_0(k1_tarski(X4),k1_enumset1(X6,X4,X5)) ),
    inference(superposition,[],[f1748,f1831])).

fof(f1831,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(superposition,[],[f1761,f1687])).

fof(f3148,plain,(
    ! [X12,X10,X8,X7,X11,X9] : k6_enumset1(X7,X7,X7,X8,X9,X10,X11,X12) = k2_xboole_0(k1_enumset1(X9,X7,X8),k1_enumset1(X10,X11,X12)) ),
    inference(superposition,[],[f274,f2715])).

fof(f673,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X3,X4,X5,X0,X0,X1,X2) = k2_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f195,f34])).

fof(f4151,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X1,X1,X2,X3) = k3_enumset1(X3,X1,X2,X0,X0) ),
    inference(superposition,[],[f3334,f39])).

fof(f16753,plain,(
    ! [X26,X24,X23,X25] : k3_enumset1(X26,X25,X25,X23,X24) = k2_enumset1(X24,X23,X25,X26) ),
    inference(forward_demodulation,[],[f16714,f16236])).

fof(f16714,plain,(
    ! [X26,X24,X23,X25] : k3_enumset1(X26,X25,X25,X23,X24) = k3_enumset1(X24,X23,X23,X25,X26) ),
    inference(superposition,[],[f3486,f3430])).

fof(f3486,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X4,X2,X3,X0,X1) = k4_enumset1(X3,X4,X2,X0,X0,X1) ),
    inference(forward_demodulation,[],[f3469,f3334])).

fof(f3469,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X1,X2,X2,X3,X4) = k4_enumset1(X3,X4,X2,X0,X0,X1) ),
    inference(superposition,[],[f3394,f40])).

fof(f3394,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X3,X4,X5) = k4_enumset1(X4,X5,X3,X0,X1,X2) ),
    inference(backward_demodulation,[],[f719,f3376])).

fof(f45170,plain,(
    ! [X134,X132,X133,X131] : k2_enumset1(X131,X132,X133,X134) = k2_enumset1(X133,X134,X132,X131) ),
    inference(superposition,[],[f16754,f16236])).

fof(f16754,plain,(
    ! [X30,X28,X31,X29] : k2_enumset1(X29,X28,X30,X31) = k3_enumset1(X31,X30,X30,X29,X28) ),
    inference(forward_demodulation,[],[f16716,f37])).

fof(f16716,plain,(
    ! [X30,X28,X31,X29] : k3_enumset1(X31,X30,X30,X29,X28) = k3_enumset1(X29,X29,X28,X30,X31) ),
    inference(superposition,[],[f3486,f3431])).

fof(f3431,plain,(
    ! [X6,X8,X7,X5,X9] : k3_enumset1(X9,X7,X8,X5,X6) = k4_enumset1(X6,X5,X5,X7,X8,X9) ),
    inference(forward_demodulation,[],[f3416,f3334])).

fof(f3416,plain,(
    ! [X6,X8,X7,X5,X9] : k4_enumset1(X5,X6,X7,X7,X8,X9) = k4_enumset1(X6,X5,X5,X7,X8,X9) ),
    inference(superposition,[],[f3376,f680])).

fof(f680,plain,(
    ! [X24,X23,X21,X25,X22,X20] : k4_enumset1(X20,X21,X22,X23,X24,X25) = k5_enumset1(X20,X21,X20,X22,X23,X24,X25) ),
    inference(forward_demodulation,[],[f670,f679])).

fof(f670,plain,(
    ! [X24,X23,X21,X25,X22,X20] : k5_enumset1(X20,X21,X20,X22,X23,X24,X25) = k2_xboole_0(k2_tarski(X20,X21),k2_enumset1(X22,X23,X24,X25)) ),
    inference(superposition,[],[f195,f54])).

fof(f49632,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK1,sK2,sK3)) ),
    inference(superposition,[],[f25,f49070])).

fof(f49070,plain,(
    ! [X121,X122,X120,X119] : k2_enumset1(X120,X119,X121,X122) = k2_enumset1(X120,X122,X119,X121) ),
    inference(superposition,[],[f48559,f45169])).

fof(f45169,plain,(
    ! [X127,X130,X128,X129] : k2_enumset1(X130,X129,X128,X127) = k2_enumset1(X129,X130,X128,X127) ),
    inference(superposition,[],[f16754,f16753])).

fof(f48559,plain,(
    ! [X231,X229,X230,X228] : k2_enumset1(X230,X231,X228,X229) = k2_enumset1(X231,X229,X230,X228) ),
    inference(superposition,[],[f17074,f16235])).

fof(f17074,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X3) = k2_enumset1(X2,X3,X0,X1) ),
    inference(forward_demodulation,[],[f17038,f16745])).

fof(f16745,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X1,X0,X2,X3) = k2_enumset1(X3,X2,X0,X1) ),
    inference(backward_demodulation,[],[f16708,f16744])).

fof(f16744,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X5,X6,X6,X7) = k2_enumset1(X7,X6,X4,X5) ),
    inference(forward_demodulation,[],[f16709,f16608])).

fof(f16608,plain,(
    ! [X30,X28,X29,X27] : k2_enumset1(X27,X28,X29,X30) = k3_enumset1(X30,X28,X29,X28,X27) ),
    inference(forward_demodulation,[],[f16580,f16236])).

fof(f16580,plain,(
    ! [X30,X28,X29,X27] : k3_enumset1(X27,X28,X28,X29,X30) = k3_enumset1(X30,X28,X29,X28,X27) ),
    inference(superposition,[],[f3432,f3431])).

fof(f3432,plain,(
    ! [X14,X12,X10,X13,X11] : k4_enumset1(X11,X10,X12,X12,X13,X14) = k3_enumset1(X11,X10,X12,X13,X14) ),
    inference(forward_demodulation,[],[f3417,f39])).

fof(f3417,plain,(
    ! [X14,X12,X10,X13,X11] : k4_enumset1(X11,X10,X12,X12,X13,X14) = k4_enumset1(X11,X11,X10,X12,X13,X14) ),
    inference(superposition,[],[f3376,f681])).

fof(f16709,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X5,X6,X6,X7) = k3_enumset1(X5,X6,X4,X6,X7) ),
    inference(superposition,[],[f3486,f3432])).

fof(f16708,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X1,X0,X2,X3) = k3_enumset1(X0,X1,X2,X2,X3) ),
    inference(superposition,[],[f3486,f39])).

fof(f17038,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X3) = k3_enumset1(X0,X1,X0,X3,X2) ),
    inference(superposition,[],[f3488,f39])).

fof(f3488,plain,(
    ! [X14,X12,X10,X13,X11] : k3_enumset1(X14,X12,X13,X11,X10) = k4_enumset1(X13,X14,X12,X10,X11,X11) ),
    inference(forward_demodulation,[],[f3471,f3334])).

fof(f3471,plain,(
    ! [X14,X12,X10,X13,X11] : k4_enumset1(X11,X10,X12,X12,X13,X14) = k4_enumset1(X13,X14,X12,X10,X11,X11) ),
    inference(superposition,[],[f3394,f681])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (26924)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (26938)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (26931)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (26927)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (26935)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (26937)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (26929)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (26925)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (26928)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (26940)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (26926)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (26932)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.50  % (26934)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.50  % (26934)Refutation not found, incomplete strategy% (26934)------------------------------
% 0.20/0.50  % (26934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (26934)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (26934)Memory used [KB]: 10618
% 0.20/0.50  % (26934)Time elapsed: 0.091 s
% 0.20/0.50  % (26934)------------------------------
% 0.20/0.50  % (26934)------------------------------
% 0.20/0.50  % (26933)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.51  % (26923)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.51  % (26936)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.52  % (26939)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.52  % (26930)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 5.32/1.04  % (26927)Time limit reached!
% 5.32/1.04  % (26927)------------------------------
% 5.32/1.04  % (26927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.32/1.05  % (26927)Termination reason: Time limit
% 5.32/1.05  
% 5.32/1.05  % (26927)Memory used [KB]: 11385
% 5.32/1.05  % (26927)Time elapsed: 0.622 s
% 5.32/1.05  % (26927)------------------------------
% 5.32/1.05  % (26927)------------------------------
% 12.38/1.94  % (26928)Time limit reached!
% 12.38/1.94  % (26928)------------------------------
% 12.38/1.94  % (26928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.38/1.94  % (26928)Termination reason: Time limit
% 12.38/1.94  % (26928)Termination phase: Saturation
% 12.38/1.94  
% 12.38/1.94  % (26928)Memory used [KB]: 35308
% 12.38/1.94  % (26928)Time elapsed: 1.500 s
% 12.38/1.94  % (26928)------------------------------
% 12.38/1.94  % (26928)------------------------------
% 12.38/1.97  % (26929)Time limit reached!
% 12.38/1.97  % (26929)------------------------------
% 12.38/1.97  % (26929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.38/1.97  % (26929)Termination reason: Time limit
% 12.38/1.97  
% 12.38/1.97  % (26929)Memory used [KB]: 24050
% 12.38/1.97  % (26929)Time elapsed: 1.502 s
% 12.38/1.97  % (26929)------------------------------
% 12.38/1.97  % (26929)------------------------------
% 14.89/2.23  % (26925)Time limit reached!
% 14.89/2.23  % (26925)------------------------------
% 14.89/2.23  % (26925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.89/2.24  % (26925)Termination reason: Time limit
% 14.89/2.24  
% 14.89/2.24  % (26925)Memory used [KB]: 25074
% 14.89/2.24  % (26925)Time elapsed: 1.814 s
% 14.89/2.24  % (26925)------------------------------
% 14.89/2.24  % (26925)------------------------------
% 17.83/2.65  % (26935)Time limit reached!
% 17.83/2.65  % (26935)------------------------------
% 17.83/2.65  % (26935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.43/2.66  % (26935)Termination reason: Time limit
% 18.43/2.66  
% 18.43/2.66  % (26935)Memory used [KB]: 23539
% 18.43/2.66  % (26935)Time elapsed: 2.234 s
% 18.43/2.66  % (26935)------------------------------
% 18.43/2.66  % (26935)------------------------------
% 33.25/4.53  % (26926)Refutation found. Thanks to Tanya!
% 33.25/4.53  % SZS status Theorem for theBenchmark
% 33.25/4.53  % SZS output start Proof for theBenchmark
% 33.25/4.53  fof(f50616,plain,(
% 33.25/4.53    $false),
% 33.25/4.53    inference(subsumption_resolution,[],[f50615,f32])).
% 33.25/4.53  fof(f32,plain,(
% 33.25/4.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 33.25/4.53    inference(cnf_transformation,[],[f19])).
% 33.25/4.53  fof(f19,axiom,(
% 33.25/4.53    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 33.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 33.25/4.53  fof(f50615,plain,(
% 33.25/4.53    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(sK3,sK4))),
% 33.25/4.53    inference(forward_demodulation,[],[f50614,f36])).
% 33.25/4.53  fof(f36,plain,(
% 33.25/4.53    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 33.25/4.53    inference(cnf_transformation,[],[f17])).
% 33.25/4.53  fof(f17,axiom,(
% 33.25/4.53    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 33.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 33.25/4.53  fof(f50614,plain,(
% 33.25/4.53    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(sK3,sK4))),
% 33.25/4.53    inference(superposition,[],[f50162,f970])).
% 33.25/4.53  fof(f970,plain,(
% 33.25/4.53    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5))) )),
% 33.25/4.53    inference(forward_demodulation,[],[f958,f33])).
% 33.25/4.53  fof(f33,plain,(
% 33.25/4.53    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 33.25/4.53    inference(cnf_transformation,[],[f18])).
% 33.25/4.53  fof(f18,axiom,(
% 33.25/4.53    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 33.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 33.25/4.53  fof(f958,plain,(
% 33.25/4.53    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5))) )),
% 33.25/4.53    inference(superposition,[],[f155,f33])).
% 33.25/4.53  fof(f155,plain,(
% 33.25/4.53    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 33.25/4.53    inference(forward_demodulation,[],[f149,f33])).
% 33.25/4.53  fof(f149,plain,(
% 33.25/4.53    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 33.25/4.53    inference(superposition,[],[f38,f33])).
% 33.25/4.53  fof(f38,plain,(
% 33.25/4.53    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 33.25/4.53    inference(cnf_transformation,[],[f16])).
% 33.25/4.53  fof(f16,axiom,(
% 33.25/4.53    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 33.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 33.25/4.53  fof(f50162,plain,(
% 33.25/4.53    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK1,sK2,sK4))),
% 33.25/4.53    inference(superposition,[],[f49632,f45757])).
% 33.25/4.53  fof(f45757,plain,(
% 33.25/4.53    ( ! [X127,X130,X128,X129] : (k2_enumset1(X130,X129,X128,X127) = k2_enumset1(X130,X129,X127,X128)) )),
% 33.25/4.53    inference(superposition,[],[f45170,f44473])).
% 33.25/4.53  fof(f44473,plain,(
% 33.25/4.53    ( ! [X127,X130,X128,X129] : (k2_enumset1(X127,X128,X129,X130) = k2_enumset1(X130,X129,X128,X127)) )),
% 33.25/4.53    inference(superposition,[],[f16753,f16236])).
% 33.25/4.53  fof(f16236,plain,(
% 33.25/4.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X1,X2,X3)) )),
% 33.25/4.53    inference(backward_demodulation,[],[f4151,f16235])).
% 33.25/4.53  fof(f16235,plain,(
% 33.25/4.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X3,X1,X2,X0,X0)) )),
% 33.25/4.53    inference(forward_demodulation,[],[f16207,f37])).
% 33.25/4.53  fof(f37,plain,(
% 33.25/4.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 33.25/4.53    inference(cnf_transformation,[],[f11])).
% 33.25/4.53  fof(f11,axiom,(
% 33.25/4.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 33.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 33.25/4.53  fof(f16207,plain,(
% 33.25/4.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X3,X1,X2,X0,X0)) )),
% 33.25/4.53    inference(superposition,[],[f3430,f39])).
% 33.25/4.53  fof(f39,plain,(
% 33.25/4.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 33.25/4.53    inference(cnf_transformation,[],[f12])).
% 33.25/4.53  fof(f12,axiom,(
% 33.25/4.53    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 33.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 33.25/4.53  fof(f3430,plain,(
% 33.25/4.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X4,X2,X3,X0,X1) = k4_enumset1(X0,X1,X0,X2,X3,X4)) )),
% 33.25/4.53    inference(forward_demodulation,[],[f3415,f3334])).
% 33.25/4.53  fof(f3334,plain,(
% 33.25/4.53    ( ! [X14,X12,X10,X13,X11] : (k4_enumset1(X11,X10,X12,X12,X13,X14) = k3_enumset1(X14,X12,X13,X11,X10)) )),
% 33.25/4.53    inference(backward_demodulation,[],[f1599,f3329])).
% 33.25/4.53  fof(f3329,plain,(
% 33.25/4.53    ( ! [X14,X12,X15,X13,X16] : (k5_enumset1(X14,X15,X16,X12,X12,X13,X13) = k3_enumset1(X16,X14,X15,X13,X12)) )),
% 33.25/4.53    inference(backward_demodulation,[],[f3232,f3328])).
% 33.25/4.53  fof(f3328,plain,(
% 33.25/4.53    ( ! [X12,X10,X13,X11,X9] : (k3_enumset1(X9,X10,X11,X12,X13) = k2_xboole_0(k1_enumset1(X11,X9,X10),k2_tarski(X12,X13))) )),
% 33.25/4.53    inference(forward_demodulation,[],[f3293,f1586])).
% 33.25/4.53  fof(f1586,plain,(
% 33.25/4.53    ( ! [X14,X12,X10,X13,X11] : (k3_enumset1(X10,X11,X12,X13,X14) = k5_enumset1(X10,X10,X10,X11,X12,X13,X14)) )),
% 33.25/4.53    inference(backward_demodulation,[],[f1036,f1585])).
% 33.25/4.53  fof(f1585,plain,(
% 33.25/4.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 33.25/4.53    inference(forward_demodulation,[],[f1564,f39])).
% 33.25/4.53  fof(f1564,plain,(
% 33.25/4.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 33.25/4.53    inference(superposition,[],[f679,f26])).
% 33.25/4.53  fof(f26,plain,(
% 33.25/4.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 33.25/4.53    inference(cnf_transformation,[],[f8])).
% 33.25/4.53  fof(f8,axiom,(
% 33.25/4.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 33.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 33.25/4.53  fof(f679,plain,(
% 33.25/4.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))) )),
% 33.25/4.53    inference(forward_demodulation,[],[f667,f40])).
% 33.25/4.53  fof(f40,plain,(
% 33.25/4.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 33.25/4.53    inference(cnf_transformation,[],[f13])).
% 33.25/4.53  fof(f13,axiom,(
% 33.25/4.53    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 33.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 33.25/4.53  fof(f667,plain,(
% 33.25/4.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))) )),
% 33.25/4.53    inference(superposition,[],[f195,f29])).
% 33.25/4.53  fof(f29,plain,(
% 33.25/4.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 33.25/4.53    inference(cnf_transformation,[],[f9])).
% 33.25/4.53  fof(f9,axiom,(
% 33.25/4.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 33.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 33.25/4.53  fof(f195,plain,(
% 33.25/4.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 33.25/4.53    inference(forward_demodulation,[],[f185,f41])).
% 33.25/4.53  fof(f41,plain,(
% 33.25/4.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 33.25/4.53    inference(cnf_transformation,[],[f14])).
% 33.25/4.53  fof(f14,axiom,(
% 33.25/4.53    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 33.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 33.25/4.53  fof(f185,plain,(
% 33.25/4.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 33.25/4.53    inference(superposition,[],[f42,f34])).
% 33.25/4.53  fof(f34,plain,(
% 33.25/4.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 33.25/4.53    inference(cnf_transformation,[],[f10])).
% 33.25/4.53  fof(f10,axiom,(
% 33.25/4.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 33.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 33.25/4.53  fof(f42,plain,(
% 33.25/4.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 33.25/4.53    inference(cnf_transformation,[],[f3])).
% 33.25/4.53  fof(f3,axiom,(
% 33.25/4.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 33.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).
% 33.25/4.53  fof(f1036,plain,(
% 33.25/4.53    ( ! [X14,X12,X10,X13,X11] : (k5_enumset1(X10,X10,X10,X11,X12,X13,X14) = k2_xboole_0(k1_tarski(X10),k2_enumset1(X11,X12,X13,X14))) )),
% 33.25/4.53    inference(forward_demodulation,[],[f1012,f1019])).
% 33.25/4.53  fof(f1019,plain,(
% 33.25/4.53    ( ! [X0] : (k1_tarski(X0) = k3_tarski(k1_tarski(k1_tarski(X0)))) )),
% 33.25/4.53    inference(forward_demodulation,[],[f1006,f26])).
% 33.25/4.53  fof(f1006,plain,(
% 33.25/4.53    ( ! [X0] : (k2_tarski(X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0)))) )),
% 33.25/4.53    inference(superposition,[],[f974,f29])).
% 33.25/4.53  fof(f974,plain,(
% 33.25/4.53    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0)))) )),
% 33.25/4.53    inference(superposition,[],[f952,f34])).
% 33.25/4.53  fof(f952,plain,(
% 33.25/4.53    ( ! [X0] : (k3_tarski(k1_tarski(k1_tarski(X0))) = k2_enumset1(X0,X0,X0,X0)) )),
% 33.25/4.53    inference(superposition,[],[f926,f37])).
% 33.25/4.53  fof(f926,plain,(
% 33.25/4.53    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0)))) )),
% 33.25/4.53    inference(forward_demodulation,[],[f920,f26])).
% 33.25/4.53  fof(f920,plain,(
% 33.25/4.53    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k3_tarski(k1_tarski(k2_tarski(X0,X0)))) )),
% 33.25/4.53    inference(superposition,[],[f895,f39])).
% 33.25/4.53  fof(f895,plain,(
% 33.25/4.53    ( ! [X0,X1] : (k4_enumset1(X0,X1,X0,X0,X0,X1) = k3_tarski(k1_tarski(k2_tarski(X0,X1)))) )),
% 33.25/4.53    inference(forward_demodulation,[],[f887,f29])).
% 33.25/4.53  fof(f887,plain,(
% 33.25/4.53    ( ! [X0,X1] : (k4_enumset1(X0,X1,X0,X0,X0,X1) = k3_tarski(k1_tarski(k1_enumset1(X0,X0,X1)))) )),
% 33.25/4.53    inference(superposition,[],[f866,f40])).
% 33.25/4.53  fof(f866,plain,(
% 33.25/4.53    ( ! [X2,X0,X1] : (k5_enumset1(X0,X1,X2,X0,X0,X1,X2) = k3_tarski(k1_tarski(k1_enumset1(X0,X1,X2)))) )),
% 33.25/4.53    inference(forward_demodulation,[],[f862,f34])).
% 33.25/4.53  fof(f862,plain,(
% 33.25/4.53    ( ! [X2,X0,X1] : (k5_enumset1(X0,X1,X2,X0,X0,X1,X2) = k3_tarski(k1_tarski(k2_enumset1(X0,X0,X1,X2)))) )),
% 33.25/4.53    inference(superposition,[],[f189,f41])).
% 33.25/4.53  fof(f189,plain,(
% 33.25/4.53    ( ! [X10,X8,X11,X9] : (k3_tarski(k1_tarski(k2_enumset1(X8,X9,X10,X11))) = k6_enumset1(X8,X9,X10,X11,X8,X9,X10,X11)) )),
% 33.25/4.53    inference(superposition,[],[f42,f46])).
% 33.25/4.53  fof(f46,plain,(
% 33.25/4.53    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))) )),
% 33.25/4.53    inference(superposition,[],[f28,f26])).
% 33.25/4.53  fof(f28,plain,(
% 33.25/4.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 33.25/4.53    inference(cnf_transformation,[],[f15])).
% 33.25/4.53  fof(f15,axiom,(
% 33.25/4.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 33.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 33.25/4.53  fof(f1012,plain,(
% 33.25/4.53    ( ! [X14,X12,X10,X13,X11] : (k5_enumset1(X10,X10,X10,X11,X12,X13,X14) = k2_xboole_0(k3_tarski(k1_tarski(k1_tarski(X10))),k2_enumset1(X11,X12,X13,X14))) )),
% 33.25/4.53    inference(superposition,[],[f195,f974])).
% 33.25/4.53  fof(f3293,plain,(
% 33.25/4.53    ( ! [X12,X10,X13,X11,X9] : (k5_enumset1(X9,X9,X9,X10,X11,X12,X13) = k2_xboole_0(k1_enumset1(X11,X9,X10),k2_tarski(X12,X13))) )),
% 33.25/4.53    inference(superposition,[],[f808,f2715])).
% 33.25/4.53  fof(f2715,plain,(
% 33.25/4.53    ( ! [X12,X13,X11] : (k1_enumset1(X12,X11,X13) = k3_enumset1(X11,X11,X11,X13,X12)) )),
% 33.25/4.53    inference(superposition,[],[f1748,f1824])).
% 33.25/4.53  fof(f1824,plain,(
% 33.25/4.53    ( ! [X4,X5,X3] : (k1_enumset1(X5,X3,X4) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X5,X3,X4))) )),
% 33.25/4.53    inference(superposition,[],[f1761,f31])).
% 33.25/4.53  fof(f31,plain,(
% 33.25/4.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 33.25/4.53    inference(cnf_transformation,[],[f4])).
% 33.25/4.53  fof(f4,axiom,(
% 33.25/4.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 33.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).
% 33.25/4.53  fof(f1761,plain,(
% 33.25/4.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2))) )),
% 33.25/4.53    inference(forward_demodulation,[],[f1743,f34])).
% 33.25/4.53  fof(f1743,plain,(
% 33.25/4.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2))) )),
% 33.25/4.53    inference(superposition,[],[f1687,f37])).
% 33.25/4.53  fof(f1687,plain,(
% 33.25/4.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X3,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))) )),
% 33.25/4.53    inference(superposition,[],[f1585,f34])).
% 33.25/4.53  fof(f1748,plain,(
% 33.25/4.53    ( ! [X6,X8,X7,X5] : (k3_enumset1(X8,X5,X5,X6,X7) = k2_xboole_0(k1_tarski(X8),k1_enumset1(X7,X5,X6))) )),
% 33.25/4.53    inference(superposition,[],[f1687,f31])).
% 33.25/4.53  fof(f808,plain,(
% 33.25/4.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k2_tarski(X0,X1)) = k5_enumset1(X2,X3,X4,X5,X6,X0,X1)) )),
% 33.25/4.53    inference(forward_demodulation,[],[f797,f769])).
% 33.25/4.53  fof(f769,plain,(
% 33.25/4.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X1,X2,X3,X4,X5,X5,X6)) )),
% 33.25/4.53    inference(forward_demodulation,[],[f767,f41])).
% 33.25/4.53  fof(f767,plain,(
% 33.25/4.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X1,X2,X3,X4,X5,X5,X6)) )),
% 33.25/4.53    inference(superposition,[],[f331,f241])).
% 33.25/4.53  fof(f241,plain,(
% 33.25/4.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 33.25/4.53    inference(forward_demodulation,[],[f234,f42])).
% 33.25/4.53  fof(f234,plain,(
% 33.25/4.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 33.25/4.53    inference(superposition,[],[f43,f37])).
% 33.25/4.53  fof(f43,plain,(
% 33.25/4.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 33.25/4.53    inference(cnf_transformation,[],[f5])).
% 33.25/4.53  fof(f5,axiom,(
% 33.25/4.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 33.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).
% 33.25/4.53  fof(f331,plain,(
% 33.25/4.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X2,X3,X4,X5,X6,X7,X0,X0,X1) = k6_enumset1(X2,X3,X4,X5,X6,X7,X0,X1)) )),
% 33.25/4.53    inference(backward_demodulation,[],[f265,f328])).
% 33.25/4.53  fof(f328,plain,(
% 33.25/4.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 33.25/4.53    inference(forward_demodulation,[],[f316,f241])).
% 33.25/4.53  fof(f316,plain,(
% 33.25/4.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 33.25/4.53    inference(superposition,[],[f45,f40])).
% 33.25/4.53  fof(f45,plain,(
% 33.25/4.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))) )),
% 33.25/4.53    inference(cnf_transformation,[],[f7])).
% 33.25/4.53  fof(f7,axiom,(
% 33.25/4.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 33.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).
% 33.25/4.53  fof(f265,plain,(
% 33.25/4.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X2,X3,X4,X5,X6,X7,X0,X0,X1) = k2_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k2_tarski(X0,X1))) )),
% 33.25/4.53    inference(superposition,[],[f44,f29])).
% 33.25/4.53  fof(f44,plain,(
% 33.25/4.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))) )),
% 33.25/4.53    inference(cnf_transformation,[],[f6])).
% 33.25/4.53  fof(f6,axiom,(
% 33.25/4.53    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 33.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).
% 33.25/4.53  fof(f797,plain,(
% 33.25/4.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X2,X3,X4,X5,X6,X0,X0,X1) = k2_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k2_tarski(X0,X1))) )),
% 33.25/4.53    inference(superposition,[],[f274,f29])).
% 33.25/4.53  fof(f274,plain,(
% 33.25/4.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 33.25/4.53    inference(forward_demodulation,[],[f264,f241])).
% 33.25/4.53  fof(f264,plain,(
% 33.25/4.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 33.25/4.53    inference(superposition,[],[f44,f39])).
% 33.25/4.53  fof(f3232,plain,(
% 33.25/4.53    ( ! [X14,X12,X15,X13,X16] : (k5_enumset1(X14,X15,X16,X12,X12,X13,X13) = k2_xboole_0(k1_enumset1(X15,X16,X14),k2_tarski(X13,X12))) )),
% 33.25/4.53    inference(superposition,[],[f669,f2550])).
% 33.25/4.53  fof(f2550,plain,(
% 33.25/4.53    ( ! [X0,X1] : (k2_tarski(X1,X0) = k2_enumset1(X0,X0,X1,X1)) )),
% 33.25/4.53    inference(forward_demodulation,[],[f2534,f1827])).
% 33.25/4.53  fof(f1827,plain,(
% 33.25/4.53    ( ! [X12,X11] : (k2_tarski(X12,X11) = k2_xboole_0(k1_tarski(X11),k2_tarski(X12,X11))) )),
% 33.25/4.53    inference(superposition,[],[f1761,f56])).
% 33.25/4.53  fof(f56,plain,(
% 33.25/4.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)) )),
% 33.25/4.53    inference(superposition,[],[f31,f29])).
% 33.25/4.53  fof(f2534,plain,(
% 33.25/4.53    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X0)) = k2_enumset1(X0,X0,X1,X1)) )),
% 33.25/4.53    inference(superposition,[],[f1751,f37])).
% 33.25/4.53  fof(f1751,plain,(
% 33.25/4.53    ( ! [X17,X18,X16] : (k3_enumset1(X18,X16,X16,X17,X17) = k2_xboole_0(k1_tarski(X18),k2_tarski(X17,X16))) )),
% 33.25/4.53    inference(superposition,[],[f1687,f56])).
% 33.25/4.53  fof(f669,plain,(
% 33.25/4.53    ( ! [X14,X19,X17,X15,X13,X18,X16] : (k5_enumset1(X13,X14,X15,X16,X17,X18,X19) = k2_xboole_0(k1_enumset1(X14,X15,X13),k2_enumset1(X16,X17,X18,X19))) )),
% 33.25/4.53    inference(superposition,[],[f195,f31])).
% 33.25/4.53  fof(f1599,plain,(
% 33.25/4.53    ( ! [X14,X12,X10,X13,X11] : (k4_enumset1(X11,X10,X12,X12,X13,X14) = k5_enumset1(X12,X13,X14,X10,X10,X11,X11)) )),
% 33.25/4.53    inference(superposition,[],[f719,f681])).
% 33.25/4.53  fof(f681,plain,(
% 33.25/4.53    ( ! [X30,X28,X26,X31,X29,X27] : (k5_enumset1(X26,X27,X27,X28,X29,X30,X31) = k4_enumset1(X27,X26,X28,X29,X30,X31)) )),
% 33.25/4.53    inference(forward_demodulation,[],[f671,f679])).
% 33.25/4.53  fof(f671,plain,(
% 33.25/4.53    ( ! [X30,X28,X26,X31,X29,X27] : (k5_enumset1(X26,X27,X27,X28,X29,X30,X31) = k2_xboole_0(k2_tarski(X27,X26),k2_enumset1(X28,X29,X30,X31))) )),
% 33.25/4.53    inference(superposition,[],[f195,f56])).
% 33.25/4.53  fof(f719,plain,(
% 33.25/4.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X3,X4,X5,X0,X0,X1,X2) = k5_enumset1(X0,X1,X2,X3,X3,X4,X5)) )),
% 33.25/4.53    inference(superposition,[],[f682,f41])).
% 33.25/4.53  fof(f682,plain,(
% 33.25/4.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X3,X4,X5,X6,X0,X0,X1,X2)) )),
% 33.25/4.53    inference(backward_demodulation,[],[f187,f675])).
% 33.25/4.53  fof(f675,plain,(
% 33.25/4.53    ( ! [X12,X10,X8,X7,X13,X11,X9] : (k2_xboole_0(k2_enumset1(X10,X11,X12,X13),k1_enumset1(X7,X8,X9)) = k5_enumset1(X7,X8,X9,X10,X11,X12,X13)) )),
% 33.25/4.53    inference(superposition,[],[f195,f52])).
% 33.25/4.53  fof(f52,plain,(
% 33.25/4.53    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 33.25/4.53    inference(superposition,[],[f47,f28])).
% 33.25/4.53  fof(f47,plain,(
% 33.25/4.53    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 33.25/4.53    inference(superposition,[],[f28,f27])).
% 33.25/4.53  fof(f27,plain,(
% 33.25/4.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 33.25/4.53    inference(cnf_transformation,[],[f2])).
% 33.25/4.53  fof(f2,axiom,(
% 33.25/4.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 33.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 33.25/4.53  fof(f187,plain,(
% 33.25/4.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X3,X4,X5,X6,X0,X0,X1,X2) = k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_enumset1(X0,X1,X2))) )),
% 33.25/4.53    inference(superposition,[],[f42,f34])).
% 33.25/4.53  fof(f3415,plain,(
% 33.25/4.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X1,X2,X2,X3,X4) = k4_enumset1(X0,X1,X0,X2,X3,X4)) )),
% 33.25/4.53    inference(superposition,[],[f3376,f40])).
% 33.25/4.53  fof(f3376,plain,(
% 33.25/4.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X3,X4,X5,X0,X0,X1,X2) = k4_enumset1(X4,X5,X3,X0,X1,X2)) )),
% 33.25/4.53    inference(backward_demodulation,[],[f673,f3374])).
% 33.25/4.53  fof(f3374,plain,(
% 33.25/4.53    ( ! [X12,X10,X8,X7,X11,X9] : (k4_enumset1(X7,X8,X9,X10,X11,X12) = k2_xboole_0(k1_enumset1(X9,X7,X8),k1_enumset1(X10,X11,X12))) )),
% 33.25/4.53    inference(backward_demodulation,[],[f3148,f3373])).
% 33.25/4.53  fof(f3373,plain,(
% 33.25/4.53    ( ! [X6,X10,X8,X7,X11,X9] : (k4_enumset1(X6,X7,X8,X9,X10,X11) = k6_enumset1(X6,X6,X6,X7,X8,X9,X10,X11)) )),
% 33.25/4.53    inference(forward_demodulation,[],[f3363,f679])).
% 33.25/4.53  fof(f3363,plain,(
% 33.25/4.53    ( ! [X6,X10,X8,X7,X11,X9] : (k2_xboole_0(k2_tarski(X6,X7),k2_enumset1(X8,X9,X10,X11)) = k6_enumset1(X6,X6,X6,X7,X8,X9,X10,X11)) )),
% 33.25/4.53    inference(superposition,[],[f42,f3279])).
% 33.25/4.53  fof(f3279,plain,(
% 33.25/4.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 33.25/4.53    inference(forward_demodulation,[],[f3249,f54])).
% 33.25/4.53  fof(f54,plain,(
% 33.25/4.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 33.25/4.53    inference(superposition,[],[f31,f29])).
% 33.25/4.53  fof(f3249,plain,(
% 33.25/4.53    ( ! [X0,X1] : (k1_enumset1(X0,X1,X0) = k2_enumset1(X0,X0,X0,X1)) )),
% 33.25/4.53    inference(superposition,[],[f3203,f37])).
% 33.25/4.53  fof(f3203,plain,(
% 33.25/4.53    ( ! [X4,X5,X3] : (k3_enumset1(X3,X4,X4,X3,X5) = k1_enumset1(X3,X5,X4)) )),
% 33.25/4.53    inference(superposition,[],[f2699,f1687])).
% 33.25/4.53  fof(f2699,plain,(
% 33.25/4.53    ( ! [X6,X4,X5] : (k1_enumset1(X4,X5,X6) = k2_xboole_0(k1_tarski(X4),k1_enumset1(X6,X4,X5))) )),
% 33.25/4.53    inference(superposition,[],[f1748,f1831])).
% 33.25/4.53  fof(f1831,plain,(
% 33.25/4.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 33.25/4.53    inference(superposition,[],[f1761,f1687])).
% 33.25/4.53  fof(f3148,plain,(
% 33.25/4.53    ( ! [X12,X10,X8,X7,X11,X9] : (k6_enumset1(X7,X7,X7,X8,X9,X10,X11,X12) = k2_xboole_0(k1_enumset1(X9,X7,X8),k1_enumset1(X10,X11,X12))) )),
% 33.25/4.53    inference(superposition,[],[f274,f2715])).
% 33.25/4.53  fof(f673,plain,(
% 33.25/4.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X3,X4,X5,X0,X0,X1,X2) = k2_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2))) )),
% 33.25/4.53    inference(superposition,[],[f195,f34])).
% 33.25/4.53  fof(f4151,plain,(
% 33.25/4.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X1,X1,X2,X3) = k3_enumset1(X3,X1,X2,X0,X0)) )),
% 33.25/4.53    inference(superposition,[],[f3334,f39])).
% 33.25/4.53  fof(f16753,plain,(
% 33.25/4.53    ( ! [X26,X24,X23,X25] : (k3_enumset1(X26,X25,X25,X23,X24) = k2_enumset1(X24,X23,X25,X26)) )),
% 33.25/4.53    inference(forward_demodulation,[],[f16714,f16236])).
% 33.25/4.53  fof(f16714,plain,(
% 33.25/4.53    ( ! [X26,X24,X23,X25] : (k3_enumset1(X26,X25,X25,X23,X24) = k3_enumset1(X24,X23,X23,X25,X26)) )),
% 33.25/4.53    inference(superposition,[],[f3486,f3430])).
% 33.25/4.53  fof(f3486,plain,(
% 33.25/4.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X4,X2,X3,X0,X1) = k4_enumset1(X3,X4,X2,X0,X0,X1)) )),
% 33.25/4.53    inference(forward_demodulation,[],[f3469,f3334])).
% 33.25/4.53  fof(f3469,plain,(
% 33.25/4.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X1,X2,X2,X3,X4) = k4_enumset1(X3,X4,X2,X0,X0,X1)) )),
% 33.25/4.53    inference(superposition,[],[f3394,f40])).
% 33.25/4.53  fof(f3394,plain,(
% 33.25/4.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X3,X4,X5) = k4_enumset1(X4,X5,X3,X0,X1,X2)) )),
% 33.25/4.53    inference(backward_demodulation,[],[f719,f3376])).
% 33.25/4.53  fof(f45170,plain,(
% 33.25/4.53    ( ! [X134,X132,X133,X131] : (k2_enumset1(X131,X132,X133,X134) = k2_enumset1(X133,X134,X132,X131)) )),
% 33.25/4.53    inference(superposition,[],[f16754,f16236])).
% 33.25/4.53  fof(f16754,plain,(
% 33.25/4.53    ( ! [X30,X28,X31,X29] : (k2_enumset1(X29,X28,X30,X31) = k3_enumset1(X31,X30,X30,X29,X28)) )),
% 33.25/4.53    inference(forward_demodulation,[],[f16716,f37])).
% 33.25/4.53  fof(f16716,plain,(
% 33.25/4.53    ( ! [X30,X28,X31,X29] : (k3_enumset1(X31,X30,X30,X29,X28) = k3_enumset1(X29,X29,X28,X30,X31)) )),
% 33.25/4.53    inference(superposition,[],[f3486,f3431])).
% 33.25/4.53  fof(f3431,plain,(
% 33.25/4.53    ( ! [X6,X8,X7,X5,X9] : (k3_enumset1(X9,X7,X8,X5,X6) = k4_enumset1(X6,X5,X5,X7,X8,X9)) )),
% 33.25/4.53    inference(forward_demodulation,[],[f3416,f3334])).
% 33.25/4.53  fof(f3416,plain,(
% 33.25/4.53    ( ! [X6,X8,X7,X5,X9] : (k4_enumset1(X5,X6,X7,X7,X8,X9) = k4_enumset1(X6,X5,X5,X7,X8,X9)) )),
% 33.25/4.53    inference(superposition,[],[f3376,f680])).
% 33.25/4.53  fof(f680,plain,(
% 33.25/4.53    ( ! [X24,X23,X21,X25,X22,X20] : (k4_enumset1(X20,X21,X22,X23,X24,X25) = k5_enumset1(X20,X21,X20,X22,X23,X24,X25)) )),
% 33.25/4.53    inference(forward_demodulation,[],[f670,f679])).
% 33.25/4.53  fof(f670,plain,(
% 33.25/4.53    ( ! [X24,X23,X21,X25,X22,X20] : (k5_enumset1(X20,X21,X20,X22,X23,X24,X25) = k2_xboole_0(k2_tarski(X20,X21),k2_enumset1(X22,X23,X24,X25))) )),
% 33.25/4.53    inference(superposition,[],[f195,f54])).
% 33.25/4.53  fof(f49632,plain,(
% 33.25/4.53    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK1,sK2,sK3))),
% 33.25/4.53    inference(superposition,[],[f25,f49070])).
% 33.25/4.53  fof(f49070,plain,(
% 33.25/4.53    ( ! [X121,X122,X120,X119] : (k2_enumset1(X120,X119,X121,X122) = k2_enumset1(X120,X122,X119,X121)) )),
% 33.25/4.53    inference(superposition,[],[f48559,f45169])).
% 33.25/4.53  fof(f45169,plain,(
% 33.25/4.53    ( ! [X127,X130,X128,X129] : (k2_enumset1(X130,X129,X128,X127) = k2_enumset1(X129,X130,X128,X127)) )),
% 33.25/4.53    inference(superposition,[],[f16754,f16753])).
% 33.25/4.53  fof(f48559,plain,(
% 33.25/4.53    ( ! [X231,X229,X230,X228] : (k2_enumset1(X230,X231,X228,X229) = k2_enumset1(X231,X229,X230,X228)) )),
% 33.25/4.53    inference(superposition,[],[f17074,f16235])).
% 33.25/4.53  fof(f17074,plain,(
% 33.25/4.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X3) = k2_enumset1(X2,X3,X0,X1)) )),
% 33.25/4.53    inference(forward_demodulation,[],[f17038,f16745])).
% 33.25/4.53  fof(f16745,plain,(
% 33.25/4.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X1,X0,X2,X3) = k2_enumset1(X3,X2,X0,X1)) )),
% 33.25/4.53    inference(backward_demodulation,[],[f16708,f16744])).
% 33.25/4.53  fof(f16744,plain,(
% 33.25/4.53    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X5,X6,X6,X7) = k2_enumset1(X7,X6,X4,X5)) )),
% 33.25/4.53    inference(forward_demodulation,[],[f16709,f16608])).
% 33.25/4.53  fof(f16608,plain,(
% 33.25/4.53    ( ! [X30,X28,X29,X27] : (k2_enumset1(X27,X28,X29,X30) = k3_enumset1(X30,X28,X29,X28,X27)) )),
% 33.25/4.53    inference(forward_demodulation,[],[f16580,f16236])).
% 33.25/4.53  fof(f16580,plain,(
% 33.25/4.53    ( ! [X30,X28,X29,X27] : (k3_enumset1(X27,X28,X28,X29,X30) = k3_enumset1(X30,X28,X29,X28,X27)) )),
% 33.25/4.53    inference(superposition,[],[f3432,f3431])).
% 33.25/4.53  fof(f3432,plain,(
% 33.25/4.53    ( ! [X14,X12,X10,X13,X11] : (k4_enumset1(X11,X10,X12,X12,X13,X14) = k3_enumset1(X11,X10,X12,X13,X14)) )),
% 33.25/4.53    inference(forward_demodulation,[],[f3417,f39])).
% 33.25/4.53  fof(f3417,plain,(
% 33.25/4.53    ( ! [X14,X12,X10,X13,X11] : (k4_enumset1(X11,X10,X12,X12,X13,X14) = k4_enumset1(X11,X11,X10,X12,X13,X14)) )),
% 33.25/4.53    inference(superposition,[],[f3376,f681])).
% 33.25/4.53  fof(f16709,plain,(
% 33.25/4.53    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X5,X6,X6,X7) = k3_enumset1(X5,X6,X4,X6,X7)) )),
% 33.25/4.53    inference(superposition,[],[f3486,f3432])).
% 33.25/4.53  fof(f16708,plain,(
% 33.25/4.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X1,X0,X2,X3) = k3_enumset1(X0,X1,X2,X2,X3)) )),
% 33.25/4.53    inference(superposition,[],[f3486,f39])).
% 33.25/4.53  fof(f17038,plain,(
% 33.25/4.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X3) = k3_enumset1(X0,X1,X0,X3,X2)) )),
% 33.25/4.53    inference(superposition,[],[f3488,f39])).
% 33.25/4.53  fof(f3488,plain,(
% 33.25/4.53    ( ! [X14,X12,X10,X13,X11] : (k3_enumset1(X14,X12,X13,X11,X10) = k4_enumset1(X13,X14,X12,X10,X11,X11)) )),
% 33.25/4.53    inference(forward_demodulation,[],[f3471,f3334])).
% 33.25/4.53  fof(f3471,plain,(
% 33.25/4.53    ( ! [X14,X12,X10,X13,X11] : (k4_enumset1(X11,X10,X12,X12,X13,X14) = k4_enumset1(X13,X14,X12,X10,X11,X11)) )),
% 33.25/4.53    inference(superposition,[],[f3394,f681])).
% 33.25/4.53  fof(f25,plain,(
% 33.25/4.53    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 33.25/4.53    inference(cnf_transformation,[],[f24])).
% 33.25/4.53  fof(f24,plain,(
% 33.25/4.53    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 33.25/4.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f23])).
% 33.25/4.53  fof(f23,plain,(
% 33.25/4.53    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 33.25/4.53    introduced(choice_axiom,[])).
% 33.25/4.53  fof(f22,plain,(
% 33.25/4.53    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 33.25/4.53    inference(ennf_transformation,[],[f21])).
% 33.25/4.53  fof(f21,negated_conjecture,(
% 33.25/4.53    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 33.25/4.53    inference(negated_conjecture,[],[f20])).
% 33.25/4.53  fof(f20,conjecture,(
% 33.25/4.53    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 33.25/4.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).
% 33.25/4.53  % SZS output end Proof for theBenchmark
% 33.25/4.53  % (26926)------------------------------
% 33.25/4.53  % (26926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 33.25/4.53  % (26926)Termination reason: Refutation
% 33.25/4.53  
% 33.25/4.53  % (26926)Memory used [KB]: 82258
% 33.25/4.53  % (26926)Time elapsed: 4.117 s
% 33.25/4.53  % (26926)------------------------------
% 33.25/4.53  % (26926)------------------------------
% 33.37/4.54  % (26922)Success in time 4.183 s
%------------------------------------------------------------------------------
