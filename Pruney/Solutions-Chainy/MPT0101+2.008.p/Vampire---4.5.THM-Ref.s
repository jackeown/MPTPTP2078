%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:52 EST 2020

% Result     : Theorem 3.83s
% Output     : Refutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   94 (1806 expanded)
%              Number of leaves         :   10 ( 602 expanded)
%              Depth                    :   26
%              Number of atoms          :   95 (1807 expanded)
%              Number of equality atoms :   94 (1806 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14247,plain,(
    $false ),
    inference(subsumption_resolution,[],[f9998,f14240])).

fof(f14240,plain,(
    ! [X37,X38] : k2_xboole_0(X37,X38) = k5_xboole_0(k3_xboole_0(X37,X38),k5_xboole_0(X37,X38)) ),
    inference(backward_demodulation,[],[f12572,f14237])).

fof(f14237,plain,(
    ! [X12,X11] : k2_xboole_0(X11,X12) = k2_xboole_0(X11,k5_xboole_0(X11,X12)) ),
    inference(forward_demodulation,[],[f14143,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f14143,plain,(
    ! [X12,X11] : k2_xboole_0(X11,k4_xboole_0(X12,X11)) = k2_xboole_0(X11,k5_xboole_0(X11,X12)) ),
    inference(superposition,[],[f18,f12942])).

fof(f12942,plain,(
    ! [X52,X53] : k4_xboole_0(X53,X52) = k4_xboole_0(k5_xboole_0(X52,X53),X52) ),
    inference(forward_demodulation,[],[f12872,f387])).

fof(f387,plain,(
    ! [X8,X7] : k4_xboole_0(X8,X7) = k4_xboole_0(k5_xboole_0(X7,X8),k4_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f386,f150])).

fof(f150,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f136,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f136,plain,(
    ! [X17,X18] : k2_xboole_0(k4_xboole_0(X17,X18),X17) = X17 ),
    inference(superposition,[],[f86,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f86,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f50,f16])).

fof(f50,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(X3,k2_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f45,f18])).

fof(f45,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k2_xboole_0(X3,X4)) = k2_xboole_0(X3,k4_xboole_0(X4,X3)) ),
    inference(superposition,[],[f18,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f19,f16])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f386,plain,(
    ! [X8,X7] : k4_xboole_0(k5_xboole_0(X7,X8),k4_xboole_0(X7,X8)) = k4_xboole_0(X8,k2_xboole_0(X7,k4_xboole_0(X7,X8))) ),
    inference(forward_demodulation,[],[f338,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f338,plain,(
    ! [X8,X7] : k4_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(X7,X8)) = k4_xboole_0(k5_xboole_0(X7,X8),k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f26,f21])).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f12872,plain,(
    ! [X52,X53] : k4_xboole_0(k5_xboole_0(X52,X53),X52) = k4_xboole_0(k5_xboole_0(X52,X53),k4_xboole_0(X52,X53)) ),
    inference(superposition,[],[f999,f12558])).

fof(f12558,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k5_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f12452,f962])).

fof(f962,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f23,f961])).

fof(f961,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k3_xboole_0(X6,k4_xboole_0(X6,X7)) ),
    inference(backward_demodulation,[],[f48,f927])).

fof(f927,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k4_xboole_0(k4_xboole_0(X4,X5),k3_xboole_0(X4,X5)) ),
    inference(superposition,[],[f894,f17])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f894,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4 ),
    inference(backward_demodulation,[],[f52,f891])).

fof(f891,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f856,f590])).

fof(f590,plain,(
    ! [X0] : k4_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(backward_demodulation,[],[f390,f585])).

fof(f585,plain,(
    ! [X2] : k3_xboole_0(X2,X2) = X2 ),
    inference(forward_demodulation,[],[f576,f427])).

fof(f427,plain,(
    ! [X2] : k5_xboole_0(k5_xboole_0(X2,X2),X2) = X2 ),
    inference(forward_demodulation,[],[f421,f106])).

fof(f106,plain,(
    ! [X2] : k2_xboole_0(X2,X2) = X2 ),
    inference(forward_demodulation,[],[f102,f99])).

fof(f99,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k3_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f91,f16])).

fof(f91,plain,(
    ! [X10,X11] : k2_xboole_0(k3_xboole_0(X10,X11),X10) = X10 ),
    inference(superposition,[],[f50,f20])).

fof(f102,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k3_xboole_0(X2,X3)) = k2_xboole_0(X2,X2) ),
    inference(superposition,[],[f31,f91])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f29,f18])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f18,f19])).

fof(f421,plain,(
    ! [X2] : k2_xboole_0(X2,X2) = k5_xboole_0(k5_xboole_0(X2,X2),X2) ),
    inference(superposition,[],[f349,f331])).

fof(f331,plain,(
    ! [X2] : k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2) ),
    inference(superposition,[],[f21,f106])).

fof(f349,plain,(
    ! [X10,X11] : k5_xboole_0(k4_xboole_0(X10,X11),X11) = k2_xboole_0(X11,X10) ),
    inference(forward_demodulation,[],[f348,f18])).

fof(f348,plain,(
    ! [X10,X11] : k5_xboole_0(k4_xboole_0(X10,X11),X11) = k2_xboole_0(X11,k4_xboole_0(X10,X11)) ),
    inference(forward_demodulation,[],[f347,f16])).

fof(f347,plain,(
    ! [X10,X11] : k5_xboole_0(k4_xboole_0(X10,X11),X11) = k2_xboole_0(k4_xboole_0(X10,X11),X11) ),
    inference(forward_demodulation,[],[f322,f18])).

fof(f322,plain,(
    ! [X10,X11] : k5_xboole_0(k4_xboole_0(X10,X11),X11) = k2_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X11,k4_xboole_0(X10,X11))) ),
    inference(superposition,[],[f21,f47])).

fof(f47,plain,(
    ! [X4,X5] : k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4) ),
    inference(forward_demodulation,[],[f42,f26])).

fof(f42,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X5,X4),X4) = k4_xboole_0(k2_xboole_0(X4,X5),X4) ),
    inference(superposition,[],[f26,f18])).

fof(f576,plain,(
    ! [X2] : k3_xboole_0(X2,X2) = k5_xboole_0(k5_xboole_0(X2,X2),X2) ),
    inference(superposition,[],[f351,f331])).

fof(f351,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k5_xboole_0(k4_xboole_0(X12,X13),X12) ),
    inference(forward_demodulation,[],[f350,f216])).

fof(f216,plain,(
    ! [X10,X11] : k3_xboole_0(X10,X11) = k2_xboole_0(k4_xboole_0(X10,X10),k3_xboole_0(X10,X11)) ),
    inference(superposition,[],[f136,f103])).

fof(f103,plain,(
    ! [X6,X7] : k4_xboole_0(k3_xboole_0(X6,X7),X6) = k4_xboole_0(X6,X6) ),
    inference(superposition,[],[f19,f91])).

fof(f350,plain,(
    ! [X12,X13] : k2_xboole_0(k4_xboole_0(X12,X12),k3_xboole_0(X12,X13)) = k5_xboole_0(k4_xboole_0(X12,X13),X12) ),
    inference(forward_demodulation,[],[f323,f17])).

fof(f323,plain,(
    ! [X12,X13] : k5_xboole_0(k4_xboole_0(X12,X13),X12) = k2_xboole_0(k4_xboole_0(X12,X12),k4_xboole_0(X12,k4_xboole_0(X12,X13))) ),
    inference(superposition,[],[f21,f154])).

fof(f154,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X4) = k4_xboole_0(k4_xboole_0(X4,X5),X4) ),
    inference(superposition,[],[f19,f136])).

fof(f390,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k4_xboole_0(X0,k5_xboole_0(X0,X0)) ),
    inference(superposition,[],[f17,f331])).

fof(f856,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k5_xboole_0(X0,X0)) ),
    inference(superposition,[],[f17,f810])).

fof(f810,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k5_xboole_0(X5,X5) ),
    inference(backward_demodulation,[],[f94,f803])).

fof(f803,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)) = k5_xboole_0(X2,X2) ),
    inference(backward_demodulation,[],[f282,f761])).

fof(f761,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X3,X2)) = k5_xboole_0(X2,X2) ),
    inference(superposition,[],[f22,f363])).

fof(f363,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X4,X5),X4) = k5_xboole_0(X4,X4) ),
    inference(backward_demodulation,[],[f154,f331])).

fof(f282,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f281,f31])).

fof(f281,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)) = k4_xboole_0(X2,k2_xboole_0(X3,k2_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f267,f22])).

fof(f267,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X2,X3),k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f154,f19])).

fof(f94,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f19,f50])).

fof(f52,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k3_xboole_0(X4,k2_xboole_0(X4,X5)) ),
    inference(backward_demodulation,[],[f28,f51])).

fof(f51,plain,(
    ! [X6,X5] : k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) = k3_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f46,f15])).

fof(f15,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f46,plain,(
    ! [X6,X5] : k3_xboole_0(k2_xboole_0(X5,X6),X5) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) ),
    inference(superposition,[],[f17,f26])).

fof(f28,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) ),
    inference(superposition,[],[f19,f18])).

fof(f48,plain,(
    ! [X6,X7] : k4_xboole_0(k4_xboole_0(X6,X7),k3_xboole_0(X6,X7)) = k3_xboole_0(X6,k4_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f43,f23])).

fof(f43,plain,(
    ! [X6,X7] : k4_xboole_0(k4_xboole_0(X6,X7),k3_xboole_0(X6,X7)) = k4_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(superposition,[],[f26,f20])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f17,f17])).

fof(f12452,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k5_xboole_0(X2,X3)) ),
    inference(superposition,[],[f17,f12350])).

fof(f12350,plain,(
    ! [X12,X13] : k3_xboole_0(X13,X12) = k4_xboole_0(X13,k5_xboole_0(X13,X12)) ),
    inference(forward_demodulation,[],[f12239,f17])).

fof(f12239,plain,(
    ! [X12,X13] : k4_xboole_0(X13,k4_xboole_0(X13,X12)) = k4_xboole_0(X13,k5_xboole_0(X13,X12)) ),
    inference(superposition,[],[f944,f332])).

fof(f332,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X3,X4)) = k5_xboole_0(X3,X4) ),
    inference(superposition,[],[f21,f16])).

fof(f944,plain,(
    ! [X12,X13,X11] : k4_xboole_0(X11,k2_xboole_0(k4_xboole_0(X12,X11),X13)) = k4_xboole_0(X11,X13) ),
    inference(superposition,[],[f22,f894])).

fof(f999,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f962,f15])).

fof(f12572,plain,(
    ! [X37,X38] : k5_xboole_0(k3_xboole_0(X37,X38),k5_xboole_0(X37,X38)) = k2_xboole_0(X37,k5_xboole_0(X37,X38)) ),
    inference(forward_demodulation,[],[f12469,f16])).

fof(f12469,plain,(
    ! [X37,X38] : k2_xboole_0(k5_xboole_0(X37,X38),X37) = k5_xboole_0(k3_xboole_0(X37,X38),k5_xboole_0(X37,X38)) ),
    inference(superposition,[],[f349,f12350])).

fof(f9998,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f14,f9708])).

fof(f9708,plain,(
    ! [X2,X3] : k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2) ),
    inference(superposition,[],[f332,f21])).

fof(f14,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:49:07 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.46  % (12277)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (12282)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (12278)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (12288)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (12280)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (12281)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (12274)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (12285)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (12275)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (12285)Refutation not found, incomplete strategy% (12285)------------------------------
% 0.21/0.48  % (12285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (12285)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (12285)Memory used [KB]: 10490
% 0.21/0.48  % (12285)Time elapsed: 0.071 s
% 0.21/0.48  % (12285)------------------------------
% 0.21/0.48  % (12285)------------------------------
% 0.21/0.48  % (12287)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (12290)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (12283)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (12276)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (12289)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (12279)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (12291)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (12284)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.53  % (12286)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 3.83/0.86  % (12290)Refutation found. Thanks to Tanya!
% 3.83/0.86  % SZS status Theorem for theBenchmark
% 3.83/0.86  % SZS output start Proof for theBenchmark
% 3.83/0.86  fof(f14247,plain,(
% 3.83/0.86    $false),
% 3.83/0.86    inference(subsumption_resolution,[],[f9998,f14240])).
% 3.83/0.86  fof(f14240,plain,(
% 3.83/0.86    ( ! [X37,X38] : (k2_xboole_0(X37,X38) = k5_xboole_0(k3_xboole_0(X37,X38),k5_xboole_0(X37,X38))) )),
% 3.83/0.86    inference(backward_demodulation,[],[f12572,f14237])).
% 3.83/0.86  fof(f14237,plain,(
% 3.83/0.86    ( ! [X12,X11] : (k2_xboole_0(X11,X12) = k2_xboole_0(X11,k5_xboole_0(X11,X12))) )),
% 3.83/0.86    inference(forward_demodulation,[],[f14143,f18])).
% 3.83/0.86  fof(f18,plain,(
% 3.83/0.86    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.83/0.86    inference(cnf_transformation,[],[f4])).
% 3.83/0.86  fof(f4,axiom,(
% 3.83/0.86    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.83/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 3.83/0.86  fof(f14143,plain,(
% 3.83/0.86    ( ! [X12,X11] : (k2_xboole_0(X11,k4_xboole_0(X12,X11)) = k2_xboole_0(X11,k5_xboole_0(X11,X12))) )),
% 3.83/0.86    inference(superposition,[],[f18,f12942])).
% 3.83/0.86  fof(f12942,plain,(
% 3.83/0.86    ( ! [X52,X53] : (k4_xboole_0(X53,X52) = k4_xboole_0(k5_xboole_0(X52,X53),X52)) )),
% 3.83/0.86    inference(forward_demodulation,[],[f12872,f387])).
% 3.83/0.86  fof(f387,plain,(
% 3.83/0.86    ( ! [X8,X7] : (k4_xboole_0(X8,X7) = k4_xboole_0(k5_xboole_0(X7,X8),k4_xboole_0(X7,X8))) )),
% 3.83/0.86    inference(forward_demodulation,[],[f386,f150])).
% 3.83/0.86  fof(f150,plain,(
% 3.83/0.86    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 3.83/0.86    inference(superposition,[],[f136,f16])).
% 3.83/0.86  fof(f16,plain,(
% 3.83/0.86    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.83/0.86    inference(cnf_transformation,[],[f1])).
% 3.83/0.86  fof(f1,axiom,(
% 3.83/0.86    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.83/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.83/0.86  fof(f136,plain,(
% 3.83/0.86    ( ! [X17,X18] : (k2_xboole_0(k4_xboole_0(X17,X18),X17) = X17) )),
% 3.83/0.86    inference(superposition,[],[f86,f20])).
% 3.83/0.86  fof(f20,plain,(
% 3.83/0.86    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 3.83/0.86    inference(cnf_transformation,[],[f8])).
% 3.83/0.86  fof(f8,axiom,(
% 3.83/0.86    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 3.83/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 3.83/0.86  fof(f86,plain,(
% 3.83/0.86    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 3.83/0.86    inference(superposition,[],[f50,f16])).
% 3.83/0.86  fof(f50,plain,(
% 3.83/0.86    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(X3,k2_xboole_0(X3,X4))) )),
% 3.83/0.86    inference(forward_demodulation,[],[f45,f18])).
% 3.83/0.86  fof(f45,plain,(
% 3.83/0.86    ( ! [X4,X3] : (k2_xboole_0(X3,k2_xboole_0(X3,X4)) = k2_xboole_0(X3,k4_xboole_0(X4,X3))) )),
% 3.83/0.86    inference(superposition,[],[f18,f26])).
% 3.83/0.86  fof(f26,plain,(
% 3.83/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 3.83/0.86    inference(superposition,[],[f19,f16])).
% 3.83/0.86  fof(f19,plain,(
% 3.83/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.83/0.86    inference(cnf_transformation,[],[f5])).
% 3.83/0.86  fof(f5,axiom,(
% 3.83/0.86    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.83/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 3.83/0.86  fof(f386,plain,(
% 3.83/0.86    ( ! [X8,X7] : (k4_xboole_0(k5_xboole_0(X7,X8),k4_xboole_0(X7,X8)) = k4_xboole_0(X8,k2_xboole_0(X7,k4_xboole_0(X7,X8)))) )),
% 3.83/0.86    inference(forward_demodulation,[],[f338,f22])).
% 3.83/0.86  fof(f22,plain,(
% 3.83/0.86    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.83/0.86    inference(cnf_transformation,[],[f6])).
% 3.83/0.86  fof(f6,axiom,(
% 3.83/0.86    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.83/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 3.83/0.86  fof(f338,plain,(
% 3.83/0.86    ( ! [X8,X7] : (k4_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(X7,X8)) = k4_xboole_0(k5_xboole_0(X7,X8),k4_xboole_0(X7,X8))) )),
% 3.83/0.86    inference(superposition,[],[f26,f21])).
% 3.83/0.86  fof(f21,plain,(
% 3.83/0.86    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 3.83/0.86    inference(cnf_transformation,[],[f3])).
% 3.83/0.86  fof(f3,axiom,(
% 3.83/0.86    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 3.83/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 3.83/0.86  fof(f12872,plain,(
% 3.83/0.86    ( ! [X52,X53] : (k4_xboole_0(k5_xboole_0(X52,X53),X52) = k4_xboole_0(k5_xboole_0(X52,X53),k4_xboole_0(X52,X53))) )),
% 3.83/0.86    inference(superposition,[],[f999,f12558])).
% 3.83/0.86  fof(f12558,plain,(
% 3.83/0.86    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k5_xboole_0(X2,X3))) )),
% 3.83/0.86    inference(forward_demodulation,[],[f12452,f962])).
% 3.83/0.86  fof(f962,plain,(
% 3.83/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.83/0.86    inference(backward_demodulation,[],[f23,f961])).
% 3.83/0.86  fof(f961,plain,(
% 3.83/0.86    ( ! [X6,X7] : (k4_xboole_0(X6,X7) = k3_xboole_0(X6,k4_xboole_0(X6,X7))) )),
% 3.83/0.86    inference(backward_demodulation,[],[f48,f927])).
% 3.83/0.86  fof(f927,plain,(
% 3.83/0.86    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k4_xboole_0(k4_xboole_0(X4,X5),k3_xboole_0(X4,X5))) )),
% 3.83/0.86    inference(superposition,[],[f894,f17])).
% 3.83/0.86  fof(f17,plain,(
% 3.83/0.86    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.83/0.86    inference(cnf_transformation,[],[f7])).
% 3.83/0.86  fof(f7,axiom,(
% 3.83/0.86    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.83/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.83/0.86  fof(f894,plain,(
% 3.83/0.86    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4) )),
% 3.83/0.86    inference(backward_demodulation,[],[f52,f891])).
% 3.83/0.86  fof(f891,plain,(
% 3.83/0.86    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 3.83/0.86    inference(forward_demodulation,[],[f856,f590])).
% 3.83/0.86  fof(f590,plain,(
% 3.83/0.86    ( ! [X0] : (k4_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 3.83/0.86    inference(backward_demodulation,[],[f390,f585])).
% 3.83/0.86  fof(f585,plain,(
% 3.83/0.86    ( ! [X2] : (k3_xboole_0(X2,X2) = X2) )),
% 3.83/0.86    inference(forward_demodulation,[],[f576,f427])).
% 3.83/0.86  fof(f427,plain,(
% 3.83/0.86    ( ! [X2] : (k5_xboole_0(k5_xboole_0(X2,X2),X2) = X2) )),
% 3.83/0.86    inference(forward_demodulation,[],[f421,f106])).
% 3.83/0.86  fof(f106,plain,(
% 3.83/0.86    ( ! [X2] : (k2_xboole_0(X2,X2) = X2) )),
% 3.83/0.86    inference(forward_demodulation,[],[f102,f99])).
% 3.83/0.86  fof(f99,plain,(
% 3.83/0.86    ( ! [X2,X3] : (k2_xboole_0(X2,k3_xboole_0(X2,X3)) = X2) )),
% 3.83/0.86    inference(superposition,[],[f91,f16])).
% 3.83/0.86  fof(f91,plain,(
% 3.83/0.86    ( ! [X10,X11] : (k2_xboole_0(k3_xboole_0(X10,X11),X10) = X10) )),
% 3.83/0.86    inference(superposition,[],[f50,f20])).
% 3.83/0.86  fof(f102,plain,(
% 3.83/0.86    ( ! [X2,X3] : (k2_xboole_0(X2,k3_xboole_0(X2,X3)) = k2_xboole_0(X2,X2)) )),
% 3.83/0.86    inference(superposition,[],[f31,f91])).
% 3.83/0.86  fof(f31,plain,(
% 3.83/0.86    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) )),
% 3.83/0.86    inference(forward_demodulation,[],[f29,f18])).
% 3.83/0.86  fof(f29,plain,(
% 3.83/0.86    ( ! [X0,X1] : (k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 3.83/0.86    inference(superposition,[],[f18,f19])).
% 3.83/0.86  fof(f421,plain,(
% 3.83/0.86    ( ! [X2] : (k2_xboole_0(X2,X2) = k5_xboole_0(k5_xboole_0(X2,X2),X2)) )),
% 3.83/0.86    inference(superposition,[],[f349,f331])).
% 3.83/0.86  fof(f331,plain,(
% 3.83/0.86    ( ! [X2] : (k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2)) )),
% 3.83/0.86    inference(superposition,[],[f21,f106])).
% 3.83/0.86  fof(f349,plain,(
% 3.83/0.86    ( ! [X10,X11] : (k5_xboole_0(k4_xboole_0(X10,X11),X11) = k2_xboole_0(X11,X10)) )),
% 3.83/0.86    inference(forward_demodulation,[],[f348,f18])).
% 3.83/0.86  fof(f348,plain,(
% 3.83/0.86    ( ! [X10,X11] : (k5_xboole_0(k4_xboole_0(X10,X11),X11) = k2_xboole_0(X11,k4_xboole_0(X10,X11))) )),
% 3.83/0.86    inference(forward_demodulation,[],[f347,f16])).
% 3.83/0.86  fof(f347,plain,(
% 3.83/0.86    ( ! [X10,X11] : (k5_xboole_0(k4_xboole_0(X10,X11),X11) = k2_xboole_0(k4_xboole_0(X10,X11),X11)) )),
% 3.83/0.86    inference(forward_demodulation,[],[f322,f18])).
% 3.83/0.86  fof(f322,plain,(
% 3.83/0.86    ( ! [X10,X11] : (k5_xboole_0(k4_xboole_0(X10,X11),X11) = k2_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X11,k4_xboole_0(X10,X11)))) )),
% 3.83/0.86    inference(superposition,[],[f21,f47])).
% 3.83/0.86  fof(f47,plain,(
% 3.83/0.86    ( ! [X4,X5] : (k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)) )),
% 3.83/0.86    inference(forward_demodulation,[],[f42,f26])).
% 3.83/0.86  fof(f42,plain,(
% 3.83/0.86    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X5,X4),X4) = k4_xboole_0(k2_xboole_0(X4,X5),X4)) )),
% 3.83/0.86    inference(superposition,[],[f26,f18])).
% 3.83/0.86  fof(f576,plain,(
% 3.83/0.86    ( ! [X2] : (k3_xboole_0(X2,X2) = k5_xboole_0(k5_xboole_0(X2,X2),X2)) )),
% 3.83/0.86    inference(superposition,[],[f351,f331])).
% 3.83/0.86  fof(f351,plain,(
% 3.83/0.86    ( ! [X12,X13] : (k3_xboole_0(X12,X13) = k5_xboole_0(k4_xboole_0(X12,X13),X12)) )),
% 3.83/0.86    inference(forward_demodulation,[],[f350,f216])).
% 3.83/0.86  fof(f216,plain,(
% 3.83/0.86    ( ! [X10,X11] : (k3_xboole_0(X10,X11) = k2_xboole_0(k4_xboole_0(X10,X10),k3_xboole_0(X10,X11))) )),
% 3.83/0.86    inference(superposition,[],[f136,f103])).
% 3.83/0.86  fof(f103,plain,(
% 3.83/0.86    ( ! [X6,X7] : (k4_xboole_0(k3_xboole_0(X6,X7),X6) = k4_xboole_0(X6,X6)) )),
% 3.83/0.86    inference(superposition,[],[f19,f91])).
% 3.83/0.86  fof(f350,plain,(
% 3.83/0.86    ( ! [X12,X13] : (k2_xboole_0(k4_xboole_0(X12,X12),k3_xboole_0(X12,X13)) = k5_xboole_0(k4_xboole_0(X12,X13),X12)) )),
% 3.83/0.86    inference(forward_demodulation,[],[f323,f17])).
% 3.83/0.86  fof(f323,plain,(
% 3.83/0.86    ( ! [X12,X13] : (k5_xboole_0(k4_xboole_0(X12,X13),X12) = k2_xboole_0(k4_xboole_0(X12,X12),k4_xboole_0(X12,k4_xboole_0(X12,X13)))) )),
% 3.83/0.86    inference(superposition,[],[f21,f154])).
% 3.83/0.86  fof(f154,plain,(
% 3.83/0.86    ( ! [X4,X5] : (k4_xboole_0(X4,X4) = k4_xboole_0(k4_xboole_0(X4,X5),X4)) )),
% 3.83/0.86    inference(superposition,[],[f19,f136])).
% 3.83/0.86  fof(f390,plain,(
% 3.83/0.86    ( ! [X0] : (k3_xboole_0(X0,X0) = k4_xboole_0(X0,k5_xboole_0(X0,X0))) )),
% 3.83/0.86    inference(superposition,[],[f17,f331])).
% 3.83/0.86  fof(f856,plain,(
% 3.83/0.86    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k5_xboole_0(X0,X0))) )),
% 3.83/0.86    inference(superposition,[],[f17,f810])).
% 3.83/0.86  fof(f810,plain,(
% 3.83/0.86    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k5_xboole_0(X5,X5)) )),
% 3.83/0.86    inference(backward_demodulation,[],[f94,f803])).
% 3.83/0.86  fof(f803,plain,(
% 3.83/0.86    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)) = k5_xboole_0(X2,X2)) )),
% 3.83/0.86    inference(backward_demodulation,[],[f282,f761])).
% 3.83/0.86  fof(f761,plain,(
% 3.83/0.86    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X3,X2)) = k5_xboole_0(X2,X2)) )),
% 3.83/0.86    inference(superposition,[],[f22,f363])).
% 3.83/0.86  fof(f363,plain,(
% 3.83/0.86    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),X4) = k5_xboole_0(X4,X4)) )),
% 3.83/0.86    inference(backward_demodulation,[],[f154,f331])).
% 3.83/0.86  fof(f282,plain,(
% 3.83/0.86    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X2,X3))) )),
% 3.83/0.86    inference(forward_demodulation,[],[f281,f31])).
% 3.83/0.86  fof(f281,plain,(
% 3.83/0.86    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)) = k4_xboole_0(X2,k2_xboole_0(X3,k2_xboole_0(X2,X3)))) )),
% 3.83/0.86    inference(forward_demodulation,[],[f267,f22])).
% 3.83/0.86  fof(f267,plain,(
% 3.83/0.86    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X2,X3),k2_xboole_0(X2,X3))) )),
% 3.83/0.86    inference(superposition,[],[f154,f19])).
% 3.83/0.86  fof(f94,plain,(
% 3.83/0.86    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6))) )),
% 3.83/0.86    inference(superposition,[],[f19,f50])).
% 3.83/0.86  fof(f52,plain,(
% 3.83/0.86    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k3_xboole_0(X4,k2_xboole_0(X4,X5))) )),
% 3.83/0.86    inference(backward_demodulation,[],[f28,f51])).
% 3.83/0.86  fof(f51,plain,(
% 3.83/0.86    ( ! [X6,X5] : (k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) = k3_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 3.83/0.86    inference(forward_demodulation,[],[f46,f15])).
% 3.83/0.86  fof(f15,plain,(
% 3.83/0.86    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.83/0.86    inference(cnf_transformation,[],[f2])).
% 3.83/0.86  fof(f2,axiom,(
% 3.83/0.86    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.83/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.83/0.86  fof(f46,plain,(
% 3.83/0.86    ( ! [X6,X5] : (k3_xboole_0(k2_xboole_0(X5,X6),X5) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5))) )),
% 3.83/0.86    inference(superposition,[],[f17,f26])).
% 3.83/0.86  fof(f28,plain,(
% 3.83/0.86    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4))) )),
% 3.83/0.86    inference(superposition,[],[f19,f18])).
% 3.83/0.86  fof(f48,plain,(
% 3.83/0.86    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),k3_xboole_0(X6,X7)) = k3_xboole_0(X6,k4_xboole_0(X6,X7))) )),
% 3.83/0.86    inference(forward_demodulation,[],[f43,f23])).
% 3.83/0.86  fof(f43,plain,(
% 3.83/0.86    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),k3_xboole_0(X6,X7)) = k4_xboole_0(X6,k3_xboole_0(X6,X7))) )),
% 3.83/0.86    inference(superposition,[],[f26,f20])).
% 3.83/0.86  fof(f23,plain,(
% 3.83/0.86    ( ! [X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.83/0.86    inference(superposition,[],[f17,f17])).
% 3.83/0.86  fof(f12452,plain,(
% 3.83/0.86    ( ! [X2,X3] : (k4_xboole_0(X2,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k5_xboole_0(X2,X3))) )),
% 3.83/0.86    inference(superposition,[],[f17,f12350])).
% 3.83/0.86  fof(f12350,plain,(
% 3.83/0.86    ( ! [X12,X13] : (k3_xboole_0(X13,X12) = k4_xboole_0(X13,k5_xboole_0(X13,X12))) )),
% 3.83/0.86    inference(forward_demodulation,[],[f12239,f17])).
% 3.83/0.86  fof(f12239,plain,(
% 3.83/0.86    ( ! [X12,X13] : (k4_xboole_0(X13,k4_xboole_0(X13,X12)) = k4_xboole_0(X13,k5_xboole_0(X13,X12))) )),
% 3.83/0.86    inference(superposition,[],[f944,f332])).
% 3.83/0.86  fof(f332,plain,(
% 3.83/0.86    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X3,X4)) = k5_xboole_0(X3,X4)) )),
% 3.83/0.86    inference(superposition,[],[f21,f16])).
% 3.83/0.86  fof(f944,plain,(
% 3.83/0.86    ( ! [X12,X13,X11] : (k4_xboole_0(X11,k2_xboole_0(k4_xboole_0(X12,X11),X13)) = k4_xboole_0(X11,X13)) )),
% 3.83/0.86    inference(superposition,[],[f22,f894])).
% 3.83/0.86  fof(f999,plain,(
% 3.83/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 3.83/0.86    inference(superposition,[],[f962,f15])).
% 3.83/0.86  fof(f12572,plain,(
% 3.83/0.86    ( ! [X37,X38] : (k5_xboole_0(k3_xboole_0(X37,X38),k5_xboole_0(X37,X38)) = k2_xboole_0(X37,k5_xboole_0(X37,X38))) )),
% 3.83/0.86    inference(forward_demodulation,[],[f12469,f16])).
% 3.83/0.86  fof(f12469,plain,(
% 3.83/0.86    ( ! [X37,X38] : (k2_xboole_0(k5_xboole_0(X37,X38),X37) = k5_xboole_0(k3_xboole_0(X37,X38),k5_xboole_0(X37,X38))) )),
% 3.83/0.86    inference(superposition,[],[f349,f12350])).
% 3.83/0.86  fof(f9998,plain,(
% 3.83/0.86    k2_xboole_0(sK0,sK1) != k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 3.83/0.86    inference(superposition,[],[f14,f9708])).
% 3.83/0.86  fof(f9708,plain,(
% 3.83/0.86    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2)) )),
% 3.83/0.86    inference(superposition,[],[f332,f21])).
% 3.83/0.86  fof(f14,plain,(
% 3.83/0.86    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 3.83/0.86    inference(cnf_transformation,[],[f13])).
% 3.83/0.86  fof(f13,plain,(
% 3.83/0.86    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 3.83/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 3.83/0.86  fof(f12,plain,(
% 3.83/0.86    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 3.83/0.86    introduced(choice_axiom,[])).
% 3.83/0.86  fof(f11,plain,(
% 3.83/0.86    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.83/0.86    inference(ennf_transformation,[],[f10])).
% 3.83/0.86  fof(f10,negated_conjecture,(
% 3.83/0.86    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.83/0.86    inference(negated_conjecture,[],[f9])).
% 3.83/0.86  fof(f9,conjecture,(
% 3.83/0.86    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.83/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 3.83/0.86  % SZS output end Proof for theBenchmark
% 3.83/0.86  % (12290)------------------------------
% 3.83/0.86  % (12290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.83/0.86  % (12290)Termination reason: Refutation
% 3.83/0.86  
% 3.83/0.86  % (12290)Memory used [KB]: 12025
% 3.83/0.86  % (12290)Time elapsed: 0.447 s
% 3.83/0.86  % (12290)------------------------------
% 3.83/0.86  % (12290)------------------------------
% 3.83/0.86  % (12273)Success in time 0.5 s
%------------------------------------------------------------------------------
