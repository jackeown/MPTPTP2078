%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:20 EST 2020

% Result     : Theorem 3.95s
% Output     : Refutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :   96 (1131 expanded)
%              Number of leaves         :   13 ( 377 expanded)
%              Depth                    :   30
%              Number of atoms          :   97 (1132 expanded)
%              Number of equality atoms :   96 (1131 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13410,plain,(
    $false ),
    inference(subsumption_resolution,[],[f18,f13407])).

fof(f13407,plain,(
    ! [X14,X15] : k5_xboole_0(X14,X15) = k4_xboole_0(k2_xboole_0(X14,X15),k3_xboole_0(X14,X15)) ),
    inference(backward_demodulation,[],[f1692,f13405])).

fof(f13405,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k3_xboole_0(X12,k4_xboole_0(X13,k5_xboole_0(X12,X13))) ),
    inference(forward_demodulation,[],[f13404,f180])).

fof(f180,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f174,f24])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f174,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f149,f81])).

fof(f81,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f70,f20])).

fof(f20,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f70,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f50,f62])).

fof(f62,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f31,f57])).

fof(f57,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f53,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f53,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f25,f46])).

fof(f46,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f24,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f35,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f23,f19])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f22,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f23,f46])).

fof(f149,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f27,f78])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f75,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f51,f59])).

fof(f59,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f57,f21])).

fof(f51,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f25,f19])).

fof(f75,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f24,f73])).

fof(f73,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f71,f19])).

fof(f71,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f25,f67])).

fof(f27,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f13404,plain,(
    ! [X12,X13] : k5_xboole_0(X12,k4_xboole_0(X12,X13)) = k3_xboole_0(X12,k4_xboole_0(X13,k5_xboole_0(X12,X13))) ),
    inference(backward_demodulation,[],[f497,f13254])).

fof(f13254,plain,(
    ! [X12,X11] : k4_xboole_0(X12,X11) = k5_xboole_0(X11,k2_xboole_0(X12,X11)) ),
    inference(superposition,[],[f182,f13109])).

fof(f13109,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(superposition,[],[f13056,f85])).

fof(f85,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f35,f81])).

fof(f13056,plain,(
    ! [X47,X46] : k2_xboole_0(X46,X47) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X47,X46)) ),
    inference(forward_demodulation,[],[f12963,f13041])).

fof(f13041,plain,(
    ! [X15,X16] : k2_xboole_0(X15,X16) = k3_xboole_0(k2_xboole_0(X15,X16),k2_xboole_0(X16,X15)) ),
    inference(forward_demodulation,[],[f12948,f19])).

fof(f12948,plain,(
    ! [X15,X16] : k4_xboole_0(k2_xboole_0(X15,X16),k1_xboole_0) = k3_xboole_0(k2_xboole_0(X15,X16),k2_xboole_0(X16,X15)) ),
    inference(superposition,[],[f25,f12869])).

fof(f12869,plain,(
    ! [X23,X22] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X22,X23),k2_xboole_0(X23,X22)) ),
    inference(forward_demodulation,[],[f12868,f23])).

fof(f12868,plain,(
    ! [X23,X22] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X23,X22)),k2_xboole_0(X23,X22)) ),
    inference(forward_demodulation,[],[f12867,f20])).

fof(f12867,plain,(
    ! [X23,X22] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X23,X22),X22),k2_xboole_0(X23,X22)) ),
    inference(forward_demodulation,[],[f12866,f152])).

fof(f152,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X10)) = k5_xboole_0(k4_xboole_0(X8,X9),X10) ),
    inference(superposition,[],[f27,f24])).

fof(f12866,plain,(
    ! [X23,X22] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X23,k5_xboole_0(k3_xboole_0(X23,X22),X22)),k2_xboole_0(X23,X22)) ),
    inference(forward_demodulation,[],[f12865,f160])).

fof(f160,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f27,f20])).

fof(f12865,plain,(
    ! [X23,X22] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(k3_xboole_0(X23,X22),k5_xboole_0(X22,X23)),k2_xboole_0(X23,X22)) ),
    inference(forward_demodulation,[],[f12683,f20])).

fof(f12683,plain,(
    ! [X23,X22] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(k5_xboole_0(X22,X23),k3_xboole_0(X23,X22)),k2_xboole_0(X23,X22)) ),
    inference(superposition,[],[f826,f123])).

fof(f123,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f26,f20])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f826,plain,(
    ! [X12,X13] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X12,X13),k2_xboole_0(X12,X13)) ),
    inference(superposition,[],[f801,f26])).

fof(f801,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f764,f46])).

fof(f764,plain,(
    ! [X0,X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f28,f67])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f12963,plain,(
    ! [X47,X46] : k2_xboole_0(X46,X47) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k2_xboole_0(X47,X46),k2_xboole_0(X46,X47))) ),
    inference(superposition,[],[f341,f12869])).

fof(f341,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f333,f21])).

fof(f333,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,X6)) = X5 ),
    inference(backward_demodulation,[],[f138,f332])).

fof(f332,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f326,f180])).

fof(f326,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f180,f314])).

fof(f314,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(backward_demodulation,[],[f52,f313])).

fof(f313,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k3_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f297,f24])).

fof(f297,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f180,f25])).

fof(f52,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f25,f25])).

fof(f138,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,k3_xboole_0(X5,X6))) = X5 ),
    inference(forward_demodulation,[],[f125,f22])).

fof(f125,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k3_xboole_0(X5,X6)) = k2_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,k3_xboole_0(X5,X6))) ),
    inference(superposition,[],[f26,f24])).

fof(f182,plain,(
    ! [X12,X11] : k4_xboole_0(X12,X11) = k5_xboole_0(X11,k2_xboole_0(X11,X12)) ),
    inference(superposition,[],[f174,f23])).

fof(f497,plain,(
    ! [X12,X13] : k5_xboole_0(X12,k5_xboole_0(X13,k2_xboole_0(X12,X13))) = k3_xboole_0(X12,k4_xboole_0(X13,k5_xboole_0(X12,X13))) ),
    inference(forward_demodulation,[],[f496,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f496,plain,(
    ! [X12,X13] : k4_xboole_0(k3_xboole_0(X12,X13),k5_xboole_0(X12,X13)) = k5_xboole_0(X12,k5_xboole_0(X13,k2_xboole_0(X12,X13))) ),
    inference(forward_demodulation,[],[f470,f27])).

fof(f470,plain,(
    ! [X12,X13] : k4_xboole_0(k3_xboole_0(X12,X13),k5_xboole_0(X12,X13)) = k5_xboole_0(k5_xboole_0(X12,X13),k2_xboole_0(X12,X13)) ),
    inference(superposition,[],[f182,f26])).

fof(f1692,plain,(
    ! [X14,X15] : k5_xboole_0(X14,X15) = k4_xboole_0(k2_xboole_0(X14,X15),k3_xboole_0(X14,k4_xboole_0(X15,k5_xboole_0(X14,X15)))) ),
    inference(forward_demodulation,[],[f1638,f29])).

fof(f1638,plain,(
    ! [X14,X15] : k5_xboole_0(X14,X15) = k4_xboole_0(k2_xboole_0(X14,X15),k4_xboole_0(k3_xboole_0(X14,X15),k5_xboole_0(X14,X15))) ),
    inference(superposition,[],[f1336,f26])).

fof(f1336,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = X2 ),
    inference(forward_demodulation,[],[f1335,f853])).

fof(f853,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2 ),
    inference(forward_demodulation,[],[f835,f19])).

fof(f835,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f25,f801])).

fof(f1335,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f1307,f21])).

fof(f1307,plain,(
    ! [X2,X3] : k3_xboole_0(k2_xboole_0(X2,X3),X2) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) ),
    inference(superposition,[],[f25,f901])).

fof(f901,plain,(
    ! [X12,X13] : k4_xboole_0(X13,X12) = k4_xboole_0(k2_xboole_0(X12,X13),X12) ),
    inference(forward_demodulation,[],[f900,f182])).

fof(f900,plain,(
    ! [X12,X13] : k4_xboole_0(k2_xboole_0(X12,X13),X12) = k5_xboole_0(X12,k2_xboole_0(X12,X13)) ),
    inference(forward_demodulation,[],[f886,f20])).

fof(f886,plain,(
    ! [X12,X13] : k5_xboole_0(k2_xboole_0(X12,X13),X12) = k4_xboole_0(k2_xboole_0(X12,X13),X12) ),
    inference(superposition,[],[f44,f853])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f24,f21])).

fof(f18,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:33:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (29540)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (29553)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (29542)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (29543)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (29545)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (29541)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (29549)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (29546)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (29551)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (29554)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (29550)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (29538)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (29552)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (29547)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (29550)Refutation not found, incomplete strategy% (29550)------------------------------
% 0.22/0.50  % (29550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (29550)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (29550)Memory used [KB]: 10490
% 0.22/0.50  % (29550)Time elapsed: 0.082 s
% 0.22/0.50  % (29550)------------------------------
% 0.22/0.50  % (29550)------------------------------
% 0.22/0.50  % (29556)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (29539)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.51  % (29548)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.52  % (29555)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 3.95/0.92  % (29555)Refutation found. Thanks to Tanya!
% 3.95/0.92  % SZS status Theorem for theBenchmark
% 3.95/0.92  % SZS output start Proof for theBenchmark
% 3.95/0.92  fof(f13410,plain,(
% 3.95/0.92    $false),
% 3.95/0.92    inference(subsumption_resolution,[],[f18,f13407])).
% 3.95/0.92  fof(f13407,plain,(
% 3.95/0.92    ( ! [X14,X15] : (k5_xboole_0(X14,X15) = k4_xboole_0(k2_xboole_0(X14,X15),k3_xboole_0(X14,X15))) )),
% 3.95/0.92    inference(backward_demodulation,[],[f1692,f13405])).
% 3.95/0.92  fof(f13405,plain,(
% 3.95/0.92    ( ! [X12,X13] : (k3_xboole_0(X12,X13) = k3_xboole_0(X12,k4_xboole_0(X13,k5_xboole_0(X12,X13)))) )),
% 3.95/0.92    inference(forward_demodulation,[],[f13404,f180])).
% 3.95/0.92  fof(f180,plain,(
% 3.95/0.92    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 3.95/0.92    inference(superposition,[],[f174,f24])).
% 3.95/0.92  fof(f24,plain,(
% 3.95/0.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.95/0.92    inference(cnf_transformation,[],[f3])).
% 3.95/0.92  fof(f3,axiom,(
% 3.95/0.92    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.95/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.95/0.92  fof(f174,plain,(
% 3.95/0.92    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 3.95/0.92    inference(forward_demodulation,[],[f149,f81])).
% 3.95/0.92  fof(f81,plain,(
% 3.95/0.92    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 3.95/0.92    inference(superposition,[],[f70,f20])).
% 3.95/0.92  fof(f20,plain,(
% 3.95/0.92    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.95/0.92    inference(cnf_transformation,[],[f2])).
% 3.95/0.92  fof(f2,axiom,(
% 3.95/0.92    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.95/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 3.95/0.92  fof(f70,plain,(
% 3.95/0.92    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.95/0.92    inference(backward_demodulation,[],[f50,f62])).
% 3.95/0.92  fof(f62,plain,(
% 3.95/0.92    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 3.95/0.92    inference(superposition,[],[f31,f57])).
% 3.95/0.92  fof(f57,plain,(
% 3.95/0.92    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3)) )),
% 3.95/0.92    inference(forward_demodulation,[],[f53,f19])).
% 3.95/0.92  fof(f19,plain,(
% 3.95/0.92    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.95/0.92    inference(cnf_transformation,[],[f6])).
% 3.95/0.92  fof(f6,axiom,(
% 3.95/0.92    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.95/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 3.95/0.92  fof(f53,plain,(
% 3.95/0.92    ( ! [X3] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,X3)) )),
% 3.95/0.92    inference(superposition,[],[f25,f46])).
% 3.95/0.92  fof(f46,plain,(
% 3.95/0.92    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6)) )),
% 3.95/0.92    inference(superposition,[],[f24,f36])).
% 3.95/0.92  fof(f36,plain,(
% 3.95/0.92    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 3.95/0.92    inference(superposition,[],[f35,f22])).
% 3.95/0.92  fof(f22,plain,(
% 3.95/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.95/0.92    inference(cnf_transformation,[],[f5])).
% 3.95/0.92  fof(f5,axiom,(
% 3.95/0.92    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.95/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 3.95/0.92  fof(f35,plain,(
% 3.95/0.92    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 3.95/0.92    inference(superposition,[],[f23,f19])).
% 3.95/0.92  fof(f23,plain,(
% 3.95/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.95/0.92    inference(cnf_transformation,[],[f12])).
% 3.95/0.92  fof(f12,axiom,(
% 3.95/0.92    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.95/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 3.95/0.92  fof(f25,plain,(
% 3.95/0.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.95/0.92    inference(cnf_transformation,[],[f8])).
% 3.95/0.92  fof(f8,axiom,(
% 3.95/0.92    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.95/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.95/0.92  fof(f31,plain,(
% 3.95/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0) )),
% 3.95/0.92    inference(superposition,[],[f22,f21])).
% 3.95/0.92  fof(f21,plain,(
% 3.95/0.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.95/0.92    inference(cnf_transformation,[],[f1])).
% 3.95/0.92  fof(f1,axiom,(
% 3.95/0.92    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.95/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.95/0.92  fof(f50,plain,(
% 3.95/0.92    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0)) )),
% 3.95/0.92    inference(superposition,[],[f23,f46])).
% 3.95/0.92  fof(f149,plain,(
% 3.95/0.92    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 3.95/0.92    inference(superposition,[],[f27,f78])).
% 3.95/0.92  fof(f78,plain,(
% 3.95/0.92    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.95/0.92    inference(forward_demodulation,[],[f75,f67])).
% 3.95/0.92  fof(f67,plain,(
% 3.95/0.92    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 3.95/0.92    inference(backward_demodulation,[],[f51,f59])).
% 3.95/0.92  fof(f59,plain,(
% 3.95/0.92    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 3.95/0.92    inference(superposition,[],[f57,f21])).
% 3.95/0.92  fof(f51,plain,(
% 3.95/0.92    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 3.95/0.92    inference(superposition,[],[f25,f19])).
% 3.95/0.92  fof(f75,plain,(
% 3.95/0.92    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 3.95/0.92    inference(superposition,[],[f24,f73])).
% 3.95/0.92  fof(f73,plain,(
% 3.95/0.92    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.95/0.92    inference(forward_demodulation,[],[f71,f19])).
% 3.95/0.92  fof(f71,plain,(
% 3.95/0.92    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 3.95/0.92    inference(superposition,[],[f25,f67])).
% 3.95/0.92  fof(f27,plain,(
% 3.95/0.92    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 3.95/0.92    inference(cnf_transformation,[],[f10])).
% 3.95/0.92  fof(f10,axiom,(
% 3.95/0.92    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 3.95/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 3.95/0.92  fof(f13404,plain,(
% 3.95/0.92    ( ! [X12,X13] : (k5_xboole_0(X12,k4_xboole_0(X12,X13)) = k3_xboole_0(X12,k4_xboole_0(X13,k5_xboole_0(X12,X13)))) )),
% 3.95/0.92    inference(backward_demodulation,[],[f497,f13254])).
% 3.95/0.92  fof(f13254,plain,(
% 3.95/0.92    ( ! [X12,X11] : (k4_xboole_0(X12,X11) = k5_xboole_0(X11,k2_xboole_0(X12,X11))) )),
% 3.95/0.92    inference(superposition,[],[f182,f13109])).
% 3.95/0.92  fof(f13109,plain,(
% 3.95/0.92    ( ! [X4,X5] : (k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4)) )),
% 3.95/0.92    inference(superposition,[],[f13056,f85])).
% 3.95/0.92  fof(f85,plain,(
% 3.95/0.92    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 3.95/0.92    inference(backward_demodulation,[],[f35,f81])).
% 3.95/0.92  fof(f13056,plain,(
% 3.95/0.92    ( ! [X47,X46] : (k2_xboole_0(X46,X47) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X47,X46))) )),
% 3.95/0.92    inference(forward_demodulation,[],[f12963,f13041])).
% 3.95/0.92  fof(f13041,plain,(
% 3.95/0.92    ( ! [X15,X16] : (k2_xboole_0(X15,X16) = k3_xboole_0(k2_xboole_0(X15,X16),k2_xboole_0(X16,X15))) )),
% 3.95/0.92    inference(forward_demodulation,[],[f12948,f19])).
% 3.95/0.92  fof(f12948,plain,(
% 3.95/0.92    ( ! [X15,X16] : (k4_xboole_0(k2_xboole_0(X15,X16),k1_xboole_0) = k3_xboole_0(k2_xboole_0(X15,X16),k2_xboole_0(X16,X15))) )),
% 3.95/0.92    inference(superposition,[],[f25,f12869])).
% 3.95/0.92  fof(f12869,plain,(
% 3.95/0.92    ( ! [X23,X22] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X22,X23),k2_xboole_0(X23,X22))) )),
% 3.95/0.92    inference(forward_demodulation,[],[f12868,f23])).
% 3.95/0.92  fof(f12868,plain,(
% 3.95/0.92    ( ! [X23,X22] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X22,k4_xboole_0(X23,X22)),k2_xboole_0(X23,X22))) )),
% 3.95/0.92    inference(forward_demodulation,[],[f12867,f20])).
% 3.95/0.92  fof(f12867,plain,(
% 3.95/0.92    ( ! [X23,X22] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X23,X22),X22),k2_xboole_0(X23,X22))) )),
% 3.95/0.92    inference(forward_demodulation,[],[f12866,f152])).
% 3.95/0.92  fof(f152,plain,(
% 3.95/0.92    ( ! [X10,X8,X9] : (k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X10)) = k5_xboole_0(k4_xboole_0(X8,X9),X10)) )),
% 3.95/0.92    inference(superposition,[],[f27,f24])).
% 3.95/0.92  fof(f12866,plain,(
% 3.95/0.92    ( ! [X23,X22] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X23,k5_xboole_0(k3_xboole_0(X23,X22),X22)),k2_xboole_0(X23,X22))) )),
% 3.95/0.92    inference(forward_demodulation,[],[f12865,f160])).
% 3.95/0.92  fof(f160,plain,(
% 3.95/0.92    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))) )),
% 3.95/0.92    inference(superposition,[],[f27,f20])).
% 3.95/0.92  fof(f12865,plain,(
% 3.95/0.92    ( ! [X23,X22] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(k3_xboole_0(X23,X22),k5_xboole_0(X22,X23)),k2_xboole_0(X23,X22))) )),
% 3.95/0.92    inference(forward_demodulation,[],[f12683,f20])).
% 3.95/0.92  fof(f12683,plain,(
% 3.95/0.92    ( ! [X23,X22] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(k5_xboole_0(X22,X23),k3_xboole_0(X23,X22)),k2_xboole_0(X23,X22))) )),
% 3.95/0.92    inference(superposition,[],[f826,f123])).
% 3.95/0.92  fof(f123,plain,(
% 3.95/0.92    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X1,X2))) )),
% 3.95/0.92    inference(superposition,[],[f26,f20])).
% 3.95/0.92  fof(f26,plain,(
% 3.95/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 3.95/0.92    inference(cnf_transformation,[],[f11])).
% 3.95/0.92  fof(f11,axiom,(
% 3.95/0.92    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.95/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 3.95/0.92  fof(f826,plain,(
% 3.95/0.92    ( ! [X12,X13] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X12,X13),k2_xboole_0(X12,X13))) )),
% 3.95/0.92    inference(superposition,[],[f801,f26])).
% 3.95/0.92  fof(f801,plain,(
% 3.95/0.92    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.95/0.92    inference(forward_demodulation,[],[f764,f46])).
% 3.95/0.92  fof(f764,plain,(
% 3.95/0.92    ( ! [X0,X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.95/0.92    inference(superposition,[],[f28,f67])).
% 3.95/0.92  fof(f28,plain,(
% 3.95/0.92    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.95/0.92    inference(cnf_transformation,[],[f7])).
% 3.95/0.92  fof(f7,axiom,(
% 3.95/0.92    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.95/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 3.95/0.92  fof(f12963,plain,(
% 3.95/0.92    ( ! [X47,X46] : (k2_xboole_0(X46,X47) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k2_xboole_0(X47,X46),k2_xboole_0(X46,X47)))) )),
% 3.95/0.92    inference(superposition,[],[f341,f12869])).
% 3.95/0.92  fof(f341,plain,(
% 3.95/0.92    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = X0) )),
% 3.95/0.92    inference(superposition,[],[f333,f21])).
% 3.95/0.92  fof(f333,plain,(
% 3.95/0.92    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,X6)) = X5) )),
% 3.95/0.92    inference(backward_demodulation,[],[f138,f332])).
% 3.95/0.92  fof(f332,plain,(
% 3.95/0.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.95/0.92    inference(forward_demodulation,[],[f326,f180])).
% 3.95/0.92  fof(f326,plain,(
% 3.95/0.92    ( ! [X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.95/0.92    inference(superposition,[],[f180,f314])).
% 3.95/0.93  fof(f314,plain,(
% 3.95/0.93    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 3.95/0.93    inference(backward_demodulation,[],[f52,f313])).
% 3.95/0.93  fof(f313,plain,(
% 3.95/0.93    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k3_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 3.95/0.93    inference(forward_demodulation,[],[f297,f24])).
% 3.95/0.93  fof(f297,plain,(
% 3.95/0.93    ( ! [X2,X1] : (k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 3.95/0.93    inference(superposition,[],[f180,f25])).
% 3.95/0.93  fof(f52,plain,(
% 3.95/0.93    ( ! [X2,X1] : (k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 3.95/0.93    inference(superposition,[],[f25,f25])).
% 3.95/0.93  fof(f138,plain,(
% 3.95/0.93    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,k3_xboole_0(X5,X6))) = X5) )),
% 3.95/0.93    inference(forward_demodulation,[],[f125,f22])).
% 3.95/0.93  fof(f125,plain,(
% 3.95/0.93    ( ! [X6,X5] : (k2_xboole_0(X5,k3_xboole_0(X5,X6)) = k2_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,k3_xboole_0(X5,X6)))) )),
% 3.95/0.93    inference(superposition,[],[f26,f24])).
% 3.95/0.93  fof(f182,plain,(
% 3.95/0.93    ( ! [X12,X11] : (k4_xboole_0(X12,X11) = k5_xboole_0(X11,k2_xboole_0(X11,X12))) )),
% 3.95/0.93    inference(superposition,[],[f174,f23])).
% 3.95/0.93  fof(f497,plain,(
% 3.95/0.93    ( ! [X12,X13] : (k5_xboole_0(X12,k5_xboole_0(X13,k2_xboole_0(X12,X13))) = k3_xboole_0(X12,k4_xboole_0(X13,k5_xboole_0(X12,X13)))) )),
% 3.95/0.93    inference(forward_demodulation,[],[f496,f29])).
% 3.95/0.93  fof(f29,plain,(
% 3.95/0.93    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.95/0.93    inference(cnf_transformation,[],[f9])).
% 3.95/0.93  fof(f9,axiom,(
% 3.95/0.93    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.95/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 3.95/0.93  fof(f496,plain,(
% 3.95/0.93    ( ! [X12,X13] : (k4_xboole_0(k3_xboole_0(X12,X13),k5_xboole_0(X12,X13)) = k5_xboole_0(X12,k5_xboole_0(X13,k2_xboole_0(X12,X13)))) )),
% 3.95/0.93    inference(forward_demodulation,[],[f470,f27])).
% 3.95/0.93  fof(f470,plain,(
% 3.95/0.93    ( ! [X12,X13] : (k4_xboole_0(k3_xboole_0(X12,X13),k5_xboole_0(X12,X13)) = k5_xboole_0(k5_xboole_0(X12,X13),k2_xboole_0(X12,X13))) )),
% 3.95/0.93    inference(superposition,[],[f182,f26])).
% 3.95/0.93  fof(f1692,plain,(
% 3.95/0.93    ( ! [X14,X15] : (k5_xboole_0(X14,X15) = k4_xboole_0(k2_xboole_0(X14,X15),k3_xboole_0(X14,k4_xboole_0(X15,k5_xboole_0(X14,X15))))) )),
% 3.95/0.93    inference(forward_demodulation,[],[f1638,f29])).
% 3.95/0.93  fof(f1638,plain,(
% 3.95/0.93    ( ! [X14,X15] : (k5_xboole_0(X14,X15) = k4_xboole_0(k2_xboole_0(X14,X15),k4_xboole_0(k3_xboole_0(X14,X15),k5_xboole_0(X14,X15)))) )),
% 3.95/0.93    inference(superposition,[],[f1336,f26])).
% 3.95/0.93  fof(f1336,plain,(
% 3.95/0.93    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = X2) )),
% 3.95/0.93    inference(forward_demodulation,[],[f1335,f853])).
% 3.95/0.93  fof(f853,plain,(
% 3.95/0.93    ( ! [X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2) )),
% 3.95/0.93    inference(forward_demodulation,[],[f835,f19])).
% 3.95/0.93  fof(f835,plain,(
% 3.95/0.93    ( ! [X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(X2,k1_xboole_0)) )),
% 3.95/0.93    inference(superposition,[],[f25,f801])).
% 3.95/0.93  fof(f1335,plain,(
% 3.95/0.93    ( ! [X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2))) )),
% 3.95/0.93    inference(forward_demodulation,[],[f1307,f21])).
% 3.95/0.93  fof(f1307,plain,(
% 3.95/0.93    ( ! [X2,X3] : (k3_xboole_0(k2_xboole_0(X2,X3),X2) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2))) )),
% 3.95/0.93    inference(superposition,[],[f25,f901])).
% 3.95/0.93  fof(f901,plain,(
% 3.95/0.93    ( ! [X12,X13] : (k4_xboole_0(X13,X12) = k4_xboole_0(k2_xboole_0(X12,X13),X12)) )),
% 3.95/0.93    inference(forward_demodulation,[],[f900,f182])).
% 3.95/0.93  fof(f900,plain,(
% 3.95/0.93    ( ! [X12,X13] : (k4_xboole_0(k2_xboole_0(X12,X13),X12) = k5_xboole_0(X12,k2_xboole_0(X12,X13))) )),
% 3.95/0.93    inference(forward_demodulation,[],[f886,f20])).
% 3.95/0.93  fof(f886,plain,(
% 3.95/0.93    ( ! [X12,X13] : (k5_xboole_0(k2_xboole_0(X12,X13),X12) = k4_xboole_0(k2_xboole_0(X12,X13),X12)) )),
% 3.95/0.93    inference(superposition,[],[f44,f853])).
% 3.95/0.93  fof(f44,plain,(
% 3.95/0.93    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 3.95/0.93    inference(superposition,[],[f24,f21])).
% 3.95/0.93  fof(f18,plain,(
% 3.95/0.93    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 3.95/0.93    inference(cnf_transformation,[],[f17])).
% 3.95/0.93  fof(f17,plain,(
% 3.95/0.93    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 3.95/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 3.95/0.93  fof(f16,plain,(
% 3.95/0.93    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 3.95/0.93    introduced(choice_axiom,[])).
% 3.95/0.93  fof(f15,plain,(
% 3.95/0.93    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.95/0.93    inference(ennf_transformation,[],[f14])).
% 3.95/0.93  fof(f14,negated_conjecture,(
% 3.95/0.93    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.95/0.93    inference(negated_conjecture,[],[f13])).
% 3.95/0.93  fof(f13,conjecture,(
% 3.95/0.93    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.95/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 3.95/0.93  % SZS output end Proof for theBenchmark
% 3.95/0.93  % (29555)------------------------------
% 3.95/0.93  % (29555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.95/0.93  % (29555)Termination reason: Refutation
% 3.95/0.93  
% 3.95/0.93  % (29555)Memory used [KB]: 14072
% 3.95/0.93  % (29555)Time elapsed: 0.512 s
% 3.95/0.93  % (29555)------------------------------
% 3.95/0.93  % (29555)------------------------------
% 3.95/0.93  % (29535)Success in time 0.565 s
%------------------------------------------------------------------------------
