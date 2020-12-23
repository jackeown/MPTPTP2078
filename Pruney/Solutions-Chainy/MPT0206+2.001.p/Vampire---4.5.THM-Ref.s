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
% DateTime   : Thu Dec  3 12:34:39 EST 2020

% Result     : Theorem 4.51s
% Output     : Refutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :  125 (2791 expanded)
%              Number of leaves         :   12 ( 930 expanded)
%              Depth                    :   32
%              Number of atoms          :  126 (2792 expanded)
%              Number of equality atoms :  125 (2791 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7382,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f7365])).

fof(f7365,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) ),
    inference(superposition,[],[f18,f7343])).

fof(f7343,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X6,X7,X8,X0,X1,X2),k1_enumset1(X3,X4,X5)) = k7_enumset1(X6,X7,X8,X0,X1,X2,X3,X4,X5) ),
    inference(backward_demodulation,[],[f124,f7342])).

fof(f7342,plain,(
    ! [X61,X59,X57,X54,X62,X60,X58,X56,X55] : k7_enumset1(X61,X62,X54,X55,X56,X57,X58,X59,X60) = k2_xboole_0(k1_enumset1(X61,X62,X54),k4_enumset1(X55,X56,X57,X58,X59,X60)) ),
    inference(backward_demodulation,[],[f3967,f7341])).

fof(f7341,plain,(
    ! [X158,X156,X163,X161,X159,X157,X155,X162,X160] : k7_enumset1(X155,X156,X157,X158,X159,X160,X161,X162,X163) = k2_xboole_0(k1_enumset1(X155,X155,X156),k2_xboole_0(k1_tarski(X157),k4_enumset1(X158,X159,X160,X161,X162,X163))) ),
    inference(forward_demodulation,[],[f7340,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(superposition,[],[f23,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_enumset1)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).

fof(f7340,plain,(
    ! [X158,X156,X163,X161,X159,X157,X155,X162,X160] : k7_enumset1(X155,X156,X157,X158,X159,X160,X161,X162,X163) = k2_xboole_0(k2_enumset1(X155,X155,X155,X156),k2_xboole_0(k1_tarski(X157),k4_enumset1(X158,X159,X160,X161,X162,X163))) ),
    inference(forward_demodulation,[],[f7339,f1391])).

fof(f1391,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k7_enumset1(X0,X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(backward_demodulation,[],[f95,f1390])).

fof(f1390,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X3,X4,X5),k2_enumset1(X6,X0,X1,X2)) = k2_xboole_0(k1_tarski(X3),k4_enumset1(X4,X5,X6,X0,X1,X2)) ),
    inference(backward_demodulation,[],[f899,f1371])).

fof(f1371,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X6,X0,X1,X2),k1_enumset1(X3,X4,X5)) = k2_xboole_0(k1_tarski(X6),k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(superposition,[],[f781,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

fof(f781,plain,(
    ! [X26,X24,X23,X25,X22] : k2_xboole_0(k1_tarski(X22),k2_xboole_0(k1_enumset1(X23,X24,X25),X26)) = k2_xboole_0(k2_enumset1(X22,X23,X24,X25),X26) ),
    inference(forward_demodulation,[],[f777,f196])).

fof(f196,plain,(
    ! [X80,X83,X81,X84,X82] : k2_xboole_0(k2_enumset1(X80,X81,X82,X83),X84) = k5_xboole_0(k1_tarski(X80),k5_xboole_0(k4_xboole_0(k2_enumset1(X80,X81,X82,X83),k1_tarski(X80)),k4_xboole_0(X84,k2_enumset1(X80,X81,X82,X83)))) ),
    inference(forward_demodulation,[],[f171,f123])).

fof(f123,plain,(
    ! [X6,X4,X8,X7,X5] : k2_xboole_0(k2_enumset1(X4,X5,X6,X7),X8) = k2_xboole_0(k1_tarski(X4),k2_xboole_0(k2_enumset1(X4,X5,X6,X7),X8)) ),
    inference(superposition,[],[f21,f100])).

fof(f100,plain,(
    ! [X6,X4,X5,X3] : k2_enumset1(X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X3),k2_enumset1(X3,X4,X5,X6)) ),
    inference(superposition,[],[f49,f23])).

fof(f49,plain,(
    ! [X6,X4,X8,X7,X5] : k4_enumset1(X8,X4,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X8),k2_enumset1(X4,X5,X6,X7)) ),
    inference(superposition,[],[f26,f43])).

fof(f43,plain,(
    ! [X6,X4,X5,X3] : k2_enumset1(X3,X4,X5,X6) = k3_enumset1(X3,X3,X4,X5,X6) ),
    inference(superposition,[],[f24,f23])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(f21,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f171,plain,(
    ! [X80,X83,X81,X84,X82] : k2_xboole_0(k1_tarski(X80),k2_xboole_0(k2_enumset1(X80,X81,X82,X83),X84)) = k5_xboole_0(k1_tarski(X80),k5_xboole_0(k4_xboole_0(k2_enumset1(X80,X81,X82,X83),k1_tarski(X80)),k4_xboole_0(X84,k2_enumset1(X80,X81,X82,X83)))) ),
    inference(superposition,[],[f70,f100])).

fof(f70,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X2,k2_xboole_0(X0,X1)))) ),
    inference(forward_demodulation,[],[f59,f21])).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X2,k2_xboole_0(X0,X1)))) ),
    inference(superposition,[],[f33,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f33,plain,(
    ! [X4,X5,X3] : k2_xboole_0(k5_xboole_0(X3,X4),X5) = k5_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(X5,k5_xboole_0(X3,X4)))) ),
    inference(superposition,[],[f20,f19])).

fof(f20,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f777,plain,(
    ! [X26,X24,X23,X25,X22] : k2_xboole_0(k1_tarski(X22),k2_xboole_0(k1_enumset1(X23,X24,X25),X26)) = k5_xboole_0(k1_tarski(X22),k5_xboole_0(k4_xboole_0(k2_enumset1(X22,X23,X24,X25),k1_tarski(X22)),k4_xboole_0(X26,k2_enumset1(X22,X23,X24,X25)))) ),
    inference(backward_demodulation,[],[f672,f775])).

fof(f775,plain,(
    ! [X12,X10,X13,X11] : k2_enumset1(X10,X11,X12,X13) = k2_xboole_0(k1_tarski(X10),k1_enumset1(X11,X12,X13)) ),
    inference(forward_demodulation,[],[f766,f774])).

fof(f774,plain,(
    ! [X6,X8,X7,X9] : k2_enumset1(X6,X7,X8,X9) = k3_enumset1(X6,X7,X7,X8,X9) ),
    inference(forward_demodulation,[],[f765,f43])).

fof(f765,plain,(
    ! [X6,X8,X7,X9] : k3_enumset1(X6,X6,X7,X8,X9) = k3_enumset1(X6,X7,X7,X8,X9) ),
    inference(superposition,[],[f704,f24])).

fof(f704,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X2,X3,X4) ),
    inference(backward_demodulation,[],[f680,f703])).

fof(f703,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(backward_demodulation,[],[f677,f702])).

fof(f702,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X2,X3,X4)) ),
    inference(forward_demodulation,[],[f682,f24])).

fof(f682,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X2,X3,X4)) ),
    inference(superposition,[],[f677,f27])).

fof(f677,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X2,X3,X4)) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(forward_demodulation,[],[f676,f40])).

fof(f676,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_enumset1(X2,X3,X4)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X2,X3,X4)) ),
    inference(forward_demodulation,[],[f674,f40])).

fof(f674,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_enumset1(X2,X3,X4)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X2,X2,X3,X4)) ),
    inference(superposition,[],[f95,f91])).

fof(f91,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k7_enumset1(X3,X4,X5,X6,X0,X0,X0,X1,X2) = k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f29,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(superposition,[],[f24,f22])).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l142_enumset1)).

fof(f680,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X1,X2,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(superposition,[],[f677,f27])).

fof(f766,plain,(
    ! [X12,X10,X13,X11] : k3_enumset1(X10,X11,X11,X12,X13) = k2_xboole_0(k1_tarski(X10),k1_enumset1(X11,X12,X13)) ),
    inference(superposition,[],[f704,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X3,X0,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f26,f42])).

fof(f672,plain,(
    ! [X26,X24,X23,X25,X22] : k5_xboole_0(k1_tarski(X22),k5_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(X22),k1_enumset1(X23,X24,X25)),k1_tarski(X22)),k4_xboole_0(X26,k2_xboole_0(k1_tarski(X22),k1_enumset1(X23,X24,X25))))) = k2_xboole_0(k1_tarski(X22),k2_xboole_0(k1_enumset1(X23,X24,X25),X26)) ),
    inference(forward_demodulation,[],[f671,f666])).

fof(f666,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_enumset1(X1,X2,X3),X4)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_enumset1(X1,X2,X3),X4))) ),
    inference(forward_demodulation,[],[f659,f21])).

fof(f659,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_enumset1(X1,X2,X3),X4))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)),X4) ),
    inference(superposition,[],[f264,f534])).

fof(f534,plain,(
    ! [X14,X12,X15,X13] : k2_xboole_0(k1_tarski(X12),k1_enumset1(X13,X14,X15)) = k2_xboole_0(k1_tarski(X12),k2_xboole_0(k1_tarski(X12),k1_enumset1(X13,X14,X15))) ),
    inference(superposition,[],[f129,f48])).

fof(f129,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(superposition,[],[f94,f27])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),X3) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_enumset1(X0,X1,X2),X3)) ),
    inference(superposition,[],[f21,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f48,f22])).

fof(f264,plain,(
    ! [X6,X4,X5,X3] : k2_xboole_0(k2_xboole_0(X3,k2_xboole_0(X4,X5)),X6) = k2_xboole_0(X3,k2_xboole_0(X4,k2_xboole_0(X5,X6))) ),
    inference(forward_demodulation,[],[f236,f182])).

fof(f182,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k5_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X2,k2_xboole_0(X0,X1)),k4_xboole_0(X3,k2_xboole_0(X0,k2_xboole_0(X1,X2))))) ),
    inference(forward_demodulation,[],[f161,f21])).

fof(f161,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k5_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X2,k2_xboole_0(X0,X1)),k4_xboole_0(X3,k2_xboole_0(X0,k2_xboole_0(X1,X2))))) ),
    inference(superposition,[],[f70,f21])).

fof(f236,plain,(
    ! [X6,X4,X5,X3] : k2_xboole_0(k2_xboole_0(X3,k2_xboole_0(X4,X5)),X6) = k5_xboole_0(k2_xboole_0(X3,X4),k5_xboole_0(k4_xboole_0(X5,k2_xboole_0(X3,X4)),k4_xboole_0(X6,k2_xboole_0(X3,k2_xboole_0(X4,X5))))) ),
    inference(superposition,[],[f33,f175])).

fof(f175,plain,(
    ! [X4,X5,X3] : k5_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,k2_xboole_0(X3,X4))) = k2_xboole_0(X3,k2_xboole_0(X4,X5)) ),
    inference(superposition,[],[f70,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),X2)) = k5_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[],[f20,f19])).

fof(f671,plain,(
    ! [X26,X24,X23,X25,X22] : k5_xboole_0(k1_tarski(X22),k5_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(X22),k1_enumset1(X23,X24,X25)),k1_tarski(X22)),k4_xboole_0(X26,k2_xboole_0(k1_tarski(X22),k1_enumset1(X23,X24,X25))))) = k2_xboole_0(k1_tarski(X22),k2_xboole_0(k1_tarski(X22),k2_xboole_0(k1_enumset1(X23,X24,X25),X26))) ),
    inference(forward_demodulation,[],[f663,f21])).

fof(f663,plain,(
    ! [X26,X24,X23,X25,X22] : k2_xboole_0(k1_tarski(X22),k2_xboole_0(k2_xboole_0(k1_tarski(X22),k1_enumset1(X23,X24,X25)),X26)) = k5_xboole_0(k1_tarski(X22),k5_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(X22),k1_enumset1(X23,X24,X25)),k1_tarski(X22)),k4_xboole_0(X26,k2_xboole_0(k1_tarski(X22),k1_enumset1(X23,X24,X25))))) ),
    inference(superposition,[],[f70,f534])).

fof(f899,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_enumset1(X0,X1,X2)) = k2_xboole_0(k1_enumset1(X3,X4,X5),k2_enumset1(X6,X0,X1,X2)) ),
    inference(forward_demodulation,[],[f880,f806])).

fof(f806,plain,(
    ! [X39,X37,X35,X33,X38,X36,X34] : k7_enumset1(X37,X37,X38,X39,X33,X34,X34,X35,X36) = k2_xboole_0(k1_enumset1(X37,X38,X39),k2_enumset1(X33,X34,X35,X36)) ),
    inference(superposition,[],[f90,f774])).

fof(f90,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(superposition,[],[f29,f40])).

fof(f880,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_enumset1(X0,X1,X2)) = k7_enumset1(X3,X3,X4,X5,X6,X0,X0,X1,X2) ),
    inference(superposition,[],[f96,f40])).

fof(f96,plain,(
    ! [X14,X12,X10,X8,X7,X13,X11,X9] : k7_enumset1(X7,X7,X8,X9,X10,X11,X12,X13,X14) = k2_xboole_0(k2_enumset1(X7,X8,X9,X10),k2_enumset1(X11,X12,X13,X14)) ),
    inference(superposition,[],[f30,f43])).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

fof(f95,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k7_enumset1(X0,X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(superposition,[],[f30,f42])).

fof(f7339,plain,(
    ! [X158,X156,X163,X161,X159,X157,X155,X162,X160] : k2_xboole_0(k2_enumset1(X155,X155,X155,X156),k7_enumset1(X157,X157,X157,X158,X159,X160,X161,X162,X163)) = k7_enumset1(X155,X156,X157,X158,X159,X160,X161,X162,X163) ),
    inference(forward_demodulation,[],[f7300,f30])).

fof(f7300,plain,(
    ! [X158,X156,X163,X161,X159,X157,X155,X162,X160] : k2_xboole_0(k2_enumset1(X155,X155,X155,X156),k7_enumset1(X157,X157,X157,X158,X159,X160,X161,X162,X163)) = k2_xboole_0(k3_enumset1(X155,X156,X157,X158,X159),k2_enumset1(X160,X161,X162,X163)) ),
    inference(superposition,[],[f155,f7074])).

fof(f7074,plain,(
    ! [X90,X88,X87,X89,X86] : k3_enumset1(X86,X87,X88,X89,X90) = k7_enumset1(X86,X86,X86,X87,X88,X88,X88,X89,X90) ),
    inference(superposition,[],[f4758,f881])).

fof(f881,plain,(
    ! [X14,X12,X10,X8,X15,X13,X11,X9] : k7_enumset1(X8,X8,X9,X10,X11,X12,X13,X14,X15) = k7_enumset1(X8,X9,X10,X11,X12,X12,X13,X14,X15) ),
    inference(superposition,[],[f96,f92])).

fof(f92,plain,(
    ! [X14,X12,X10,X8,X7,X13,X11,X9] : k7_enumset1(X11,X12,X13,X14,X7,X7,X8,X9,X10) = k2_xboole_0(k2_enumset1(X11,X12,X13,X14),k2_enumset1(X7,X8,X9,X10)) ),
    inference(superposition,[],[f29,f43])).

fof(f4758,plain,(
    ! [X61,X59,X62,X60,X58] : k3_enumset1(X58,X59,X60,X61,X62) = k7_enumset1(X58,X58,X59,X60,X60,X60,X60,X61,X62) ),
    inference(superposition,[],[f4663,f881])).

fof(f4663,plain,(
    ! [X52,X50,X48,X51,X49] : k3_enumset1(X48,X49,X50,X51,X52) = k7_enumset1(X48,X49,X50,X50,X50,X50,X50,X51,X52) ),
    inference(forward_demodulation,[],[f4625,f24])).

fof(f4625,plain,(
    ! [X52,X50,X48,X51,X49] : k7_enumset1(X48,X49,X50,X50,X50,X50,X50,X51,X52) = k4_enumset1(X48,X48,X49,X50,X51,X52) ),
    inference(superposition,[],[f3349,f881])).

fof(f3349,plain,(
    ! [X57,X54,X52,X56,X55,X53] : k4_enumset1(X52,X53,X54,X55,X56,X57) = k7_enumset1(X52,X53,X54,X55,X55,X55,X55,X56,X57) ),
    inference(forward_demodulation,[],[f3299,f129])).

fof(f3299,plain,(
    ! [X57,X54,X52,X56,X55,X53] : k2_xboole_0(k1_tarski(X52),k4_enumset1(X52,X53,X54,X55,X56,X57)) = k7_enumset1(X52,X53,X54,X55,X55,X55,X55,X56,X57) ),
    inference(superposition,[],[f881,f1396])).

fof(f1396,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k7_enumset1(X3,X4,X5,X6,X0,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k4_enumset1(X4,X5,X6,X0,X1,X2)) ),
    inference(backward_demodulation,[],[f900,f1390])).

fof(f900,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k7_enumset1(X3,X4,X5,X6,X0,X0,X0,X1,X2) = k2_xboole_0(k1_enumset1(X3,X4,X5),k2_enumset1(X6,X0,X1,X2)) ),
    inference(backward_demodulation,[],[f91,f899])).

fof(f155,plain,(
    ! [X6,X4,X2,X0,X12,X10,X8,X7,X5,X3,X1,X11,X9] : k2_xboole_0(k7_enumset1(X9,X10,X11,X12,X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k2_xboole_0(k2_enumset1(X9,X10,X11,X12),k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(superposition,[],[f93,f30])).

fof(f93,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : k2_xboole_0(k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8),X9) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k3_enumset1(X4,X5,X6,X7,X8),X9)) ),
    inference(superposition,[],[f21,f29])).

fof(f3967,plain,(
    ! [X61,X59,X57,X54,X62,X60,X58,X56,X55] : k2_xboole_0(k1_enumset1(X61,X61,X62),k2_xboole_0(k1_tarski(X54),k4_enumset1(X55,X56,X57,X58,X59,X60))) = k2_xboole_0(k1_enumset1(X61,X62,X54),k4_enumset1(X55,X56,X57,X58,X59,X60)) ),
    inference(forward_demodulation,[],[f3937,f1925])).

fof(f1925,plain,(
    ! [X30,X28,X26,X24,X31,X29,X27,X25,X32] : k2_xboole_0(k4_enumset1(X30,X31,X32,X24,X25,X26),k2_enumset1(X26,X27,X28,X29)) = k2_xboole_0(k1_enumset1(X30,X31,X32),k4_enumset1(X24,X25,X26,X27,X28,X29)) ),
    inference(superposition,[],[f58,f938])).

fof(f938,plain,(
    ! [X12,X10,X8,X7,X11,X9] : k2_xboole_0(k1_enumset1(X7,X8,X9),k2_enumset1(X9,X10,X11,X12)) = k4_enumset1(X7,X8,X9,X10,X11,X12) ),
    inference(backward_demodulation,[],[f857,f937])).

fof(f937,plain,(
    ! [X14,X12,X17,X15,X13,X16] : k2_xboole_0(k1_enumset1(X12,X12,X13),k2_enumset1(X14,X15,X16,X17)) = k4_enumset1(X12,X13,X14,X15,X16,X17) ),
    inference(forward_demodulation,[],[f936,f897])).

fof(f897,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X3,X4,X5)) ),
    inference(forward_demodulation,[],[f896,f27])).

fof(f896,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X3,X4,X5)) ),
    inference(forward_demodulation,[],[f895,f40])).

fof(f895,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k1_enumset1(X3,X4,X5)) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X3,X4,X5)) ),
    inference(forward_demodulation,[],[f875,f40])).

fof(f875,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k1_enumset1(X3,X4,X5)) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X3,X3,X4,X5)) ),
    inference(superposition,[],[f96,f91])).

fof(f936,plain,(
    ! [X14,X12,X17,X15,X13,X16] : k2_xboole_0(k1_enumset1(X12,X12,X13),k2_enumset1(X14,X15,X16,X17)) = k2_xboole_0(k2_enumset1(X12,X13,X14,X15),k1_enumset1(X15,X16,X17)) ),
    inference(forward_demodulation,[],[f927,f40])).

fof(f927,plain,(
    ! [X14,X12,X17,X15,X13,X16] : k2_xboole_0(k2_enumset1(X12,X13,X14,X15),k2_enumset1(X15,X15,X16,X17)) = k2_xboole_0(k1_enumset1(X12,X12,X13),k2_enumset1(X14,X15,X16,X17)) ),
    inference(superposition,[],[f900,f96])).

fof(f857,plain,(
    ! [X12,X10,X8,X7,X11,X9] : k2_xboole_0(k1_enumset1(X7,X8,X9),k2_enumset1(X9,X10,X11,X12)) = k2_xboole_0(k1_enumset1(X7,X7,X8),k2_enumset1(X9,X10,X11,X12)) ),
    inference(forward_demodulation,[],[f842,f40])).

fof(f842,plain,(
    ! [X12,X10,X8,X7,X11,X9] : k2_xboole_0(k1_enumset1(X7,X8,X9),k2_enumset1(X9,X10,X11,X12)) = k2_xboole_0(k2_enumset1(X7,X7,X7,X8),k2_enumset1(X9,X10,X11,X12)) ),
    inference(superposition,[],[f92,f95])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) ),
    inference(superposition,[],[f21,f27])).

fof(f3937,plain,(
    ! [X61,X59,X57,X54,X62,X60,X58,X56,X55] : k2_xboole_0(k4_enumset1(X61,X62,X54,X55,X56,X57),k2_enumset1(X57,X58,X59,X60)) = k2_xboole_0(k1_enumset1(X61,X61,X62),k2_xboole_0(k1_tarski(X54),k4_enumset1(X55,X56,X57,X58,X59,X60))) ),
    inference(superposition,[],[f1661,f1395])).

fof(f1395,plain,(
    ! [X30,X35,X33,X31,X29,X34,X32] : k2_xboole_0(k2_enumset1(X29,X30,X31,X32),k2_enumset1(X32,X33,X34,X35)) = k2_xboole_0(k1_tarski(X29),k4_enumset1(X30,X31,X32,X33,X34,X35)) ),
    inference(backward_demodulation,[],[f898,f1390])).

fof(f898,plain,(
    ! [X30,X35,X33,X31,X29,X34,X32] : k2_xboole_0(k2_enumset1(X29,X30,X31,X32),k2_enumset1(X32,X33,X34,X35)) = k2_xboole_0(k1_enumset1(X29,X30,X31),k2_enumset1(X32,X33,X34,X35)) ),
    inference(forward_demodulation,[],[f878,f40])).

fof(f878,plain,(
    ! [X30,X35,X33,X31,X29,X34,X32] : k2_xboole_0(k2_enumset1(X29,X29,X30,X31),k2_enumset1(X32,X33,X34,X35)) = k2_xboole_0(k2_enumset1(X29,X30,X31,X32),k2_enumset1(X32,X33,X34,X35)) ),
    inference(superposition,[],[f96,f92])).

fof(f1661,plain,(
    ! [X39,X37,X35,X33,X38,X36,X34] : k2_xboole_0(k4_enumset1(X33,X34,X35,X36,X37,X38),X39) = k2_xboole_0(k1_enumset1(X33,X33,X34),k2_xboole_0(k2_enumset1(X35,X36,X37,X38),X39)) ),
    inference(forward_demodulation,[],[f1660,f40])).

fof(f1660,plain,(
    ! [X39,X37,X35,X33,X38,X36,X34] : k2_xboole_0(k4_enumset1(X33,X34,X35,X36,X37,X38),X39) = k2_xboole_0(k2_enumset1(X33,X33,X33,X34),k2_xboole_0(k2_enumset1(X35,X36,X37,X38),X39)) ),
    inference(forward_demodulation,[],[f1659,f50])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),X6)) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),X6) ),
    inference(superposition,[],[f21,f26])).

fof(f1659,plain,(
    ! [X39,X37,X35,X33,X38,X36,X34] : k2_xboole_0(k2_enumset1(X33,X33,X33,X34),k2_xboole_0(k2_enumset1(X35,X36,X37,X38),X39)) = k2_xboole_0(k1_tarski(X33),k2_xboole_0(k3_enumset1(X34,X35,X36,X37,X38),X39)) ),
    inference(forward_demodulation,[],[f1658,f21])).

fof(f1658,plain,(
    ! [X39,X37,X35,X33,X38,X36,X34] : k2_xboole_0(k2_enumset1(X33,X33,X33,X34),k2_xboole_0(k2_enumset1(X35,X36,X37,X38),X39)) = k2_xboole_0(k2_xboole_0(k1_tarski(X33),k3_enumset1(X34,X35,X36,X37,X38)),X39) ),
    inference(forward_demodulation,[],[f1614,f812])).

fof(f812,plain,(
    ! [X6,X4,X8,X7,X5] : k4_enumset1(X8,X4,X4,X5,X6,X7) = k3_enumset1(X8,X4,X5,X6,X7) ),
    inference(backward_demodulation,[],[f49,f810])).

fof(f810,plain,(
    ! [X6,X10,X8,X7,X9] : k2_xboole_0(k1_tarski(X10),k2_enumset1(X6,X7,X8,X9)) = k3_enumset1(X10,X6,X7,X8,X9) ),
    inference(forward_demodulation,[],[f802,f704])).

fof(f802,plain,(
    ! [X6,X10,X8,X7,X9] : k4_enumset1(X10,X6,X7,X7,X8,X9) = k2_xboole_0(k1_tarski(X10),k2_enumset1(X6,X7,X8,X9)) ),
    inference(superposition,[],[f26,f774])).

fof(f1614,plain,(
    ! [X39,X37,X35,X33,X38,X36,X34] : k2_xboole_0(k2_enumset1(X33,X33,X33,X34),k2_xboole_0(k2_enumset1(X35,X36,X37,X38),X39)) = k2_xboole_0(k2_xboole_0(k1_tarski(X33),k4_enumset1(X34,X35,X35,X36,X37,X38)),X39) ),
    inference(superposition,[],[f154,f1391])).

fof(f154,plain,(
    ! [X14,X12,X10,X8,X15,X13,X11,X9,X16] : k2_xboole_0(k7_enumset1(X12,X13,X14,X15,X8,X8,X9,X10,X11),X16) = k2_xboole_0(k2_enumset1(X12,X13,X14,X15),k2_xboole_0(k2_enumset1(X8,X9,X10,X11),X16)) ),
    inference(superposition,[],[f93,f43])).

fof(f124,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X6,X7,X8,X0,X1,X2),k1_enumset1(X3,X4,X5)) = k2_xboole_0(k1_enumset1(X6,X7,X8),k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(superposition,[],[f58,f27])).

fof(f18,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (31725)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (31718)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (31717)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (31724)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (31724)Refutation not found, incomplete strategy% (31724)------------------------------
% 0.21/0.48  % (31724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31724)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (31724)Memory used [KB]: 10618
% 0.21/0.48  % (31724)Time elapsed: 0.071 s
% 0.21/0.48  % (31724)------------------------------
% 0.21/0.48  % (31724)------------------------------
% 0.21/0.48  % (31723)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (31726)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (31713)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (31730)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (31722)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (31721)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (31719)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (31715)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (31720)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (31728)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (31714)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (31716)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (31727)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (31729)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 4.51/0.95  % (31716)Refutation found. Thanks to Tanya!
% 4.51/0.95  % SZS status Theorem for theBenchmark
% 4.51/0.95  % SZS output start Proof for theBenchmark
% 4.51/0.95  fof(f7382,plain,(
% 4.51/0.95    $false),
% 4.51/0.95    inference(trivial_inequality_removal,[],[f7365])).
% 4.51/0.95  fof(f7365,plain,(
% 4.51/0.95    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),
% 4.51/0.95    inference(superposition,[],[f18,f7343])).
% 4.51/0.95  fof(f7343,plain,(
% 4.51/0.95    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X6,X7,X8,X0,X1,X2),k1_enumset1(X3,X4,X5)) = k7_enumset1(X6,X7,X8,X0,X1,X2,X3,X4,X5)) )),
% 4.51/0.95    inference(backward_demodulation,[],[f124,f7342])).
% 4.51/0.95  fof(f7342,plain,(
% 4.51/0.95    ( ! [X61,X59,X57,X54,X62,X60,X58,X56,X55] : (k7_enumset1(X61,X62,X54,X55,X56,X57,X58,X59,X60) = k2_xboole_0(k1_enumset1(X61,X62,X54),k4_enumset1(X55,X56,X57,X58,X59,X60))) )),
% 4.51/0.95    inference(backward_demodulation,[],[f3967,f7341])).
% 4.51/0.95  fof(f7341,plain,(
% 4.51/0.95    ( ! [X158,X156,X163,X161,X159,X157,X155,X162,X160] : (k7_enumset1(X155,X156,X157,X158,X159,X160,X161,X162,X163) = k2_xboole_0(k1_enumset1(X155,X155,X156),k2_xboole_0(k1_tarski(X157),k4_enumset1(X158,X159,X160,X161,X162,X163)))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f7340,f40])).
% 4.51/0.95  fof(f40,plain,(
% 4.51/0.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.51/0.95    inference(superposition,[],[f23,f22])).
% 4.51/0.95  fof(f22,plain,(
% 4.51/0.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 4.51/0.95    inference(cnf_transformation,[],[f12])).
% 4.51/0.95  fof(f12,axiom,(
% 4.51/0.95    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)),
% 4.51/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_enumset1)).
% 4.51/0.95  fof(f23,plain,(
% 4.51/0.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 4.51/0.95    inference(cnf_transformation,[],[f11])).
% 4.51/0.95  fof(f11,axiom,(
% 4.51/0.95    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)),
% 4.51/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).
% 4.51/0.95  fof(f7340,plain,(
% 4.51/0.95    ( ! [X158,X156,X163,X161,X159,X157,X155,X162,X160] : (k7_enumset1(X155,X156,X157,X158,X159,X160,X161,X162,X163) = k2_xboole_0(k2_enumset1(X155,X155,X155,X156),k2_xboole_0(k1_tarski(X157),k4_enumset1(X158,X159,X160,X161,X162,X163)))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f7339,f1391])).
% 4.51/0.95  fof(f1391,plain,(
% 4.51/0.95    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k7_enumset1(X0,X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 4.51/0.95    inference(backward_demodulation,[],[f95,f1390])).
% 4.51/0.95  fof(f1390,plain,(
% 4.51/0.95    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X3,X4,X5),k2_enumset1(X6,X0,X1,X2)) = k2_xboole_0(k1_tarski(X3),k4_enumset1(X4,X5,X6,X0,X1,X2))) )),
% 4.51/0.95    inference(backward_demodulation,[],[f899,f1371])).
% 4.51/0.95  fof(f1371,plain,(
% 4.51/0.95    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X6,X0,X1,X2),k1_enumset1(X3,X4,X5)) = k2_xboole_0(k1_tarski(X6),k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 4.51/0.95    inference(superposition,[],[f781,f27])).
% 4.51/0.95  fof(f27,plain,(
% 4.51/0.95    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 4.51/0.95    inference(cnf_transformation,[],[f5])).
% 4.51/0.95  fof(f5,axiom,(
% 4.51/0.95    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 4.51/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).
% 4.51/0.95  fof(f781,plain,(
% 4.51/0.95    ( ! [X26,X24,X23,X25,X22] : (k2_xboole_0(k1_tarski(X22),k2_xboole_0(k1_enumset1(X23,X24,X25),X26)) = k2_xboole_0(k2_enumset1(X22,X23,X24,X25),X26)) )),
% 4.51/0.95    inference(forward_demodulation,[],[f777,f196])).
% 4.51/0.95  fof(f196,plain,(
% 4.51/0.95    ( ! [X80,X83,X81,X84,X82] : (k2_xboole_0(k2_enumset1(X80,X81,X82,X83),X84) = k5_xboole_0(k1_tarski(X80),k5_xboole_0(k4_xboole_0(k2_enumset1(X80,X81,X82,X83),k1_tarski(X80)),k4_xboole_0(X84,k2_enumset1(X80,X81,X82,X83))))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f171,f123])).
% 4.51/0.95  fof(f123,plain,(
% 4.51/0.95    ( ! [X6,X4,X8,X7,X5] : (k2_xboole_0(k2_enumset1(X4,X5,X6,X7),X8) = k2_xboole_0(k1_tarski(X4),k2_xboole_0(k2_enumset1(X4,X5,X6,X7),X8))) )),
% 4.51/0.95    inference(superposition,[],[f21,f100])).
% 4.51/0.95  fof(f100,plain,(
% 4.51/0.95    ( ! [X6,X4,X5,X3] : (k2_enumset1(X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X3),k2_enumset1(X3,X4,X5,X6))) )),
% 4.51/0.95    inference(superposition,[],[f49,f23])).
% 4.51/0.95  fof(f49,plain,(
% 4.51/0.95    ( ! [X6,X4,X8,X7,X5] : (k4_enumset1(X8,X4,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X8),k2_enumset1(X4,X5,X6,X7))) )),
% 4.51/0.95    inference(superposition,[],[f26,f43])).
% 4.51/0.95  fof(f43,plain,(
% 4.51/0.95    ( ! [X6,X4,X5,X3] : (k2_enumset1(X3,X4,X5,X6) = k3_enumset1(X3,X3,X4,X5,X6)) )),
% 4.51/0.95    inference(superposition,[],[f24,f23])).
% 4.51/0.95  fof(f24,plain,(
% 4.51/0.95    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 4.51/0.95    inference(cnf_transformation,[],[f9])).
% 4.51/0.95  fof(f9,axiom,(
% 4.51/0.95    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 4.51/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 4.51/0.95  fof(f26,plain,(
% 4.51/0.95    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 4.51/0.95    inference(cnf_transformation,[],[f8])).
% 4.51/0.95  fof(f8,axiom,(
% 4.51/0.95    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 4.51/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).
% 4.51/0.95  fof(f21,plain,(
% 4.51/0.95    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.51/0.95    inference(cnf_transformation,[],[f1])).
% 4.51/0.95  fof(f1,axiom,(
% 4.51/0.95    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.51/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 4.51/0.95  fof(f171,plain,(
% 4.51/0.95    ( ! [X80,X83,X81,X84,X82] : (k2_xboole_0(k1_tarski(X80),k2_xboole_0(k2_enumset1(X80,X81,X82,X83),X84)) = k5_xboole_0(k1_tarski(X80),k5_xboole_0(k4_xboole_0(k2_enumset1(X80,X81,X82,X83),k1_tarski(X80)),k4_xboole_0(X84,k2_enumset1(X80,X81,X82,X83))))) )),
% 4.51/0.95    inference(superposition,[],[f70,f100])).
% 4.51/0.95  fof(f70,plain,(
% 4.51/0.95    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X2,k2_xboole_0(X0,X1))))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f59,f21])).
% 4.51/0.95  fof(f59,plain,(
% 4.51/0.95    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X2,k2_xboole_0(X0,X1))))) )),
% 4.51/0.95    inference(superposition,[],[f33,f19])).
% 4.51/0.95  fof(f19,plain,(
% 4.51/0.95    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.51/0.95    inference(cnf_transformation,[],[f3])).
% 4.51/0.95  fof(f3,axiom,(
% 4.51/0.95    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.51/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 4.51/0.95  fof(f33,plain,(
% 4.51/0.95    ( ! [X4,X5,X3] : (k2_xboole_0(k5_xboole_0(X3,X4),X5) = k5_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(X5,k5_xboole_0(X3,X4))))) )),
% 4.51/0.95    inference(superposition,[],[f20,f19])).
% 4.51/0.95  fof(f20,plain,(
% 4.51/0.95    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 4.51/0.95    inference(cnf_transformation,[],[f2])).
% 4.51/0.95  fof(f2,axiom,(
% 4.51/0.95    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 4.51/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 4.51/0.95  fof(f777,plain,(
% 4.51/0.95    ( ! [X26,X24,X23,X25,X22] : (k2_xboole_0(k1_tarski(X22),k2_xboole_0(k1_enumset1(X23,X24,X25),X26)) = k5_xboole_0(k1_tarski(X22),k5_xboole_0(k4_xboole_0(k2_enumset1(X22,X23,X24,X25),k1_tarski(X22)),k4_xboole_0(X26,k2_enumset1(X22,X23,X24,X25))))) )),
% 4.51/0.95    inference(backward_demodulation,[],[f672,f775])).
% 4.51/0.95  fof(f775,plain,(
% 4.51/0.95    ( ! [X12,X10,X13,X11] : (k2_enumset1(X10,X11,X12,X13) = k2_xboole_0(k1_tarski(X10),k1_enumset1(X11,X12,X13))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f766,f774])).
% 4.51/0.95  fof(f774,plain,(
% 4.51/0.95    ( ! [X6,X8,X7,X9] : (k2_enumset1(X6,X7,X8,X9) = k3_enumset1(X6,X7,X7,X8,X9)) )),
% 4.51/0.95    inference(forward_demodulation,[],[f765,f43])).
% 4.51/0.95  fof(f765,plain,(
% 4.51/0.95    ( ! [X6,X8,X7,X9] : (k3_enumset1(X6,X6,X7,X8,X9) = k3_enumset1(X6,X7,X7,X8,X9)) )),
% 4.51/0.95    inference(superposition,[],[f704,f24])).
% 4.51/0.95  fof(f704,plain,(
% 4.51/0.95    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X2,X3,X4)) )),
% 4.51/0.95    inference(backward_demodulation,[],[f680,f703])).
% 4.51/0.95  fof(f703,plain,(
% 4.51/0.95    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4))) )),
% 4.51/0.95    inference(backward_demodulation,[],[f677,f702])).
% 4.51/0.95  fof(f702,plain,(
% 4.51/0.95    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X2,X3,X4))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f682,f24])).
% 4.51/0.95  fof(f682,plain,(
% 4.51/0.95    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X2,X3,X4))) )),
% 4.51/0.95    inference(superposition,[],[f677,f27])).
% 4.51/0.95  fof(f677,plain,(
% 4.51/0.95    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X2,X3,X4)) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f676,f40])).
% 4.51/0.95  fof(f676,plain,(
% 4.51/0.95    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_enumset1(X2,X3,X4)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X2,X3,X4))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f674,f40])).
% 4.51/0.95  fof(f674,plain,(
% 4.51/0.95    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k1_enumset1(X2,X3,X4)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X2,X2,X3,X4))) )),
% 4.51/0.95    inference(superposition,[],[f95,f91])).
% 4.51/0.95  fof(f91,plain,(
% 4.51/0.95    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k7_enumset1(X3,X4,X5,X6,X0,X0,X0,X1,X2) = k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_enumset1(X0,X1,X2))) )),
% 4.51/0.95    inference(superposition,[],[f29,f42])).
% 4.51/0.95  fof(f42,plain,(
% 4.51/0.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 4.51/0.95    inference(superposition,[],[f24,f22])).
% 4.51/0.95  fof(f29,plain,(
% 4.51/0.95    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))) )),
% 4.51/0.95    inference(cnf_transformation,[],[f4])).
% 4.51/0.95  fof(f4,axiom,(
% 4.51/0.95    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))),
% 4.51/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l142_enumset1)).
% 4.51/0.95  fof(f680,plain,(
% 4.51/0.95    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X1,X2,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4))) )),
% 4.51/0.95    inference(superposition,[],[f677,f27])).
% 4.51/0.95  fof(f766,plain,(
% 4.51/0.95    ( ! [X12,X10,X13,X11] : (k3_enumset1(X10,X11,X11,X12,X13) = k2_xboole_0(k1_tarski(X10),k1_enumset1(X11,X12,X13))) )),
% 4.51/0.95    inference(superposition,[],[f704,f48])).
% 4.51/0.95  fof(f48,plain,(
% 4.51/0.95    ( ! [X2,X0,X3,X1] : (k4_enumset1(X3,X0,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))) )),
% 4.51/0.95    inference(superposition,[],[f26,f42])).
% 4.51/0.95  fof(f672,plain,(
% 4.51/0.95    ( ! [X26,X24,X23,X25,X22] : (k5_xboole_0(k1_tarski(X22),k5_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(X22),k1_enumset1(X23,X24,X25)),k1_tarski(X22)),k4_xboole_0(X26,k2_xboole_0(k1_tarski(X22),k1_enumset1(X23,X24,X25))))) = k2_xboole_0(k1_tarski(X22),k2_xboole_0(k1_enumset1(X23,X24,X25),X26))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f671,f666])).
% 4.51/0.95  fof(f666,plain,(
% 4.51/0.95    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_enumset1(X1,X2,X3),X4)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_enumset1(X1,X2,X3),X4)))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f659,f21])).
% 4.51/0.95  fof(f659,plain,(
% 4.51/0.95    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_enumset1(X1,X2,X3),X4))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)),X4)) )),
% 4.51/0.95    inference(superposition,[],[f264,f534])).
% 4.51/0.95  fof(f534,plain,(
% 4.51/0.95    ( ! [X14,X12,X15,X13] : (k2_xboole_0(k1_tarski(X12),k1_enumset1(X13,X14,X15)) = k2_xboole_0(k1_tarski(X12),k2_xboole_0(k1_tarski(X12),k1_enumset1(X13,X14,X15)))) )),
% 4.51/0.95    inference(superposition,[],[f129,f48])).
% 4.51/0.95  fof(f129,plain,(
% 4.51/0.95    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 4.51/0.95    inference(superposition,[],[f94,f27])).
% 4.51/0.95  fof(f94,plain,(
% 4.51/0.95    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),X3) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_enumset1(X0,X1,X2),X3))) )),
% 4.51/0.95    inference(superposition,[],[f21,f80])).
% 4.51/0.95  fof(f80,plain,(
% 4.51/0.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2))) )),
% 4.51/0.95    inference(superposition,[],[f48,f22])).
% 4.51/0.95  fof(f264,plain,(
% 4.51/0.95    ( ! [X6,X4,X5,X3] : (k2_xboole_0(k2_xboole_0(X3,k2_xboole_0(X4,X5)),X6) = k2_xboole_0(X3,k2_xboole_0(X4,k2_xboole_0(X5,X6)))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f236,f182])).
% 4.51/0.95  fof(f182,plain,(
% 4.51/0.95    ( ! [X2,X0,X3,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k5_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X2,k2_xboole_0(X0,X1)),k4_xboole_0(X3,k2_xboole_0(X0,k2_xboole_0(X1,X2)))))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f161,f21])).
% 4.51/0.95  fof(f161,plain,(
% 4.51/0.95    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k5_xboole_0(k2_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X2,k2_xboole_0(X0,X1)),k4_xboole_0(X3,k2_xboole_0(X0,k2_xboole_0(X1,X2)))))) )),
% 4.51/0.95    inference(superposition,[],[f70,f21])).
% 4.51/0.95  fof(f236,plain,(
% 4.51/0.95    ( ! [X6,X4,X5,X3] : (k2_xboole_0(k2_xboole_0(X3,k2_xboole_0(X4,X5)),X6) = k5_xboole_0(k2_xboole_0(X3,X4),k5_xboole_0(k4_xboole_0(X5,k2_xboole_0(X3,X4)),k4_xboole_0(X6,k2_xboole_0(X3,k2_xboole_0(X4,X5)))))) )),
% 4.51/0.95    inference(superposition,[],[f33,f175])).
% 4.51/0.95  fof(f175,plain,(
% 4.51/0.95    ( ! [X4,X5,X3] : (k5_xboole_0(k2_xboole_0(X3,X4),k4_xboole_0(X5,k2_xboole_0(X3,X4))) = k2_xboole_0(X3,k2_xboole_0(X4,X5))) )),
% 4.51/0.95    inference(superposition,[],[f70,f31])).
% 4.51/0.95  fof(f31,plain,(
% 4.51/0.95    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),X2)) = k5_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 4.51/0.95    inference(superposition,[],[f20,f19])).
% 4.51/0.95  fof(f671,plain,(
% 4.51/0.95    ( ! [X26,X24,X23,X25,X22] : (k5_xboole_0(k1_tarski(X22),k5_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(X22),k1_enumset1(X23,X24,X25)),k1_tarski(X22)),k4_xboole_0(X26,k2_xboole_0(k1_tarski(X22),k1_enumset1(X23,X24,X25))))) = k2_xboole_0(k1_tarski(X22),k2_xboole_0(k1_tarski(X22),k2_xboole_0(k1_enumset1(X23,X24,X25),X26)))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f663,f21])).
% 4.51/0.95  fof(f663,plain,(
% 4.51/0.95    ( ! [X26,X24,X23,X25,X22] : (k2_xboole_0(k1_tarski(X22),k2_xboole_0(k2_xboole_0(k1_tarski(X22),k1_enumset1(X23,X24,X25)),X26)) = k5_xboole_0(k1_tarski(X22),k5_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(X22),k1_enumset1(X23,X24,X25)),k1_tarski(X22)),k4_xboole_0(X26,k2_xboole_0(k1_tarski(X22),k1_enumset1(X23,X24,X25)))))) )),
% 4.51/0.95    inference(superposition,[],[f70,f534])).
% 4.51/0.95  fof(f899,plain,(
% 4.51/0.95    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_enumset1(X0,X1,X2)) = k2_xboole_0(k1_enumset1(X3,X4,X5),k2_enumset1(X6,X0,X1,X2))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f880,f806])).
% 4.51/0.95  fof(f806,plain,(
% 4.51/0.95    ( ! [X39,X37,X35,X33,X38,X36,X34] : (k7_enumset1(X37,X37,X38,X39,X33,X34,X34,X35,X36) = k2_xboole_0(k1_enumset1(X37,X38,X39),k2_enumset1(X33,X34,X35,X36))) )),
% 4.51/0.95    inference(superposition,[],[f90,f774])).
% 4.51/0.95  fof(f90,plain,(
% 4.51/0.95    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7))) )),
% 4.51/0.95    inference(superposition,[],[f29,f40])).
% 4.51/0.95  fof(f880,plain,(
% 4.51/0.95    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_enumset1(X0,X1,X2)) = k7_enumset1(X3,X3,X4,X5,X6,X0,X0,X1,X2)) )),
% 4.51/0.95    inference(superposition,[],[f96,f40])).
% 4.51/0.95  fof(f96,plain,(
% 4.51/0.95    ( ! [X14,X12,X10,X8,X7,X13,X11,X9] : (k7_enumset1(X7,X7,X8,X9,X10,X11,X12,X13,X14) = k2_xboole_0(k2_enumset1(X7,X8,X9,X10),k2_enumset1(X11,X12,X13,X14))) )),
% 4.51/0.95    inference(superposition,[],[f30,f43])).
% 4.51/0.95  fof(f30,plain,(
% 4.51/0.95    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 4.51/0.95    inference(cnf_transformation,[],[f7])).
% 4.51/0.95  fof(f7,axiom,(
% 4.51/0.95    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 4.51/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).
% 4.51/0.95  fof(f95,plain,(
% 4.51/0.95    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k7_enumset1(X0,X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 4.51/0.95    inference(superposition,[],[f30,f42])).
% 4.51/0.95  fof(f7339,plain,(
% 4.51/0.95    ( ! [X158,X156,X163,X161,X159,X157,X155,X162,X160] : (k2_xboole_0(k2_enumset1(X155,X155,X155,X156),k7_enumset1(X157,X157,X157,X158,X159,X160,X161,X162,X163)) = k7_enumset1(X155,X156,X157,X158,X159,X160,X161,X162,X163)) )),
% 4.51/0.95    inference(forward_demodulation,[],[f7300,f30])).
% 4.51/0.95  fof(f7300,plain,(
% 4.51/0.95    ( ! [X158,X156,X163,X161,X159,X157,X155,X162,X160] : (k2_xboole_0(k2_enumset1(X155,X155,X155,X156),k7_enumset1(X157,X157,X157,X158,X159,X160,X161,X162,X163)) = k2_xboole_0(k3_enumset1(X155,X156,X157,X158,X159),k2_enumset1(X160,X161,X162,X163))) )),
% 4.51/0.95    inference(superposition,[],[f155,f7074])).
% 4.51/0.95  fof(f7074,plain,(
% 4.51/0.95    ( ! [X90,X88,X87,X89,X86] : (k3_enumset1(X86,X87,X88,X89,X90) = k7_enumset1(X86,X86,X86,X87,X88,X88,X88,X89,X90)) )),
% 4.51/0.95    inference(superposition,[],[f4758,f881])).
% 4.51/0.95  fof(f881,plain,(
% 4.51/0.95    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] : (k7_enumset1(X8,X8,X9,X10,X11,X12,X13,X14,X15) = k7_enumset1(X8,X9,X10,X11,X12,X12,X13,X14,X15)) )),
% 4.51/0.95    inference(superposition,[],[f96,f92])).
% 4.51/0.95  fof(f92,plain,(
% 4.51/0.95    ( ! [X14,X12,X10,X8,X7,X13,X11,X9] : (k7_enumset1(X11,X12,X13,X14,X7,X7,X8,X9,X10) = k2_xboole_0(k2_enumset1(X11,X12,X13,X14),k2_enumset1(X7,X8,X9,X10))) )),
% 4.51/0.95    inference(superposition,[],[f29,f43])).
% 4.51/0.95  fof(f4758,plain,(
% 4.51/0.95    ( ! [X61,X59,X62,X60,X58] : (k3_enumset1(X58,X59,X60,X61,X62) = k7_enumset1(X58,X58,X59,X60,X60,X60,X60,X61,X62)) )),
% 4.51/0.95    inference(superposition,[],[f4663,f881])).
% 4.51/0.95  fof(f4663,plain,(
% 4.51/0.95    ( ! [X52,X50,X48,X51,X49] : (k3_enumset1(X48,X49,X50,X51,X52) = k7_enumset1(X48,X49,X50,X50,X50,X50,X50,X51,X52)) )),
% 4.51/0.95    inference(forward_demodulation,[],[f4625,f24])).
% 4.51/0.95  fof(f4625,plain,(
% 4.51/0.95    ( ! [X52,X50,X48,X51,X49] : (k7_enumset1(X48,X49,X50,X50,X50,X50,X50,X51,X52) = k4_enumset1(X48,X48,X49,X50,X51,X52)) )),
% 4.51/0.95    inference(superposition,[],[f3349,f881])).
% 4.51/0.95  fof(f3349,plain,(
% 4.51/0.95    ( ! [X57,X54,X52,X56,X55,X53] : (k4_enumset1(X52,X53,X54,X55,X56,X57) = k7_enumset1(X52,X53,X54,X55,X55,X55,X55,X56,X57)) )),
% 4.51/0.95    inference(forward_demodulation,[],[f3299,f129])).
% 4.51/0.95  fof(f3299,plain,(
% 4.51/0.95    ( ! [X57,X54,X52,X56,X55,X53] : (k2_xboole_0(k1_tarski(X52),k4_enumset1(X52,X53,X54,X55,X56,X57)) = k7_enumset1(X52,X53,X54,X55,X55,X55,X55,X56,X57)) )),
% 4.51/0.95    inference(superposition,[],[f881,f1396])).
% 4.51/0.95  fof(f1396,plain,(
% 4.51/0.95    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k7_enumset1(X3,X4,X5,X6,X0,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k4_enumset1(X4,X5,X6,X0,X1,X2))) )),
% 4.51/0.95    inference(backward_demodulation,[],[f900,f1390])).
% 4.51/0.95  fof(f900,plain,(
% 4.51/0.95    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k7_enumset1(X3,X4,X5,X6,X0,X0,X0,X1,X2) = k2_xboole_0(k1_enumset1(X3,X4,X5),k2_enumset1(X6,X0,X1,X2))) )),
% 4.51/0.95    inference(backward_demodulation,[],[f91,f899])).
% 4.51/0.95  fof(f155,plain,(
% 4.51/0.95    ( ! [X6,X4,X2,X0,X12,X10,X8,X7,X5,X3,X1,X11,X9] : (k2_xboole_0(k7_enumset1(X9,X10,X11,X12,X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) = k2_xboole_0(k2_enumset1(X9,X10,X11,X12),k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8))) )),
% 4.51/0.95    inference(superposition,[],[f93,f30])).
% 4.51/0.95  fof(f93,plain,(
% 4.51/0.95    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (k2_xboole_0(k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8),X9) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k3_enumset1(X4,X5,X6,X7,X8),X9))) )),
% 4.51/0.95    inference(superposition,[],[f21,f29])).
% 4.51/0.95  fof(f3967,plain,(
% 4.51/0.95    ( ! [X61,X59,X57,X54,X62,X60,X58,X56,X55] : (k2_xboole_0(k1_enumset1(X61,X61,X62),k2_xboole_0(k1_tarski(X54),k4_enumset1(X55,X56,X57,X58,X59,X60))) = k2_xboole_0(k1_enumset1(X61,X62,X54),k4_enumset1(X55,X56,X57,X58,X59,X60))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f3937,f1925])).
% 4.51/0.95  fof(f1925,plain,(
% 4.51/0.95    ( ! [X30,X28,X26,X24,X31,X29,X27,X25,X32] : (k2_xboole_0(k4_enumset1(X30,X31,X32,X24,X25,X26),k2_enumset1(X26,X27,X28,X29)) = k2_xboole_0(k1_enumset1(X30,X31,X32),k4_enumset1(X24,X25,X26,X27,X28,X29))) )),
% 4.51/0.95    inference(superposition,[],[f58,f938])).
% 4.51/0.95  fof(f938,plain,(
% 4.51/0.95    ( ! [X12,X10,X8,X7,X11,X9] : (k2_xboole_0(k1_enumset1(X7,X8,X9),k2_enumset1(X9,X10,X11,X12)) = k4_enumset1(X7,X8,X9,X10,X11,X12)) )),
% 4.51/0.95    inference(backward_demodulation,[],[f857,f937])).
% 4.51/0.95  fof(f937,plain,(
% 4.51/0.95    ( ! [X14,X12,X17,X15,X13,X16] : (k2_xboole_0(k1_enumset1(X12,X12,X13),k2_enumset1(X14,X15,X16,X17)) = k4_enumset1(X12,X13,X14,X15,X16,X17)) )),
% 4.51/0.95    inference(forward_demodulation,[],[f936,f897])).
% 4.51/0.95  fof(f897,plain,(
% 4.51/0.95    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X3,X4,X5))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f896,f27])).
% 4.51/0.95  fof(f896,plain,(
% 4.51/0.95    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X3,X4,X5))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f895,f40])).
% 4.51/0.95  fof(f895,plain,(
% 4.51/0.95    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k1_enumset1(X3,X4,X5)) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X3,X4,X5))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f875,f40])).
% 4.51/0.95  fof(f875,plain,(
% 4.51/0.95    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k1_enumset1(X3,X4,X5)) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X3,X3,X4,X5))) )),
% 4.51/0.95    inference(superposition,[],[f96,f91])).
% 4.51/0.95  fof(f936,plain,(
% 4.51/0.95    ( ! [X14,X12,X17,X15,X13,X16] : (k2_xboole_0(k1_enumset1(X12,X12,X13),k2_enumset1(X14,X15,X16,X17)) = k2_xboole_0(k2_enumset1(X12,X13,X14,X15),k1_enumset1(X15,X16,X17))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f927,f40])).
% 4.51/0.95  fof(f927,plain,(
% 4.51/0.95    ( ! [X14,X12,X17,X15,X13,X16] : (k2_xboole_0(k2_enumset1(X12,X13,X14,X15),k2_enumset1(X15,X15,X16,X17)) = k2_xboole_0(k1_enumset1(X12,X12,X13),k2_enumset1(X14,X15,X16,X17))) )),
% 4.51/0.95    inference(superposition,[],[f900,f96])).
% 4.51/0.95  fof(f857,plain,(
% 4.51/0.95    ( ! [X12,X10,X8,X7,X11,X9] : (k2_xboole_0(k1_enumset1(X7,X8,X9),k2_enumset1(X9,X10,X11,X12)) = k2_xboole_0(k1_enumset1(X7,X7,X8),k2_enumset1(X9,X10,X11,X12))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f842,f40])).
% 4.51/0.95  fof(f842,plain,(
% 4.51/0.95    ( ! [X12,X10,X8,X7,X11,X9] : (k2_xboole_0(k1_enumset1(X7,X8,X9),k2_enumset1(X9,X10,X11,X12)) = k2_xboole_0(k2_enumset1(X7,X7,X7,X8),k2_enumset1(X9,X10,X11,X12))) )),
% 4.51/0.95    inference(superposition,[],[f92,f95])).
% 4.51/0.95  fof(f58,plain,(
% 4.51/0.95    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_enumset1(X3,X4,X5),X6))) )),
% 4.51/0.95    inference(superposition,[],[f21,f27])).
% 4.51/0.95  fof(f3937,plain,(
% 4.51/0.95    ( ! [X61,X59,X57,X54,X62,X60,X58,X56,X55] : (k2_xboole_0(k4_enumset1(X61,X62,X54,X55,X56,X57),k2_enumset1(X57,X58,X59,X60)) = k2_xboole_0(k1_enumset1(X61,X61,X62),k2_xboole_0(k1_tarski(X54),k4_enumset1(X55,X56,X57,X58,X59,X60)))) )),
% 4.51/0.95    inference(superposition,[],[f1661,f1395])).
% 4.51/0.95  fof(f1395,plain,(
% 4.51/0.95    ( ! [X30,X35,X33,X31,X29,X34,X32] : (k2_xboole_0(k2_enumset1(X29,X30,X31,X32),k2_enumset1(X32,X33,X34,X35)) = k2_xboole_0(k1_tarski(X29),k4_enumset1(X30,X31,X32,X33,X34,X35))) )),
% 4.51/0.95    inference(backward_demodulation,[],[f898,f1390])).
% 4.51/0.95  fof(f898,plain,(
% 4.51/0.95    ( ! [X30,X35,X33,X31,X29,X34,X32] : (k2_xboole_0(k2_enumset1(X29,X30,X31,X32),k2_enumset1(X32,X33,X34,X35)) = k2_xboole_0(k1_enumset1(X29,X30,X31),k2_enumset1(X32,X33,X34,X35))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f878,f40])).
% 4.51/0.95  fof(f878,plain,(
% 4.51/0.95    ( ! [X30,X35,X33,X31,X29,X34,X32] : (k2_xboole_0(k2_enumset1(X29,X29,X30,X31),k2_enumset1(X32,X33,X34,X35)) = k2_xboole_0(k2_enumset1(X29,X30,X31,X32),k2_enumset1(X32,X33,X34,X35))) )),
% 4.51/0.95    inference(superposition,[],[f96,f92])).
% 4.51/0.95  fof(f1661,plain,(
% 4.51/0.95    ( ! [X39,X37,X35,X33,X38,X36,X34] : (k2_xboole_0(k4_enumset1(X33,X34,X35,X36,X37,X38),X39) = k2_xboole_0(k1_enumset1(X33,X33,X34),k2_xboole_0(k2_enumset1(X35,X36,X37,X38),X39))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f1660,f40])).
% 4.51/0.95  fof(f1660,plain,(
% 4.51/0.95    ( ! [X39,X37,X35,X33,X38,X36,X34] : (k2_xboole_0(k4_enumset1(X33,X34,X35,X36,X37,X38),X39) = k2_xboole_0(k2_enumset1(X33,X33,X33,X34),k2_xboole_0(k2_enumset1(X35,X36,X37,X38),X39))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f1659,f50])).
% 4.51/0.95  fof(f50,plain,(
% 4.51/0.95    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),X6)) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),X6)) )),
% 4.51/0.95    inference(superposition,[],[f21,f26])).
% 4.51/0.95  fof(f1659,plain,(
% 4.51/0.95    ( ! [X39,X37,X35,X33,X38,X36,X34] : (k2_xboole_0(k2_enumset1(X33,X33,X33,X34),k2_xboole_0(k2_enumset1(X35,X36,X37,X38),X39)) = k2_xboole_0(k1_tarski(X33),k2_xboole_0(k3_enumset1(X34,X35,X36,X37,X38),X39))) )),
% 4.51/0.95    inference(forward_demodulation,[],[f1658,f21])).
% 4.51/0.95  fof(f1658,plain,(
% 4.51/0.95    ( ! [X39,X37,X35,X33,X38,X36,X34] : (k2_xboole_0(k2_enumset1(X33,X33,X33,X34),k2_xboole_0(k2_enumset1(X35,X36,X37,X38),X39)) = k2_xboole_0(k2_xboole_0(k1_tarski(X33),k3_enumset1(X34,X35,X36,X37,X38)),X39)) )),
% 4.51/0.95    inference(forward_demodulation,[],[f1614,f812])).
% 4.51/0.95  fof(f812,plain,(
% 4.51/0.95    ( ! [X6,X4,X8,X7,X5] : (k4_enumset1(X8,X4,X4,X5,X6,X7) = k3_enumset1(X8,X4,X5,X6,X7)) )),
% 4.51/0.95    inference(backward_demodulation,[],[f49,f810])).
% 4.51/0.95  fof(f810,plain,(
% 4.51/0.95    ( ! [X6,X10,X8,X7,X9] : (k2_xboole_0(k1_tarski(X10),k2_enumset1(X6,X7,X8,X9)) = k3_enumset1(X10,X6,X7,X8,X9)) )),
% 4.51/0.95    inference(forward_demodulation,[],[f802,f704])).
% 4.51/0.95  fof(f802,plain,(
% 4.51/0.95    ( ! [X6,X10,X8,X7,X9] : (k4_enumset1(X10,X6,X7,X7,X8,X9) = k2_xboole_0(k1_tarski(X10),k2_enumset1(X6,X7,X8,X9))) )),
% 4.51/0.95    inference(superposition,[],[f26,f774])).
% 4.51/0.95  fof(f1614,plain,(
% 4.51/0.95    ( ! [X39,X37,X35,X33,X38,X36,X34] : (k2_xboole_0(k2_enumset1(X33,X33,X33,X34),k2_xboole_0(k2_enumset1(X35,X36,X37,X38),X39)) = k2_xboole_0(k2_xboole_0(k1_tarski(X33),k4_enumset1(X34,X35,X35,X36,X37,X38)),X39)) )),
% 4.51/0.95    inference(superposition,[],[f154,f1391])).
% 4.51/0.95  fof(f154,plain,(
% 4.51/0.95    ( ! [X14,X12,X10,X8,X15,X13,X11,X9,X16] : (k2_xboole_0(k7_enumset1(X12,X13,X14,X15,X8,X8,X9,X10,X11),X16) = k2_xboole_0(k2_enumset1(X12,X13,X14,X15),k2_xboole_0(k2_enumset1(X8,X9,X10,X11),X16))) )),
% 4.51/0.95    inference(superposition,[],[f93,f43])).
% 4.51/0.95  fof(f124,plain,(
% 4.51/0.95    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X6,X7,X8,X0,X1,X2),k1_enumset1(X3,X4,X5)) = k2_xboole_0(k1_enumset1(X6,X7,X8),k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 4.51/0.95    inference(superposition,[],[f58,f27])).
% 4.51/0.95  fof(f18,plain,(
% 4.51/0.95    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))),
% 4.51/0.95    inference(cnf_transformation,[],[f17])).
% 4.51/0.95  fof(f17,plain,(
% 4.51/0.95    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))),
% 4.51/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f15,f16])).
% 4.51/0.95  fof(f16,plain,(
% 4.51/0.95    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_enumset1(sK6,sK7,sK8))),
% 4.51/0.95    introduced(choice_axiom,[])).
% 4.51/0.95  fof(f15,plain,(
% 4.51/0.95    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 4.51/0.95    inference(ennf_transformation,[],[f14])).
% 4.51/0.95  fof(f14,negated_conjecture,(
% 4.51/0.95    ~! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 4.51/0.95    inference(negated_conjecture,[],[f13])).
% 4.51/0.95  fof(f13,conjecture,(
% 4.51/0.95    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 4.51/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).
% 4.51/0.95  % SZS output end Proof for theBenchmark
% 4.51/0.95  % (31716)------------------------------
% 4.51/0.95  % (31716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.51/0.95  % (31716)Termination reason: Refutation
% 4.51/0.95  
% 4.51/0.95  % (31716)Memory used [KB]: 10490
% 4.51/0.95  % (31716)Time elapsed: 0.510 s
% 4.51/0.95  % (31716)------------------------------
% 4.51/0.95  % (31716)------------------------------
% 4.51/0.95  % (31712)Success in time 0.594 s
%------------------------------------------------------------------------------
