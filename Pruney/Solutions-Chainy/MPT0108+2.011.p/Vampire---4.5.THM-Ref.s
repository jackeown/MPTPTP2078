%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:19 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :  100 (9105 expanded)
%              Number of leaves         :   13 (3035 expanded)
%              Depth                    :   28
%              Number of atoms          :  101 (9106 expanded)
%              Number of equality atoms :  100 (9105 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7202,plain,(
    $false ),
    inference(subsumption_resolution,[],[f17,f7201])).

fof(f7201,plain,(
    ! [X37,X38] : k5_xboole_0(X37,X38) = k4_xboole_0(k2_xboole_0(X37,X38),k3_xboole_0(X37,X38)) ),
    inference(forward_demodulation,[],[f7153,f6077])).

fof(f6077,plain,(
    ! [X33,X34] : k5_xboole_0(X33,X34) = k4_xboole_0(k5_xboole_0(X33,X34),k3_xboole_0(X33,X34)) ),
    inference(forward_demodulation,[],[f6041,f4374])).

fof(f4374,plain,(
    ! [X8,X7] : k5_xboole_0(k2_xboole_0(X8,X7),k3_xboole_0(X8,X7)) = k5_xboole_0(X8,X7) ),
    inference(superposition,[],[f479,f169])).

fof(f169,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f57,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(backward_demodulation,[],[f32,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(backward_demodulation,[],[f34,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f53,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f29,f24])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f20,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[],[f25,f20])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f33,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f22,f20])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f31,f19])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f21,f20])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f479,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),X2)) = k5_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[],[f27,f21])).

fof(f27,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f6041,plain,(
    ! [X33,X34] : k4_xboole_0(k5_xboole_0(X33,X34),k3_xboole_0(X33,X34)) = k5_xboole_0(k2_xboole_0(X33,X34),k3_xboole_0(X33,X34)) ),
    inference(superposition,[],[f5300,f443])).

fof(f443,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3)) ),
    inference(superposition,[],[f26,f19])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f5300,plain,(
    ! [X17,X16] : k4_xboole_0(X17,X16) = k5_xboole_0(k2_xboole_0(X16,X17),X16) ),
    inference(superposition,[],[f4324,f4419])).

fof(f4419,plain,(
    ! [X28,X27] : k5_xboole_0(k2_xboole_0(X28,X27),k4_xboole_0(X27,X28)) = X28 ),
    inference(forward_demodulation,[],[f4384,f4309])).

fof(f4309,plain,(
    ! [X30,X31] : k5_xboole_0(X31,k4_xboole_0(X30,X30)) = X31 ),
    inference(backward_demodulation,[],[f3363,f4234])).

fof(f4234,plain,(
    ! [X24,X25] : k2_xboole_0(X25,k4_xboole_0(X24,X24)) = X25 ),
    inference(superposition,[],[f47,f3300])).

fof(f3300,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X0) = k3_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(forward_demodulation,[],[f3267,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f42,f25])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f39,f19])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f22,f24])).

fof(f3267,plain,(
    ! [X0,X1] : k3_xboole_0(k4_xboole_0(X0,X0),X1) = k2_xboole_0(k4_xboole_0(X0,X0),k3_xboole_0(k4_xboole_0(X0,X0),X1)) ),
    inference(superposition,[],[f2574,f1792])).

fof(f1792,plain,(
    ! [X14] : k4_xboole_0(X14,X14) = k4_xboole_0(k4_xboole_0(X14,X14),k4_xboole_0(X14,X14)) ),
    inference(forward_demodulation,[],[f1791,f188])).

fof(f188,plain,(
    ! [X2] : k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2) ),
    inference(superposition,[],[f23,f186])).

fof(f186,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f181,f61])).

fof(f61,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f56,f22])).

fof(f181,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k2_xboole_0(X0,X0) ),
    inference(superposition,[],[f69,f21])).

fof(f69,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k5_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f65,f20])).

fof(f65,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f23,f30])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1791,plain,(
    ! [X14] : k5_xboole_0(X14,X14) = k4_xboole_0(k4_xboole_0(X14,X14),k4_xboole_0(X14,X14)) ),
    inference(forward_demodulation,[],[f1790,f61])).

fof(f1790,plain,(
    ! [X14] : k4_xboole_0(k4_xboole_0(X14,X14),k4_xboole_0(X14,X14)) = k5_xboole_0(X14,k2_xboole_0(X14,X14)) ),
    inference(forward_demodulation,[],[f1761,f21])).

fof(f1761,plain,(
    ! [X14] : k4_xboole_0(k4_xboole_0(X14,X14),k4_xboole_0(X14,X14)) = k5_xboole_0(X14,k5_xboole_0(X14,k4_xboole_0(X14,X14))) ),
    inference(superposition,[],[f484,f188])).

fof(f484,plain,(
    ! [X14,X15] : k5_xboole_0(X14,k5_xboole_0(X14,X15)) = k5_xboole_0(k4_xboole_0(X14,X14),X15) ),
    inference(superposition,[],[f27,f188])).

fof(f2574,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k2_xboole_0(k4_xboole_0(X5,X5),k3_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f2559,f47])).

fof(f2559,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X5),k3_xboole_0(X5,X6)) = k2_xboole_0(k3_xboole_0(X5,X6),k3_xboole_0(k4_xboole_0(X5,X5),k3_xboole_0(X5,X6))) ),
    inference(superposition,[],[f26,f1819])).

fof(f1819,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k5_xboole_0(k4_xboole_0(X2,X2),k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f489,f69])).

fof(f489,plain,(
    ! [X28,X29] : k5_xboole_0(X28,X29) = k5_xboole_0(k4_xboole_0(X28,X28),k5_xboole_0(X28,X29)) ),
    inference(superposition,[],[f27,f197])).

fof(f197,plain,(
    ! [X13] : k5_xboole_0(k4_xboole_0(X13,X13),X13) = X13 ),
    inference(superposition,[],[f57,f186])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f43,f18])).

fof(f3363,plain,(
    ! [X30,X31] : k2_xboole_0(X31,k4_xboole_0(X30,X30)) = k5_xboole_0(X31,k4_xboole_0(X30,X30)) ),
    inference(superposition,[],[f21,f3301])).

fof(f3301,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(backward_demodulation,[],[f2649,f3300])).

fof(f2649,plain,(
    ! [X0,X1] : k3_xboole_0(k4_xboole_0(X0,X0),X1) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(forward_demodulation,[],[f2628,f69])).

fof(f2628,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X0),X1) = k5_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),X1)) ),
    inference(superposition,[],[f1821,f1792])).

fof(f1821,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k5_xboole_0(k4_xboole_0(X5,X5),k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f489,f23])).

fof(f4384,plain,(
    ! [X28,X27] : k5_xboole_0(k2_xboole_0(X28,X27),k4_xboole_0(X27,X28)) = k5_xboole_0(X28,k4_xboole_0(k4_xboole_0(X27,X28),k4_xboole_0(X27,X28))) ),
    inference(superposition,[],[f479,f188])).

fof(f4324,plain,(
    ! [X6,X5] : k5_xboole_0(X5,k5_xboole_0(X5,X6)) = X6 ),
    inference(backward_demodulation,[],[f4306,f4321])).

fof(f4321,plain,(
    ! [X14,X15] : k2_xboole_0(k4_xboole_0(X14,X14),X15) = X15 ),
    inference(backward_demodulation,[],[f4313,f4310])).

fof(f4310,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X0),X1) = X1 ),
    inference(backward_demodulation,[],[f2962,f4234])).

fof(f2962,plain,(
    ! [X0,X1] : k2_xboole_0(X1,k4_xboole_0(X0,X0)) = k5_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X1,k4_xboole_0(X0,X0))) ),
    inference(superposition,[],[f2441,f1792])).

fof(f2441,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k5_xboole_0(k4_xboole_0(X1,X1),k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f1818,f19])).

fof(f1818,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f489,f21])).

fof(f4313,plain,(
    ! [X14,X15] : k5_xboole_0(k4_xboole_0(X14,X14),X15) = k2_xboole_0(k4_xboole_0(X14,X14),X15) ),
    inference(backward_demodulation,[],[f484,f4306])).

fof(f4306,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X5),X6) = k5_xboole_0(X5,k5_xboole_0(X5,X6)) ),
    inference(backward_demodulation,[],[f4303,f4234])).

fof(f4303,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X5),X6) = k5_xboole_0(X5,k5_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X5)))) ),
    inference(backward_demodulation,[],[f1756,f4302])).

fof(f4302,plain,(
    ! [X14,X15] : k4_xboole_0(X15,k4_xboole_0(X14,X14)) = k2_xboole_0(X15,k4_xboole_0(X14,X14)) ),
    inference(forward_demodulation,[],[f4230,f3363])).

fof(f4230,plain,(
    ! [X14,X15] : k4_xboole_0(X15,k4_xboole_0(X14,X14)) = k5_xboole_0(X15,k4_xboole_0(X14,X14)) ),
    inference(superposition,[],[f35,f3300])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f23,f18])).

fof(f1756,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X5),X6) = k5_xboole_0(X5,k5_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X5,X5)))) ),
    inference(superposition,[],[f484,f21])).

fof(f7153,plain,(
    ! [X37,X38] : k4_xboole_0(k5_xboole_0(X37,X38),k3_xboole_0(X37,X38)) = k4_xboole_0(k2_xboole_0(X37,X38),k3_xboole_0(X37,X38)) ),
    inference(superposition,[],[f5356,f443])).

fof(f5356,plain,(
    ! [X12,X13] : k4_xboole_0(X13,X12) = k4_xboole_0(k2_xboole_0(X12,X13),X12) ),
    inference(backward_demodulation,[],[f3646,f5300])).

fof(f3646,plain,(
    ! [X12,X13] : k4_xboole_0(k2_xboole_0(X12,X13),X12) = k5_xboole_0(k2_xboole_0(X12,X13),X12) ),
    inference(superposition,[],[f35,f3563])).

fof(f3563,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f3562,f186])).

fof(f3562,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X1) = k3_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f3457,f20])).

fof(f3457,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X1,k4_xboole_0(X1,X1)) ),
    inference(superposition,[],[f20,f3309])).

fof(f3309,plain,(
    ! [X12,X11] : k4_xboole_0(X11,X11) = k4_xboole_0(X11,k2_xboole_0(X11,X12)) ),
    inference(backward_demodulation,[],[f2427,f3301])).

fof(f2427,plain,(
    ! [X12,X11] : k4_xboole_0(X11,k2_xboole_0(X11,X12)) = k4_xboole_0(k4_xboole_0(X11,X11),k2_xboole_0(k4_xboole_0(X11,X11),X12)) ),
    inference(forward_demodulation,[],[f2399,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f2399,plain,(
    ! [X12,X11] : k4_xboole_0(k4_xboole_0(X11,X11),k2_xboole_0(k4_xboole_0(X11,X11),X12)) = k4_xboole_0(k4_xboole_0(X11,X11),X12) ),
    inference(superposition,[],[f28,f1792])).

fof(f17,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:34:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (22929)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (22923)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (22918)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (22917)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (22925)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (22932)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (22926)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (22933)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (22920)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (22927)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (22919)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (22928)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (22928)Refutation not found, incomplete strategy% (22928)------------------------------
% 0.21/0.50  % (22928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (22928)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (22928)Memory used [KB]: 10490
% 0.21/0.50  % (22928)Time elapsed: 0.084 s
% 0.21/0.50  % (22928)------------------------------
% 0.21/0.50  % (22928)------------------------------
% 0.21/0.51  % (22921)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (22924)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (22931)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (22930)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.52  % (22934)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.52  % (22922)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 2.12/0.69  % (22933)Refutation found. Thanks to Tanya!
% 2.12/0.69  % SZS status Theorem for theBenchmark
% 2.12/0.69  % SZS output start Proof for theBenchmark
% 2.12/0.69  fof(f7202,plain,(
% 2.12/0.69    $false),
% 2.12/0.69    inference(subsumption_resolution,[],[f17,f7201])).
% 2.12/0.69  fof(f7201,plain,(
% 2.12/0.69    ( ! [X37,X38] : (k5_xboole_0(X37,X38) = k4_xboole_0(k2_xboole_0(X37,X38),k3_xboole_0(X37,X38))) )),
% 2.12/0.69    inference(forward_demodulation,[],[f7153,f6077])).
% 2.12/0.69  fof(f6077,plain,(
% 2.12/0.69    ( ! [X33,X34] : (k5_xboole_0(X33,X34) = k4_xboole_0(k5_xboole_0(X33,X34),k3_xboole_0(X33,X34))) )),
% 2.12/0.69    inference(forward_demodulation,[],[f6041,f4374])).
% 2.12/0.69  fof(f4374,plain,(
% 2.12/0.69    ( ! [X8,X7] : (k5_xboole_0(k2_xboole_0(X8,X7),k3_xboole_0(X8,X7)) = k5_xboole_0(X8,X7)) )),
% 2.12/0.69    inference(superposition,[],[f479,f169])).
% 2.12/0.69  fof(f169,plain,(
% 2.12/0.69    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = X0) )),
% 2.12/0.69    inference(superposition,[],[f57,f18])).
% 2.12/0.69  fof(f18,plain,(
% 2.12/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.12/0.69    inference(cnf_transformation,[],[f2])).
% 2.12/0.69  fof(f2,axiom,(
% 2.12/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.12/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.12/0.69  fof(f57,plain,(
% 2.12/0.69    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0) )),
% 2.12/0.69    inference(backward_demodulation,[],[f32,f56])).
% 2.12/0.69  fof(f56,plain,(
% 2.12/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 2.12/0.69    inference(backward_demodulation,[],[f34,f55])).
% 2.12/0.69  fof(f55,plain,(
% 2.12/0.69    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0) )),
% 2.12/0.69    inference(forward_demodulation,[],[f53,f30])).
% 2.12/0.69  fof(f30,plain,(
% 2.12/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.12/0.69    inference(forward_demodulation,[],[f29,f24])).
% 2.12/0.69  fof(f24,plain,(
% 2.12/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.12/0.69    inference(cnf_transformation,[],[f6])).
% 2.12/0.69  fof(f6,axiom,(
% 2.12/0.69    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.12/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.12/0.69  fof(f29,plain,(
% 2.12/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.12/0.69    inference(superposition,[],[f20,f20])).
% 2.12/0.69  fof(f20,plain,(
% 2.12/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.12/0.69    inference(cnf_transformation,[],[f7])).
% 2.12/0.69  fof(f7,axiom,(
% 2.12/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.12/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.12/0.69  fof(f53,plain,(
% 2.12/0.69    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0) )),
% 2.12/0.69    inference(superposition,[],[f25,f20])).
% 2.12/0.69  fof(f25,plain,(
% 2.12/0.69    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.12/0.69    inference(cnf_transformation,[],[f8])).
% 2.12/0.69  fof(f8,axiom,(
% 2.12/0.69    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.12/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.12/0.69  fof(f34,plain,(
% 2.12/0.69    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.12/0.69    inference(forward_demodulation,[],[f33,f19])).
% 2.12/0.69  fof(f19,plain,(
% 2.12/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.12/0.69    inference(cnf_transformation,[],[f1])).
% 2.12/0.69  fof(f1,axiom,(
% 2.12/0.69    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.12/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.12/0.69  fof(f33,plain,(
% 2.12/0.69    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 2.12/0.69    inference(superposition,[],[f22,f20])).
% 2.12/0.69  fof(f22,plain,(
% 2.12/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.12/0.69    inference(cnf_transformation,[],[f4])).
% 2.12/0.69  fof(f4,axiom,(
% 2.12/0.69    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.12/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.12/0.69  fof(f32,plain,(
% 2.12/0.69    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.12/0.69    inference(forward_demodulation,[],[f31,f19])).
% 2.12/0.69  fof(f31,plain,(
% 2.12/0.69    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.12/0.69    inference(superposition,[],[f21,f20])).
% 2.12/0.69  fof(f21,plain,(
% 2.12/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.12/0.69    inference(cnf_transformation,[],[f11])).
% 2.12/0.69  fof(f11,axiom,(
% 2.12/0.69    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.12/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.12/0.69  fof(f479,plain,(
% 2.12/0.69    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),X2)) = k5_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 2.12/0.69    inference(superposition,[],[f27,f21])).
% 2.12/0.69  fof(f27,plain,(
% 2.12/0.69    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.12/0.69    inference(cnf_transformation,[],[f9])).
% 2.12/0.69  fof(f9,axiom,(
% 2.12/0.69    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.12/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.12/0.69  fof(f6041,plain,(
% 2.12/0.69    ( ! [X33,X34] : (k4_xboole_0(k5_xboole_0(X33,X34),k3_xboole_0(X33,X34)) = k5_xboole_0(k2_xboole_0(X33,X34),k3_xboole_0(X33,X34))) )),
% 2.12/0.69    inference(superposition,[],[f5300,f443])).
% 2.12/0.69  fof(f443,plain,(
% 2.12/0.69    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))) )),
% 2.12/0.69    inference(superposition,[],[f26,f19])).
% 2.12/0.69  fof(f26,plain,(
% 2.12/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.12/0.69    inference(cnf_transformation,[],[f10])).
% 2.12/0.69  fof(f10,axiom,(
% 2.12/0.69    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.12/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 2.12/0.69  fof(f5300,plain,(
% 2.12/0.69    ( ! [X17,X16] : (k4_xboole_0(X17,X16) = k5_xboole_0(k2_xboole_0(X16,X17),X16)) )),
% 2.12/0.69    inference(superposition,[],[f4324,f4419])).
% 2.12/0.69  fof(f4419,plain,(
% 2.12/0.69    ( ! [X28,X27] : (k5_xboole_0(k2_xboole_0(X28,X27),k4_xboole_0(X27,X28)) = X28) )),
% 2.12/0.69    inference(forward_demodulation,[],[f4384,f4309])).
% 2.12/0.69  fof(f4309,plain,(
% 2.12/0.69    ( ! [X30,X31] : (k5_xboole_0(X31,k4_xboole_0(X30,X30)) = X31) )),
% 2.12/0.69    inference(backward_demodulation,[],[f3363,f4234])).
% 2.12/0.69  fof(f4234,plain,(
% 2.12/0.69    ( ! [X24,X25] : (k2_xboole_0(X25,k4_xboole_0(X24,X24)) = X25) )),
% 2.12/0.69    inference(superposition,[],[f47,f3300])).
% 2.12/0.69  fof(f3300,plain,(
% 2.12/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = k3_xboole_0(k4_xboole_0(X0,X0),X1)) )),
% 2.12/0.69    inference(forward_demodulation,[],[f3267,f43])).
% 2.12/0.70  fof(f43,plain,(
% 2.12/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.12/0.70    inference(forward_demodulation,[],[f42,f25])).
% 2.12/0.70  fof(f42,plain,(
% 2.12/0.70    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.12/0.70    inference(forward_demodulation,[],[f39,f19])).
% 2.12/0.70  fof(f39,plain,(
% 2.12/0.70    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 2.12/0.70    inference(superposition,[],[f22,f24])).
% 2.12/0.70  fof(f3267,plain,(
% 2.12/0.70    ( ! [X0,X1] : (k3_xboole_0(k4_xboole_0(X0,X0),X1) = k2_xboole_0(k4_xboole_0(X0,X0),k3_xboole_0(k4_xboole_0(X0,X0),X1))) )),
% 2.12/0.70    inference(superposition,[],[f2574,f1792])).
% 2.12/0.70  fof(f1792,plain,(
% 2.12/0.70    ( ! [X14] : (k4_xboole_0(X14,X14) = k4_xboole_0(k4_xboole_0(X14,X14),k4_xboole_0(X14,X14))) )),
% 2.12/0.70    inference(forward_demodulation,[],[f1791,f188])).
% 2.12/0.70  fof(f188,plain,(
% 2.12/0.70    ( ! [X2] : (k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2)) )),
% 2.12/0.70    inference(superposition,[],[f23,f186])).
% 2.12/0.70  fof(f186,plain,(
% 2.12/0.70    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.12/0.70    inference(forward_demodulation,[],[f181,f61])).
% 2.12/0.70  fof(f61,plain,(
% 2.12/0.70    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.12/0.70    inference(superposition,[],[f56,f22])).
% 2.12/0.70  fof(f181,plain,(
% 2.12/0.70    ( ! [X0] : (k3_xboole_0(X0,X0) = k2_xboole_0(X0,X0)) )),
% 2.12/0.70    inference(superposition,[],[f69,f21])).
% 2.12/0.70  fof(f69,plain,(
% 2.12/0.70    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) )),
% 2.12/0.70    inference(forward_demodulation,[],[f65,f20])).
% 2.12/0.70  fof(f65,plain,(
% 2.12/0.70    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) )),
% 2.12/0.70    inference(superposition,[],[f23,f30])).
% 2.12/0.70  fof(f23,plain,(
% 2.12/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.12/0.70    inference(cnf_transformation,[],[f3])).
% 2.12/0.70  fof(f3,axiom,(
% 2.12/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.12/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.12/0.70  fof(f1791,plain,(
% 2.12/0.70    ( ! [X14] : (k5_xboole_0(X14,X14) = k4_xboole_0(k4_xboole_0(X14,X14),k4_xboole_0(X14,X14))) )),
% 2.12/0.70    inference(forward_demodulation,[],[f1790,f61])).
% 2.12/0.70  fof(f1790,plain,(
% 2.12/0.70    ( ! [X14] : (k4_xboole_0(k4_xboole_0(X14,X14),k4_xboole_0(X14,X14)) = k5_xboole_0(X14,k2_xboole_0(X14,X14))) )),
% 2.12/0.70    inference(forward_demodulation,[],[f1761,f21])).
% 2.12/0.70  fof(f1761,plain,(
% 2.12/0.70    ( ! [X14] : (k4_xboole_0(k4_xboole_0(X14,X14),k4_xboole_0(X14,X14)) = k5_xboole_0(X14,k5_xboole_0(X14,k4_xboole_0(X14,X14)))) )),
% 2.12/0.70    inference(superposition,[],[f484,f188])).
% 2.12/0.70  fof(f484,plain,(
% 2.12/0.70    ( ! [X14,X15] : (k5_xboole_0(X14,k5_xboole_0(X14,X15)) = k5_xboole_0(k4_xboole_0(X14,X14),X15)) )),
% 2.12/0.70    inference(superposition,[],[f27,f188])).
% 2.12/0.70  fof(f2574,plain,(
% 2.12/0.70    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k2_xboole_0(k4_xboole_0(X5,X5),k3_xboole_0(X5,X6))) )),
% 2.12/0.70    inference(forward_demodulation,[],[f2559,f47])).
% 2.12/0.70  fof(f2559,plain,(
% 2.12/0.70    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X5),k3_xboole_0(X5,X6)) = k2_xboole_0(k3_xboole_0(X5,X6),k3_xboole_0(k4_xboole_0(X5,X5),k3_xboole_0(X5,X6)))) )),
% 2.12/0.70    inference(superposition,[],[f26,f1819])).
% 2.12/0.70  fof(f1819,plain,(
% 2.12/0.70    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k5_xboole_0(k4_xboole_0(X2,X2),k3_xboole_0(X2,X3))) )),
% 2.12/0.70    inference(superposition,[],[f489,f69])).
% 2.12/0.70  fof(f489,plain,(
% 2.12/0.70    ( ! [X28,X29] : (k5_xboole_0(X28,X29) = k5_xboole_0(k4_xboole_0(X28,X28),k5_xboole_0(X28,X29))) )),
% 2.12/0.70    inference(superposition,[],[f27,f197])).
% 2.12/0.70  fof(f197,plain,(
% 2.12/0.70    ( ! [X13] : (k5_xboole_0(k4_xboole_0(X13,X13),X13) = X13) )),
% 2.12/0.70    inference(superposition,[],[f57,f186])).
% 2.12/0.70  fof(f47,plain,(
% 2.12/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0) )),
% 2.12/0.70    inference(superposition,[],[f43,f18])).
% 2.12/0.70  fof(f3363,plain,(
% 2.12/0.70    ( ! [X30,X31] : (k2_xboole_0(X31,k4_xboole_0(X30,X30)) = k5_xboole_0(X31,k4_xboole_0(X30,X30))) )),
% 2.12/0.70    inference(superposition,[],[f21,f3301])).
% 2.12/0.70  fof(f3301,plain,(
% 2.12/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(X0,X0),X1)) )),
% 2.12/0.70    inference(backward_demodulation,[],[f2649,f3300])).
% 2.12/0.70  fof(f2649,plain,(
% 2.12/0.70    ( ! [X0,X1] : (k3_xboole_0(k4_xboole_0(X0,X0),X1) = k4_xboole_0(k4_xboole_0(X0,X0),X1)) )),
% 2.12/0.70    inference(forward_demodulation,[],[f2628,f69])).
% 2.12/0.70  fof(f2628,plain,(
% 2.12/0.70    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X0),X1) = k5_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),X1))) )),
% 2.12/0.70    inference(superposition,[],[f1821,f1792])).
% 2.12/0.70  fof(f1821,plain,(
% 2.12/0.70    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k5_xboole_0(k4_xboole_0(X5,X5),k4_xboole_0(X5,X6))) )),
% 2.12/0.70    inference(superposition,[],[f489,f23])).
% 2.12/0.70  fof(f4384,plain,(
% 2.12/0.70    ( ! [X28,X27] : (k5_xboole_0(k2_xboole_0(X28,X27),k4_xboole_0(X27,X28)) = k5_xboole_0(X28,k4_xboole_0(k4_xboole_0(X27,X28),k4_xboole_0(X27,X28)))) )),
% 2.12/0.70    inference(superposition,[],[f479,f188])).
% 2.12/0.70  fof(f4324,plain,(
% 2.12/0.70    ( ! [X6,X5] : (k5_xboole_0(X5,k5_xboole_0(X5,X6)) = X6) )),
% 2.12/0.70    inference(backward_demodulation,[],[f4306,f4321])).
% 2.12/0.70  fof(f4321,plain,(
% 2.12/0.70    ( ! [X14,X15] : (k2_xboole_0(k4_xboole_0(X14,X14),X15) = X15) )),
% 2.12/0.70    inference(backward_demodulation,[],[f4313,f4310])).
% 2.12/0.70  fof(f4310,plain,(
% 2.12/0.70    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X0),X1) = X1) )),
% 2.12/0.70    inference(backward_demodulation,[],[f2962,f4234])).
% 2.12/0.70  fof(f2962,plain,(
% 2.12/0.70    ( ! [X0,X1] : (k2_xboole_0(X1,k4_xboole_0(X0,X0)) = k5_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X1,k4_xboole_0(X0,X0)))) )),
% 2.12/0.70    inference(superposition,[],[f2441,f1792])).
% 2.12/0.70  fof(f2441,plain,(
% 2.12/0.70    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k5_xboole_0(k4_xboole_0(X1,X1),k2_xboole_0(X2,X1))) )),
% 2.12/0.70    inference(superposition,[],[f1818,f19])).
% 2.12/0.70  fof(f1818,plain,(
% 2.12/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X1))) )),
% 2.12/0.70    inference(superposition,[],[f489,f21])).
% 2.12/0.71  fof(f4313,plain,(
% 2.12/0.71    ( ! [X14,X15] : (k5_xboole_0(k4_xboole_0(X14,X14),X15) = k2_xboole_0(k4_xboole_0(X14,X14),X15)) )),
% 2.12/0.71    inference(backward_demodulation,[],[f484,f4306])).
% 2.12/0.71  fof(f4306,plain,(
% 2.12/0.71    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X5),X6) = k5_xboole_0(X5,k5_xboole_0(X5,X6))) )),
% 2.12/0.71    inference(backward_demodulation,[],[f4303,f4234])).
% 2.12/0.71  fof(f4303,plain,(
% 2.12/0.71    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X5),X6) = k5_xboole_0(X5,k5_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X5))))) )),
% 2.12/0.71    inference(backward_demodulation,[],[f1756,f4302])).
% 2.12/0.71  fof(f4302,plain,(
% 2.12/0.71    ( ! [X14,X15] : (k4_xboole_0(X15,k4_xboole_0(X14,X14)) = k2_xboole_0(X15,k4_xboole_0(X14,X14))) )),
% 2.12/0.71    inference(forward_demodulation,[],[f4230,f3363])).
% 2.12/0.71  fof(f4230,plain,(
% 2.12/0.71    ( ! [X14,X15] : (k4_xboole_0(X15,k4_xboole_0(X14,X14)) = k5_xboole_0(X15,k4_xboole_0(X14,X14))) )),
% 2.12/0.71    inference(superposition,[],[f35,f3300])).
% 2.12/0.71  fof(f35,plain,(
% 2.12/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 2.12/0.71    inference(superposition,[],[f23,f18])).
% 2.12/0.71  fof(f1756,plain,(
% 2.12/0.71    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X5),X6) = k5_xboole_0(X5,k5_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X5,X5))))) )),
% 2.12/0.71    inference(superposition,[],[f484,f21])).
% 2.12/0.71  fof(f7153,plain,(
% 2.12/0.71    ( ! [X37,X38] : (k4_xboole_0(k5_xboole_0(X37,X38),k3_xboole_0(X37,X38)) = k4_xboole_0(k2_xboole_0(X37,X38),k3_xboole_0(X37,X38))) )),
% 2.12/0.71    inference(superposition,[],[f5356,f443])).
% 2.12/0.71  fof(f5356,plain,(
% 2.12/0.71    ( ! [X12,X13] : (k4_xboole_0(X13,X12) = k4_xboole_0(k2_xboole_0(X12,X13),X12)) )),
% 2.12/0.71    inference(backward_demodulation,[],[f3646,f5300])).
% 2.12/0.71  fof(f3646,plain,(
% 2.12/0.71    ( ! [X12,X13] : (k4_xboole_0(k2_xboole_0(X12,X13),X12) = k5_xboole_0(k2_xboole_0(X12,X13),X12)) )),
% 2.12/0.71    inference(superposition,[],[f35,f3563])).
% 2.12/0.71  fof(f3563,plain,(
% 2.12/0.71    ( ! [X2,X1] : (k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1) )),
% 2.12/0.71    inference(forward_demodulation,[],[f3562,f186])).
% 2.12/0.71  fof(f3562,plain,(
% 2.12/0.71    ( ! [X2,X1] : (k3_xboole_0(X1,X1) = k3_xboole_0(X1,k2_xboole_0(X1,X2))) )),
% 2.12/0.71    inference(forward_demodulation,[],[f3457,f20])).
% 2.12/0.71  fof(f3457,plain,(
% 2.12/0.71    ( ! [X2,X1] : (k3_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X1,k4_xboole_0(X1,X1))) )),
% 2.12/0.71    inference(superposition,[],[f20,f3309])).
% 2.12/0.71  fof(f3309,plain,(
% 2.12/0.71    ( ! [X12,X11] : (k4_xboole_0(X11,X11) = k4_xboole_0(X11,k2_xboole_0(X11,X12))) )),
% 2.12/0.71    inference(backward_demodulation,[],[f2427,f3301])).
% 2.12/0.71  fof(f2427,plain,(
% 2.12/0.71    ( ! [X12,X11] : (k4_xboole_0(X11,k2_xboole_0(X11,X12)) = k4_xboole_0(k4_xboole_0(X11,X11),k2_xboole_0(k4_xboole_0(X11,X11),X12))) )),
% 2.12/0.71    inference(forward_demodulation,[],[f2399,f28])).
% 2.12/0.71  fof(f28,plain,(
% 2.12/0.71    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.12/0.71    inference(cnf_transformation,[],[f5])).
% 2.12/0.71  fof(f5,axiom,(
% 2.12/0.71    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.12/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.12/0.71  fof(f2399,plain,(
% 2.12/0.71    ( ! [X12,X11] : (k4_xboole_0(k4_xboole_0(X11,X11),k2_xboole_0(k4_xboole_0(X11,X11),X12)) = k4_xboole_0(k4_xboole_0(X11,X11),X12)) )),
% 2.12/0.71    inference(superposition,[],[f28,f1792])).
% 2.12/0.71  fof(f17,plain,(
% 2.12/0.71    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.12/0.71    inference(cnf_transformation,[],[f16])).
% 2.12/0.71  fof(f16,plain,(
% 2.12/0.71    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.12/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 2.12/0.71  fof(f15,plain,(
% 2.12/0.71    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.12/0.71    introduced(choice_axiom,[])).
% 2.12/0.71  fof(f14,plain,(
% 2.12/0.71    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.12/0.71    inference(ennf_transformation,[],[f13])).
% 2.12/0.71  fof(f13,negated_conjecture,(
% 2.12/0.71    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.12/0.71    inference(negated_conjecture,[],[f12])).
% 2.12/0.71  fof(f12,conjecture,(
% 2.12/0.71    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.12/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 2.12/0.71  % SZS output end Proof for theBenchmark
% 2.12/0.71  % (22933)------------------------------
% 2.12/0.71  % (22933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.71  % (22933)Termination reason: Refutation
% 2.12/0.71  
% 2.12/0.71  % (22933)Memory used [KB]: 9978
% 2.12/0.71  % (22933)Time elapsed: 0.269 s
% 2.12/0.71  % (22933)------------------------------
% 2.12/0.71  % (22933)------------------------------
% 2.12/0.71  % (22916)Success in time 0.35 s
%------------------------------------------------------------------------------
