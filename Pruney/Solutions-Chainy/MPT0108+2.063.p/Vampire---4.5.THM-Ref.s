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
% DateTime   : Thu Dec  3 12:32:27 EST 2020

% Result     : Theorem 8.87s
% Output     : Refutation 9.23s
% Verified   : 
% Statistics : Number of formulae       :  173 (36081 expanded)
%              Number of leaves         :   11 (12027 expanded)
%              Depth                    :   56
%              Number of atoms          :  174 (36082 expanded)
%              Number of equality atoms :  173 (36081 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27657,plain,(
    $false ),
    inference(subsumption_resolution,[],[f15,f27656])).

fof(f27656,plain,(
    ! [X147,X148] : k5_xboole_0(X147,X148) = k4_xboole_0(k2_xboole_0(X147,X148),k3_xboole_0(X147,X148)) ),
    inference(forward_demodulation,[],[f27655,f5228])).

fof(f5228,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X0),X1) = X1 ),
    inference(backward_demodulation,[],[f719,f5227])).

fof(f5227,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(backward_demodulation,[],[f4800,f5226])).

fof(f5226,plain,(
    ! [X17,X18] : k2_xboole_0(k4_xboole_0(X18,X18),X17) = X17 ),
    inference(forward_demodulation,[],[f5202,f4957])).

fof(f4957,plain,(
    ! [X14,X13] : k4_xboole_0(X13,X13) = k3_xboole_0(X14,k4_xboole_0(X13,X13)) ),
    inference(backward_demodulation,[],[f131,f4907])).

fof(f4907,plain,(
    ! [X19,X20] : k4_xboole_0(X19,X19) = k4_xboole_0(k3_xboole_0(X20,X19),k3_xboole_0(X19,X20)) ),
    inference(backward_demodulation,[],[f877,f4898])).

fof(f4898,plain,(
    ! [X4,X5] : k3_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(X4,X4) ),
    inference(forward_demodulation,[],[f4888,f691])).

fof(f691,plain,(
    ! [X2] : k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2) ),
    inference(superposition,[],[f19,f669])).

fof(f669,plain,(
    ! [X23] : k3_xboole_0(X23,X23) = X23 ),
    inference(forward_demodulation,[],[f668,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[],[f21,f16])).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f668,plain,(
    ! [X23,X22] : k3_xboole_0(X23,X23) = k2_xboole_0(k3_xboole_0(X22,X23),k4_xboole_0(X23,X22)) ),
    inference(forward_demodulation,[],[f667,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f25,f20])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f18,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f667,plain,(
    ! [X23,X22] : k3_xboole_0(X23,X23) = k2_xboole_0(k3_xboole_0(X22,X23),k3_xboole_0(X23,k4_xboole_0(X23,X22))) ),
    inference(forward_demodulation,[],[f631,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f631,plain,(
    ! [X23,X22] : k3_xboole_0(X23,X23) = k2_xboole_0(k3_xboole_0(X22,X23),k4_xboole_0(k3_xboole_0(X23,X23),X22)) ),
    inference(superposition,[],[f35,f539])).

fof(f539,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X1,X1)) ),
    inference(superposition,[],[f449,f156])).

fof(f156,plain,(
    ! [X24,X23] : k3_xboole_0(X24,X23) = k3_xboole_0(k3_xboole_0(X24,X23),X23) ),
    inference(forward_demodulation,[],[f149,f124])).

fof(f124,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f123,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f32,f18])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f18,f20])).

fof(f123,plain,(
    ! [X6,X7] : k3_xboole_0(X6,k3_xboole_0(X6,X7)) = k3_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f111,f16])).

fof(f111,plain,(
    ! [X6,X7] : k3_xboole_0(k3_xboole_0(X6,X7),X6) = k3_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X7)) ),
    inference(superposition,[],[f59,f34])).

fof(f59,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k3_xboole_0(X6,X5)) = k3_xboole_0(X5,X6) ),
    inference(forward_demodulation,[],[f56,f18])).

fof(f56,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k3_xboole_0(X6,X5)) = k4_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f18,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f20,f16])).

fof(f149,plain,(
    ! [X24,X23] : k3_xboole_0(k3_xboole_0(X24,X23),X23) = k3_xboole_0(k3_xboole_0(X24,X23),k3_xboole_0(X24,X23)) ),
    inference(superposition,[],[f59,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k3_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f34,f16])).

fof(f449,plain,(
    ! [X6,X8,X7] : k3_xboole_0(k3_xboole_0(X6,X7),X8) = k3_xboole_0(X6,k3_xboole_0(X7,X8)) ),
    inference(backward_demodulation,[],[f378,f387])).

fof(f387,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[],[f352,f18])).

fof(f352,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,k4_xboole_0(X3,X5)) ),
    inference(superposition,[],[f272,f23])).

fof(f272,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f23,f16])).

fof(f378,plain,(
    ! [X6,X8,X7] : k3_xboole_0(k3_xboole_0(X6,X7),X8) = k3_xboole_0(X7,k4_xboole_0(X6,k4_xboole_0(X7,X8))) ),
    inference(forward_demodulation,[],[f377,f20])).

fof(f377,plain,(
    ! [X6,X8,X7] : k3_xboole_0(k3_xboole_0(X6,X7),X8) = k3_xboole_0(X7,k4_xboole_0(X6,k3_xboole_0(X6,k4_xboole_0(X7,X8)))) ),
    inference(forward_demodulation,[],[f353,f23])).

fof(f353,plain,(
    ! [X6,X8,X7] : k3_xboole_0(k3_xboole_0(X6,X7),X8) = k3_xboole_0(X7,k4_xboole_0(X6,k4_xboole_0(k3_xboole_0(X6,X7),X8))) ),
    inference(superposition,[],[f272,f18])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f4888,plain,(
    ! [X4,X5] : k3_xboole_0(X4,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,X4) ),
    inference(backward_demodulation,[],[f3605,f4884])).

fof(f4884,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2 ),
    inference(backward_demodulation,[],[f3977,f4883])).

fof(f4883,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k3_xboole_0(X0,k4_xboole_0(X1,X0))) = X2 ),
    inference(backward_demodulation,[],[f4166,f4882])).

fof(f4882,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k3_xboole_0(X0,k4_xboole_0(X1,X0))) = X2 ),
    inference(forward_demodulation,[],[f4867,f389])).

fof(f389,plain,(
    ! [X6,X8,X7] : k3_xboole_0(X8,k4_xboole_0(X6,X7)) = k3_xboole_0(X6,k4_xboole_0(X8,k3_xboole_0(X7,X6))) ),
    inference(superposition,[],[f352,f30])).

fof(f4867,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k3_xboole_0(X1,k4_xboole_0(X0,k3_xboole_0(X0,X1)))) = X2 ),
    inference(superposition,[],[f4801,f272])).

fof(f4801,plain,(
    ! [X6,X7] : k2_xboole_0(X7,k4_xboole_0(X6,X6)) = X7 ),
    inference(backward_demodulation,[],[f3692,f4799])).

fof(f4799,plain,(
    ! [X26,X27] : k4_xboole_0(X27,k4_xboole_0(X26,X26)) = X27 ),
    inference(forward_demodulation,[],[f4798,f21])).

fof(f4798,plain,(
    ! [X26,X27] : k4_xboole_0(X27,k4_xboole_0(X26,X26)) = k2_xboole_0(k3_xboole_0(X27,X26),k4_xboole_0(X27,X26)) ),
    inference(forward_demodulation,[],[f4797,f697])).

fof(f697,plain,(
    ! [X11] : k2_xboole_0(k4_xboole_0(X11,X11),X11) = X11 ),
    inference(superposition,[],[f39,f669])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f37,f27])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[],[f21,f18])).

fof(f4797,plain,(
    ! [X26,X27] : k4_xboole_0(X27,k4_xboole_0(X26,X26)) = k2_xboole_0(k3_xboole_0(X27,X26),k4_xboole_0(X27,k2_xboole_0(k4_xboole_0(X26,X26),X26))) ),
    inference(forward_demodulation,[],[f4711,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f4711,plain,(
    ! [X26,X27] : k4_xboole_0(X27,k4_xboole_0(X26,X26)) = k2_xboole_0(k3_xboole_0(X27,X26),k4_xboole_0(k4_xboole_0(X27,k4_xboole_0(X26,X26)),X26)) ),
    inference(superposition,[],[f35,f4214])).

fof(f4214,plain,(
    ! [X14,X15] : k3_xboole_0(X15,X14) = k3_xboole_0(X14,k4_xboole_0(X15,k4_xboole_0(X14,X14))) ),
    inference(superposition,[],[f352,f4169])).

fof(f4169,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f4154,f669])).

fof(f4154,plain,(
    ! [X0] : k4_xboole_0(k3_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f3692,f21])).

fof(f3692,plain,(
    ! [X6,X7] : k2_xboole_0(X7,k4_xboole_0(X6,X6)) = k4_xboole_0(X7,k4_xboole_0(X6,X6)) ),
    inference(forward_demodulation,[],[f3640,f411])).

fof(f411,plain,(
    ! [X10,X8,X9] : k4_xboole_0(X8,k4_xboole_0(X9,X10)) = k5_xboole_0(X8,k3_xboole_0(X9,k4_xboole_0(X8,X10))) ),
    inference(superposition,[],[f19,f352])).

fof(f3640,plain,(
    ! [X6,X7] : k2_xboole_0(X7,k4_xboole_0(X6,X6)) = k5_xboole_0(X7,k3_xboole_0(X6,k4_xboole_0(X7,X6))) ),
    inference(superposition,[],[f17,f3608])).

fof(f3608,plain,(
    ! [X6,X7] : k3_xboole_0(X6,k4_xboole_0(X7,X6)) = k4_xboole_0(k4_xboole_0(X6,X6),X7) ),
    inference(forward_demodulation,[],[f3607,f46])).

fof(f46,plain,(
    ! [X4,X5] : k5_xboole_0(X4,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,X5) ),
    inference(forward_demodulation,[],[f44,f18])).

fof(f44,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f19,f27])).

fof(f3607,plain,(
    ! [X6,X7] : k4_xboole_0(k4_xboole_0(X6,X6),X7) = k5_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X6))) ),
    inference(forward_demodulation,[],[f3606,f19])).

fof(f3606,plain,(
    ! [X6,X7] : k4_xboole_0(k4_xboole_0(X6,X6),X7) = k5_xboole_0(X6,k5_xboole_0(X6,k3_xboole_0(X6,k4_xboole_0(X7,X6)))) ),
    inference(forward_demodulation,[],[f3592,f393])).

fof(f393,plain,(
    ! [X10,X8,X9] : k3_xboole_0(k4_xboole_0(X9,X10),X8) = k3_xboole_0(X9,k4_xboole_0(X8,X10)) ),
    inference(superposition,[],[f352,f16])).

fof(f3592,plain,(
    ! [X6,X7] : k4_xboole_0(k4_xboole_0(X6,X6),X7) = k5_xboole_0(X6,k5_xboole_0(X6,k3_xboole_0(k4_xboole_0(X6,X6),X7))) ),
    inference(superposition,[],[f719,f19])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f4166,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k3_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X2,k3_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f4148,f389])).

fof(f4148,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k3_xboole_0(X1,k4_xboole_0(X0,k3_xboole_0(X0,X1)))) = k4_xboole_0(X2,k3_xboole_0(X1,k4_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(superposition,[],[f3692,f272])).

fof(f3977,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(superposition,[],[f18,f3632])).

fof(f3632,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f3608,f24])).

fof(f3605,plain,(
    ! [X4,X5] : k3_xboole_0(X4,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k3_xboole_0(X4,k2_xboole_0(X4,X5))) ),
    inference(forward_demodulation,[],[f3604,f393])).

fof(f3604,plain,(
    ! [X4,X5] : k3_xboole_0(k4_xboole_0(X4,X4),X5) = k5_xboole_0(X4,k3_xboole_0(X4,k2_xboole_0(X4,X5))) ),
    inference(forward_demodulation,[],[f3603,f46])).

fof(f3603,plain,(
    ! [X4,X5] : k3_xboole_0(k4_xboole_0(X4,X4),X5) = k5_xboole_0(X4,k5_xboole_0(X4,k4_xboole_0(X4,k2_xboole_0(X4,X5)))) ),
    inference(forward_demodulation,[],[f3591,f24])).

fof(f3591,plain,(
    ! [X4,X5] : k3_xboole_0(k4_xboole_0(X4,X4),X5) = k5_xboole_0(X4,k5_xboole_0(X4,k4_xboole_0(k4_xboole_0(X4,X4),X5))) ),
    inference(superposition,[],[f719,f46])).

fof(f877,plain,(
    ! [X19,X20] : k3_xboole_0(X19,k4_xboole_0(X20,X19)) = k4_xboole_0(k3_xboole_0(X20,X19),k3_xboole_0(X19,X20)) ),
    inference(forward_demodulation,[],[f876,f461])).

fof(f461,plain,(
    ! [X10,X11,X9] : k3_xboole_0(X9,k4_xboole_0(X10,X11)) = k3_xboole_0(X10,k4_xboole_0(X9,k3_xboole_0(X10,X11))) ),
    inference(forward_demodulation,[],[f460,f20])).

fof(f460,plain,(
    ! [X10,X11,X9] : k3_xboole_0(X9,k4_xboole_0(X10,X11)) = k3_xboole_0(X10,k4_xboole_0(X9,k3_xboole_0(X9,k3_xboole_0(X10,X11)))) ),
    inference(backward_demodulation,[],[f379,f449])).

fof(f379,plain,(
    ! [X10,X11,X9] : k3_xboole_0(X9,k4_xboole_0(X10,X11)) = k3_xboole_0(X10,k4_xboole_0(X9,k3_xboole_0(k3_xboole_0(X9,X10),X11))) ),
    inference(forward_demodulation,[],[f354,f23])).

fof(f354,plain,(
    ! [X10,X11,X9] : k4_xboole_0(k3_xboole_0(X9,X10),X11) = k3_xboole_0(X10,k4_xboole_0(X9,k3_xboole_0(k3_xboole_0(X9,X10),X11))) ),
    inference(superposition,[],[f272,f20])).

fof(f876,plain,(
    ! [X19,X20] : k4_xboole_0(k3_xboole_0(X20,X19),k3_xboole_0(X19,X20)) = k3_xboole_0(X20,k4_xboole_0(X19,k3_xboole_0(X20,X19))) ),
    inference(forward_demodulation,[],[f838,f23])).

fof(f838,plain,(
    ! [X19,X20] : k4_xboole_0(k3_xboole_0(X20,X19),k3_xboole_0(X19,X20)) = k4_xboole_0(k3_xboole_0(X20,X19),k3_xboole_0(X20,X19)) ),
    inference(superposition,[],[f30,f126])).

fof(f126,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,X9)) ),
    inference(forward_demodulation,[],[f125,f59])).

fof(f125,plain,(
    ! [X8,X9] : k3_xboole_0(X8,k3_xboole_0(X9,X8)) = k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,X9)) ),
    inference(forward_demodulation,[],[f112,f16])).

fof(f112,plain,(
    ! [X8,X9] : k3_xboole_0(k3_xboole_0(X9,X8),X8) = k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,X9)) ),
    inference(superposition,[],[f59,f59])).

fof(f131,plain,(
    ! [X14,X13] : k4_xboole_0(k3_xboole_0(X14,X13),k3_xboole_0(X13,X14)) = k3_xboole_0(X14,k4_xboole_0(X13,X13)) ),
    inference(forward_demodulation,[],[f117,f23])).

fof(f117,plain,(
    ! [X14,X13] : k4_xboole_0(k3_xboole_0(X14,X13),X13) = k4_xboole_0(k3_xboole_0(X14,X13),k3_xboole_0(X13,X14)) ),
    inference(superposition,[],[f30,f59])).

fof(f5202,plain,(
    ! [X17,X18] : k2_xboole_0(k3_xboole_0(X17,k4_xboole_0(X18,X18)),X17) = X17 ),
    inference(superposition,[],[f21,f4799])).

fof(f4800,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X2),X3) = k5_xboole_0(X2,k5_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f3590,f4799])).

fof(f3590,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X2),X3) = k5_xboole_0(X2,k5_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X2,X2)))) ),
    inference(superposition,[],[f719,f17])).

fof(f719,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[],[f22,f691])).

fof(f22,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f27655,plain,(
    ! [X147,X148] : k4_xboole_0(k2_xboole_0(X147,X148),k3_xboole_0(X147,X148)) = k5_xboole_0(k4_xboole_0(X148,X148),k5_xboole_0(X147,X148)) ),
    inference(forward_demodulation,[],[f27654,f7010])).

fof(f7010,plain,(
    ! [X24,X23,X25] : k4_xboole_0(X23,X23) = k3_xboole_0(X25,k4_xboole_0(X23,k2_xboole_0(X24,X23))) ),
    inference(forward_demodulation,[],[f6982,f7004])).

fof(f7004,plain,(
    ! [X33,X31,X32] : k4_xboole_0(X31,X31) = k4_xboole_0(k4_xboole_0(X31,k2_xboole_0(X32,X31)),X33) ),
    inference(forward_demodulation,[],[f7003,f5751])).

fof(f5751,plain,(
    ! [X23,X21,X22] : k4_xboole_0(X23,X23) = k3_xboole_0(X23,k4_xboole_0(X21,k2_xboole_0(X22,X23))) ),
    inference(superposition,[],[f4898,f24])).

fof(f7003,plain,(
    ! [X33,X31,X32] : k4_xboole_0(k4_xboole_0(X31,k2_xboole_0(X32,X31)),X33) = k3_xboole_0(X31,k4_xboole_0(X33,k2_xboole_0(X32,X31))) ),
    inference(forward_demodulation,[],[f6970,f393])).

fof(f6970,plain,(
    ! [X33,X31,X32] : k4_xboole_0(k4_xboole_0(X31,k2_xboole_0(X32,X31)),X33) = k3_xboole_0(k4_xboole_0(X31,k2_xboole_0(X32,X31)),X33) ),
    inference(superposition,[],[f6920,f46])).

fof(f6920,plain,(
    ! [X6,X8,X7] : k5_xboole_0(k4_xboole_0(X6,k2_xboole_0(X7,X6)),X8) = X8 ),
    inference(backward_demodulation,[],[f5237,f6908])).

fof(f6908,plain,(
    ! [X4,X3] : k2_xboole_0(X4,X3) = k2_xboole_0(X4,k4_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f6886,f17])).

fof(f6886,plain,(
    ! [X4,X3] : k2_xboole_0(X4,k4_xboole_0(X3,X4)) = k5_xboole_0(X4,k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f17,f5849])).

fof(f5849,plain,(
    ! [X21,X22] : k4_xboole_0(X22,X21) = k4_xboole_0(k4_xboole_0(X22,X21),X21) ),
    inference(forward_demodulation,[],[f5767,f5239])).

fof(f5239,plain,(
    ! [X23,X22] : k5_xboole_0(X22,k4_xboole_0(X23,X23)) = X22 ),
    inference(forward_demodulation,[],[f5238,f673])).

fof(f673,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(backward_demodulation,[],[f103,f669])).

fof(f103,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k2_xboole_0(X0,X0) ),
    inference(superposition,[],[f46,f17])).

fof(f5238,plain,(
    ! [X23,X22] : k2_xboole_0(X22,X22) = k5_xboole_0(X22,k4_xboole_0(X23,X23)) ),
    inference(forward_demodulation,[],[f5204,f4957])).

fof(f5204,plain,(
    ! [X23,X22] : k2_xboole_0(X22,X22) = k5_xboole_0(X22,k3_xboole_0(X22,k4_xboole_0(X23,X23))) ),
    inference(superposition,[],[f26,f4799])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f17,f18])).

fof(f5767,plain,(
    ! [X21,X22] : k4_xboole_0(k4_xboole_0(X22,X21),X21) = k5_xboole_0(k4_xboole_0(X22,X21),k4_xboole_0(X21,X21)) ),
    inference(superposition,[],[f28,f4898])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f19,f16])).

fof(f5237,plain,(
    ! [X6,X8,X7] : k5_xboole_0(k4_xboole_0(X6,k2_xboole_0(X7,k4_xboole_0(X6,X7))),X8) = X8 ),
    inference(backward_demodulation,[],[f3589,f5227])).

fof(f3589,plain,(
    ! [X6,X8,X7] : k5_xboole_0(k4_xboole_0(X6,X7),k5_xboole_0(k4_xboole_0(X6,X7),X8)) = k5_xboole_0(k4_xboole_0(X6,k2_xboole_0(X7,k4_xboole_0(X6,X7))),X8) ),
    inference(superposition,[],[f719,f24])).

fof(f6982,plain,(
    ! [X24,X23,X25] : k3_xboole_0(X25,k4_xboole_0(X23,k2_xboole_0(X24,X23))) = k4_xboole_0(k4_xboole_0(X23,k2_xboole_0(X24,X23)),X25) ),
    inference(superposition,[],[f28,f6920])).

fof(f27654,plain,(
    ! [X147,X148] : k4_xboole_0(k2_xboole_0(X147,X148),k3_xboole_0(X147,X148)) = k5_xboole_0(k3_xboole_0(X147,k4_xboole_0(X148,k2_xboole_0(X147,X148))),k5_xboole_0(X147,X148)) ),
    inference(forward_demodulation,[],[f27456,f23])).

fof(f27456,plain,(
    ! [X147,X148] : k4_xboole_0(k2_xboole_0(X147,X148),k3_xboole_0(X147,X148)) = k5_xboole_0(k4_xboole_0(k3_xboole_0(X147,X148),k2_xboole_0(X147,X148)),k5_xboole_0(X147,X148)) ),
    inference(superposition,[],[f24277,f7800])).

fof(f7800,plain,(
    ! [X8,X9] : k5_xboole_0(k2_xboole_0(X9,X8),k3_xboole_0(X9,X8)) = k5_xboole_0(X9,X8) ),
    inference(superposition,[],[f257,f6255])).

fof(f6255,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = X1 ),
    inference(backward_demodulation,[],[f3781,f6252])).

fof(f6252,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(backward_demodulation,[],[f26,f6251])).

fof(f6251,plain,(
    ! [X6,X5] : k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,X6)) = X5 ),
    inference(backward_demodulation,[],[f3943,f6250])).

fof(f6250,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k5_xboole_0(k4_xboole_0(X4,X5),X4) ),
    inference(forward_demodulation,[],[f6236,f5903])).

fof(f5903,plain,(
    ! [X8,X7] : k3_xboole_0(X7,X8) = k4_xboole_0(k3_xboole_0(X7,X8),k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f5838,f20])).

fof(f5838,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k4_xboole_0(X11,X10)) = X10 ),
    inference(forward_demodulation,[],[f5837,f673])).

fof(f5837,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X10) = k4_xboole_0(X10,k4_xboole_0(X11,X10)) ),
    inference(forward_demodulation,[],[f5762,f17])).

fof(f5762,plain,(
    ! [X10,X11] : k5_xboole_0(X10,k4_xboole_0(X10,X10)) = k4_xboole_0(X10,k4_xboole_0(X11,X10)) ),
    inference(superposition,[],[f19,f4898])).

fof(f6236,plain,(
    ! [X4,X5] : k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k5_xboole_0(k4_xboole_0(X4,X5),X4) ),
    inference(superposition,[],[f5293,f39])).

fof(f5293,plain,(
    ! [X6,X5] : k4_xboole_0(X6,X5) = k5_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f5227,f17])).

fof(f3943,plain,(
    ! [X6,X5] : k5_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k4_xboole_0(X5,X6),X5)) = X5 ),
    inference(superposition,[],[f3901,f39])).

fof(f3901,plain,(
    ! [X6,X5] : k2_xboole_0(X5,X6) = k5_xboole_0(X5,k5_xboole_0(X5,k2_xboole_0(X5,X6))) ),
    inference(superposition,[],[f3894,f17])).

fof(f3894,plain,(
    ! [X2,X3] : k5_xboole_0(X2,X3) = k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f3882,f719])).

fof(f3882,plain,(
    ! [X2,X3] : k5_xboole_0(X2,X3) = k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X2),X3)) ),
    inference(superposition,[],[f22,f3830])).

fof(f3830,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f3829,f697])).

fof(f3829,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(k4_xboole_0(X0,X0),X0) ),
    inference(forward_demodulation,[],[f3828,f691])).

fof(f3828,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,X0),X0) = k5_xboole_0(X0,k5_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f3780,f719])).

fof(f3780,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,X0),X0) = k5_xboole_0(k4_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f26,f669])).

fof(f3781,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f26,f16])).

fof(f257,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),X2)) = k5_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[],[f22,f17])).

fof(f24277,plain,(
    ! [X114,X115] : k4_xboole_0(X114,X115) = k5_xboole_0(k4_xboole_0(X115,X114),k5_xboole_0(X114,X115)) ),
    inference(superposition,[],[f24205,f13758])).

fof(f13758,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f259,f6345])).

fof(f6345,plain,(
    ! [X8,X7] : k5_xboole_0(k3_xboole_0(X8,X7),k4_xboole_0(X7,X8)) = X7 ),
    inference(backward_demodulation,[],[f57,f6302])).

fof(f6302,plain,(
    ! [X2,X1] : k2_xboole_0(k3_xboole_0(X2,X1),X1) = X1 ),
    inference(superposition,[],[f6266,f16])).

fof(f6266,plain,(
    ! [X2,X3] : k2_xboole_0(k3_xboole_0(X2,X3),X2) = X2 ),
    inference(backward_demodulation,[],[f33,f6265])).

fof(f6265,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(backward_demodulation,[],[f3940,f6264])).

fof(f6264,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(k3_xboole_0(X8,X9),X8) ),
    inference(forward_demodulation,[],[f6238,f5899])).

fof(f5899,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f5838,f18])).

fof(f6238,plain,(
    ! [X8,X9] : k4_xboole_0(k4_xboole_0(X8,X9),k3_xboole_0(X8,X9)) = k5_xboole_0(k3_xboole_0(X8,X9),X8) ),
    inference(superposition,[],[f5293,f21])).

fof(f3940,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X1),X0)) = X0 ),
    inference(superposition,[],[f3901,f21])).

fof(f33,plain,(
    ! [X2,X3] : k2_xboole_0(k3_xboole_0(X2,X3),X2) = k5_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f17,f20])).

fof(f57,plain,(
    ! [X8,X7] : k2_xboole_0(k3_xboole_0(X8,X7),X7) = k5_xboole_0(k3_xboole_0(X8,X7),k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f17,f30])).

fof(f259,plain,(
    ! [X6,X8,X7] : k5_xboole_0(X6,k5_xboole_0(k3_xboole_0(X6,X7),X8)) = k5_xboole_0(k4_xboole_0(X6,X7),X8) ),
    inference(superposition,[],[f22,f19])).

fof(f24205,plain,(
    ! [X4,X5] : k5_xboole_0(X5,k5_xboole_0(X4,X5)) = X4 ),
    inference(forward_demodulation,[],[f24010,f9296])).

fof(f9296,plain,(
    ! [X0,X1] : k5_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(superposition,[],[f5227,f7843])).

fof(f7843,plain,(
    ! [X2,X1] : k4_xboole_0(X2,X1) = k5_xboole_0(k2_xboole_0(X2,X1),X1) ),
    inference(forward_demodulation,[],[f7797,f19])).

fof(f7797,plain,(
    ! [X2,X1] : k5_xboole_0(k2_xboole_0(X2,X1),X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f257,f6450])).

fof(f6450,plain,(
    ! [X2,X1] : k3_xboole_0(X2,X1) = k5_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(superposition,[],[f5227,f6255])).

fof(f24010,plain,(
    ! [X4,X5] : k5_xboole_0(k2_xboole_0(X5,X4),k4_xboole_0(X5,X4)) = k5_xboole_0(X5,k5_xboole_0(X4,X5)) ),
    inference(superposition,[],[f257,f13758])).

fof(f15,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:48:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (30952)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.52  % (30945)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.52  % (30947)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.52  % (30954)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.52  % (30959)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.53  % (30956)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.53  % (30957)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.54  % (30958)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.54  % (30948)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.56  % (30944)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.57  % (30949)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.58  % (30951)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.58  % (30950)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 1.79/0.59  % (30953)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.79/0.59  % (30961)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.79/0.60  % (30955)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.79/0.60  % (30955)Refutation not found, incomplete strategy% (30955)------------------------------
% 1.79/0.60  % (30955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.60  % (30955)Termination reason: Refutation not found, incomplete strategy
% 1.79/0.60  
% 1.79/0.60  % (30955)Memory used [KB]: 10490
% 1.79/0.60  % (30955)Time elapsed: 0.156 s
% 1.79/0.60  % (30955)------------------------------
% 1.79/0.60  % (30955)------------------------------
% 1.97/0.62  % (30960)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.97/0.62  % (30946)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 5.37/1.07  % (30948)Time limit reached!
% 5.37/1.07  % (30948)------------------------------
% 5.37/1.07  % (30948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.37/1.07  % (30948)Termination reason: Time limit
% 5.37/1.07  % (30948)Termination phase: Saturation
% 5.37/1.07  
% 5.37/1.07  % (30948)Memory used [KB]: 15991
% 5.37/1.07  % (30948)Time elapsed: 0.600 s
% 5.37/1.07  % (30948)------------------------------
% 5.37/1.07  % (30948)------------------------------
% 8.87/1.50  % (30960)Refutation found. Thanks to Tanya!
% 8.87/1.50  % SZS status Theorem for theBenchmark
% 9.23/1.52  % SZS output start Proof for theBenchmark
% 9.23/1.52  fof(f27657,plain,(
% 9.23/1.52    $false),
% 9.23/1.52    inference(subsumption_resolution,[],[f15,f27656])).
% 9.23/1.52  fof(f27656,plain,(
% 9.23/1.52    ( ! [X147,X148] : (k5_xboole_0(X147,X148) = k4_xboole_0(k2_xboole_0(X147,X148),k3_xboole_0(X147,X148))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f27655,f5228])).
% 9.23/1.52  fof(f5228,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X0),X1) = X1) )),
% 9.23/1.52    inference(backward_demodulation,[],[f719,f5227])).
% 9.23/1.52  fof(f5227,plain,(
% 9.23/1.52    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 9.23/1.52    inference(backward_demodulation,[],[f4800,f5226])).
% 9.23/1.52  fof(f5226,plain,(
% 9.23/1.52    ( ! [X17,X18] : (k2_xboole_0(k4_xboole_0(X18,X18),X17) = X17) )),
% 9.23/1.52    inference(forward_demodulation,[],[f5202,f4957])).
% 9.23/1.52  fof(f4957,plain,(
% 9.23/1.52    ( ! [X14,X13] : (k4_xboole_0(X13,X13) = k3_xboole_0(X14,k4_xboole_0(X13,X13))) )),
% 9.23/1.52    inference(backward_demodulation,[],[f131,f4907])).
% 9.23/1.52  fof(f4907,plain,(
% 9.23/1.52    ( ! [X19,X20] : (k4_xboole_0(X19,X19) = k4_xboole_0(k3_xboole_0(X20,X19),k3_xboole_0(X19,X20))) )),
% 9.23/1.52    inference(backward_demodulation,[],[f877,f4898])).
% 9.23/1.52  fof(f4898,plain,(
% 9.23/1.52    ( ! [X4,X5] : (k3_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(X4,X4)) )),
% 9.23/1.52    inference(forward_demodulation,[],[f4888,f691])).
% 9.23/1.52  fof(f691,plain,(
% 9.23/1.52    ( ! [X2] : (k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2)) )),
% 9.23/1.52    inference(superposition,[],[f19,f669])).
% 9.23/1.52  fof(f669,plain,(
% 9.23/1.52    ( ! [X23] : (k3_xboole_0(X23,X23) = X23) )),
% 9.23/1.52    inference(forward_demodulation,[],[f668,f35])).
% 9.23/1.52  fof(f35,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1)) = X0) )),
% 9.23/1.52    inference(superposition,[],[f21,f16])).
% 9.23/1.52  fof(f16,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 9.23/1.52    inference(cnf_transformation,[],[f1])).
% 9.23/1.52  fof(f1,axiom,(
% 9.23/1.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 9.23/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 9.23/1.52  fof(f21,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 9.23/1.52    inference(cnf_transformation,[],[f7])).
% 9.23/1.52  fof(f7,axiom,(
% 9.23/1.52    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 9.23/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 9.23/1.52  fof(f668,plain,(
% 9.23/1.52    ( ! [X23,X22] : (k3_xboole_0(X23,X23) = k2_xboole_0(k3_xboole_0(X22,X23),k4_xboole_0(X23,X22))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f667,f27])).
% 9.23/1.52  fof(f27,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f25,f20])).
% 9.23/1.52  fof(f20,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 9.23/1.52    inference(cnf_transformation,[],[f4])).
% 9.23/1.52  fof(f4,axiom,(
% 9.23/1.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 9.23/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 9.23/1.52  fof(f25,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 9.23/1.52    inference(superposition,[],[f18,f18])).
% 9.23/1.52  fof(f18,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 9.23/1.52    inference(cnf_transformation,[],[f5])).
% 9.23/1.52  fof(f5,axiom,(
% 9.23/1.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 9.23/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 9.23/1.52  fof(f667,plain,(
% 9.23/1.52    ( ! [X23,X22] : (k3_xboole_0(X23,X23) = k2_xboole_0(k3_xboole_0(X22,X23),k3_xboole_0(X23,k4_xboole_0(X23,X22)))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f631,f23])).
% 9.23/1.52  fof(f23,plain,(
% 9.23/1.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 9.23/1.52    inference(cnf_transformation,[],[f6])).
% 9.23/1.52  fof(f6,axiom,(
% 9.23/1.52    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 9.23/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 9.23/1.52  fof(f631,plain,(
% 9.23/1.52    ( ! [X23,X22] : (k3_xboole_0(X23,X23) = k2_xboole_0(k3_xboole_0(X22,X23),k4_xboole_0(k3_xboole_0(X23,X23),X22))) )),
% 9.23/1.52    inference(superposition,[],[f35,f539])).
% 9.23/1.52  fof(f539,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X1,X1))) )),
% 9.23/1.52    inference(superposition,[],[f449,f156])).
% 9.23/1.52  fof(f156,plain,(
% 9.23/1.52    ( ! [X24,X23] : (k3_xboole_0(X24,X23) = k3_xboole_0(k3_xboole_0(X24,X23),X23)) )),
% 9.23/1.52    inference(forward_demodulation,[],[f149,f124])).
% 9.23/1.52  fof(f124,plain,(
% 9.23/1.52    ( ! [X6,X7] : (k3_xboole_0(X6,X7) = k3_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X7))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f123,f34])).
% 9.23/1.52  fof(f34,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f32,f18])).
% 9.23/1.52  fof(f32,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 9.23/1.52    inference(superposition,[],[f18,f20])).
% 9.23/1.52  fof(f123,plain,(
% 9.23/1.52    ( ! [X6,X7] : (k3_xboole_0(X6,k3_xboole_0(X6,X7)) = k3_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X7))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f111,f16])).
% 9.23/1.52  fof(f111,plain,(
% 9.23/1.52    ( ! [X6,X7] : (k3_xboole_0(k3_xboole_0(X6,X7),X6) = k3_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X7))) )),
% 9.23/1.52    inference(superposition,[],[f59,f34])).
% 9.23/1.52  fof(f59,plain,(
% 9.23/1.52    ( ! [X6,X5] : (k3_xboole_0(X5,k3_xboole_0(X6,X5)) = k3_xboole_0(X5,X6)) )),
% 9.23/1.52    inference(forward_demodulation,[],[f56,f18])).
% 9.23/1.52  fof(f56,plain,(
% 9.23/1.52    ( ! [X6,X5] : (k3_xboole_0(X5,k3_xboole_0(X6,X5)) = k4_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 9.23/1.52    inference(superposition,[],[f18,f30])).
% 9.23/1.52  fof(f30,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 9.23/1.52    inference(superposition,[],[f20,f16])).
% 9.23/1.52  fof(f149,plain,(
% 9.23/1.52    ( ! [X24,X23] : (k3_xboole_0(k3_xboole_0(X24,X23),X23) = k3_xboole_0(k3_xboole_0(X24,X23),k3_xboole_0(X24,X23))) )),
% 9.23/1.52    inference(superposition,[],[f59,f61])).
% 9.23/1.52  fof(f61,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k3_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 9.23/1.52    inference(superposition,[],[f34,f16])).
% 9.23/1.52  fof(f449,plain,(
% 9.23/1.52    ( ! [X6,X8,X7] : (k3_xboole_0(k3_xboole_0(X6,X7),X8) = k3_xboole_0(X6,k3_xboole_0(X7,X8))) )),
% 9.23/1.52    inference(backward_demodulation,[],[f378,f387])).
% 9.23/1.52  fof(f387,plain,(
% 9.23/1.52    ( ! [X2,X0,X1] : (k3_xboole_0(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1)))) )),
% 9.23/1.52    inference(superposition,[],[f352,f18])).
% 9.23/1.52  fof(f352,plain,(
% 9.23/1.52    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,k4_xboole_0(X3,X5))) )),
% 9.23/1.52    inference(superposition,[],[f272,f23])).
% 9.23/1.52  fof(f272,plain,(
% 9.23/1.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2)) )),
% 9.23/1.52    inference(superposition,[],[f23,f16])).
% 9.23/1.52  fof(f378,plain,(
% 9.23/1.52    ( ! [X6,X8,X7] : (k3_xboole_0(k3_xboole_0(X6,X7),X8) = k3_xboole_0(X7,k4_xboole_0(X6,k4_xboole_0(X7,X8)))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f377,f20])).
% 9.23/1.52  fof(f377,plain,(
% 9.23/1.52    ( ! [X6,X8,X7] : (k3_xboole_0(k3_xboole_0(X6,X7),X8) = k3_xboole_0(X7,k4_xboole_0(X6,k3_xboole_0(X6,k4_xboole_0(X7,X8))))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f353,f23])).
% 9.23/1.52  fof(f353,plain,(
% 9.23/1.52    ( ! [X6,X8,X7] : (k3_xboole_0(k3_xboole_0(X6,X7),X8) = k3_xboole_0(X7,k4_xboole_0(X6,k4_xboole_0(k3_xboole_0(X6,X7),X8)))) )),
% 9.23/1.52    inference(superposition,[],[f272,f18])).
% 9.23/1.52  fof(f19,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 9.23/1.52    inference(cnf_transformation,[],[f2])).
% 9.23/1.52  fof(f2,axiom,(
% 9.23/1.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 9.23/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 9.23/1.52  fof(f4888,plain,(
% 9.23/1.52    ( ! [X4,X5] : (k3_xboole_0(X4,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,X4)) )),
% 9.23/1.52    inference(backward_demodulation,[],[f3605,f4884])).
% 9.23/1.52  fof(f4884,plain,(
% 9.23/1.52    ( ! [X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2) )),
% 9.23/1.52    inference(backward_demodulation,[],[f3977,f4883])).
% 9.23/1.52  fof(f4883,plain,(
% 9.23/1.52    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k3_xboole_0(X0,k4_xboole_0(X1,X0))) = X2) )),
% 9.23/1.52    inference(backward_demodulation,[],[f4166,f4882])).
% 9.23/1.52  fof(f4882,plain,(
% 9.23/1.52    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k3_xboole_0(X0,k4_xboole_0(X1,X0))) = X2) )),
% 9.23/1.52    inference(forward_demodulation,[],[f4867,f389])).
% 9.23/1.52  fof(f389,plain,(
% 9.23/1.52    ( ! [X6,X8,X7] : (k3_xboole_0(X8,k4_xboole_0(X6,X7)) = k3_xboole_0(X6,k4_xboole_0(X8,k3_xboole_0(X7,X6)))) )),
% 9.23/1.52    inference(superposition,[],[f352,f30])).
% 9.23/1.52  fof(f4867,plain,(
% 9.23/1.52    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k3_xboole_0(X1,k4_xboole_0(X0,k3_xboole_0(X0,X1)))) = X2) )),
% 9.23/1.52    inference(superposition,[],[f4801,f272])).
% 9.23/1.52  fof(f4801,plain,(
% 9.23/1.52    ( ! [X6,X7] : (k2_xboole_0(X7,k4_xboole_0(X6,X6)) = X7) )),
% 9.23/1.52    inference(backward_demodulation,[],[f3692,f4799])).
% 9.23/1.52  fof(f4799,plain,(
% 9.23/1.52    ( ! [X26,X27] : (k4_xboole_0(X27,k4_xboole_0(X26,X26)) = X27) )),
% 9.23/1.52    inference(forward_demodulation,[],[f4798,f21])).
% 9.23/1.52  fof(f4798,plain,(
% 9.23/1.52    ( ! [X26,X27] : (k4_xboole_0(X27,k4_xboole_0(X26,X26)) = k2_xboole_0(k3_xboole_0(X27,X26),k4_xboole_0(X27,X26))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f4797,f697])).
% 9.23/1.52  fof(f697,plain,(
% 9.23/1.52    ( ! [X11] : (k2_xboole_0(k4_xboole_0(X11,X11),X11) = X11) )),
% 9.23/1.52    inference(superposition,[],[f39,f669])).
% 9.23/1.52  fof(f39,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0) )),
% 9.23/1.52    inference(forward_demodulation,[],[f37,f27])).
% 9.23/1.52  fof(f37,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0) )),
% 9.23/1.52    inference(superposition,[],[f21,f18])).
% 9.23/1.52  fof(f4797,plain,(
% 9.23/1.52    ( ! [X26,X27] : (k4_xboole_0(X27,k4_xboole_0(X26,X26)) = k2_xboole_0(k3_xboole_0(X27,X26),k4_xboole_0(X27,k2_xboole_0(k4_xboole_0(X26,X26),X26)))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f4711,f24])).
% 9.23/1.52  fof(f24,plain,(
% 9.23/1.52    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 9.23/1.52    inference(cnf_transformation,[],[f3])).
% 9.23/1.52  fof(f3,axiom,(
% 9.23/1.52    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 9.23/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 9.23/1.52  fof(f4711,plain,(
% 9.23/1.52    ( ! [X26,X27] : (k4_xboole_0(X27,k4_xboole_0(X26,X26)) = k2_xboole_0(k3_xboole_0(X27,X26),k4_xboole_0(k4_xboole_0(X27,k4_xboole_0(X26,X26)),X26))) )),
% 9.23/1.52    inference(superposition,[],[f35,f4214])).
% 9.23/1.52  fof(f4214,plain,(
% 9.23/1.52    ( ! [X14,X15] : (k3_xboole_0(X15,X14) = k3_xboole_0(X14,k4_xboole_0(X15,k4_xboole_0(X14,X14)))) )),
% 9.23/1.52    inference(superposition,[],[f352,f4169])).
% 9.23/1.52  fof(f4169,plain,(
% 9.23/1.52    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 9.23/1.52    inference(forward_demodulation,[],[f4154,f669])).
% 9.23/1.52  fof(f4154,plain,(
% 9.23/1.52    ( ! [X0] : (k4_xboole_0(k3_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = X0) )),
% 9.23/1.52    inference(superposition,[],[f3692,f21])).
% 9.23/1.52  fof(f3692,plain,(
% 9.23/1.52    ( ! [X6,X7] : (k2_xboole_0(X7,k4_xboole_0(X6,X6)) = k4_xboole_0(X7,k4_xboole_0(X6,X6))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f3640,f411])).
% 9.23/1.52  fof(f411,plain,(
% 9.23/1.52    ( ! [X10,X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X9,X10)) = k5_xboole_0(X8,k3_xboole_0(X9,k4_xboole_0(X8,X10)))) )),
% 9.23/1.52    inference(superposition,[],[f19,f352])).
% 9.23/1.52  fof(f3640,plain,(
% 9.23/1.52    ( ! [X6,X7] : (k2_xboole_0(X7,k4_xboole_0(X6,X6)) = k5_xboole_0(X7,k3_xboole_0(X6,k4_xboole_0(X7,X6)))) )),
% 9.23/1.52    inference(superposition,[],[f17,f3608])).
% 9.23/1.52  fof(f3608,plain,(
% 9.23/1.52    ( ! [X6,X7] : (k3_xboole_0(X6,k4_xboole_0(X7,X6)) = k4_xboole_0(k4_xboole_0(X6,X6),X7)) )),
% 9.23/1.52    inference(forward_demodulation,[],[f3607,f46])).
% 9.23/1.52  fof(f46,plain,(
% 9.23/1.52    ( ! [X4,X5] : (k5_xboole_0(X4,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,X5)) )),
% 9.23/1.52    inference(forward_demodulation,[],[f44,f18])).
% 9.23/1.52  fof(f44,plain,(
% 9.23/1.52    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) )),
% 9.23/1.52    inference(superposition,[],[f19,f27])).
% 9.23/1.52  fof(f3607,plain,(
% 9.23/1.52    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X6,X6),X7) = k5_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X6)))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f3606,f19])).
% 9.23/1.52  fof(f3606,plain,(
% 9.23/1.52    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X6,X6),X7) = k5_xboole_0(X6,k5_xboole_0(X6,k3_xboole_0(X6,k4_xboole_0(X7,X6))))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f3592,f393])).
% 9.23/1.52  fof(f393,plain,(
% 9.23/1.52    ( ! [X10,X8,X9] : (k3_xboole_0(k4_xboole_0(X9,X10),X8) = k3_xboole_0(X9,k4_xboole_0(X8,X10))) )),
% 9.23/1.52    inference(superposition,[],[f352,f16])).
% 9.23/1.52  fof(f3592,plain,(
% 9.23/1.52    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X6,X6),X7) = k5_xboole_0(X6,k5_xboole_0(X6,k3_xboole_0(k4_xboole_0(X6,X6),X7)))) )),
% 9.23/1.52    inference(superposition,[],[f719,f19])).
% 9.23/1.52  fof(f17,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 9.23/1.52    inference(cnf_transformation,[],[f9])).
% 9.23/1.52  fof(f9,axiom,(
% 9.23/1.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 9.23/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 9.23/1.52  fof(f4166,plain,(
% 9.23/1.52    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k3_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X2,k3_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f4148,f389])).
% 9.23/1.52  fof(f4148,plain,(
% 9.23/1.52    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k3_xboole_0(X1,k4_xboole_0(X0,k3_xboole_0(X0,X1)))) = k4_xboole_0(X2,k3_xboole_0(X1,k4_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 9.23/1.52    inference(superposition,[],[f3692,f272])).
% 9.23/1.52  fof(f3977,plain,(
% 9.23/1.52    ( ! [X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,k4_xboole_0(X3,X2)))) )),
% 9.23/1.52    inference(superposition,[],[f18,f3632])).
% 9.23/1.52  fof(f3632,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 9.23/1.52    inference(superposition,[],[f3608,f24])).
% 9.23/1.52  fof(f3605,plain,(
% 9.23/1.52    ( ! [X4,X5] : (k3_xboole_0(X4,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k3_xboole_0(X4,k2_xboole_0(X4,X5)))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f3604,f393])).
% 9.23/1.52  fof(f3604,plain,(
% 9.23/1.52    ( ! [X4,X5] : (k3_xboole_0(k4_xboole_0(X4,X4),X5) = k5_xboole_0(X4,k3_xboole_0(X4,k2_xboole_0(X4,X5)))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f3603,f46])).
% 9.23/1.52  fof(f3603,plain,(
% 9.23/1.52    ( ! [X4,X5] : (k3_xboole_0(k4_xboole_0(X4,X4),X5) = k5_xboole_0(X4,k5_xboole_0(X4,k4_xboole_0(X4,k2_xboole_0(X4,X5))))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f3591,f24])).
% 9.23/1.52  fof(f3591,plain,(
% 9.23/1.52    ( ! [X4,X5] : (k3_xboole_0(k4_xboole_0(X4,X4),X5) = k5_xboole_0(X4,k5_xboole_0(X4,k4_xboole_0(k4_xboole_0(X4,X4),X5)))) )),
% 9.23/1.52    inference(superposition,[],[f719,f46])).
% 9.23/1.52  fof(f877,plain,(
% 9.23/1.52    ( ! [X19,X20] : (k3_xboole_0(X19,k4_xboole_0(X20,X19)) = k4_xboole_0(k3_xboole_0(X20,X19),k3_xboole_0(X19,X20))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f876,f461])).
% 9.23/1.52  fof(f461,plain,(
% 9.23/1.52    ( ! [X10,X11,X9] : (k3_xboole_0(X9,k4_xboole_0(X10,X11)) = k3_xboole_0(X10,k4_xboole_0(X9,k3_xboole_0(X10,X11)))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f460,f20])).
% 9.23/1.52  fof(f460,plain,(
% 9.23/1.52    ( ! [X10,X11,X9] : (k3_xboole_0(X9,k4_xboole_0(X10,X11)) = k3_xboole_0(X10,k4_xboole_0(X9,k3_xboole_0(X9,k3_xboole_0(X10,X11))))) )),
% 9.23/1.52    inference(backward_demodulation,[],[f379,f449])).
% 9.23/1.52  fof(f379,plain,(
% 9.23/1.52    ( ! [X10,X11,X9] : (k3_xboole_0(X9,k4_xboole_0(X10,X11)) = k3_xboole_0(X10,k4_xboole_0(X9,k3_xboole_0(k3_xboole_0(X9,X10),X11)))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f354,f23])).
% 9.23/1.52  fof(f354,plain,(
% 9.23/1.52    ( ! [X10,X11,X9] : (k4_xboole_0(k3_xboole_0(X9,X10),X11) = k3_xboole_0(X10,k4_xboole_0(X9,k3_xboole_0(k3_xboole_0(X9,X10),X11)))) )),
% 9.23/1.52    inference(superposition,[],[f272,f20])).
% 9.23/1.52  fof(f876,plain,(
% 9.23/1.52    ( ! [X19,X20] : (k4_xboole_0(k3_xboole_0(X20,X19),k3_xboole_0(X19,X20)) = k3_xboole_0(X20,k4_xboole_0(X19,k3_xboole_0(X20,X19)))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f838,f23])).
% 9.23/1.52  fof(f838,plain,(
% 9.23/1.52    ( ! [X19,X20] : (k4_xboole_0(k3_xboole_0(X20,X19),k3_xboole_0(X19,X20)) = k4_xboole_0(k3_xboole_0(X20,X19),k3_xboole_0(X20,X19))) )),
% 9.23/1.52    inference(superposition,[],[f30,f126])).
% 9.23/1.52  fof(f126,plain,(
% 9.23/1.52    ( ! [X8,X9] : (k3_xboole_0(X8,X9) = k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,X9))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f125,f59])).
% 9.23/1.52  fof(f125,plain,(
% 9.23/1.52    ( ! [X8,X9] : (k3_xboole_0(X8,k3_xboole_0(X9,X8)) = k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,X9))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f112,f16])).
% 9.23/1.52  fof(f112,plain,(
% 9.23/1.52    ( ! [X8,X9] : (k3_xboole_0(k3_xboole_0(X9,X8),X8) = k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,X9))) )),
% 9.23/1.52    inference(superposition,[],[f59,f59])).
% 9.23/1.52  fof(f131,plain,(
% 9.23/1.52    ( ! [X14,X13] : (k4_xboole_0(k3_xboole_0(X14,X13),k3_xboole_0(X13,X14)) = k3_xboole_0(X14,k4_xboole_0(X13,X13))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f117,f23])).
% 9.23/1.52  fof(f117,plain,(
% 9.23/1.52    ( ! [X14,X13] : (k4_xboole_0(k3_xboole_0(X14,X13),X13) = k4_xboole_0(k3_xboole_0(X14,X13),k3_xboole_0(X13,X14))) )),
% 9.23/1.52    inference(superposition,[],[f30,f59])).
% 9.23/1.52  fof(f5202,plain,(
% 9.23/1.52    ( ! [X17,X18] : (k2_xboole_0(k3_xboole_0(X17,k4_xboole_0(X18,X18)),X17) = X17) )),
% 9.23/1.52    inference(superposition,[],[f21,f4799])).
% 9.23/1.52  fof(f4800,plain,(
% 9.23/1.52    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X2),X3) = k5_xboole_0(X2,k5_xboole_0(X2,X3))) )),
% 9.23/1.52    inference(backward_demodulation,[],[f3590,f4799])).
% 9.23/1.52  fof(f3590,plain,(
% 9.23/1.52    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X2),X3) = k5_xboole_0(X2,k5_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X2,X2))))) )),
% 9.23/1.52    inference(superposition,[],[f719,f17])).
% 9.23/1.52  fof(f719,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k4_xboole_0(X0,X0),X1)) )),
% 9.23/1.52    inference(superposition,[],[f22,f691])).
% 9.23/1.52  fof(f22,plain,(
% 9.23/1.52    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 9.23/1.52    inference(cnf_transformation,[],[f8])).
% 9.23/1.52  fof(f8,axiom,(
% 9.23/1.52    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 9.23/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 9.23/1.52  fof(f27655,plain,(
% 9.23/1.52    ( ! [X147,X148] : (k4_xboole_0(k2_xboole_0(X147,X148),k3_xboole_0(X147,X148)) = k5_xboole_0(k4_xboole_0(X148,X148),k5_xboole_0(X147,X148))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f27654,f7010])).
% 9.23/1.52  fof(f7010,plain,(
% 9.23/1.52    ( ! [X24,X23,X25] : (k4_xboole_0(X23,X23) = k3_xboole_0(X25,k4_xboole_0(X23,k2_xboole_0(X24,X23)))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f6982,f7004])).
% 9.23/1.52  fof(f7004,plain,(
% 9.23/1.52    ( ! [X33,X31,X32] : (k4_xboole_0(X31,X31) = k4_xboole_0(k4_xboole_0(X31,k2_xboole_0(X32,X31)),X33)) )),
% 9.23/1.52    inference(forward_demodulation,[],[f7003,f5751])).
% 9.23/1.52  fof(f5751,plain,(
% 9.23/1.52    ( ! [X23,X21,X22] : (k4_xboole_0(X23,X23) = k3_xboole_0(X23,k4_xboole_0(X21,k2_xboole_0(X22,X23)))) )),
% 9.23/1.52    inference(superposition,[],[f4898,f24])).
% 9.23/1.52  fof(f7003,plain,(
% 9.23/1.52    ( ! [X33,X31,X32] : (k4_xboole_0(k4_xboole_0(X31,k2_xboole_0(X32,X31)),X33) = k3_xboole_0(X31,k4_xboole_0(X33,k2_xboole_0(X32,X31)))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f6970,f393])).
% 9.23/1.52  fof(f6970,plain,(
% 9.23/1.52    ( ! [X33,X31,X32] : (k4_xboole_0(k4_xboole_0(X31,k2_xboole_0(X32,X31)),X33) = k3_xboole_0(k4_xboole_0(X31,k2_xboole_0(X32,X31)),X33)) )),
% 9.23/1.52    inference(superposition,[],[f6920,f46])).
% 9.23/1.52  fof(f6920,plain,(
% 9.23/1.52    ( ! [X6,X8,X7] : (k5_xboole_0(k4_xboole_0(X6,k2_xboole_0(X7,X6)),X8) = X8) )),
% 9.23/1.52    inference(backward_demodulation,[],[f5237,f6908])).
% 9.23/1.52  fof(f6908,plain,(
% 9.23/1.52    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k2_xboole_0(X4,k4_xboole_0(X3,X4))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f6886,f17])).
% 9.23/1.52  fof(f6886,plain,(
% 9.23/1.52    ( ! [X4,X3] : (k2_xboole_0(X4,k4_xboole_0(X3,X4)) = k5_xboole_0(X4,k4_xboole_0(X3,X4))) )),
% 9.23/1.52    inference(superposition,[],[f17,f5849])).
% 9.23/1.52  fof(f5849,plain,(
% 9.23/1.52    ( ! [X21,X22] : (k4_xboole_0(X22,X21) = k4_xboole_0(k4_xboole_0(X22,X21),X21)) )),
% 9.23/1.52    inference(forward_demodulation,[],[f5767,f5239])).
% 9.23/1.52  fof(f5239,plain,(
% 9.23/1.52    ( ! [X23,X22] : (k5_xboole_0(X22,k4_xboole_0(X23,X23)) = X22) )),
% 9.23/1.52    inference(forward_demodulation,[],[f5238,f673])).
% 9.23/1.52  fof(f673,plain,(
% 9.23/1.52    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 9.23/1.52    inference(backward_demodulation,[],[f103,f669])).
% 9.23/1.52  fof(f103,plain,(
% 9.23/1.52    ( ! [X0] : (k3_xboole_0(X0,X0) = k2_xboole_0(X0,X0)) )),
% 9.23/1.52    inference(superposition,[],[f46,f17])).
% 9.23/1.52  fof(f5238,plain,(
% 9.23/1.52    ( ! [X23,X22] : (k2_xboole_0(X22,X22) = k5_xboole_0(X22,k4_xboole_0(X23,X23))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f5204,f4957])).
% 9.23/1.52  fof(f5204,plain,(
% 9.23/1.52    ( ! [X23,X22] : (k2_xboole_0(X22,X22) = k5_xboole_0(X22,k3_xboole_0(X22,k4_xboole_0(X23,X23)))) )),
% 9.23/1.52    inference(superposition,[],[f26,f4799])).
% 9.23/1.52  fof(f26,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 9.23/1.52    inference(superposition,[],[f17,f18])).
% 9.23/1.52  fof(f5767,plain,(
% 9.23/1.52    ( ! [X21,X22] : (k4_xboole_0(k4_xboole_0(X22,X21),X21) = k5_xboole_0(k4_xboole_0(X22,X21),k4_xboole_0(X21,X21))) )),
% 9.23/1.52    inference(superposition,[],[f28,f4898])).
% 9.23/1.52  fof(f28,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 9.23/1.52    inference(superposition,[],[f19,f16])).
% 9.23/1.52  fof(f5237,plain,(
% 9.23/1.52    ( ! [X6,X8,X7] : (k5_xboole_0(k4_xboole_0(X6,k2_xboole_0(X7,k4_xboole_0(X6,X7))),X8) = X8) )),
% 9.23/1.52    inference(backward_demodulation,[],[f3589,f5227])).
% 9.23/1.52  fof(f3589,plain,(
% 9.23/1.52    ( ! [X6,X8,X7] : (k5_xboole_0(k4_xboole_0(X6,X7),k5_xboole_0(k4_xboole_0(X6,X7),X8)) = k5_xboole_0(k4_xboole_0(X6,k2_xboole_0(X7,k4_xboole_0(X6,X7))),X8)) )),
% 9.23/1.52    inference(superposition,[],[f719,f24])).
% 9.23/1.52  fof(f6982,plain,(
% 9.23/1.52    ( ! [X24,X23,X25] : (k3_xboole_0(X25,k4_xboole_0(X23,k2_xboole_0(X24,X23))) = k4_xboole_0(k4_xboole_0(X23,k2_xboole_0(X24,X23)),X25)) )),
% 9.23/1.52    inference(superposition,[],[f28,f6920])).
% 9.23/1.52  fof(f27654,plain,(
% 9.23/1.52    ( ! [X147,X148] : (k4_xboole_0(k2_xboole_0(X147,X148),k3_xboole_0(X147,X148)) = k5_xboole_0(k3_xboole_0(X147,k4_xboole_0(X148,k2_xboole_0(X147,X148))),k5_xboole_0(X147,X148))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f27456,f23])).
% 9.23/1.52  fof(f27456,plain,(
% 9.23/1.52    ( ! [X147,X148] : (k4_xboole_0(k2_xboole_0(X147,X148),k3_xboole_0(X147,X148)) = k5_xboole_0(k4_xboole_0(k3_xboole_0(X147,X148),k2_xboole_0(X147,X148)),k5_xboole_0(X147,X148))) )),
% 9.23/1.52    inference(superposition,[],[f24277,f7800])).
% 9.23/1.52  fof(f7800,plain,(
% 9.23/1.52    ( ! [X8,X9] : (k5_xboole_0(k2_xboole_0(X9,X8),k3_xboole_0(X9,X8)) = k5_xboole_0(X9,X8)) )),
% 9.23/1.52    inference(superposition,[],[f257,f6255])).
% 9.23/1.52  fof(f6255,plain,(
% 9.23/1.52    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = X1) )),
% 9.23/1.52    inference(backward_demodulation,[],[f3781,f6252])).
% 9.23/1.52  fof(f6252,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 9.23/1.52    inference(backward_demodulation,[],[f26,f6251])).
% 9.23/1.52  fof(f6251,plain,(
% 9.23/1.52    ( ! [X6,X5] : (k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,X6)) = X5) )),
% 9.23/1.52    inference(backward_demodulation,[],[f3943,f6250])).
% 9.23/1.52  fof(f6250,plain,(
% 9.23/1.52    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k5_xboole_0(k4_xboole_0(X4,X5),X4)) )),
% 9.23/1.52    inference(forward_demodulation,[],[f6236,f5903])).
% 9.23/1.52  fof(f5903,plain,(
% 9.23/1.52    ( ! [X8,X7] : (k3_xboole_0(X7,X8) = k4_xboole_0(k3_xboole_0(X7,X8),k4_xboole_0(X7,X8))) )),
% 9.23/1.52    inference(superposition,[],[f5838,f20])).
% 9.23/1.52  fof(f5838,plain,(
% 9.23/1.52    ( ! [X10,X11] : (k4_xboole_0(X10,k4_xboole_0(X11,X10)) = X10) )),
% 9.23/1.52    inference(forward_demodulation,[],[f5837,f673])).
% 9.23/1.52  fof(f5837,plain,(
% 9.23/1.52    ( ! [X10,X11] : (k2_xboole_0(X10,X10) = k4_xboole_0(X10,k4_xboole_0(X11,X10))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f5762,f17])).
% 9.23/1.52  fof(f5762,plain,(
% 9.23/1.52    ( ! [X10,X11] : (k5_xboole_0(X10,k4_xboole_0(X10,X10)) = k4_xboole_0(X10,k4_xboole_0(X11,X10))) )),
% 9.23/1.52    inference(superposition,[],[f19,f4898])).
% 9.23/1.52  fof(f6236,plain,(
% 9.23/1.52    ( ! [X4,X5] : (k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k5_xboole_0(k4_xboole_0(X4,X5),X4)) )),
% 9.23/1.52    inference(superposition,[],[f5293,f39])).
% 9.23/1.52  fof(f5293,plain,(
% 9.23/1.52    ( ! [X6,X5] : (k4_xboole_0(X6,X5) = k5_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 9.23/1.52    inference(superposition,[],[f5227,f17])).
% 9.23/1.52  fof(f3943,plain,(
% 9.23/1.52    ( ! [X6,X5] : (k5_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(k4_xboole_0(X5,X6),X5)) = X5) )),
% 9.23/1.52    inference(superposition,[],[f3901,f39])).
% 9.23/1.52  fof(f3901,plain,(
% 9.23/1.52    ( ! [X6,X5] : (k2_xboole_0(X5,X6) = k5_xboole_0(X5,k5_xboole_0(X5,k2_xboole_0(X5,X6)))) )),
% 9.23/1.52    inference(superposition,[],[f3894,f17])).
% 9.23/1.52  fof(f3894,plain,(
% 9.23/1.52    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X2,X3)))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f3882,f719])).
% 9.23/1.52  fof(f3882,plain,(
% 9.23/1.52    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X2),X3))) )),
% 9.23/1.52    inference(superposition,[],[f22,f3830])).
% 9.23/1.52  fof(f3830,plain,(
% 9.23/1.52    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 9.23/1.52    inference(forward_demodulation,[],[f3829,f697])).
% 9.23/1.52  fof(f3829,plain,(
% 9.23/1.52    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k2_xboole_0(k4_xboole_0(X0,X0),X0)) )),
% 9.23/1.52    inference(forward_demodulation,[],[f3828,f691])).
% 9.23/1.52  fof(f3828,plain,(
% 9.23/1.52    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,X0),X0) = k5_xboole_0(X0,k5_xboole_0(X0,X0))) )),
% 9.23/1.52    inference(forward_demodulation,[],[f3780,f719])).
% 9.23/1.52  fof(f3780,plain,(
% 9.23/1.52    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,X0),X0) = k5_xboole_0(k4_xboole_0(X0,X0),X0)) )),
% 9.23/1.52    inference(superposition,[],[f26,f669])).
% 9.23/1.52  fof(f3781,plain,(
% 9.23/1.52    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1))) )),
% 9.23/1.52    inference(superposition,[],[f26,f16])).
% 9.23/1.52  fof(f257,plain,(
% 9.23/1.52    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),X2)) = k5_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 9.23/1.52    inference(superposition,[],[f22,f17])).
% 9.23/1.52  fof(f24277,plain,(
% 9.23/1.52    ( ! [X114,X115] : (k4_xboole_0(X114,X115) = k5_xboole_0(k4_xboole_0(X115,X114),k5_xboole_0(X114,X115))) )),
% 9.23/1.52    inference(superposition,[],[f24205,f13758])).
% 9.23/1.52  fof(f13758,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 9.23/1.52    inference(superposition,[],[f259,f6345])).
% 9.23/1.52  fof(f6345,plain,(
% 9.23/1.52    ( ! [X8,X7] : (k5_xboole_0(k3_xboole_0(X8,X7),k4_xboole_0(X7,X8)) = X7) )),
% 9.23/1.52    inference(backward_demodulation,[],[f57,f6302])).
% 9.23/1.52  fof(f6302,plain,(
% 9.23/1.52    ( ! [X2,X1] : (k2_xboole_0(k3_xboole_0(X2,X1),X1) = X1) )),
% 9.23/1.52    inference(superposition,[],[f6266,f16])).
% 9.23/1.52  fof(f6266,plain,(
% 9.23/1.52    ( ! [X2,X3] : (k2_xboole_0(k3_xboole_0(X2,X3),X2) = X2) )),
% 9.23/1.52    inference(backward_demodulation,[],[f33,f6265])).
% 9.23/1.52  fof(f6265,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 9.23/1.52    inference(backward_demodulation,[],[f3940,f6264])).
% 9.23/1.52  fof(f6264,plain,(
% 9.23/1.52    ( ! [X8,X9] : (k4_xboole_0(X8,X9) = k5_xboole_0(k3_xboole_0(X8,X9),X8)) )),
% 9.23/1.52    inference(forward_demodulation,[],[f6238,f5899])).
% 9.23/1.52  fof(f5899,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 9.23/1.52    inference(superposition,[],[f5838,f18])).
% 9.23/1.52  fof(f6238,plain,(
% 9.23/1.52    ( ! [X8,X9] : (k4_xboole_0(k4_xboole_0(X8,X9),k3_xboole_0(X8,X9)) = k5_xboole_0(k3_xboole_0(X8,X9),X8)) )),
% 9.23/1.52    inference(superposition,[],[f5293,f21])).
% 9.23/1.52  fof(f3940,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X1),X0)) = X0) )),
% 9.23/1.52    inference(superposition,[],[f3901,f21])).
% 9.23/1.52  fof(f33,plain,(
% 9.23/1.52    ( ! [X2,X3] : (k2_xboole_0(k3_xboole_0(X2,X3),X2) = k5_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3))) )),
% 9.23/1.52    inference(superposition,[],[f17,f20])).
% 9.23/1.52  fof(f57,plain,(
% 9.23/1.52    ( ! [X8,X7] : (k2_xboole_0(k3_xboole_0(X8,X7),X7) = k5_xboole_0(k3_xboole_0(X8,X7),k4_xboole_0(X7,X8))) )),
% 9.23/1.52    inference(superposition,[],[f17,f30])).
% 9.23/1.52  fof(f259,plain,(
% 9.23/1.52    ( ! [X6,X8,X7] : (k5_xboole_0(X6,k5_xboole_0(k3_xboole_0(X6,X7),X8)) = k5_xboole_0(k4_xboole_0(X6,X7),X8)) )),
% 9.23/1.52    inference(superposition,[],[f22,f19])).
% 9.23/1.52  fof(f24205,plain,(
% 9.23/1.52    ( ! [X4,X5] : (k5_xboole_0(X5,k5_xboole_0(X4,X5)) = X4) )),
% 9.23/1.52    inference(forward_demodulation,[],[f24010,f9296])).
% 9.23/1.52  fof(f9296,plain,(
% 9.23/1.52    ( ! [X0,X1] : (k5_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1) )),
% 9.23/1.52    inference(superposition,[],[f5227,f7843])).
% 9.23/1.52  fof(f7843,plain,(
% 9.23/1.52    ( ! [X2,X1] : (k4_xboole_0(X2,X1) = k5_xboole_0(k2_xboole_0(X2,X1),X1)) )),
% 9.23/1.52    inference(forward_demodulation,[],[f7797,f19])).
% 9.23/1.52  fof(f7797,plain,(
% 9.23/1.52    ( ! [X2,X1] : (k5_xboole_0(k2_xboole_0(X2,X1),X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))) )),
% 9.23/1.52    inference(superposition,[],[f257,f6450])).
% 9.23/1.52  fof(f6450,plain,(
% 9.23/1.52    ( ! [X2,X1] : (k3_xboole_0(X2,X1) = k5_xboole_0(k4_xboole_0(X1,X2),X1)) )),
% 9.23/1.52    inference(superposition,[],[f5227,f6255])).
% 9.23/1.52  fof(f24010,plain,(
% 9.23/1.52    ( ! [X4,X5] : (k5_xboole_0(k2_xboole_0(X5,X4),k4_xboole_0(X5,X4)) = k5_xboole_0(X5,k5_xboole_0(X4,X5))) )),
% 9.23/1.52    inference(superposition,[],[f257,f13758])).
% 9.23/1.52  fof(f15,plain,(
% 9.23/1.52    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 9.23/1.52    inference(cnf_transformation,[],[f14])).
% 9.23/1.52  fof(f14,plain,(
% 9.23/1.52    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 9.23/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 9.23/1.52  fof(f13,plain,(
% 9.23/1.52    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 9.23/1.52    introduced(choice_axiom,[])).
% 9.23/1.52  fof(f12,plain,(
% 9.23/1.52    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 9.23/1.52    inference(ennf_transformation,[],[f11])).
% 9.23/1.52  fof(f11,negated_conjecture,(
% 9.23/1.52    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 9.23/1.52    inference(negated_conjecture,[],[f10])).
% 9.23/1.52  fof(f10,conjecture,(
% 9.23/1.52    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 9.23/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 9.23/1.52  % SZS output end Proof for theBenchmark
% 9.23/1.52  % (30960)------------------------------
% 9.23/1.52  % (30960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.23/1.52  % (30960)Termination reason: Refutation
% 9.23/1.52  
% 9.23/1.52  % (30960)Memory used [KB]: 25585
% 9.23/1.52  % (30960)Time elapsed: 1.036 s
% 9.23/1.52  % (30960)------------------------------
% 9.23/1.52  % (30960)------------------------------
% 9.23/1.52  % (30943)Success in time 1.153 s
%------------------------------------------------------------------------------
