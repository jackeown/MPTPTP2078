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
% DateTime   : Thu Dec  3 12:32:26 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   89 (6129 expanded)
%              Number of leaves         :   11 (2043 expanded)
%              Depth                    :   37
%              Number of atoms          :   90 (6130 expanded)
%              Number of equality atoms :   89 (6129 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6483,plain,(
    $false ),
    inference(subsumption_resolution,[],[f16,f6482])).

fof(f6482,plain,(
    ! [X30,X31] : k5_xboole_0(X30,X31) = k4_xboole_0(k2_xboole_0(X30,X31),k3_xboole_0(X30,X31)) ),
    inference(forward_demodulation,[],[f6391,f2189])).

fof(f2189,plain,(
    ! [X23,X22] : k3_xboole_0(X22,X23) = k4_xboole_0(k3_xboole_0(X22,X23),k5_xboole_0(X22,X23)) ),
    inference(forward_demodulation,[],[f2188,f585])).

fof(f585,plain,(
    ! [X4,X3] : k3_xboole_0(X4,X3) = k5_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(backward_demodulation,[],[f76,f538])).

fof(f538,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f74,f537])).

fof(f537,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f89,f536])).

fof(f536,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(forward_demodulation,[],[f535,f327])).

fof(f327,plain,(
    ! [X3] : k2_xboole_0(k1_xboole_0,X3) = X3 ),
    inference(backward_demodulation,[],[f91,f321])).

fof(f321,plain,(
    ! [X0] : k2_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f184,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f184,plain,(
    ! [X0] : k2_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[],[f97,f74])).

fof(f97,plain,(
    ! [X3] : k2_xboole_0(k5_xboole_0(k1_xboole_0,X3),k3_xboole_0(X3,k1_xboole_0)) = X3 ),
    inference(forward_demodulation,[],[f94,f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f94,plain,(
    ! [X3] : k2_xboole_0(X3,k1_xboole_0) = k2_xboole_0(k5_xboole_0(k1_xboole_0,X3),k3_xboole_0(X3,k1_xboole_0)) ),
    inference(superposition,[],[f24,f74])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f91,plain,(
    ! [X3] : k2_xboole_0(k1_xboole_0,X3) = k2_xboole_0(k5_xboole_0(X3,k1_xboole_0),k3_xboole_0(k1_xboole_0,X3)) ),
    inference(superposition,[],[f24,f74])).

fof(f535,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f534,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f534,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f525,f74])).

fof(f525,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0)) = k5_xboole_0(k4_xboole_0(X1,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f58,f388])).

fof(f388,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f63,f331])).

fof(f331,plain,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(X3,k1_xboole_0),X3) ),
    inference(backward_demodulation,[],[f102,f327])).

fof(f102,plain,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(X3,k1_xboole_0),k2_xboole_0(k1_xboole_0,X3)) ),
    inference(superposition,[],[f96,f21])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f92,f17])).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f92,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f58,f74])).

fof(f63,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f26,f17])).

fof(f26,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f26,f17])).

fof(f89,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f58,f74])).

fof(f74,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f58,f17])).

fof(f76,plain,(
    ! [X4,X3] : k5_xboole_0(k1_xboole_0,k3_xboole_0(X4,X3)) = k5_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f58,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f22,f19])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f2188,plain,(
    ! [X23,X22] : k4_xboole_0(k3_xboole_0(X22,X23),k5_xboole_0(X22,X23)) = k5_xboole_0(X23,k4_xboole_0(X23,X22)) ),
    inference(forward_demodulation,[],[f2187,f691])).

fof(f691,plain,(
    ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(superposition,[],[f563,f671])).

fof(f671,plain,(
    ! [X8,X7] : k5_xboole_0(X8,k5_xboole_0(X7,X8)) = X7 ),
    inference(forward_demodulation,[],[f657,f537])).

fof(f657,plain,(
    ! [X8,X7] : k5_xboole_0(X7,k1_xboole_0) = k5_xboole_0(X8,k5_xboole_0(X7,X8)) ),
    inference(superposition,[],[f563,f63])).

fof(f563,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f58,f538])).

fof(f2187,plain,(
    ! [X23,X22] : k4_xboole_0(k3_xboole_0(X22,X23),k5_xboole_0(X22,X23)) = k5_xboole_0(k4_xboole_0(X23,X22),X23) ),
    inference(backward_demodulation,[],[f2156,f2162])).

fof(f2162,plain,(
    ! [X4,X2,X3] : k5_xboole_0(k4_xboole_0(X3,X2),X4) = k5_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X4)) ),
    inference(superposition,[],[f26,f861])).

fof(f861,plain,(
    ! [X6,X5] : k4_xboole_0(X6,X5) = k5_xboole_0(k2_xboole_0(X5,X6),X5) ),
    inference(superposition,[],[f685,f21])).

fof(f685,plain,(
    ! [X10,X9] : k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9 ),
    inference(superposition,[],[f671,f671])).

fof(f2156,plain,(
    ! [X23,X22] : k4_xboole_0(k3_xboole_0(X22,X23),k5_xboole_0(X22,X23)) = k5_xboole_0(k2_xboole_0(X22,X23),k5_xboole_0(X22,X23)) ),
    inference(superposition,[],[f861,f24])).

fof(f6391,plain,(
    ! [X30,X31] : k5_xboole_0(X30,X31) = k4_xboole_0(k2_xboole_0(X30,X31),k4_xboole_0(k3_xboole_0(X30,X31),k5_xboole_0(X30,X31))) ),
    inference(superposition,[],[f3877,f24])).

fof(f3877,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(forward_demodulation,[],[f3876,f938])).

fof(f938,plain,(
    ! [X12,X11] : k3_xboole_0(X11,k2_xboole_0(X11,X12)) = X11 ),
    inference(forward_demodulation,[],[f933,f608])).

fof(f608,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f562,f538])).

fof(f562,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f389,f537])).

fof(f389,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k4_xboole_0(X1,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f58,f331])).

fof(f933,plain,(
    ! [X12,X11] : k3_xboole_0(X11,k2_xboole_0(X11,X12)) = k4_xboole_0(X11,k1_xboole_0) ),
    inference(superposition,[],[f20,f845])).

fof(f845,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f839,f737])).

fof(f737,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f728,f18])).

fof(f728,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(backward_demodulation,[],[f28,f712])).

fof(f712,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1 ),
    inference(superposition,[],[f684,f22])).

fof(f684,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X7,X8),X8) = X7 ),
    inference(superposition,[],[f671,f563])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f21,f20])).

fof(f839,plain,(
    ! [X2,X1] : k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f25,f755])).

fof(f755,plain,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(X5,X5) ),
    inference(backward_demodulation,[],[f650,f742])).

fof(f742,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(X3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f593,f737])).

fof(f593,plain,(
    ! [X3] : k3_xboole_0(X3,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(backward_demodulation,[],[f478,f585])).

fof(f478,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)) ),
    inference(superposition,[],[f89,f303])).

fof(f303,plain,(
    ! [X4] : k4_xboole_0(k1_xboole_0,X4) = k5_xboole_0(k3_xboole_0(X4,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f302,f22])).

fof(f302,plain,(
    ! [X4] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X4)) = k5_xboole_0(k3_xboole_0(X4,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f279,f75])).

fof(f75,plain,(
    ! [X2,X1] : k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f58,f22])).

fof(f279,plain,(
    ! [X4] : k5_xboole_0(k3_xboole_0(X4,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X4)) ),
    inference(superposition,[],[f108,f29])).

fof(f108,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f58,f96])).

fof(f650,plain,(
    ! [X5] : k3_xboole_0(X5,k1_xboole_0) = k4_xboole_0(X5,X5) ),
    inference(superposition,[],[f20,f608])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f3876,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f3837,f19])).

fof(f3837,plain,(
    ! [X0,X1] : k3_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f20,f1026])).

fof(f1026,plain,(
    ! [X12,X13] : k4_xboole_0(k2_xboole_0(X12,X13),X12) = k4_xboole_0(X13,X12) ),
    inference(forward_demodulation,[],[f1016,f861])).

fof(f1016,plain,(
    ! [X12,X13] : k4_xboole_0(k2_xboole_0(X12,X13),X12) = k5_xboole_0(k2_xboole_0(X12,X13),X12) ),
    inference(superposition,[],[f29,f938])).

fof(f16,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:44:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (23967)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.45  % (23977)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.45  % (23975)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (23971)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (23979)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (23968)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (23972)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (23966)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (23965)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (23980)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (23970)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (23976)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (23969)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (23976)Refutation not found, incomplete strategy% (23976)------------------------------
% 0.20/0.49  % (23976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (23976)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (23976)Memory used [KB]: 10490
% 0.20/0.49  % (23976)Time elapsed: 0.070 s
% 0.20/0.49  % (23976)------------------------------
% 0.20/0.49  % (23976)------------------------------
% 0.20/0.49  % (23981)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.49  % (23973)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (23982)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (23974)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.50  % (23978)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 2.12/0.64  % (23981)Refutation found. Thanks to Tanya!
% 2.12/0.64  % SZS status Theorem for theBenchmark
% 2.12/0.64  % SZS output start Proof for theBenchmark
% 2.12/0.64  fof(f6483,plain,(
% 2.12/0.64    $false),
% 2.12/0.64    inference(subsumption_resolution,[],[f16,f6482])).
% 2.12/0.64  fof(f6482,plain,(
% 2.12/0.64    ( ! [X30,X31] : (k5_xboole_0(X30,X31) = k4_xboole_0(k2_xboole_0(X30,X31),k3_xboole_0(X30,X31))) )),
% 2.12/0.64    inference(forward_demodulation,[],[f6391,f2189])).
% 2.12/0.64  fof(f2189,plain,(
% 2.12/0.64    ( ! [X23,X22] : (k3_xboole_0(X22,X23) = k4_xboole_0(k3_xboole_0(X22,X23),k5_xboole_0(X22,X23))) )),
% 2.12/0.64    inference(forward_demodulation,[],[f2188,f585])).
% 2.12/0.64  fof(f585,plain,(
% 2.12/0.64    ( ! [X4,X3] : (k3_xboole_0(X4,X3) = k5_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 2.12/0.64    inference(backward_demodulation,[],[f76,f538])).
% 2.12/0.64  fof(f538,plain,(
% 2.12/0.64    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.12/0.64    inference(backward_demodulation,[],[f74,f537])).
% 2.12/0.64  fof(f537,plain,(
% 2.12/0.64    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.12/0.64    inference(backward_demodulation,[],[f89,f536])).
% 2.12/0.64  fof(f536,plain,(
% 2.12/0.64    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0)) = X1) )),
% 2.12/0.64    inference(forward_demodulation,[],[f535,f327])).
% 2.12/0.64  fof(f327,plain,(
% 2.12/0.64    ( ! [X3] : (k2_xboole_0(k1_xboole_0,X3) = X3) )),
% 2.12/0.64    inference(backward_demodulation,[],[f91,f321])).
% 2.12/0.64  fof(f321,plain,(
% 2.12/0.64    ( ! [X0] : (k2_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k1_xboole_0,X0)) = X0) )),
% 2.12/0.64    inference(superposition,[],[f184,f19])).
% 2.12/0.64  fof(f19,plain,(
% 2.12/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f1])).
% 2.12/0.64  fof(f1,axiom,(
% 2.12/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.12/0.64  fof(f184,plain,(
% 2.12/0.64    ( ! [X0] : (k2_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 2.12/0.64    inference(superposition,[],[f97,f74])).
% 2.12/0.64  fof(f97,plain,(
% 2.12/0.64    ( ! [X3] : (k2_xboole_0(k5_xboole_0(k1_xboole_0,X3),k3_xboole_0(X3,k1_xboole_0)) = X3) )),
% 2.12/0.64    inference(forward_demodulation,[],[f94,f18])).
% 2.12/0.64  fof(f18,plain,(
% 2.12/0.64    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.12/0.64    inference(cnf_transformation,[],[f3])).
% 2.12/0.64  fof(f3,axiom,(
% 2.12/0.64    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 2.12/0.64  fof(f94,plain,(
% 2.12/0.64    ( ! [X3] : (k2_xboole_0(X3,k1_xboole_0) = k2_xboole_0(k5_xboole_0(k1_xboole_0,X3),k3_xboole_0(X3,k1_xboole_0))) )),
% 2.12/0.64    inference(superposition,[],[f24,f74])).
% 2.12/0.64  fof(f24,plain,(
% 2.12/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.12/0.64    inference(cnf_transformation,[],[f9])).
% 2.12/0.64  fof(f9,axiom,(
% 2.12/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 2.12/0.64  fof(f91,plain,(
% 2.12/0.64    ( ! [X3] : (k2_xboole_0(k1_xboole_0,X3) = k2_xboole_0(k5_xboole_0(X3,k1_xboole_0),k3_xboole_0(k1_xboole_0,X3))) )),
% 2.12/0.64    inference(superposition,[],[f24,f74])).
% 2.12/0.64  fof(f535,plain,(
% 2.12/0.64    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,X1)) )),
% 2.12/0.64    inference(forward_demodulation,[],[f534,f21])).
% 2.12/0.64  fof(f21,plain,(
% 2.12/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.12/0.64    inference(cnf_transformation,[],[f10])).
% 2.12/0.64  fof(f10,axiom,(
% 2.12/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.12/0.64  fof(f534,plain,(
% 2.12/0.64    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0))) )),
% 2.12/0.64    inference(forward_demodulation,[],[f525,f74])).
% 2.12/0.64  fof(f525,plain,(
% 2.12/0.64    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0)) = k5_xboole_0(k4_xboole_0(X1,k1_xboole_0),k1_xboole_0)) )),
% 2.12/0.64    inference(superposition,[],[f58,f388])).
% 2.12/0.64  fof(f388,plain,(
% 2.12/0.64    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k1_xboole_0))) )),
% 2.12/0.64    inference(superposition,[],[f63,f331])).
% 2.12/0.64  fof(f331,plain,(
% 2.12/0.64    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(X3,k1_xboole_0),X3)) )),
% 2.12/0.64    inference(backward_demodulation,[],[f102,f327])).
% 2.12/0.64  fof(f102,plain,(
% 2.12/0.64    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(X3,k1_xboole_0),k2_xboole_0(k1_xboole_0,X3))) )),
% 2.12/0.64    inference(superposition,[],[f96,f21])).
% 2.12/0.64  fof(f96,plain,(
% 2.12/0.64    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))) )),
% 2.12/0.64    inference(forward_demodulation,[],[f92,f17])).
% 2.12/0.64  fof(f17,plain,(
% 2.12/0.64    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.12/0.64    inference(cnf_transformation,[],[f8])).
% 2.12/0.64  fof(f8,axiom,(
% 2.12/0.64    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.12/0.64  fof(f92,plain,(
% 2.12/0.64    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))) )),
% 2.12/0.64    inference(superposition,[],[f58,f74])).
% 2.12/0.64  fof(f63,plain,(
% 2.12/0.64    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 2.12/0.64    inference(superposition,[],[f26,f17])).
% 2.12/0.64  fof(f26,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.12/0.64    inference(cnf_transformation,[],[f7])).
% 2.12/0.64  fof(f7,axiom,(
% 2.12/0.64    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.12/0.64  fof(f58,plain,(
% 2.12/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 2.12/0.64    inference(superposition,[],[f26,f17])).
% 2.12/0.64  fof(f89,plain,(
% 2.12/0.64    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) )),
% 2.12/0.64    inference(superposition,[],[f58,f74])).
% 2.12/0.64  fof(f74,plain,(
% 2.12/0.64    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 2.12/0.64    inference(superposition,[],[f58,f17])).
% 2.12/0.64  fof(f76,plain,(
% 2.12/0.64    ( ! [X4,X3] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(X4,X3)) = k5_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 2.12/0.64    inference(superposition,[],[f58,f29])).
% 2.12/0.64  fof(f29,plain,(
% 2.12/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 2.12/0.64    inference(superposition,[],[f22,f19])).
% 2.12/0.64  fof(f22,plain,(
% 2.12/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.12/0.64    inference(cnf_transformation,[],[f2])).
% 2.12/0.64  fof(f2,axiom,(
% 2.12/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.12/0.64  fof(f2188,plain,(
% 2.12/0.64    ( ! [X23,X22] : (k4_xboole_0(k3_xboole_0(X22,X23),k5_xboole_0(X22,X23)) = k5_xboole_0(X23,k4_xboole_0(X23,X22))) )),
% 2.12/0.64    inference(forward_demodulation,[],[f2187,f691])).
% 2.12/0.64  fof(f691,plain,(
% 2.12/0.64    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) )),
% 2.12/0.64    inference(superposition,[],[f563,f671])).
% 2.12/0.64  fof(f671,plain,(
% 2.12/0.64    ( ! [X8,X7] : (k5_xboole_0(X8,k5_xboole_0(X7,X8)) = X7) )),
% 2.12/0.64    inference(forward_demodulation,[],[f657,f537])).
% 2.12/0.64  fof(f657,plain,(
% 2.12/0.64    ( ! [X8,X7] : (k5_xboole_0(X7,k1_xboole_0) = k5_xboole_0(X8,k5_xboole_0(X7,X8))) )),
% 2.12/0.64    inference(superposition,[],[f563,f63])).
% 2.12/0.64  fof(f563,plain,(
% 2.12/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.12/0.64    inference(backward_demodulation,[],[f58,f538])).
% 2.12/0.64  fof(f2187,plain,(
% 2.12/0.64    ( ! [X23,X22] : (k4_xboole_0(k3_xboole_0(X22,X23),k5_xboole_0(X22,X23)) = k5_xboole_0(k4_xboole_0(X23,X22),X23)) )),
% 2.12/0.64    inference(backward_demodulation,[],[f2156,f2162])).
% 2.12/0.64  fof(f2162,plain,(
% 2.12/0.64    ( ! [X4,X2,X3] : (k5_xboole_0(k4_xboole_0(X3,X2),X4) = k5_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X4))) )),
% 2.12/0.64    inference(superposition,[],[f26,f861])).
% 2.12/0.64  fof(f861,plain,(
% 2.12/0.64    ( ! [X6,X5] : (k4_xboole_0(X6,X5) = k5_xboole_0(k2_xboole_0(X5,X6),X5)) )),
% 2.12/0.64    inference(superposition,[],[f685,f21])).
% 2.12/0.64  fof(f685,plain,(
% 2.12/0.64    ( ! [X10,X9] : (k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9) )),
% 2.12/0.64    inference(superposition,[],[f671,f671])).
% 2.12/0.64  fof(f2156,plain,(
% 2.12/0.64    ( ! [X23,X22] : (k4_xboole_0(k3_xboole_0(X22,X23),k5_xboole_0(X22,X23)) = k5_xboole_0(k2_xboole_0(X22,X23),k5_xboole_0(X22,X23))) )),
% 2.12/0.64    inference(superposition,[],[f861,f24])).
% 2.12/0.64  fof(f6391,plain,(
% 2.12/0.64    ( ! [X30,X31] : (k5_xboole_0(X30,X31) = k4_xboole_0(k2_xboole_0(X30,X31),k4_xboole_0(k3_xboole_0(X30,X31),k5_xboole_0(X30,X31)))) )),
% 2.12/0.64    inference(superposition,[],[f3877,f24])).
% 2.12/0.64  fof(f3877,plain,(
% 2.12/0.64    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0) )),
% 2.12/0.64    inference(forward_demodulation,[],[f3876,f938])).
% 2.12/0.64  fof(f938,plain,(
% 2.12/0.64    ( ! [X12,X11] : (k3_xboole_0(X11,k2_xboole_0(X11,X12)) = X11) )),
% 2.12/0.64    inference(forward_demodulation,[],[f933,f608])).
% 2.12/0.64  fof(f608,plain,(
% 2.12/0.64    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 2.12/0.64    inference(forward_demodulation,[],[f562,f538])).
% 2.12/0.64  fof(f562,plain,(
% 2.12/0.64    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X1,k1_xboole_0)) )),
% 2.12/0.64    inference(backward_demodulation,[],[f389,f537])).
% 2.12/0.64  fof(f389,plain,(
% 2.12/0.64    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k4_xboole_0(X1,k1_xboole_0),k1_xboole_0)) )),
% 2.12/0.64    inference(superposition,[],[f58,f331])).
% 2.12/0.64  fof(f933,plain,(
% 2.12/0.64    ( ! [X12,X11] : (k3_xboole_0(X11,k2_xboole_0(X11,X12)) = k4_xboole_0(X11,k1_xboole_0)) )),
% 2.12/0.64    inference(superposition,[],[f20,f845])).
% 2.12/0.64  fof(f845,plain,(
% 2.12/0.64    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X1,X2))) )),
% 2.12/0.64    inference(forward_demodulation,[],[f839,f737])).
% 2.12/0.64  fof(f737,plain,(
% 2.12/0.64    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) )),
% 2.12/0.64    inference(superposition,[],[f728,f18])).
% 2.12/0.64  fof(f728,plain,(
% 2.12/0.64    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 2.12/0.64    inference(backward_demodulation,[],[f28,f712])).
% 2.12/0.64  fof(f712,plain,(
% 2.12/0.64    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1) )),
% 2.12/0.64    inference(superposition,[],[f684,f22])).
% 2.12/0.64  fof(f684,plain,(
% 2.12/0.64    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X7,X8),X8) = X7) )),
% 2.12/0.64    inference(superposition,[],[f671,f563])).
% 2.12/0.64  fof(f28,plain,(
% 2.12/0.64    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.12/0.64    inference(superposition,[],[f21,f20])).
% 2.12/0.64  fof(f839,plain,(
% 2.12/0.64    ( ! [X2,X1] : (k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X1,k2_xboole_0(X1,X2))) )),
% 2.12/0.64    inference(superposition,[],[f25,f755])).
% 2.12/0.64  fof(f755,plain,(
% 2.12/0.64    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(X5,X5)) )),
% 2.12/0.64    inference(backward_demodulation,[],[f650,f742])).
% 2.12/0.64  fof(f742,plain,(
% 2.12/0.64    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(X3,k1_xboole_0)) )),
% 2.12/0.64    inference(backward_demodulation,[],[f593,f737])).
% 2.12/0.64  fof(f593,plain,(
% 2.12/0.64    ( ! [X3] : (k3_xboole_0(X3,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X3)) )),
% 2.12/0.64    inference(backward_demodulation,[],[f478,f585])).
% 2.12/0.64  fof(f478,plain,(
% 2.12/0.64    ( ! [X3] : (k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))) )),
% 2.12/0.64    inference(superposition,[],[f89,f303])).
% 2.12/0.64  fof(f303,plain,(
% 2.12/0.64    ( ! [X4] : (k4_xboole_0(k1_xboole_0,X4) = k5_xboole_0(k3_xboole_0(X4,k1_xboole_0),k1_xboole_0)) )),
% 2.12/0.64    inference(forward_demodulation,[],[f302,f22])).
% 2.12/0.64  fof(f302,plain,(
% 2.12/0.64    ( ! [X4] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X4)) = k5_xboole_0(k3_xboole_0(X4,k1_xboole_0),k1_xboole_0)) )),
% 2.12/0.64    inference(forward_demodulation,[],[f279,f75])).
% 2.12/0.64  fof(f75,plain,(
% 2.12/0.64    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 2.12/0.64    inference(superposition,[],[f58,f22])).
% 2.12/0.64  fof(f279,plain,(
% 2.12/0.64    ( ! [X4] : (k5_xboole_0(k3_xboole_0(X4,k1_xboole_0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X4))) )),
% 2.12/0.64    inference(superposition,[],[f108,f29])).
% 2.12/0.64  fof(f108,plain,(
% 2.12/0.64    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 2.12/0.64    inference(superposition,[],[f58,f96])).
% 2.12/0.64  fof(f650,plain,(
% 2.12/0.64    ( ! [X5] : (k3_xboole_0(X5,k1_xboole_0) = k4_xboole_0(X5,X5)) )),
% 2.12/0.64    inference(superposition,[],[f20,f608])).
% 2.12/0.64  fof(f25,plain,(
% 2.12/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.12/0.64    inference(cnf_transformation,[],[f4])).
% 2.12/0.64  fof(f4,axiom,(
% 2.12/0.64    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.12/0.64  fof(f20,plain,(
% 2.12/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.12/0.64    inference(cnf_transformation,[],[f5])).
% 2.12/0.64  fof(f5,axiom,(
% 2.12/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.12/0.64  fof(f3876,plain,(
% 2.12/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 2.12/0.64    inference(forward_demodulation,[],[f3837,f19])).
% 2.12/0.64  fof(f3837,plain,(
% 2.12/0.64    ( ! [X0,X1] : (k3_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 2.12/0.64    inference(superposition,[],[f20,f1026])).
% 2.12/0.64  fof(f1026,plain,(
% 2.12/0.64    ( ! [X12,X13] : (k4_xboole_0(k2_xboole_0(X12,X13),X12) = k4_xboole_0(X13,X12)) )),
% 2.12/0.64    inference(forward_demodulation,[],[f1016,f861])).
% 2.12/0.64  fof(f1016,plain,(
% 2.12/0.64    ( ! [X12,X13] : (k4_xboole_0(k2_xboole_0(X12,X13),X12) = k5_xboole_0(k2_xboole_0(X12,X13),X12)) )),
% 2.12/0.64    inference(superposition,[],[f29,f938])).
% 2.12/0.64  fof(f16,plain,(
% 2.12/0.64    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.12/0.64    inference(cnf_transformation,[],[f15])).
% 2.12/0.64  fof(f15,plain,(
% 2.12/0.64    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.12/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 2.12/0.64  fof(f14,plain,(
% 2.12/0.64    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.12/0.64    introduced(choice_axiom,[])).
% 2.12/0.64  fof(f13,plain,(
% 2.12/0.64    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.12/0.64    inference(ennf_transformation,[],[f12])).
% 2.12/0.64  fof(f12,negated_conjecture,(
% 2.12/0.64    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.12/0.64    inference(negated_conjecture,[],[f11])).
% 2.12/0.64  fof(f11,conjecture,(
% 2.12/0.64    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 2.12/0.64  % SZS output end Proof for theBenchmark
% 2.12/0.64  % (23981)------------------------------
% 2.12/0.64  % (23981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.64  % (23981)Termination reason: Refutation
% 2.12/0.64  
% 2.12/0.64  % (23981)Memory used [KB]: 9083
% 2.12/0.64  % (23981)Time elapsed: 0.167 s
% 2.12/0.64  % (23981)------------------------------
% 2.12/0.64  % (23981)------------------------------
% 2.12/0.64  % (23961)Success in time 0.286 s
%------------------------------------------------------------------------------
