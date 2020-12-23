%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:21 EST 2020

% Result     : Theorem 42.40s
% Output     : Refutation 42.40s
% Verified   : 
% Statistics : Number of formulae       :  125 (11082 expanded)
%              Number of leaves         :   16 (3891 expanded)
%              Depth                    :   39
%              Number of atoms          :  134 (11095 expanded)
%              Number of equality atoms :  119 (11076 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71615,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f56,f57,f339,f71508])).

fof(f71508,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f71507])).

fof(f71507,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f338,f71506])).

fof(f71506,plain,(
    ! [X313,X312] : k5_xboole_0(X312,X313) = k4_xboole_0(k5_xboole_0(X312,k4_xboole_0(X313,X312)),k5_xboole_0(X312,k4_xboole_0(X312,X313))) ),
    inference(forward_demodulation,[],[f71112,f71294])).

fof(f71294,plain,(
    ! [X66,X67] : k5_xboole_0(X66,k4_xboole_0(X66,X67)) = k4_xboole_0(X66,k5_xboole_0(X66,X67)) ),
    inference(forward_demodulation,[],[f71293,f1011])).

fof(f1011,plain,(
    ! [X30,X31,X32] : k5_xboole_0(X30,k5_xboole_0(X32,k5_xboole_0(X31,k4_xboole_0(X31,X30)))) = k5_xboole_0(X32,k4_xboole_0(X30,X31)) ),
    inference(superposition,[],[f436,f325])).

fof(f325,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(backward_demodulation,[],[f88,f312])).

fof(f312,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k5_xboole_0(X7,k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f262,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f262,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f260,f42])).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f21,f19])).

fof(f19,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f260,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f28,f240])).

fof(f240,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5) ),
    inference(backward_demodulation,[],[f200,f215])).

fof(f215,plain,(
    ! [X10] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X10) ),
    inference(superposition,[],[f186,f111])).

fof(f111,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f107,f31])).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f18,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f107,plain,(
    ! [X2] : k5_xboole_0(X2,k4_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f29,f86])).

fof(f86,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f32,f76])).

fof(f76,plain,(
    ! [X6] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6)) ),
    inference(superposition,[],[f29,f42])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f24,f24])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f186,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2 ),
    inference(superposition,[],[f41,f29])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    inference(backward_demodulation,[],[f33,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f26,f24,f24])).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    inference(definition_unfolding,[],[f22,f23,f24])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f200,plain,(
    ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X5,X5) ),
    inference(backward_demodulation,[],[f108,f186])).

fof(f108,plain,(
    ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k1_xboole_0,X5))) ),
    inference(superposition,[],[f29,f86])).

fof(f28,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f88,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f29,f32])).

fof(f436,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X4,k5_xboole_0(X3,X5)) = k5_xboole_0(X3,k5_xboole_0(X4,X5)) ),
    inference(superposition,[],[f60,f28])).

fof(f60,plain,(
    ! [X4,X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_xboole_0(X3,X2),X4) ),
    inference(superposition,[],[f28,f21])).

fof(f71293,plain,(
    ! [X66,X67] : k4_xboole_0(X66,k5_xboole_0(X66,X67)) = k5_xboole_0(X66,k5_xboole_0(X66,k5_xboole_0(X67,k4_xboole_0(X67,X66)))) ),
    inference(forward_demodulation,[],[f71024,f28])).

fof(f71024,plain,(
    ! [X66,X67] : k4_xboole_0(X66,k5_xboole_0(X66,X67)) = k5_xboole_0(X66,k5_xboole_0(k5_xboole_0(X66,X67),k4_xboole_0(X67,X66))) ),
    inference(superposition,[],[f325,f68068])).

fof(f68068,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f67916,f21])).

fof(f67916,plain,(
    ! [X204,X205] : k4_xboole_0(X204,X205) = k4_xboole_0(k5_xboole_0(X204,X205),X205) ),
    inference(forward_demodulation,[],[f67915,f900])).

fof(f900,plain,(
    ! [X6,X7,X5] : k4_xboole_0(X7,X5) = k4_xboole_0(k4_xboole_0(X7,X5),k4_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f888,f19])).

fof(f888,plain,(
    ! [X6,X7,X5] : k4_xboole_0(k4_xboole_0(X7,X5),k4_xboole_0(X5,X6)) = k4_xboole_0(X7,k5_xboole_0(X5,k1_xboole_0)) ),
    inference(superposition,[],[f35,f841])).

fof(f841,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),X4) ),
    inference(forward_demodulation,[],[f840,f240])).

fof(f840,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X4,X5),X4) = k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f839,f325])).

fof(f839,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X4,X5),X4) = k5_xboole_0(k4_xboole_0(X4,X5),k5_xboole_0(X4,k5_xboole_0(X5,k4_xboole_0(X5,X4)))) ),
    inference(forward_demodulation,[],[f808,f312])).

fof(f808,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X4,X5),X4) = k5_xboole_0(k4_xboole_0(X4,X5),k5_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X5,X4)))) ),
    inference(superposition,[],[f325,f32])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f27,f23])).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f67915,plain,(
    ! [X204,X205] : k4_xboole_0(k4_xboole_0(X204,X205),k4_xboole_0(X205,k4_xboole_0(X205,X204))) = k4_xboole_0(k5_xboole_0(X204,X205),X205) ),
    inference(forward_demodulation,[],[f67914,f5957])).

fof(f5957,plain,(
    ! [X8,X7] : k4_xboole_0(k5_xboole_0(X8,X7),X7) = k5_xboole_0(X8,k4_xboole_0(X7,k5_xboole_0(X8,X7))) ),
    inference(superposition,[],[f3969,f310])).

fof(f310,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f262,f21])).

fof(f3969,plain,(
    ! [X14,X15] : k4_xboole_0(X15,X14) = k5_xboole_0(k5_xboole_0(X14,X15),k4_xboole_0(X14,X15)) ),
    inference(superposition,[],[f2140,f652])).

fof(f652,plain,(
    ! [X23,X21,X22] : k5_xboole_0(k5_xboole_0(X21,X22),X23) = k5_xboole_0(X23,k5_xboole_0(X22,X21)) ),
    inference(forward_demodulation,[],[f633,f19])).

fof(f633,plain,(
    ! [X23,X21,X22] : k5_xboole_0(X23,k5_xboole_0(X22,X21)) = k5_xboole_0(k5_xboole_0(X21,X22),k5_xboole_0(X23,k1_xboole_0)) ),
    inference(superposition,[],[f66,f512])).

fof(f512,plain,(
    ! [X24,X25] : k5_xboole_0(X25,X24) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X24,X25)) ),
    inference(superposition,[],[f66,f42])).

fof(f66,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f28,f21])).

fof(f2140,plain,(
    ! [X6,X5] : k4_xboole_0(X6,X5) = k5_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(X6,X5)) ),
    inference(superposition,[],[f863,f497])).

fof(f497,plain,(
    ! [X14,X12,X13] : k5_xboole_0(X14,k5_xboole_0(X12,X13)) = k5_xboole_0(k5_xboole_0(X13,X14),X12) ),
    inference(superposition,[],[f66,f21])).

fof(f863,plain,(
    ! [X30,X29] : k4_xboole_0(X29,X30) = k5_xboole_0(k5_xboole_0(X30,k4_xboole_0(X30,X29)),X29) ),
    inference(forward_demodulation,[],[f831,f42])).

fof(f831,plain,(
    ! [X30,X29] : k5_xboole_0(k5_xboole_0(X30,k4_xboole_0(X30,X29)),X29) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X29,X30)) ),
    inference(superposition,[],[f512,f325])).

fof(f67914,plain,(
    ! [X204,X205] : k4_xboole_0(k4_xboole_0(X204,X205),k4_xboole_0(X205,k4_xboole_0(X205,X204))) = k5_xboole_0(X204,k4_xboole_0(X205,k5_xboole_0(X204,X205))) ),
    inference(forward_demodulation,[],[f67913,f21])).

fof(f67913,plain,(
    ! [X204,X205] : k4_xboole_0(k4_xboole_0(X204,X205),k4_xboole_0(X205,k4_xboole_0(X205,X204))) = k5_xboole_0(k4_xboole_0(X205,k5_xboole_0(X204,X205)),X204) ),
    inference(forward_demodulation,[],[f67912,f3989])).

fof(f3989,plain,(
    ! [X35,X34] : k5_xboole_0(X35,X34) = k5_xboole_0(k4_xboole_0(X34,X35),k4_xboole_0(X35,X34)) ),
    inference(superposition,[],[f262,f2140])).

fof(f67912,plain,(
    ! [X204,X205] : k4_xboole_0(k4_xboole_0(X204,X205),k4_xboole_0(X205,k4_xboole_0(X205,X204))) = k5_xboole_0(k4_xboole_0(X205,k5_xboole_0(k4_xboole_0(X205,X204),k4_xboole_0(X204,X205))),X204) ),
    inference(forward_demodulation,[],[f67650,f2463])).

fof(f2463,plain,(
    ! [X26,X24,X23,X25] : k4_xboole_0(k4_xboole_0(X26,k4_xboole_0(X24,X25)),k4_xboole_0(X23,X24)) = k4_xboole_0(X26,k5_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(X23,X24))) ),
    inference(superposition,[],[f35,f900])).

fof(f67650,plain,(
    ! [X204,X205] : k4_xboole_0(k4_xboole_0(X204,X205),k4_xboole_0(X205,k4_xboole_0(X205,X204))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X205,k4_xboole_0(X205,X204)),k4_xboole_0(X204,X205)),X204) ),
    inference(superposition,[],[f3934,f53795])).

fof(f53795,plain,(
    ! [X4,X3] : k4_xboole_0(X4,k4_xboole_0(X4,X3)) = k5_xboole_0(k4_xboole_0(X3,X4),X3) ),
    inference(superposition,[],[f3691,f642])).

fof(f642,plain,(
    ! [X17,X18] : k5_xboole_0(X18,X17) = k5_xboole_0(k5_xboole_0(X17,X18),k1_xboole_0) ),
    inference(forward_demodulation,[],[f615,f42])).

fof(f615,plain,(
    ! [X17,X18] : k5_xboole_0(k5_xboole_0(X17,X18),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X18,X17)) ),
    inference(superposition,[],[f512,f512])).

fof(f3691,plain,(
    ! [X24,X23] : k4_xboole_0(X24,k4_xboole_0(X24,X23)) = k5_xboole_0(k5_xboole_0(X23,k4_xboole_0(X23,X24)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3584,f996])).

fof(f996,plain,(
    ! [X12,X11] : k4_xboole_0(X12,X11) = k4_xboole_0(X12,k5_xboole_0(X11,k4_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f995,f325])).

fof(f995,plain,(
    ! [X12,X11] : k4_xboole_0(X12,k5_xboole_0(X11,k4_xboole_0(X11,X12))) = k5_xboole_0(X12,k5_xboole_0(X11,k4_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f972,f19])).

fof(f972,plain,(
    ! [X12,X11] : k4_xboole_0(X12,k5_xboole_0(X11,k4_xboole_0(X11,X12))) = k5_xboole_0(X12,k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(X11,X12)),k1_xboole_0)) ),
    inference(superposition,[],[f325,f894])).

fof(f894,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X5,X4)),X4) ),
    inference(forward_demodulation,[],[f875,f312])).

fof(f875,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4) ),
    inference(superposition,[],[f841,f32])).

fof(f3584,plain,(
    ! [X24,X23] : k5_xboole_0(k5_xboole_0(X23,k4_xboole_0(X23,X24)),k1_xboole_0) = k4_xboole_0(X24,k4_xboole_0(X24,k5_xboole_0(X23,k4_xboole_0(X23,X24)))) ),
    inference(superposition,[],[f997,f894])).

fof(f997,plain,(
    ! [X0,X1] : k4_xboole_0(X1,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f992,f996])).

fof(f992,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(forward_demodulation,[],[f967,f111])).

fof(f967,plain,(
    ! [X0,X1] : k4_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) ),
    inference(superposition,[],[f32,f894])).

fof(f3934,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k5_xboole_0(X5,X6)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X5,X6),X5),X6) ),
    inference(superposition,[],[f2140,f262])).

fof(f71112,plain,(
    ! [X313,X312] : k5_xboole_0(X312,X313) = k4_xboole_0(k5_xboole_0(X312,k4_xboole_0(X313,X312)),k4_xboole_0(X312,k5_xboole_0(X312,X313))) ),
    inference(superposition,[],[f6525,f68068])).

fof(f6525,plain,(
    ! [X4,X5] : k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X4,X5)) = X5 ),
    inference(forward_demodulation,[],[f6524,f186])).

fof(f6524,plain,(
    ! [X4,X5] : k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X4,X5)) = k4_xboole_0(X5,k4_xboole_0(k4_xboole_0(X5,X4),X5)) ),
    inference(forward_demodulation,[],[f6416,f35])).

fof(f6416,plain,(
    ! [X4,X5] : k4_xboole_0(X5,k4_xboole_0(X5,k5_xboole_0(X4,k4_xboole_0(X5,X4)))) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f32,f4061])).

fof(f4061,plain,(
    ! [X68,X69] : k4_xboole_0(X68,X69) = k4_xboole_0(k5_xboole_0(X68,k4_xboole_0(X69,X68)),X69) ),
    inference(forward_demodulation,[],[f4060,f42])).

fof(f4060,plain,(
    ! [X68,X69] : k4_xboole_0(k5_xboole_0(X68,k4_xboole_0(X69,X68)),X69) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X68,X69)) ),
    inference(forward_demodulation,[],[f4059,f841])).

fof(f4059,plain,(
    ! [X68,X69] : k4_xboole_0(k5_xboole_0(X68,k4_xboole_0(X69,X68)),X69) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X69,X68),X69),k4_xboole_0(X68,X69)) ),
    inference(forward_demodulation,[],[f3959,f35])).

fof(f3959,plain,(
    ! [X68,X69] : k4_xboole_0(k5_xboole_0(X68,k4_xboole_0(X69,X68)),X69) = k5_xboole_0(k4_xboole_0(X69,k5_xboole_0(X68,k4_xboole_0(X69,X68))),k4_xboole_0(X68,X69)) ),
    inference(superposition,[],[f2140,f1612])).

fof(f1612,plain,(
    ! [X54,X53] : k4_xboole_0(X54,X53) = k5_xboole_0(k5_xboole_0(X54,k4_xboole_0(X53,X54)),X53) ),
    inference(forward_demodulation,[],[f1574,f42])).

fof(f1574,plain,(
    ! [X54,X53] : k5_xboole_0(k5_xboole_0(X54,k4_xboole_0(X53,X54)),X53) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X54,X53)) ),
    inference(superposition,[],[f512,f855])).

fof(f855,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k5_xboole_0(X4,k5_xboole_0(X3,k4_xboole_0(X4,X3))) ),
    inference(forward_demodulation,[],[f817,f21])).

fof(f817,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k5_xboole_0(X4,k5_xboole_0(k4_xboole_0(X4,X3),X3)) ),
    inference(superposition,[],[f325,f66])).

fof(f338,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl2_3
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f339,plain,
    ( ~ spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f330,f37,f336])).

fof(f37,plain,
    ( spl2_1
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f330,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(backward_demodulation,[],[f39,f312])).

fof(f39,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f57,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f51,f53])).

fof(f53,plain,
    ( spl2_2
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f51,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f42,f31])).

fof(f56,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f50,f53])).

fof(f50,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f31,f42])).

fof(f40,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f30,f37])).

fof(f30,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f17,f23,f24])).

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
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:44:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (13933)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (13938)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (13928)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (13929)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (13932)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (13941)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (13931)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (13930)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (13939)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.52  % (13936)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (13937)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.52  % (13940)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.52  % (13937)Refutation not found, incomplete strategy% (13937)------------------------------
% 0.21/0.52  % (13937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13937)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13937)Memory used [KB]: 10490
% 0.21/0.52  % (13937)Time elapsed: 0.084 s
% 0.21/0.52  % (13937)------------------------------
% 0.21/0.52  % (13937)------------------------------
% 0.21/0.55  % (13926)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.56  % (13943)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.48/0.56  % (13934)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.48/0.56  % (13935)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.48/0.57  % (13942)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.48/0.57  % (13927)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 5.57/1.09  % (13930)Time limit reached!
% 5.57/1.09  % (13930)------------------------------
% 5.57/1.09  % (13930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.57/1.10  % (13930)Termination reason: Time limit
% 5.57/1.10  % (13930)Termination phase: Saturation
% 5.57/1.10  
% 5.57/1.10  % (13930)Memory used [KB]: 21492
% 5.57/1.10  % (13930)Time elapsed: 0.600 s
% 5.57/1.10  % (13930)------------------------------
% 5.57/1.10  % (13930)------------------------------
% 12.76/1.98  % (13932)Time limit reached!
% 12.76/1.98  % (13932)------------------------------
% 12.76/1.98  % (13932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.76/1.98  % (13932)Termination reason: Time limit
% 12.76/1.98  
% 12.76/1.98  % (13932)Memory used [KB]: 42728
% 12.76/1.98  % (13932)Time elapsed: 1.524 s
% 12.76/1.98  % (13932)------------------------------
% 12.76/1.98  % (13932)------------------------------
% 12.76/2.02  % (13931)Time limit reached!
% 12.76/2.02  % (13931)------------------------------
% 12.76/2.02  % (13931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.76/2.03  % (13931)Termination reason: Time limit
% 12.76/2.03  % (13931)Termination phase: Saturation
% 12.76/2.03  
% 12.76/2.03  % (13931)Memory used [KB]: 42728
% 12.76/2.03  % (13931)Time elapsed: 1.500 s
% 12.76/2.03  % (13931)------------------------------
% 12.76/2.03  % (13931)------------------------------
% 14.78/2.27  % (13928)Time limit reached!
% 14.78/2.27  % (13928)------------------------------
% 14.78/2.27  % (13928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.78/2.27  % (13928)Termination reason: Time limit
% 14.78/2.27  
% 14.78/2.27  % (13928)Memory used [KB]: 42344
% 14.78/2.27  % (13928)Time elapsed: 1.834 s
% 14.78/2.27  % (13928)------------------------------
% 14.78/2.27  % (13928)------------------------------
% 17.66/2.65  % (13938)Time limit reached!
% 17.66/2.65  % (13938)------------------------------
% 17.66/2.65  % (13938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.66/2.65  % (13938)Termination reason: Time limit
% 18.28/2.65  % (13938)Termination phase: Saturation
% 18.28/2.65  
% 18.28/2.65  % (13938)Memory used [KB]: 46182
% 18.28/2.65  % (13938)Time elapsed: 2.200 s
% 18.28/2.65  % (13938)------------------------------
% 18.28/2.65  % (13938)------------------------------
% 42.40/5.68  % (13936)Refutation found. Thanks to Tanya!
% 42.40/5.68  % SZS status Theorem for theBenchmark
% 42.40/5.68  % SZS output start Proof for theBenchmark
% 42.40/5.68  fof(f71615,plain,(
% 42.40/5.68    $false),
% 42.40/5.68    inference(avatar_sat_refutation,[],[f40,f56,f57,f339,f71508])).
% 42.40/5.68  fof(f71508,plain,(
% 42.40/5.68    spl2_3),
% 42.40/5.68    inference(avatar_contradiction_clause,[],[f71507])).
% 42.40/5.68  fof(f71507,plain,(
% 42.40/5.68    $false | spl2_3),
% 42.40/5.68    inference(subsumption_resolution,[],[f338,f71506])).
% 42.40/5.68  fof(f71506,plain,(
% 42.40/5.68    ( ! [X313,X312] : (k5_xboole_0(X312,X313) = k4_xboole_0(k5_xboole_0(X312,k4_xboole_0(X313,X312)),k5_xboole_0(X312,k4_xboole_0(X312,X313)))) )),
% 42.40/5.68    inference(forward_demodulation,[],[f71112,f71294])).
% 42.40/5.68  fof(f71294,plain,(
% 42.40/5.68    ( ! [X66,X67] : (k5_xboole_0(X66,k4_xboole_0(X66,X67)) = k4_xboole_0(X66,k5_xboole_0(X66,X67))) )),
% 42.40/5.68    inference(forward_demodulation,[],[f71293,f1011])).
% 42.40/5.68  fof(f1011,plain,(
% 42.40/5.68    ( ! [X30,X31,X32] : (k5_xboole_0(X30,k5_xboole_0(X32,k5_xboole_0(X31,k4_xboole_0(X31,X30)))) = k5_xboole_0(X32,k4_xboole_0(X30,X31))) )),
% 42.40/5.68    inference(superposition,[],[f436,f325])).
% 42.40/5.68  fof(f325,plain,(
% 42.40/5.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 42.40/5.68    inference(backward_demodulation,[],[f88,f312])).
% 42.40/5.68  fof(f312,plain,(
% 42.40/5.68    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k5_xboole_0(X7,k4_xboole_0(X7,X8))) )),
% 42.40/5.68    inference(superposition,[],[f262,f29])).
% 42.40/5.68  fof(f29,plain,(
% 42.40/5.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 42.40/5.68    inference(definition_unfolding,[],[f25,f24])).
% 42.40/5.68  fof(f24,plain,(
% 42.40/5.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 42.40/5.68    inference(cnf_transformation,[],[f7])).
% 42.40/5.68  fof(f7,axiom,(
% 42.40/5.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 42.40/5.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 42.40/5.68  fof(f25,plain,(
% 42.40/5.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 42.40/5.68    inference(cnf_transformation,[],[f3])).
% 42.40/5.68  fof(f3,axiom,(
% 42.40/5.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 42.40/5.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 42.40/5.68  fof(f262,plain,(
% 42.40/5.68    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 42.40/5.68    inference(forward_demodulation,[],[f260,f42])).
% 42.40/5.68  fof(f42,plain,(
% 42.40/5.68    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 42.40/5.68    inference(superposition,[],[f21,f19])).
% 42.40/5.68  fof(f19,plain,(
% 42.40/5.68    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 42.40/5.68    inference(cnf_transformation,[],[f9])).
% 42.40/5.68  fof(f9,axiom,(
% 42.40/5.68    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 42.40/5.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 42.40/5.68  fof(f21,plain,(
% 42.40/5.68    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 42.40/5.68    inference(cnf_transformation,[],[f2])).
% 42.40/5.68  fof(f2,axiom,(
% 42.40/5.68    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 42.40/5.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 42.40/5.68  fof(f260,plain,(
% 42.40/5.68    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 42.40/5.68    inference(superposition,[],[f28,f240])).
% 42.40/5.68  fof(f240,plain,(
% 42.40/5.68    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,X5)) )),
% 42.40/5.68    inference(backward_demodulation,[],[f200,f215])).
% 42.40/5.68  fof(f215,plain,(
% 42.40/5.68    ( ! [X10] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X10)) )),
% 42.40/5.68    inference(superposition,[],[f186,f111])).
% 42.40/5.68  fof(f111,plain,(
% 42.40/5.68    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 42.40/5.68    inference(forward_demodulation,[],[f107,f31])).
% 42.40/5.68  fof(f31,plain,(
% 42.40/5.68    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 42.40/5.68    inference(definition_unfolding,[],[f18,f23])).
% 42.40/5.68  fof(f23,plain,(
% 42.40/5.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 42.40/5.68    inference(cnf_transformation,[],[f11])).
% 42.40/5.68  fof(f11,axiom,(
% 42.40/5.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 42.40/5.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 42.40/5.68  fof(f18,plain,(
% 42.40/5.68    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 42.40/5.68    inference(cnf_transformation,[],[f4])).
% 42.40/5.68  fof(f4,axiom,(
% 42.40/5.68    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 42.40/5.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 42.40/5.68  fof(f107,plain,(
% 42.40/5.68    ( ! [X2] : (k5_xboole_0(X2,k4_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(X2,k1_xboole_0)) )),
% 42.40/5.68    inference(superposition,[],[f29,f86])).
% 42.40/5.68  fof(f86,plain,(
% 42.40/5.68    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 42.40/5.68    inference(superposition,[],[f32,f76])).
% 42.40/5.68  fof(f76,plain,(
% 42.40/5.68    ( ! [X6] : (k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6))) )),
% 42.40/5.68    inference(superposition,[],[f29,f42])).
% 42.40/5.68  fof(f32,plain,(
% 42.40/5.68    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 42.40/5.68    inference(definition_unfolding,[],[f20,f24,f24])).
% 42.40/5.68  fof(f20,plain,(
% 42.40/5.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 42.40/5.68    inference(cnf_transformation,[],[f1])).
% 42.40/5.68  fof(f1,axiom,(
% 42.40/5.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 42.40/5.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 42.40/5.68  fof(f186,plain,(
% 42.40/5.68    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) )),
% 42.40/5.68    inference(superposition,[],[f41,f29])).
% 42.40/5.68  fof(f41,plain,(
% 42.40/5.68    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0) )),
% 42.40/5.68    inference(backward_demodulation,[],[f33,f34])).
% 42.40/5.68  fof(f34,plain,(
% 42.40/5.68    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 42.40/5.68    inference(definition_unfolding,[],[f26,f24,f24])).
% 42.40/5.68  fof(f26,plain,(
% 42.40/5.68    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 42.40/5.68    inference(cnf_transformation,[],[f8])).
% 42.40/5.68  fof(f8,axiom,(
% 42.40/5.68    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 42.40/5.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 42.40/5.68  fof(f33,plain,(
% 42.40/5.68    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0) )),
% 42.40/5.68    inference(definition_unfolding,[],[f22,f23,f24])).
% 42.40/5.68  fof(f22,plain,(
% 42.40/5.68    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 42.40/5.68    inference(cnf_transformation,[],[f5])).
% 42.40/5.68  fof(f5,axiom,(
% 42.40/5.68    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 42.40/5.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 42.40/5.68  fof(f200,plain,(
% 42.40/5.68    ( ! [X5] : (k4_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X5,X5)) )),
% 42.40/5.68    inference(backward_demodulation,[],[f108,f186])).
% 42.40/5.68  fof(f108,plain,(
% 42.40/5.68    ( ! [X5] : (k4_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k1_xboole_0,X5)))) )),
% 42.40/5.68    inference(superposition,[],[f29,f86])).
% 42.40/5.68  fof(f28,plain,(
% 42.40/5.68    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 42.40/5.68    inference(cnf_transformation,[],[f10])).
% 42.40/5.68  fof(f10,axiom,(
% 42.40/5.68    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 42.40/5.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 42.40/5.68  fof(f88,plain,(
% 42.40/5.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 42.40/5.68    inference(superposition,[],[f29,f32])).
% 42.40/5.68  fof(f436,plain,(
% 42.40/5.68    ( ! [X4,X5,X3] : (k5_xboole_0(X4,k5_xboole_0(X3,X5)) = k5_xboole_0(X3,k5_xboole_0(X4,X5))) )),
% 42.40/5.68    inference(superposition,[],[f60,f28])).
% 42.40/5.68  fof(f60,plain,(
% 42.40/5.68    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_xboole_0(X3,X2),X4)) )),
% 42.40/5.68    inference(superposition,[],[f28,f21])).
% 42.40/5.68  fof(f71293,plain,(
% 42.40/5.68    ( ! [X66,X67] : (k4_xboole_0(X66,k5_xboole_0(X66,X67)) = k5_xboole_0(X66,k5_xboole_0(X66,k5_xboole_0(X67,k4_xboole_0(X67,X66))))) )),
% 42.40/5.68    inference(forward_demodulation,[],[f71024,f28])).
% 42.40/5.68  fof(f71024,plain,(
% 42.40/5.68    ( ! [X66,X67] : (k4_xboole_0(X66,k5_xboole_0(X66,X67)) = k5_xboole_0(X66,k5_xboole_0(k5_xboole_0(X66,X67),k4_xboole_0(X67,X66)))) )),
% 42.40/5.68    inference(superposition,[],[f325,f68068])).
% 42.40/5.68  fof(f68068,plain,(
% 42.40/5.68    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2)) )),
% 42.40/5.68    inference(superposition,[],[f67916,f21])).
% 42.40/5.68  fof(f67916,plain,(
% 42.40/5.68    ( ! [X204,X205] : (k4_xboole_0(X204,X205) = k4_xboole_0(k5_xboole_0(X204,X205),X205)) )),
% 42.40/5.68    inference(forward_demodulation,[],[f67915,f900])).
% 42.40/5.68  fof(f900,plain,(
% 42.40/5.68    ( ! [X6,X7,X5] : (k4_xboole_0(X7,X5) = k4_xboole_0(k4_xboole_0(X7,X5),k4_xboole_0(X5,X6))) )),
% 42.40/5.68    inference(forward_demodulation,[],[f888,f19])).
% 42.40/5.68  fof(f888,plain,(
% 42.40/5.68    ( ! [X6,X7,X5] : (k4_xboole_0(k4_xboole_0(X7,X5),k4_xboole_0(X5,X6)) = k4_xboole_0(X7,k5_xboole_0(X5,k1_xboole_0))) )),
% 42.40/5.68    inference(superposition,[],[f35,f841])).
% 42.40/5.68  fof(f841,plain,(
% 42.40/5.68    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),X4)) )),
% 42.40/5.68    inference(forward_demodulation,[],[f840,f240])).
% 42.40/5.68  fof(f840,plain,(
% 42.40/5.68    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),X4) = k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5))) )),
% 42.40/5.68    inference(forward_demodulation,[],[f839,f325])).
% 42.40/5.68  fof(f839,plain,(
% 42.40/5.68    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),X4) = k5_xboole_0(k4_xboole_0(X4,X5),k5_xboole_0(X4,k5_xboole_0(X5,k4_xboole_0(X5,X4))))) )),
% 42.40/5.68    inference(forward_demodulation,[],[f808,f312])).
% 42.40/5.68  fof(f808,plain,(
% 42.40/5.68    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),X4) = k5_xboole_0(k4_xboole_0(X4,X5),k5_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X5,X4))))) )),
% 42.40/5.68    inference(superposition,[],[f325,f32])).
% 42.40/5.68  fof(f35,plain,(
% 42.40/5.68    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 42.40/5.68    inference(definition_unfolding,[],[f27,f23])).
% 42.40/5.68  fof(f27,plain,(
% 42.40/5.68    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 42.40/5.68    inference(cnf_transformation,[],[f6])).
% 42.40/5.68  fof(f6,axiom,(
% 42.40/5.68    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 42.40/5.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 42.40/5.68  fof(f67915,plain,(
% 42.40/5.68    ( ! [X204,X205] : (k4_xboole_0(k4_xboole_0(X204,X205),k4_xboole_0(X205,k4_xboole_0(X205,X204))) = k4_xboole_0(k5_xboole_0(X204,X205),X205)) )),
% 42.40/5.68    inference(forward_demodulation,[],[f67914,f5957])).
% 42.40/5.68  fof(f5957,plain,(
% 42.40/5.68    ( ! [X8,X7] : (k4_xboole_0(k5_xboole_0(X8,X7),X7) = k5_xboole_0(X8,k4_xboole_0(X7,k5_xboole_0(X8,X7)))) )),
% 42.40/5.68    inference(superposition,[],[f3969,f310])).
% 42.40/5.68  fof(f310,plain,(
% 42.40/5.68    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 42.40/5.68    inference(superposition,[],[f262,f21])).
% 42.40/5.68  fof(f3969,plain,(
% 42.40/5.68    ( ! [X14,X15] : (k4_xboole_0(X15,X14) = k5_xboole_0(k5_xboole_0(X14,X15),k4_xboole_0(X14,X15))) )),
% 42.40/5.68    inference(superposition,[],[f2140,f652])).
% 42.40/5.68  fof(f652,plain,(
% 42.40/5.68    ( ! [X23,X21,X22] : (k5_xboole_0(k5_xboole_0(X21,X22),X23) = k5_xboole_0(X23,k5_xboole_0(X22,X21))) )),
% 42.40/5.68    inference(forward_demodulation,[],[f633,f19])).
% 42.40/5.68  fof(f633,plain,(
% 42.40/5.68    ( ! [X23,X21,X22] : (k5_xboole_0(X23,k5_xboole_0(X22,X21)) = k5_xboole_0(k5_xboole_0(X21,X22),k5_xboole_0(X23,k1_xboole_0))) )),
% 42.40/5.68    inference(superposition,[],[f66,f512])).
% 42.40/5.68  fof(f512,plain,(
% 42.40/5.68    ( ! [X24,X25] : (k5_xboole_0(X25,X24) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X24,X25))) )),
% 42.40/5.68    inference(superposition,[],[f66,f42])).
% 42.40/5.68  fof(f66,plain,(
% 42.40/5.68    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))) )),
% 42.40/5.68    inference(superposition,[],[f28,f21])).
% 42.40/5.68  fof(f2140,plain,(
% 42.40/5.68    ( ! [X6,X5] : (k4_xboole_0(X6,X5) = k5_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(X6,X5))) )),
% 42.40/5.68    inference(superposition,[],[f863,f497])).
% 42.40/5.68  fof(f497,plain,(
% 42.40/5.68    ( ! [X14,X12,X13] : (k5_xboole_0(X14,k5_xboole_0(X12,X13)) = k5_xboole_0(k5_xboole_0(X13,X14),X12)) )),
% 42.40/5.68    inference(superposition,[],[f66,f21])).
% 42.40/5.68  fof(f863,plain,(
% 42.40/5.68    ( ! [X30,X29] : (k4_xboole_0(X29,X30) = k5_xboole_0(k5_xboole_0(X30,k4_xboole_0(X30,X29)),X29)) )),
% 42.40/5.68    inference(forward_demodulation,[],[f831,f42])).
% 42.40/5.68  fof(f831,plain,(
% 42.40/5.68    ( ! [X30,X29] : (k5_xboole_0(k5_xboole_0(X30,k4_xboole_0(X30,X29)),X29) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X29,X30))) )),
% 42.40/5.68    inference(superposition,[],[f512,f325])).
% 42.40/5.68  fof(f67914,plain,(
% 42.40/5.68    ( ! [X204,X205] : (k4_xboole_0(k4_xboole_0(X204,X205),k4_xboole_0(X205,k4_xboole_0(X205,X204))) = k5_xboole_0(X204,k4_xboole_0(X205,k5_xboole_0(X204,X205)))) )),
% 42.40/5.68    inference(forward_demodulation,[],[f67913,f21])).
% 42.40/5.68  fof(f67913,plain,(
% 42.40/5.68    ( ! [X204,X205] : (k4_xboole_0(k4_xboole_0(X204,X205),k4_xboole_0(X205,k4_xboole_0(X205,X204))) = k5_xboole_0(k4_xboole_0(X205,k5_xboole_0(X204,X205)),X204)) )),
% 42.40/5.68    inference(forward_demodulation,[],[f67912,f3989])).
% 42.40/5.68  fof(f3989,plain,(
% 42.40/5.68    ( ! [X35,X34] : (k5_xboole_0(X35,X34) = k5_xboole_0(k4_xboole_0(X34,X35),k4_xboole_0(X35,X34))) )),
% 42.40/5.68    inference(superposition,[],[f262,f2140])).
% 42.40/5.68  fof(f67912,plain,(
% 42.40/5.68    ( ! [X204,X205] : (k4_xboole_0(k4_xboole_0(X204,X205),k4_xboole_0(X205,k4_xboole_0(X205,X204))) = k5_xboole_0(k4_xboole_0(X205,k5_xboole_0(k4_xboole_0(X205,X204),k4_xboole_0(X204,X205))),X204)) )),
% 42.40/5.68    inference(forward_demodulation,[],[f67650,f2463])).
% 42.40/5.68  fof(f2463,plain,(
% 42.40/5.68    ( ! [X26,X24,X23,X25] : (k4_xboole_0(k4_xboole_0(X26,k4_xboole_0(X24,X25)),k4_xboole_0(X23,X24)) = k4_xboole_0(X26,k5_xboole_0(k4_xboole_0(X24,X25),k4_xboole_0(X23,X24)))) )),
% 42.40/5.68    inference(superposition,[],[f35,f900])).
% 42.40/5.68  fof(f67650,plain,(
% 42.40/5.68    ( ! [X204,X205] : (k4_xboole_0(k4_xboole_0(X204,X205),k4_xboole_0(X205,k4_xboole_0(X205,X204))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X205,k4_xboole_0(X205,X204)),k4_xboole_0(X204,X205)),X204)) )),
% 42.40/5.68    inference(superposition,[],[f3934,f53795])).
% 42.40/5.68  fof(f53795,plain,(
% 42.40/5.68    ( ! [X4,X3] : (k4_xboole_0(X4,k4_xboole_0(X4,X3)) = k5_xboole_0(k4_xboole_0(X3,X4),X3)) )),
% 42.40/5.68    inference(superposition,[],[f3691,f642])).
% 42.40/5.68  fof(f642,plain,(
% 42.40/5.68    ( ! [X17,X18] : (k5_xboole_0(X18,X17) = k5_xboole_0(k5_xboole_0(X17,X18),k1_xboole_0)) )),
% 42.40/5.68    inference(forward_demodulation,[],[f615,f42])).
% 42.40/5.68  fof(f615,plain,(
% 42.40/5.68    ( ! [X17,X18] : (k5_xboole_0(k5_xboole_0(X17,X18),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X18,X17))) )),
% 42.40/5.68    inference(superposition,[],[f512,f512])).
% 42.40/5.68  fof(f3691,plain,(
% 42.40/5.68    ( ! [X24,X23] : (k4_xboole_0(X24,k4_xboole_0(X24,X23)) = k5_xboole_0(k5_xboole_0(X23,k4_xboole_0(X23,X24)),k1_xboole_0)) )),
% 42.40/5.68    inference(forward_demodulation,[],[f3584,f996])).
% 42.40/5.68  fof(f996,plain,(
% 42.40/5.68    ( ! [X12,X11] : (k4_xboole_0(X12,X11) = k4_xboole_0(X12,k5_xboole_0(X11,k4_xboole_0(X11,X12)))) )),
% 42.40/5.68    inference(forward_demodulation,[],[f995,f325])).
% 42.40/5.68  fof(f995,plain,(
% 42.40/5.68    ( ! [X12,X11] : (k4_xboole_0(X12,k5_xboole_0(X11,k4_xboole_0(X11,X12))) = k5_xboole_0(X12,k5_xboole_0(X11,k4_xboole_0(X11,X12)))) )),
% 42.40/5.68    inference(forward_demodulation,[],[f972,f19])).
% 42.40/5.68  fof(f972,plain,(
% 42.40/5.68    ( ! [X12,X11] : (k4_xboole_0(X12,k5_xboole_0(X11,k4_xboole_0(X11,X12))) = k5_xboole_0(X12,k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(X11,X12)),k1_xboole_0))) )),
% 42.40/5.68    inference(superposition,[],[f325,f894])).
% 42.40/5.68  fof(f894,plain,(
% 42.40/5.68    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X5,X4)),X4)) )),
% 42.40/5.68    inference(forward_demodulation,[],[f875,f312])).
% 42.40/5.68  fof(f875,plain,(
% 42.40/5.68    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4)) )),
% 42.40/5.68    inference(superposition,[],[f841,f32])).
% 42.40/5.68  fof(f3584,plain,(
% 42.40/5.68    ( ! [X24,X23] : (k5_xboole_0(k5_xboole_0(X23,k4_xboole_0(X23,X24)),k1_xboole_0) = k4_xboole_0(X24,k4_xboole_0(X24,k5_xboole_0(X23,k4_xboole_0(X23,X24))))) )),
% 42.40/5.68    inference(superposition,[],[f997,f894])).
% 42.40/5.68  fof(f997,plain,(
% 42.40/5.68    ( ! [X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 42.40/5.68    inference(backward_demodulation,[],[f992,f996])).
% 42.40/5.68  fof(f992,plain,(
% 42.40/5.68    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X0,X1))))) )),
% 42.40/5.68    inference(forward_demodulation,[],[f967,f111])).
% 42.40/5.68  fof(f967,plain,(
% 42.40/5.68    ( ! [X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0)) )),
% 42.40/5.68    inference(superposition,[],[f32,f894])).
% 42.40/5.68  fof(f3934,plain,(
% 42.40/5.68    ( ! [X6,X5] : (k4_xboole_0(X5,k5_xboole_0(X5,X6)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X5,X6),X5),X6)) )),
% 42.40/5.68    inference(superposition,[],[f2140,f262])).
% 42.40/5.68  fof(f71112,plain,(
% 42.40/5.68    ( ! [X313,X312] : (k5_xboole_0(X312,X313) = k4_xboole_0(k5_xboole_0(X312,k4_xboole_0(X313,X312)),k4_xboole_0(X312,k5_xboole_0(X312,X313)))) )),
% 42.40/5.68    inference(superposition,[],[f6525,f68068])).
% 42.40/5.68  fof(f6525,plain,(
% 42.40/5.68    ( ! [X4,X5] : (k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X4,X5)) = X5) )),
% 42.40/5.68    inference(forward_demodulation,[],[f6524,f186])).
% 42.40/5.68  fof(f6524,plain,(
% 42.40/5.68    ( ! [X4,X5] : (k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X4,X5)) = k4_xboole_0(X5,k4_xboole_0(k4_xboole_0(X5,X4),X5))) )),
% 42.40/5.68    inference(forward_demodulation,[],[f6416,f35])).
% 42.40/5.68  fof(f6416,plain,(
% 42.40/5.68    ( ! [X4,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,k5_xboole_0(X4,k4_xboole_0(X5,X4)))) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X4,X5))) )),
% 42.40/5.68    inference(superposition,[],[f32,f4061])).
% 42.40/5.68  fof(f4061,plain,(
% 42.40/5.68    ( ! [X68,X69] : (k4_xboole_0(X68,X69) = k4_xboole_0(k5_xboole_0(X68,k4_xboole_0(X69,X68)),X69)) )),
% 42.40/5.68    inference(forward_demodulation,[],[f4060,f42])).
% 42.40/5.68  fof(f4060,plain,(
% 42.40/5.68    ( ! [X68,X69] : (k4_xboole_0(k5_xboole_0(X68,k4_xboole_0(X69,X68)),X69) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X68,X69))) )),
% 42.40/5.68    inference(forward_demodulation,[],[f4059,f841])).
% 42.40/5.68  fof(f4059,plain,(
% 42.40/5.68    ( ! [X68,X69] : (k4_xboole_0(k5_xboole_0(X68,k4_xboole_0(X69,X68)),X69) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X69,X68),X69),k4_xboole_0(X68,X69))) )),
% 42.40/5.68    inference(forward_demodulation,[],[f3959,f35])).
% 42.40/5.68  fof(f3959,plain,(
% 42.40/5.68    ( ! [X68,X69] : (k4_xboole_0(k5_xboole_0(X68,k4_xboole_0(X69,X68)),X69) = k5_xboole_0(k4_xboole_0(X69,k5_xboole_0(X68,k4_xboole_0(X69,X68))),k4_xboole_0(X68,X69))) )),
% 42.40/5.68    inference(superposition,[],[f2140,f1612])).
% 42.40/5.68  fof(f1612,plain,(
% 42.40/5.68    ( ! [X54,X53] : (k4_xboole_0(X54,X53) = k5_xboole_0(k5_xboole_0(X54,k4_xboole_0(X53,X54)),X53)) )),
% 42.40/5.68    inference(forward_demodulation,[],[f1574,f42])).
% 42.40/5.68  fof(f1574,plain,(
% 42.40/5.68    ( ! [X54,X53] : (k5_xboole_0(k5_xboole_0(X54,k4_xboole_0(X53,X54)),X53) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X54,X53))) )),
% 42.40/5.68    inference(superposition,[],[f512,f855])).
% 42.40/5.68  fof(f855,plain,(
% 42.40/5.68    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k5_xboole_0(X4,k5_xboole_0(X3,k4_xboole_0(X4,X3)))) )),
% 42.40/5.68    inference(forward_demodulation,[],[f817,f21])).
% 42.40/5.68  fof(f817,plain,(
% 42.40/5.68    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k5_xboole_0(X4,k5_xboole_0(k4_xboole_0(X4,X3),X3))) )),
% 42.40/5.68    inference(superposition,[],[f325,f66])).
% 42.40/5.68  fof(f338,plain,(
% 42.40/5.68    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_3),
% 42.40/5.68    inference(avatar_component_clause,[],[f336])).
% 42.40/5.68  fof(f336,plain,(
% 42.40/5.68    spl2_3 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 42.40/5.68    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 42.40/5.68  fof(f339,plain,(
% 42.40/5.68    ~spl2_3 | spl2_1),
% 42.40/5.68    inference(avatar_split_clause,[],[f330,f37,f336])).
% 42.40/5.68  fof(f37,plain,(
% 42.40/5.68    spl2_1 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 42.40/5.68    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 42.40/5.68  fof(f330,plain,(
% 42.40/5.68    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 42.40/5.68    inference(backward_demodulation,[],[f39,f312])).
% 42.40/5.68  fof(f39,plain,(
% 42.40/5.68    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 42.40/5.68    inference(avatar_component_clause,[],[f37])).
% 42.40/5.68  fof(f57,plain,(
% 42.40/5.68    spl2_2),
% 42.40/5.68    inference(avatar_split_clause,[],[f51,f53])).
% 42.40/5.68  fof(f53,plain,(
% 42.40/5.68    spl2_2 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 42.40/5.68    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 42.40/5.68  fof(f51,plain,(
% 42.40/5.68    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 42.40/5.68    inference(superposition,[],[f42,f31])).
% 42.40/5.68  fof(f56,plain,(
% 42.40/5.68    spl2_2),
% 42.40/5.68    inference(avatar_split_clause,[],[f50,f53])).
% 42.40/5.68  fof(f50,plain,(
% 42.40/5.68    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 42.40/5.68    inference(superposition,[],[f31,f42])).
% 42.40/5.68  fof(f40,plain,(
% 42.40/5.68    ~spl2_1),
% 42.40/5.68    inference(avatar_split_clause,[],[f30,f37])).
% 42.40/5.68  fof(f30,plain,(
% 42.40/5.68    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 42.40/5.68    inference(definition_unfolding,[],[f17,f23,f24])).
% 42.40/5.68  fof(f17,plain,(
% 42.40/5.68    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 42.40/5.68    inference(cnf_transformation,[],[f16])).
% 42.40/5.68  fof(f16,plain,(
% 42.40/5.68    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 42.40/5.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 42.40/5.68  fof(f15,plain,(
% 42.40/5.68    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 42.40/5.68    introduced(choice_axiom,[])).
% 42.40/5.68  fof(f14,plain,(
% 42.40/5.68    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 42.40/5.68    inference(ennf_transformation,[],[f13])).
% 42.40/5.68  fof(f13,negated_conjecture,(
% 42.40/5.68    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 42.40/5.68    inference(negated_conjecture,[],[f12])).
% 42.40/5.68  fof(f12,conjecture,(
% 42.40/5.68    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 42.40/5.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 42.40/5.68  % SZS output end Proof for theBenchmark
% 42.40/5.68  % (13936)------------------------------
% 42.40/5.68  % (13936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 42.40/5.68  % (13936)Termination reason: Refutation
% 42.40/5.68  
% 42.40/5.68  % (13936)Memory used [KB]: 152620
% 42.40/5.68  % (13936)Time elapsed: 5.203 s
% 42.40/5.68  % (13936)------------------------------
% 42.40/5.68  % (13936)------------------------------
% 42.40/5.70  % (13925)Success in time 5.32 s
%------------------------------------------------------------------------------
