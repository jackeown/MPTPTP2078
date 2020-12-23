%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:25 EST 2020

% Result     : Theorem 20.45s
% Output     : Refutation 20.45s
% Verified   : 
% Statistics : Number of formulae       :  183 (100979 expanded)
%              Number of leaves         :   14 (33771 expanded)
%              Depth                    :   49
%              Number of atoms          :  188 (100985 expanded)
%              Number of equality atoms :  179 (100975 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f45222,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f45,f45196])).

fof(f45196,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f45194])).

fof(f45194,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f37,f45193])).

fof(f45193,plain,(
    ! [X227,X226] : k5_xboole_0(X226,X227) = k4_xboole_0(k5_xboole_0(X226,k4_xboole_0(X227,X226)),k4_xboole_0(X226,k4_xboole_0(X226,X227))) ),
    inference(forward_demodulation,[],[f44806,f45077])).

fof(f45077,plain,(
    ! [X28,X27] : k4_xboole_0(X27,k4_xboole_0(X27,X28)) = k4_xboole_0(X27,k5_xboole_0(X27,X28)) ),
    inference(forward_demodulation,[],[f45076,f251])).

fof(f251,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f220,f239])).

fof(f239,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f219,f103])).

fof(f103,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f92,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f30,f29])).

fof(f29,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f17,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f30,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f19,f21])).

fof(f19,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f92,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f27,f18])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f219,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f116,f106])).

fof(f106,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f93,f18])).

fof(f93,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f27,f30])).

fof(f116,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f24,f106])).

fof(f24,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f220,plain,(
    ! [X2,X1] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f116,f27])).

fof(f45076,plain,(
    ! [X28,X27] : k5_xboole_0(X27,k4_xboole_0(X27,X28)) = k4_xboole_0(X27,k5_xboole_0(X27,X28)) ),
    inference(forward_demodulation,[],[f44729,f36132])).

fof(f36132,plain,(
    ! [X101,X102] : k4_xboole_0(X101,X102) = k4_xboole_0(k5_xboole_0(X101,X102),k4_xboole_0(X102,X101)) ),
    inference(forward_demodulation,[],[f36128,f239])).

fof(f36128,plain,(
    ! [X101,X102] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X101,X102)) = k4_xboole_0(k5_xboole_0(X101,X102),k4_xboole_0(X102,X101)) ),
    inference(backward_demodulation,[],[f24022,f35939])).

fof(f35939,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(X6,X5)) ),
    inference(superposition,[],[f1841,f23180])).

fof(f23180,plain,(
    ! [X14,X15] : k5_xboole_0(X14,X15) = k5_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X15)) ),
    inference(superposition,[],[f323,f22825])).

fof(f22825,plain,(
    ! [X80,X81] : k4_xboole_0(X80,X81) = k5_xboole_0(k5_xboole_0(X80,X81),k4_xboole_0(X81,X80)) ),
    inference(superposition,[],[f20572,f334])).

fof(f334,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X6,X5),X6) = X5 ),
    inference(superposition,[],[f323,f323])).

fof(f20572,plain,(
    ! [X24,X23] : k5_xboole_0(X23,k4_xboole_0(k5_xboole_0(X23,X24),X24)) = k4_xboole_0(X24,k5_xboole_0(X23,X24)) ),
    inference(backward_demodulation,[],[f20541,f20571])).

fof(f20571,plain,(
    ! [X72,X71] : k4_xboole_0(k5_xboole_0(X72,k4_xboole_0(k5_xboole_0(X71,X72),X72)),k5_xboole_0(X71,X72)) = k4_xboole_0(X72,k5_xboole_0(X71,X72)) ),
    inference(forward_demodulation,[],[f20570,f27])).

fof(f20570,plain,(
    ! [X72,X71] : k4_xboole_0(k5_xboole_0(X72,k4_xboole_0(k5_xboole_0(X71,X72),X72)),k5_xboole_0(X71,X72)) = k5_xboole_0(X72,k4_xboole_0(X72,k4_xboole_0(X72,k5_xboole_0(X71,X72)))) ),
    inference(forward_demodulation,[],[f20569,f1066])).

fof(f1066,plain,(
    ! [X12,X13,X11] : k5_xboole_0(X13,k4_xboole_0(X12,k4_xboole_0(X12,X11))) = k5_xboole_0(X11,k5_xboole_0(X13,k4_xboole_0(X11,X12))) ),
    inference(superposition,[],[f349,f277])).

fof(f277,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f27,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f23,f23])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f349,plain,(
    ! [X6,X4,X5] : k5_xboole_0(X5,X6) = k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,X6))) ),
    inference(forward_demodulation,[],[f342,f24])).

fof(f342,plain,(
    ! [X6,X4,X5] : k5_xboole_0(X5,X6) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X5,X4),X6)) ),
    inference(superposition,[],[f24,f323])).

fof(f20569,plain,(
    ! [X72,X71] : k4_xboole_0(k5_xboole_0(X72,k4_xboole_0(k5_xboole_0(X71,X72),X72)),k5_xboole_0(X71,X72)) = k5_xboole_0(k5_xboole_0(X71,X72),k5_xboole_0(X72,k4_xboole_0(k5_xboole_0(X71,X72),X72))) ),
    inference(forward_demodulation,[],[f20441,f18])).

fof(f20441,plain,(
    ! [X72,X71] : k4_xboole_0(k5_xboole_0(X72,k4_xboole_0(k5_xboole_0(X71,X72),X72)),k5_xboole_0(X71,X72)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X71,X72),k1_xboole_0),k5_xboole_0(X72,k4_xboole_0(k5_xboole_0(X71,X72),X72))) ),
    inference(superposition,[],[f896,f19147])).

fof(f19147,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,X2),X2))) ),
    inference(forward_demodulation,[],[f19146,f341])).

fof(f341,plain,(
    ! [X2,X3] : k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2) ),
    inference(superposition,[],[f248,f323])).

fof(f248,plain,(
    ! [X4,X5] : k5_xboole_0(X4,k5_xboole_0(X4,X5)) = X5 ),
    inference(forward_demodulation,[],[f240,f239])).

fof(f240,plain,(
    ! [X4,X5] : k5_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X4,k5_xboole_0(X4,X5)) ),
    inference(backward_demodulation,[],[f217,f239])).

fof(f217,plain,(
    ! [X4,X5] : k5_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X4,k5_xboole_0(k1_xboole_0,k5_xboole_0(X4,X5))) ),
    inference(forward_demodulation,[],[f209,f24])).

fof(f209,plain,(
    ! [X4,X5] : k5_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(k1_xboole_0,X4),X5)) ),
    inference(superposition,[],[f24,f172])).

fof(f172,plain,(
    ! [X7] : k1_xboole_0 = k5_xboole_0(X7,k5_xboole_0(k1_xboole_0,X7)) ),
    inference(superposition,[],[f114,f103])).

fof(f114,plain,(
    ! [X2,X1] : k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(superposition,[],[f106,f24])).

fof(f19146,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(k4_xboole_0(k5_xboole_0(X3,X2),X2),X2)) ),
    inference(forward_demodulation,[],[f18888,f4943])).

fof(f4943,plain,(
    ! [X80,X81,X79] : k5_xboole_0(k4_xboole_0(k5_xboole_0(X79,X80),X81),X80) = k5_xboole_0(X79,k4_xboole_0(X81,k4_xboole_0(X81,k5_xboole_0(X79,X80)))) ),
    inference(superposition,[],[f349,f429])).

fof(f429,plain,(
    ! [X12,X11] : k4_xboole_0(X12,k4_xboole_0(X12,X11)) = k5_xboole_0(k4_xboole_0(X11,X12),X11) ),
    inference(superposition,[],[f334,f277])).

fof(f18888,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,X2))))) ),
    inference(superposition,[],[f71,f251])).

fof(f71,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X4,k5_xboole_0(X2,X3))))) ),
    inference(superposition,[],[f30,f24])).

fof(f896,plain,(
    ! [X26,X25] : k4_xboole_0(X25,X26) = k5_xboole_0(k4_xboole_0(X26,k4_xboole_0(X26,X25)),X25) ),
    inference(superposition,[],[f334,f426])).

fof(f426,plain,(
    ! [X6,X5] : k4_xboole_0(X6,k4_xboole_0(X6,X5)) = k5_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f248,f277])).

fof(f20541,plain,(
    ! [X24,X23] : k4_xboole_0(k5_xboole_0(X24,k4_xboole_0(k5_xboole_0(X23,X24),X24)),k5_xboole_0(X23,X24)) = k5_xboole_0(X23,k4_xboole_0(k5_xboole_0(X23,X24),X24)) ),
    inference(forward_demodulation,[],[f20540,f1010])).

fof(f1010,plain,(
    ! [X24,X23,X25] : k5_xboole_0(X25,X23) = k5_xboole_0(k5_xboole_0(X24,X23),k5_xboole_0(X25,X24)) ),
    inference(superposition,[],[f336,f323])).

fof(f336,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(X10,k5_xboole_0(X8,k5_xboole_0(X9,X10))) ),
    inference(superposition,[],[f323,f24])).

fof(f20540,plain,(
    ! [X24,X23] : k4_xboole_0(k5_xboole_0(X24,k4_xboole_0(k5_xboole_0(X23,X24),X24)),k5_xboole_0(X23,X24)) = k5_xboole_0(k5_xboole_0(X24,k4_xboole_0(k5_xboole_0(X23,X24),X24)),k5_xboole_0(X23,X24)) ),
    inference(forward_demodulation,[],[f20421,f18])).

fof(f20421,plain,(
    ! [X24,X23] : k4_xboole_0(k5_xboole_0(X24,k4_xboole_0(k5_xboole_0(X23,X24),X24)),k5_xboole_0(X23,X24)) = k5_xboole_0(k5_xboole_0(X24,k4_xboole_0(k5_xboole_0(X23,X24),X24)),k4_xboole_0(k5_xboole_0(X23,X24),k1_xboole_0)) ),
    inference(superposition,[],[f277,f19147])).

fof(f323,plain,(
    ! [X4,X3] : k5_xboole_0(X4,k5_xboole_0(X3,X4)) = X3 ),
    inference(forward_demodulation,[],[f310,f103])).

fof(f310,plain,(
    ! [X4,X3] : k5_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X4,k5_xboole_0(X3,X4)) ),
    inference(superposition,[],[f248,f114])).

fof(f1841,plain,(
    ! [X24,X23,X22] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X23,X24),k5_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X22,X23))) ),
    inference(superposition,[],[f30,f1589])).

fof(f1589,plain,(
    ! [X19,X17,X18] : k4_xboole_0(X18,X17) = k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(X17,X19)) ),
    inference(superposition,[],[f1558,f1317])).

fof(f1317,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(forward_demodulation,[],[f1283,f103])).

fof(f1283,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(superposition,[],[f27,f1148])).

fof(f1148,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f32,f443])).

fof(f443,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),X4) ),
    inference(backward_demodulation,[],[f279,f428])).

fof(f428,plain,(
    ! [X10,X9] : k5_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X10,k4_xboole_0(X10,X9))) = X9 ),
    inference(superposition,[],[f333,f277])).

fof(f333,plain,(
    ! [X4,X3] : k5_xboole_0(k5_xboole_0(X3,X4),X4) = X3 ),
    inference(superposition,[],[f323,f248])).

fof(f279,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X5,X4)))) ),
    inference(superposition,[],[f30,f31])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f25,f23,f23])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f1558,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0 ),
    inference(forward_demodulation,[],[f1500,f103])).

fof(f1500,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) ),
    inference(superposition,[],[f27,f1320])).

fof(f1320,plain,(
    ! [X8,X7,X9] : k1_xboole_0 = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(k4_xboole_0(X8,X7),X9))) ),
    inference(forward_demodulation,[],[f1284,f127])).

fof(f127,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f124,f103])).

fof(f124,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f27,f100])).

fof(f100,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f46,f27])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f30,f18])).

fof(f1284,plain,(
    ! [X8,X7,X9] : k4_xboole_0(k1_xboole_0,X9) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(k4_xboole_0(X8,X7),X9))) ),
    inference(superposition,[],[f32,f1148])).

fof(f24022,plain,(
    ! [X101,X102] : k4_xboole_0(k5_xboole_0(X101,X102),k4_xboole_0(X102,X101)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X102,X101),k5_xboole_0(X101,X102)),k4_xboole_0(X101,X102)) ),
    inference(superposition,[],[f23173,f22825])).

fof(f23173,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(k4_xboole_0(X13,X12),k5_xboole_0(X12,X13)) ),
    inference(superposition,[],[f22825,f341])).

fof(f44729,plain,(
    ! [X28,X27] : k4_xboole_0(X27,k5_xboole_0(X27,X28)) = k5_xboole_0(X27,k4_xboole_0(k5_xboole_0(X27,X28),k4_xboole_0(X28,X27))) ),
    inference(superposition,[],[f277,f44371])).

fof(f44371,plain,(
    ! [X78,X77] : k4_xboole_0(X78,X77) = k4_xboole_0(k5_xboole_0(X77,X78),X77) ),
    inference(forward_demodulation,[],[f44370,f103])).

fof(f44370,plain,(
    ! [X78,X77] : k4_xboole_0(k5_xboole_0(X77,X78),X77) = k5_xboole_0(k4_xboole_0(X78,X77),k1_xboole_0) ),
    inference(forward_demodulation,[],[f44369,f43840])).

fof(f43840,plain,(
    ! [X28,X27] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X28,X27),k4_xboole_0(k5_xboole_0(X27,X28),X27)) ),
    inference(superposition,[],[f41366,f248])).

fof(f41366,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X2,X3),X2),k4_xboole_0(X3,X2)) ),
    inference(superposition,[],[f33427,f36124])).

fof(f36124,plain,(
    ! [X103,X104] : k4_xboole_0(X104,X103) = k4_xboole_0(k5_xboole_0(X103,X104),k4_xboole_0(X103,X104)) ),
    inference(forward_demodulation,[],[f36121,f239])).

fof(f36121,plain,(
    ! [X103,X104] : k4_xboole_0(k5_xboole_0(X103,X104),k4_xboole_0(X103,X104)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X104,X103)) ),
    inference(backward_demodulation,[],[f24023,f35938])).

fof(f35938,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X3,X4)) ),
    inference(superposition,[],[f1841,f23181])).

fof(f23181,plain,(
    ! [X17,X16] : k5_xboole_0(X16,X17) = k5_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X17,X16)) ),
    inference(superposition,[],[f333,f22825])).

fof(f24023,plain,(
    ! [X103,X104] : k4_xboole_0(k5_xboole_0(X103,X104),k4_xboole_0(X103,X104)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X103,X104),k5_xboole_0(X103,X104)),k4_xboole_0(X104,X103)) ),
    inference(superposition,[],[f23173,f22826])).

fof(f22826,plain,(
    ! [X83,X82] : k4_xboole_0(X83,X82) = k5_xboole_0(k5_xboole_0(X82,X83),k4_xboole_0(X82,X83)) ),
    inference(superposition,[],[f20572,f333])).

fof(f33427,plain,(
    ! [X21,X19,X20] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X19,k4_xboole_0(X20,X21))) ),
    inference(superposition,[],[f33143,f1589])).

fof(f33143,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(X2,X4)) ),
    inference(forward_demodulation,[],[f33142,f248])).

fof(f33142,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(X3,k5_xboole_0(X3,X2)),X4)) ),
    inference(forward_demodulation,[],[f33141,f23180])).

fof(f33141,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(X3,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))),X4)) ),
    inference(forward_demodulation,[],[f33140,f1065])).

fof(f1065,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))) = k5_xboole_0(X8,k5_xboole_0(X10,k4_xboole_0(X8,X9))) ),
    inference(superposition,[],[f349,f27])).

fof(f33140,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,k4_xboole_0(X3,X2))),X4)) ),
    inference(forward_demodulation,[],[f32943,f18])).

fof(f32943,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),k1_xboole_0)),X4)) ),
    inference(superposition,[],[f27067,f18698])).

fof(f18698,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f18697,f48])).

fof(f18697,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X36,X36)) ),
    inference(forward_demodulation,[],[f18696,f18])).

fof(f18696,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X36,k4_xboole_0(X36,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f18695,f48])).

fof(f18695,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X35,X35)))) ),
    inference(forward_demodulation,[],[f18694,f3852])).

fof(f3852,plain,(
    ! [X24,X23,X25] : k4_xboole_0(X23,k4_xboole_0(X23,k4_xboole_0(X24,X25))) = k4_xboole_0(X23,k4_xboole_0(X23,k4_xboole_0(X24,k4_xboole_0(X25,k4_xboole_0(X25,X23))))) ),
    inference(backward_demodulation,[],[f1233,f3844])).

fof(f3844,plain,(
    ! [X47,X48,X49] : k4_xboole_0(X49,k4_xboole_0(X47,k4_xboole_0(X47,X48))) = k4_xboole_0(X49,k4_xboole_0(X47,k4_xboole_0(X47,k4_xboole_0(X48,k4_xboole_0(X48,X49))))) ),
    inference(backward_demodulation,[],[f1247,f3577])).

fof(f3577,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5)))) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5)))))) ),
    inference(superposition,[],[f39,f32])).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    inference(forward_demodulation,[],[f33,f32])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f26,f23,f23,f23,f23])).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f1247,plain,(
    ! [X47,X48,X49] : k4_xboole_0(X49,k4_xboole_0(X47,k4_xboole_0(X47,X48))) = k4_xboole_0(X49,k4_xboole_0(X47,k4_xboole_0(X47,k4_xboole_0(X48,k4_xboole_0(X47,k4_xboole_0(X47,k4_xboole_0(X48,X49))))))) ),
    inference(forward_demodulation,[],[f1176,f32])).

fof(f1176,plain,(
    ! [X47,X48,X49] : k4_xboole_0(X49,k4_xboole_0(X47,k4_xboole_0(X47,X48))) = k4_xboole_0(X49,k4_xboole_0(k4_xboole_0(X47,k4_xboole_0(X47,X48)),k4_xboole_0(X47,k4_xboole_0(X47,k4_xboole_0(X48,X49))))) ),
    inference(superposition,[],[f494,f32])).

fof(f494,plain,(
    ! [X10,X9] : k4_xboole_0(X10,X9) = k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f493,f277])).

fof(f493,plain,(
    ! [X10,X9] : k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k5_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f480,f18])).

fof(f480,plain,(
    ! [X10,X9] : k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k5_xboole_0(X10,k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),k1_xboole_0)) ),
    inference(superposition,[],[f277,f446])).

fof(f446,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1) ),
    inference(superposition,[],[f443,f31])).

fof(f1233,plain,(
    ! [X24,X23,X25] : k4_xboole_0(X23,k4_xboole_0(X23,k4_xboole_0(X24,k4_xboole_0(X25,k4_xboole_0(X25,k4_xboole_0(X23,k4_xboole_0(X23,X24))))))) = k4_xboole_0(X23,k4_xboole_0(X23,k4_xboole_0(X24,X25))) ),
    inference(forward_demodulation,[],[f1156,f32])).

fof(f1156,plain,(
    ! [X24,X23,X25] : k4_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,X24)),X25) = k4_xboole_0(X23,k4_xboole_0(X23,k4_xboole_0(X24,k4_xboole_0(X25,k4_xboole_0(X25,k4_xboole_0(X23,k4_xboole_0(X23,X24))))))) ),
    inference(superposition,[],[f32,f494])).

fof(f18694,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X35,X36)))))) ),
    inference(forward_demodulation,[],[f18693,f32])).

fof(f18693,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X35,k4_xboole_0(X35,X36)))) ),
    inference(forward_demodulation,[],[f18469,f18])).

fof(f18469,plain,(
    ! [X35,X36] : k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X35,k4_xboole_0(X35,X36)))) = k4_xboole_0(k4_xboole_0(X35,k4_xboole_0(X35,X36)),k1_xboole_0) ),
    inference(superposition,[],[f31,f736])).

fof(f736,plain,(
    ! [X8,X7] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8))) ),
    inference(forward_demodulation,[],[f735,f48])).

fof(f735,plain,(
    ! [X8,X7] : k4_xboole_0(X8,X8) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8))) ),
    inference(forward_demodulation,[],[f734,f18])).

fof(f734,plain,(
    ! [X8,X7] : k4_xboole_0(X8,k4_xboole_0(X8,k1_xboole_0)) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8))) ),
    inference(forward_demodulation,[],[f733,f48])).

fof(f733,plain,(
    ! [X8,X7] : k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X7,X7))) ),
    inference(forward_demodulation,[],[f703,f32])).

fof(f703,plain,(
    ! [X8,X7] : k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),X7) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8))) ),
    inference(superposition,[],[f494,f494])).

fof(f27067,plain,(
    ! [X54,X55,X53] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X53,X55),k4_xboole_0(k5_xboole_0(X53,k4_xboole_0(X54,X53)),X55)) ),
    inference(superposition,[],[f446,f1199])).

fof(f1199,plain,(
    ! [X19,X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X19))) = k4_xboole_0(X17,X19) ),
    inference(forward_demodulation,[],[f1132,f18])).

fof(f1132,plain,(
    ! [X19,X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X19))) = k4_xboole_0(k4_xboole_0(X17,k1_xboole_0),X19) ),
    inference(superposition,[],[f32,f30])).

fof(f44369,plain,(
    ! [X78,X77] : k4_xboole_0(k5_xboole_0(X77,X78),X77) = k5_xboole_0(k4_xboole_0(X78,X77),k4_xboole_0(k4_xboole_0(X78,X77),k4_xboole_0(k5_xboole_0(X77,X78),X77))) ),
    inference(forward_demodulation,[],[f44021,f18])).

fof(f44021,plain,(
    ! [X78,X77] : k5_xboole_0(k4_xboole_0(X78,X77),k4_xboole_0(k4_xboole_0(X78,X77),k4_xboole_0(k5_xboole_0(X77,X78),X77))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X77,X78),X77),k1_xboole_0) ),
    inference(superposition,[],[f426,f41366])).

fof(f44806,plain,(
    ! [X227,X226] : k5_xboole_0(X226,X227) = k4_xboole_0(k5_xboole_0(X226,k4_xboole_0(X227,X226)),k4_xboole_0(X226,k5_xboole_0(X226,X227))) ),
    inference(superposition,[],[f25395,f44371])).

fof(f25395,plain,(
    ! [X273,X272] : k4_xboole_0(k5_xboole_0(X273,k4_xboole_0(X272,X273)),k4_xboole_0(X273,X272)) = X272 ),
    inference(forward_demodulation,[],[f25394,f103])).

fof(f25394,plain,(
    ! [X273,X272] : k5_xboole_0(X272,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X273,k4_xboole_0(X272,X273)),k4_xboole_0(X273,X272)) ),
    inference(forward_demodulation,[],[f25222,f17679])).

fof(f17679,plain,(
    ! [X97,X98,X96] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X96,X98),k5_xboole_0(X96,k4_xboole_0(X97,X96))) ),
    inference(superposition,[],[f17567,f529])).

fof(f529,plain,(
    ! [X4,X5] : k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4)) = X4 ),
    inference(forward_demodulation,[],[f528,f18])).

fof(f528,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4)) ),
    inference(forward_demodulation,[],[f514,f30])).

fof(f514,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,k5_xboole_0(X4,k4_xboole_0(X5,X4)))) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4)) ),
    inference(superposition,[],[f31,f433])).

fof(f433,plain,(
    ! [X6,X5] : k4_xboole_0(X6,X5) = k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),X5) ),
    inference(forward_demodulation,[],[f432,f334])).

fof(f432,plain,(
    ! [X6,X5] : k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),X5) = k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),X5) ),
    inference(forward_demodulation,[],[f416,f18])).

fof(f416,plain,(
    ! [X6,X5] : k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),X5) = k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,k1_xboole_0)) ),
    inference(superposition,[],[f277,f30])).

fof(f17567,plain,(
    ! [X39,X38,X40] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X38,X39),X40),X38) ),
    inference(forward_demodulation,[],[f17460,f18])).

fof(f17460,plain,(
    ! [X39,X38,X40] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X38,X39),X40),k1_xboole_0),X38) ),
    inference(superposition,[],[f17265,f443])).

fof(f17265,plain,(
    ! [X54,X55,X53] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X55,k4_xboole_0(X55,k4_xboole_0(X53,X54))),X53) ),
    inference(forward_demodulation,[],[f17131,f18])).

fof(f17131,plain,(
    ! [X54,X55,X53] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X55,k4_xboole_0(X55,k4_xboole_0(k4_xboole_0(X53,X54),k1_xboole_0))),X53) ),
    inference(superposition,[],[f3842,f443])).

fof(f3842,plain,(
    ! [X43,X41,X42] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X41,k4_xboole_0(X41,k4_xboole_0(X42,k4_xboole_0(X42,X43)))),X43) ),
    inference(backward_demodulation,[],[f1245,f3577])).

fof(f1245,plain,(
    ! [X43,X41,X42] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X41,k4_xboole_0(X41,k4_xboole_0(X42,k4_xboole_0(X41,k4_xboole_0(X41,k4_xboole_0(X42,X43)))))),X43) ),
    inference(forward_demodulation,[],[f1174,f32])).

fof(f1174,plain,(
    ! [X43,X41,X42] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X41,k4_xboole_0(X41,X42)),k4_xboole_0(X41,k4_xboole_0(X41,k4_xboole_0(X42,X43)))),X43) ),
    inference(superposition,[],[f446,f32])).

fof(f25222,plain,(
    ! [X273,X272] : k5_xboole_0(X272,k4_xboole_0(k4_xboole_0(X273,X272),k5_xboole_0(X273,k4_xboole_0(X272,X273)))) = k4_xboole_0(k5_xboole_0(X273,k4_xboole_0(X272,X273)),k4_xboole_0(X273,X272)) ),
    inference(superposition,[],[f20572,f23374])).

fof(f23374,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X5,k5_xboole_0(X4,k4_xboole_0(X5,X4))) ),
    inference(forward_demodulation,[],[f23169,f341])).

fof(f23169,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X5,k5_xboole_0(k4_xboole_0(X5,X4),X4)) ),
    inference(superposition,[],[f22825,f2242])).

fof(f2242,plain,(
    ! [X24,X23,X25] : k5_xboole_0(k5_xboole_0(X24,X23),X25) = k5_xboole_0(X23,k5_xboole_0(X25,X24)) ),
    inference(forward_demodulation,[],[f2189,f24])).

fof(f2189,plain,(
    ! [X24,X23,X25] : k5_xboole_0(k5_xboole_0(X24,X23),X25) = k5_xboole_0(k5_xboole_0(X23,X25),X24) ),
    inference(superposition,[],[f635,f323])).

fof(f635,plain,(
    ! [X21,X22,X20] : k5_xboole_0(X21,X20) = k5_xboole_0(k5_xboole_0(X22,X20),k5_xboole_0(X22,X21)) ),
    inference(superposition,[],[f257,f323])).

fof(f257,plain,(
    ! [X12,X13,X11] : k5_xboole_0(k5_xboole_0(X11,X12),k5_xboole_0(X11,k5_xboole_0(X12,X13))) = X13 ),
    inference(forward_demodulation,[],[f226,f239])).

fof(f226,plain,(
    ! [X12,X13,X11] : k5_xboole_0(k1_xboole_0,X13) = k5_xboole_0(k5_xboole_0(X11,X12),k5_xboole_0(X11,k5_xboole_0(X12,X13))) ),
    inference(superposition,[],[f116,f24])).

fof(f37,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl2_1
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f45,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f40,f42])).

fof(f42,plain,
    ( spl2_2
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f40,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f29,f18])).

fof(f38,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f28,f35])).

fof(f28,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f16,f21,f23])).

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
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (29433)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.46  % (29427)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (29424)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (29432)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.46  % (29434)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (29434)Refutation not found, incomplete strategy% (29434)------------------------------
% 0.21/0.47  % (29434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (29434)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (29434)Memory used [KB]: 10490
% 0.21/0.47  % (29434)Time elapsed: 0.061 s
% 0.21/0.47  % (29434)------------------------------
% 0.21/0.47  % (29434)------------------------------
% 0.21/0.47  % (29426)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (29428)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (29423)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (29439)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.47  % (29435)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (29425)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (29429)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (29438)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (29436)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (29437)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (29430)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (29431)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (29440)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 5.15/1.01  % (29427)Time limit reached!
% 5.15/1.01  % (29427)------------------------------
% 5.15/1.01  % (29427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.15/1.01  % (29427)Termination reason: Time limit
% 5.15/1.01  % (29427)Termination phase: Saturation
% 5.15/1.01  
% 5.15/1.01  % (29427)Memory used [KB]: 15735
% 5.15/1.01  % (29427)Time elapsed: 0.600 s
% 5.15/1.01  % (29427)------------------------------
% 5.15/1.01  % (29427)------------------------------
% 12.40/1.96  % (29429)Time limit reached!
% 12.40/1.96  % (29429)------------------------------
% 12.40/1.96  % (29429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.40/1.97  % (29429)Termination reason: Time limit
% 12.40/1.97  
% 12.40/1.97  % (29429)Memory used [KB]: 40809
% 12.40/1.97  % (29429)Time elapsed: 1.530 s
% 12.40/1.97  % (29429)------------------------------
% 12.40/1.97  % (29429)------------------------------
% 13.07/2.01  % (29428)Time limit reached!
% 13.07/2.01  % (29428)------------------------------
% 13.07/2.01  % (29428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.07/2.01  % (29428)Termination reason: Time limit
% 13.07/2.01  % (29428)Termination phase: Saturation
% 13.07/2.01  
% 13.07/2.01  % (29428)Memory used [KB]: 44263
% 13.07/2.01  % (29428)Time elapsed: 1.500 s
% 13.07/2.01  % (29428)------------------------------
% 13.07/2.01  % (29428)------------------------------
% 14.08/2.22  % (29425)Time limit reached!
% 14.08/2.22  % (29425)------------------------------
% 14.08/2.22  % (29425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.93/2.23  % (29425)Termination reason: Time limit
% 14.93/2.23  % (29425)Termination phase: Saturation
% 14.93/2.23  
% 14.93/2.23  % (29425)Memory used [KB]: 44263
% 14.93/2.23  % (29425)Time elapsed: 1.800 s
% 14.93/2.23  % (29425)------------------------------
% 14.93/2.23  % (29425)------------------------------
% 17.96/2.61  % (29435)Time limit reached!
% 17.96/2.61  % (29435)------------------------------
% 17.96/2.61  % (29435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.96/2.61  % (29435)Termination reason: Time limit
% 17.96/2.61  % (29435)Termination phase: Saturation
% 17.96/2.61  
% 17.96/2.61  % (29435)Memory used [KB]: 63964
% 17.96/2.61  % (29435)Time elapsed: 2.200 s
% 17.96/2.61  % (29435)------------------------------
% 17.96/2.61  % (29435)------------------------------
% 20.45/2.92  % (29433)Refutation found. Thanks to Tanya!
% 20.45/2.92  % SZS status Theorem for theBenchmark
% 20.45/2.92  % SZS output start Proof for theBenchmark
% 20.45/2.92  fof(f45222,plain,(
% 20.45/2.92    $false),
% 20.45/2.92    inference(avatar_sat_refutation,[],[f38,f45,f45196])).
% 20.45/2.92  fof(f45196,plain,(
% 20.45/2.92    spl2_1),
% 20.45/2.92    inference(avatar_contradiction_clause,[],[f45194])).
% 20.45/2.92  fof(f45194,plain,(
% 20.45/2.92    $false | spl2_1),
% 20.45/2.92    inference(subsumption_resolution,[],[f37,f45193])).
% 20.45/2.92  fof(f45193,plain,(
% 20.45/2.92    ( ! [X227,X226] : (k5_xboole_0(X226,X227) = k4_xboole_0(k5_xboole_0(X226,k4_xboole_0(X227,X226)),k4_xboole_0(X226,k4_xboole_0(X226,X227)))) )),
% 20.45/2.92    inference(forward_demodulation,[],[f44806,f45077])).
% 20.45/2.92  fof(f45077,plain,(
% 20.45/2.92    ( ! [X28,X27] : (k4_xboole_0(X27,k4_xboole_0(X27,X28)) = k4_xboole_0(X27,k5_xboole_0(X27,X28))) )),
% 20.45/2.92    inference(forward_demodulation,[],[f45076,f251])).
% 20.45/2.92  fof(f251,plain,(
% 20.45/2.92    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 20.45/2.92    inference(forward_demodulation,[],[f220,f239])).
% 20.45/2.92  fof(f239,plain,(
% 20.45/2.92    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 20.45/2.92    inference(forward_demodulation,[],[f219,f103])).
% 20.45/2.92  fof(f103,plain,(
% 20.45/2.92    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 20.45/2.92    inference(forward_demodulation,[],[f92,f48])).
% 20.45/2.92  fof(f48,plain,(
% 20.45/2.92    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 20.45/2.92    inference(superposition,[],[f30,f29])).
% 20.45/2.92  fof(f29,plain,(
% 20.45/2.92    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 20.45/2.92    inference(definition_unfolding,[],[f17,f21])).
% 20.45/2.92  fof(f21,plain,(
% 20.45/2.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 20.45/2.92    inference(cnf_transformation,[],[f10])).
% 20.45/2.92  fof(f10,axiom,(
% 20.45/2.92    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 20.45/2.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 20.45/2.92  fof(f17,plain,(
% 20.45/2.92    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 20.45/2.92    inference(cnf_transformation,[],[f4])).
% 20.45/2.92  fof(f4,axiom,(
% 20.45/2.92    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 20.45/2.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 20.45/2.92  fof(f30,plain,(
% 20.45/2.92    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 20.45/2.92    inference(definition_unfolding,[],[f19,f21])).
% 20.45/2.92  fof(f19,plain,(
% 20.45/2.92    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 20.45/2.92    inference(cnf_transformation,[],[f6])).
% 20.45/2.92  fof(f6,axiom,(
% 20.45/2.92    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 20.45/2.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 20.45/2.92  fof(f92,plain,(
% 20.45/2.92    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 20.45/2.92    inference(superposition,[],[f27,f18])).
% 20.45/2.92  fof(f18,plain,(
% 20.45/2.92    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 20.45/2.92    inference(cnf_transformation,[],[f5])).
% 20.45/2.92  fof(f5,axiom,(
% 20.45/2.92    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 20.45/2.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 20.45/2.92  fof(f27,plain,(
% 20.45/2.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 20.45/2.92    inference(definition_unfolding,[],[f22,f23])).
% 20.45/2.92  fof(f23,plain,(
% 20.45/2.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 20.45/2.92    inference(cnf_transformation,[],[f7])).
% 20.45/2.92  fof(f7,axiom,(
% 20.45/2.92    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 20.45/2.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 20.45/2.92  fof(f22,plain,(
% 20.45/2.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 20.45/2.92    inference(cnf_transformation,[],[f2])).
% 20.45/2.92  fof(f2,axiom,(
% 20.45/2.92    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 20.45/2.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 20.45/2.92  fof(f219,plain,(
% 20.45/2.92    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 20.45/2.92    inference(superposition,[],[f116,f106])).
% 20.45/2.92  fof(f106,plain,(
% 20.45/2.92    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 20.45/2.92    inference(forward_demodulation,[],[f93,f18])).
% 20.45/2.92  fof(f93,plain,(
% 20.45/2.92    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 20.45/2.92    inference(superposition,[],[f27,f30])).
% 20.45/2.92  fof(f116,plain,(
% 20.45/2.92    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 20.45/2.92    inference(superposition,[],[f24,f106])).
% 20.45/2.92  fof(f24,plain,(
% 20.45/2.92    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 20.45/2.92    inference(cnf_transformation,[],[f9])).
% 20.45/2.92  fof(f9,axiom,(
% 20.45/2.92    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 20.45/2.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 20.45/2.92  fof(f220,plain,(
% 20.45/2.92    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 20.45/2.92    inference(superposition,[],[f116,f27])).
% 20.45/2.92  fof(f45076,plain,(
% 20.45/2.92    ( ! [X28,X27] : (k5_xboole_0(X27,k4_xboole_0(X27,X28)) = k4_xboole_0(X27,k5_xboole_0(X27,X28))) )),
% 20.45/2.92    inference(forward_demodulation,[],[f44729,f36132])).
% 20.45/2.92  fof(f36132,plain,(
% 20.45/2.92    ( ! [X101,X102] : (k4_xboole_0(X101,X102) = k4_xboole_0(k5_xboole_0(X101,X102),k4_xboole_0(X102,X101))) )),
% 20.45/2.92    inference(forward_demodulation,[],[f36128,f239])).
% 20.45/2.92  fof(f36128,plain,(
% 20.45/2.92    ( ! [X101,X102] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X101,X102)) = k4_xboole_0(k5_xboole_0(X101,X102),k4_xboole_0(X102,X101))) )),
% 20.45/2.92    inference(backward_demodulation,[],[f24022,f35939])).
% 20.45/2.92  fof(f35939,plain,(
% 20.45/2.92    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(X6,X5))) )),
% 20.45/2.92    inference(superposition,[],[f1841,f23180])).
% 20.45/2.92  fof(f23180,plain,(
% 20.45/2.92    ( ! [X14,X15] : (k5_xboole_0(X14,X15) = k5_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X15))) )),
% 20.45/2.92    inference(superposition,[],[f323,f22825])).
% 20.45/2.92  fof(f22825,plain,(
% 20.45/2.92    ( ! [X80,X81] : (k4_xboole_0(X80,X81) = k5_xboole_0(k5_xboole_0(X80,X81),k4_xboole_0(X81,X80))) )),
% 20.45/2.92    inference(superposition,[],[f20572,f334])).
% 20.45/2.92  fof(f334,plain,(
% 20.45/2.92    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X6,X5),X6) = X5) )),
% 20.45/2.92    inference(superposition,[],[f323,f323])).
% 20.45/2.92  fof(f20572,plain,(
% 20.45/2.92    ( ! [X24,X23] : (k5_xboole_0(X23,k4_xboole_0(k5_xboole_0(X23,X24),X24)) = k4_xboole_0(X24,k5_xboole_0(X23,X24))) )),
% 20.45/2.92    inference(backward_demodulation,[],[f20541,f20571])).
% 20.45/2.92  fof(f20571,plain,(
% 20.45/2.92    ( ! [X72,X71] : (k4_xboole_0(k5_xboole_0(X72,k4_xboole_0(k5_xboole_0(X71,X72),X72)),k5_xboole_0(X71,X72)) = k4_xboole_0(X72,k5_xboole_0(X71,X72))) )),
% 20.45/2.92    inference(forward_demodulation,[],[f20570,f27])).
% 20.45/2.92  fof(f20570,plain,(
% 20.45/2.92    ( ! [X72,X71] : (k4_xboole_0(k5_xboole_0(X72,k4_xboole_0(k5_xboole_0(X71,X72),X72)),k5_xboole_0(X71,X72)) = k5_xboole_0(X72,k4_xboole_0(X72,k4_xboole_0(X72,k5_xboole_0(X71,X72))))) )),
% 20.45/2.92    inference(forward_demodulation,[],[f20569,f1066])).
% 20.45/2.92  fof(f1066,plain,(
% 20.45/2.92    ( ! [X12,X13,X11] : (k5_xboole_0(X13,k4_xboole_0(X12,k4_xboole_0(X12,X11))) = k5_xboole_0(X11,k5_xboole_0(X13,k4_xboole_0(X11,X12)))) )),
% 20.45/2.92    inference(superposition,[],[f349,f277])).
% 20.45/2.92  fof(f277,plain,(
% 20.45/2.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 20.45/2.92    inference(superposition,[],[f27,f31])).
% 20.45/2.92  fof(f31,plain,(
% 20.45/2.92    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 20.45/2.92    inference(definition_unfolding,[],[f20,f23,f23])).
% 20.45/2.92  fof(f20,plain,(
% 20.45/2.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 20.45/2.92    inference(cnf_transformation,[],[f1])).
% 20.45/2.92  fof(f1,axiom,(
% 20.45/2.92    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 20.45/2.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 20.45/2.92  fof(f349,plain,(
% 20.45/2.92    ( ! [X6,X4,X5] : (k5_xboole_0(X5,X6) = k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,X6)))) )),
% 20.45/2.92    inference(forward_demodulation,[],[f342,f24])).
% 20.45/2.92  fof(f342,plain,(
% 20.45/2.92    ( ! [X6,X4,X5] : (k5_xboole_0(X5,X6) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X5,X4),X6))) )),
% 20.45/2.92    inference(superposition,[],[f24,f323])).
% 20.45/2.92  fof(f20569,plain,(
% 20.45/2.92    ( ! [X72,X71] : (k4_xboole_0(k5_xboole_0(X72,k4_xboole_0(k5_xboole_0(X71,X72),X72)),k5_xboole_0(X71,X72)) = k5_xboole_0(k5_xboole_0(X71,X72),k5_xboole_0(X72,k4_xboole_0(k5_xboole_0(X71,X72),X72)))) )),
% 20.45/2.92    inference(forward_demodulation,[],[f20441,f18])).
% 20.45/2.92  fof(f20441,plain,(
% 20.45/2.92    ( ! [X72,X71] : (k4_xboole_0(k5_xboole_0(X72,k4_xboole_0(k5_xboole_0(X71,X72),X72)),k5_xboole_0(X71,X72)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X71,X72),k1_xboole_0),k5_xboole_0(X72,k4_xboole_0(k5_xboole_0(X71,X72),X72)))) )),
% 20.45/2.92    inference(superposition,[],[f896,f19147])).
% 20.45/2.92  fof(f19147,plain,(
% 20.45/2.92    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,X2),X2)))) )),
% 20.45/2.92    inference(forward_demodulation,[],[f19146,f341])).
% 20.45/2.92  fof(f341,plain,(
% 20.45/2.92    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2)) )),
% 20.45/2.92    inference(superposition,[],[f248,f323])).
% 20.45/2.92  fof(f248,plain,(
% 20.45/2.92    ( ! [X4,X5] : (k5_xboole_0(X4,k5_xboole_0(X4,X5)) = X5) )),
% 20.45/2.92    inference(forward_demodulation,[],[f240,f239])).
% 20.45/2.92  fof(f240,plain,(
% 20.45/2.92    ( ! [X4,X5] : (k5_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X4,k5_xboole_0(X4,X5))) )),
% 20.45/2.92    inference(backward_demodulation,[],[f217,f239])).
% 20.45/2.92  fof(f217,plain,(
% 20.45/2.92    ( ! [X4,X5] : (k5_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X4,k5_xboole_0(k1_xboole_0,k5_xboole_0(X4,X5)))) )),
% 20.45/2.92    inference(forward_demodulation,[],[f209,f24])).
% 20.45/2.92  fof(f209,plain,(
% 20.45/2.92    ( ! [X4,X5] : (k5_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(k1_xboole_0,X4),X5))) )),
% 20.45/2.92    inference(superposition,[],[f24,f172])).
% 20.45/2.92  fof(f172,plain,(
% 20.45/2.92    ( ! [X7] : (k1_xboole_0 = k5_xboole_0(X7,k5_xboole_0(k1_xboole_0,X7))) )),
% 20.45/2.92    inference(superposition,[],[f114,f103])).
% 20.45/2.92  fof(f114,plain,(
% 20.45/2.92    ( ! [X2,X1] : (k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))) )),
% 20.45/2.92    inference(superposition,[],[f106,f24])).
% 20.45/2.92  fof(f19146,plain,(
% 20.45/2.92    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(k4_xboole_0(k5_xboole_0(X3,X2),X2),X2))) )),
% 20.45/2.92    inference(forward_demodulation,[],[f18888,f4943])).
% 20.45/2.92  fof(f4943,plain,(
% 20.45/2.92    ( ! [X80,X81,X79] : (k5_xboole_0(k4_xboole_0(k5_xboole_0(X79,X80),X81),X80) = k5_xboole_0(X79,k4_xboole_0(X81,k4_xboole_0(X81,k5_xboole_0(X79,X80))))) )),
% 20.45/2.92    inference(superposition,[],[f349,f429])).
% 20.45/2.92  fof(f429,plain,(
% 20.45/2.92    ( ! [X12,X11] : (k4_xboole_0(X12,k4_xboole_0(X12,X11)) = k5_xboole_0(k4_xboole_0(X11,X12),X11)) )),
% 20.45/2.92    inference(superposition,[],[f334,f277])).
% 20.45/2.92  fof(f18888,plain,(
% 20.45/2.92    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,X2)))))) )),
% 20.45/2.92    inference(superposition,[],[f71,f251])).
% 20.45/2.92  fof(f71,plain,(
% 20.45/2.92    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X4,k5_xboole_0(X2,X3)))))) )),
% 20.45/2.92    inference(superposition,[],[f30,f24])).
% 20.45/2.92  fof(f896,plain,(
% 20.45/2.92    ( ! [X26,X25] : (k4_xboole_0(X25,X26) = k5_xboole_0(k4_xboole_0(X26,k4_xboole_0(X26,X25)),X25)) )),
% 20.45/2.92    inference(superposition,[],[f334,f426])).
% 20.45/2.92  fof(f426,plain,(
% 20.45/2.92    ( ! [X6,X5] : (k4_xboole_0(X6,k4_xboole_0(X6,X5)) = k5_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 20.45/2.92    inference(superposition,[],[f248,f277])).
% 20.45/2.92  fof(f20541,plain,(
% 20.45/2.92    ( ! [X24,X23] : (k4_xboole_0(k5_xboole_0(X24,k4_xboole_0(k5_xboole_0(X23,X24),X24)),k5_xboole_0(X23,X24)) = k5_xboole_0(X23,k4_xboole_0(k5_xboole_0(X23,X24),X24))) )),
% 20.45/2.92    inference(forward_demodulation,[],[f20540,f1010])).
% 20.45/2.92  fof(f1010,plain,(
% 20.45/2.92    ( ! [X24,X23,X25] : (k5_xboole_0(X25,X23) = k5_xboole_0(k5_xboole_0(X24,X23),k5_xboole_0(X25,X24))) )),
% 20.45/2.92    inference(superposition,[],[f336,f323])).
% 20.45/2.92  fof(f336,plain,(
% 20.45/2.92    ( ! [X10,X8,X9] : (k5_xboole_0(X8,X9) = k5_xboole_0(X10,k5_xboole_0(X8,k5_xboole_0(X9,X10)))) )),
% 20.45/2.92    inference(superposition,[],[f323,f24])).
% 20.45/2.92  fof(f20540,plain,(
% 20.45/2.92    ( ! [X24,X23] : (k4_xboole_0(k5_xboole_0(X24,k4_xboole_0(k5_xboole_0(X23,X24),X24)),k5_xboole_0(X23,X24)) = k5_xboole_0(k5_xboole_0(X24,k4_xboole_0(k5_xboole_0(X23,X24),X24)),k5_xboole_0(X23,X24))) )),
% 20.45/2.92    inference(forward_demodulation,[],[f20421,f18])).
% 20.45/2.92  fof(f20421,plain,(
% 20.45/2.92    ( ! [X24,X23] : (k4_xboole_0(k5_xboole_0(X24,k4_xboole_0(k5_xboole_0(X23,X24),X24)),k5_xboole_0(X23,X24)) = k5_xboole_0(k5_xboole_0(X24,k4_xboole_0(k5_xboole_0(X23,X24),X24)),k4_xboole_0(k5_xboole_0(X23,X24),k1_xboole_0))) )),
% 20.45/2.92    inference(superposition,[],[f277,f19147])).
% 20.45/2.92  fof(f323,plain,(
% 20.45/2.92    ( ! [X4,X3] : (k5_xboole_0(X4,k5_xboole_0(X3,X4)) = X3) )),
% 20.45/2.92    inference(forward_demodulation,[],[f310,f103])).
% 20.45/2.92  fof(f310,plain,(
% 20.45/2.92    ( ! [X4,X3] : (k5_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X4,k5_xboole_0(X3,X4))) )),
% 20.45/2.92    inference(superposition,[],[f248,f114])).
% 20.45/2.92  fof(f1841,plain,(
% 20.45/2.92    ( ! [X24,X23,X22] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X23,X24),k5_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X22,X23)))) )),
% 20.45/2.92    inference(superposition,[],[f30,f1589])).
% 20.45/2.92  fof(f1589,plain,(
% 20.45/2.92    ( ! [X19,X17,X18] : (k4_xboole_0(X18,X17) = k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(X17,X19))) )),
% 20.45/2.92    inference(superposition,[],[f1558,f1317])).
% 20.45/2.92  fof(f1317,plain,(
% 20.45/2.92    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1) )),
% 20.45/2.92    inference(forward_demodulation,[],[f1283,f103])).
% 20.45/2.92  fof(f1283,plain,(
% 20.45/2.92    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X2,X1))) )),
% 20.45/2.92    inference(superposition,[],[f27,f1148])).
% 20.45/2.92  fof(f1148,plain,(
% 20.45/2.92    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 20.45/2.92    inference(superposition,[],[f32,f443])).
% 20.45/2.92  fof(f443,plain,(
% 20.45/2.92    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),X4)) )),
% 20.45/2.92    inference(backward_demodulation,[],[f279,f428])).
% 20.45/2.92  fof(f428,plain,(
% 20.45/2.92    ( ! [X10,X9] : (k5_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X10,k4_xboole_0(X10,X9))) = X9) )),
% 20.45/2.92    inference(superposition,[],[f333,f277])).
% 20.45/2.92  fof(f333,plain,(
% 20.45/2.92    ( ! [X4,X3] : (k5_xboole_0(k5_xboole_0(X3,X4),X4) = X3) )),
% 20.45/2.92    inference(superposition,[],[f323,f248])).
% 20.45/2.92  fof(f279,plain,(
% 20.45/2.92    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X5,X4))))) )),
% 20.45/2.92    inference(superposition,[],[f30,f31])).
% 20.45/2.92  fof(f32,plain,(
% 20.45/2.92    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 20.45/2.92    inference(definition_unfolding,[],[f25,f23,f23])).
% 20.45/2.92  fof(f25,plain,(
% 20.45/2.92    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 20.45/2.92    inference(cnf_transformation,[],[f8])).
% 20.45/2.92  fof(f8,axiom,(
% 20.45/2.92    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 20.45/2.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 20.45/2.92  fof(f1558,plain,(
% 20.45/2.92    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0) )),
% 20.45/2.92    inference(forward_demodulation,[],[f1500,f103])).
% 20.45/2.92  fof(f1500,plain,(
% 20.45/2.92    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) )),
% 20.45/2.92    inference(superposition,[],[f27,f1320])).
% 20.45/2.92  fof(f1320,plain,(
% 20.45/2.92    ( ! [X8,X7,X9] : (k1_xboole_0 = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(k4_xboole_0(X8,X7),X9)))) )),
% 20.45/2.92    inference(forward_demodulation,[],[f1284,f127])).
% 20.45/2.92  fof(f127,plain,(
% 20.45/2.92    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 20.45/2.92    inference(forward_demodulation,[],[f124,f103])).
% 20.45/2.92  fof(f124,plain,(
% 20.45/2.92    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X1)) )),
% 20.45/2.92    inference(superposition,[],[f27,f100])).
% 20.45/2.92  fof(f100,plain,(
% 20.45/2.92    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) )),
% 20.45/2.92    inference(superposition,[],[f46,f27])).
% 20.45/2.92  fof(f46,plain,(
% 20.45/2.92    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 20.45/2.92    inference(superposition,[],[f30,f18])).
% 20.45/2.92  fof(f1284,plain,(
% 20.45/2.92    ( ! [X8,X7,X9] : (k4_xboole_0(k1_xboole_0,X9) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(k4_xboole_0(X8,X7),X9)))) )),
% 20.45/2.92    inference(superposition,[],[f32,f1148])).
% 20.45/2.92  fof(f24022,plain,(
% 20.45/2.92    ( ! [X101,X102] : (k4_xboole_0(k5_xboole_0(X101,X102),k4_xboole_0(X102,X101)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X102,X101),k5_xboole_0(X101,X102)),k4_xboole_0(X101,X102))) )),
% 20.45/2.92    inference(superposition,[],[f23173,f22825])).
% 20.45/2.92  fof(f23173,plain,(
% 20.45/2.92    ( ! [X12,X13] : (k4_xboole_0(X12,X13) = k5_xboole_0(k4_xboole_0(X13,X12),k5_xboole_0(X12,X13))) )),
% 20.45/2.92    inference(superposition,[],[f22825,f341])).
% 20.45/2.92  fof(f44729,plain,(
% 20.45/2.92    ( ! [X28,X27] : (k4_xboole_0(X27,k5_xboole_0(X27,X28)) = k5_xboole_0(X27,k4_xboole_0(k5_xboole_0(X27,X28),k4_xboole_0(X28,X27)))) )),
% 20.45/2.92    inference(superposition,[],[f277,f44371])).
% 20.45/2.92  fof(f44371,plain,(
% 20.45/2.92    ( ! [X78,X77] : (k4_xboole_0(X78,X77) = k4_xboole_0(k5_xboole_0(X77,X78),X77)) )),
% 20.45/2.92    inference(forward_demodulation,[],[f44370,f103])).
% 20.45/2.92  fof(f44370,plain,(
% 20.45/2.92    ( ! [X78,X77] : (k4_xboole_0(k5_xboole_0(X77,X78),X77) = k5_xboole_0(k4_xboole_0(X78,X77),k1_xboole_0)) )),
% 20.45/2.92    inference(forward_demodulation,[],[f44369,f43840])).
% 20.45/2.92  fof(f43840,plain,(
% 20.45/2.92    ( ! [X28,X27] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X28,X27),k4_xboole_0(k5_xboole_0(X27,X28),X27))) )),
% 20.45/2.92    inference(superposition,[],[f41366,f248])).
% 20.45/2.92  fof(f41366,plain,(
% 20.45/2.92    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X2,X3),X2),k4_xboole_0(X3,X2))) )),
% 20.45/2.92    inference(superposition,[],[f33427,f36124])).
% 20.45/2.92  fof(f36124,plain,(
% 20.45/2.92    ( ! [X103,X104] : (k4_xboole_0(X104,X103) = k4_xboole_0(k5_xboole_0(X103,X104),k4_xboole_0(X103,X104))) )),
% 20.45/2.92    inference(forward_demodulation,[],[f36121,f239])).
% 20.45/2.92  fof(f36121,plain,(
% 20.45/2.92    ( ! [X103,X104] : (k4_xboole_0(k5_xboole_0(X103,X104),k4_xboole_0(X103,X104)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X104,X103))) )),
% 20.45/2.92    inference(backward_demodulation,[],[f24023,f35938])).
% 20.45/2.92  fof(f35938,plain,(
% 20.45/2.92    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X3,X4))) )),
% 20.45/2.92    inference(superposition,[],[f1841,f23181])).
% 20.45/2.92  fof(f23181,plain,(
% 20.45/2.92    ( ! [X17,X16] : (k5_xboole_0(X16,X17) = k5_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X17,X16))) )),
% 20.45/2.92    inference(superposition,[],[f333,f22825])).
% 20.45/2.93  fof(f24023,plain,(
% 20.45/2.93    ( ! [X103,X104] : (k4_xboole_0(k5_xboole_0(X103,X104),k4_xboole_0(X103,X104)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X103,X104),k5_xboole_0(X103,X104)),k4_xboole_0(X104,X103))) )),
% 20.45/2.93    inference(superposition,[],[f23173,f22826])).
% 20.45/2.93  fof(f22826,plain,(
% 20.45/2.93    ( ! [X83,X82] : (k4_xboole_0(X83,X82) = k5_xboole_0(k5_xboole_0(X82,X83),k4_xboole_0(X82,X83))) )),
% 20.45/2.93    inference(superposition,[],[f20572,f333])).
% 20.45/2.93  fof(f33427,plain,(
% 20.45/2.93    ( ! [X21,X19,X20] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X19,k4_xboole_0(X20,X21)))) )),
% 20.45/2.93    inference(superposition,[],[f33143,f1589])).
% 20.45/2.93  fof(f33143,plain,(
% 20.45/2.93    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(X2,X4))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f33142,f248])).
% 20.45/2.93  fof(f33142,plain,(
% 20.45/2.93    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(X3,k5_xboole_0(X3,X2)),X4))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f33141,f23180])).
% 20.45/2.93  fof(f33141,plain,(
% 20.45/2.93    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(X3,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))),X4))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f33140,f1065])).
% 20.45/2.93  fof(f1065,plain,(
% 20.45/2.93    ( ! [X10,X8,X9] : (k5_xboole_0(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))) = k5_xboole_0(X8,k5_xboole_0(X10,k4_xboole_0(X8,X9)))) )),
% 20.45/2.93    inference(superposition,[],[f349,f27])).
% 20.45/2.93  fof(f33140,plain,(
% 20.45/2.93    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,k4_xboole_0(X3,X2))),X4))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f32943,f18])).
% 20.45/2.93  fof(f32943,plain,(
% 20.45/2.93    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),k1_xboole_0)),X4))) )),
% 20.45/2.93    inference(superposition,[],[f27067,f18698])).
% 20.45/2.93  fof(f18698,plain,(
% 20.45/2.93    ( ! [X35,X36] : (k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k1_xboole_0)) )),
% 20.45/2.93    inference(forward_demodulation,[],[f18697,f48])).
% 20.45/2.93  fof(f18697,plain,(
% 20.45/2.93    ( ! [X35,X36] : (k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X36,X36))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f18696,f18])).
% 20.45/2.93  fof(f18696,plain,(
% 20.45/2.93    ( ! [X35,X36] : (k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X36,k4_xboole_0(X36,k1_xboole_0)))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f18695,f48])).
% 20.45/2.93  fof(f18695,plain,(
% 20.45/2.93    ( ! [X35,X36] : (k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X35,X35))))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f18694,f3852])).
% 20.45/2.93  fof(f3852,plain,(
% 20.45/2.93    ( ! [X24,X23,X25] : (k4_xboole_0(X23,k4_xboole_0(X23,k4_xboole_0(X24,X25))) = k4_xboole_0(X23,k4_xboole_0(X23,k4_xboole_0(X24,k4_xboole_0(X25,k4_xboole_0(X25,X23)))))) )),
% 20.45/2.93    inference(backward_demodulation,[],[f1233,f3844])).
% 20.45/2.93  fof(f3844,plain,(
% 20.45/2.93    ( ! [X47,X48,X49] : (k4_xboole_0(X49,k4_xboole_0(X47,k4_xboole_0(X47,X48))) = k4_xboole_0(X49,k4_xboole_0(X47,k4_xboole_0(X47,k4_xboole_0(X48,k4_xboole_0(X48,X49)))))) )),
% 20.45/2.93    inference(backward_demodulation,[],[f1247,f3577])).
% 20.45/2.93  fof(f3577,plain,(
% 20.45/2.93    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5)))) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5))))))) )),
% 20.45/2.93    inference(superposition,[],[f39,f32])).
% 20.45/2.93  fof(f39,plain,(
% 20.45/2.93    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f33,f32])).
% 20.45/2.93  fof(f33,plain,(
% 20.45/2.93    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 20.45/2.93    inference(definition_unfolding,[],[f26,f23,f23,f23,f23])).
% 20.45/2.93  fof(f26,plain,(
% 20.45/2.93    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 20.45/2.93    inference(cnf_transformation,[],[f3])).
% 20.45/2.93  fof(f3,axiom,(
% 20.45/2.93    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 20.45/2.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 20.45/2.93  fof(f1247,plain,(
% 20.45/2.93    ( ! [X47,X48,X49] : (k4_xboole_0(X49,k4_xboole_0(X47,k4_xboole_0(X47,X48))) = k4_xboole_0(X49,k4_xboole_0(X47,k4_xboole_0(X47,k4_xboole_0(X48,k4_xboole_0(X47,k4_xboole_0(X47,k4_xboole_0(X48,X49)))))))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f1176,f32])).
% 20.45/2.93  fof(f1176,plain,(
% 20.45/2.93    ( ! [X47,X48,X49] : (k4_xboole_0(X49,k4_xboole_0(X47,k4_xboole_0(X47,X48))) = k4_xboole_0(X49,k4_xboole_0(k4_xboole_0(X47,k4_xboole_0(X47,X48)),k4_xboole_0(X47,k4_xboole_0(X47,k4_xboole_0(X48,X49)))))) )),
% 20.45/2.93    inference(superposition,[],[f494,f32])).
% 20.45/2.93  fof(f494,plain,(
% 20.45/2.93    ( ! [X10,X9] : (k4_xboole_0(X10,X9) = k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f493,f277])).
% 20.45/2.93  fof(f493,plain,(
% 20.45/2.93    ( ! [X10,X9] : (k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k5_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f480,f18])).
% 20.45/2.93  fof(f480,plain,(
% 20.45/2.93    ( ! [X10,X9] : (k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k5_xboole_0(X10,k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),k1_xboole_0))) )),
% 20.45/2.93    inference(superposition,[],[f277,f446])).
% 20.45/2.93  fof(f446,plain,(
% 20.45/2.93    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1)) )),
% 20.45/2.93    inference(superposition,[],[f443,f31])).
% 20.45/2.93  fof(f1233,plain,(
% 20.45/2.93    ( ! [X24,X23,X25] : (k4_xboole_0(X23,k4_xboole_0(X23,k4_xboole_0(X24,k4_xboole_0(X25,k4_xboole_0(X25,k4_xboole_0(X23,k4_xboole_0(X23,X24))))))) = k4_xboole_0(X23,k4_xboole_0(X23,k4_xboole_0(X24,X25)))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f1156,f32])).
% 20.45/2.93  fof(f1156,plain,(
% 20.45/2.93    ( ! [X24,X23,X25] : (k4_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,X24)),X25) = k4_xboole_0(X23,k4_xboole_0(X23,k4_xboole_0(X24,k4_xboole_0(X25,k4_xboole_0(X25,k4_xboole_0(X23,k4_xboole_0(X23,X24)))))))) )),
% 20.45/2.93    inference(superposition,[],[f32,f494])).
% 20.45/2.93  fof(f18694,plain,(
% 20.45/2.93    ( ! [X35,X36] : (k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X35,X36))))))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f18693,f32])).
% 20.45/2.93  fof(f18693,plain,(
% 20.45/2.93    ( ! [X35,X36] : (k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X35,k4_xboole_0(X35,X36))))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f18469,f18])).
% 20.45/2.93  fof(f18469,plain,(
% 20.45/2.93    ( ! [X35,X36] : (k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X35,k4_xboole_0(X35,X36)))) = k4_xboole_0(k4_xboole_0(X35,k4_xboole_0(X35,X36)),k1_xboole_0)) )),
% 20.45/2.93    inference(superposition,[],[f31,f736])).
% 20.45/2.93  fof(f736,plain,(
% 20.45/2.93    ( ! [X8,X7] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8)))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f735,f48])).
% 20.45/2.93  fof(f735,plain,(
% 20.45/2.93    ( ! [X8,X7] : (k4_xboole_0(X8,X8) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8)))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f734,f18])).
% 20.45/2.93  fof(f734,plain,(
% 20.45/2.93    ( ! [X8,X7] : (k4_xboole_0(X8,k4_xboole_0(X8,k1_xboole_0)) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8)))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f733,f48])).
% 20.45/2.93  fof(f733,plain,(
% 20.45/2.93    ( ! [X8,X7] : (k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X7,X7)))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f703,f32])).
% 20.45/2.93  fof(f703,plain,(
% 20.45/2.93    ( ! [X8,X7] : (k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),X7) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),k4_xboole_0(X7,k4_xboole_0(X7,X8)))) )),
% 20.45/2.93    inference(superposition,[],[f494,f494])).
% 20.45/2.93  fof(f27067,plain,(
% 20.45/2.93    ( ! [X54,X55,X53] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X53,X55),k4_xboole_0(k5_xboole_0(X53,k4_xboole_0(X54,X53)),X55))) )),
% 20.45/2.93    inference(superposition,[],[f446,f1199])).
% 20.45/2.93  fof(f1199,plain,(
% 20.45/2.93    ( ! [X19,X17,X18] : (k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X19))) = k4_xboole_0(X17,X19)) )),
% 20.45/2.93    inference(forward_demodulation,[],[f1132,f18])).
% 20.45/2.93  fof(f1132,plain,(
% 20.45/2.93    ( ! [X19,X17,X18] : (k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X19))) = k4_xboole_0(k4_xboole_0(X17,k1_xboole_0),X19)) )),
% 20.45/2.93    inference(superposition,[],[f32,f30])).
% 20.45/2.93  fof(f44369,plain,(
% 20.45/2.93    ( ! [X78,X77] : (k4_xboole_0(k5_xboole_0(X77,X78),X77) = k5_xboole_0(k4_xboole_0(X78,X77),k4_xboole_0(k4_xboole_0(X78,X77),k4_xboole_0(k5_xboole_0(X77,X78),X77)))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f44021,f18])).
% 20.45/2.93  fof(f44021,plain,(
% 20.45/2.93    ( ! [X78,X77] : (k5_xboole_0(k4_xboole_0(X78,X77),k4_xboole_0(k4_xboole_0(X78,X77),k4_xboole_0(k5_xboole_0(X77,X78),X77))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X77,X78),X77),k1_xboole_0)) )),
% 20.45/2.93    inference(superposition,[],[f426,f41366])).
% 20.45/2.93  fof(f44806,plain,(
% 20.45/2.93    ( ! [X227,X226] : (k5_xboole_0(X226,X227) = k4_xboole_0(k5_xboole_0(X226,k4_xboole_0(X227,X226)),k4_xboole_0(X226,k5_xboole_0(X226,X227)))) )),
% 20.45/2.93    inference(superposition,[],[f25395,f44371])).
% 20.45/2.93  fof(f25395,plain,(
% 20.45/2.93    ( ! [X273,X272] : (k4_xboole_0(k5_xboole_0(X273,k4_xboole_0(X272,X273)),k4_xboole_0(X273,X272)) = X272) )),
% 20.45/2.93    inference(forward_demodulation,[],[f25394,f103])).
% 20.45/2.93  fof(f25394,plain,(
% 20.45/2.93    ( ! [X273,X272] : (k5_xboole_0(X272,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X273,k4_xboole_0(X272,X273)),k4_xboole_0(X273,X272))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f25222,f17679])).
% 20.45/2.93  fof(f17679,plain,(
% 20.45/2.93    ( ! [X97,X98,X96] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X96,X98),k5_xboole_0(X96,k4_xboole_0(X97,X96)))) )),
% 20.45/2.93    inference(superposition,[],[f17567,f529])).
% 20.45/2.93  fof(f529,plain,(
% 20.45/2.93    ( ! [X4,X5] : (k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4)) = X4) )),
% 20.45/2.93    inference(forward_demodulation,[],[f528,f18])).
% 20.45/2.93  fof(f528,plain,(
% 20.45/2.93    ( ! [X4,X5] : (k4_xboole_0(X4,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f514,f30])).
% 20.45/2.93  fof(f514,plain,(
% 20.45/2.93    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,k5_xboole_0(X4,k4_xboole_0(X5,X4)))) = k4_xboole_0(k5_xboole_0(X4,k4_xboole_0(X5,X4)),k4_xboole_0(X5,X4))) )),
% 20.45/2.93    inference(superposition,[],[f31,f433])).
% 20.45/2.93  fof(f433,plain,(
% 20.45/2.93    ( ! [X6,X5] : (k4_xboole_0(X6,X5) = k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),X5)) )),
% 20.45/2.93    inference(forward_demodulation,[],[f432,f334])).
% 20.45/2.93  fof(f432,plain,(
% 20.45/2.93    ( ! [X6,X5] : (k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),X5) = k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),X5)) )),
% 20.45/2.93    inference(forward_demodulation,[],[f416,f18])).
% 20.45/2.93  fof(f416,plain,(
% 20.45/2.93    ( ! [X6,X5] : (k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),X5) = k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,k1_xboole_0))) )),
% 20.45/2.93    inference(superposition,[],[f277,f30])).
% 20.45/2.93  fof(f17567,plain,(
% 20.45/2.93    ( ! [X39,X38,X40] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X38,X39),X40),X38)) )),
% 20.45/2.93    inference(forward_demodulation,[],[f17460,f18])).
% 20.45/2.93  fof(f17460,plain,(
% 20.45/2.93    ( ! [X39,X38,X40] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X38,X39),X40),k1_xboole_0),X38)) )),
% 20.45/2.93    inference(superposition,[],[f17265,f443])).
% 20.45/2.93  fof(f17265,plain,(
% 20.45/2.93    ( ! [X54,X55,X53] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X55,k4_xboole_0(X55,k4_xboole_0(X53,X54))),X53)) )),
% 20.45/2.93    inference(forward_demodulation,[],[f17131,f18])).
% 20.45/2.93  fof(f17131,plain,(
% 20.45/2.93    ( ! [X54,X55,X53] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X55,k4_xboole_0(X55,k4_xboole_0(k4_xboole_0(X53,X54),k1_xboole_0))),X53)) )),
% 20.45/2.93    inference(superposition,[],[f3842,f443])).
% 20.45/2.93  fof(f3842,plain,(
% 20.45/2.93    ( ! [X43,X41,X42] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X41,k4_xboole_0(X41,k4_xboole_0(X42,k4_xboole_0(X42,X43)))),X43)) )),
% 20.45/2.93    inference(backward_demodulation,[],[f1245,f3577])).
% 20.45/2.93  fof(f1245,plain,(
% 20.45/2.93    ( ! [X43,X41,X42] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X41,k4_xboole_0(X41,k4_xboole_0(X42,k4_xboole_0(X41,k4_xboole_0(X41,k4_xboole_0(X42,X43)))))),X43)) )),
% 20.45/2.93    inference(forward_demodulation,[],[f1174,f32])).
% 20.45/2.93  fof(f1174,plain,(
% 20.45/2.93    ( ! [X43,X41,X42] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X41,k4_xboole_0(X41,X42)),k4_xboole_0(X41,k4_xboole_0(X41,k4_xboole_0(X42,X43)))),X43)) )),
% 20.45/2.93    inference(superposition,[],[f446,f32])).
% 20.45/2.93  fof(f25222,plain,(
% 20.45/2.93    ( ! [X273,X272] : (k5_xboole_0(X272,k4_xboole_0(k4_xboole_0(X273,X272),k5_xboole_0(X273,k4_xboole_0(X272,X273)))) = k4_xboole_0(k5_xboole_0(X273,k4_xboole_0(X272,X273)),k4_xboole_0(X273,X272))) )),
% 20.45/2.93    inference(superposition,[],[f20572,f23374])).
% 20.45/2.93  fof(f23374,plain,(
% 20.45/2.93    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k5_xboole_0(X5,k5_xboole_0(X4,k4_xboole_0(X5,X4)))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f23169,f341])).
% 20.45/2.93  fof(f23169,plain,(
% 20.45/2.93    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k5_xboole_0(X5,k5_xboole_0(k4_xboole_0(X5,X4),X4))) )),
% 20.45/2.93    inference(superposition,[],[f22825,f2242])).
% 20.45/2.93  fof(f2242,plain,(
% 20.45/2.93    ( ! [X24,X23,X25] : (k5_xboole_0(k5_xboole_0(X24,X23),X25) = k5_xboole_0(X23,k5_xboole_0(X25,X24))) )),
% 20.45/2.93    inference(forward_demodulation,[],[f2189,f24])).
% 20.45/2.93  fof(f2189,plain,(
% 20.45/2.93    ( ! [X24,X23,X25] : (k5_xboole_0(k5_xboole_0(X24,X23),X25) = k5_xboole_0(k5_xboole_0(X23,X25),X24)) )),
% 20.45/2.93    inference(superposition,[],[f635,f323])).
% 20.45/2.93  fof(f635,plain,(
% 20.45/2.93    ( ! [X21,X22,X20] : (k5_xboole_0(X21,X20) = k5_xboole_0(k5_xboole_0(X22,X20),k5_xboole_0(X22,X21))) )),
% 20.45/2.93    inference(superposition,[],[f257,f323])).
% 20.45/2.93  fof(f257,plain,(
% 20.45/2.93    ( ! [X12,X13,X11] : (k5_xboole_0(k5_xboole_0(X11,X12),k5_xboole_0(X11,k5_xboole_0(X12,X13))) = X13) )),
% 20.45/2.93    inference(forward_demodulation,[],[f226,f239])).
% 20.45/2.93  fof(f226,plain,(
% 20.45/2.93    ( ! [X12,X13,X11] : (k5_xboole_0(k1_xboole_0,X13) = k5_xboole_0(k5_xboole_0(X11,X12),k5_xboole_0(X11,k5_xboole_0(X12,X13)))) )),
% 20.45/2.93    inference(superposition,[],[f116,f24])).
% 20.45/2.93  fof(f37,plain,(
% 20.45/2.93    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 20.45/2.93    inference(avatar_component_clause,[],[f35])).
% 20.45/2.93  fof(f35,plain,(
% 20.45/2.93    spl2_1 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 20.45/2.93    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 20.45/2.93  fof(f45,plain,(
% 20.45/2.93    spl2_2),
% 20.45/2.93    inference(avatar_split_clause,[],[f40,f42])).
% 20.45/2.93  fof(f42,plain,(
% 20.45/2.93    spl2_2 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 20.45/2.93    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 20.45/2.93  fof(f40,plain,(
% 20.45/2.93    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 20.45/2.93    inference(superposition,[],[f29,f18])).
% 20.45/2.93  fof(f38,plain,(
% 20.45/2.93    ~spl2_1),
% 20.45/2.93    inference(avatar_split_clause,[],[f28,f35])).
% 20.45/2.93  fof(f28,plain,(
% 20.45/2.93    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 20.45/2.93    inference(definition_unfolding,[],[f16,f21,f23])).
% 20.45/2.93  fof(f16,plain,(
% 20.45/2.93    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 20.45/2.93    inference(cnf_transformation,[],[f15])).
% 20.45/2.93  fof(f15,plain,(
% 20.45/2.93    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 20.45/2.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 20.45/2.93  fof(f14,plain,(
% 20.45/2.93    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 20.45/2.93    introduced(choice_axiom,[])).
% 20.45/2.93  fof(f13,plain,(
% 20.45/2.93    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 20.45/2.93    inference(ennf_transformation,[],[f12])).
% 20.45/2.93  fof(f12,negated_conjecture,(
% 20.45/2.93    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 20.45/2.93    inference(negated_conjecture,[],[f11])).
% 20.45/2.93  fof(f11,conjecture,(
% 20.45/2.93    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 20.45/2.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 20.45/2.93  % SZS output end Proof for theBenchmark
% 20.45/2.93  % (29433)------------------------------
% 20.45/2.93  % (29433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.45/2.93  % (29433)Termination reason: Refutation
% 20.45/2.93  
% 20.45/2.93  % (29433)Memory used [KB]: 78804
% 20.45/2.93  % (29433)Time elapsed: 2.518 s
% 20.45/2.93  % (29433)------------------------------
% 20.45/2.93  % (29433)------------------------------
% 20.45/2.94  % (29422)Success in time 2.579 s
%------------------------------------------------------------------------------
