%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:50 EST 2020

% Result     : Theorem 8.05s
% Output     : Refutation 8.05s
% Verified   : 
% Statistics : Number of formulae       :  110 (2778 expanded)
%              Number of leaves         :   12 ( 955 expanded)
%              Depth                    :   31
%              Number of atoms          :  111 (2779 expanded)
%              Number of equality atoms :  110 (2778 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24322,plain,(
    $false ),
    inference(subsumption_resolution,[],[f24321,f8229])).

fof(f8229,plain,(
    ! [X10,X9] : k2_xboole_0(X9,X10) = k2_xboole_0(k4_xboole_0(X10,X9),X9) ),
    inference(forward_demodulation,[],[f8139,f18])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f8139,plain,(
    ! [X10,X9] : k2_xboole_0(k4_xboole_0(X10,X9),X9) = k4_xboole_0(k2_xboole_0(X9,X10),k1_xboole_0) ),
    inference(superposition,[],[f8101,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f8101,plain,(
    ! [X12,X13] : k2_xboole_0(X12,X13) = k4_xboole_0(k2_xboole_0(X13,X12),k1_xboole_0) ),
    inference(forward_demodulation,[],[f8100,f7530])).

fof(f7530,plain,(
    ! [X10,X11] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X10,X11),k2_xboole_0(X11,X10)) ),
    inference(superposition,[],[f172,f7351])).

fof(f7351,plain,(
    ! [X2,X1] : k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X2,X1),X1)) = X2 ),
    inference(superposition,[],[f7301,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f7301,plain,(
    ! [X70,X69] : k2_xboole_0(X70,k4_xboole_0(k2_xboole_0(X69,X70),X69)) = X70 ),
    inference(forward_demodulation,[],[f7114,f34])).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[],[f22,f32])).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(backward_demodulation,[],[f28,f18])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f17,f25])).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f17,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f7114,plain,(
    ! [X70,X69] : k2_xboole_0(X70,k1_xboole_0) = k2_xboole_0(X70,k4_xboole_0(k2_xboole_0(X69,X70),X69)) ),
    inference(superposition,[],[f54,f122])).

fof(f122,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f57,f119])).

fof(f119,plain,(
    ! [X15] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X15)) ),
    inference(forward_demodulation,[],[f109,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f24,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f109,plain,(
    ! [X15] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X15)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X15)),k4_xboole_0(k1_xboole_0,X15)) ),
    inference(superposition,[],[f32,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f21])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f57,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f29,f18])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f21,f21])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f54,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(superposition,[],[f22,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f172,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X2,X3)))) ),
    inference(superposition,[],[f123,f26])).

fof(f123,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(backward_demodulation,[],[f92,f119])).

fof(f92,plain,(
    ! [X2,X1] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f83,f22])).

fof(f83,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) ),
    inference(superposition,[],[f57,f26])).

fof(f8100,plain,(
    ! [X12,X13] : k2_xboole_0(X12,X13) = k4_xboole_0(k2_xboole_0(X13,X12),k4_xboole_0(k2_xboole_0(X13,X12),k2_xboole_0(X12,X13))) ),
    inference(forward_demodulation,[],[f7979,f18])).

fof(f7979,plain,(
    ! [X12,X13] : k4_xboole_0(k2_xboole_0(X13,X12),k4_xboole_0(k2_xboole_0(X13,X12),k2_xboole_0(X12,X13))) = k4_xboole_0(k2_xboole_0(X12,X13),k1_xboole_0) ),
    inference(superposition,[],[f29,f7530])).

fof(f24321,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) ),
    inference(forward_demodulation,[],[f24320,f232])).

fof(f232,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f221,f20])).

fof(f221,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5 ),
    inference(forward_demodulation,[],[f199,f102])).

fof(f102,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f30,f29])).

fof(f199,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X6,X5))),X5) = X5 ),
    inference(superposition,[],[f118,f29])).

fof(f118,plain,(
    ! [X12,X11] : k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X11) = X11 ),
    inference(forward_demodulation,[],[f108,f31])).

fof(f108,plain,(
    ! [X12,X11] : k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X11) = k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),k4_xboole_0(X11,X12)) ),
    inference(superposition,[],[f22,f30])).

fof(f24320,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f24319,f20])).

fof(f24319,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) ),
    inference(forward_demodulation,[],[f24318,f22])).

fof(f24318,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f24087,f20])).

fof(f24087,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f27,f22390])).

fof(f22390,plain,(
    ! [X101,X99,X100] : k2_xboole_0(k2_xboole_0(X100,X101),X99) = k2_xboole_0(X101,k2_xboole_0(X99,X100)) ),
    inference(forward_demodulation,[],[f22364,f10893])).

fof(f10893,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(k4_xboole_0(X2,X1),X1) ),
    inference(backward_demodulation,[],[f1030,f10798])).

fof(f10798,plain,(
    ! [X2,X1] : k4_xboole_0(X2,X1) = k4_xboole_0(k2_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f10659,f20])).

fof(f10659,plain,(
    ! [X17,X18] : k4_xboole_0(X18,X17) = k4_xboole_0(k2_xboole_0(X17,X18),X17) ),
    inference(forward_demodulation,[],[f10658,f18])).

fof(f10658,plain,(
    ! [X17,X18] : k4_xboole_0(k2_xboole_0(X17,X18),X17) = k4_xboole_0(k4_xboole_0(X18,X17),k1_xboole_0) ),
    inference(forward_demodulation,[],[f10657,f375])).

fof(f375,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,k2_xboole_0(X2,X3))) ),
    inference(superposition,[],[f178,f20])).

fof(f178,plain,(
    ! [X6,X8,X7] : k1_xboole_0 = k4_xboole_0(X6,k2_xboole_0(k2_xboole_0(X7,X6),X8)) ),
    inference(forward_demodulation,[],[f174,f129])).

fof(f129,plain,(
    ! [X9] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X9) ),
    inference(forward_demodulation,[],[f125,f18])).

fof(f125,plain,(
    ! [X9] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X9) ),
    inference(backward_demodulation,[],[f105,f122])).

fof(f105,plain,(
    ! [X9] : k4_xboole_0(k1_xboole_0,X9) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X9,X9)) ),
    inference(superposition,[],[f30,f57])).

fof(f174,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k1_xboole_0,X8) = k4_xboole_0(X6,k2_xboole_0(k2_xboole_0(X7,X6),X8)) ),
    inference(superposition,[],[f26,f123])).

fof(f10657,plain,(
    ! [X17,X18] : k4_xboole_0(k2_xboole_0(X17,X18),X17) = k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(X18,k2_xboole_0(X17,k2_xboole_0(X17,X18)))) ),
    inference(forward_demodulation,[],[f10656,f22])).

fof(f10656,plain,(
    ! [X17,X18] : k4_xboole_0(k2_xboole_0(X17,X18),X17) = k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(X18,k2_xboole_0(X17,k4_xboole_0(k2_xboole_0(X17,X18),X17)))) ),
    inference(forward_demodulation,[],[f10655,f26])).

fof(f10655,plain,(
    ! [X17,X18] : k4_xboole_0(k2_xboole_0(X17,X18),X17) = k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(k2_xboole_0(X17,X18),X17))) ),
    inference(forward_demodulation,[],[f10398,f18])).

fof(f10398,plain,(
    ! [X17,X18] : k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(k2_xboole_0(X17,X18),X17))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X17,X18),X17),k1_xboole_0) ),
    inference(superposition,[],[f29,f7620])).

fof(f7620,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),X9),k4_xboole_0(X10,X9)) ),
    inference(superposition,[],[f7398,f22])).

fof(f7398,plain,(
    ! [X21,X20] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X21,X20),X21),X20) ),
    inference(superposition,[],[f123,f7301])).

fof(f1030,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X2,X1),X1),X1) ),
    inference(forward_demodulation,[],[f959,f18])).

fof(f959,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X2,X1),X1),k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f240,f123])).

fof(f240,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) = X3 ),
    inference(backward_demodulation,[],[f73,f232])).

fof(f73,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) = k2_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f64,f20])).

fof(f64,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) ),
    inference(superposition,[],[f22,f29])).

fof(f22364,plain,(
    ! [X101,X99,X100] : k2_xboole_0(k2_xboole_0(X100,X101),X99) = k2_xboole_0(k4_xboole_0(X101,k2_xboole_0(X99,X100)),k2_xboole_0(X99,X100)) ),
    inference(backward_demodulation,[],[f20333,f22178])).

fof(f22178,plain,(
    ! [X161,X159,X160] : k4_xboole_0(X161,k2_xboole_0(X159,X160)) = k4_xboole_0(k2_xboole_0(X160,X161),k2_xboole_0(X159,X160)) ),
    inference(superposition,[],[f17466,f11393])).

fof(f11393,plain,(
    ! [X144,X143] : k4_xboole_0(k2_xboole_0(X143,X144),k4_xboole_0(X143,X144)) = X144 ),
    inference(forward_demodulation,[],[f11316,f10989])).

fof(f10989,plain,(
    ! [X81,X82] : k4_xboole_0(X82,k4_xboole_0(X81,X82)) = X82 ),
    inference(forward_demodulation,[],[f10988,f18])).

fof(f10988,plain,(
    ! [X81,X82] : k4_xboole_0(X82,k1_xboole_0) = k4_xboole_0(X82,k4_xboole_0(X81,X82)) ),
    inference(forward_demodulation,[],[f10987,f10798])).

fof(f10987,plain,(
    ! [X81,X82] : k4_xboole_0(X82,k1_xboole_0) = k4_xboole_0(X82,k4_xboole_0(k2_xboole_0(X81,X82),X82)) ),
    inference(forward_demodulation,[],[f10986,f123])).

fof(f10986,plain,(
    ! [X81,X82] : k4_xboole_0(X82,k4_xboole_0(k2_xboole_0(X81,X82),X82)) = k4_xboole_0(X82,k4_xboole_0(X82,k2_xboole_0(X81,X82))) ),
    inference(forward_demodulation,[],[f10823,f29])).

fof(f10823,plain,(
    ! [X81,X82] : k4_xboole_0(X82,k4_xboole_0(k2_xboole_0(X81,X82),X82)) = k4_xboole_0(k2_xboole_0(X81,X82),k4_xboole_0(k2_xboole_0(X81,X82),X82)) ),
    inference(superposition,[],[f10659,f1030])).

fof(f11316,plain,(
    ! [X144,X143] : k4_xboole_0(X144,k4_xboole_0(X143,X144)) = k4_xboole_0(k2_xboole_0(X143,X144),k4_xboole_0(X143,X144)) ),
    inference(superposition,[],[f10659,f10893])).

fof(f17466,plain,(
    ! [X24,X23,X22] : k4_xboole_0(X24,X22) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X22,X23),X24),X22) ),
    inference(forward_demodulation,[],[f17465,f232])).

fof(f17465,plain,(
    ! [X24,X23,X22] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X22,X23),X24),X22) = k4_xboole_0(X24,k2_xboole_0(X22,k4_xboole_0(X22,X23))) ),
    inference(forward_demodulation,[],[f17464,f20])).

fof(f17464,plain,(
    ! [X24,X23,X22] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X22,X23),X24),X22) = k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X22,X23),X22)) ),
    inference(forward_demodulation,[],[f17351,f26])).

fof(f17351,plain,(
    ! [X24,X23,X22] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X22,X23),X24),X22) = k4_xboole_0(k4_xboole_0(X24,k4_xboole_0(X22,X23)),X22) ),
    inference(superposition,[],[f10950,f10659])).

fof(f10950,plain,(
    ! [X17,X18,X16] : k4_xboole_0(X17,X16) = k4_xboole_0(k4_xboole_0(X17,k4_xboole_0(X16,X18)),X16) ),
    inference(forward_demodulation,[],[f10803,f10659])).

fof(f10803,plain,(
    ! [X17,X18,X16] : k4_xboole_0(k2_xboole_0(X16,X17),X16) = k4_xboole_0(k4_xboole_0(X17,k4_xboole_0(X16,X18)),X16) ),
    inference(superposition,[],[f10659,f7246])).

fof(f7246,plain,(
    ! [X61,X62,X63] : k2_xboole_0(X61,X63) = k2_xboole_0(X61,k4_xboole_0(X63,k4_xboole_0(X61,X62))) ),
    inference(forward_demodulation,[],[f7079,f22])).

fof(f7079,plain,(
    ! [X61,X62,X63] : k2_xboole_0(X61,k4_xboole_0(X63,k4_xboole_0(X61,X62))) = k2_xboole_0(X61,k4_xboole_0(X63,X61)) ),
    inference(superposition,[],[f54,f221])).

fof(f20333,plain,(
    ! [X101,X99,X100] : k2_xboole_0(k2_xboole_0(X100,X101),X99) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X100,X101),k2_xboole_0(X99,X100)),k2_xboole_0(X99,X100)) ),
    inference(forward_demodulation,[],[f20332,f11709])).

fof(f11709,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X6,k2_xboole_0(X7,X8)) = k4_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f11619,f26])).

fof(f11619,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k4_xboole_0(X6,X7),X8) = k4_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X7,X8)) ),
    inference(superposition,[],[f26,f10798])).

fof(f20332,plain,(
    ! [X101,X99,X100] : k2_xboole_0(k2_xboole_0(X100,X101),X99) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(X100,X101),X99),k2_xboole_0(X99,X100)),k2_xboole_0(X99,X100)) ),
    inference(forward_demodulation,[],[f20231,f18])).

fof(f20231,plain,(
    ! [X101,X99,X100] : k2_xboole_0(k2_xboole_0(X100,X101),X99) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(X100,X101),X99),k2_xboole_0(X99,X100)),k4_xboole_0(k2_xboole_0(X99,X100),k1_xboole_0)) ),
    inference(superposition,[],[f240,f15199])).

fof(f15199,plain,(
    ! [X10,X8,X9] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(k2_xboole_0(X9,X10),X8)) ),
    inference(superposition,[],[f9635,f20])).

fof(f9635,plain,(
    ! [X14,X12,X13] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X12,k2_xboole_0(X13,X14))) ),
    inference(superposition,[],[f7400,f26])).

fof(f7400,plain,(
    ! [X26,X24,X25] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X25,X24),X25),k2_xboole_0(X24,X26)) ),
    inference(superposition,[],[f178,f7301])).

fof(f27,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f16,f25,f21])).

fof(f16,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (9194)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.50  % (9188)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.50  % (9183)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.50  % (9185)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (9191)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (9184)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (9189)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.50  % (9186)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.50  % (9196)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.51  % (9192)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.51  % (9193)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.51  % (9197)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.52  % (9192)Refutation not found, incomplete strategy% (9192)------------------------------
% 0.20/0.52  % (9192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (9192)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (9192)Memory used [KB]: 10618
% 0.20/0.52  % (9192)Time elapsed: 0.077 s
% 0.20/0.52  % (9192)------------------------------
% 0.20/0.52  % (9192)------------------------------
% 0.20/0.55  % (9190)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.55  % (9181)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.55  % (9187)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.56  % (9198)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.56  % (9182)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.56  % (9195)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 4.84/1.04  % (9185)Time limit reached!
% 4.84/1.04  % (9185)------------------------------
% 4.84/1.04  % (9185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.84/1.04  % (9185)Termination reason: Time limit
% 4.84/1.04  
% 4.84/1.04  % (9185)Memory used [KB]: 16630
% 4.84/1.04  % (9185)Time elapsed: 0.606 s
% 4.84/1.04  % (9185)------------------------------
% 4.84/1.04  % (9185)------------------------------
% 8.05/1.44  % (9195)Refutation found. Thanks to Tanya!
% 8.05/1.44  % SZS status Theorem for theBenchmark
% 8.05/1.44  % SZS output start Proof for theBenchmark
% 8.05/1.44  fof(f24322,plain,(
% 8.05/1.44    $false),
% 8.05/1.44    inference(subsumption_resolution,[],[f24321,f8229])).
% 8.05/1.44  fof(f8229,plain,(
% 8.05/1.44    ( ! [X10,X9] : (k2_xboole_0(X9,X10) = k2_xboole_0(k4_xboole_0(X10,X9),X9)) )),
% 8.05/1.44    inference(forward_demodulation,[],[f8139,f18])).
% 8.05/1.44  fof(f18,plain,(
% 8.05/1.44    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.05/1.44    inference(cnf_transformation,[],[f5])).
% 8.05/1.44  fof(f5,axiom,(
% 8.05/1.44    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 8.05/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 8.05/1.44  fof(f8139,plain,(
% 8.05/1.44    ( ! [X10,X9] : (k2_xboole_0(k4_xboole_0(X10,X9),X9) = k4_xboole_0(k2_xboole_0(X9,X10),k1_xboole_0)) )),
% 8.05/1.44    inference(superposition,[],[f8101,f22])).
% 8.05/1.44  fof(f22,plain,(
% 8.05/1.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 8.05/1.44    inference(cnf_transformation,[],[f4])).
% 8.05/1.44  fof(f4,axiom,(
% 8.05/1.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 8.05/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 8.05/1.44  fof(f8101,plain,(
% 8.05/1.44    ( ! [X12,X13] : (k2_xboole_0(X12,X13) = k4_xboole_0(k2_xboole_0(X13,X12),k1_xboole_0)) )),
% 8.05/1.44    inference(forward_demodulation,[],[f8100,f7530])).
% 8.05/1.44  fof(f7530,plain,(
% 8.05/1.44    ( ! [X10,X11] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X10,X11),k2_xboole_0(X11,X10))) )),
% 8.05/1.44    inference(superposition,[],[f172,f7351])).
% 8.05/1.44  fof(f7351,plain,(
% 8.05/1.44    ( ! [X2,X1] : (k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X2,X1),X1)) = X2) )),
% 8.05/1.44    inference(superposition,[],[f7301,f20])).
% 8.05/1.44  fof(f20,plain,(
% 8.05/1.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 8.05/1.44    inference(cnf_transformation,[],[f1])).
% 8.05/1.44  fof(f1,axiom,(
% 8.05/1.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 8.05/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 8.05/1.44  fof(f7301,plain,(
% 8.05/1.44    ( ! [X70,X69] : (k2_xboole_0(X70,k4_xboole_0(k2_xboole_0(X69,X70),X69)) = X70) )),
% 8.05/1.44    inference(forward_demodulation,[],[f7114,f34])).
% 8.05/1.44  fof(f34,plain,(
% 8.05/1.44    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.05/1.44    inference(superposition,[],[f22,f32])).
% 8.05/1.44  fof(f32,plain,(
% 8.05/1.44    ( ! [X0] : (k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 8.05/1.44    inference(backward_demodulation,[],[f28,f18])).
% 8.05/1.44  fof(f28,plain,(
% 8.05/1.44    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 8.05/1.44    inference(definition_unfolding,[],[f17,f25])).
% 8.05/1.44  fof(f25,plain,(
% 8.05/1.44    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 8.05/1.44    inference(cnf_transformation,[],[f3])).
% 8.05/1.44  fof(f3,axiom,(
% 8.05/1.44    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 8.05/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 8.05/1.44  fof(f17,plain,(
% 8.05/1.44    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.05/1.44    inference(cnf_transformation,[],[f10])).
% 8.05/1.44  fof(f10,axiom,(
% 8.05/1.44    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 8.05/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 8.05/1.44  fof(f7114,plain,(
% 8.05/1.44    ( ! [X70,X69] : (k2_xboole_0(X70,k1_xboole_0) = k2_xboole_0(X70,k4_xboole_0(k2_xboole_0(X69,X70),X69))) )),
% 8.05/1.44    inference(superposition,[],[f54,f122])).
% 8.05/1.44  fof(f122,plain,(
% 8.05/1.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 8.05/1.44    inference(backward_demodulation,[],[f57,f119])).
% 8.05/1.44  fof(f119,plain,(
% 8.05/1.44    ( ! [X15] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X15))) )),
% 8.05/1.44    inference(forward_demodulation,[],[f109,f31])).
% 8.05/1.44  fof(f31,plain,(
% 8.05/1.44    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 8.05/1.44    inference(definition_unfolding,[],[f24,f21])).
% 8.05/1.44  fof(f21,plain,(
% 8.05/1.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 8.05/1.44    inference(cnf_transformation,[],[f8])).
% 8.05/1.44  fof(f8,axiom,(
% 8.05/1.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 8.05/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 8.05/1.44  fof(f24,plain,(
% 8.05/1.44    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 8.05/1.44    inference(cnf_transformation,[],[f9])).
% 8.05/1.44  fof(f9,axiom,(
% 8.05/1.44    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 8.05/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 8.05/1.44  fof(f109,plain,(
% 8.05/1.44    ( ! [X15] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X15)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X15)),k4_xboole_0(k1_xboole_0,X15))) )),
% 8.05/1.44    inference(superposition,[],[f32,f30])).
% 8.05/1.44  fof(f30,plain,(
% 8.05/1.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 8.05/1.44    inference(definition_unfolding,[],[f23,f21])).
% 8.05/1.44  fof(f23,plain,(
% 8.05/1.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.05/1.44    inference(cnf_transformation,[],[f7])).
% 8.05/1.44  fof(f7,axiom,(
% 8.05/1.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 8.05/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 8.05/1.44  fof(f57,plain,(
% 8.05/1.44    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0)) )),
% 8.05/1.44    inference(superposition,[],[f29,f18])).
% 8.05/1.44  fof(f29,plain,(
% 8.05/1.44    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 8.05/1.44    inference(definition_unfolding,[],[f19,f21,f21])).
% 8.05/1.44  fof(f19,plain,(
% 8.05/1.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 8.05/1.44    inference(cnf_transformation,[],[f2])).
% 8.05/1.44  fof(f2,axiom,(
% 8.05/1.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 8.05/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 8.05/1.44  fof(f54,plain,(
% 8.05/1.44    ( ! [X4,X2,X3] : (k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4)))) )),
% 8.05/1.44    inference(superposition,[],[f22,f26])).
% 8.05/1.44  fof(f26,plain,(
% 8.05/1.44    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 8.05/1.44    inference(cnf_transformation,[],[f6])).
% 8.05/1.44  fof(f6,axiom,(
% 8.05/1.44    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 8.05/1.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 8.05/1.44  fof(f172,plain,(
% 8.05/1.44    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X2,X3))))) )),
% 8.05/1.44    inference(superposition,[],[f123,f26])).
% 8.05/1.44  fof(f123,plain,(
% 8.05/1.44    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 8.05/1.44    inference(backward_demodulation,[],[f92,f119])).
% 8.05/1.44  fof(f92,plain,(
% 8.05/1.44    ( ! [X2,X1] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 8.05/1.44    inference(forward_demodulation,[],[f83,f22])).
% 8.05/1.44  fof(f83,plain,(
% 8.05/1.44    ( ! [X2,X1] : (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)))) )),
% 8.05/1.44    inference(superposition,[],[f57,f26])).
% 8.05/1.44  fof(f8100,plain,(
% 8.05/1.44    ( ! [X12,X13] : (k2_xboole_0(X12,X13) = k4_xboole_0(k2_xboole_0(X13,X12),k4_xboole_0(k2_xboole_0(X13,X12),k2_xboole_0(X12,X13)))) )),
% 8.05/1.44    inference(forward_demodulation,[],[f7979,f18])).
% 8.05/1.44  fof(f7979,plain,(
% 8.05/1.44    ( ! [X12,X13] : (k4_xboole_0(k2_xboole_0(X13,X12),k4_xboole_0(k2_xboole_0(X13,X12),k2_xboole_0(X12,X13))) = k4_xboole_0(k2_xboole_0(X12,X13),k1_xboole_0)) )),
% 8.05/1.44    inference(superposition,[],[f29,f7530])).
% 8.05/1.44  fof(f24321,plain,(
% 8.05/1.44    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)),
% 8.05/1.44    inference(forward_demodulation,[],[f24320,f232])).
% 8.05/1.45  fof(f232,plain,(
% 8.05/1.45    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 8.05/1.45    inference(superposition,[],[f221,f20])).
% 8.05/1.45  fof(f221,plain,(
% 8.05/1.45    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5) )),
% 8.05/1.45    inference(forward_demodulation,[],[f199,f102])).
% 8.05/1.45  fof(f102,plain,(
% 8.05/1.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 8.05/1.45    inference(superposition,[],[f30,f29])).
% 8.05/1.45  fof(f199,plain,(
% 8.05/1.45    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X6,X5))),X5) = X5) )),
% 8.05/1.45    inference(superposition,[],[f118,f29])).
% 8.05/1.45  fof(f118,plain,(
% 8.05/1.45    ( ! [X12,X11] : (k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X11) = X11) )),
% 8.05/1.45    inference(forward_demodulation,[],[f108,f31])).
% 8.05/1.45  fof(f108,plain,(
% 8.05/1.45    ( ! [X12,X11] : (k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X11) = k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),k4_xboole_0(X11,X12))) )),
% 8.05/1.45    inference(superposition,[],[f22,f30])).
% 8.05/1.45  fof(f24320,plain,(
% 8.05/1.45    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 8.05/1.45    inference(forward_demodulation,[],[f24319,f20])).
% 8.05/1.45  fof(f24319,plain,(
% 8.05/1.45    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0))),
% 8.05/1.45    inference(forward_demodulation,[],[f24318,f22])).
% 8.05/1.45  fof(f24318,plain,(
% 8.05/1.45    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 8.05/1.45    inference(forward_demodulation,[],[f24087,f20])).
% 8.05/1.45  fof(f24087,plain,(
% 8.05/1.45    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)))),
% 8.05/1.45    inference(superposition,[],[f27,f22390])).
% 8.05/1.45  fof(f22390,plain,(
% 8.05/1.45    ( ! [X101,X99,X100] : (k2_xboole_0(k2_xboole_0(X100,X101),X99) = k2_xboole_0(X101,k2_xboole_0(X99,X100))) )),
% 8.05/1.45    inference(forward_demodulation,[],[f22364,f10893])).
% 8.05/1.45  fof(f10893,plain,(
% 8.05/1.45    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(k4_xboole_0(X2,X1),X1)) )),
% 8.05/1.45    inference(backward_demodulation,[],[f1030,f10798])).
% 8.05/1.45  fof(f10798,plain,(
% 8.05/1.45    ( ! [X2,X1] : (k4_xboole_0(X2,X1) = k4_xboole_0(k2_xboole_0(X2,X1),X1)) )),
% 8.05/1.45    inference(superposition,[],[f10659,f20])).
% 8.05/1.45  fof(f10659,plain,(
% 8.05/1.45    ( ! [X17,X18] : (k4_xboole_0(X18,X17) = k4_xboole_0(k2_xboole_0(X17,X18),X17)) )),
% 8.05/1.45    inference(forward_demodulation,[],[f10658,f18])).
% 8.05/1.45  fof(f10658,plain,(
% 8.05/1.45    ( ! [X17,X18] : (k4_xboole_0(k2_xboole_0(X17,X18),X17) = k4_xboole_0(k4_xboole_0(X18,X17),k1_xboole_0)) )),
% 8.05/1.45    inference(forward_demodulation,[],[f10657,f375])).
% 8.05/1.45  fof(f375,plain,(
% 8.05/1.45    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,k2_xboole_0(X2,X3)))) )),
% 8.05/1.45    inference(superposition,[],[f178,f20])).
% 8.05/1.45  fof(f178,plain,(
% 8.05/1.45    ( ! [X6,X8,X7] : (k1_xboole_0 = k4_xboole_0(X6,k2_xboole_0(k2_xboole_0(X7,X6),X8))) )),
% 8.05/1.45    inference(forward_demodulation,[],[f174,f129])).
% 8.05/1.45  fof(f129,plain,(
% 8.05/1.45    ( ! [X9] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X9)) )),
% 8.05/1.45    inference(forward_demodulation,[],[f125,f18])).
% 8.05/1.45  fof(f125,plain,(
% 8.05/1.45    ( ! [X9] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X9)) )),
% 8.05/1.45    inference(backward_demodulation,[],[f105,f122])).
% 8.05/1.45  fof(f105,plain,(
% 8.05/1.45    ( ! [X9] : (k4_xboole_0(k1_xboole_0,X9) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X9,X9))) )),
% 8.05/1.45    inference(superposition,[],[f30,f57])).
% 8.05/1.45  fof(f174,plain,(
% 8.05/1.45    ( ! [X6,X8,X7] : (k4_xboole_0(k1_xboole_0,X8) = k4_xboole_0(X6,k2_xboole_0(k2_xboole_0(X7,X6),X8))) )),
% 8.05/1.45    inference(superposition,[],[f26,f123])).
% 8.05/1.45  fof(f10657,plain,(
% 8.05/1.45    ( ! [X17,X18] : (k4_xboole_0(k2_xboole_0(X17,X18),X17) = k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(X18,k2_xboole_0(X17,k2_xboole_0(X17,X18))))) )),
% 8.05/1.45    inference(forward_demodulation,[],[f10656,f22])).
% 8.05/1.45  fof(f10656,plain,(
% 8.05/1.45    ( ! [X17,X18] : (k4_xboole_0(k2_xboole_0(X17,X18),X17) = k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(X18,k2_xboole_0(X17,k4_xboole_0(k2_xboole_0(X17,X18),X17))))) )),
% 8.05/1.45    inference(forward_demodulation,[],[f10655,f26])).
% 8.05/1.45  fof(f10655,plain,(
% 8.05/1.45    ( ! [X17,X18] : (k4_xboole_0(k2_xboole_0(X17,X18),X17) = k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(k2_xboole_0(X17,X18),X17)))) )),
% 8.05/1.45    inference(forward_demodulation,[],[f10398,f18])).
% 8.05/1.45  fof(f10398,plain,(
% 8.05/1.45    ( ! [X17,X18] : (k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(k2_xboole_0(X17,X18),X17))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X17,X18),X17),k1_xboole_0)) )),
% 8.05/1.45    inference(superposition,[],[f29,f7620])).
% 8.05/1.45  fof(f7620,plain,(
% 8.05/1.45    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),X9),k4_xboole_0(X10,X9))) )),
% 8.05/1.45    inference(superposition,[],[f7398,f22])).
% 8.05/1.45  fof(f7398,plain,(
% 8.05/1.45    ( ! [X21,X20] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X21,X20),X21),X20)) )),
% 8.05/1.45    inference(superposition,[],[f123,f7301])).
% 8.05/1.45  fof(f1030,plain,(
% 8.05/1.45    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X2,X1),X1),X1)) )),
% 8.05/1.45    inference(forward_demodulation,[],[f959,f18])).
% 8.05/1.45  fof(f959,plain,(
% 8.05/1.45    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X2,X1),X1),k4_xboole_0(X1,k1_xboole_0))) )),
% 8.05/1.45    inference(superposition,[],[f240,f123])).
% 8.05/1.45  fof(f240,plain,(
% 8.05/1.45    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) = X3) )),
% 8.05/1.45    inference(backward_demodulation,[],[f73,f232])).
% 8.05/1.45  fof(f73,plain,(
% 8.05/1.45    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) = k2_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 8.05/1.45    inference(forward_demodulation,[],[f64,f20])).
% 8.05/1.45  fof(f64,plain,(
% 8.05/1.45    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3)))) )),
% 8.05/1.45    inference(superposition,[],[f22,f29])).
% 8.05/1.45  fof(f22364,plain,(
% 8.05/1.45    ( ! [X101,X99,X100] : (k2_xboole_0(k2_xboole_0(X100,X101),X99) = k2_xboole_0(k4_xboole_0(X101,k2_xboole_0(X99,X100)),k2_xboole_0(X99,X100))) )),
% 8.05/1.45    inference(backward_demodulation,[],[f20333,f22178])).
% 8.05/1.45  fof(f22178,plain,(
% 8.05/1.45    ( ! [X161,X159,X160] : (k4_xboole_0(X161,k2_xboole_0(X159,X160)) = k4_xboole_0(k2_xboole_0(X160,X161),k2_xboole_0(X159,X160))) )),
% 8.05/1.45    inference(superposition,[],[f17466,f11393])).
% 8.05/1.45  fof(f11393,plain,(
% 8.05/1.45    ( ! [X144,X143] : (k4_xboole_0(k2_xboole_0(X143,X144),k4_xboole_0(X143,X144)) = X144) )),
% 8.05/1.45    inference(forward_demodulation,[],[f11316,f10989])).
% 8.05/1.45  fof(f10989,plain,(
% 8.05/1.45    ( ! [X81,X82] : (k4_xboole_0(X82,k4_xboole_0(X81,X82)) = X82) )),
% 8.05/1.45    inference(forward_demodulation,[],[f10988,f18])).
% 8.05/1.45  fof(f10988,plain,(
% 8.05/1.45    ( ! [X81,X82] : (k4_xboole_0(X82,k1_xboole_0) = k4_xboole_0(X82,k4_xboole_0(X81,X82))) )),
% 8.05/1.45    inference(forward_demodulation,[],[f10987,f10798])).
% 8.05/1.45  fof(f10987,plain,(
% 8.05/1.45    ( ! [X81,X82] : (k4_xboole_0(X82,k1_xboole_0) = k4_xboole_0(X82,k4_xboole_0(k2_xboole_0(X81,X82),X82))) )),
% 8.05/1.45    inference(forward_demodulation,[],[f10986,f123])).
% 8.05/1.45  fof(f10986,plain,(
% 8.05/1.45    ( ! [X81,X82] : (k4_xboole_0(X82,k4_xboole_0(k2_xboole_0(X81,X82),X82)) = k4_xboole_0(X82,k4_xboole_0(X82,k2_xboole_0(X81,X82)))) )),
% 8.05/1.45    inference(forward_demodulation,[],[f10823,f29])).
% 8.05/1.45  fof(f10823,plain,(
% 8.05/1.45    ( ! [X81,X82] : (k4_xboole_0(X82,k4_xboole_0(k2_xboole_0(X81,X82),X82)) = k4_xboole_0(k2_xboole_0(X81,X82),k4_xboole_0(k2_xboole_0(X81,X82),X82))) )),
% 8.05/1.45    inference(superposition,[],[f10659,f1030])).
% 8.05/1.45  fof(f11316,plain,(
% 8.05/1.45    ( ! [X144,X143] : (k4_xboole_0(X144,k4_xboole_0(X143,X144)) = k4_xboole_0(k2_xboole_0(X143,X144),k4_xboole_0(X143,X144))) )),
% 8.05/1.45    inference(superposition,[],[f10659,f10893])).
% 8.05/1.45  fof(f17466,plain,(
% 8.05/1.45    ( ! [X24,X23,X22] : (k4_xboole_0(X24,X22) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X22,X23),X24),X22)) )),
% 8.05/1.45    inference(forward_demodulation,[],[f17465,f232])).
% 8.05/1.45  fof(f17465,plain,(
% 8.05/1.45    ( ! [X24,X23,X22] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X22,X23),X24),X22) = k4_xboole_0(X24,k2_xboole_0(X22,k4_xboole_0(X22,X23)))) )),
% 8.05/1.45    inference(forward_demodulation,[],[f17464,f20])).
% 8.05/1.45  fof(f17464,plain,(
% 8.05/1.45    ( ! [X24,X23,X22] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X22,X23),X24),X22) = k4_xboole_0(X24,k2_xboole_0(k4_xboole_0(X22,X23),X22))) )),
% 8.05/1.45    inference(forward_demodulation,[],[f17351,f26])).
% 8.05/1.45  fof(f17351,plain,(
% 8.05/1.45    ( ! [X24,X23,X22] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X22,X23),X24),X22) = k4_xboole_0(k4_xboole_0(X24,k4_xboole_0(X22,X23)),X22)) )),
% 8.05/1.45    inference(superposition,[],[f10950,f10659])).
% 8.05/1.45  fof(f10950,plain,(
% 8.05/1.45    ( ! [X17,X18,X16] : (k4_xboole_0(X17,X16) = k4_xboole_0(k4_xboole_0(X17,k4_xboole_0(X16,X18)),X16)) )),
% 8.05/1.45    inference(forward_demodulation,[],[f10803,f10659])).
% 8.05/1.45  fof(f10803,plain,(
% 8.05/1.45    ( ! [X17,X18,X16] : (k4_xboole_0(k2_xboole_0(X16,X17),X16) = k4_xboole_0(k4_xboole_0(X17,k4_xboole_0(X16,X18)),X16)) )),
% 8.05/1.45    inference(superposition,[],[f10659,f7246])).
% 8.05/1.45  fof(f7246,plain,(
% 8.05/1.45    ( ! [X61,X62,X63] : (k2_xboole_0(X61,X63) = k2_xboole_0(X61,k4_xboole_0(X63,k4_xboole_0(X61,X62)))) )),
% 8.05/1.45    inference(forward_demodulation,[],[f7079,f22])).
% 8.05/1.45  fof(f7079,plain,(
% 8.05/1.45    ( ! [X61,X62,X63] : (k2_xboole_0(X61,k4_xboole_0(X63,k4_xboole_0(X61,X62))) = k2_xboole_0(X61,k4_xboole_0(X63,X61))) )),
% 8.05/1.45    inference(superposition,[],[f54,f221])).
% 8.05/1.45  fof(f20333,plain,(
% 8.05/1.45    ( ! [X101,X99,X100] : (k2_xboole_0(k2_xboole_0(X100,X101),X99) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X100,X101),k2_xboole_0(X99,X100)),k2_xboole_0(X99,X100))) )),
% 8.05/1.45    inference(forward_demodulation,[],[f20332,f11709])).
% 8.05/1.45  fof(f11709,plain,(
% 8.05/1.45    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k2_xboole_0(X7,X8)) = k4_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X7,X8))) )),
% 8.05/1.45    inference(forward_demodulation,[],[f11619,f26])).
% 8.05/1.45  fof(f11619,plain,(
% 8.05/1.45    ( ! [X6,X8,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),X8) = k4_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X7,X8))) )),
% 8.05/1.45    inference(superposition,[],[f26,f10798])).
% 8.05/1.45  fof(f20332,plain,(
% 8.05/1.45    ( ! [X101,X99,X100] : (k2_xboole_0(k2_xboole_0(X100,X101),X99) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(X100,X101),X99),k2_xboole_0(X99,X100)),k2_xboole_0(X99,X100))) )),
% 8.05/1.45    inference(forward_demodulation,[],[f20231,f18])).
% 8.05/1.45  fof(f20231,plain,(
% 8.05/1.45    ( ! [X101,X99,X100] : (k2_xboole_0(k2_xboole_0(X100,X101),X99) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(X100,X101),X99),k2_xboole_0(X99,X100)),k4_xboole_0(k2_xboole_0(X99,X100),k1_xboole_0))) )),
% 8.05/1.45    inference(superposition,[],[f240,f15199])).
% 8.05/1.45  fof(f15199,plain,(
% 8.05/1.45    ( ! [X10,X8,X9] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(k2_xboole_0(X9,X10),X8))) )),
% 8.05/1.45    inference(superposition,[],[f9635,f20])).
% 8.05/1.45  fof(f9635,plain,(
% 8.05/1.45    ( ! [X14,X12,X13] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X12,k2_xboole_0(X13,X14)))) )),
% 8.05/1.45    inference(superposition,[],[f7400,f26])).
% 8.05/1.45  fof(f7400,plain,(
% 8.05/1.45    ( ! [X26,X24,X25] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X25,X24),X25),k2_xboole_0(X24,X26))) )),
% 8.05/1.45    inference(superposition,[],[f178,f7301])).
% 8.05/1.45  fof(f27,plain,(
% 8.05/1.45    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 8.05/1.45    inference(definition_unfolding,[],[f16,f25,f21])).
% 8.05/1.45  fof(f16,plain,(
% 8.05/1.45    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 8.05/1.45    inference(cnf_transformation,[],[f15])).
% 8.05/1.45  fof(f15,plain,(
% 8.05/1.45    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 8.05/1.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 8.05/1.45  fof(f14,plain,(
% 8.05/1.45    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 8.05/1.45    introduced(choice_axiom,[])).
% 8.05/1.45  fof(f13,plain,(
% 8.05/1.45    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 8.05/1.45    inference(ennf_transformation,[],[f12])).
% 8.05/1.45  fof(f12,negated_conjecture,(
% 8.05/1.45    ~! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 8.05/1.45    inference(negated_conjecture,[],[f11])).
% 8.05/1.45  fof(f11,conjecture,(
% 8.05/1.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 8.05/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 8.05/1.45  % SZS output end Proof for theBenchmark
% 8.05/1.45  % (9195)------------------------------
% 8.05/1.45  % (9195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.05/1.45  % (9195)Termination reason: Refutation
% 8.05/1.45  
% 8.05/1.45  % (9195)Memory used [KB]: 19189
% 8.05/1.45  % (9195)Time elapsed: 1.023 s
% 8.05/1.45  % (9195)------------------------------
% 8.05/1.45  % (9195)------------------------------
% 8.05/1.45  % (9180)Success in time 1.088 s
%------------------------------------------------------------------------------
