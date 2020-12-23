%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:50 EST 2020

% Result     : Theorem 5.32s
% Output     : Refutation 5.32s
% Verified   : 
% Statistics : Number of formulae       :   89 (4951 expanded)
%              Number of leaves         :   10 (1707 expanded)
%              Depth                    :   37
%              Number of atoms          :   90 (4952 expanded)
%              Number of equality atoms :   89 (4951 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19959,plain,(
    $false ),
    inference(subsumption_resolution,[],[f19958,f544])).

fof(f544,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(X9,X8),X8) ),
    inference(forward_demodulation,[],[f514,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f21,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f514,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X8,X9),X8),X8) ),
    inference(superposition,[],[f29,f227])).

fof(f227,plain,(
    ! [X8,X9] : k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X9,X8)) = X8 ),
    inference(forward_demodulation,[],[f226,f17])).

fof(f17,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f226,plain,(
    ! [X8,X9] : k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X9,X8)) = k4_xboole_0(X8,k1_xboole_0) ),
    inference(backward_demodulation,[],[f70,f225])).

fof(f225,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f206,f204])).

fof(f204,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f189,f138])).

fof(f138,plain,(
    ! [X7] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,X7),k4_xboole_0(k1_xboole_0,X7)) ),
    inference(superposition,[],[f29,f91])).

fof(f91,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f68,f44])).

fof(f44,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f21,f38])).

fof(f38,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f36,f19])).

fof(f36,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f34,f17])).

fof(f34,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f21,f17])).

fof(f68,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f28,f17])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f18,f20,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f189,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f177,f91])).

fof(f177,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f167,f91])).

fof(f167,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X0) = X0 ),
    inference(superposition,[],[f141,f68])).

fof(f141,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
    inference(superposition,[],[f29,f17])).

fof(f206,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(backward_demodulation,[],[f55,f204])).

fof(f55,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),X3) ),
    inference(superposition,[],[f24,f44])).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f70,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X8,X9))) = k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X9,X8)) ),
    inference(superposition,[],[f28,f32])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f19958,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) ),
    inference(forward_demodulation,[],[f19957,f453])).

fof(f453,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f411,f19])).

fof(f411,plain,(
    ! [X19,X20] : k2_xboole_0(k4_xboole_0(X19,X20),X19) = X19 ),
    inference(forward_demodulation,[],[f390,f36])).

fof(f390,plain,(
    ! [X19,X20] : k2_xboole_0(k4_xboole_0(X19,X20),X19) = k2_xboole_0(X19,k1_xboole_0) ),
    inference(superposition,[],[f237,f292])).

fof(f292,plain,(
    ! [X6,X7] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X6,X7),X6) ),
    inference(superposition,[],[f234,f29])).

fof(f234,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f217,f228])).

fof(f228,plain,(
    ! [X10,X9] : k2_xboole_0(X9,X10) = k2_xboole_0(X9,k4_xboole_0(X10,X9)) ),
    inference(backward_demodulation,[],[f147,f227])).

fof(f147,plain,(
    ! [X10,X9] : k2_xboole_0(X9,X10) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(X10,X9)),k4_xboole_0(X10,X9)) ),
    inference(superposition,[],[f29,f32])).

fof(f217,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(backward_demodulation,[],[f61,f204])).

fof(f61,plain,(
    ! [X6,X5] : k4_xboole_0(k1_xboole_0,k4_xboole_0(X5,X6)) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f24,f44])).

fof(f237,plain,(
    ! [X8,X7] : k2_xboole_0(X7,X8) = k2_xboole_0(X8,k4_xboole_0(X7,X8)) ),
    inference(backward_demodulation,[],[f146,f236])).

fof(f236,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = X7 ),
    inference(forward_demodulation,[],[f235,f17])).

fof(f235,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = k4_xboole_0(X7,k1_xboole_0) ),
    inference(backward_demodulation,[],[f69,f234])).

fof(f69,plain,(
    ! [X6,X7] : k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(X6,X7))) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f28,f21])).

fof(f146,plain,(
    ! [X8,X7] : k2_xboole_0(X7,X8) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X7,X8)),k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f29,f21])).

fof(f19957,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f19956,f19])).

fof(f19956,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) ),
    inference(forward_demodulation,[],[f19763,f228])).

fof(f19763,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f27,f16017])).

fof(f16017,plain,(
    ! [X59,X60,X58] : k2_xboole_0(X60,k2_xboole_0(X58,X59)) = k2_xboole_0(k2_xboole_0(X58,X60),X59) ),
    inference(forward_demodulation,[],[f16016,f237])).

fof(f16016,plain,(
    ! [X59,X60,X58] : k2_xboole_0(k2_xboole_0(X58,X59),k4_xboole_0(X60,k2_xboole_0(X58,X59))) = k2_xboole_0(k2_xboole_0(X58,X60),X59) ),
    inference(forward_demodulation,[],[f16015,f17])).

fof(f16015,plain,(
    ! [X59,X60,X58] : k2_xboole_0(k2_xboole_0(X58,X60),X59) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X58,X59),k1_xboole_0),k4_xboole_0(X60,k2_xboole_0(X58,X59))) ),
    inference(forward_demodulation,[],[f16014,f65])).

fof(f65,plain,(
    ! [X8,X7,X9] : k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,X9)) = k4_xboole_0(X8,k2_xboole_0(X7,X9)) ),
    inference(forward_demodulation,[],[f57,f24])).

fof(f57,plain,(
    ! [X8,X7,X9] : k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,X9)) = k4_xboole_0(k4_xboole_0(X8,X7),X9) ),
    inference(superposition,[],[f24,f32])).

fof(f16014,plain,(
    ! [X59,X60,X58] : k2_xboole_0(k2_xboole_0(X58,X60),X59) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X58,X59),k1_xboole_0),k4_xboole_0(k2_xboole_0(X58,X60),k2_xboole_0(X58,X59))) ),
    inference(forward_demodulation,[],[f15925,f15263])).

fof(f15263,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X4,k2_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X4,X2),k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f64,f19])).

fof(f64,plain,(
    ! [X6,X4,X5] : k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(X4,k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f56,f24])).

fof(f56,plain,(
    ! [X6,X4,X5] : k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(k4_xboole_0(X4,X5),X6) ),
    inference(superposition,[],[f24,f21])).

fof(f15925,plain,(
    ! [X59,X60,X58] : k2_xboole_0(k2_xboole_0(X58,X60),X59) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X58,X59),k1_xboole_0),k4_xboole_0(k2_xboole_0(k2_xboole_0(X58,X60),X59),k2_xboole_0(X58,X59))) ),
    inference(superposition,[],[f135,f15474])).

fof(f15474,plain,(
    ! [X101,X102,X100] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X100,X101),k2_xboole_0(k2_xboole_0(X100,X102),X101)) ),
    inference(backward_demodulation,[],[f8546,f15472])).

fof(f15472,plain,(
    ! [X121,X120,X119] : k2_xboole_0(k2_xboole_0(X120,X121),k4_xboole_0(X119,X120)) = k2_xboole_0(k2_xboole_0(X120,X121),X119) ),
    inference(forward_demodulation,[],[f15455,f350])).

fof(f350,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X2,X3),X3) ),
    inference(forward_demodulation,[],[f340,f21])).

fof(f340,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X2,X3),X3),X3) ),
    inference(superposition,[],[f29,f236])).

fof(f15455,plain,(
    ! [X121,X120,X119] : k2_xboole_0(k2_xboole_0(X120,X121),k4_xboole_0(X119,X120)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X120,X121),X119),X119) ),
    inference(backward_demodulation,[],[f8706,f15289])).

fof(f15289,plain,(
    ! [X85,X86,X84] : k4_xboole_0(X86,X84) = k4_xboole_0(k2_xboole_0(X86,k4_xboole_0(X84,X85)),X84) ),
    inference(superposition,[],[f64,f411])).

fof(f8706,plain,(
    ! [X121,X120,X119] : k2_xboole_0(k2_xboole_0(X120,X121),k4_xboole_0(X119,X120)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(X120,X121),k4_xboole_0(X119,X120)),X119),X119) ),
    inference(forward_demodulation,[],[f8613,f17])).

fof(f8613,plain,(
    ! [X121,X120,X119] : k2_xboole_0(k2_xboole_0(X120,X121),k4_xboole_0(X119,X120)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(X120,X121),k4_xboole_0(X119,X120)),X119),k4_xboole_0(X119,k1_xboole_0)) ),
    inference(superposition,[],[f463,f5206])).

fof(f5206,plain,(
    ! [X6,X7,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f307,f24])).

fof(f307,plain,(
    ! [X14,X15,X16] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X14,k2_xboole_0(X15,X16)),k4_xboole_0(X14,X15)) ),
    inference(superposition,[],[f292,f24])).

fof(f463,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,k4_xboole_0(X6,X5))) = X5 ),
    inference(backward_demodulation,[],[f383,f453])).

fof(f383,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k4_xboole_0(X5,X6)) = k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,k4_xboole_0(X6,X5))) ),
    inference(superposition,[],[f237,f28])).

fof(f8546,plain,(
    ! [X101,X102,X100] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X100,X101),k2_xboole_0(k2_xboole_0(X100,X102),k4_xboole_0(X101,X100))) ),
    inference(superposition,[],[f5206,f32])).

fof(f135,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[],[f29,f28])).

fof(f27,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f16,f23,f20])).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:23:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (971)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.43  % (969)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.44  % (952)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (951)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (949)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (947)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (970)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (946)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (945)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (968)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (968)Refutation not found, incomplete strategy% (968)------------------------------
% 0.21/0.48  % (968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (968)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (968)Memory used [KB]: 10618
% 0.21/0.48  % (968)Time elapsed: 0.072 s
% 0.21/0.48  % (968)------------------------------
% 0.21/0.48  % (968)------------------------------
% 0.21/0.49  % (948)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (962)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (965)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (973)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (953)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (974)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (972)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.52  % (967)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 4.71/1.02  % (949)Time limit reached!
% 4.71/1.02  % (949)------------------------------
% 4.71/1.02  % (949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.71/1.02  % (949)Termination reason: Time limit
% 4.71/1.02  % (949)Termination phase: Saturation
% 4.71/1.02  
% 4.71/1.02  % (949)Memory used [KB]: 16247
% 4.71/1.02  % (949)Time elapsed: 0.600 s
% 4.71/1.02  % (949)------------------------------
% 4.71/1.02  % (949)------------------------------
% 5.32/1.05  % (971)Refutation found. Thanks to Tanya!
% 5.32/1.05  % SZS status Theorem for theBenchmark
% 5.32/1.05  % SZS output start Proof for theBenchmark
% 5.32/1.05  fof(f19959,plain,(
% 5.32/1.05    $false),
% 5.32/1.05    inference(subsumption_resolution,[],[f19958,f544])).
% 5.32/1.05  fof(f544,plain,(
% 5.32/1.05    ( ! [X8,X9] : (k2_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(X9,X8),X8)) )),
% 5.32/1.05    inference(forward_demodulation,[],[f514,f32])).
% 5.32/1.05  fof(f32,plain,(
% 5.32/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 5.32/1.05    inference(superposition,[],[f21,f19])).
% 5.32/1.05  fof(f19,plain,(
% 5.32/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 5.32/1.05    inference(cnf_transformation,[],[f1])).
% 5.32/1.05  fof(f1,axiom,(
% 5.32/1.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 5.32/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 5.32/1.05  fof(f21,plain,(
% 5.32/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 5.32/1.05    inference(cnf_transformation,[],[f6])).
% 5.32/1.05  fof(f6,axiom,(
% 5.32/1.05    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 5.32/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 5.32/1.05  fof(f514,plain,(
% 5.32/1.05    ( ! [X8,X9] : (k2_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X8,X9),X8),X8)) )),
% 5.32/1.05    inference(superposition,[],[f29,f227])).
% 5.32/1.05  fof(f227,plain,(
% 5.32/1.05    ( ! [X8,X9] : (k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X9,X8)) = X8) )),
% 5.32/1.05    inference(forward_demodulation,[],[f226,f17])).
% 5.32/1.05  fof(f17,plain,(
% 5.32/1.05    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.32/1.05    inference(cnf_transformation,[],[f5])).
% 5.32/1.05  fof(f5,axiom,(
% 5.32/1.05    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 5.32/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 5.32/1.05  fof(f226,plain,(
% 5.32/1.05    ( ! [X8,X9] : (k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X9,X8)) = k4_xboole_0(X8,k1_xboole_0)) )),
% 5.32/1.05    inference(backward_demodulation,[],[f70,f225])).
% 5.32/1.05  fof(f225,plain,(
% 5.32/1.05    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 5.32/1.05    inference(forward_demodulation,[],[f206,f204])).
% 5.32/1.05  fof(f204,plain,(
% 5.32/1.05    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 5.32/1.05    inference(forward_demodulation,[],[f189,f138])).
% 5.32/1.05  fof(f138,plain,(
% 5.32/1.05    ( ! [X7] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,X7),k4_xboole_0(k1_xboole_0,X7))) )),
% 5.32/1.05    inference(superposition,[],[f29,f91])).
% 5.32/1.05  fof(f91,plain,(
% 5.32/1.05    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) )),
% 5.32/1.05    inference(superposition,[],[f68,f44])).
% 5.32/1.05  fof(f44,plain,(
% 5.32/1.05    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0)) )),
% 5.32/1.05    inference(superposition,[],[f21,f38])).
% 5.32/1.05  fof(f38,plain,(
% 5.32/1.05    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 5.32/1.05    inference(superposition,[],[f36,f19])).
% 5.32/1.05  fof(f36,plain,(
% 5.32/1.05    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 5.32/1.05    inference(forward_demodulation,[],[f34,f17])).
% 5.32/1.05  fof(f34,plain,(
% 5.32/1.05    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 5.32/1.05    inference(superposition,[],[f21,f17])).
% 5.32/1.05  fof(f68,plain,(
% 5.32/1.05    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 5.32/1.05    inference(superposition,[],[f28,f17])).
% 5.32/1.05  fof(f28,plain,(
% 5.32/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 5.32/1.05    inference(definition_unfolding,[],[f18,f20,f20])).
% 5.32/1.05  fof(f20,plain,(
% 5.32/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 5.32/1.05    inference(cnf_transformation,[],[f8])).
% 5.32/1.05  fof(f8,axiom,(
% 5.32/1.05    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.32/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.32/1.05  fof(f18,plain,(
% 5.32/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.32/1.05    inference(cnf_transformation,[],[f2])).
% 5.32/1.05  fof(f2,axiom,(
% 5.32/1.05    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.32/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.32/1.05  fof(f189,plain,(
% 5.32/1.05    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,X1))) )),
% 5.32/1.05    inference(superposition,[],[f177,f91])).
% 5.32/1.05  fof(f177,plain,(
% 5.32/1.05    ( ! [X0] : (k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) = X0) )),
% 5.32/1.05    inference(forward_demodulation,[],[f167,f91])).
% 5.32/1.05  fof(f167,plain,(
% 5.32/1.05    ( ! [X0] : (k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),X0) = X0) )),
% 5.32/1.05    inference(superposition,[],[f141,f68])).
% 5.32/1.05  fof(f141,plain,(
% 5.32/1.05    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0) )),
% 5.32/1.05    inference(superposition,[],[f29,f17])).
% 5.32/1.05  fof(f206,plain,(
% 5.32/1.05    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) )),
% 5.32/1.05    inference(backward_demodulation,[],[f55,f204])).
% 5.32/1.05  fof(f55,plain,(
% 5.32/1.05    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),X3)) )),
% 5.32/1.05    inference(superposition,[],[f24,f44])).
% 5.32/1.05  fof(f24,plain,(
% 5.32/1.05    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 5.32/1.05    inference(cnf_transformation,[],[f7])).
% 5.32/1.05  fof(f7,axiom,(
% 5.32/1.05    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 5.32/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 5.32/1.05  fof(f70,plain,(
% 5.32/1.05    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X8,X9))) = k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X9,X8))) )),
% 5.32/1.05    inference(superposition,[],[f28,f32])).
% 5.32/1.05  fof(f29,plain,(
% 5.32/1.05    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 5.32/1.05    inference(definition_unfolding,[],[f22,f20])).
% 5.32/1.05  fof(f22,plain,(
% 5.32/1.05    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 5.32/1.05    inference(cnf_transformation,[],[f9])).
% 5.32/1.05  fof(f9,axiom,(
% 5.32/1.05    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 5.32/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 5.32/1.05  fof(f19958,plain,(
% 5.32/1.05    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)),
% 5.32/1.05    inference(forward_demodulation,[],[f19957,f453])).
% 5.32/1.05  fof(f453,plain,(
% 5.32/1.05    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 5.32/1.05    inference(superposition,[],[f411,f19])).
% 5.32/1.05  fof(f411,plain,(
% 5.32/1.05    ( ! [X19,X20] : (k2_xboole_0(k4_xboole_0(X19,X20),X19) = X19) )),
% 5.32/1.05    inference(forward_demodulation,[],[f390,f36])).
% 5.32/1.05  fof(f390,plain,(
% 5.32/1.05    ( ! [X19,X20] : (k2_xboole_0(k4_xboole_0(X19,X20),X19) = k2_xboole_0(X19,k1_xboole_0)) )),
% 5.32/1.05    inference(superposition,[],[f237,f292])).
% 5.32/1.05  fof(f292,plain,(
% 5.32/1.05    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X6,X7),X6)) )),
% 5.32/1.05    inference(superposition,[],[f234,f29])).
% 5.32/1.05  fof(f234,plain,(
% 5.32/1.05    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 5.32/1.05    inference(forward_demodulation,[],[f217,f228])).
% 5.32/1.05  fof(f228,plain,(
% 5.32/1.05    ( ! [X10,X9] : (k2_xboole_0(X9,X10) = k2_xboole_0(X9,k4_xboole_0(X10,X9))) )),
% 5.32/1.05    inference(backward_demodulation,[],[f147,f227])).
% 5.32/1.05  fof(f147,plain,(
% 5.32/1.05    ( ! [X10,X9] : (k2_xboole_0(X9,X10) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),k4_xboole_0(X10,X9)),k4_xboole_0(X10,X9))) )),
% 5.32/1.05    inference(superposition,[],[f29,f32])).
% 5.32/1.05  fof(f217,plain,(
% 5.32/1.05    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 5.32/1.05    inference(backward_demodulation,[],[f61,f204])).
% 5.32/1.05  fof(f61,plain,(
% 5.32/1.05    ( ! [X6,X5] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(X5,X6)) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 5.32/1.05    inference(superposition,[],[f24,f44])).
% 5.32/1.05  fof(f237,plain,(
% 5.32/1.05    ( ! [X8,X7] : (k2_xboole_0(X7,X8) = k2_xboole_0(X8,k4_xboole_0(X7,X8))) )),
% 5.32/1.05    inference(backward_demodulation,[],[f146,f236])).
% 5.32/1.05  fof(f236,plain,(
% 5.32/1.05    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = X7) )),
% 5.32/1.05    inference(forward_demodulation,[],[f235,f17])).
% 5.32/1.05  fof(f235,plain,(
% 5.32/1.05    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = k4_xboole_0(X7,k1_xboole_0)) )),
% 5.32/1.05    inference(backward_demodulation,[],[f69,f234])).
% 5.32/1.05  fof(f69,plain,(
% 5.32/1.05    ( ! [X6,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(X6,X7))) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7))) )),
% 5.32/1.05    inference(superposition,[],[f28,f21])).
% 5.32/1.05  fof(f146,plain,(
% 5.32/1.05    ( ! [X8,X7] : (k2_xboole_0(X7,X8) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X7,X8)),k4_xboole_0(X7,X8))) )),
% 5.32/1.05    inference(superposition,[],[f29,f21])).
% 5.32/1.05  fof(f19957,plain,(
% 5.32/1.05    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 5.32/1.05    inference(forward_demodulation,[],[f19956,f19])).
% 5.32/1.05  fof(f19956,plain,(
% 5.32/1.05    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0))),
% 5.32/1.05    inference(forward_demodulation,[],[f19763,f228])).
% 5.32/1.05  fof(f19763,plain,(
% 5.32/1.05    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 5.32/1.05    inference(superposition,[],[f27,f16017])).
% 5.32/1.05  fof(f16017,plain,(
% 5.32/1.05    ( ! [X59,X60,X58] : (k2_xboole_0(X60,k2_xboole_0(X58,X59)) = k2_xboole_0(k2_xboole_0(X58,X60),X59)) )),
% 5.32/1.05    inference(forward_demodulation,[],[f16016,f237])).
% 5.32/1.05  fof(f16016,plain,(
% 5.32/1.05    ( ! [X59,X60,X58] : (k2_xboole_0(k2_xboole_0(X58,X59),k4_xboole_0(X60,k2_xboole_0(X58,X59))) = k2_xboole_0(k2_xboole_0(X58,X60),X59)) )),
% 5.32/1.05    inference(forward_demodulation,[],[f16015,f17])).
% 5.32/1.05  fof(f16015,plain,(
% 5.32/1.05    ( ! [X59,X60,X58] : (k2_xboole_0(k2_xboole_0(X58,X60),X59) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X58,X59),k1_xboole_0),k4_xboole_0(X60,k2_xboole_0(X58,X59)))) )),
% 5.32/1.05    inference(forward_demodulation,[],[f16014,f65])).
% 5.32/1.05  fof(f65,plain,(
% 5.32/1.05    ( ! [X8,X7,X9] : (k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,X9)) = k4_xboole_0(X8,k2_xboole_0(X7,X9))) )),
% 5.32/1.05    inference(forward_demodulation,[],[f57,f24])).
% 5.32/1.05  fof(f57,plain,(
% 5.32/1.05    ( ! [X8,X7,X9] : (k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,X9)) = k4_xboole_0(k4_xboole_0(X8,X7),X9)) )),
% 5.32/1.05    inference(superposition,[],[f24,f32])).
% 5.32/1.05  fof(f16014,plain,(
% 5.32/1.05    ( ! [X59,X60,X58] : (k2_xboole_0(k2_xboole_0(X58,X60),X59) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X58,X59),k1_xboole_0),k4_xboole_0(k2_xboole_0(X58,X60),k2_xboole_0(X58,X59)))) )),
% 5.32/1.05    inference(forward_demodulation,[],[f15925,f15263])).
% 5.32/1.05  fof(f15263,plain,(
% 5.32/1.05    ( ! [X4,X2,X3] : (k4_xboole_0(X4,k2_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X4,X2),k2_xboole_0(X3,X2))) )),
% 5.32/1.05    inference(superposition,[],[f64,f19])).
% 5.32/1.05  fof(f64,plain,(
% 5.32/1.05    ( ! [X6,X4,X5] : (k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(X4,k2_xboole_0(X5,X6))) )),
% 5.32/1.05    inference(forward_demodulation,[],[f56,f24])).
% 5.32/1.05  fof(f56,plain,(
% 5.32/1.05    ( ! [X6,X4,X5] : (k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(k4_xboole_0(X4,X5),X6)) )),
% 5.32/1.05    inference(superposition,[],[f24,f21])).
% 5.32/1.05  fof(f15925,plain,(
% 5.32/1.05    ( ! [X59,X60,X58] : (k2_xboole_0(k2_xboole_0(X58,X60),X59) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X58,X59),k1_xboole_0),k4_xboole_0(k2_xboole_0(k2_xboole_0(X58,X60),X59),k2_xboole_0(X58,X59)))) )),
% 5.32/1.05    inference(superposition,[],[f135,f15474])).
% 5.32/1.05  fof(f15474,plain,(
% 5.32/1.05    ( ! [X101,X102,X100] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X100,X101),k2_xboole_0(k2_xboole_0(X100,X102),X101))) )),
% 5.32/1.05    inference(backward_demodulation,[],[f8546,f15472])).
% 5.32/1.05  fof(f15472,plain,(
% 5.32/1.05    ( ! [X121,X120,X119] : (k2_xboole_0(k2_xboole_0(X120,X121),k4_xboole_0(X119,X120)) = k2_xboole_0(k2_xboole_0(X120,X121),X119)) )),
% 5.32/1.05    inference(forward_demodulation,[],[f15455,f350])).
% 5.32/1.05  fof(f350,plain,(
% 5.32/1.05    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X2,X3),X3)) )),
% 5.32/1.05    inference(forward_demodulation,[],[f340,f21])).
% 5.32/1.05  fof(f340,plain,(
% 5.32/1.05    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X2,X3),X3),X3)) )),
% 5.32/1.05    inference(superposition,[],[f29,f236])).
% 5.32/1.05  fof(f15455,plain,(
% 5.32/1.05    ( ! [X121,X120,X119] : (k2_xboole_0(k2_xboole_0(X120,X121),k4_xboole_0(X119,X120)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X120,X121),X119),X119)) )),
% 5.32/1.05    inference(backward_demodulation,[],[f8706,f15289])).
% 5.32/1.05  fof(f15289,plain,(
% 5.32/1.05    ( ! [X85,X86,X84] : (k4_xboole_0(X86,X84) = k4_xboole_0(k2_xboole_0(X86,k4_xboole_0(X84,X85)),X84)) )),
% 5.32/1.05    inference(superposition,[],[f64,f411])).
% 5.32/1.05  fof(f8706,plain,(
% 5.32/1.05    ( ! [X121,X120,X119] : (k2_xboole_0(k2_xboole_0(X120,X121),k4_xboole_0(X119,X120)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(X120,X121),k4_xboole_0(X119,X120)),X119),X119)) )),
% 5.32/1.05    inference(forward_demodulation,[],[f8613,f17])).
% 5.32/1.05  fof(f8613,plain,(
% 5.32/1.05    ( ! [X121,X120,X119] : (k2_xboole_0(k2_xboole_0(X120,X121),k4_xboole_0(X119,X120)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(X120,X121),k4_xboole_0(X119,X120)),X119),k4_xboole_0(X119,k1_xboole_0))) )),
% 5.32/1.05    inference(superposition,[],[f463,f5206])).
% 5.32/1.05  fof(f5206,plain,(
% 5.32/1.05    ( ! [X6,X7,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X5,X6)))) )),
% 5.32/1.05    inference(superposition,[],[f307,f24])).
% 5.32/1.05  fof(f307,plain,(
% 5.32/1.05    ( ! [X14,X15,X16] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X14,k2_xboole_0(X15,X16)),k4_xboole_0(X14,X15))) )),
% 5.32/1.05    inference(superposition,[],[f292,f24])).
% 5.32/1.05  fof(f463,plain,(
% 5.32/1.05    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,k4_xboole_0(X6,X5))) = X5) )),
% 5.32/1.05    inference(backward_demodulation,[],[f383,f453])).
% 5.32/1.05  fof(f383,plain,(
% 5.32/1.05    ( ! [X6,X5] : (k2_xboole_0(X5,k4_xboole_0(X5,X6)) = k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,k4_xboole_0(X6,X5)))) )),
% 5.32/1.05    inference(superposition,[],[f237,f28])).
% 5.32/1.05  fof(f8546,plain,(
% 5.32/1.05    ( ! [X101,X102,X100] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X100,X101),k2_xboole_0(k2_xboole_0(X100,X102),k4_xboole_0(X101,X100)))) )),
% 5.32/1.05    inference(superposition,[],[f5206,f32])).
% 5.32/1.05  fof(f135,plain,(
% 5.32/1.05    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0) )),
% 5.32/1.05    inference(superposition,[],[f29,f28])).
% 5.32/1.05  fof(f27,plain,(
% 5.32/1.05    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 5.32/1.05    inference(definition_unfolding,[],[f16,f23,f20])).
% 5.32/1.05  fof(f23,plain,(
% 5.32/1.05    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 5.32/1.05    inference(cnf_transformation,[],[f3])).
% 5.32/1.05  fof(f3,axiom,(
% 5.32/1.05    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 5.32/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 5.32/1.05  fof(f16,plain,(
% 5.32/1.05    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 5.32/1.05    inference(cnf_transformation,[],[f15])).
% 5.32/1.05  fof(f15,plain,(
% 5.32/1.05    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 5.32/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 5.32/1.05  fof(f14,plain,(
% 5.32/1.05    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 5.32/1.05    introduced(choice_axiom,[])).
% 5.32/1.05  fof(f13,plain,(
% 5.32/1.05    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.32/1.05    inference(ennf_transformation,[],[f12])).
% 5.32/1.05  fof(f12,negated_conjecture,(
% 5.32/1.05    ~! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.32/1.05    inference(negated_conjecture,[],[f11])).
% 5.32/1.05  fof(f11,conjecture,(
% 5.32/1.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.32/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).
% 5.32/1.05  % SZS output end Proof for theBenchmark
% 5.32/1.05  % (971)------------------------------
% 5.32/1.05  % (971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.32/1.05  % (971)Termination reason: Refutation
% 5.32/1.05  
% 5.32/1.05  % (971)Memory used [KB]: 19317
% 5.32/1.05  % (971)Time elapsed: 0.619 s
% 5.32/1.05  % (971)------------------------------
% 5.32/1.05  % (971)------------------------------
% 5.32/1.06  % (941)Success in time 0.708 s
%------------------------------------------------------------------------------
