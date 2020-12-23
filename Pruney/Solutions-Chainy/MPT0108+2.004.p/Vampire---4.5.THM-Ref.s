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
% DateTime   : Thu Dec  3 12:32:18 EST 2020

% Result     : Theorem 5.69s
% Output     : Refutation 5.69s
% Verified   : 
% Statistics : Number of formulae       :  111 (3413 expanded)
%              Number of leaves         :   15 (1197 expanded)
%              Depth                    :   32
%              Number of atoms          :  112 (3414 expanded)
%              Number of equality atoms :  111 (3413 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9479,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f9478])).

fof(f9478,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f9477,f1421])).

fof(f1421,plain,(
    ! [X9] : k5_xboole_0(X9,k1_xboole_0) = X9 ),
    inference(backward_demodulation,[],[f611,f1400])).

fof(f1400,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[],[f1395,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1395,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(backward_demodulation,[],[f37,f1380])).

fof(f1380,plain,(
    ! [X2] : k3_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f1060,f692])).

fof(f692,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f35,f682])).

fof(f682,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f110,f651])).

fof(f651,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f31,f605])).

fof(f605,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f578,f35])).

fof(f578,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) = X2 ),
    inference(forward_demodulation,[],[f557,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) ),
    inference(backward_demodulation,[],[f41,f31])).

fof(f41,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f30,f27,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f557,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,k3_xboole_0(X3,X2)))) = X2 ),
    inference(superposition,[],[f46,f79])).

fof(f79,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,k3_xboole_0(X4,X5)) = k3_xboole_0(X5,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f31,f24])).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(forward_demodulation,[],[f40,f24])).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
    inference(definition_unfolding,[],[f25,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f110,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f35,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f28,f27,f27])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f1060,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f29,f1054])).

fof(f1054,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1051,f627])).

fof(f627,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(backward_demodulation,[],[f38,f605])).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f22,f34])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f1051,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f802,f29])).

fof(f802,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f37,f652])).

fof(f652,plain,(
    ! [X4] : k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X4,X4))) = X4 ),
    inference(superposition,[],[f35,f605])).

fof(f29,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f21,f34])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f611,plain,(
    ! [X9] : k5_xboole_0(X9,k3_xboole_0(X9,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(X9,k3_xboole_0(X9,k1_xboole_0)),k1_xboole_0) ),
    inference(superposition,[],[f37,f578])).

fof(f9477,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f9476,f1550])).

fof(f1550,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2) ),
    inference(backward_demodulation,[],[f1380,f1541])).

fof(f1541,plain,(
    ! [X19] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X19)) ),
    inference(superposition,[],[f1485,f651])).

fof(f1485,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1))) = X0 ),
    inference(forward_demodulation,[],[f1465,f24])).

fof(f1465,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0)) = X0 ),
    inference(backward_demodulation,[],[f683,f1441])).

fof(f1441,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f692,f1400])).

fof(f683,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = X0 ),
    inference(backward_demodulation,[],[f46,f651])).

fof(f9476,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK0))) ),
    inference(forward_demodulation,[],[f9475,f24])).

fof(f9475,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f9473,f1636])).

fof(f1636,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f1441,f1583])).

fof(f1583,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f1550,f24])).

fof(f9473,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)))) ),
    inference(backward_demodulation,[],[f3127,f9425])).

fof(f9425,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,k3_xboole_0(X3,X2)))) = X2 ),
    inference(superposition,[],[f4063,f1687])).

fof(f1687,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1))) ),
    inference(superposition,[],[f39,f24])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f34,f34])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f4063,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(forward_demodulation,[],[f4062,f1421])).

fof(f4062,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(forward_demodulation,[],[f4061,f1583])).

fof(f4061,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(forward_demodulation,[],[f3867,f1636])).

fof(f3867,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X0,X0))) ),
    inference(superposition,[],[f2062,f605])).

fof(f2062,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(backward_demodulation,[],[f50,f2059])).

fof(f2059,plain,(
    ! [X45,X43,X44] : k3_xboole_0(X43,k5_xboole_0(X44,k3_xboole_0(X44,k3_xboole_0(X43,X45)))) = k3_xboole_0(X44,k5_xboole_0(X43,k3_xboole_0(X43,X45))) ),
    inference(forward_demodulation,[],[f2058,f2053])).

fof(f2053,plain,(
    ! [X41,X42,X40] : k3_xboole_0(X41,k5_xboole_0(X40,k3_xboole_0(X40,X42))) = k3_xboole_0(X40,k3_xboole_0(X41,k5_xboole_0(X40,k3_xboole_0(X40,X42)))) ),
    inference(forward_demodulation,[],[f2052,f48])).

fof(f2052,plain,(
    ! [X41,X42,X40] : k3_xboole_0(X40,k5_xboole_0(k3_xboole_0(X41,X40),k3_xboole_0(X41,k3_xboole_0(X40,X42)))) = k3_xboole_0(X41,k5_xboole_0(X40,k3_xboole_0(X40,X42))) ),
    inference(forward_demodulation,[],[f2051,f651])).

fof(f2051,plain,(
    ! [X41,X42,X40] : k3_xboole_0(X40,k5_xboole_0(k3_xboole_0(X41,X40),k3_xboole_0(X41,k3_xboole_0(X40,X42)))) = k3_xboole_0(X41,k5_xboole_0(X40,k3_xboole_0(X40,k3_xboole_0(X40,X42)))) ),
    inference(forward_demodulation,[],[f2050,f763])).

fof(f763,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k3_xboole_0(X0,X2))) ),
    inference(backward_demodulation,[],[f51,f718])).

fof(f718,plain,(
    ! [X6,X4,X5] : k3_xboole_0(X6,k3_xboole_0(X4,X5)) = k3_xboole_0(X4,k3_xboole_0(X6,k3_xboole_0(X4,X5))) ),
    inference(superposition,[],[f651,f79])).

fof(f51,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X0,X2)))) ),
    inference(forward_demodulation,[],[f43,f31])).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f33,f27,f27])).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f2050,plain,(
    ! [X41,X42,X40] : k3_xboole_0(X40,k5_xboole_0(k3_xboole_0(X41,X40),k3_xboole_0(X41,k3_xboole_0(X40,X42)))) = k5_xboole_0(k3_xboole_0(X41,X40),k3_xboole_0(X40,k3_xboole_0(X41,k3_xboole_0(X40,X42)))) ),
    inference(forward_demodulation,[],[f1977,f31])).

fof(f1977,plain,(
    ! [X41,X42,X40] : k3_xboole_0(X40,k5_xboole_0(k3_xboole_0(X41,X40),k3_xboole_0(k3_xboole_0(X41,X40),X42))) = k5_xboole_0(k3_xboole_0(X41,X40),k3_xboole_0(X40,k3_xboole_0(k3_xboole_0(X41,X40),X42))) ),
    inference(superposition,[],[f48,f680])).

fof(f680,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,k3_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f675,f651])).

fof(f675,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,k3_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f640,f24])).

fof(f640,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,k3_xboole_0(k3_xboole_0(X2,X3),X2)) ),
    inference(superposition,[],[f605,f79])).

fof(f2058,plain,(
    ! [X45,X43,X44] : k3_xboole_0(X43,k5_xboole_0(X44,k3_xboole_0(X44,k3_xboole_0(X43,X45)))) = k3_xboole_0(X43,k3_xboole_0(X44,k5_xboole_0(X43,k3_xboole_0(X43,X45)))) ),
    inference(forward_demodulation,[],[f2057,f48])).

fof(f2057,plain,(
    ! [X45,X43,X44] : k3_xboole_0(X43,k5_xboole_0(k3_xboole_0(X44,X43),k3_xboole_0(X44,k3_xboole_0(X43,X45)))) = k3_xboole_0(X43,k5_xboole_0(X44,k3_xboole_0(X44,k3_xboole_0(X43,X45)))) ),
    inference(forward_demodulation,[],[f2056,f48])).

fof(f2056,plain,(
    ! [X45,X43,X44] : k3_xboole_0(X43,k5_xboole_0(k3_xboole_0(X44,X43),k3_xboole_0(X44,k3_xboole_0(X43,X45)))) = k5_xboole_0(k3_xboole_0(X43,X44),k3_xboole_0(X43,k3_xboole_0(X44,k3_xboole_0(X43,X45)))) ),
    inference(forward_demodulation,[],[f1978,f31])).

fof(f1978,plain,(
    ! [X45,X43,X44] : k3_xboole_0(X43,k5_xboole_0(k3_xboole_0(X44,X43),k3_xboole_0(k3_xboole_0(X44,X43),X45))) = k5_xboole_0(k3_xboole_0(X43,X44),k3_xboole_0(X43,k3_xboole_0(k3_xboole_0(X44,X43),X45))) ),
    inference(superposition,[],[f48,f661])).

fof(f661,plain,(
    ! [X21,X20] : k3_xboole_0(X20,X21) = k3_xboole_0(X20,k3_xboole_0(X21,X20)) ),
    inference(superposition,[],[f134,f605])).

fof(f134,plain,(
    ! [X6,X8,X7] : k3_xboole_0(X8,k3_xboole_0(X6,X7)) = k3_xboole_0(k3_xboole_0(X7,X8),X6) ),
    inference(superposition,[],[f79,f24])).

fof(f50,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(X0,X1))))) ),
    inference(forward_demodulation,[],[f49,f48])).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(X0,X1))))) ),
    inference(forward_demodulation,[],[f42,f31])).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f32,f34,f34])).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f3127,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))) ),
    inference(forward_demodulation,[],[f3126,f48])).

fof(f3126,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))) ),
    inference(forward_demodulation,[],[f3125,f29])).

fof(f3125,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))) ),
    inference(superposition,[],[f47,f29])).

fof(f47,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) ),
    inference(backward_demodulation,[],[f45,f31])).

fof(f45,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f44,f24])).

fof(f44,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f36,f24])).

fof(f36,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f20,f27,f34])).

fof(f20,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (1669)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.45  % (1669)Refutation not found, incomplete strategy% (1669)------------------------------
% 0.20/0.45  % (1669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (1669)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (1669)Memory used [KB]: 10618
% 0.20/0.45  % (1669)Time elapsed: 0.043 s
% 0.20/0.45  % (1669)------------------------------
% 0.20/0.45  % (1669)------------------------------
% 0.20/0.46  % (1673)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (1659)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (1665)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (1670)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (1668)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (1663)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (1674)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  % (1667)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (1661)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (1664)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (1672)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (1658)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (1662)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (1671)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (1660)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.50  % (1666)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.50  % (1676)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 5.18/1.02  % (1662)Time limit reached!
% 5.18/1.02  % (1662)------------------------------
% 5.18/1.02  % (1662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.18/1.02  % (1662)Termination reason: Time limit
% 5.18/1.02  % (1662)Termination phase: Saturation
% 5.18/1.02  
% 5.18/1.02  % (1662)Memory used [KB]: 15351
% 5.18/1.02  % (1662)Time elapsed: 0.600 s
% 5.18/1.02  % (1662)------------------------------
% 5.18/1.02  % (1662)------------------------------
% 5.69/1.10  % (1659)Refutation found. Thanks to Tanya!
% 5.69/1.10  % SZS status Theorem for theBenchmark
% 5.69/1.10  % SZS output start Proof for theBenchmark
% 5.69/1.10  fof(f9479,plain,(
% 5.69/1.10    $false),
% 5.69/1.10    inference(trivial_inequality_removal,[],[f9478])).
% 5.69/1.10  fof(f9478,plain,(
% 5.69/1.10    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1)),
% 5.69/1.10    inference(forward_demodulation,[],[f9477,f1421])).
% 5.69/1.10  fof(f1421,plain,(
% 5.69/1.10    ( ! [X9] : (k5_xboole_0(X9,k1_xboole_0) = X9) )),
% 5.69/1.10    inference(backward_demodulation,[],[f611,f1400])).
% 5.69/1.10  fof(f1400,plain,(
% 5.69/1.10    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 5.69/1.10    inference(superposition,[],[f1395,f24])).
% 5.69/1.10  fof(f24,plain,(
% 5.69/1.10    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.69/1.10    inference(cnf_transformation,[],[f2])).
% 5.69/1.10  fof(f2,axiom,(
% 5.69/1.10    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.69/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.69/1.10  fof(f1395,plain,(
% 5.69/1.10    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0) )),
% 5.69/1.10    inference(backward_demodulation,[],[f37,f1380])).
% 5.69/1.10  fof(f1380,plain,(
% 5.69/1.10    ( ! [X2] : (k3_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2))) )),
% 5.69/1.10    inference(superposition,[],[f1060,f692])).
% 5.69/1.10  fof(f692,plain,(
% 5.69/1.10    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 5.69/1.10    inference(backward_demodulation,[],[f35,f682])).
% 5.69/1.10  fof(f682,plain,(
% 5.69/1.10    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 5.69/1.10    inference(backward_demodulation,[],[f110,f651])).
% 5.69/1.10  fof(f651,plain,(
% 5.69/1.10    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 5.69/1.10    inference(superposition,[],[f31,f605])).
% 5.69/1.10  fof(f605,plain,(
% 5.69/1.10    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 5.69/1.10    inference(superposition,[],[f578,f35])).
% 5.69/1.10  fof(f578,plain,(
% 5.69/1.10    ( ! [X2,X3] : (k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) = X2) )),
% 5.69/1.10    inference(forward_demodulation,[],[f557,f48])).
% 5.69/1.10  fof(f48,plain,(
% 5.69/1.10    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))) )),
% 5.69/1.10    inference(backward_demodulation,[],[f41,f31])).
% 5.69/1.10  fof(f41,plain,(
% 5.69/1.10    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 5.69/1.10    inference(definition_unfolding,[],[f30,f27,f27])).
% 5.69/1.10  fof(f27,plain,(
% 5.69/1.10    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.69/1.10    inference(cnf_transformation,[],[f4])).
% 5.69/1.10  fof(f4,axiom,(
% 5.69/1.10    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.69/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 5.69/1.10  fof(f30,plain,(
% 5.69/1.10    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 5.69/1.10    inference(cnf_transformation,[],[f10])).
% 5.69/1.10  fof(f10,axiom,(
% 5.69/1.10    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 5.69/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 5.69/1.10  fof(f557,plain,(
% 5.69/1.10    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,k3_xboole_0(X3,X2)))) = X2) )),
% 5.69/1.10    inference(superposition,[],[f46,f79])).
% 5.69/1.10  fof(f79,plain,(
% 5.69/1.10    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k3_xboole_0(X4,X5)) = k3_xboole_0(X5,k3_xboole_0(X3,X4))) )),
% 5.69/1.10    inference(superposition,[],[f31,f24])).
% 5.69/1.10  fof(f46,plain,(
% 5.69/1.10    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0) )),
% 5.69/1.10    inference(forward_demodulation,[],[f40,f24])).
% 5.69/1.10  fof(f40,plain,(
% 5.69/1.10    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0) )),
% 5.69/1.10    inference(definition_unfolding,[],[f25,f34])).
% 5.69/1.10  fof(f34,plain,(
% 5.69/1.10    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 5.69/1.10    inference(definition_unfolding,[],[f26,f27])).
% 5.69/1.10  fof(f26,plain,(
% 5.69/1.10    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 5.69/1.10    inference(cnf_transformation,[],[f13])).
% 5.69/1.10  fof(f13,axiom,(
% 5.69/1.10    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 5.69/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 5.69/1.10  fof(f25,plain,(
% 5.69/1.10    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 5.69/1.10    inference(cnf_transformation,[],[f7])).
% 5.69/1.10  fof(f7,axiom,(
% 5.69/1.10    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 5.69/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 5.69/1.10  fof(f31,plain,(
% 5.69/1.10    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 5.69/1.10    inference(cnf_transformation,[],[f5])).
% 5.69/1.10  fof(f5,axiom,(
% 5.69/1.10    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 5.69/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 5.69/1.10  fof(f110,plain,(
% 5.69/1.10    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 5.69/1.10    inference(superposition,[],[f35,f35])).
% 5.69/1.10  fof(f35,plain,(
% 5.69/1.10    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 5.69/1.10    inference(definition_unfolding,[],[f28,f27,f27])).
% 5.69/1.10  fof(f28,plain,(
% 5.69/1.10    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 5.69/1.10    inference(cnf_transformation,[],[f9])).
% 5.69/1.10  fof(f9,axiom,(
% 5.69/1.10    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.69/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.69/1.10  fof(f1060,plain,(
% 5.69/1.10    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 5.69/1.10    inference(superposition,[],[f29,f1054])).
% 5.69/1.10  fof(f1054,plain,(
% 5.69/1.10    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 5.69/1.10    inference(forward_demodulation,[],[f1051,f627])).
% 5.69/1.10  fof(f627,plain,(
% 5.69/1.10    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 5.69/1.10    inference(backward_demodulation,[],[f38,f605])).
% 5.69/1.10  fof(f38,plain,(
% 5.69/1.10    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 5.69/1.10    inference(definition_unfolding,[],[f22,f34])).
% 5.69/1.10  fof(f22,plain,(
% 5.69/1.10    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 5.69/1.10    inference(cnf_transformation,[],[f16])).
% 5.69/1.10  fof(f16,plain,(
% 5.69/1.10    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 5.69/1.10    inference(rectify,[],[f3])).
% 5.69/1.10  fof(f3,axiom,(
% 5.69/1.10    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 5.69/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 5.69/1.10  fof(f1051,plain,(
% 5.69/1.10    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))),
% 5.69/1.10    inference(superposition,[],[f802,f29])).
% 5.69/1.10  fof(f802,plain,(
% 5.69/1.10    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 5.69/1.10    inference(superposition,[],[f37,f652])).
% 5.69/1.10  fof(f652,plain,(
% 5.69/1.10    ( ! [X4] : (k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X4,X4))) = X4) )),
% 5.69/1.10    inference(superposition,[],[f35,f605])).
% 5.69/1.10  fof(f29,plain,(
% 5.69/1.10    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 5.69/1.10    inference(cnf_transformation,[],[f12])).
% 5.69/1.10  fof(f12,axiom,(
% 5.69/1.10    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 5.69/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 5.69/1.10  fof(f37,plain,(
% 5.69/1.10    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 5.69/1.10    inference(definition_unfolding,[],[f21,f34])).
% 5.69/1.10  fof(f21,plain,(
% 5.69/1.10    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.69/1.10    inference(cnf_transformation,[],[f6])).
% 5.69/1.10  fof(f6,axiom,(
% 5.69/1.10    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 5.69/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 5.69/1.10  fof(f611,plain,(
% 5.69/1.10    ( ! [X9] : (k5_xboole_0(X9,k3_xboole_0(X9,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(X9,k3_xboole_0(X9,k1_xboole_0)),k1_xboole_0)) )),
% 5.69/1.10    inference(superposition,[],[f37,f578])).
% 5.69/1.10  fof(f9477,plain,(
% 5.69/1.10    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0))),
% 5.69/1.10    inference(forward_demodulation,[],[f9476,f1550])).
% 5.69/1.10  fof(f1550,plain,(
% 5.69/1.10    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) )),
% 5.69/1.10    inference(backward_demodulation,[],[f1380,f1541])).
% 5.69/1.10  fof(f1541,plain,(
% 5.69/1.10    ( ! [X19] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X19))) )),
% 5.69/1.10    inference(superposition,[],[f1485,f651])).
% 5.69/1.10  fof(f1485,plain,(
% 5.69/1.10    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1))) = X0) )),
% 5.69/1.10    inference(forward_demodulation,[],[f1465,f24])).
% 5.69/1.10  fof(f1465,plain,(
% 5.69/1.10    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0)) = X0) )),
% 5.69/1.10    inference(backward_demodulation,[],[f683,f1441])).
% 5.69/1.10  fof(f1441,plain,(
% 5.69/1.10    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0)) )),
% 5.69/1.10    inference(superposition,[],[f692,f1400])).
% 5.69/1.10  fof(f683,plain,(
% 5.69/1.10    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = X0) )),
% 5.69/1.10    inference(backward_demodulation,[],[f46,f651])).
% 5.69/1.10  fof(f9476,plain,(
% 5.69/1.10    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK0)))),
% 5.69/1.10    inference(forward_demodulation,[],[f9475,f24])).
% 5.69/1.10  fof(f9475,plain,(
% 5.69/1.10    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k1_xboole_0)))),
% 5.69/1.10    inference(forward_demodulation,[],[f9473,f1636])).
% 5.69/1.10  fof(f1636,plain,(
% 5.69/1.10    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 5.69/1.10    inference(backward_demodulation,[],[f1441,f1583])).
% 5.69/1.10  fof(f1583,plain,(
% 5.69/1.10    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 5.69/1.10    inference(superposition,[],[f1550,f24])).
% 5.69/1.10  fof(f9473,plain,(
% 5.69/1.10    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,sK1))))),
% 5.69/1.10    inference(backward_demodulation,[],[f3127,f9425])).
% 5.69/1.10  fof(f9425,plain,(
% 5.69/1.10    ( ! [X2,X3] : (k3_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,k3_xboole_0(X3,X2)))) = X2) )),
% 5.69/1.10    inference(superposition,[],[f4063,f1687])).
% 5.69/1.10  fof(f1687,plain,(
% 5.69/1.10    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) )),
% 5.69/1.10    inference(superposition,[],[f39,f24])).
% 5.69/1.10  fof(f39,plain,(
% 5.69/1.10    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 5.69/1.10    inference(definition_unfolding,[],[f23,f34,f34])).
% 5.69/1.10  fof(f23,plain,(
% 5.69/1.10    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 5.69/1.10    inference(cnf_transformation,[],[f1])).
% 5.69/1.10  fof(f1,axiom,(
% 5.69/1.10    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 5.69/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 5.69/1.10  fof(f4063,plain,(
% 5.69/1.10    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 5.69/1.10    inference(forward_demodulation,[],[f4062,f1421])).
% 5.69/1.10  fof(f4062,plain,(
% 5.69/1.10    ( ! [X0,X1] : (k5_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 5.69/1.10    inference(forward_demodulation,[],[f4061,f1583])).
% 5.69/1.10  fof(f4061,plain,(
% 5.69/1.10    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) = k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 5.69/1.10    inference(forward_demodulation,[],[f3867,f1636])).
% 5.69/1.10  fof(f3867,plain,(
% 5.69/1.10    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X0,X0)))) )),
% 5.69/1.10    inference(superposition,[],[f2062,f605])).
% 5.69/1.10  fof(f2062,plain,(
% 5.69/1.10    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 5.69/1.10    inference(backward_demodulation,[],[f50,f2059])).
% 5.69/1.10  fof(f2059,plain,(
% 5.69/1.10    ( ! [X45,X43,X44] : (k3_xboole_0(X43,k5_xboole_0(X44,k3_xboole_0(X44,k3_xboole_0(X43,X45)))) = k3_xboole_0(X44,k5_xboole_0(X43,k3_xboole_0(X43,X45)))) )),
% 5.69/1.10    inference(forward_demodulation,[],[f2058,f2053])).
% 5.69/1.10  fof(f2053,plain,(
% 5.69/1.10    ( ! [X41,X42,X40] : (k3_xboole_0(X41,k5_xboole_0(X40,k3_xboole_0(X40,X42))) = k3_xboole_0(X40,k3_xboole_0(X41,k5_xboole_0(X40,k3_xboole_0(X40,X42))))) )),
% 5.69/1.10    inference(forward_demodulation,[],[f2052,f48])).
% 5.69/1.10  fof(f2052,plain,(
% 5.69/1.10    ( ! [X41,X42,X40] : (k3_xboole_0(X40,k5_xboole_0(k3_xboole_0(X41,X40),k3_xboole_0(X41,k3_xboole_0(X40,X42)))) = k3_xboole_0(X41,k5_xboole_0(X40,k3_xboole_0(X40,X42)))) )),
% 5.69/1.10    inference(forward_demodulation,[],[f2051,f651])).
% 5.69/1.10  fof(f2051,plain,(
% 5.69/1.10    ( ! [X41,X42,X40] : (k3_xboole_0(X40,k5_xboole_0(k3_xboole_0(X41,X40),k3_xboole_0(X41,k3_xboole_0(X40,X42)))) = k3_xboole_0(X41,k5_xboole_0(X40,k3_xboole_0(X40,k3_xboole_0(X40,X42))))) )),
% 5.69/1.10    inference(forward_demodulation,[],[f2050,f763])).
% 5.69/1.10  fof(f763,plain,(
% 5.69/1.10    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k3_xboole_0(X0,X2)))) )),
% 5.69/1.10    inference(backward_demodulation,[],[f51,f718])).
% 5.69/1.10  fof(f718,plain,(
% 5.69/1.10    ( ! [X6,X4,X5] : (k3_xboole_0(X6,k3_xboole_0(X4,X5)) = k3_xboole_0(X4,k3_xboole_0(X6,k3_xboole_0(X4,X5)))) )),
% 5.69/1.10    inference(superposition,[],[f651,f79])).
% 5.69/1.10  fof(f51,plain,(
% 5.69/1.10    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X0,X2))))) )),
% 5.69/1.10    inference(forward_demodulation,[],[f43,f31])).
% 5.69/1.10  fof(f43,plain,(
% 5.69/1.10    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)))) )),
% 5.69/1.10    inference(definition_unfolding,[],[f33,f27,f27])).
% 5.69/1.10  fof(f33,plain,(
% 5.69/1.10    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 5.69/1.10    inference(cnf_transformation,[],[f11])).
% 5.69/1.10  fof(f11,axiom,(
% 5.69/1.10    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 5.69/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).
% 5.69/1.10  fof(f2050,plain,(
% 5.69/1.10    ( ! [X41,X42,X40] : (k3_xboole_0(X40,k5_xboole_0(k3_xboole_0(X41,X40),k3_xboole_0(X41,k3_xboole_0(X40,X42)))) = k5_xboole_0(k3_xboole_0(X41,X40),k3_xboole_0(X40,k3_xboole_0(X41,k3_xboole_0(X40,X42))))) )),
% 5.69/1.10    inference(forward_demodulation,[],[f1977,f31])).
% 5.69/1.10  fof(f1977,plain,(
% 5.69/1.10    ( ! [X41,X42,X40] : (k3_xboole_0(X40,k5_xboole_0(k3_xboole_0(X41,X40),k3_xboole_0(k3_xboole_0(X41,X40),X42))) = k5_xboole_0(k3_xboole_0(X41,X40),k3_xboole_0(X40,k3_xboole_0(k3_xboole_0(X41,X40),X42)))) )),
% 5.69/1.10    inference(superposition,[],[f48,f680])).
% 5.69/1.10  fof(f680,plain,(
% 5.69/1.10    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,k3_xboole_0(X2,X3))) )),
% 5.69/1.10    inference(backward_demodulation,[],[f675,f651])).
% 5.69/1.10  fof(f675,plain,(
% 5.69/1.10    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,k3_xboole_0(X2,k3_xboole_0(X2,X3)))) )),
% 5.69/1.10    inference(forward_demodulation,[],[f640,f24])).
% 5.69/1.10  fof(f640,plain,(
% 5.69/1.10    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,k3_xboole_0(k3_xboole_0(X2,X3),X2))) )),
% 5.69/1.10    inference(superposition,[],[f605,f79])).
% 5.69/1.10  fof(f2058,plain,(
% 5.69/1.10    ( ! [X45,X43,X44] : (k3_xboole_0(X43,k5_xboole_0(X44,k3_xboole_0(X44,k3_xboole_0(X43,X45)))) = k3_xboole_0(X43,k3_xboole_0(X44,k5_xboole_0(X43,k3_xboole_0(X43,X45))))) )),
% 5.69/1.10    inference(forward_demodulation,[],[f2057,f48])).
% 5.69/1.10  fof(f2057,plain,(
% 5.69/1.10    ( ! [X45,X43,X44] : (k3_xboole_0(X43,k5_xboole_0(k3_xboole_0(X44,X43),k3_xboole_0(X44,k3_xboole_0(X43,X45)))) = k3_xboole_0(X43,k5_xboole_0(X44,k3_xboole_0(X44,k3_xboole_0(X43,X45))))) )),
% 5.69/1.10    inference(forward_demodulation,[],[f2056,f48])).
% 5.69/1.10  fof(f2056,plain,(
% 5.69/1.10    ( ! [X45,X43,X44] : (k3_xboole_0(X43,k5_xboole_0(k3_xboole_0(X44,X43),k3_xboole_0(X44,k3_xboole_0(X43,X45)))) = k5_xboole_0(k3_xboole_0(X43,X44),k3_xboole_0(X43,k3_xboole_0(X44,k3_xboole_0(X43,X45))))) )),
% 5.69/1.10    inference(forward_demodulation,[],[f1978,f31])).
% 5.69/1.10  fof(f1978,plain,(
% 5.69/1.10    ( ! [X45,X43,X44] : (k3_xboole_0(X43,k5_xboole_0(k3_xboole_0(X44,X43),k3_xboole_0(k3_xboole_0(X44,X43),X45))) = k5_xboole_0(k3_xboole_0(X43,X44),k3_xboole_0(X43,k3_xboole_0(k3_xboole_0(X44,X43),X45)))) )),
% 5.69/1.10    inference(superposition,[],[f48,f661])).
% 5.69/1.10  fof(f661,plain,(
% 5.69/1.10    ( ! [X21,X20] : (k3_xboole_0(X20,X21) = k3_xboole_0(X20,k3_xboole_0(X21,X20))) )),
% 5.69/1.10    inference(superposition,[],[f134,f605])).
% 5.69/1.10  fof(f134,plain,(
% 5.69/1.10    ( ! [X6,X8,X7] : (k3_xboole_0(X8,k3_xboole_0(X6,X7)) = k3_xboole_0(k3_xboole_0(X7,X8),X6)) )),
% 5.69/1.10    inference(superposition,[],[f79,f24])).
% 5.69/1.10  fof(f50,plain,(
% 5.69/1.10    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(X0,X1)))))) )),
% 5.69/1.10    inference(forward_demodulation,[],[f49,f48])).
% 5.69/1.10  fof(f49,plain,(
% 5.69/1.10    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(X0,X1)))))) )),
% 5.69/1.10    inference(forward_demodulation,[],[f42,f31])).
% 5.69/1.10  fof(f42,plain,(
% 5.69/1.10    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,X1))))) )),
% 5.69/1.10    inference(definition_unfolding,[],[f32,f34,f34])).
% 5.69/1.10  fof(f32,plain,(
% 5.69/1.10    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 5.69/1.10    inference(cnf_transformation,[],[f8])).
% 5.69/1.10  fof(f8,axiom,(
% 5.69/1.10    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 5.69/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 5.69/1.10  fof(f3127,plain,(
% 5.69/1.10    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))))),
% 5.69/1.10    inference(forward_demodulation,[],[f3126,f48])).
% 5.69/1.10  fof(f3126,plain,(
% 5.69/1.10    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))))),
% 5.69/1.10    inference(forward_demodulation,[],[f3125,f29])).
% 5.69/1.10  fof(f3125,plain,(
% 5.69/1.10    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))),
% 5.69/1.10    inference(superposition,[],[f47,f29])).
% 5.69/1.10  fof(f47,plain,(
% 5.69/1.10    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))),
% 5.69/1.10    inference(backward_demodulation,[],[f45,f31])).
% 5.69/1.10  fof(f45,plain,(
% 5.69/1.10    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),
% 5.69/1.10    inference(forward_demodulation,[],[f44,f24])).
% 5.69/1.10  fof(f44,plain,(
% 5.69/1.10    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),
% 5.69/1.10    inference(backward_demodulation,[],[f36,f24])).
% 5.69/1.10  fof(f36,plain,(
% 5.69/1.10    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1)))),
% 5.69/1.10    inference(definition_unfolding,[],[f20,f27,f34])).
% 5.69/1.10  fof(f20,plain,(
% 5.69/1.10    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 5.69/1.10    inference(cnf_transformation,[],[f19])).
% 5.69/1.10  fof(f19,plain,(
% 5.69/1.10    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 5.69/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 5.69/1.10  fof(f18,plain,(
% 5.69/1.10    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 5.69/1.10    introduced(choice_axiom,[])).
% 5.69/1.10  fof(f17,plain,(
% 5.69/1.10    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.69/1.10    inference(ennf_transformation,[],[f15])).
% 5.69/1.10  fof(f15,negated_conjecture,(
% 5.69/1.10    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.69/1.10    inference(negated_conjecture,[],[f14])).
% 5.69/1.10  fof(f14,conjecture,(
% 5.69/1.10    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.69/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 5.69/1.10  % SZS output end Proof for theBenchmark
% 5.69/1.10  % (1659)------------------------------
% 5.69/1.10  % (1659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.69/1.10  % (1659)Termination reason: Refutation
% 5.69/1.10  
% 5.69/1.10  % (1659)Memory used [KB]: 12153
% 5.69/1.10  % (1659)Time elapsed: 0.675 s
% 5.69/1.10  % (1659)------------------------------
% 5.69/1.10  % (1659)------------------------------
% 5.69/1.10  % (1657)Success in time 0.743 s
%------------------------------------------------------------------------------
