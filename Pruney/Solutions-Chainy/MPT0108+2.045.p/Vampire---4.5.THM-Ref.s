%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:24 EST 2020

% Result     : Theorem 47.51s
% Output     : Refutation 47.51s
% Verified   : 
% Statistics : Number of formulae       :  170 (4289 expanded)
%              Number of leaves         :   13 (1483 expanded)
%              Depth                    :   36
%              Number of atoms          :  181 (4300 expanded)
%              Number of equality atoms :  180 (4299 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    9 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32445,plain,(
    $false ),
    inference(subsumption_resolution,[],[f32444,f248])).

fof(f248,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X6,X7))) ),
    inference(forward_demodulation,[],[f241,f20])).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f241,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X6,X7))) = k4_xboole_0(k4_xboole_0(X6,k1_xboole_0),X7) ),
    inference(superposition,[],[f36,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f59,f64])).

fof(f64,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2) ),
    inference(forward_demodulation,[],[f57,f20])).

fof(f57,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f31,f34])).

fof(f34,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f59,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f31,f33])).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f21,f26])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f29,f26,f26])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f32444,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) != k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f32441,f17775])).

fof(f17775,plain,(
    ! [X8,X9] : k5_xboole_0(k4_xboole_0(X9,X8),k4_xboole_0(X8,X9)) = k5_xboole_0(X9,X8) ),
    inference(forward_demodulation,[],[f17751,f66])).

fof(f66,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f55,f65])).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f31,f20])).

fof(f17751,plain,(
    ! [X8,X9] : k5_xboole_0(k4_xboole_0(X9,X8),k4_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X8,k1_xboole_0)) ),
    inference(superposition,[],[f1968,f64])).

fof(f1968,plain,(
    ! [X14,X12,X13] : k5_xboole_0(k4_xboole_0(X12,X13),X14) = k5_xboole_0(X12,k5_xboole_0(X13,k5_xboole_0(k4_xboole_0(X13,X12),X14))) ),
    inference(forward_demodulation,[],[f1897,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1897,plain,(
    ! [X14,X12,X13] : k5_xboole_0(k4_xboole_0(X12,X13),X14) = k5_xboole_0(X12,k5_xboole_0(k5_xboole_0(X13,k4_xboole_0(X13,X12)),X14)) ),
    inference(superposition,[],[f62,f1623])).

fof(f1623,plain,(
    ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f74,f1622])).

fof(f1622,plain,(
    ! [X43,X42] : k4_xboole_0(X42,X43) = k4_xboole_0(X42,k4_xboole_0(X43,k4_xboole_0(X43,X42))) ),
    inference(forward_demodulation,[],[f1621,f248])).

fof(f1621,plain,(
    ! [X43,X42] : k4_xboole_0(X42,k4_xboole_0(X43,k4_xboole_0(X43,X42))) = k4_xboole_0(X42,k4_xboole_0(X42,k4_xboole_0(X42,X43))) ),
    inference(forward_demodulation,[],[f1465,f20])).

fof(f1465,plain,(
    ! [X43,X42] : k4_xboole_0(X42,k4_xboole_0(X43,k4_xboole_0(X43,X42))) = k4_xboole_0(X42,k4_xboole_0(X42,k4_xboole_0(k4_xboole_0(X42,X43),k1_xboole_0))) ),
    inference(superposition,[],[f89,f20])).

fof(f89,plain,(
    ! [X6,X7,X5] : k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k4_xboole_0(X5,X6),X7))) = k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X6,X5))),X7) ),
    inference(superposition,[],[f36,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f26,f26])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f74,plain,(
    ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))) ),
    inference(superposition,[],[f31,f35])).

fof(f62,plain,(
    ! [X2,X3,X1] : k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)) = k5_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(superposition,[],[f28,f31])).

fof(f32441,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) != k4_xboole_0(k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f15995,f32439])).

fof(f32439,plain,(
    ! [X331,X332,X330] : k4_xboole_0(k5_xboole_0(X330,k4_xboole_0(X331,X330)),k4_xboole_0(X330,k4_xboole_0(X330,X332))) = k5_xboole_0(k4_xboole_0(X330,X332),k4_xboole_0(X331,X330)) ),
    inference(backward_demodulation,[],[f32332,f32438])).

fof(f32438,plain,(
    ! [X68,X66,X67] : k5_xboole_0(k4_xboole_0(X66,X68),k4_xboole_0(X67,X66)) = k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),k4_xboole_0(X68,k4_xboole_0(X67,X66))) ),
    inference(forward_demodulation,[],[f32437,f12686])).

fof(f12686,plain,(
    ! [X6,X5] : k4_xboole_0(X6,X5) = k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),X5) ),
    inference(backward_demodulation,[],[f291,f12637])).

fof(f12637,plain,(
    ! [X10,X9] : k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9 ),
    inference(superposition,[],[f8712,f8712])).

fof(f8712,plain,(
    ! [X10,X9] : k5_xboole_0(X10,k5_xboole_0(X9,X10)) = X9 ),
    inference(forward_demodulation,[],[f8690,f66])).

fof(f8690,plain,(
    ! [X10,X9] : k5_xboole_0(X10,k5_xboole_0(X9,X10)) = k5_xboole_0(X9,k1_xboole_0) ),
    inference(superposition,[],[f4351,f81])).

fof(f81,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) ),
    inference(superposition,[],[f64,f28])).

fof(f4351,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f83,f4349])).

fof(f4349,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,X3) = X3 ),
    inference(forward_demodulation,[],[f4321,f66])).

fof(f4321,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f83,f64])).

fof(f83,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f28,f64])).

fof(f291,plain,(
    ! [X6,X5] : k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),X5) = k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),X5) ),
    inference(forward_demodulation,[],[f278,f20])).

fof(f278,plain,(
    ! [X6,X5] : k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),X5) = k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,k1_xboole_0)) ),
    inference(superposition,[],[f73,f34])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f31,f35])).

fof(f32437,plain,(
    ! [X68,X66,X67] : k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),k4_xboole_0(X68,k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),X66))) = k5_xboole_0(k4_xboole_0(X66,X68),k4_xboole_0(X67,X66)) ),
    inference(forward_demodulation,[],[f32436,f12712])).

fof(f12712,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(X7,k5_xboole_0(X8,k5_xboole_0(X7,X9))) ),
    inference(forward_demodulation,[],[f12647,f28])).

fof(f12647,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(X7,k5_xboole_0(k5_xboole_0(X8,X7),X9)) ),
    inference(superposition,[],[f28,f8712])).

fof(f32436,plain,(
    ! [X68,X66,X67] : k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),k4_xboole_0(X68,k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),X66))) = k5_xboole_0(X66,k5_xboole_0(k4_xboole_0(X66,X68),k5_xboole_0(X66,k4_xboole_0(X67,X66)))) ),
    inference(forward_demodulation,[],[f32435,f17911])).

fof(f17911,plain,(
    ! [X74,X72,X73] : k5_xboole_0(X74,k4_xboole_0(X72,k4_xboole_0(X72,X73))) = k5_xboole_0(X72,k5_xboole_0(k4_xboole_0(X72,X73),X74)) ),
    inference(forward_demodulation,[],[f17910,f4351])).

fof(f17910,plain,(
    ! [X74,X72,X73] : k5_xboole_0(X74,k4_xboole_0(X72,k4_xboole_0(X72,X73))) = k5_xboole_0(X72,k5_xboole_0(X72,k5_xboole_0(X72,k5_xboole_0(k4_xboole_0(X72,X73),X74)))) ),
    inference(forward_demodulation,[],[f17909,f8692])).

fof(f8692,plain,(
    ! [X14,X15,X16] : k5_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X16) = k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X14,X15),X16)) ),
    inference(superposition,[],[f4351,f62])).

fof(f17909,plain,(
    ! [X74,X72,X73] : k5_xboole_0(X74,k4_xboole_0(X72,k4_xboole_0(X72,X73))) = k5_xboole_0(X72,k5_xboole_0(X72,k5_xboole_0(k4_xboole_0(X72,k4_xboole_0(X72,X73)),X74))) ),
    inference(forward_demodulation,[],[f17908,f8692])).

fof(f17908,plain,(
    ! [X74,X72,X73] : k5_xboole_0(X72,k5_xboole_0(k4_xboole_0(X72,k4_xboole_0(X72,k4_xboole_0(X72,X73))),X74)) = k5_xboole_0(X74,k4_xboole_0(X72,k4_xboole_0(X72,X73))) ),
    inference(forward_demodulation,[],[f17907,f4349])).

fof(f17907,plain,(
    ! [X74,X72,X73] : k5_xboole_0(X72,k5_xboole_0(k4_xboole_0(X72,k4_xboole_0(X72,k4_xboole_0(X72,X73))),X74)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X74,k4_xboole_0(X72,k4_xboole_0(X72,X73)))) ),
    inference(forward_demodulation,[],[f17794,f15029])).

fof(f15029,plain,(
    ! [X24,X23,X25] : k5_xboole_0(X23,k5_xboole_0(X24,X25)) = k5_xboole_0(X25,k5_xboole_0(X23,X24)) ),
    inference(superposition,[],[f12645,f28])).

fof(f12645,plain,(
    ! [X2,X3] : k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2) ),
    inference(superposition,[],[f4351,f8712])).

fof(f17794,plain,(
    ! [X74,X72,X73] : k5_xboole_0(X72,k5_xboole_0(k4_xboole_0(X72,k4_xboole_0(X72,k4_xboole_0(X72,X73))),X74)) = k5_xboole_0(k4_xboole_0(X72,k4_xboole_0(X72,X73)),k5_xboole_0(k1_xboole_0,X74)) ),
    inference(superposition,[],[f1994,f780])).

fof(f780,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(forward_demodulation,[],[f779,f65])).

fof(f779,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X1) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(forward_demodulation,[],[f671,f20])).

fof(f671,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f93,f65])).

fof(f93,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[],[f36,f35])).

fof(f1994,plain,(
    ! [X59,X60,X58] : k5_xboole_0(X59,k5_xboole_0(k4_xboole_0(X59,X58),X60)) = k5_xboole_0(X58,k5_xboole_0(k4_xboole_0(X58,X59),X60)) ),
    inference(forward_demodulation,[],[f1993,f1622])).

fof(f1993,plain,(
    ! [X59,X60,X58] : k5_xboole_0(X59,k5_xboole_0(k4_xboole_0(X59,X58),X60)) = k5_xboole_0(X58,k5_xboole_0(k4_xboole_0(X58,k4_xboole_0(X59,k4_xboole_0(X59,X58))),X60)) ),
    inference(forward_demodulation,[],[f1992,f1881])).

fof(f1881,plain,(
    ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X3,k4_xboole_0(X3,X2)) ),
    inference(superposition,[],[f1623,f35])).

fof(f1992,plain,(
    ! [X59,X60,X58] : k5_xboole_0(X58,k5_xboole_0(k4_xboole_0(X58,k5_xboole_0(X59,k4_xboole_0(X59,X58))),X60)) = k5_xboole_0(X59,k5_xboole_0(k4_xboole_0(X59,X58),X60)) ),
    inference(forward_demodulation,[],[f1911,f28])).

fof(f1911,plain,(
    ! [X59,X60,X58] : k5_xboole_0(X58,k5_xboole_0(k4_xboole_0(X58,k5_xboole_0(X59,k4_xboole_0(X59,X58))),X60)) = k5_xboole_0(k5_xboole_0(X59,k4_xboole_0(X59,X58)),X60) ),
    inference(superposition,[],[f62,f1623])).

fof(f32435,plain,(
    ! [X68,X66,X67] : k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),k4_xboole_0(X68,k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),X66))) = k5_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),k4_xboole_0(X66,k4_xboole_0(X66,X68))) ),
    inference(forward_demodulation,[],[f32434,f1938])).

fof(f1938,plain,(
    ! [X10,X11,X9] : k4_xboole_0(X9,k4_xboole_0(X9,X11)) = k4_xboole_0(X9,k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),X11)) ),
    inference(backward_demodulation,[],[f1018,f1881])).

fof(f1018,plain,(
    ! [X10,X11,X9] : k4_xboole_0(X9,k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),X11)) = k5_xboole_0(X9,k4_xboole_0(X9,X11)) ),
    inference(superposition,[],[f31,f114])).

fof(f114,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X4))) = k4_xboole_0(X2,X4) ),
    inference(forward_demodulation,[],[f88,f20])).

fof(f88,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X4))) = k4_xboole_0(k4_xboole_0(X2,k1_xboole_0),X4) ),
    inference(superposition,[],[f36,f34])).

fof(f32434,plain,(
    ! [X68,X66,X67] : k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),k4_xboole_0(X68,k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),X66))) = k5_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),k4_xboole_0(X66,k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),X68))) ),
    inference(forward_demodulation,[],[f31925,f248])).

fof(f31925,plain,(
    ! [X68,X66,X67] : k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),k4_xboole_0(X68,k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),X66))) = k5_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),k4_xboole_0(X66,k4_xboole_0(X66,k4_xboole_0(X66,k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),X68))))) ),
    inference(superposition,[],[f2421,f1938])).

fof(f2421,plain,(
    ! [X14,X12,X13] : k5_xboole_0(X12,k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X12,k4_xboole_0(X12,X13))))) = k4_xboole_0(X12,k4_xboole_0(X13,k4_xboole_0(X12,X14))) ),
    inference(superposition,[],[f31,f2107])).

fof(f2107,plain,(
    ! [X10,X8,X9] : k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9)))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X8,X10)))) ),
    inference(backward_demodulation,[],[f128,f2106])).

fof(f2106,plain,(
    ! [X80,X81,X82] : k4_xboole_0(X80,k4_xboole_0(X81,X82)) = k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(X80,X82)))) ),
    inference(forward_demodulation,[],[f2105,f66])).

fof(f2105,plain,(
    ! [X80,X81,X82] : k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(X80,X82)))) = k5_xboole_0(k4_xboole_0(X80,k4_xboole_0(X81,X82)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f2104,f65])).

fof(f2104,plain,(
    ! [X80,X81,X82] : k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(X80,X82)))) = k5_xboole_0(k4_xboole_0(X80,k4_xboole_0(X81,X82)),k4_xboole_0(X80,X80)) ),
    inference(forward_demodulation,[],[f2103,f20])).

fof(f2103,plain,(
    ! [X80,X81,X82] : k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(X80,X82)))) = k5_xboole_0(k4_xboole_0(X80,k4_xboole_0(X81,X82)),k4_xboole_0(X80,k4_xboole_0(X80,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f2102,f65])).

fof(f2102,plain,(
    ! [X80,X81,X82] : k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(X80,X82)))) = k5_xboole_0(k4_xboole_0(X80,k4_xboole_0(X81,X82)),k4_xboole_0(X80,k4_xboole_0(X80,k4_xboole_0(k4_xboole_0(X81,X82),k4_xboole_0(X81,X82))))) ),
    inference(forward_demodulation,[],[f2101,f1669])).

fof(f1669,plain,(
    ! [X39,X37,X38,X40] : k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(k4_xboole_0(X38,X39),X40))) = k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X38,k4_xboole_0(X38,k4_xboole_0(k4_xboole_0(X37,X39),X40))))) ),
    inference(backward_demodulation,[],[f1552,f1664])).

fof(f1664,plain,(
    ! [X24,X23,X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X22,X23),X24))) = k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X22,X23),X24))))))) ),
    inference(backward_demodulation,[],[f235,f1624])).

fof(f1624,plain,(
    ! [X6,X7,X5] : k4_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k4_xboole_0(X5,X6),X7))) ),
    inference(backward_demodulation,[],[f89,f1622])).

fof(f235,plain,(
    ! [X24,X23,X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(k4_xboole_0(X22,X23),X24))))) = k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X22,X23),X24))))))) ),
    inference(forward_demodulation,[],[f234,f36])).

fof(f234,plain,(
    ! [X24,X23,X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(k4_xboole_0(X22,X23),X24))))) = k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,X23))),X24))))) ),
    inference(forward_demodulation,[],[f233,f36])).

fof(f233,plain,(
    ! [X24,X23,X21,X22] : k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,X23))),X24))) = k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(k4_xboole_0(X22,X23),X24))))) ),
    inference(forward_demodulation,[],[f232,f218])).

fof(f218,plain,(
    ! [X14,X15,X13,X16] : k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,X15)))),X16))) = k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16))))) ),
    inference(backward_demodulation,[],[f123,f158])).

fof(f158,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5)))) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5)))))) ),
    inference(superposition,[],[f38,f36])).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    inference(forward_demodulation,[],[f37,f36])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f30,f26,f26,f26,f26])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f123,plain,(
    ! [X14,X15,X13,X16] : k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,X15)))),X16))) = k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(X15,X16))))))) ),
    inference(forward_demodulation,[],[f122,f36])).

fof(f122,plain,(
    ! [X14,X15,X13,X16] : k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,X15)))),X16))) = k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X15,X16))))) ),
    inference(forward_demodulation,[],[f121,f36])).

fof(f121,plain,(
    ! [X14,X15,X13,X16] : k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X15,X16))) = k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,X15)))),X16))) ),
    inference(forward_demodulation,[],[f120,f36])).

fof(f120,plain,(
    ! [X14,X15,X13,X16] : k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X15,X16))) = k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,X15)))))),X16) ),
    inference(forward_demodulation,[],[f92,f36])).

fof(f92,plain,(
    ! [X14,X15,X13,X16] : k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X15,X16))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,X15)))),X16) ),
    inference(superposition,[],[f36,f36])).

fof(f232,plain,(
    ! [X24,X23,X21,X22] : k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,X23))),X24))) = k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,X23))))),X24))) ),
    inference(forward_demodulation,[],[f231,f36])).

fof(f231,plain,(
    ! [X24,X23,X21,X22] : k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,X23))),X24))) = k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,X23))))))),X24) ),
    inference(forward_demodulation,[],[f162,f36])).

fof(f162,plain,(
    ! [X24,X23,X21,X22] : k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,X23))),X24))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,X23))))),X24) ),
    inference(superposition,[],[f36,f38])).

fof(f1552,plain,(
    ! [X39,X37,X38,X40] : k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,X38)),k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X38,k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(k4_xboole_0(X38,X39),X40))))))) = k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X38,k4_xboole_0(X38,k4_xboole_0(k4_xboole_0(X37,X39),X40))))) ),
    inference(forward_demodulation,[],[f1551,f1548])).

fof(f1548,plain,(
    ! [X35,X33,X36,X34] : k4_xboole_0(X33,k4_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(k4_xboole_0(X33,X35),X36))))) = k4_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X33,k4_xboole_0(X33,X34))))))),X36) ),
    inference(forward_demodulation,[],[f1547,f36])).

fof(f1547,plain,(
    ! [X35,X33,X36,X34] : k4_xboole_0(k4_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,X34)),k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X33,k4_xboole_0(X33,X34))))),X36) = k4_xboole_0(X33,k4_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(k4_xboole_0(X33,X35),X36))))) ),
    inference(forward_demodulation,[],[f1546,f38])).

fof(f1546,plain,(
    ! [X35,X33,X36,X34] : k4_xboole_0(k4_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,X34)),k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X33,k4_xboole_0(X33,X34))))),X36) = k4_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,X34)),k4_xboole_0(X33,k4_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(k4_xboole_0(X33,X35),X36))))) ),
    inference(forward_demodulation,[],[f1545,f248])).

fof(f1545,plain,(
    ! [X35,X33,X36,X34] : k4_xboole_0(k4_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,X34)),k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X33,k4_xboole_0(X33,X34))))),X36) = k4_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,X34)),k4_xboole_0(X33,k4_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(k4_xboole_0(X33,X35),X36))))))) ),
    inference(forward_demodulation,[],[f1544,f36])).

fof(f1544,plain,(
    ! [X35,X33,X36,X34] : k4_xboole_0(k4_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,X34)),k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X33,k4_xboole_0(X33,X34))))),X36) = k4_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,X34)),k4_xboole_0(X33,k4_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(k4_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(X33,X35))),X36))))) ),
    inference(forward_demodulation,[],[f1415,f36])).

fof(f1415,plain,(
    ! [X35,X33,X36,X34] : k4_xboole_0(k4_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,X34)),k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X33,k4_xboole_0(X33,X34))))),X36) = k4_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,X34)),k4_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,X34)),k4_xboole_0(k4_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(X33,X35))),X36))) ),
    inference(superposition,[],[f89,f93])).

fof(f1551,plain,(
    ! [X39,X37,X38,X40] : k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,X38)),k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X38,k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(k4_xboole_0(X38,X39),X40))))))) = k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X38,k4_xboole_0(X39,k4_xboole_0(X39,k4_xboole_0(X37,k4_xboole_0(X37,X38))))))),X40) ),
    inference(forward_demodulation,[],[f1550,f36])).

fof(f1550,plain,(
    ! [X39,X37,X38,X40] : k4_xboole_0(k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,X38)),k4_xboole_0(X39,k4_xboole_0(X39,k4_xboole_0(X37,k4_xboole_0(X37,X38))))),X40) = k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,X38)),k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X38,k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(k4_xboole_0(X38,X39),X40))))))) ),
    inference(forward_demodulation,[],[f1549,f36])).

fof(f1549,plain,(
    ! [X39,X37,X38,X40] : k4_xboole_0(k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,X38)),k4_xboole_0(X39,k4_xboole_0(X39,k4_xboole_0(X37,k4_xboole_0(X37,X38))))),X40) = k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,X38)),k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X38,k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X38,X39))),X40))))) ),
    inference(forward_demodulation,[],[f1416,f36])).

fof(f1416,plain,(
    ! [X39,X37,X38,X40] : k4_xboole_0(k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,X38)),k4_xboole_0(X39,k4_xboole_0(X39,k4_xboole_0(X37,k4_xboole_0(X37,X38))))),X40) = k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,X38)),k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,X38)),k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X38,X39))),X40))) ),
    inference(superposition,[],[f89,f36])).

fof(f2101,plain,(
    ! [X80,X81,X82] : k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(X80,X82)))) = k5_xboole_0(k4_xboole_0(X80,k4_xboole_0(X81,X82)),k4_xboole_0(X80,k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(k4_xboole_0(X80,X82),k4_xboole_0(X81,X82))))))) ),
    inference(forward_demodulation,[],[f2093,f36])).

fof(f2093,plain,(
    ! [X80,X81,X82] : k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(X80,X82)))) = k5_xboole_0(k4_xboole_0(X80,k4_xboole_0(X81,X82)),k4_xboole_0(X80,k4_xboole_0(X80,k4_xboole_0(k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(X80,X82))),k4_xboole_0(X81,X82))))) ),
    inference(backward_demodulation,[],[f880,f2092])).

fof(f2092,plain,(
    ! [X21,X19,X20] : k4_xboole_0(X19,k4_xboole_0(X19,k4_xboole_0(X21,X20))) = k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X19,X21)) ),
    inference(forward_demodulation,[],[f2091,f809])).

fof(f809,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X4,X5),X3)) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,X5))) ),
    inference(forward_demodulation,[],[f689,f36])).

fof(f689,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X3)),X5) = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X4,X5),X3)) ),
    inference(superposition,[],[f93,f35])).

fof(f2091,plain,(
    ! [X21,X19,X20] : k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(k4_xboole_0(X19,X20),X21)) = k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X19,X21)) ),
    inference(forward_demodulation,[],[f2090,f2086])).

fof(f2086,plain,(
    ! [X17,X18,X16] : k4_xboole_0(k4_xboole_0(X16,X17),X18) = k4_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X16,X18))) ),
    inference(forward_demodulation,[],[f2056,f20])).

fof(f2056,plain,(
    ! [X17,X18,X16] : k4_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X16,X18))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X16,X17),k1_xboole_0),X18) ),
    inference(superposition,[],[f36,f1677])).

fof(f1677,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(forward_demodulation,[],[f1627,f64])).

fof(f1627,plain,(
    ! [X2,X1] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) ),
    inference(backward_demodulation,[],[f276,f1622])).

fof(f276,plain,(
    ! [X2,X1] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) ),
    inference(superposition,[],[f73,f35])).

fof(f2090,plain,(
    ! [X21,X19,X20] : k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(k4_xboole_0(X19,X20),X21)) = k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X19,k4_xboole_0(X19,X21)))) ),
    inference(forward_demodulation,[],[f2089,f20])).

fof(f2089,plain,(
    ! [X21,X19,X20] : k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X19,k4_xboole_0(X19,X21)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X19,X20),k1_xboole_0),k4_xboole_0(k4_xboole_0(X19,X20),X21)) ),
    inference(forward_demodulation,[],[f2088,f1624])).

fof(f2088,plain,(
    ! [X21,X19,X20] : k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X19,k4_xboole_0(X19,X21)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X19,X20),k1_xboole_0),k4_xboole_0(X19,k4_xboole_0(X19,k4_xboole_0(k4_xboole_0(X19,X20),X21)))) ),
    inference(forward_demodulation,[],[f2087,f36])).

fof(f2087,plain,(
    ! [X21,X19,X20] : k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X19,k4_xboole_0(X19,X21)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X19,X20),k1_xboole_0),k4_xboole_0(k4_xboole_0(X19,k4_xboole_0(X19,k4_xboole_0(X19,X20))),X21)) ),
    inference(forward_demodulation,[],[f2057,f93])).

fof(f2057,plain,(
    ! [X21,X19,X20] : k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X19,k4_xboole_0(X19,X21)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X19,X20),k1_xboole_0),k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X19,X21)))) ),
    inference(superposition,[],[f38,f1677])).

fof(f880,plain,(
    ! [X80,X81,X82] : k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(X80,X82)))) = k5_xboole_0(k4_xboole_0(X80,k4_xboole_0(X81,X82)),k4_xboole_0(k4_xboole_0(X80,k4_xboole_0(X81,X82)),k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(X80,X82)))))) ),
    inference(forward_demodulation,[],[f734,f36])).

fof(f734,plain,(
    ! [X80,X81,X82] : k4_xboole_0(X80,k4_xboole_0(k4_xboole_0(X81,k4_xboole_0(X81,X80)),X82)) = k5_xboole_0(k4_xboole_0(X80,k4_xboole_0(X81,X82)),k4_xboole_0(k4_xboole_0(X80,k4_xboole_0(X81,X82)),k4_xboole_0(X80,k4_xboole_0(k4_xboole_0(X81,k4_xboole_0(X81,X80)),X82)))) ),
    inference(superposition,[],[f74,f93])).

fof(f128,plain,(
    ! [X10,X8,X9] : k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9)))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10)))))) ),
    inference(forward_demodulation,[],[f98,f36])).

fof(f98,plain,(
    ! [X10,X8,X9] : k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9)))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10)))) ),
    inference(superposition,[],[f36,f35])).

fof(f32332,plain,(
    ! [X331,X332,X330] : k4_xboole_0(k5_xboole_0(X330,k4_xboole_0(X331,X330)),k4_xboole_0(X332,k4_xboole_0(X331,X330))) = k4_xboole_0(k5_xboole_0(X330,k4_xboole_0(X331,X330)),k4_xboole_0(X330,k4_xboole_0(X330,X332))) ),
    inference(forward_demodulation,[],[f32331,f1938])).

fof(f32331,plain,(
    ! [X331,X332,X330] : k4_xboole_0(k5_xboole_0(X330,k4_xboole_0(X331,X330)),k4_xboole_0(X330,k4_xboole_0(k5_xboole_0(X330,k4_xboole_0(X331,X330)),X332))) = k4_xboole_0(k5_xboole_0(X330,k4_xboole_0(X331,X330)),k4_xboole_0(X332,k4_xboole_0(X331,X330))) ),
    inference(forward_demodulation,[],[f31870,f857])).

fof(f857,plain,(
    ! [X8,X7,X9] : k4_xboole_0(X7,k4_xboole_0(X8,X9)) = k5_xboole_0(X7,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X7,X9)))) ),
    inference(forward_demodulation,[],[f716,f36])).

fof(f716,plain,(
    ! [X8,X7,X9] : k4_xboole_0(X7,k4_xboole_0(X8,X9)) = k5_xboole_0(X7,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),X9)) ),
    inference(superposition,[],[f31,f93])).

fof(f31870,plain,(
    ! [X331,X332,X330] : k4_xboole_0(k5_xboole_0(X330,k4_xboole_0(X331,X330)),k4_xboole_0(X330,k4_xboole_0(k5_xboole_0(X330,k4_xboole_0(X331,X330)),X332))) = k5_xboole_0(k5_xboole_0(X330,k4_xboole_0(X331,X330)),k4_xboole_0(X332,k4_xboole_0(X332,k4_xboole_0(k5_xboole_0(X330,k4_xboole_0(X331,X330)),k4_xboole_0(X331,X330))))) ),
    inference(superposition,[],[f2421,f12686])).

fof(f15995,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))) ),
    inference(unit_resulting_resolution,[],[f32,f3479])).

fof(f3479,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,X0) != k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
      | X0 = X1 ) ),
    inference(forward_demodulation,[],[f3478,f20])).

fof(f3478,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_xboole_0) = X1
      | k4_xboole_0(X1,X0) != k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) ),
    inference(forward_demodulation,[],[f3477,f65])).

fof(f3477,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,X0) != k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
      | k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X1 ) ),
    inference(forward_demodulation,[],[f3476,f20])).

fof(f3476,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) != k4_xboole_0(X1,k4_xboole_0(X0,k1_xboole_0))
      | k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X1 ) ),
    inference(forward_demodulation,[],[f3475,f65])).

fof(f3475,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) != k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X0)))
      | k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X1 ) ),
    inference(forward_demodulation,[],[f3388,f1881])).

fof(f3388,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X0))) != k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))
      | k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X1 ) ),
    inference(superposition,[],[f100,f1623])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) != k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(superposition,[],[f27,f36])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f32,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f19,f24,f26])).

fof(f19,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:51:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (23330)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (23335)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (23344)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.28/0.53  % (23338)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.28/0.53  % (23351)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.28/0.53  % (23334)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.28/0.54  % (23332)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.28/0.54  % (23346)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.28/0.54  % (23333)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.28/0.54  % (23355)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.28/0.54  % (23331)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.54  % (23343)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.28/0.54  % (23341)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.54  % (23331)Refutation not found, incomplete strategy% (23331)------------------------------
% 1.28/0.54  % (23331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (23331)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (23331)Memory used [KB]: 10618
% 1.28/0.54  % (23331)Time elapsed: 0.134 s
% 1.28/0.54  % (23331)------------------------------
% 1.28/0.54  % (23331)------------------------------
% 1.28/0.54  % (23356)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.28/0.54  % (23353)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.28/0.54  % (23342)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.42/0.55  % (23347)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.42/0.55  % (23337)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.42/0.55  % (23348)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.42/0.55  % (23339)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.42/0.55  % (23340)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.42/0.55  % (23354)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.42/0.55  % (23345)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.42/0.55  % (23358)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.42/0.55  % (23349)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.42/0.55  % (23346)Refutation not found, incomplete strategy% (23346)------------------------------
% 1.42/0.55  % (23346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (23346)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (23346)Memory used [KB]: 10618
% 1.42/0.55  % (23346)Time elapsed: 0.146 s
% 1.42/0.55  % (23346)------------------------------
% 1.42/0.55  % (23346)------------------------------
% 1.42/0.56  % (23351)Refutation not found, incomplete strategy% (23351)------------------------------
% 1.42/0.56  % (23351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (23351)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (23351)Memory used [KB]: 10618
% 1.42/0.56  % (23351)Time elapsed: 0.151 s
% 1.42/0.56  % (23351)------------------------------
% 1.42/0.56  % (23351)------------------------------
% 1.42/0.56  % (23357)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.42/0.56  % (23329)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.42/0.56  % (23329)Refutation not found, incomplete strategy% (23329)------------------------------
% 1.42/0.56  % (23329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (23329)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (23329)Memory used [KB]: 1663
% 1.42/0.56  % (23329)Time elapsed: 0.087 s
% 1.42/0.56  % (23329)------------------------------
% 1.42/0.56  % (23329)------------------------------
% 1.42/0.57  % (23350)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.42/0.57  % (23350)Refutation not found, incomplete strategy% (23350)------------------------------
% 1.42/0.57  % (23350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (23350)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (23350)Memory used [KB]: 1663
% 1.42/0.57  % (23350)Time elapsed: 0.160 s
% 1.42/0.57  % (23350)------------------------------
% 1.42/0.57  % (23350)------------------------------
% 1.42/0.57  % (23352)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.42/0.57  % (23349)Refutation not found, incomplete strategy% (23349)------------------------------
% 1.42/0.57  % (23349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (23349)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (23349)Memory used [KB]: 10618
% 1.42/0.57  % (23349)Time elapsed: 0.159 s
% 1.42/0.57  % (23349)------------------------------
% 1.42/0.57  % (23349)------------------------------
% 1.42/0.57  % (23352)Refutation not found, incomplete strategy% (23352)------------------------------
% 1.42/0.57  % (23352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (23352)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (23352)Memory used [KB]: 1663
% 1.42/0.57  % (23352)Time elapsed: 0.088 s
% 1.42/0.57  % (23352)------------------------------
% 1.42/0.57  % (23352)------------------------------
% 1.42/0.57  % (23336)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.42/0.57  % (23337)Refutation not found, incomplete strategy% (23337)------------------------------
% 1.42/0.57  % (23337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (23337)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (23337)Memory used [KB]: 10618
% 1.42/0.57  % (23337)Time elapsed: 0.168 s
% 1.42/0.57  % (23337)------------------------------
% 1.42/0.57  % (23337)------------------------------
% 2.26/0.70  % (23368)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.26/0.71  % (23364)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.26/0.71  % (23363)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.26/0.74  % (23367)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.26/0.74  % (23362)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.26/0.74  % (23362)Refutation not found, incomplete strategy% (23362)------------------------------
% 2.26/0.74  % (23362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.74  % (23362)Termination reason: Refutation not found, incomplete strategy
% 2.26/0.74  
% 2.26/0.74  % (23362)Memory used [KB]: 6140
% 2.26/0.74  % (23362)Time elapsed: 0.158 s
% 2.26/0.74  % (23362)------------------------------
% 2.26/0.74  % (23362)------------------------------
% 2.26/0.75  % (23365)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.85/0.78  % (23366)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.85/0.80  % (23369)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 3.13/0.82  % (23334)Time limit reached!
% 3.13/0.82  % (23334)------------------------------
% 3.13/0.82  % (23334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.13/0.82  % (23334)Termination reason: Time limit
% 3.13/0.82  % (23334)Termination phase: Saturation
% 3.13/0.82  
% 3.13/0.82  % (23334)Memory used [KB]: 8827
% 3.13/0.82  % (23334)Time elapsed: 0.417 s
% 3.13/0.82  % (23334)------------------------------
% 3.13/0.82  % (23334)------------------------------
% 3.30/0.87  % (23395)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 3.75/0.94  % (23339)Time limit reached!
% 3.75/0.94  % (23339)------------------------------
% 3.75/0.94  % (23339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.75/0.94  % (23339)Termination reason: Time limit
% 3.75/0.94  % (23339)Termination phase: Saturation
% 3.75/0.94  
% 3.75/0.94  % (23339)Memory used [KB]: 48869
% 3.75/0.94  % (23339)Time elapsed: 0.500 s
% 3.75/0.94  % (23339)------------------------------
% 3.75/0.94  % (23339)------------------------------
% 3.75/0.94  % (23330)Time limit reached!
% 3.75/0.94  % (23330)------------------------------
% 3.75/0.94  % (23330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.75/0.94  % (23330)Termination reason: Time limit
% 3.75/0.94  
% 3.75/0.94  % (23330)Memory used [KB]: 8955
% 3.75/0.94  % (23330)Time elapsed: 0.512 s
% 3.75/0.94  % (23330)------------------------------
% 3.75/0.94  % (23330)------------------------------
% 3.75/0.95  % (23341)Time limit reached!
% 3.75/0.95  % (23341)------------------------------
% 3.75/0.95  % (23341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.75/0.95  % (23341)Termination reason: Time limit
% 3.75/0.95  
% 3.75/0.95  % (23341)Memory used [KB]: 10618
% 3.75/0.95  % (23341)Time elapsed: 0.546 s
% 3.75/0.95  % (23341)------------------------------
% 3.75/0.95  % (23341)------------------------------
% 3.75/0.97  % (23396)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 4.08/1.00  % (23365)Time limit reached!
% 4.08/1.00  % (23365)------------------------------
% 4.08/1.00  % (23365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.08/1.00  % (23365)Termination reason: Time limit
% 4.08/1.00  
% 4.08/1.00  % (23365)Memory used [KB]: 6780
% 4.08/1.00  % (23365)Time elapsed: 0.401 s
% 4.08/1.00  % (23365)------------------------------
% 4.08/1.00  % (23365)------------------------------
% 4.08/1.02  % (23366)Time limit reached!
% 4.08/1.02  % (23366)------------------------------
% 4.08/1.02  % (23366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.08/1.02  % (23345)Time limit reached!
% 4.08/1.02  % (23345)------------------------------
% 4.08/1.02  % (23345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.08/1.03  % (23366)Termination reason: Time limit
% 4.08/1.03  
% 4.08/1.03  % (23366)Memory used [KB]: 12920
% 4.08/1.03  % (23366)Time elapsed: 0.413 s
% 4.08/1.03  % (23366)------------------------------
% 4.08/1.03  % (23366)------------------------------
% 4.08/1.03  % (23345)Termination reason: Time limit
% 4.08/1.03  
% 4.08/1.03  % (23345)Memory used [KB]: 15479
% 4.08/1.03  % (23345)Time elapsed: 0.619 s
% 4.08/1.03  % (23345)------------------------------
% 4.08/1.03  % (23345)------------------------------
% 4.67/1.05  % (23357)Time limit reached!
% 4.67/1.05  % (23357)------------------------------
% 4.67/1.05  % (23357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.67/1.05  % (23357)Termination reason: Time limit
% 4.67/1.05  
% 4.67/1.05  % (23357)Memory used [KB]: 9210
% 4.67/1.05  % (23357)Time elapsed: 0.633 s
% 4.67/1.05  % (23357)------------------------------
% 4.67/1.05  % (23357)------------------------------
% 5.63/1.08  % (23336)Time limit reached!
% 5.63/1.08  % (23336)------------------------------
% 5.63/1.08  % (23336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.63/1.08  % (23336)Termination reason: Time limit
% 5.63/1.08  % (23336)Termination phase: Saturation
% 5.63/1.08  
% 5.63/1.08  % (23336)Memory used [KB]: 12409
% 5.63/1.08  % (23336)Time elapsed: 0.600 s
% 5.63/1.08  % (23336)------------------------------
% 5.63/1.08  % (23336)------------------------------
% 5.63/1.10  % (23399)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 6.02/1.13  % (23398)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 6.02/1.13  % (23398)Refutation not found, incomplete strategy% (23398)------------------------------
% 6.02/1.13  % (23398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.02/1.13  % (23398)Termination reason: Refutation not found, incomplete strategy
% 6.02/1.13  
% 6.02/1.13  % (23398)Memory used [KB]: 1663
% 6.02/1.13  % (23398)Time elapsed: 0.108 s
% 6.02/1.13  % (23398)------------------------------
% 6.02/1.13  % (23398)------------------------------
% 6.02/1.13  % (23397)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.02/1.13  % (23397)Refutation not found, incomplete strategy% (23397)------------------------------
% 6.02/1.13  % (23397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.02/1.13  % (23397)Termination reason: Refutation not found, incomplete strategy
% 6.02/1.13  
% 6.02/1.13  % (23397)Memory used [KB]: 6140
% 6.02/1.13  % (23397)Time elapsed: 0.153 s
% 6.02/1.13  % (23397)------------------------------
% 6.02/1.13  % (23397)------------------------------
% 6.02/1.16  % (23400)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 6.24/1.16  % (23400)Refutation not found, incomplete strategy% (23400)------------------------------
% 6.24/1.16  % (23400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.24/1.16  % (23400)Termination reason: Refutation not found, incomplete strategy
% 6.24/1.16  
% 6.24/1.16  % (23400)Memory used [KB]: 1663
% 6.24/1.16  % (23400)Time elapsed: 0.138 s
% 6.24/1.16  % (23400)------------------------------
% 6.24/1.16  % (23400)------------------------------
% 6.24/1.17  % (23402)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 6.24/1.17  % (23402)Refutation not found, incomplete strategy% (23402)------------------------------
% 6.24/1.17  % (23402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.24/1.17  % (23402)Termination reason: Refutation not found, incomplete strategy
% 6.24/1.17  
% 6.24/1.17  % (23402)Memory used [KB]: 6140
% 6.24/1.17  % (23402)Time elapsed: 0.077 s
% 6.24/1.17  % (23402)------------------------------
% 6.24/1.17  % (23402)------------------------------
% 6.24/1.18  % (23404)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 6.24/1.19  % (23401)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 6.24/1.21  % (23403)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 6.70/1.26  % (23409)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 6.70/1.26  % (23405)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 6.93/1.27  % (23415)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 6.93/1.29  % (23406)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 8.18/1.49  % (23399)Time limit reached!
% 8.18/1.49  % (23399)------------------------------
% 8.18/1.49  % (23399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.18/1.49  % (23403)Time limit reached!
% 8.18/1.49  % (23403)------------------------------
% 8.18/1.49  % (23403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.18/1.49  % (23403)Termination reason: Time limit
% 8.18/1.49  % (23403)Termination phase: Saturation
% 8.18/1.49  
% 8.18/1.49  % (23403)Memory used [KB]: 3709
% 8.18/1.49  % (23403)Time elapsed: 0.400 s
% 8.18/1.49  % (23403)------------------------------
% 8.18/1.49  % (23403)------------------------------
% 8.18/1.50  % (23399)Termination reason: Time limit
% 8.18/1.50  
% 8.18/1.50  % (23399)Memory used [KB]: 4477
% 8.18/1.50  % (23399)Time elapsed: 0.514 s
% 8.18/1.50  % (23399)------------------------------
% 8.18/1.50  % (23399)------------------------------
% 8.95/1.57  % (23406)Time limit reached!
% 8.95/1.57  % (23406)------------------------------
% 8.95/1.57  % (23406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.95/1.59  % (23406)Termination reason: Time limit
% 8.95/1.59  % (23406)Termination phase: Saturation
% 8.95/1.59  
% 8.95/1.59  % (23406)Memory used [KB]: 3965
% 8.95/1.59  % (23406)Time elapsed: 0.400 s
% 8.95/1.59  % (23406)------------------------------
% 8.95/1.59  % (23406)------------------------------
% 8.95/1.63  % (23566)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 8.95/1.63  % (23565)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 10.85/1.74  % (23588)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 10.99/1.80  % (23353)Time limit reached!
% 10.99/1.80  % (23353)------------------------------
% 10.99/1.80  % (23353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.49/1.82  % (23353)Termination reason: Time limit
% 11.49/1.82  
% 11.49/1.82  % (23353)Memory used [KB]: 22387
% 11.49/1.82  % (23353)Time elapsed: 1.390 s
% 11.49/1.82  % (23353)------------------------------
% 11.49/1.82  % (23353)------------------------------
% 11.49/1.83  % (23355)Time limit reached!
% 11.49/1.83  % (23355)------------------------------
% 11.49/1.83  % (23355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.49/1.84  % (23355)Termination reason: Time limit
% 11.49/1.84  % (23355)Termination phase: Saturation
% 11.49/1.84  
% 11.49/1.84  % (23355)Memory used [KB]: 117183
% 11.49/1.84  % (23355)Time elapsed: 1.200 s
% 11.49/1.84  % (23355)------------------------------
% 11.49/1.84  % (23355)------------------------------
% 11.82/1.88  % (23368)Time limit reached!
% 11.82/1.88  % (23368)------------------------------
% 11.82/1.88  % (23368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.82/1.88  % (23368)Termination reason: Time limit
% 11.82/1.88  
% 11.82/1.88  % (23368)Memory used [KB]: 14072
% 11.82/1.88  % (23368)Time elapsed: 1.205 s
% 11.82/1.88  % (23368)------------------------------
% 11.82/1.88  % (23368)------------------------------
% 11.82/1.91  % (23642)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 11.82/1.93  % (23356)Time limit reached!
% 11.82/1.93  % (23356)------------------------------
% 11.82/1.93  % (23356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.82/1.93  % (23642)Refutation not found, incomplete strategy% (23642)------------------------------
% 11.82/1.93  % (23642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.82/1.93  % (23642)Termination reason: Refutation not found, incomplete strategy
% 11.82/1.93  
% 11.82/1.93  % (23642)Memory used [KB]: 6140
% 11.82/1.93  % (23642)Time elapsed: 0.073 s
% 11.82/1.93  % (23642)------------------------------
% 11.82/1.93  % (23642)------------------------------
% 11.82/1.93  % (23356)Termination reason: Time limit
% 11.82/1.93  % (23356)Termination phase: Saturation
% 11.82/1.93  
% 11.82/1.93  % (23356)Memory used [KB]: 22003
% 11.82/1.93  % (23356)Time elapsed: 1.500 s
% 11.82/1.93  % (23356)------------------------------
% 11.82/1.93  % (23356)------------------------------
% 11.82/1.93  % (23643)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 12.72/1.99  % (23644)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 12.72/2.00  % (23644)Refutation not found, incomplete strategy% (23644)------------------------------
% 12.72/2.00  % (23644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.72/2.00  % (23644)Termination reason: Refutation not found, incomplete strategy
% 12.72/2.00  
% 12.72/2.00  % (23644)Memory used [KB]: 10618
% 12.72/2.00  % (23644)Time elapsed: 0.087 s
% 12.72/2.00  % (23644)------------------------------
% 12.72/2.00  % (23644)------------------------------
% 12.72/2.02  % (23340)Time limit reached!
% 12.72/2.02  % (23340)------------------------------
% 12.72/2.02  % (23340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.72/2.02  % (23340)Termination reason: Time limit
% 12.72/2.02  
% 12.72/2.02  % (23340)Memory used [KB]: 28144
% 12.72/2.02  % (23340)Time elapsed: 1.614 s
% 12.72/2.02  % (23340)------------------------------
% 12.72/2.02  % (23340)------------------------------
% 13.23/2.05  % (23588)Time limit reached!
% 13.23/2.05  % (23588)------------------------------
% 13.23/2.05  % (23588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.35/2.06  % (23588)Termination reason: Time limit
% 13.35/2.06  % (23588)Termination phase: Saturation
% 13.35/2.06  
% 13.35/2.06  % (23588)Memory used [KB]: 10874
% 13.35/2.06  % (23588)Time elapsed: 0.400 s
% 13.35/2.06  % (23588)------------------------------
% 13.35/2.06  % (23588)------------------------------
% 13.35/2.07  % (23344)Time limit reached!
% 13.35/2.07  % (23344)------------------------------
% 13.35/2.07  % (23344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.35/2.07  % (23344)Termination reason: Time limit
% 13.35/2.07  % (23344)Termination phase: Saturation
% 13.35/2.07  
% 13.35/2.07  % (23344)Memory used [KB]: 183707
% 13.35/2.07  % (23344)Time elapsed: 1.300 s
% 13.35/2.07  % (23344)------------------------------
% 13.35/2.07  % (23344)------------------------------
% 14.34/2.23  % (23343)Time limit reached!
% 14.34/2.23  % (23343)------------------------------
% 14.34/2.23  % (23343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.34/2.23  % (23343)Termination reason: Time limit
% 14.34/2.23  
% 14.34/2.23  % (23343)Memory used [KB]: 20596
% 14.34/2.23  % (23343)Time elapsed: 1.814 s
% 14.34/2.23  % (23343)------------------------------
% 14.34/2.23  % (23343)------------------------------
% 15.30/2.30  % (23364)Time limit reached!
% 15.30/2.30  % (23364)------------------------------
% 15.30/2.30  % (23364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.30/2.30  % (23364)Termination reason: Time limit
% 15.30/2.30  
% 15.30/2.30  % (23364)Memory used [KB]: 24946
% 15.30/2.30  % (23364)Time elapsed: 1.713 s
% 15.30/2.30  % (23364)------------------------------
% 15.30/2.30  % (23364)------------------------------
% 15.30/2.31  % (23333)Time limit reached!
% 15.30/2.31  % (23333)------------------------------
% 15.30/2.31  % (23333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.30/2.31  % (23333)Termination reason: Time limit
% 15.30/2.31  
% 15.30/2.31  % (23333)Memory used [KB]: 143281
% 15.30/2.31  % (23333)Time elapsed: 1.834 s
% 15.30/2.31  % (23333)------------------------------
% 15.30/2.31  % (23333)------------------------------
% 15.78/2.38  % (23643)Time limit reached!
% 15.78/2.38  % (23643)------------------------------
% 15.78/2.38  % (23643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.78/2.38  % (23643)Termination reason: Time limit
% 15.78/2.38  % (23643)Termination phase: Saturation
% 15.78/2.38  
% 15.78/2.38  % (23643)Memory used [KB]: 62045
% 15.78/2.38  % (23643)Time elapsed: 0.400 s
% 15.78/2.38  % (23643)------------------------------
% 15.78/2.38  % (23643)------------------------------
% 16.68/2.46  % (23335)Time limit reached!
% 16.68/2.46  % (23335)------------------------------
% 16.68/2.46  % (23335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.68/2.46  % (23335)Termination reason: Time limit
% 16.68/2.46  % (23335)Termination phase: Saturation
% 16.68/2.46  
% 16.68/2.46  % (23335)Memory used [KB]: 36843
% 16.68/2.46  % (23335)Time elapsed: 2.0000 s
% 16.68/2.46  % (23335)------------------------------
% 16.68/2.46  % (23335)------------------------------
% 16.68/2.48  % (23405)Time limit reached!
% 16.68/2.48  % (23405)------------------------------
% 16.68/2.48  % (23405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.68/2.48  % (23405)Termination reason: Time limit
% 16.68/2.48  
% 16.68/2.48  % (23405)Memory used [KB]: 22771
% 16.68/2.48  % (23405)Time elapsed: 1.308 s
% 16.68/2.48  % (23405)------------------------------
% 16.68/2.48  % (23405)------------------------------
% 16.68/2.50  % (23347)Time limit reached!
% 16.68/2.50  % (23347)------------------------------
% 16.68/2.50  % (23347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.68/2.50  % (23347)Termination reason: Time limit
% 16.68/2.50  
% 16.68/2.50  % (23347)Memory used [KB]: 37867
% 16.68/2.50  % (23347)Time elapsed: 2.100 s
% 16.68/2.50  % (23347)------------------------------
% 16.68/2.50  % (23347)------------------------------
% 16.68/2.52  % (23395)Time limit reached!
% 16.68/2.52  % (23395)------------------------------
% 16.68/2.52  % (23395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.68/2.52  % (23395)Termination reason: Time limit
% 16.68/2.52  % (23395)Termination phase: Saturation
% 16.68/2.52  
% 16.68/2.52  % (23395)Memory used [KB]: 194581
% 16.68/2.52  % (23395)Time elapsed: 1.700 s
% 16.68/2.52  % (23395)------------------------------
% 16.68/2.52  % (23395)------------------------------
% 21.12/3.02  % (23348)Time limit reached!
% 21.12/3.02  % (23348)------------------------------
% 21.12/3.02  % (23348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.12/3.02  % (23348)Termination reason: Time limit
% 21.12/3.02  % (23348)Termination phase: Saturation
% 21.12/3.02  
% 21.12/3.02  % (23348)Memory used [KB]: 52067
% 21.12/3.02  % (23348)Time elapsed: 2.600 s
% 21.12/3.02  % (23348)------------------------------
% 21.12/3.02  % (23348)------------------------------
% 24.08/3.43  % (23342)Time limit reached!
% 24.08/3.43  % (23342)------------------------------
% 24.08/3.43  % (23342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.08/3.43  % (23342)Termination reason: Time limit
% 24.08/3.43  
% 24.08/3.43  % (23342)Memory used [KB]: 16630
% 24.08/3.43  % (23342)Time elapsed: 3.021 s
% 24.08/3.43  % (23342)------------------------------
% 24.08/3.43  % (23342)------------------------------
% 24.08/3.44  % (23363)Time limit reached!
% 24.08/3.44  % (23363)------------------------------
% 24.08/3.44  % (23363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.08/3.44  % (23363)Termination reason: Time limit
% 24.08/3.44  % (23363)Termination phase: Saturation
% 24.08/3.44  
% 24.08/3.44  % (23363)Memory used [KB]: 47461
% 24.08/3.44  % (23363)Time elapsed: 2.800 s
% 24.08/3.44  % (23363)------------------------------
% 24.08/3.44  % (23363)------------------------------
% 31.24/4.32  % (23358)Time limit reached!
% 31.24/4.32  % (23358)------------------------------
% 31.24/4.32  % (23358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.24/4.33  % (23358)Termination reason: Time limit
% 31.24/4.33  
% 31.24/4.33  % (23358)Memory used [KB]: 75990
% 31.24/4.33  % (23358)Time elapsed: 3.916 s
% 31.24/4.33  % (23358)------------------------------
% 31.24/4.33  % (23358)------------------------------
% 33.57/4.60  % (23401)Time limit reached!
% 33.57/4.60  % (23401)------------------------------
% 33.57/4.60  % (23401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 33.57/4.60  % (23401)Termination reason: Time limit
% 33.57/4.60  % (23401)Termination phase: Saturation
% 33.57/4.60  
% 33.57/4.60  % (23401)Memory used [KB]: 125754
% 33.57/4.60  % (23401)Time elapsed: 3.500 s
% 33.57/4.60  % (23401)------------------------------
% 33.57/4.60  % (23401)------------------------------
% 39.74/5.34  % (23338)Time limit reached!
% 39.74/5.34  % (23338)------------------------------
% 39.74/5.34  % (23338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 39.74/5.34  % (23338)Termination reason: Time limit
% 39.74/5.34  % (23338)Termination phase: Saturation
% 39.74/5.34  
% 39.74/5.34  % (23338)Memory used [KB]: 826553
% 39.74/5.34  % (23338)Time elapsed: 4.600 s
% 39.74/5.34  % (23338)------------------------------
% 39.74/5.34  % (23338)------------------------------
% 42.13/5.64  % (23332)Time limit reached!
% 42.13/5.64  % (23332)------------------------------
% 42.13/5.64  % (23332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 42.21/5.65  % (23332)Termination reason: Time limit
% 42.21/5.65  % (23332)Termination phase: Saturation
% 42.21/5.65  
% 42.21/5.65  % (23332)Memory used [KB]: 136245
% 42.21/5.65  % (23332)Time elapsed: 5.200 s
% 42.21/5.65  % (23332)------------------------------
% 42.21/5.65  % (23332)------------------------------
% 45.56/6.13  % (23369)Time limit reached!
% 45.56/6.13  % (23369)------------------------------
% 45.56/6.13  % (23369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 45.56/6.13  % (23369)Termination reason: Time limit
% 45.56/6.13  % (23369)Termination phase: Saturation
% 45.56/6.13  
% 45.56/6.13  % (23369)Memory used [KB]: 133686
% 45.56/6.13  % (23369)Time elapsed: 5.500 s
% 45.56/6.13  % (23369)------------------------------
% 45.56/6.13  % (23369)------------------------------
% 47.51/6.35  % (23415)Refutation found. Thanks to Tanya!
% 47.51/6.35  % SZS status Theorem for theBenchmark
% 47.51/6.35  % SZS output start Proof for theBenchmark
% 47.51/6.35  fof(f32445,plain,(
% 47.51/6.35    $false),
% 47.51/6.35    inference(subsumption_resolution,[],[f32444,f248])).
% 47.51/6.35  fof(f248,plain,(
% 47.51/6.35    ( ! [X6,X7] : (k4_xboole_0(X6,X7) = k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X6,X7)))) )),
% 47.51/6.35    inference(forward_demodulation,[],[f241,f20])).
% 47.51/6.35  fof(f20,plain,(
% 47.51/6.35    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 47.51/6.35    inference(cnf_transformation,[],[f6])).
% 47.51/6.35  fof(f6,axiom,(
% 47.51/6.35    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 47.51/6.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 47.51/6.35  fof(f241,plain,(
% 47.51/6.35    ( ! [X6,X7] : (k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X6,X7))) = k4_xboole_0(k4_xboole_0(X6,k1_xboole_0),X7)) )),
% 47.51/6.35    inference(superposition,[],[f36,f65])).
% 47.51/6.35  fof(f65,plain,(
% 47.51/6.35    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 47.51/6.35    inference(forward_demodulation,[],[f59,f64])).
% 47.51/6.35  fof(f64,plain,(
% 47.51/6.35    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,X2)) )),
% 47.51/6.35    inference(forward_demodulation,[],[f57,f20])).
% 47.51/6.35  fof(f57,plain,(
% 47.51/6.35    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0))) )),
% 47.51/6.35    inference(superposition,[],[f31,f34])).
% 47.51/6.35  fof(f34,plain,(
% 47.51/6.35    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 47.51/6.35    inference(definition_unfolding,[],[f22,f24])).
% 47.51/6.35  fof(f24,plain,(
% 47.51/6.35    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 47.51/6.35    inference(cnf_transformation,[],[f11])).
% 47.51/6.35  fof(f11,axiom,(
% 47.51/6.35    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 47.51/6.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 47.51/6.35  fof(f22,plain,(
% 47.51/6.35    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 47.51/6.35    inference(cnf_transformation,[],[f7])).
% 47.51/6.35  fof(f7,axiom,(
% 47.51/6.35    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 47.51/6.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 47.51/6.35  fof(f31,plain,(
% 47.51/6.35    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 47.51/6.35    inference(definition_unfolding,[],[f25,f26])).
% 47.51/6.35  fof(f26,plain,(
% 47.51/6.35    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 47.51/6.35    inference(cnf_transformation,[],[f8])).
% 47.51/6.35  fof(f8,axiom,(
% 47.51/6.35    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 47.51/6.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 47.51/6.35  fof(f25,plain,(
% 47.51/6.35    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 47.51/6.35    inference(cnf_transformation,[],[f3])).
% 47.51/6.35  fof(f3,axiom,(
% 47.51/6.35    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 47.51/6.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 47.51/6.35  fof(f59,plain,(
% 47.51/6.35    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 47.51/6.35    inference(superposition,[],[f31,f33])).
% 47.51/6.35  fof(f33,plain,(
% 47.51/6.35    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 47.51/6.35    inference(definition_unfolding,[],[f21,f26])).
% 47.51/6.35  fof(f21,plain,(
% 47.51/6.35    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 47.51/6.35    inference(cnf_transformation,[],[f14])).
% 47.51/6.35  fof(f14,plain,(
% 47.51/6.35    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 47.51/6.35    inference(rectify,[],[f2])).
% 47.51/6.35  fof(f2,axiom,(
% 47.51/6.35    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 47.51/6.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 47.51/6.35  fof(f36,plain,(
% 47.51/6.35    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 47.51/6.35    inference(definition_unfolding,[],[f29,f26,f26])).
% 47.51/6.35  fof(f29,plain,(
% 47.51/6.35    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 47.51/6.35    inference(cnf_transformation,[],[f9])).
% 47.51/6.35  fof(f9,axiom,(
% 47.51/6.35    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 47.51/6.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 47.51/6.35  fof(f32444,plain,(
% 47.51/6.35    k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) != k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))))),
% 47.51/6.35    inference(forward_demodulation,[],[f32441,f17775])).
% 47.51/6.35  fof(f17775,plain,(
% 47.51/6.35    ( ! [X8,X9] : (k5_xboole_0(k4_xboole_0(X9,X8),k4_xboole_0(X8,X9)) = k5_xboole_0(X9,X8)) )),
% 47.51/6.35    inference(forward_demodulation,[],[f17751,f66])).
% 47.51/6.35  fof(f66,plain,(
% 47.51/6.35    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 47.51/6.35    inference(backward_demodulation,[],[f55,f65])).
% 47.51/6.35  fof(f55,plain,(
% 47.51/6.35    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 47.51/6.35    inference(superposition,[],[f31,f20])).
% 47.51/6.35  fof(f17751,plain,(
% 47.51/6.35    ( ! [X8,X9] : (k5_xboole_0(k4_xboole_0(X9,X8),k4_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X8,k1_xboole_0))) )),
% 47.51/6.35    inference(superposition,[],[f1968,f64])).
% 47.51/6.35  fof(f1968,plain,(
% 47.51/6.35    ( ! [X14,X12,X13] : (k5_xboole_0(k4_xboole_0(X12,X13),X14) = k5_xboole_0(X12,k5_xboole_0(X13,k5_xboole_0(k4_xboole_0(X13,X12),X14)))) )),
% 47.51/6.35    inference(forward_demodulation,[],[f1897,f28])).
% 47.51/6.35  fof(f28,plain,(
% 47.51/6.35    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 47.51/6.35    inference(cnf_transformation,[],[f10])).
% 47.51/6.35  fof(f10,axiom,(
% 47.51/6.35    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 47.51/6.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 47.51/6.35  fof(f1897,plain,(
% 47.51/6.35    ( ! [X14,X12,X13] : (k5_xboole_0(k4_xboole_0(X12,X13),X14) = k5_xboole_0(X12,k5_xboole_0(k5_xboole_0(X13,k4_xboole_0(X13,X12)),X14))) )),
% 47.51/6.35    inference(superposition,[],[f62,f1623])).
% 47.51/6.35  fof(f1623,plain,(
% 47.51/6.35    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 47.51/6.35    inference(backward_demodulation,[],[f74,f1622])).
% 47.51/6.35  fof(f1622,plain,(
% 47.51/6.35    ( ! [X43,X42] : (k4_xboole_0(X42,X43) = k4_xboole_0(X42,k4_xboole_0(X43,k4_xboole_0(X43,X42)))) )),
% 47.51/6.35    inference(forward_demodulation,[],[f1621,f248])).
% 47.51/6.35  fof(f1621,plain,(
% 47.51/6.35    ( ! [X43,X42] : (k4_xboole_0(X42,k4_xboole_0(X43,k4_xboole_0(X43,X42))) = k4_xboole_0(X42,k4_xboole_0(X42,k4_xboole_0(X42,X43)))) )),
% 47.51/6.35    inference(forward_demodulation,[],[f1465,f20])).
% 47.51/6.35  fof(f1465,plain,(
% 47.51/6.35    ( ! [X43,X42] : (k4_xboole_0(X42,k4_xboole_0(X43,k4_xboole_0(X43,X42))) = k4_xboole_0(X42,k4_xboole_0(X42,k4_xboole_0(k4_xboole_0(X42,X43),k1_xboole_0)))) )),
% 47.51/6.35    inference(superposition,[],[f89,f20])).
% 47.51/6.35  fof(f89,plain,(
% 47.51/6.35    ( ! [X6,X7,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k4_xboole_0(X5,X6),X7))) = k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X6,X5))),X7)) )),
% 47.51/6.35    inference(superposition,[],[f36,f35])).
% 47.51/6.35  fof(f35,plain,(
% 47.51/6.35    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 47.51/6.35    inference(definition_unfolding,[],[f23,f26,f26])).
% 47.51/6.35  fof(f23,plain,(
% 47.51/6.35    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 47.51/6.35    inference(cnf_transformation,[],[f1])).
% 47.51/6.35  fof(f1,axiom,(
% 47.51/6.35    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 47.51/6.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 47.51/6.35  fof(f74,plain,(
% 47.51/6.35    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))) )),
% 47.51/6.35    inference(superposition,[],[f31,f35])).
% 47.51/6.35  fof(f62,plain,(
% 47.51/6.35    ( ! [X2,X3,X1] : (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)) = k5_xboole_0(k4_xboole_0(X1,X2),X3)) )),
% 47.51/6.35    inference(superposition,[],[f28,f31])).
% 47.51/6.35  fof(f32441,plain,(
% 47.51/6.35    k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) != k4_xboole_0(k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 47.51/6.35    inference(backward_demodulation,[],[f15995,f32439])).
% 47.51/6.35  fof(f32439,plain,(
% 47.51/6.35    ( ! [X331,X332,X330] : (k4_xboole_0(k5_xboole_0(X330,k4_xboole_0(X331,X330)),k4_xboole_0(X330,k4_xboole_0(X330,X332))) = k5_xboole_0(k4_xboole_0(X330,X332),k4_xboole_0(X331,X330))) )),
% 47.51/6.35    inference(backward_demodulation,[],[f32332,f32438])).
% 47.51/6.35  fof(f32438,plain,(
% 47.51/6.35    ( ! [X68,X66,X67] : (k5_xboole_0(k4_xboole_0(X66,X68),k4_xboole_0(X67,X66)) = k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),k4_xboole_0(X68,k4_xboole_0(X67,X66)))) )),
% 47.51/6.35    inference(forward_demodulation,[],[f32437,f12686])).
% 47.51/6.35  fof(f12686,plain,(
% 47.51/6.35    ( ! [X6,X5] : (k4_xboole_0(X6,X5) = k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),X5)) )),
% 47.51/6.35    inference(backward_demodulation,[],[f291,f12637])).
% 47.51/6.35  fof(f12637,plain,(
% 47.51/6.35    ( ! [X10,X9] : (k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9) )),
% 47.51/6.35    inference(superposition,[],[f8712,f8712])).
% 47.51/6.35  fof(f8712,plain,(
% 47.51/6.35    ( ! [X10,X9] : (k5_xboole_0(X10,k5_xboole_0(X9,X10)) = X9) )),
% 47.51/6.35    inference(forward_demodulation,[],[f8690,f66])).
% 47.51/6.35  fof(f8690,plain,(
% 47.51/6.35    ( ! [X10,X9] : (k5_xboole_0(X10,k5_xboole_0(X9,X10)) = k5_xboole_0(X9,k1_xboole_0)) )),
% 47.51/6.35    inference(superposition,[],[f4351,f81])).
% 47.51/6.35  fof(f81,plain,(
% 47.51/6.35    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) )),
% 47.51/6.35    inference(superposition,[],[f64,f28])).
% 47.51/6.35  fof(f4351,plain,(
% 47.51/6.35    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 47.51/6.35    inference(backward_demodulation,[],[f83,f4349])).
% 47.51/6.35  fof(f4349,plain,(
% 47.51/6.35    ( ! [X3] : (k5_xboole_0(k1_xboole_0,X3) = X3) )),
% 47.51/6.35    inference(forward_demodulation,[],[f4321,f66])).
% 47.51/6.35  fof(f4321,plain,(
% 47.51/6.35    ( ! [X3] : (k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X3,k1_xboole_0)) )),
% 47.51/6.35    inference(superposition,[],[f83,f64])).
% 47.51/6.35  fof(f83,plain,(
% 47.51/6.35    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 47.51/6.35    inference(superposition,[],[f28,f64])).
% 47.51/6.35  fof(f291,plain,(
% 47.51/6.35    ( ! [X6,X5] : (k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),X5) = k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),X5)) )),
% 47.51/6.35    inference(forward_demodulation,[],[f278,f20])).
% 47.51/6.36  fof(f278,plain,(
% 47.51/6.36    ( ! [X6,X5] : (k4_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),X5) = k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(X6,X5)),k4_xboole_0(X5,k1_xboole_0))) )),
% 47.51/6.36    inference(superposition,[],[f73,f34])).
% 47.51/6.36  fof(f73,plain,(
% 47.51/6.36    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 47.51/6.36    inference(superposition,[],[f31,f35])).
% 47.51/6.36  fof(f32437,plain,(
% 47.51/6.36    ( ! [X68,X66,X67] : (k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),k4_xboole_0(X68,k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),X66))) = k5_xboole_0(k4_xboole_0(X66,X68),k4_xboole_0(X67,X66))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f32436,f12712])).
% 47.51/6.36  fof(f12712,plain,(
% 47.51/6.36    ( ! [X8,X7,X9] : (k5_xboole_0(X8,X9) = k5_xboole_0(X7,k5_xboole_0(X8,k5_xboole_0(X7,X9)))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f12647,f28])).
% 47.51/6.36  fof(f12647,plain,(
% 47.51/6.36    ( ! [X8,X7,X9] : (k5_xboole_0(X8,X9) = k5_xboole_0(X7,k5_xboole_0(k5_xboole_0(X8,X7),X9))) )),
% 47.51/6.36    inference(superposition,[],[f28,f8712])).
% 47.51/6.36  fof(f32436,plain,(
% 47.51/6.36    ( ! [X68,X66,X67] : (k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),k4_xboole_0(X68,k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),X66))) = k5_xboole_0(X66,k5_xboole_0(k4_xboole_0(X66,X68),k5_xboole_0(X66,k4_xboole_0(X67,X66))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f32435,f17911])).
% 47.51/6.36  fof(f17911,plain,(
% 47.51/6.36    ( ! [X74,X72,X73] : (k5_xboole_0(X74,k4_xboole_0(X72,k4_xboole_0(X72,X73))) = k5_xboole_0(X72,k5_xboole_0(k4_xboole_0(X72,X73),X74))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f17910,f4351])).
% 47.51/6.36  fof(f17910,plain,(
% 47.51/6.36    ( ! [X74,X72,X73] : (k5_xboole_0(X74,k4_xboole_0(X72,k4_xboole_0(X72,X73))) = k5_xboole_0(X72,k5_xboole_0(X72,k5_xboole_0(X72,k5_xboole_0(k4_xboole_0(X72,X73),X74))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f17909,f8692])).
% 47.51/6.36  fof(f8692,plain,(
% 47.51/6.36    ( ! [X14,X15,X16] : (k5_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X16) = k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X14,X15),X16))) )),
% 47.51/6.36    inference(superposition,[],[f4351,f62])).
% 47.51/6.36  fof(f17909,plain,(
% 47.51/6.36    ( ! [X74,X72,X73] : (k5_xboole_0(X74,k4_xboole_0(X72,k4_xboole_0(X72,X73))) = k5_xboole_0(X72,k5_xboole_0(X72,k5_xboole_0(k4_xboole_0(X72,k4_xboole_0(X72,X73)),X74)))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f17908,f8692])).
% 47.51/6.36  fof(f17908,plain,(
% 47.51/6.36    ( ! [X74,X72,X73] : (k5_xboole_0(X72,k5_xboole_0(k4_xboole_0(X72,k4_xboole_0(X72,k4_xboole_0(X72,X73))),X74)) = k5_xboole_0(X74,k4_xboole_0(X72,k4_xboole_0(X72,X73)))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f17907,f4349])).
% 47.51/6.36  fof(f17907,plain,(
% 47.51/6.36    ( ! [X74,X72,X73] : (k5_xboole_0(X72,k5_xboole_0(k4_xboole_0(X72,k4_xboole_0(X72,k4_xboole_0(X72,X73))),X74)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X74,k4_xboole_0(X72,k4_xboole_0(X72,X73))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f17794,f15029])).
% 47.51/6.36  fof(f15029,plain,(
% 47.51/6.36    ( ! [X24,X23,X25] : (k5_xboole_0(X23,k5_xboole_0(X24,X25)) = k5_xboole_0(X25,k5_xboole_0(X23,X24))) )),
% 47.51/6.36    inference(superposition,[],[f12645,f28])).
% 47.51/6.36  fof(f12645,plain,(
% 47.51/6.36    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2)) )),
% 47.51/6.36    inference(superposition,[],[f4351,f8712])).
% 47.51/6.36  fof(f17794,plain,(
% 47.51/6.36    ( ! [X74,X72,X73] : (k5_xboole_0(X72,k5_xboole_0(k4_xboole_0(X72,k4_xboole_0(X72,k4_xboole_0(X72,X73))),X74)) = k5_xboole_0(k4_xboole_0(X72,k4_xboole_0(X72,X73)),k5_xboole_0(k1_xboole_0,X74))) )),
% 47.51/6.36    inference(superposition,[],[f1994,f780])).
% 47.51/6.36  fof(f780,plain,(
% 47.51/6.36    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 47.51/6.36    inference(forward_demodulation,[],[f779,f65])).
% 47.51/6.36  fof(f779,plain,(
% 47.51/6.36    ( ! [X0,X1] : (k4_xboole_0(X1,X1) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 47.51/6.36    inference(forward_demodulation,[],[f671,f20])).
% 47.51/6.36  fof(f671,plain,(
% 47.51/6.36    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 47.51/6.36    inference(superposition,[],[f93,f65])).
% 47.51/6.36  fof(f93,plain,(
% 47.51/6.36    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) )),
% 47.51/6.36    inference(superposition,[],[f36,f35])).
% 47.51/6.36  fof(f1994,plain,(
% 47.51/6.36    ( ! [X59,X60,X58] : (k5_xboole_0(X59,k5_xboole_0(k4_xboole_0(X59,X58),X60)) = k5_xboole_0(X58,k5_xboole_0(k4_xboole_0(X58,X59),X60))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f1993,f1622])).
% 47.51/6.36  fof(f1993,plain,(
% 47.51/6.36    ( ! [X59,X60,X58] : (k5_xboole_0(X59,k5_xboole_0(k4_xboole_0(X59,X58),X60)) = k5_xboole_0(X58,k5_xboole_0(k4_xboole_0(X58,k4_xboole_0(X59,k4_xboole_0(X59,X58))),X60))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f1992,f1881])).
% 47.51/6.36  fof(f1881,plain,(
% 47.51/6.36    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X3,k4_xboole_0(X3,X2))) )),
% 47.51/6.36    inference(superposition,[],[f1623,f35])).
% 47.51/6.36  fof(f1992,plain,(
% 47.51/6.36    ( ! [X59,X60,X58] : (k5_xboole_0(X58,k5_xboole_0(k4_xboole_0(X58,k5_xboole_0(X59,k4_xboole_0(X59,X58))),X60)) = k5_xboole_0(X59,k5_xboole_0(k4_xboole_0(X59,X58),X60))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f1911,f28])).
% 47.51/6.36  fof(f1911,plain,(
% 47.51/6.36    ( ! [X59,X60,X58] : (k5_xboole_0(X58,k5_xboole_0(k4_xboole_0(X58,k5_xboole_0(X59,k4_xboole_0(X59,X58))),X60)) = k5_xboole_0(k5_xboole_0(X59,k4_xboole_0(X59,X58)),X60)) )),
% 47.51/6.36    inference(superposition,[],[f62,f1623])).
% 47.51/6.36  fof(f32435,plain,(
% 47.51/6.36    ( ! [X68,X66,X67] : (k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),k4_xboole_0(X68,k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),X66))) = k5_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),k4_xboole_0(X66,k4_xboole_0(X66,X68)))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f32434,f1938])).
% 47.51/6.36  fof(f1938,plain,(
% 47.51/6.36    ( ! [X10,X11,X9] : (k4_xboole_0(X9,k4_xboole_0(X9,X11)) = k4_xboole_0(X9,k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),X11))) )),
% 47.51/6.36    inference(backward_demodulation,[],[f1018,f1881])).
% 47.51/6.36  fof(f1018,plain,(
% 47.51/6.36    ( ! [X10,X11,X9] : (k4_xboole_0(X9,k4_xboole_0(k5_xboole_0(X9,k4_xboole_0(X10,X9)),X11)) = k5_xboole_0(X9,k4_xboole_0(X9,X11))) )),
% 47.51/6.36    inference(superposition,[],[f31,f114])).
% 47.51/6.36  fof(f114,plain,(
% 47.51/6.36    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X4))) = k4_xboole_0(X2,X4)) )),
% 47.51/6.36    inference(forward_demodulation,[],[f88,f20])).
% 47.51/6.36  fof(f88,plain,(
% 47.51/6.36    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X4))) = k4_xboole_0(k4_xboole_0(X2,k1_xboole_0),X4)) )),
% 47.51/6.36    inference(superposition,[],[f36,f34])).
% 47.51/6.36  fof(f32434,plain,(
% 47.51/6.36    ( ! [X68,X66,X67] : (k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),k4_xboole_0(X68,k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),X66))) = k5_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),k4_xboole_0(X66,k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),X68)))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f31925,f248])).
% 47.51/6.36  fof(f31925,plain,(
% 47.51/6.36    ( ! [X68,X66,X67] : (k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),k4_xboole_0(X68,k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),X66))) = k5_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),k4_xboole_0(X66,k4_xboole_0(X66,k4_xboole_0(X66,k4_xboole_0(k5_xboole_0(X66,k4_xboole_0(X67,X66)),X68)))))) )),
% 47.51/6.36    inference(superposition,[],[f2421,f1938])).
% 47.51/6.36  fof(f2421,plain,(
% 47.51/6.36    ( ! [X14,X12,X13] : (k5_xboole_0(X12,k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X12,k4_xboole_0(X12,X13))))) = k4_xboole_0(X12,k4_xboole_0(X13,k4_xboole_0(X12,X14)))) )),
% 47.51/6.36    inference(superposition,[],[f31,f2107])).
% 47.51/6.36  fof(f2107,plain,(
% 47.51/6.36    ( ! [X10,X8,X9] : (k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9)))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X8,X10))))) )),
% 47.51/6.36    inference(backward_demodulation,[],[f128,f2106])).
% 47.51/6.36  fof(f2106,plain,(
% 47.51/6.36    ( ! [X80,X81,X82] : (k4_xboole_0(X80,k4_xboole_0(X81,X82)) = k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(X80,X82))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f2105,f66])).
% 47.51/6.36  fof(f2105,plain,(
% 47.51/6.36    ( ! [X80,X81,X82] : (k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(X80,X82)))) = k5_xboole_0(k4_xboole_0(X80,k4_xboole_0(X81,X82)),k1_xboole_0)) )),
% 47.51/6.36    inference(forward_demodulation,[],[f2104,f65])).
% 47.51/6.36  fof(f2104,plain,(
% 47.51/6.36    ( ! [X80,X81,X82] : (k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(X80,X82)))) = k5_xboole_0(k4_xboole_0(X80,k4_xboole_0(X81,X82)),k4_xboole_0(X80,X80))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f2103,f20])).
% 47.51/6.36  fof(f2103,plain,(
% 47.51/6.36    ( ! [X80,X81,X82] : (k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(X80,X82)))) = k5_xboole_0(k4_xboole_0(X80,k4_xboole_0(X81,X82)),k4_xboole_0(X80,k4_xboole_0(X80,k1_xboole_0)))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f2102,f65])).
% 47.51/6.36  fof(f2102,plain,(
% 47.51/6.36    ( ! [X80,X81,X82] : (k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(X80,X82)))) = k5_xboole_0(k4_xboole_0(X80,k4_xboole_0(X81,X82)),k4_xboole_0(X80,k4_xboole_0(X80,k4_xboole_0(k4_xboole_0(X81,X82),k4_xboole_0(X81,X82)))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f2101,f1669])).
% 47.51/6.36  fof(f1669,plain,(
% 47.51/6.36    ( ! [X39,X37,X38,X40] : (k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(k4_xboole_0(X38,X39),X40))) = k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X38,k4_xboole_0(X38,k4_xboole_0(k4_xboole_0(X37,X39),X40)))))) )),
% 47.51/6.36    inference(backward_demodulation,[],[f1552,f1664])).
% 47.51/6.36  fof(f1664,plain,(
% 47.51/6.36    ( ! [X24,X23,X21,X22] : (k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X22,X23),X24))) = k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X22,X23),X24)))))))) )),
% 47.51/6.36    inference(backward_demodulation,[],[f235,f1624])).
% 47.51/6.36  fof(f1624,plain,(
% 47.51/6.36    ( ! [X6,X7,X5] : (k4_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k4_xboole_0(X5,X6),X7)))) )),
% 47.51/6.36    inference(backward_demodulation,[],[f89,f1622])).
% 47.51/6.36  fof(f235,plain,(
% 47.51/6.36    ( ! [X24,X23,X21,X22] : (k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(k4_xboole_0(X22,X23),X24))))) = k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X22,X23),X24)))))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f234,f36])).
% 47.51/6.36  fof(f234,plain,(
% 47.51/6.36    ( ! [X24,X23,X21,X22] : (k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(k4_xboole_0(X22,X23),X24))))) = k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,X23))),X24)))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f233,f36])).
% 47.51/6.36  fof(f233,plain,(
% 47.51/6.36    ( ! [X24,X23,X21,X22] : (k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,X23))),X24))) = k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(k4_xboole_0(X22,X23),X24)))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f232,f218])).
% 47.51/6.36  fof(f218,plain,(
% 47.51/6.36    ( ! [X14,X15,X13,X16] : (k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,X15)))),X16))) = k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16)))))) )),
% 47.51/6.36    inference(backward_demodulation,[],[f123,f158])).
% 47.51/6.36  fof(f158,plain,(
% 47.51/6.36    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5)))) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5))))))) )),
% 47.51/6.36    inference(superposition,[],[f38,f36])).
% 47.51/6.36  fof(f38,plain,(
% 47.51/6.36    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f37,f36])).
% 47.51/6.36  fof(f37,plain,(
% 47.51/6.36    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 47.51/6.36    inference(definition_unfolding,[],[f30,f26,f26,f26,f26])).
% 47.51/6.36  fof(f30,plain,(
% 47.51/6.36    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 47.51/6.36    inference(cnf_transformation,[],[f4])).
% 47.51/6.36  fof(f4,axiom,(
% 47.51/6.36    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 47.51/6.36    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 47.51/6.36  fof(f123,plain,(
% 47.51/6.36    ( ! [X14,X15,X13,X16] : (k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,X15)))),X16))) = k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(X15,X16)))))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f122,f36])).
% 47.51/6.36  fof(f122,plain,(
% 47.51/6.36    ( ! [X14,X15,X13,X16] : (k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,X15)))),X16))) = k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X15,X16)))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f121,f36])).
% 47.51/6.36  fof(f121,plain,(
% 47.51/6.36    ( ! [X14,X15,X13,X16] : (k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X15,X16))) = k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,X15)))),X16)))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f120,f36])).
% 47.51/6.36  fof(f120,plain,(
% 47.51/6.36    ( ! [X14,X15,X13,X16] : (k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X15,X16))) = k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,X15)))))),X16)) )),
% 47.51/6.36    inference(forward_demodulation,[],[f92,f36])).
% 47.51/6.36  fof(f92,plain,(
% 47.51/6.36    ( ! [X14,X15,X13,X16] : (k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X15,X16))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,X15)))),X16)) )),
% 47.51/6.36    inference(superposition,[],[f36,f36])).
% 47.51/6.36  fof(f232,plain,(
% 47.51/6.36    ( ! [X24,X23,X21,X22] : (k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,X23))),X24))) = k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,X23))))),X24)))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f231,f36])).
% 47.51/6.36  fof(f231,plain,(
% 47.51/6.36    ( ! [X24,X23,X21,X22] : (k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,X23))),X24))) = k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,X23))))))),X24)) )),
% 47.51/6.36    inference(forward_demodulation,[],[f162,f36])).
% 47.51/6.36  fof(f162,plain,(
% 47.51/6.36    ( ! [X24,X23,X21,X22] : (k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,X23))),X24))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,X23))))),X24)) )),
% 47.51/6.36    inference(superposition,[],[f36,f38])).
% 47.51/6.36  fof(f1552,plain,(
% 47.51/6.36    ( ! [X39,X37,X38,X40] : (k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,X38)),k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X38,k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(k4_xboole_0(X38,X39),X40))))))) = k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X38,k4_xboole_0(X38,k4_xboole_0(k4_xboole_0(X37,X39),X40)))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f1551,f1548])).
% 47.51/6.36  fof(f1548,plain,(
% 47.51/6.36    ( ! [X35,X33,X36,X34] : (k4_xboole_0(X33,k4_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(k4_xboole_0(X33,X35),X36))))) = k4_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X33,k4_xboole_0(X33,X34))))))),X36)) )),
% 47.51/6.36    inference(forward_demodulation,[],[f1547,f36])).
% 47.51/6.36  fof(f1547,plain,(
% 47.51/6.36    ( ! [X35,X33,X36,X34] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,X34)),k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X33,k4_xboole_0(X33,X34))))),X36) = k4_xboole_0(X33,k4_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(k4_xboole_0(X33,X35),X36)))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f1546,f38])).
% 47.51/6.36  fof(f1546,plain,(
% 47.51/6.36    ( ! [X35,X33,X36,X34] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,X34)),k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X33,k4_xboole_0(X33,X34))))),X36) = k4_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,X34)),k4_xboole_0(X33,k4_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(k4_xboole_0(X33,X35),X36)))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f1545,f248])).
% 47.51/6.36  fof(f1545,plain,(
% 47.51/6.36    ( ! [X35,X33,X36,X34] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,X34)),k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X33,k4_xboole_0(X33,X34))))),X36) = k4_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,X34)),k4_xboole_0(X33,k4_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(k4_xboole_0(X33,X35),X36)))))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f1544,f36])).
% 47.51/6.36  fof(f1544,plain,(
% 47.51/6.36    ( ! [X35,X33,X36,X34] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,X34)),k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X33,k4_xboole_0(X33,X34))))),X36) = k4_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,X34)),k4_xboole_0(X33,k4_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(k4_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(X33,X35))),X36)))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f1415,f36])).
% 47.51/6.36  fof(f1415,plain,(
% 47.51/6.36    ( ! [X35,X33,X36,X34] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,X34)),k4_xboole_0(X35,k4_xboole_0(X35,k4_xboole_0(X33,k4_xboole_0(X33,X34))))),X36) = k4_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,X34)),k4_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,X34)),k4_xboole_0(k4_xboole_0(X34,k4_xboole_0(X34,k4_xboole_0(X33,X35))),X36)))) )),
% 47.51/6.36    inference(superposition,[],[f89,f93])).
% 47.51/6.36  fof(f1551,plain,(
% 47.51/6.36    ( ! [X39,X37,X38,X40] : (k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,X38)),k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X38,k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(k4_xboole_0(X38,X39),X40))))))) = k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X38,k4_xboole_0(X39,k4_xboole_0(X39,k4_xboole_0(X37,k4_xboole_0(X37,X38))))))),X40)) )),
% 47.51/6.36    inference(forward_demodulation,[],[f1550,f36])).
% 47.51/6.36  fof(f1550,plain,(
% 47.51/6.36    ( ! [X39,X37,X38,X40] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,X38)),k4_xboole_0(X39,k4_xboole_0(X39,k4_xboole_0(X37,k4_xboole_0(X37,X38))))),X40) = k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,X38)),k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X38,k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(k4_xboole_0(X38,X39),X40)))))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f1549,f36])).
% 47.51/6.36  fof(f1549,plain,(
% 47.51/6.36    ( ! [X39,X37,X38,X40] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,X38)),k4_xboole_0(X39,k4_xboole_0(X39,k4_xboole_0(X37,k4_xboole_0(X37,X38))))),X40) = k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,X38)),k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X38,k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X38,X39))),X40)))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f1416,f36])).
% 47.51/6.36  fof(f1416,plain,(
% 47.51/6.36    ( ! [X39,X37,X38,X40] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,X38)),k4_xboole_0(X39,k4_xboole_0(X39,k4_xboole_0(X37,k4_xboole_0(X37,X38))))),X40) = k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,X38)),k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,X38)),k4_xboole_0(k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X38,X39))),X40)))) )),
% 47.51/6.36    inference(superposition,[],[f89,f36])).
% 47.51/6.36  fof(f2101,plain,(
% 47.51/6.36    ( ! [X80,X81,X82] : (k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(X80,X82)))) = k5_xboole_0(k4_xboole_0(X80,k4_xboole_0(X81,X82)),k4_xboole_0(X80,k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(k4_xboole_0(X80,X82),k4_xboole_0(X81,X82)))))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f2093,f36])).
% 47.51/6.36  fof(f2093,plain,(
% 47.51/6.36    ( ! [X80,X81,X82] : (k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(X80,X82)))) = k5_xboole_0(k4_xboole_0(X80,k4_xboole_0(X81,X82)),k4_xboole_0(X80,k4_xboole_0(X80,k4_xboole_0(k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(X80,X82))),k4_xboole_0(X81,X82)))))) )),
% 47.51/6.36    inference(backward_demodulation,[],[f880,f2092])).
% 47.51/6.36  fof(f2092,plain,(
% 47.51/6.36    ( ! [X21,X19,X20] : (k4_xboole_0(X19,k4_xboole_0(X19,k4_xboole_0(X21,X20))) = k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X19,X21))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f2091,f809])).
% 47.51/6.36  fof(f809,plain,(
% 47.51/6.36    ( ! [X4,X5,X3] : (k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X4,X5),X3)) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,X5)))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f689,f36])).
% 47.51/6.36  fof(f689,plain,(
% 47.51/6.36    ( ! [X4,X5,X3] : (k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X3)),X5) = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X4,X5),X3))) )),
% 47.51/6.36    inference(superposition,[],[f93,f35])).
% 47.51/6.36  fof(f2091,plain,(
% 47.51/6.36    ( ! [X21,X19,X20] : (k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(k4_xboole_0(X19,X20),X21)) = k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X19,X21))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f2090,f2086])).
% 47.51/6.36  fof(f2086,plain,(
% 47.51/6.36    ( ! [X17,X18,X16] : (k4_xboole_0(k4_xboole_0(X16,X17),X18) = k4_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X16,X18)))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f2056,f20])).
% 47.51/6.36  fof(f2056,plain,(
% 47.51/6.36    ( ! [X17,X18,X16] : (k4_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X16,X18))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X16,X17),k1_xboole_0),X18)) )),
% 47.51/6.36    inference(superposition,[],[f36,f1677])).
% 47.51/6.36  fof(f1677,plain,(
% 47.51/6.36    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)) )),
% 47.51/6.36    inference(forward_demodulation,[],[f1627,f64])).
% 47.51/6.36  fof(f1627,plain,(
% 47.51/6.36    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))) )),
% 47.51/6.36    inference(backward_demodulation,[],[f276,f1622])).
% 47.51/6.36  fof(f276,plain,(
% 47.51/6.36    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))))) )),
% 47.51/6.36    inference(superposition,[],[f73,f35])).
% 47.51/6.36  fof(f2090,plain,(
% 47.51/6.36    ( ! [X21,X19,X20] : (k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(k4_xboole_0(X19,X20),X21)) = k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X19,k4_xboole_0(X19,X21))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f2089,f20])).
% 47.51/6.36  fof(f2089,plain,(
% 47.51/6.36    ( ! [X21,X19,X20] : (k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X19,k4_xboole_0(X19,X21)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X19,X20),k1_xboole_0),k4_xboole_0(k4_xboole_0(X19,X20),X21))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f2088,f1624])).
% 47.51/6.36  fof(f2088,plain,(
% 47.51/6.36    ( ! [X21,X19,X20] : (k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X19,k4_xboole_0(X19,X21)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X19,X20),k1_xboole_0),k4_xboole_0(X19,k4_xboole_0(X19,k4_xboole_0(k4_xboole_0(X19,X20),X21))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f2087,f36])).
% 47.51/6.36  fof(f2087,plain,(
% 47.51/6.36    ( ! [X21,X19,X20] : (k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X19,k4_xboole_0(X19,X21)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X19,X20),k1_xboole_0),k4_xboole_0(k4_xboole_0(X19,k4_xboole_0(X19,k4_xboole_0(X19,X20))),X21))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f2057,f93])).
% 47.51/6.36  fof(f2057,plain,(
% 47.51/6.36    ( ! [X21,X19,X20] : (k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X19,k4_xboole_0(X19,X21)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X19,X20),k1_xboole_0),k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X19,X21))))) )),
% 47.51/6.36    inference(superposition,[],[f38,f1677])).
% 47.51/6.36  fof(f880,plain,(
% 47.51/6.36    ( ! [X80,X81,X82] : (k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(X80,X82)))) = k5_xboole_0(k4_xboole_0(X80,k4_xboole_0(X81,X82)),k4_xboole_0(k4_xboole_0(X80,k4_xboole_0(X81,X82)),k4_xboole_0(X80,k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(X80,X82))))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f734,f36])).
% 47.51/6.36  fof(f734,plain,(
% 47.51/6.36    ( ! [X80,X81,X82] : (k4_xboole_0(X80,k4_xboole_0(k4_xboole_0(X81,k4_xboole_0(X81,X80)),X82)) = k5_xboole_0(k4_xboole_0(X80,k4_xboole_0(X81,X82)),k4_xboole_0(k4_xboole_0(X80,k4_xboole_0(X81,X82)),k4_xboole_0(X80,k4_xboole_0(k4_xboole_0(X81,k4_xboole_0(X81,X80)),X82))))) )),
% 47.51/6.36    inference(superposition,[],[f74,f93])).
% 47.51/6.36  fof(f128,plain,(
% 47.51/6.36    ( ! [X10,X8,X9] : (k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9)))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,X10))))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f98,f36])).
% 47.51/6.36  fof(f98,plain,(
% 47.51/6.36    ( ! [X10,X8,X9] : (k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9)))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X9)),X10))))) )),
% 47.51/6.36    inference(superposition,[],[f36,f35])).
% 47.51/6.36  fof(f32332,plain,(
% 47.51/6.36    ( ! [X331,X332,X330] : (k4_xboole_0(k5_xboole_0(X330,k4_xboole_0(X331,X330)),k4_xboole_0(X332,k4_xboole_0(X331,X330))) = k4_xboole_0(k5_xboole_0(X330,k4_xboole_0(X331,X330)),k4_xboole_0(X330,k4_xboole_0(X330,X332)))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f32331,f1938])).
% 47.51/6.36  fof(f32331,plain,(
% 47.51/6.36    ( ! [X331,X332,X330] : (k4_xboole_0(k5_xboole_0(X330,k4_xboole_0(X331,X330)),k4_xboole_0(X330,k4_xboole_0(k5_xboole_0(X330,k4_xboole_0(X331,X330)),X332))) = k4_xboole_0(k5_xboole_0(X330,k4_xboole_0(X331,X330)),k4_xboole_0(X332,k4_xboole_0(X331,X330)))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f31870,f857])).
% 47.51/6.36  fof(f857,plain,(
% 47.51/6.36    ( ! [X8,X7,X9] : (k4_xboole_0(X7,k4_xboole_0(X8,X9)) = k5_xboole_0(X7,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X7,X9))))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f716,f36])).
% 47.51/6.36  fof(f716,plain,(
% 47.51/6.36    ( ! [X8,X7,X9] : (k4_xboole_0(X7,k4_xboole_0(X8,X9)) = k5_xboole_0(X7,k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,X7)),X9))) )),
% 47.51/6.36    inference(superposition,[],[f31,f93])).
% 47.51/6.36  fof(f31870,plain,(
% 47.51/6.36    ( ! [X331,X332,X330] : (k4_xboole_0(k5_xboole_0(X330,k4_xboole_0(X331,X330)),k4_xboole_0(X330,k4_xboole_0(k5_xboole_0(X330,k4_xboole_0(X331,X330)),X332))) = k5_xboole_0(k5_xboole_0(X330,k4_xboole_0(X331,X330)),k4_xboole_0(X332,k4_xboole_0(X332,k4_xboole_0(k5_xboole_0(X330,k4_xboole_0(X331,X330)),k4_xboole_0(X331,X330)))))) )),
% 47.51/6.36    inference(superposition,[],[f2421,f12686])).
% 47.51/6.36  fof(f15995,plain,(
% 47.51/6.36    k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))))),
% 47.51/6.36    inference(unit_resulting_resolution,[],[f32,f3479])).
% 47.51/6.36  fof(f3479,plain,(
% 47.51/6.36    ( ! [X0,X1] : (k4_xboole_0(X1,X0) != k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) | X0 = X1) )),
% 47.51/6.36    inference(forward_demodulation,[],[f3478,f20])).
% 47.51/6.36  fof(f3478,plain,(
% 47.51/6.36    ( ! [X0,X1] : (k4_xboole_0(X0,k1_xboole_0) = X1 | k4_xboole_0(X1,X0) != k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 47.51/6.36    inference(forward_demodulation,[],[f3477,f65])).
% 47.51/6.36  fof(f3477,plain,(
% 47.51/6.36    ( ! [X0,X1] : (k4_xboole_0(X1,X0) != k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) | k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X1) )),
% 47.51/6.36    inference(forward_demodulation,[],[f3476,f20])).
% 47.51/6.36  fof(f3476,plain,(
% 47.51/6.36    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) != k4_xboole_0(X1,k4_xboole_0(X0,k1_xboole_0)) | k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X1) )),
% 47.51/6.36    inference(forward_demodulation,[],[f3475,f65])).
% 47.51/6.36  fof(f3475,plain,(
% 47.51/6.36    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) != k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X0))) | k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X1) )),
% 47.51/6.36    inference(forward_demodulation,[],[f3388,f1881])).
% 47.51/6.36  fof(f3388,plain,(
% 47.51/6.36    ( ! [X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X0))) != k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) | k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X1) )),
% 47.51/6.36    inference(superposition,[],[f100,f1623])).
% 47.51/6.36  fof(f100,plain,(
% 47.51/6.36    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) != k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 47.51/6.36    inference(superposition,[],[f27,f36])).
% 47.51/6.36  fof(f27,plain,(
% 47.51/6.36    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 47.51/6.36    inference(cnf_transformation,[],[f16])).
% 47.51/6.36  fof(f16,plain,(
% 47.51/6.36    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 47.51/6.36    inference(ennf_transformation,[],[f5])).
% 47.51/6.36  fof(f5,axiom,(
% 47.51/6.36    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 47.51/6.36    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
% 47.51/6.36  fof(f32,plain,(
% 47.51/6.36    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 47.51/6.36    inference(definition_unfolding,[],[f19,f24,f26])).
% 47.51/6.36  fof(f19,plain,(
% 47.51/6.36    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 47.51/6.36    inference(cnf_transformation,[],[f18])).
% 47.51/6.36  fof(f18,plain,(
% 47.51/6.36    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 47.51/6.36    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).
% 47.51/6.36  fof(f17,plain,(
% 47.51/6.36    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 47.51/6.36    introduced(choice_axiom,[])).
% 47.51/6.36  fof(f15,plain,(
% 47.51/6.36    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 47.51/6.36    inference(ennf_transformation,[],[f13])).
% 47.51/6.36  fof(f13,negated_conjecture,(
% 47.51/6.36    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 47.51/6.36    inference(negated_conjecture,[],[f12])).
% 47.51/6.36  fof(f12,conjecture,(
% 47.51/6.36    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 47.51/6.36    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 47.51/6.36  % SZS output end Proof for theBenchmark
% 47.51/6.36  % (23415)------------------------------
% 47.51/6.36  % (23415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 47.51/6.36  % (23415)Termination reason: Refutation
% 47.51/6.36  
% 47.51/6.36  % (23415)Memory used [KB]: 144432
% 47.51/6.36  % (23415)Time elapsed: 5.121 s
% 47.51/6.36  % (23415)------------------------------
% 47.51/6.36  % (23415)------------------------------
% 47.51/6.37  % (23328)Success in time 5.998 s
%------------------------------------------------------------------------------
