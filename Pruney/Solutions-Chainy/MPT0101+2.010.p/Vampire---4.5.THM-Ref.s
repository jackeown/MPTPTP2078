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
% DateTime   : Thu Dec  3 12:31:53 EST 2020

% Result     : Theorem 21.97s
% Output     : Refutation 21.97s
% Verified   : 
% Statistics : Number of formulae       :  244 (44799 expanded)
%              Number of leaves         :   10 (14933 expanded)
%              Depth                    :   47
%              Number of atoms          :  245 (44800 expanded)
%              Number of equality atoms :  244 (44799 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83727,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1044,f83726])).

fof(f83726,plain,(
    ! [X21,X20] : k2_xboole_0(X20,X21) = k5_xboole_0(k3_xboole_0(X20,X21),k5_xboole_0(X20,X21)) ),
    inference(forward_demodulation,[],[f83719,f348])).

fof(f348,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3)) ),
    inference(superposition,[],[f21,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f83719,plain,(
    ! [X21,X20] : k2_xboole_0(k3_xboole_0(X20,X21),k5_xboole_0(X20,X21)) = k5_xboole_0(k3_xboole_0(X20,X21),k5_xboole_0(X20,X21)) ),
    inference(backward_demodulation,[],[f81586,f83715])).

fof(f83715,plain,(
    ! [X125,X126] : k5_xboole_0(X125,X126) = k3_xboole_0(k2_xboole_0(X125,X126),k5_xboole_0(X125,X126)) ),
    inference(forward_demodulation,[],[f83714,f10944])).

fof(f10944,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f38,f6875])).

fof(f6875,plain,(
    ! [X2,X3] : k3_xboole_0(k1_xboole_0,k2_xboole_0(X2,X3)) = k3_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f6874,f3827])).

fof(f3827,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f1290,f3823])).

fof(f3823,plain,(
    ! [X15,X16] : k3_xboole_0(k1_xboole_0,k4_xboole_0(X15,X16)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X15,X16)) ),
    inference(forward_demodulation,[],[f3822,f3607])).

fof(f3607,plain,(
    ! [X3] : k3_xboole_0(k1_xboole_0,X3) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f3606,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f31,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f18,f19])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f3606,plain,(
    ! [X3] : k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f3605,f25])).

fof(f25,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k3_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f24,f19])).

fof(f24,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f18,f18])).

fof(f3605,plain,(
    ! [X3] : k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)) ),
    inference(forward_demodulation,[],[f3582,f3560])).

fof(f3560,plain,(
    ! [X5] : k3_xboole_0(k1_xboole_0,X5) = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X5)) ),
    inference(forward_demodulation,[],[f3559,f32])).

fof(f3559,plain,(
    ! [X5] : k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5)) = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X5)) ),
    inference(forward_demodulation,[],[f3489,f110])).

fof(f110,plain,(
    ! [X10,X9] : k4_xboole_0(k3_xboole_0(X10,X9),X9) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X10,X9)) ),
    inference(forward_demodulation,[],[f109,f16])).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f109,plain,(
    ! [X10,X9] : k4_xboole_0(k3_xboole_0(X10,X9),X9) = k3_xboole_0(k3_xboole_0(X10,X9),k1_xboole_0) ),
    inference(forward_demodulation,[],[f105,f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f18,f15])).

fof(f15,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f105,plain,(
    ! [X10,X9] : k4_xboole_0(k3_xboole_0(X10,X9),X9) = k4_xboole_0(k3_xboole_0(X10,X9),k3_xboole_0(X10,X9)) ),
    inference(superposition,[],[f29,f70])).

fof(f70,plain,(
    ! [X2,X1] : k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f32,f16])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f19,f16])).

fof(f3489,plain,(
    ! [X5] : k4_xboole_0(k3_xboole_0(k1_xboole_0,X5),X5) = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X5)) ),
    inference(superposition,[],[f375,f270])).

fof(f270,plain,(
    ! [X9] : k5_xboole_0(k1_xboole_0,X9) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X9),X9) ),
    inference(superposition,[],[f20,f15])).

fof(f20,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f375,plain,(
    ! [X14,X12,X13] : k4_xboole_0(X12,k2_xboole_0(k4_xboole_0(X12,X13),X14)) = k4_xboole_0(k3_xboole_0(X12,X13),X14) ),
    inference(superposition,[],[f22,f18])).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f3582,plain,(
    ! [X3] : k3_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)) = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3))) ),
    inference(superposition,[],[f3560,f325])).

fof(f325,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(backward_demodulation,[],[f306,f316])).

fof(f316,plain,(
    ! [X0] : k2_xboole_0(k3_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f308,f19])).

fof(f308,plain,(
    ! [X1] : k2_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f270,f17])).

fof(f306,plain,(
    ! [X2] : k2_xboole_0(k3_xboole_0(k1_xboole_0,X2),k4_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f270,f18])).

fof(f3822,plain,(
    ! [X15,X16] : k3_xboole_0(k1_xboole_0,k4_xboole_0(X15,X16)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X15,X16)) ),
    inference(forward_demodulation,[],[f3623,f2397])).

fof(f2397,plain,(
    ! [X6,X7] : k3_xboole_0(k1_xboole_0,k4_xboole_0(X6,X7)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X6),k2_xboole_0(k3_xboole_0(k1_xboole_0,X6),X7)) ),
    inference(forward_demodulation,[],[f2359,f1534])).

fof(f1534,plain,(
    ! [X0,X1] : k3_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) ),
    inference(backward_demodulation,[],[f771,f1533])).

fof(f1533,plain,(
    ! [X0,X1] : k3_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f370,f1532])).

fof(f1532,plain,(
    ! [X0,X1] : k3_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
    inference(forward_demodulation,[],[f1465,f1290])).

fof(f1465,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
    inference(superposition,[],[f370,f17])).

fof(f370,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
    inference(superposition,[],[f22,f23])).

fof(f771,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) ),
    inference(backward_demodulation,[],[f556,f756])).

fof(f756,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f719,f36])).

fof(f36,plain,(
    ! [X5] : k3_xboole_0(X5,X5) = X5 ),
    inference(superposition,[],[f25,f15])).

fof(f719,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f506,f505])).

fof(f505,plain,(
    ! [X2] : k2_xboole_0(k1_xboole_0,X2) = k3_xboole_0(k2_xboole_0(k1_xboole_0,X2),X2) ),
    inference(superposition,[],[f442,f36])).

fof(f442,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k3_xboole_0(X12,k2_xboole_0(k1_xboole_0,X13)) ),
    inference(forward_demodulation,[],[f424,f18])).

fof(f424,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k4_xboole_0(X12,X13)) = k3_xboole_0(X12,k2_xboole_0(k1_xboole_0,X13)) ),
    inference(superposition,[],[f18,f376])).

fof(f376,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k2_xboole_0(k1_xboole_0,X16)) = k4_xboole_0(X15,X16) ),
    inference(superposition,[],[f22,f15])).

fof(f506,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(k2_xboole_0(k1_xboole_0,X4),X3) ),
    inference(superposition,[],[f442,f16])).

fof(f556,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k2_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) ),
    inference(superposition,[],[f22,f443])).

fof(f443,plain,(
    ! [X2] : k3_xboole_0(k1_xboole_0,X2) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X2),X2) ),
    inference(backward_demodulation,[],[f438,f442])).

fof(f438,plain,(
    ! [X2] : k4_xboole_0(k2_xboole_0(k1_xboole_0,X2),X2) = k3_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X2)) ),
    inference(forward_demodulation,[],[f416,f16])).

fof(f416,plain,(
    ! [X2] : k3_xboole_0(k2_xboole_0(k1_xboole_0,X2),k1_xboole_0) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X2),X2) ),
    inference(superposition,[],[f376,f23])).

fof(f2359,plain,(
    ! [X6,X7] : k4_xboole_0(k3_xboole_0(k1_xboole_0,X6),X7) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X6),k2_xboole_0(k3_xboole_0(k1_xboole_0,X6),X7)) ),
    inference(superposition,[],[f372,f90])).

fof(f90,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k3_xboole_0(k3_xboole_0(X5,X6),X5) ),
    inference(forward_demodulation,[],[f82,f36])).

fof(f82,plain,(
    ! [X6,X5] : k3_xboole_0(k3_xboole_0(X5,X6),X5) = k3_xboole_0(k3_xboole_0(X5,X6),k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f68,f32])).

fof(f68,plain,(
    ! [X4,X5] : k3_xboole_0(X4,k3_xboole_0(X5,X4)) = k3_xboole_0(X4,X5) ),
    inference(forward_demodulation,[],[f65,f18])).

fof(f65,plain,(
    ! [X4,X5] : k3_xboole_0(X4,k3_xboole_0(X5,X4)) = k4_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f18,f29])).

fof(f372,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k4_xboole_0(X5,k2_xboole_0(k3_xboole_0(X5,k1_xboole_0),X6)) ),
    inference(superposition,[],[f22,f37])).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(backward_demodulation,[],[f27,f36])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f18,f23])).

fof(f3623,plain,(
    ! [X15,X16] : k4_xboole_0(k1_xboole_0,k2_xboole_0(X15,X16)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X15),k2_xboole_0(k3_xboole_0(k1_xboole_0,X15),X16)) ),
    inference(backward_demodulation,[],[f2402,f3607])).

fof(f2402,plain,(
    ! [X15,X16] : k4_xboole_0(k4_xboole_0(k1_xboole_0,X15),k2_xboole_0(k4_xboole_0(k1_xboole_0,X15),X16)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X15,X16)) ),
    inference(forward_demodulation,[],[f2364,f22])).

fof(f2364,plain,(
    ! [X15,X16] : k4_xboole_0(k4_xboole_0(k1_xboole_0,X15),X16) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X15),k2_xboole_0(k4_xboole_0(k1_xboole_0,X15),X16)) ),
    inference(superposition,[],[f372,f93])).

fof(f93,plain,(
    ! [X10,X9] : k4_xboole_0(X9,X10) = k3_xboole_0(k4_xboole_0(X9,X10),X9) ),
    inference(forward_demodulation,[],[f84,f36])).

fof(f84,plain,(
    ! [X10,X9] : k3_xboole_0(k4_xboole_0(X9,X10),X9) = k3_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,X10)) ),
    inference(superposition,[],[f68,f25])).

fof(f1290,plain,(
    ! [X0,X1] : k3_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f67,f22])).

fof(f67,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X4,X5),X4) = k3_xboole_0(k1_xboole_0,k4_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f66,f16])).

fof(f66,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X4,X5),X4) = k3_xboole_0(k4_xboole_0(X4,X5),k1_xboole_0) ),
    inference(forward_demodulation,[],[f59,f23])).

fof(f59,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X4,X5),X4) = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f29,f25])).

fof(f6874,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X3,X2)) = k3_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f6811,f5159])).

fof(f5159,plain,(
    ! [X28,X29] : k4_xboole_0(X29,k2_xboole_0(X28,k5_xboole_0(X29,X28))) = k3_xboole_0(k1_xboole_0,k5_xboole_0(X29,X28)) ),
    inference(forward_demodulation,[],[f5158,f20])).

fof(f5158,plain,(
    ! [X28,X29] : k3_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(X29,X28),k4_xboole_0(X28,X29))) = k4_xboole_0(X29,k2_xboole_0(X28,k5_xboole_0(X29,X28))) ),
    inference(forward_demodulation,[],[f5104,f22])).

fof(f5104,plain,(
    ! [X28,X29] : k3_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(X29,X28),k4_xboole_0(X28,X29))) = k4_xboole_0(k4_xboole_0(X29,X28),k5_xboole_0(X29,X28)) ),
    inference(superposition,[],[f3827,f271])).

fof(f271,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3)) = k5_xboole_0(X2,X3) ),
    inference(superposition,[],[f20,f17])).

fof(f6811,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X3,X2)) = k4_xboole_0(X2,k2_xboole_0(X3,k5_xboole_0(X2,X3))) ),
    inference(superposition,[],[f397,f1963])).

fof(f1963,plain,(
    ! [X6,X5] : k2_xboole_0(X5,X6) = k2_xboole_0(k3_xboole_0(X6,X5),k5_xboole_0(X6,X5)) ),
    inference(superposition,[],[f1214,f1010])).

fof(f1010,plain,(
    ! [X2,X3] : k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2) ),
    inference(superposition,[],[f271,f20])).

fof(f1214,plain,(
    ! [X6,X5] : k2_xboole_0(k3_xboole_0(X6,X5),k5_xboole_0(X5,X6)) = k2_xboole_0(X5,X6) ),
    inference(superposition,[],[f335,f17])).

fof(f335,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f21,f16])).

fof(f397,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k2_xboole_0(k3_xboole_0(X2,X3),X4)) = k4_xboole_0(X2,k2_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f371,f22])).

fof(f371,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k2_xboole_0(k3_xboole_0(X2,X3),X4)) = k4_xboole_0(k4_xboole_0(X2,X3),X4) ),
    inference(superposition,[],[f22,f19])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f37,f16])).

fof(f83714,plain,(
    ! [X125,X126] : k3_xboole_0(k2_xboole_0(X125,X126),k5_xboole_0(X125,X126)) = k4_xboole_0(k5_xboole_0(X125,X126),k3_xboole_0(k1_xboole_0,k2_xboole_0(X125,X126))) ),
    inference(forward_demodulation,[],[f83713,f4710])).

fof(f4710,plain,(
    ! [X17,X16] : k3_xboole_0(k1_xboole_0,k3_xboole_0(X16,X17)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X16,X17)) ),
    inference(forward_demodulation,[],[f4709,f4701])).

fof(f4701,plain,(
    ! [X8,X7] : k3_xboole_0(k1_xboole_0,k2_xboole_0(X7,X8)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X7,k3_xboole_0(X7,X8))) ),
    inference(forward_demodulation,[],[f4700,f3827])).

fof(f4700,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k2_xboole_0(X8,X7)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X7,k3_xboole_0(X7,X8))) ),
    inference(forward_demodulation,[],[f4665,f22])).

fof(f4665,plain,(
    ! [X8,X7] : k4_xboole_0(k4_xboole_0(X7,X8),X7) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X7,k3_xboole_0(X7,X8))) ),
    inference(superposition,[],[f3824,f19])).

fof(f3824,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X4,X5),X4) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X4,X5)) ),
    inference(backward_demodulation,[],[f67,f3823])).

fof(f4709,plain,(
    ! [X17,X16] : k3_xboole_0(k1_xboole_0,k3_xboole_0(X16,X17)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X16,k3_xboole_0(X16,X17))) ),
    inference(forward_demodulation,[],[f4708,f17])).

fof(f4708,plain,(
    ! [X17,X16] : k3_xboole_0(k1_xboole_0,k3_xboole_0(X16,X17)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(k3_xboole_0(X16,X17),X16)) ),
    inference(forward_demodulation,[],[f4671,f1777])).

fof(f1777,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X0),X0) ),
    inference(superposition,[],[f1556,f16])).

fof(f1556,plain,(
    ! [X11] : k3_xboole_0(k1_xboole_0,X11) = k4_xboole_0(k3_xboole_0(X11,k1_xboole_0),X11) ),
    inference(forward_demodulation,[],[f1555,f1545])).

fof(f1545,plain,(
    ! [X8] : k3_xboole_0(k1_xboole_0,X8) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X8),k5_xboole_0(X8,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1544,f32])).

fof(f1544,plain,(
    ! [X8] : k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X8)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X8)),k5_xboole_0(X8,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1543,f16])).

fof(f1543,plain,(
    ! [X8] : k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X8)) = k4_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,X8),k1_xboole_0),k5_xboole_0(X8,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1471,f110])).

fof(f1471,plain,(
    ! [X8] : k4_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,X8),k1_xboole_0),k5_xboole_0(X8,k1_xboole_0)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X8),X8) ),
    inference(superposition,[],[f370,f890])).

fof(f890,plain,(
    ! [X1] : k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(superposition,[],[f757,f17])).

fof(f757,plain,(
    ! [X1] : k2_xboole_0(k5_xboole_0(X1,k1_xboole_0),k3_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(backward_demodulation,[],[f333,f756])).

fof(f333,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = k2_xboole_0(k5_xboole_0(X1,k1_xboole_0),k3_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f21,f322])).

fof(f322,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f308,f263])).

fof(f263,plain,(
    ! [X9] : k5_xboole_0(X9,k1_xboole_0) = k2_xboole_0(X9,k4_xboole_0(k1_xboole_0,X9)) ),
    inference(superposition,[],[f20,f15])).

fof(f1555,plain,(
    ! [X11] : k4_xboole_0(k3_xboole_0(X11,k1_xboole_0),X11) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X11),k5_xboole_0(X11,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1554,f68])).

fof(f1554,plain,(
    ! [X11] : k4_xboole_0(k3_xboole_0(X11,k1_xboole_0),X11) = k4_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X11,k1_xboole_0)),k5_xboole_0(X11,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1474,f16])).

fof(f1474,plain,(
    ! [X11] : k4_xboole_0(k3_xboole_0(X11,k1_xboole_0),X11) = k4_xboole_0(k3_xboole_0(k3_xboole_0(X11,k1_xboole_0),k1_xboole_0),k5_xboole_0(X11,k1_xboole_0)) ),
    inference(superposition,[],[f370,f1093])).

fof(f1093,plain,(
    ! [X2] : k2_xboole_0(k3_xboole_0(X2,k1_xboole_0),k5_xboole_0(X2,k1_xboole_0)) = X2 ),
    inference(superposition,[],[f882,f17])).

fof(f882,plain,(
    ! [X0] : k2_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[],[f757,f16])).

fof(f4671,plain,(
    ! [X17,X16] : k3_xboole_0(k1_xboole_0,k2_xboole_0(k3_xboole_0(X16,X17),X16)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X16,X17)),k3_xboole_0(X16,X17)) ),
    inference(superposition,[],[f3824,f78])).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f77,f16])).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f75,f23])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X0) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f29,f32])).

fof(f83713,plain,(
    ! [X125,X126] : k3_xboole_0(k2_xboole_0(X125,X126),k5_xboole_0(X125,X126)) = k4_xboole_0(k5_xboole_0(X125,X126),k3_xboole_0(k1_xboole_0,k3_xboole_0(X125,X126))) ),
    inference(forward_demodulation,[],[f83712,f16])).

fof(f83712,plain,(
    ! [X125,X126] : k4_xboole_0(k5_xboole_0(X125,X126),k3_xboole_0(k3_xboole_0(X125,X126),k1_xboole_0)) = k3_xboole_0(k2_xboole_0(X125,X126),k5_xboole_0(X125,X126)) ),
    inference(forward_demodulation,[],[f83460,f81579])).

fof(f81579,plain,(
    ! [X121,X120] : k4_xboole_0(k5_xboole_0(X120,X121),k3_xboole_0(X120,X121)) = k3_xboole_0(k2_xboole_0(X120,X121),k5_xboole_0(X120,X121)) ),
    inference(forward_demodulation,[],[f81578,f16])).

fof(f81578,plain,(
    ! [X121,X120] : k4_xboole_0(k5_xboole_0(X120,X121),k3_xboole_0(X120,X121)) = k3_xboole_0(k5_xboole_0(X120,X121),k2_xboole_0(X120,X121)) ),
    inference(forward_demodulation,[],[f81362,f348])).

fof(f81362,plain,(
    ! [X121,X120] : k3_xboole_0(k5_xboole_0(X120,X121),k2_xboole_0(k3_xboole_0(X120,X121),k5_xboole_0(X120,X121))) = k4_xboole_0(k5_xboole_0(X120,X121),k3_xboole_0(X120,X121)) ),
    inference(superposition,[],[f78180,f78393])).

fof(f78393,plain,(
    ! [X41,X40] : k3_xboole_0(X40,X41) = k4_xboole_0(k3_xboole_0(X40,X41),k5_xboole_0(X40,X41)) ),
    inference(superposition,[],[f78177,f12057])).

fof(f12057,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k4_xboole_0(X2,k5_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f3487,f11955])).

fof(f11955,plain,(
    ! [X2,X1] : k3_xboole_0(X2,X1) = k4_xboole_0(k3_xboole_0(X2,X1),k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f3894,f16])).

fof(f3894,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k4_xboole_0(k3_xboole_0(X12,X13),k4_xboole_0(X12,X13)) ),
    inference(backward_demodulation,[],[f3861,f3893])).

fof(f3893,plain,(
    ! [X14,X15] : k3_xboole_0(X14,X15) = k4_xboole_0(k3_xboole_0(X14,X15),k3_xboole_0(k1_xboole_0,k2_xboole_0(X14,X15))) ),
    inference(forward_demodulation,[],[f3892,f18])).

fof(f3892,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k4_xboole_0(k3_xboole_0(X14,X15),k3_xboole_0(k1_xboole_0,k2_xboole_0(X14,X15))) ),
    inference(forward_demodulation,[],[f3891,f3650])).

fof(f3650,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(backward_demodulation,[],[f322,f3649])).

fof(f3649,plain,(
    ! [X19] : k5_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(forward_demodulation,[],[f3648,f812])).

fof(f812,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f756,f17])).

fof(f3648,plain,(
    ! [X19] : k2_xboole_0(X19,k1_xboole_0) = k5_xboole_0(X19,k1_xboole_0) ),
    inference(forward_demodulation,[],[f3640,f21])).

fof(f3640,plain,(
    ! [X19] : k5_xboole_0(X19,k1_xboole_0) = k2_xboole_0(k5_xboole_0(X19,k1_xboole_0),k3_xboole_0(X19,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f358,f3609])).

fof(f3609,plain,(
    ! [X9] : k5_xboole_0(X9,k1_xboole_0) = k2_xboole_0(X9,k3_xboole_0(k1_xboole_0,X9)) ),
    inference(backward_demodulation,[],[f263,f3607])).

fof(f358,plain,(
    ! [X19] : k2_xboole_0(X19,k3_xboole_0(k1_xboole_0,X19)) = k2_xboole_0(k2_xboole_0(X19,k3_xboole_0(k1_xboole_0,X19)),k3_xboole_0(X19,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f357,f17])).

fof(f357,plain,(
    ! [X19] : k2_xboole_0(k3_xboole_0(k1_xboole_0,X19),X19) = k2_xboole_0(k2_xboole_0(X19,k3_xboole_0(k1_xboole_0,X19)),k3_xboole_0(X19,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f345,f288])).

fof(f288,plain,(
    ! [X4] : k5_xboole_0(k3_xboole_0(k1_xboole_0,X4),X4) = k2_xboole_0(X4,k3_xboole_0(k1_xboole_0,X4)) ),
    inference(forward_demodulation,[],[f287,f17])).

fof(f287,plain,(
    ! [X4] : k5_xboole_0(k3_xboole_0(k1_xboole_0,X4),X4) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X4),X4) ),
    inference(forward_demodulation,[],[f286,f32])).

fof(f286,plain,(
    ! [X4] : k5_xboole_0(k3_xboole_0(k1_xboole_0,X4),X4) = k2_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X4)),X4) ),
    inference(forward_demodulation,[],[f267,f110])).

fof(f267,plain,(
    ! [X4] : k5_xboole_0(k3_xboole_0(k1_xboole_0,X4),X4) = k2_xboole_0(k4_xboole_0(k3_xboole_0(k1_xboole_0,X4),X4),X4) ),
    inference(superposition,[],[f20,f38])).

fof(f345,plain,(
    ! [X19] : k2_xboole_0(k3_xboole_0(k1_xboole_0,X19),X19) = k2_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,X19),X19),k3_xboole_0(X19,k1_xboole_0)) ),
    inference(superposition,[],[f21,f198])).

fof(f198,plain,(
    ! [X7] : k3_xboole_0(X7,k1_xboole_0) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X7),X7) ),
    inference(forward_demodulation,[],[f186,f92])).

fof(f92,plain,(
    ! [X8,X7] : k3_xboole_0(X7,X8) = k3_xboole_0(k3_xboole_0(X8,X7),k3_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f91,f68])).

fof(f91,plain,(
    ! [X8,X7] : k3_xboole_0(X7,k3_xboole_0(X8,X7)) = k3_xboole_0(k3_xboole_0(X8,X7),k3_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f83,f16])).

fof(f83,plain,(
    ! [X8,X7] : k3_xboole_0(k3_xboole_0(X8,X7),X7) = k3_xboole_0(k3_xboole_0(X8,X7),k3_xboole_0(X7,X8)) ),
    inference(superposition,[],[f68,f68])).

fof(f186,plain,(
    ! [X7] : k3_xboole_0(k3_xboole_0(k1_xboole_0,X7),X7) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X7),k3_xboole_0(X7,k1_xboole_0)) ),
    inference(superposition,[],[f68,f56])).

fof(f56,plain,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(forward_demodulation,[],[f55,f23])).

fof(f55,plain,(
    ! [X1] : k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f18,f38])).

fof(f3891,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k5_xboole_0(k1_xboole_0,k4_xboole_0(X14,X15))) = k4_xboole_0(k3_xboole_0(X14,X15),k3_xboole_0(k1_xboole_0,k2_xboole_0(X14,X15))) ),
    inference(forward_demodulation,[],[f3635,f3823])).

fof(f3635,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k5_xboole_0(k1_xboole_0,k4_xboole_0(X14,X15))) = k4_xboole_0(k3_xboole_0(X14,X15),k3_xboole_0(k1_xboole_0,k4_xboole_0(X14,X15))) ),
    inference(backward_demodulation,[],[f3493,f3607])).

fof(f3493,plain,(
    ! [X14,X15] : k4_xboole_0(k3_xboole_0(X14,X15),k4_xboole_0(k1_xboole_0,k4_xboole_0(X14,X15))) = k4_xboole_0(X14,k5_xboole_0(k1_xboole_0,k4_xboole_0(X14,X15))) ),
    inference(superposition,[],[f375,f308])).

fof(f3861,plain,(
    ! [X12,X13] : k4_xboole_0(k3_xboole_0(X12,X13),k4_xboole_0(X12,X13)) = k4_xboole_0(k3_xboole_0(X12,X13),k3_xboole_0(k1_xboole_0,k2_xboole_0(X12,X13))) ),
    inference(backward_demodulation,[],[f3746,f3823])).

fof(f3746,plain,(
    ! [X12,X13] : k4_xboole_0(k3_xboole_0(X12,X13),k4_xboole_0(X12,X13)) = k4_xboole_0(k3_xboole_0(X12,X13),k3_xboole_0(k1_xboole_0,k4_xboole_0(X12,X13))) ),
    inference(backward_demodulation,[],[f3561,f3720])).

fof(f3720,plain,(
    ! [X3] : k3_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X3,X3) ),
    inference(backward_demodulation,[],[f861,f3701])).

fof(f3701,plain,(
    ! [X2] : k3_xboole_0(k1_xboole_0,X2) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X2),k3_xboole_0(k1_xboole_0,X2)) ),
    inference(backward_demodulation,[],[f898,f3650])).

fof(f898,plain,(
    ! [X2] : k3_xboole_0(k1_xboole_0,X2) = k2_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2)),k3_xboole_0(k1_xboole_0,X2)) ),
    inference(forward_demodulation,[],[f884,f322])).

fof(f884,plain,(
    ! [X2] : k3_xboole_0(k1_xboole_0,X2) = k2_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,X2),k1_xboole_0),k3_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f757,f32])).

fof(f861,plain,(
    ! [X3] : k5_xboole_0(X3,X3) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X3),k3_xboole_0(k1_xboole_0,X3)) ),
    inference(superposition,[],[f20,f762])).

fof(f762,plain,(
    ! [X2] : k4_xboole_0(X2,X2) = k3_xboole_0(k1_xboole_0,X2) ),
    inference(backward_demodulation,[],[f443,f756])).

fof(f3561,plain,(
    ! [X12,X13] : k4_xboole_0(k3_xboole_0(X12,X13),k5_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,X13))) = k4_xboole_0(k3_xboole_0(X12,X13),k4_xboole_0(X12,X13)) ),
    inference(forward_demodulation,[],[f3492,f375])).

fof(f3492,plain,(
    ! [X12,X13] : k4_xboole_0(k3_xboole_0(X12,X13),k5_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,X13))) = k4_xboole_0(X12,k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,X13))) ),
    inference(superposition,[],[f375,f361])).

fof(f361,plain,(
    ! [X1] : k2_xboole_0(X1,k5_xboole_0(X1,X1)) = k2_xboole_0(X1,X1) ),
    inference(superposition,[],[f334,f17])).

fof(f334,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k2_xboole_0(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f21,f36])).

fof(f3487,plain,(
    ! [X2,X3] : k4_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = k4_xboole_0(X2,k5_xboole_0(X2,X3)) ),
    inference(superposition,[],[f375,f20])).

fof(f78177,plain,(
    ! [X8,X7] : k4_xboole_0(X7,X8) = k4_xboole_0(k4_xboole_0(X7,X8),X8) ),
    inference(forward_demodulation,[],[f77815,f4749])).

fof(f4749,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(k1_xboole_0,k2_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f4748,f25])).

fof(f4748,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(k1_xboole_0,k2_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f4686,f16])).

fof(f4686,plain,(
    ! [X2,X3] : k3_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(k1_xboole_0,k2_xboole_0(X2,X3))) ),
    inference(superposition,[],[f18,f3824])).

fof(f77815,plain,(
    ! [X8,X7] : k4_xboole_0(k4_xboole_0(X7,X8),X8) = k4_xboole_0(k4_xboole_0(X7,X8),k3_xboole_0(k1_xboole_0,k2_xboole_0(X7,X8))) ),
    inference(superposition,[],[f19,f77409])).

fof(f77409,plain,(
    ! [X0,X1] : k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X0)) = k3_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(forward_demodulation,[],[f77408,f3823])).

fof(f77408,plain,(
    ! [X0,X1] : k3_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) = k3_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(forward_demodulation,[],[f77073,f762])).

fof(f77073,plain,(
    ! [X0,X1] : k3_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f390,f3748])).

fof(f3748,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f3722,f3683])).

fof(f3683,plain,(
    ! [X2] : k2_xboole_0(k3_xboole_0(k1_xboole_0,X2),X2) = X2 ),
    inference(backward_demodulation,[],[f983,f3650])).

fof(f983,plain,(
    ! [X2] : k2_xboole_0(k3_xboole_0(k1_xboole_0,X2),k5_xboole_0(k1_xboole_0,X2)) = X2 ),
    inference(superposition,[],[f878,f17])).

fof(f878,plain,(
    ! [X0] : k2_xboole_0(k5_xboole_0(k1_xboole_0,X0),k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f757,f322])).

fof(f3722,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X0),X0) ),
    inference(backward_demodulation,[],[f334,f3720])).

fof(f390,plain,(
    ! [X14,X15,X16] : k3_xboole_0(k4_xboole_0(X14,X15),X16) = k4_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X14,k2_xboole_0(X15,X16))) ),
    inference(superposition,[],[f18,f22])).

fof(f78180,plain,(
    ! [X12,X11] : k4_xboole_0(X12,k4_xboole_0(X11,X12)) = k3_xboole_0(X12,k2_xboole_0(X11,X12)) ),
    inference(forward_demodulation,[],[f77817,f6753])).

fof(f6753,plain,(
    ! [X6,X7] : k3_xboole_0(X6,k2_xboole_0(X7,X6)) = k4_xboole_0(X6,k3_xboole_0(k1_xboole_0,k2_xboole_0(X7,X6))) ),
    inference(superposition,[],[f18,f4763])).

fof(f4763,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f3831,f17])).

fof(f3831,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f1533,f3823])).

fof(f77817,plain,(
    ! [X12,X11] : k4_xboole_0(X12,k4_xboole_0(X11,X12)) = k4_xboole_0(X12,k3_xboole_0(k1_xboole_0,k2_xboole_0(X11,X12))) ),
    inference(superposition,[],[f29,f77409])).

fof(f83460,plain,(
    ! [X125,X126] : k4_xboole_0(k5_xboole_0(X125,X126),k3_xboole_0(k3_xboole_0(X125,X126),k1_xboole_0)) = k4_xboole_0(k5_xboole_0(X125,X126),k3_xboole_0(X125,X126)) ),
    inference(superposition,[],[f80809,f78393])).

fof(f80809,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k3_xboole_0(X10,k1_xboole_0)) = k4_xboole_0(X9,k4_xboole_0(X10,X9)) ),
    inference(forward_demodulation,[],[f80359,f19])).

fof(f80359,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k4_xboole_0(X10,X9)) = k4_xboole_0(X9,k3_xboole_0(X9,k3_xboole_0(X10,k1_xboole_0))) ),
    inference(superposition,[],[f19,f78181])).

fof(f78181,plain,(
    ! [X15,X16] : k3_xboole_0(X16,k3_xboole_0(X15,k1_xboole_0)) = k3_xboole_0(X16,k4_xboole_0(X15,X16)) ),
    inference(forward_demodulation,[],[f77819,f29706])).

fof(f29706,plain,(
    ! [X24,X25] : k3_xboole_0(X25,k3_xboole_0(X24,k1_xboole_0)) = k3_xboole_0(X25,k3_xboole_0(k1_xboole_0,k2_xboole_0(X24,X25))) ),
    inference(superposition,[],[f68,f29428])).

fof(f29428,plain,(
    ! [X26,X27] : k3_xboole_0(k1_xboole_0,k2_xboole_0(X26,X27)) = k3_xboole_0(k3_xboole_0(X26,k1_xboole_0),X27) ),
    inference(backward_demodulation,[],[f5644,f29304])).

fof(f29304,plain,(
    ! [X2,X3] : k3_xboole_0(k1_xboole_0,k2_xboole_0(X2,X3)) = k5_xboole_0(k3_xboole_0(k1_xboole_0,k2_xboole_0(X2,X3)),k3_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f22182,f3831])).

fof(f22182,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f22181,f5583])).

fof(f5583,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))) ),
    inference(backward_demodulation,[],[f4714,f5581])).

fof(f5581,plain,(
    ! [X17,X18] : k4_xboole_0(X17,X18) = k5_xboole_0(X17,k3_xboole_0(X17,X18)) ),
    inference(forward_demodulation,[],[f5548,f25])).

fof(f5548,plain,(
    ! [X17,X18] : k5_xboole_0(X17,k3_xboole_0(X17,X18)) = k3_xboole_0(X17,k4_xboole_0(X17,X18)) ),
    inference(superposition,[],[f5498,f18])).

fof(f5498,plain,(
    ! [X8,X7] : k3_xboole_0(X7,X8) = k5_xboole_0(X7,k4_xboole_0(X7,X8)) ),
    inference(backward_demodulation,[],[f3829,f5443])).

fof(f5443,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k2_xboole_0(k3_xboole_0(X12,X13),k3_xboole_0(k1_xboole_0,k2_xboole_0(X12,X13))) ),
    inference(superposition,[],[f3681,f4710])).

fof(f3681,plain,(
    ! [X0] : k2_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(backward_demodulation,[],[f878,f3650])).

fof(f3829,plain,(
    ! [X8,X7] : k5_xboole_0(X7,k4_xboole_0(X7,X8)) = k2_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(k1_xboole_0,k2_xboole_0(X7,X8))) ),
    inference(backward_demodulation,[],[f1303,f3823])).

fof(f1303,plain,(
    ! [X8,X7] : k5_xboole_0(X7,k4_xboole_0(X7,X8)) = k2_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(k1_xboole_0,k4_xboole_0(X7,X8))) ),
    inference(backward_demodulation,[],[f281,f1290])).

fof(f281,plain,(
    ! [X8,X7] : k5_xboole_0(X7,k4_xboole_0(X7,X8)) = k2_xboole_0(k3_xboole_0(X7,X8),k4_xboole_0(X7,k2_xboole_0(X8,X7))) ),
    inference(forward_demodulation,[],[f262,f22])).

fof(f262,plain,(
    ! [X8,X7] : k5_xboole_0(X7,k4_xboole_0(X7,X8)) = k2_xboole_0(k3_xboole_0(X7,X8),k4_xboole_0(k4_xboole_0(X7,X8),X7)) ),
    inference(superposition,[],[f20,f18])).

fof(f4714,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))) ),
    inference(backward_demodulation,[],[f275,f4710])).

fof(f275,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f258,f78])).

fof(f258,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k3_xboole_0(X1,X2),X1)) ),
    inference(superposition,[],[f20,f19])).

fof(f22181,plain,(
    ! [X6,X5] : k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(k1_xboole_0,k2_xboole_0(X5,X6))) ),
    inference(forward_demodulation,[],[f22180,f4701])).

fof(f22180,plain,(
    ! [X6,X5] : k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(k1_xboole_0,k2_xboole_0(X5,k3_xboole_0(X5,X6)))) ),
    inference(forward_demodulation,[],[f22179,f5587])).

fof(f5587,plain,(
    ! [X12,X13] : k2_xboole_0(X12,k4_xboole_0(X12,X13)) = k2_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(backward_demodulation,[],[f5502,f5584])).

fof(f5584,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k3_xboole_0(X5,X6)) = k2_xboole_0(k3_xboole_0(X5,X6),k4_xboole_0(X5,X6)) ),
    inference(backward_demodulation,[],[f1239,f5581])).

fof(f1239,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k3_xboole_0(X5,X6)) = k2_xboole_0(k3_xboole_0(X5,X6),k5_xboole_0(X5,k3_xboole_0(X5,X6))) ),
    inference(superposition,[],[f348,f32])).

fof(f5502,plain,(
    ! [X12,X13] : k2_xboole_0(X12,k4_xboole_0(X12,X13)) = k2_xboole_0(k3_xboole_0(X12,X13),k4_xboole_0(X12,X13)) ),
    inference(backward_demodulation,[],[f341,f5498])).

fof(f341,plain,(
    ! [X12,X13] : k2_xboole_0(X12,k4_xboole_0(X12,X13)) = k2_xboole_0(k5_xboole_0(X12,k4_xboole_0(X12,X13)),k4_xboole_0(X12,X13)) ),
    inference(superposition,[],[f21,f25])).

fof(f22179,plain,(
    ! [X6,X5] : k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(k1_xboole_0,k2_xboole_0(X5,k4_xboole_0(X5,X6)))) ),
    inference(forward_demodulation,[],[f22097,f3830])).

fof(f3830,plain,(
    ! [X0,X1] : k4_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f1532,f3823])).

fof(f22097,plain,(
    ! [X6,X5] : k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(k3_xboole_0(X5,k1_xboole_0),k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f20,f15686])).

fof(f15686,plain,(
    ! [X19,X20] : k4_xboole_0(X19,X20) = k4_xboole_0(k4_xboole_0(X19,X20),k3_xboole_0(X19,k1_xboole_0)) ),
    inference(superposition,[],[f7764,f12255])).

fof(f12255,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f12204,f19])).

fof(f12204,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f18,f12057])).

fof(f7764,plain,(
    ! [X8,X7] : k3_xboole_0(X7,X8) = k4_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X7,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f7702,f18])).

fof(f7702,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k4_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X7,k1_xboole_0)) ),
    inference(superposition,[],[f2373,f375])).

fof(f2373,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k4_xboole_0(X5,k2_xboole_0(X6,k3_xboole_0(X5,k1_xboole_0))) ),
    inference(superposition,[],[f372,f17])).

fof(f5644,plain,(
    ! [X26,X27] : k3_xboole_0(k3_xboole_0(X26,k1_xboole_0),X27) = k5_xboole_0(k3_xboole_0(k1_xboole_0,k2_xboole_0(X26,X27)),k3_xboole_0(X26,k1_xboole_0)) ),
    inference(superposition,[],[f5501,f3830])).

fof(f5501,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k5_xboole_0(k4_xboole_0(X8,X9),X8) ),
    inference(backward_demodulation,[],[f1030,f5498])).

fof(f1030,plain,(
    ! [X8,X9] : k5_xboole_0(k4_xboole_0(X8,X9),X8) = k5_xboole_0(X8,k4_xboole_0(X8,X9)) ),
    inference(forward_demodulation,[],[f1029,f281])).

fof(f1029,plain,(
    ! [X8,X9] : k5_xboole_0(k4_xboole_0(X8,X9),X8) = k2_xboole_0(k3_xboole_0(X8,X9),k4_xboole_0(X8,k2_xboole_0(X9,X8))) ),
    inference(forward_demodulation,[],[f998,f22])).

fof(f998,plain,(
    ! [X8,X9] : k5_xboole_0(k4_xboole_0(X8,X9),X8) = k2_xboole_0(k3_xboole_0(X8,X9),k4_xboole_0(k4_xboole_0(X8,X9),X8)) ),
    inference(superposition,[],[f271,f18])).

fof(f77819,plain,(
    ! [X15,X16] : k3_xboole_0(X16,k3_xboole_0(k1_xboole_0,k2_xboole_0(X15,X16))) = k3_xboole_0(X16,k4_xboole_0(X15,X16)) ),
    inference(superposition,[],[f68,f77409])).

fof(f81586,plain,(
    ! [X21,X20] : k5_xboole_0(k3_xboole_0(X20,X21),k5_xboole_0(X20,X21)) = k2_xboole_0(k3_xboole_0(X20,X21),k3_xboole_0(k2_xboole_0(X20,X21),k5_xboole_0(X20,X21))) ),
    inference(backward_demodulation,[],[f81314,f81579])).

fof(f81314,plain,(
    ! [X21,X20] : k5_xboole_0(k3_xboole_0(X20,X21),k5_xboole_0(X20,X21)) = k2_xboole_0(k3_xboole_0(X20,X21),k4_xboole_0(k5_xboole_0(X20,X21),k3_xboole_0(X20,X21))) ),
    inference(superposition,[],[f20,f78393])).

fof(f1044,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f14,f1010])).

fof(f14,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:30:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (18756)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.46  % (18744)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (18749)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (18748)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  % (18742)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (18747)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (18740)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (18751)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (18741)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (18739)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (18752)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (18743)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (18746)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (18753)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (18755)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % (18745)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (18754)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (18750)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.50  % (18750)Refutation not found, incomplete strategy% (18750)------------------------------
% 0.20/0.50  % (18750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (18750)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (18750)Memory used [KB]: 10490
% 0.20/0.50  % (18750)Time elapsed: 0.066 s
% 0.20/0.50  % (18750)------------------------------
% 0.20/0.50  % (18750)------------------------------
% 5.16/1.02  % (18743)Time limit reached!
% 5.16/1.02  % (18743)------------------------------
% 5.16/1.02  % (18743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.16/1.02  % (18743)Termination reason: Time limit
% 5.16/1.02  
% 5.16/1.02  % (18743)Memory used [KB]: 15479
% 5.16/1.02  % (18743)Time elapsed: 0.612 s
% 5.16/1.02  % (18743)------------------------------
% 5.16/1.02  % (18743)------------------------------
% 11.77/1.91  % (18744)Time limit reached!
% 11.77/1.91  % (18744)------------------------------
% 11.77/1.91  % (18744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.77/1.91  % (18744)Termination reason: Time limit
% 11.77/1.91  % (18744)Termination phase: Saturation
% 11.77/1.91  
% 11.77/1.91  % (18744)Memory used [KB]: 47078
% 11.77/1.91  % (18744)Time elapsed: 1.500 s
% 11.77/1.91  % (18744)------------------------------
% 11.77/1.91  % (18744)------------------------------
% 12.45/1.98  % (18745)Time limit reached!
% 12.45/1.98  % (18745)------------------------------
% 12.45/1.98  % (18745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.45/1.98  % (18745)Termination reason: Time limit
% 12.45/1.98  
% 12.45/1.98  % (18745)Memory used [KB]: 29423
% 12.45/1.98  % (18745)Time elapsed: 1.526 s
% 12.45/1.98  % (18745)------------------------------
% 12.45/1.98  % (18745)------------------------------
% 14.18/2.21  % (18741)Time limit reached!
% 14.18/2.21  % (18741)------------------------------
% 14.18/2.21  % (18741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.86/2.22  % (18741)Termination reason: Time limit
% 14.86/2.22  % (18741)Termination phase: Saturation
% 14.86/2.22  
% 14.86/2.22  % (18741)Memory used [KB]: 40425
% 14.86/2.22  % (18741)Time elapsed: 1.800 s
% 14.86/2.22  % (18741)------------------------------
% 14.86/2.22  % (18741)------------------------------
% 17.81/2.61  % (18751)Time limit reached!
% 17.81/2.61  % (18751)------------------------------
% 17.81/2.61  % (18751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.81/2.61  % (18751)Termination reason: Time limit
% 17.81/2.61  
% 17.81/2.61  % (18751)Memory used [KB]: 37867
% 17.81/2.61  % (18751)Time elapsed: 2.207 s
% 17.81/2.61  % (18751)------------------------------
% 17.81/2.61  % (18751)------------------------------
% 21.97/3.12  % (18755)Refutation found. Thanks to Tanya!
% 21.97/3.12  % SZS status Theorem for theBenchmark
% 21.97/3.12  % SZS output start Proof for theBenchmark
% 21.97/3.12  fof(f83727,plain,(
% 21.97/3.12    $false),
% 21.97/3.12    inference(subsumption_resolution,[],[f1044,f83726])).
% 21.97/3.12  fof(f83726,plain,(
% 21.97/3.12    ( ! [X21,X20] : (k2_xboole_0(X20,X21) = k5_xboole_0(k3_xboole_0(X20,X21),k5_xboole_0(X20,X21))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f83719,f348])).
% 21.97/3.12  fof(f348,plain,(
% 21.97/3.12    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3))) )),
% 21.97/3.12    inference(superposition,[],[f21,f17])).
% 21.97/3.12  fof(f17,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 21.97/3.12    inference(cnf_transformation,[],[f1])).
% 21.97/3.12  fof(f1,axiom,(
% 21.97/3.12    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 21.97/3.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 21.97/3.12  fof(f21,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 21.97/3.12    inference(cnf_transformation,[],[f8])).
% 21.97/3.12  fof(f8,axiom,(
% 21.97/3.12    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 21.97/3.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 21.97/3.12  fof(f83719,plain,(
% 21.97/3.12    ( ! [X21,X20] : (k2_xboole_0(k3_xboole_0(X20,X21),k5_xboole_0(X20,X21)) = k5_xboole_0(k3_xboole_0(X20,X21),k5_xboole_0(X20,X21))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f81586,f83715])).
% 21.97/3.12  fof(f83715,plain,(
% 21.97/3.12    ( ! [X125,X126] : (k5_xboole_0(X125,X126) = k3_xboole_0(k2_xboole_0(X125,X126),k5_xboole_0(X125,X126))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f83714,f10944])).
% 21.97/3.12  fof(f10944,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)))) )),
% 21.97/3.12    inference(superposition,[],[f38,f6875])).
% 21.97/3.12  fof(f6875,plain,(
% 21.97/3.12    ( ! [X2,X3] : (k3_xboole_0(k1_xboole_0,k2_xboole_0(X2,X3)) = k3_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f6874,f3827])).
% 21.97/3.12  fof(f3827,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f1290,f3823])).
% 21.97/3.12  fof(f3823,plain,(
% 21.97/3.12    ( ! [X15,X16] : (k3_xboole_0(k1_xboole_0,k4_xboole_0(X15,X16)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X15,X16))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f3822,f3607])).
% 21.97/3.12  fof(f3607,plain,(
% 21.97/3.12    ( ! [X3] : (k3_xboole_0(k1_xboole_0,X3) = k4_xboole_0(k1_xboole_0,X3)) )),
% 21.97/3.12    inference(forward_demodulation,[],[f3606,f32])).
% 21.97/3.12  fof(f32,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f31,f18])).
% 21.97/3.12  fof(f18,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 21.97/3.12    inference(cnf_transformation,[],[f7])).
% 21.97/3.12  fof(f7,axiom,(
% 21.97/3.12    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 21.97/3.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 21.97/3.12  fof(f31,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 21.97/3.12    inference(superposition,[],[f18,f19])).
% 21.97/3.12  fof(f19,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 21.97/3.12    inference(cnf_transformation,[],[f6])).
% 21.97/3.12  fof(f6,axiom,(
% 21.97/3.12    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 21.97/3.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 21.97/3.12  fof(f3606,plain,(
% 21.97/3.12    ( ! [X3] : (k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3)) = k4_xboole_0(k1_xboole_0,X3)) )),
% 21.97/3.12    inference(forward_demodulation,[],[f3605,f25])).
% 21.97/3.12  fof(f25,plain,(
% 21.97/3.12    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k3_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f24,f19])).
% 21.97/3.12  fof(f24,plain,(
% 21.97/3.12    ( ! [X2,X1] : (k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 21.97/3.12    inference(superposition,[],[f18,f18])).
% 21.97/3.12  fof(f3605,plain,(
% 21.97/3.12    ( ! [X3] : (k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f3582,f3560])).
% 21.97/3.12  fof(f3560,plain,(
% 21.97/3.12    ( ! [X5] : (k3_xboole_0(k1_xboole_0,X5) = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X5))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f3559,f32])).
% 21.97/3.12  fof(f3559,plain,(
% 21.97/3.12    ( ! [X5] : (k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5)) = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X5))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f3489,f110])).
% 21.97/3.12  fof(f110,plain,(
% 21.97/3.12    ( ! [X10,X9] : (k4_xboole_0(k3_xboole_0(X10,X9),X9) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X10,X9))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f109,f16])).
% 21.97/3.12  fof(f16,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 21.97/3.12    inference(cnf_transformation,[],[f2])).
% 21.97/3.12  fof(f2,axiom,(
% 21.97/3.12    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 21.97/3.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 21.97/3.12  fof(f109,plain,(
% 21.97/3.12    ( ! [X10,X9] : (k4_xboole_0(k3_xboole_0(X10,X9),X9) = k3_xboole_0(k3_xboole_0(X10,X9),k1_xboole_0)) )),
% 21.97/3.12    inference(forward_demodulation,[],[f105,f23])).
% 21.97/3.12  fof(f23,plain,(
% 21.97/3.12    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 21.97/3.12    inference(superposition,[],[f18,f15])).
% 21.97/3.12  fof(f15,plain,(
% 21.97/3.12    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 21.97/3.12    inference(cnf_transformation,[],[f4])).
% 21.97/3.12  fof(f4,axiom,(
% 21.97/3.12    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 21.97/3.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 21.97/3.12  fof(f105,plain,(
% 21.97/3.12    ( ! [X10,X9] : (k4_xboole_0(k3_xboole_0(X10,X9),X9) = k4_xboole_0(k3_xboole_0(X10,X9),k3_xboole_0(X10,X9))) )),
% 21.97/3.12    inference(superposition,[],[f29,f70])).
% 21.97/3.12  fof(f70,plain,(
% 21.97/3.12    ( ! [X2,X1] : (k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 21.97/3.12    inference(superposition,[],[f32,f16])).
% 21.97/3.12  fof(f29,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 21.97/3.12    inference(superposition,[],[f19,f16])).
% 21.97/3.12  fof(f3489,plain,(
% 21.97/3.12    ( ! [X5] : (k4_xboole_0(k3_xboole_0(k1_xboole_0,X5),X5) = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X5))) )),
% 21.97/3.12    inference(superposition,[],[f375,f270])).
% 21.97/3.12  fof(f270,plain,(
% 21.97/3.12    ( ! [X9] : (k5_xboole_0(k1_xboole_0,X9) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X9),X9)) )),
% 21.97/3.12    inference(superposition,[],[f20,f15])).
% 21.97/3.12  fof(f20,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 21.97/3.12    inference(cnf_transformation,[],[f3])).
% 21.97/3.12  fof(f3,axiom,(
% 21.97/3.12    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 21.97/3.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 21.97/3.12  fof(f375,plain,(
% 21.97/3.12    ( ! [X14,X12,X13] : (k4_xboole_0(X12,k2_xboole_0(k4_xboole_0(X12,X13),X14)) = k4_xboole_0(k3_xboole_0(X12,X13),X14)) )),
% 21.97/3.12    inference(superposition,[],[f22,f18])).
% 21.97/3.12  fof(f22,plain,(
% 21.97/3.12    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 21.97/3.12    inference(cnf_transformation,[],[f5])).
% 21.97/3.12  fof(f5,axiom,(
% 21.97/3.12    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 21.97/3.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 21.97/3.12  fof(f3582,plain,(
% 21.97/3.12    ( ! [X3] : (k3_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)) = k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3)))) )),
% 21.97/3.12    inference(superposition,[],[f3560,f325])).
% 21.97/3.12  fof(f325,plain,(
% 21.97/3.12    ( ! [X2] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f306,f316])).
% 21.97/3.12  fof(f316,plain,(
% 21.97/3.12    ( ! [X0] : (k2_xboole_0(k3_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 21.97/3.12    inference(superposition,[],[f308,f19])).
% 21.97/3.12  fof(f308,plain,(
% 21.97/3.12    ( ! [X1] : (k2_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 21.97/3.12    inference(superposition,[],[f270,f17])).
% 21.97/3.12  fof(f306,plain,(
% 21.97/3.12    ( ! [X2] : (k2_xboole_0(k3_xboole_0(k1_xboole_0,X2),k4_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) )),
% 21.97/3.12    inference(superposition,[],[f270,f18])).
% 21.97/3.12  fof(f3822,plain,(
% 21.97/3.12    ( ! [X15,X16] : (k3_xboole_0(k1_xboole_0,k4_xboole_0(X15,X16)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X15,X16))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f3623,f2397])).
% 21.97/3.12  fof(f2397,plain,(
% 21.97/3.12    ( ! [X6,X7] : (k3_xboole_0(k1_xboole_0,k4_xboole_0(X6,X7)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X6),k2_xboole_0(k3_xboole_0(k1_xboole_0,X6),X7))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f2359,f1534])).
% 21.97/3.12  fof(f1534,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k3_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1)) )),
% 21.97/3.12    inference(backward_demodulation,[],[f771,f1533])).
% 21.97/3.12  fof(f1533,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k3_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f370,f1532])).
% 21.97/3.12  fof(f1532,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k3_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) )),
% 21.97/3.12    inference(forward_demodulation,[],[f1465,f1290])).
% 21.97/3.12  fof(f1465,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) )),
% 21.97/3.12    inference(superposition,[],[f370,f17])).
% 21.97/3.12  fof(f370,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) )),
% 21.97/3.12    inference(superposition,[],[f22,f23])).
% 21.97/3.12  fof(f771,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1)) )),
% 21.97/3.12    inference(backward_demodulation,[],[f556,f756])).
% 21.97/3.12  fof(f756,plain,(
% 21.97/3.12    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 21.97/3.12    inference(forward_demodulation,[],[f719,f36])).
% 21.97/3.12  fof(f36,plain,(
% 21.97/3.12    ( ! [X5] : (k3_xboole_0(X5,X5) = X5) )),
% 21.97/3.12    inference(superposition,[],[f25,f15])).
% 21.97/3.12  fof(f719,plain,(
% 21.97/3.12    ( ! [X0] : (k3_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,X0)) )),
% 21.97/3.12    inference(superposition,[],[f506,f505])).
% 21.97/3.12  fof(f505,plain,(
% 21.97/3.12    ( ! [X2] : (k2_xboole_0(k1_xboole_0,X2) = k3_xboole_0(k2_xboole_0(k1_xboole_0,X2),X2)) )),
% 21.97/3.12    inference(superposition,[],[f442,f36])).
% 21.97/3.12  fof(f442,plain,(
% 21.97/3.12    ( ! [X12,X13] : (k3_xboole_0(X12,X13) = k3_xboole_0(X12,k2_xboole_0(k1_xboole_0,X13))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f424,f18])).
% 21.97/3.12  fof(f424,plain,(
% 21.97/3.12    ( ! [X12,X13] : (k4_xboole_0(X12,k4_xboole_0(X12,X13)) = k3_xboole_0(X12,k2_xboole_0(k1_xboole_0,X13))) )),
% 21.97/3.12    inference(superposition,[],[f18,f376])).
% 21.97/3.12  fof(f376,plain,(
% 21.97/3.12    ( ! [X15,X16] : (k4_xboole_0(X15,k2_xboole_0(k1_xboole_0,X16)) = k4_xboole_0(X15,X16)) )),
% 21.97/3.12    inference(superposition,[],[f22,f15])).
% 21.97/3.12  fof(f506,plain,(
% 21.97/3.12    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(k2_xboole_0(k1_xboole_0,X4),X3)) )),
% 21.97/3.12    inference(superposition,[],[f442,f16])).
% 21.97/3.12  fof(f556,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k2_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1)) )),
% 21.97/3.12    inference(superposition,[],[f22,f443])).
% 21.97/3.12  fof(f443,plain,(
% 21.97/3.12    ( ! [X2] : (k3_xboole_0(k1_xboole_0,X2) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X2),X2)) )),
% 21.97/3.12    inference(backward_demodulation,[],[f438,f442])).
% 21.97/3.12  fof(f438,plain,(
% 21.97/3.12    ( ! [X2] : (k4_xboole_0(k2_xboole_0(k1_xboole_0,X2),X2) = k3_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X2))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f416,f16])).
% 21.97/3.12  fof(f416,plain,(
% 21.97/3.12    ( ! [X2] : (k3_xboole_0(k2_xboole_0(k1_xboole_0,X2),k1_xboole_0) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X2),X2)) )),
% 21.97/3.12    inference(superposition,[],[f376,f23])).
% 21.97/3.12  fof(f2359,plain,(
% 21.97/3.12    ( ! [X6,X7] : (k4_xboole_0(k3_xboole_0(k1_xboole_0,X6),X7) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X6),k2_xboole_0(k3_xboole_0(k1_xboole_0,X6),X7))) )),
% 21.97/3.12    inference(superposition,[],[f372,f90])).
% 21.97/3.12  fof(f90,plain,(
% 21.97/3.12    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k3_xboole_0(k3_xboole_0(X5,X6),X5)) )),
% 21.97/3.12    inference(forward_demodulation,[],[f82,f36])).
% 21.97/3.12  fof(f82,plain,(
% 21.97/3.12    ( ! [X6,X5] : (k3_xboole_0(k3_xboole_0(X5,X6),X5) = k3_xboole_0(k3_xboole_0(X5,X6),k3_xboole_0(X5,X6))) )),
% 21.97/3.12    inference(superposition,[],[f68,f32])).
% 21.97/3.12  fof(f68,plain,(
% 21.97/3.12    ( ! [X4,X5] : (k3_xboole_0(X4,k3_xboole_0(X5,X4)) = k3_xboole_0(X4,X5)) )),
% 21.97/3.12    inference(forward_demodulation,[],[f65,f18])).
% 21.97/3.12  fof(f65,plain,(
% 21.97/3.12    ( ! [X4,X5] : (k3_xboole_0(X4,k3_xboole_0(X5,X4)) = k4_xboole_0(X4,k4_xboole_0(X4,X5))) )),
% 21.97/3.12    inference(superposition,[],[f18,f29])).
% 21.97/3.12  fof(f372,plain,(
% 21.97/3.12    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k4_xboole_0(X5,k2_xboole_0(k3_xboole_0(X5,k1_xboole_0),X6))) )),
% 21.97/3.12    inference(superposition,[],[f22,f37])).
% 21.97/3.12  fof(f37,plain,(
% 21.97/3.12    ( ! [X0] : (k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 21.97/3.12    inference(backward_demodulation,[],[f27,f36])).
% 21.97/3.12  fof(f27,plain,(
% 21.97/3.12    ( ! [X0] : (k3_xboole_0(X0,X0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 21.97/3.12    inference(superposition,[],[f18,f23])).
% 21.97/3.12  fof(f3623,plain,(
% 21.97/3.12    ( ! [X15,X16] : (k4_xboole_0(k1_xboole_0,k2_xboole_0(X15,X16)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X15),k2_xboole_0(k3_xboole_0(k1_xboole_0,X15),X16))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f2402,f3607])).
% 21.97/3.12  fof(f2402,plain,(
% 21.97/3.12    ( ! [X15,X16] : (k4_xboole_0(k4_xboole_0(k1_xboole_0,X15),k2_xboole_0(k4_xboole_0(k1_xboole_0,X15),X16)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X15,X16))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f2364,f22])).
% 21.97/3.12  fof(f2364,plain,(
% 21.97/3.12    ( ! [X15,X16] : (k4_xboole_0(k4_xboole_0(k1_xboole_0,X15),X16) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X15),k2_xboole_0(k4_xboole_0(k1_xboole_0,X15),X16))) )),
% 21.97/3.12    inference(superposition,[],[f372,f93])).
% 21.97/3.12  fof(f93,plain,(
% 21.97/3.12    ( ! [X10,X9] : (k4_xboole_0(X9,X10) = k3_xboole_0(k4_xboole_0(X9,X10),X9)) )),
% 21.97/3.12    inference(forward_demodulation,[],[f84,f36])).
% 21.97/3.12  fof(f84,plain,(
% 21.97/3.12    ( ! [X10,X9] : (k3_xboole_0(k4_xboole_0(X9,X10),X9) = k3_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,X10))) )),
% 21.97/3.12    inference(superposition,[],[f68,f25])).
% 21.97/3.12  fof(f1290,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k3_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 21.97/3.12    inference(superposition,[],[f67,f22])).
% 21.97/3.12  fof(f67,plain,(
% 21.97/3.12    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),X4) = k3_xboole_0(k1_xboole_0,k4_xboole_0(X4,X5))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f66,f16])).
% 21.97/3.12  fof(f66,plain,(
% 21.97/3.12    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),X4) = k3_xboole_0(k4_xboole_0(X4,X5),k1_xboole_0)) )),
% 21.97/3.12    inference(forward_demodulation,[],[f59,f23])).
% 21.97/3.12  fof(f59,plain,(
% 21.97/3.12    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),X4) = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5))) )),
% 21.97/3.12    inference(superposition,[],[f29,f25])).
% 21.97/3.12  fof(f6874,plain,(
% 21.97/3.12    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X3,X2)) = k3_xboole_0(k1_xboole_0,k5_xboole_0(X2,X3))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f6811,f5159])).
% 21.97/3.12  fof(f5159,plain,(
% 21.97/3.12    ( ! [X28,X29] : (k4_xboole_0(X29,k2_xboole_0(X28,k5_xboole_0(X29,X28))) = k3_xboole_0(k1_xboole_0,k5_xboole_0(X29,X28))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f5158,f20])).
% 21.97/3.12  fof(f5158,plain,(
% 21.97/3.12    ( ! [X28,X29] : (k3_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(X29,X28),k4_xboole_0(X28,X29))) = k4_xboole_0(X29,k2_xboole_0(X28,k5_xboole_0(X29,X28)))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f5104,f22])).
% 21.97/3.12  fof(f5104,plain,(
% 21.97/3.12    ( ! [X28,X29] : (k3_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(X29,X28),k4_xboole_0(X28,X29))) = k4_xboole_0(k4_xboole_0(X29,X28),k5_xboole_0(X29,X28))) )),
% 21.97/3.12    inference(superposition,[],[f3827,f271])).
% 21.97/3.12  fof(f271,plain,(
% 21.97/3.12    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3)) = k5_xboole_0(X2,X3)) )),
% 21.97/3.12    inference(superposition,[],[f20,f17])).
% 21.97/3.12  fof(f6811,plain,(
% 21.97/3.12    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X3,X2)) = k4_xboole_0(X2,k2_xboole_0(X3,k5_xboole_0(X2,X3)))) )),
% 21.97/3.12    inference(superposition,[],[f397,f1963])).
% 21.97/3.12  fof(f1963,plain,(
% 21.97/3.12    ( ! [X6,X5] : (k2_xboole_0(X5,X6) = k2_xboole_0(k3_xboole_0(X6,X5),k5_xboole_0(X6,X5))) )),
% 21.97/3.12    inference(superposition,[],[f1214,f1010])).
% 21.97/3.12  fof(f1010,plain,(
% 21.97/3.12    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k5_xboole_0(X3,X2)) )),
% 21.97/3.12    inference(superposition,[],[f271,f20])).
% 21.97/3.12  fof(f1214,plain,(
% 21.97/3.12    ( ! [X6,X5] : (k2_xboole_0(k3_xboole_0(X6,X5),k5_xboole_0(X5,X6)) = k2_xboole_0(X5,X6)) )),
% 21.97/3.12    inference(superposition,[],[f335,f17])).
% 21.97/3.12  fof(f335,plain,(
% 21.97/3.12    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X2,X1))) )),
% 21.97/3.12    inference(superposition,[],[f21,f16])).
% 21.97/3.12  fof(f397,plain,(
% 21.97/3.12    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k2_xboole_0(k3_xboole_0(X2,X3),X4)) = k4_xboole_0(X2,k2_xboole_0(X3,X4))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f371,f22])).
% 21.97/3.12  fof(f371,plain,(
% 21.97/3.12    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k2_xboole_0(k3_xboole_0(X2,X3),X4)) = k4_xboole_0(k4_xboole_0(X2,X3),X4)) )),
% 21.97/3.12    inference(superposition,[],[f22,f19])).
% 21.97/3.12  fof(f38,plain,(
% 21.97/3.12    ( ! [X0] : (k4_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0) )),
% 21.97/3.12    inference(superposition,[],[f37,f16])).
% 21.97/3.12  fof(f83714,plain,(
% 21.97/3.12    ( ! [X125,X126] : (k3_xboole_0(k2_xboole_0(X125,X126),k5_xboole_0(X125,X126)) = k4_xboole_0(k5_xboole_0(X125,X126),k3_xboole_0(k1_xboole_0,k2_xboole_0(X125,X126)))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f83713,f4710])).
% 21.97/3.12  fof(f4710,plain,(
% 21.97/3.12    ( ! [X17,X16] : (k3_xboole_0(k1_xboole_0,k3_xboole_0(X16,X17)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X16,X17))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f4709,f4701])).
% 21.97/3.12  fof(f4701,plain,(
% 21.97/3.12    ( ! [X8,X7] : (k3_xboole_0(k1_xboole_0,k2_xboole_0(X7,X8)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X7,k3_xboole_0(X7,X8)))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f4700,f3827])).
% 21.97/3.12  fof(f4700,plain,(
% 21.97/3.12    ( ! [X8,X7] : (k4_xboole_0(X7,k2_xboole_0(X8,X7)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X7,k3_xboole_0(X7,X8)))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f4665,f22])).
% 21.97/3.12  fof(f4665,plain,(
% 21.97/3.12    ( ! [X8,X7] : (k4_xboole_0(k4_xboole_0(X7,X8),X7) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X7,k3_xboole_0(X7,X8)))) )),
% 21.97/3.12    inference(superposition,[],[f3824,f19])).
% 21.97/3.12  fof(f3824,plain,(
% 21.97/3.12    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),X4) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X4,X5))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f67,f3823])).
% 21.97/3.12  fof(f4709,plain,(
% 21.97/3.12    ( ! [X17,X16] : (k3_xboole_0(k1_xboole_0,k3_xboole_0(X16,X17)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X16,k3_xboole_0(X16,X17)))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f4708,f17])).
% 21.97/3.12  fof(f4708,plain,(
% 21.97/3.12    ( ! [X17,X16] : (k3_xboole_0(k1_xboole_0,k3_xboole_0(X16,X17)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(k3_xboole_0(X16,X17),X16))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f4671,f1777])).
% 21.97/3.12  fof(f1777,plain,(
% 21.97/3.12    ( ! [X0] : (k3_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X0),X0)) )),
% 21.97/3.12    inference(superposition,[],[f1556,f16])).
% 21.97/3.12  fof(f1556,plain,(
% 21.97/3.12    ( ! [X11] : (k3_xboole_0(k1_xboole_0,X11) = k4_xboole_0(k3_xboole_0(X11,k1_xboole_0),X11)) )),
% 21.97/3.12    inference(forward_demodulation,[],[f1555,f1545])).
% 21.97/3.12  fof(f1545,plain,(
% 21.97/3.12    ( ! [X8] : (k3_xboole_0(k1_xboole_0,X8) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X8),k5_xboole_0(X8,k1_xboole_0))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f1544,f32])).
% 21.97/3.12  fof(f1544,plain,(
% 21.97/3.12    ( ! [X8] : (k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X8)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X8)),k5_xboole_0(X8,k1_xboole_0))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f1543,f16])).
% 21.97/3.12  fof(f1543,plain,(
% 21.97/3.12    ( ! [X8] : (k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X8)) = k4_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,X8),k1_xboole_0),k5_xboole_0(X8,k1_xboole_0))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f1471,f110])).
% 21.97/3.12  fof(f1471,plain,(
% 21.97/3.12    ( ! [X8] : (k4_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,X8),k1_xboole_0),k5_xboole_0(X8,k1_xboole_0)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X8),X8)) )),
% 21.97/3.12    inference(superposition,[],[f370,f890])).
% 21.97/3.12  fof(f890,plain,(
% 21.97/3.12    ( ! [X1] : (k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,k1_xboole_0)) = X1) )),
% 21.97/3.12    inference(superposition,[],[f757,f17])).
% 21.97/3.12  fof(f757,plain,(
% 21.97/3.12    ( ! [X1] : (k2_xboole_0(k5_xboole_0(X1,k1_xboole_0),k3_xboole_0(k1_xboole_0,X1)) = X1) )),
% 21.97/3.12    inference(backward_demodulation,[],[f333,f756])).
% 21.97/3.12  fof(f333,plain,(
% 21.97/3.12    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = k2_xboole_0(k5_xboole_0(X1,k1_xboole_0),k3_xboole_0(k1_xboole_0,X1))) )),
% 21.97/3.12    inference(superposition,[],[f21,f322])).
% 21.97/3.12  fof(f322,plain,(
% 21.97/3.12    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X1)) )),
% 21.97/3.12    inference(superposition,[],[f308,f263])).
% 21.97/3.12  fof(f263,plain,(
% 21.97/3.12    ( ! [X9] : (k5_xboole_0(X9,k1_xboole_0) = k2_xboole_0(X9,k4_xboole_0(k1_xboole_0,X9))) )),
% 21.97/3.12    inference(superposition,[],[f20,f15])).
% 21.97/3.12  fof(f1555,plain,(
% 21.97/3.12    ( ! [X11] : (k4_xboole_0(k3_xboole_0(X11,k1_xboole_0),X11) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X11),k5_xboole_0(X11,k1_xboole_0))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f1554,f68])).
% 21.97/3.12  fof(f1554,plain,(
% 21.97/3.12    ( ! [X11] : (k4_xboole_0(k3_xboole_0(X11,k1_xboole_0),X11) = k4_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X11,k1_xboole_0)),k5_xboole_0(X11,k1_xboole_0))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f1474,f16])).
% 21.97/3.12  fof(f1474,plain,(
% 21.97/3.12    ( ! [X11] : (k4_xboole_0(k3_xboole_0(X11,k1_xboole_0),X11) = k4_xboole_0(k3_xboole_0(k3_xboole_0(X11,k1_xboole_0),k1_xboole_0),k5_xboole_0(X11,k1_xboole_0))) )),
% 21.97/3.12    inference(superposition,[],[f370,f1093])).
% 21.97/3.12  fof(f1093,plain,(
% 21.97/3.12    ( ! [X2] : (k2_xboole_0(k3_xboole_0(X2,k1_xboole_0),k5_xboole_0(X2,k1_xboole_0)) = X2) )),
% 21.97/3.12    inference(superposition,[],[f882,f17])).
% 21.97/3.12  fof(f882,plain,(
% 21.97/3.12    ( ! [X0] : (k2_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 21.97/3.12    inference(superposition,[],[f757,f16])).
% 21.97/3.12  fof(f4671,plain,(
% 21.97/3.12    ( ! [X17,X16] : (k3_xboole_0(k1_xboole_0,k2_xboole_0(k3_xboole_0(X16,X17),X16)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X16,X17)),k3_xboole_0(X16,X17))) )),
% 21.97/3.12    inference(superposition,[],[f3824,f78])).
% 21.97/3.12  fof(f78,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f77,f16])).
% 21.97/3.12  fof(f77,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0)) )),
% 21.97/3.12    inference(forward_demodulation,[],[f75,f23])).
% 21.97/3.12  fof(f75,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X0) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 21.97/3.12    inference(superposition,[],[f29,f32])).
% 21.97/3.12  fof(f83713,plain,(
% 21.97/3.12    ( ! [X125,X126] : (k3_xboole_0(k2_xboole_0(X125,X126),k5_xboole_0(X125,X126)) = k4_xboole_0(k5_xboole_0(X125,X126),k3_xboole_0(k1_xboole_0,k3_xboole_0(X125,X126)))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f83712,f16])).
% 21.97/3.12  fof(f83712,plain,(
% 21.97/3.12    ( ! [X125,X126] : (k4_xboole_0(k5_xboole_0(X125,X126),k3_xboole_0(k3_xboole_0(X125,X126),k1_xboole_0)) = k3_xboole_0(k2_xboole_0(X125,X126),k5_xboole_0(X125,X126))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f83460,f81579])).
% 21.97/3.12  fof(f81579,plain,(
% 21.97/3.12    ( ! [X121,X120] : (k4_xboole_0(k5_xboole_0(X120,X121),k3_xboole_0(X120,X121)) = k3_xboole_0(k2_xboole_0(X120,X121),k5_xboole_0(X120,X121))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f81578,f16])).
% 21.97/3.12  fof(f81578,plain,(
% 21.97/3.12    ( ! [X121,X120] : (k4_xboole_0(k5_xboole_0(X120,X121),k3_xboole_0(X120,X121)) = k3_xboole_0(k5_xboole_0(X120,X121),k2_xboole_0(X120,X121))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f81362,f348])).
% 21.97/3.12  fof(f81362,plain,(
% 21.97/3.12    ( ! [X121,X120] : (k3_xboole_0(k5_xboole_0(X120,X121),k2_xboole_0(k3_xboole_0(X120,X121),k5_xboole_0(X120,X121))) = k4_xboole_0(k5_xboole_0(X120,X121),k3_xboole_0(X120,X121))) )),
% 21.97/3.12    inference(superposition,[],[f78180,f78393])).
% 21.97/3.12  fof(f78393,plain,(
% 21.97/3.12    ( ! [X41,X40] : (k3_xboole_0(X40,X41) = k4_xboole_0(k3_xboole_0(X40,X41),k5_xboole_0(X40,X41))) )),
% 21.97/3.12    inference(superposition,[],[f78177,f12057])).
% 21.97/3.12  fof(f12057,plain,(
% 21.97/3.12    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k4_xboole_0(X2,k5_xboole_0(X2,X3))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f3487,f11955])).
% 21.97/3.12  fof(f11955,plain,(
% 21.97/3.12    ( ! [X2,X1] : (k3_xboole_0(X2,X1) = k4_xboole_0(k3_xboole_0(X2,X1),k4_xboole_0(X1,X2))) )),
% 21.97/3.12    inference(superposition,[],[f3894,f16])).
% 21.97/3.12  fof(f3894,plain,(
% 21.97/3.12    ( ! [X12,X13] : (k3_xboole_0(X12,X13) = k4_xboole_0(k3_xboole_0(X12,X13),k4_xboole_0(X12,X13))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f3861,f3893])).
% 21.97/3.12  fof(f3893,plain,(
% 21.97/3.12    ( ! [X14,X15] : (k3_xboole_0(X14,X15) = k4_xboole_0(k3_xboole_0(X14,X15),k3_xboole_0(k1_xboole_0,k2_xboole_0(X14,X15)))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f3892,f18])).
% 21.97/3.12  fof(f3892,plain,(
% 21.97/3.12    ( ! [X14,X15] : (k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k4_xboole_0(k3_xboole_0(X14,X15),k3_xboole_0(k1_xboole_0,k2_xboole_0(X14,X15)))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f3891,f3650])).
% 21.97/3.12  fof(f3650,plain,(
% 21.97/3.12    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 21.97/3.12    inference(backward_demodulation,[],[f322,f3649])).
% 21.97/3.12  fof(f3649,plain,(
% 21.97/3.12    ( ! [X19] : (k5_xboole_0(X19,k1_xboole_0) = X19) )),
% 21.97/3.12    inference(forward_demodulation,[],[f3648,f812])).
% 21.97/3.12  fof(f812,plain,(
% 21.97/3.12    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 21.97/3.12    inference(superposition,[],[f756,f17])).
% 21.97/3.12  fof(f3648,plain,(
% 21.97/3.12    ( ! [X19] : (k2_xboole_0(X19,k1_xboole_0) = k5_xboole_0(X19,k1_xboole_0)) )),
% 21.97/3.12    inference(forward_demodulation,[],[f3640,f21])).
% 21.97/3.12  fof(f3640,plain,(
% 21.97/3.12    ( ! [X19] : (k5_xboole_0(X19,k1_xboole_0) = k2_xboole_0(k5_xboole_0(X19,k1_xboole_0),k3_xboole_0(X19,k1_xboole_0))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f358,f3609])).
% 21.97/3.12  fof(f3609,plain,(
% 21.97/3.12    ( ! [X9] : (k5_xboole_0(X9,k1_xboole_0) = k2_xboole_0(X9,k3_xboole_0(k1_xboole_0,X9))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f263,f3607])).
% 21.97/3.12  fof(f358,plain,(
% 21.97/3.12    ( ! [X19] : (k2_xboole_0(X19,k3_xboole_0(k1_xboole_0,X19)) = k2_xboole_0(k2_xboole_0(X19,k3_xboole_0(k1_xboole_0,X19)),k3_xboole_0(X19,k1_xboole_0))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f357,f17])).
% 21.97/3.12  fof(f357,plain,(
% 21.97/3.12    ( ! [X19] : (k2_xboole_0(k3_xboole_0(k1_xboole_0,X19),X19) = k2_xboole_0(k2_xboole_0(X19,k3_xboole_0(k1_xboole_0,X19)),k3_xboole_0(X19,k1_xboole_0))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f345,f288])).
% 21.97/3.12  fof(f288,plain,(
% 21.97/3.12    ( ! [X4] : (k5_xboole_0(k3_xboole_0(k1_xboole_0,X4),X4) = k2_xboole_0(X4,k3_xboole_0(k1_xboole_0,X4))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f287,f17])).
% 21.97/3.12  fof(f287,plain,(
% 21.97/3.12    ( ! [X4] : (k5_xboole_0(k3_xboole_0(k1_xboole_0,X4),X4) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X4),X4)) )),
% 21.97/3.12    inference(forward_demodulation,[],[f286,f32])).
% 21.97/3.12  fof(f286,plain,(
% 21.97/3.12    ( ! [X4] : (k5_xboole_0(k3_xboole_0(k1_xboole_0,X4),X4) = k2_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X4)),X4)) )),
% 21.97/3.12    inference(forward_demodulation,[],[f267,f110])).
% 21.97/3.12  fof(f267,plain,(
% 21.97/3.12    ( ! [X4] : (k5_xboole_0(k3_xboole_0(k1_xboole_0,X4),X4) = k2_xboole_0(k4_xboole_0(k3_xboole_0(k1_xboole_0,X4),X4),X4)) )),
% 21.97/3.12    inference(superposition,[],[f20,f38])).
% 21.97/3.12  fof(f345,plain,(
% 21.97/3.12    ( ! [X19] : (k2_xboole_0(k3_xboole_0(k1_xboole_0,X19),X19) = k2_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,X19),X19),k3_xboole_0(X19,k1_xboole_0))) )),
% 21.97/3.12    inference(superposition,[],[f21,f198])).
% 21.97/3.12  fof(f198,plain,(
% 21.97/3.12    ( ! [X7] : (k3_xboole_0(X7,k1_xboole_0) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X7),X7)) )),
% 21.97/3.12    inference(forward_demodulation,[],[f186,f92])).
% 21.97/3.12  fof(f92,plain,(
% 21.97/3.12    ( ! [X8,X7] : (k3_xboole_0(X7,X8) = k3_xboole_0(k3_xboole_0(X8,X7),k3_xboole_0(X7,X8))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f91,f68])).
% 21.97/3.12  fof(f91,plain,(
% 21.97/3.12    ( ! [X8,X7] : (k3_xboole_0(X7,k3_xboole_0(X8,X7)) = k3_xboole_0(k3_xboole_0(X8,X7),k3_xboole_0(X7,X8))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f83,f16])).
% 21.97/3.12  fof(f83,plain,(
% 21.97/3.12    ( ! [X8,X7] : (k3_xboole_0(k3_xboole_0(X8,X7),X7) = k3_xboole_0(k3_xboole_0(X8,X7),k3_xboole_0(X7,X8))) )),
% 21.97/3.12    inference(superposition,[],[f68,f68])).
% 21.97/3.12  fof(f186,plain,(
% 21.97/3.12    ( ! [X7] : (k3_xboole_0(k3_xboole_0(k1_xboole_0,X7),X7) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X7),k3_xboole_0(X7,k1_xboole_0))) )),
% 21.97/3.12    inference(superposition,[],[f68,f56])).
% 21.97/3.12  fof(f56,plain,(
% 21.97/3.12    ( ! [X1] : (k3_xboole_0(X1,k1_xboole_0) = k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f55,f23])).
% 21.97/3.12  fof(f55,plain,(
% 21.97/3.12    ( ! [X1] : (k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X1,X1)) )),
% 21.97/3.12    inference(superposition,[],[f18,f38])).
% 21.97/3.12  fof(f3891,plain,(
% 21.97/3.12    ( ! [X14,X15] : (k4_xboole_0(X14,k5_xboole_0(k1_xboole_0,k4_xboole_0(X14,X15))) = k4_xboole_0(k3_xboole_0(X14,X15),k3_xboole_0(k1_xboole_0,k2_xboole_0(X14,X15)))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f3635,f3823])).
% 21.97/3.12  fof(f3635,plain,(
% 21.97/3.12    ( ! [X14,X15] : (k4_xboole_0(X14,k5_xboole_0(k1_xboole_0,k4_xboole_0(X14,X15))) = k4_xboole_0(k3_xboole_0(X14,X15),k3_xboole_0(k1_xboole_0,k4_xboole_0(X14,X15)))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f3493,f3607])).
% 21.97/3.12  fof(f3493,plain,(
% 21.97/3.12    ( ! [X14,X15] : (k4_xboole_0(k3_xboole_0(X14,X15),k4_xboole_0(k1_xboole_0,k4_xboole_0(X14,X15))) = k4_xboole_0(X14,k5_xboole_0(k1_xboole_0,k4_xboole_0(X14,X15)))) )),
% 21.97/3.12    inference(superposition,[],[f375,f308])).
% 21.97/3.12  fof(f3861,plain,(
% 21.97/3.12    ( ! [X12,X13] : (k4_xboole_0(k3_xboole_0(X12,X13),k4_xboole_0(X12,X13)) = k4_xboole_0(k3_xboole_0(X12,X13),k3_xboole_0(k1_xboole_0,k2_xboole_0(X12,X13)))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f3746,f3823])).
% 21.97/3.12  fof(f3746,plain,(
% 21.97/3.12    ( ! [X12,X13] : (k4_xboole_0(k3_xboole_0(X12,X13),k4_xboole_0(X12,X13)) = k4_xboole_0(k3_xboole_0(X12,X13),k3_xboole_0(k1_xboole_0,k4_xboole_0(X12,X13)))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f3561,f3720])).
% 21.97/3.12  fof(f3720,plain,(
% 21.97/3.12    ( ! [X3] : (k3_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X3,X3)) )),
% 21.97/3.12    inference(backward_demodulation,[],[f861,f3701])).
% 21.97/3.12  fof(f3701,plain,(
% 21.97/3.12    ( ! [X2] : (k3_xboole_0(k1_xboole_0,X2) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X2),k3_xboole_0(k1_xboole_0,X2))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f898,f3650])).
% 21.97/3.12  fof(f898,plain,(
% 21.97/3.12    ( ! [X2] : (k3_xboole_0(k1_xboole_0,X2) = k2_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2)),k3_xboole_0(k1_xboole_0,X2))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f884,f322])).
% 21.97/3.12  fof(f884,plain,(
% 21.97/3.12    ( ! [X2] : (k3_xboole_0(k1_xboole_0,X2) = k2_xboole_0(k5_xboole_0(k3_xboole_0(k1_xboole_0,X2),k1_xboole_0),k3_xboole_0(k1_xboole_0,X2))) )),
% 21.97/3.12    inference(superposition,[],[f757,f32])).
% 21.97/3.12  fof(f861,plain,(
% 21.97/3.12    ( ! [X3] : (k5_xboole_0(X3,X3) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X3),k3_xboole_0(k1_xboole_0,X3))) )),
% 21.97/3.12    inference(superposition,[],[f20,f762])).
% 21.97/3.12  fof(f762,plain,(
% 21.97/3.12    ( ! [X2] : (k4_xboole_0(X2,X2) = k3_xboole_0(k1_xboole_0,X2)) )),
% 21.97/3.12    inference(backward_demodulation,[],[f443,f756])).
% 21.97/3.12  fof(f3561,plain,(
% 21.97/3.12    ( ! [X12,X13] : (k4_xboole_0(k3_xboole_0(X12,X13),k5_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,X13))) = k4_xboole_0(k3_xboole_0(X12,X13),k4_xboole_0(X12,X13))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f3492,f375])).
% 21.97/3.12  fof(f3492,plain,(
% 21.97/3.12    ( ! [X12,X13] : (k4_xboole_0(k3_xboole_0(X12,X13),k5_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,X13))) = k4_xboole_0(X12,k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,X13)))) )),
% 21.97/3.12    inference(superposition,[],[f375,f361])).
% 21.97/3.12  fof(f361,plain,(
% 21.97/3.12    ( ! [X1] : (k2_xboole_0(X1,k5_xboole_0(X1,X1)) = k2_xboole_0(X1,X1)) )),
% 21.97/3.12    inference(superposition,[],[f334,f17])).
% 21.97/3.12  fof(f334,plain,(
% 21.97/3.12    ( ! [X0] : (k2_xboole_0(X0,X0) = k2_xboole_0(k5_xboole_0(X0,X0),X0)) )),
% 21.97/3.12    inference(superposition,[],[f21,f36])).
% 21.97/3.12  fof(f3487,plain,(
% 21.97/3.12    ( ! [X2,X3] : (k4_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = k4_xboole_0(X2,k5_xboole_0(X2,X3))) )),
% 21.97/3.12    inference(superposition,[],[f375,f20])).
% 21.97/3.12  fof(f78177,plain,(
% 21.97/3.12    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k4_xboole_0(k4_xboole_0(X7,X8),X8)) )),
% 21.97/3.12    inference(forward_demodulation,[],[f77815,f4749])).
% 21.97/3.12  fof(f4749,plain,(
% 21.97/3.12    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(k1_xboole_0,k2_xboole_0(X2,X3)))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f4748,f25])).
% 21.97/3.12  fof(f4748,plain,(
% 21.97/3.12    ( ! [X2,X3] : (k3_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(k1_xboole_0,k2_xboole_0(X2,X3)))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f4686,f16])).
% 21.97/3.12  fof(f4686,plain,(
% 21.97/3.12    ( ! [X2,X3] : (k3_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(k1_xboole_0,k2_xboole_0(X2,X3)))) )),
% 21.97/3.12    inference(superposition,[],[f18,f3824])).
% 21.97/3.12  fof(f77815,plain,(
% 21.97/3.12    ( ! [X8,X7] : (k4_xboole_0(k4_xboole_0(X7,X8),X8) = k4_xboole_0(k4_xboole_0(X7,X8),k3_xboole_0(k1_xboole_0,k2_xboole_0(X7,X8)))) )),
% 21.97/3.12    inference(superposition,[],[f19,f77409])).
% 21.97/3.12  fof(f77409,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X0)) = k3_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 21.97/3.12    inference(forward_demodulation,[],[f77408,f3823])).
% 21.97/3.12  fof(f77408,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k3_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) = k3_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 21.97/3.12    inference(forward_demodulation,[],[f77073,f762])).
% 21.97/3.12  fof(f77073,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k3_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0))) )),
% 21.97/3.12    inference(superposition,[],[f390,f3748])).
% 21.97/3.12  fof(f3748,plain,(
% 21.97/3.12    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 21.97/3.12    inference(forward_demodulation,[],[f3722,f3683])).
% 21.97/3.12  fof(f3683,plain,(
% 21.97/3.12    ( ! [X2] : (k2_xboole_0(k3_xboole_0(k1_xboole_0,X2),X2) = X2) )),
% 21.97/3.12    inference(backward_demodulation,[],[f983,f3650])).
% 21.97/3.12  fof(f983,plain,(
% 21.97/3.12    ( ! [X2] : (k2_xboole_0(k3_xboole_0(k1_xboole_0,X2),k5_xboole_0(k1_xboole_0,X2)) = X2) )),
% 21.97/3.12    inference(superposition,[],[f878,f17])).
% 21.97/3.12  fof(f878,plain,(
% 21.97/3.12    ( ! [X0] : (k2_xboole_0(k5_xboole_0(k1_xboole_0,X0),k3_xboole_0(k1_xboole_0,X0)) = X0) )),
% 21.97/3.12    inference(superposition,[],[f757,f322])).
% 21.97/3.12  fof(f3722,plain,(
% 21.97/3.12    ( ! [X0] : (k2_xboole_0(X0,X0) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X0),X0)) )),
% 21.97/3.12    inference(backward_demodulation,[],[f334,f3720])).
% 21.97/3.12  fof(f390,plain,(
% 21.97/3.12    ( ! [X14,X15,X16] : (k3_xboole_0(k4_xboole_0(X14,X15),X16) = k4_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X14,k2_xboole_0(X15,X16)))) )),
% 21.97/3.12    inference(superposition,[],[f18,f22])).
% 21.97/3.12  fof(f78180,plain,(
% 21.97/3.12    ( ! [X12,X11] : (k4_xboole_0(X12,k4_xboole_0(X11,X12)) = k3_xboole_0(X12,k2_xboole_0(X11,X12))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f77817,f6753])).
% 21.97/3.12  fof(f6753,plain,(
% 21.97/3.12    ( ! [X6,X7] : (k3_xboole_0(X6,k2_xboole_0(X7,X6)) = k4_xboole_0(X6,k3_xboole_0(k1_xboole_0,k2_xboole_0(X7,X6)))) )),
% 21.97/3.12    inference(superposition,[],[f18,f4763])).
% 21.97/3.12  fof(f4763,plain,(
% 21.97/3.12    ( ! [X2,X1] : (k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X2,X1))) )),
% 21.97/3.12    inference(superposition,[],[f3831,f17])).
% 21.97/3.12  fof(f3831,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f1533,f3823])).
% 21.97/3.12  fof(f77817,plain,(
% 21.97/3.12    ( ! [X12,X11] : (k4_xboole_0(X12,k4_xboole_0(X11,X12)) = k4_xboole_0(X12,k3_xboole_0(k1_xboole_0,k2_xboole_0(X11,X12)))) )),
% 21.97/3.12    inference(superposition,[],[f29,f77409])).
% 21.97/3.12  fof(f83460,plain,(
% 21.97/3.12    ( ! [X125,X126] : (k4_xboole_0(k5_xboole_0(X125,X126),k3_xboole_0(k3_xboole_0(X125,X126),k1_xboole_0)) = k4_xboole_0(k5_xboole_0(X125,X126),k3_xboole_0(X125,X126))) )),
% 21.97/3.12    inference(superposition,[],[f80809,f78393])).
% 21.97/3.12  fof(f80809,plain,(
% 21.97/3.12    ( ! [X10,X9] : (k4_xboole_0(X9,k3_xboole_0(X10,k1_xboole_0)) = k4_xboole_0(X9,k4_xboole_0(X10,X9))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f80359,f19])).
% 21.97/3.12  fof(f80359,plain,(
% 21.97/3.12    ( ! [X10,X9] : (k4_xboole_0(X9,k4_xboole_0(X10,X9)) = k4_xboole_0(X9,k3_xboole_0(X9,k3_xboole_0(X10,k1_xboole_0)))) )),
% 21.97/3.12    inference(superposition,[],[f19,f78181])).
% 21.97/3.12  fof(f78181,plain,(
% 21.97/3.12    ( ! [X15,X16] : (k3_xboole_0(X16,k3_xboole_0(X15,k1_xboole_0)) = k3_xboole_0(X16,k4_xboole_0(X15,X16))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f77819,f29706])).
% 21.97/3.12  fof(f29706,plain,(
% 21.97/3.12    ( ! [X24,X25] : (k3_xboole_0(X25,k3_xboole_0(X24,k1_xboole_0)) = k3_xboole_0(X25,k3_xboole_0(k1_xboole_0,k2_xboole_0(X24,X25)))) )),
% 21.97/3.12    inference(superposition,[],[f68,f29428])).
% 21.97/3.12  fof(f29428,plain,(
% 21.97/3.12    ( ! [X26,X27] : (k3_xboole_0(k1_xboole_0,k2_xboole_0(X26,X27)) = k3_xboole_0(k3_xboole_0(X26,k1_xboole_0),X27)) )),
% 21.97/3.12    inference(backward_demodulation,[],[f5644,f29304])).
% 21.97/3.12  fof(f29304,plain,(
% 21.97/3.12    ( ! [X2,X3] : (k3_xboole_0(k1_xboole_0,k2_xboole_0(X2,X3)) = k5_xboole_0(k3_xboole_0(k1_xboole_0,k2_xboole_0(X2,X3)),k3_xboole_0(X2,k1_xboole_0))) )),
% 21.97/3.12    inference(superposition,[],[f22182,f3831])).
% 21.97/3.12  fof(f22182,plain,(
% 21.97/3.12    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,k1_xboole_0))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f22181,f5583])).
% 21.97/3.12  fof(f5583,plain,(
% 21.97/3.12    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f4714,f5581])).
% 21.97/3.12  fof(f5581,plain,(
% 21.97/3.12    ( ! [X17,X18] : (k4_xboole_0(X17,X18) = k5_xboole_0(X17,k3_xboole_0(X17,X18))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f5548,f25])).
% 21.97/3.12  fof(f5548,plain,(
% 21.97/3.12    ( ! [X17,X18] : (k5_xboole_0(X17,k3_xboole_0(X17,X18)) = k3_xboole_0(X17,k4_xboole_0(X17,X18))) )),
% 21.97/3.12    inference(superposition,[],[f5498,f18])).
% 21.97/3.12  fof(f5498,plain,(
% 21.97/3.12    ( ! [X8,X7] : (k3_xboole_0(X7,X8) = k5_xboole_0(X7,k4_xboole_0(X7,X8))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f3829,f5443])).
% 21.97/3.12  fof(f5443,plain,(
% 21.97/3.12    ( ! [X12,X13] : (k3_xboole_0(X12,X13) = k2_xboole_0(k3_xboole_0(X12,X13),k3_xboole_0(k1_xboole_0,k2_xboole_0(X12,X13)))) )),
% 21.97/3.12    inference(superposition,[],[f3681,f4710])).
% 21.97/3.12  fof(f3681,plain,(
% 21.97/3.12    ( ! [X0] : (k2_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0) )),
% 21.97/3.12    inference(backward_demodulation,[],[f878,f3650])).
% 21.97/3.12  fof(f3829,plain,(
% 21.97/3.12    ( ! [X8,X7] : (k5_xboole_0(X7,k4_xboole_0(X7,X8)) = k2_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(k1_xboole_0,k2_xboole_0(X7,X8)))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f1303,f3823])).
% 21.97/3.12  fof(f1303,plain,(
% 21.97/3.12    ( ! [X8,X7] : (k5_xboole_0(X7,k4_xboole_0(X7,X8)) = k2_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(k1_xboole_0,k4_xboole_0(X7,X8)))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f281,f1290])).
% 21.97/3.12  fof(f281,plain,(
% 21.97/3.12    ( ! [X8,X7] : (k5_xboole_0(X7,k4_xboole_0(X7,X8)) = k2_xboole_0(k3_xboole_0(X7,X8),k4_xboole_0(X7,k2_xboole_0(X8,X7)))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f262,f22])).
% 21.97/3.12  fof(f262,plain,(
% 21.97/3.12    ( ! [X8,X7] : (k5_xboole_0(X7,k4_xboole_0(X7,X8)) = k2_xboole_0(k3_xboole_0(X7,X8),k4_xboole_0(k4_xboole_0(X7,X8),X7))) )),
% 21.97/3.12    inference(superposition,[],[f20,f18])).
% 21.97/3.12  fof(f4714,plain,(
% 21.97/3.12    ( ! [X2,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f275,f4710])).
% 21.97/3.12  fof(f275,plain,(
% 21.97/3.12    ( ! [X2,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f258,f78])).
% 21.97/3.12  fof(f258,plain,(
% 21.97/3.12    ( ! [X2,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k3_xboole_0(X1,X2),X1))) )),
% 21.97/3.12    inference(superposition,[],[f20,f19])).
% 21.97/3.12  fof(f22181,plain,(
% 21.97/3.12    ( ! [X6,X5] : (k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(k1_xboole_0,k2_xboole_0(X5,X6)))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f22180,f4701])).
% 21.97/3.12  fof(f22180,plain,(
% 21.97/3.12    ( ! [X6,X5] : (k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(k1_xboole_0,k2_xboole_0(X5,k3_xboole_0(X5,X6))))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f22179,f5587])).
% 21.97/3.12  fof(f5587,plain,(
% 21.97/3.12    ( ! [X12,X13] : (k2_xboole_0(X12,k4_xboole_0(X12,X13)) = k2_xboole_0(X12,k3_xboole_0(X12,X13))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f5502,f5584])).
% 21.97/3.12  fof(f5584,plain,(
% 21.97/3.12    ( ! [X6,X5] : (k2_xboole_0(X5,k3_xboole_0(X5,X6)) = k2_xboole_0(k3_xboole_0(X5,X6),k4_xboole_0(X5,X6))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f1239,f5581])).
% 21.97/3.12  fof(f1239,plain,(
% 21.97/3.12    ( ! [X6,X5] : (k2_xboole_0(X5,k3_xboole_0(X5,X6)) = k2_xboole_0(k3_xboole_0(X5,X6),k5_xboole_0(X5,k3_xboole_0(X5,X6)))) )),
% 21.97/3.12    inference(superposition,[],[f348,f32])).
% 21.97/3.12  fof(f5502,plain,(
% 21.97/3.12    ( ! [X12,X13] : (k2_xboole_0(X12,k4_xboole_0(X12,X13)) = k2_xboole_0(k3_xboole_0(X12,X13),k4_xboole_0(X12,X13))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f341,f5498])).
% 21.97/3.12  fof(f341,plain,(
% 21.97/3.12    ( ! [X12,X13] : (k2_xboole_0(X12,k4_xboole_0(X12,X13)) = k2_xboole_0(k5_xboole_0(X12,k4_xboole_0(X12,X13)),k4_xboole_0(X12,X13))) )),
% 21.97/3.12    inference(superposition,[],[f21,f25])).
% 21.97/3.12  fof(f22179,plain,(
% 21.97/3.12    ( ! [X6,X5] : (k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(k1_xboole_0,k2_xboole_0(X5,k4_xboole_0(X5,X6))))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f22097,f3830])).
% 21.97/3.12  fof(f3830,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k4_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f1532,f3823])).
% 21.97/3.12  fof(f22097,plain,(
% 21.97/3.12    ( ! [X6,X5] : (k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(k3_xboole_0(X5,k1_xboole_0),k4_xboole_0(X5,X6)))) )),
% 21.97/3.12    inference(superposition,[],[f20,f15686])).
% 21.97/3.12  fof(f15686,plain,(
% 21.97/3.12    ( ! [X19,X20] : (k4_xboole_0(X19,X20) = k4_xboole_0(k4_xboole_0(X19,X20),k3_xboole_0(X19,k1_xboole_0))) )),
% 21.97/3.12    inference(superposition,[],[f7764,f12255])).
% 21.97/3.12  fof(f12255,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f12204,f19])).
% 21.97/3.12  fof(f12204,plain,(
% 21.97/3.12    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 21.97/3.12    inference(superposition,[],[f18,f12057])).
% 21.97/3.12  fof(f7764,plain,(
% 21.97/3.12    ( ! [X8,X7] : (k3_xboole_0(X7,X8) = k4_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X7,k1_xboole_0))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f7702,f18])).
% 21.97/3.12  fof(f7702,plain,(
% 21.97/3.12    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k4_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X7,k1_xboole_0))) )),
% 21.97/3.12    inference(superposition,[],[f2373,f375])).
% 21.97/3.12  fof(f2373,plain,(
% 21.97/3.12    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k4_xboole_0(X5,k2_xboole_0(X6,k3_xboole_0(X5,k1_xboole_0)))) )),
% 21.97/3.12    inference(superposition,[],[f372,f17])).
% 21.97/3.12  fof(f5644,plain,(
% 21.97/3.12    ( ! [X26,X27] : (k3_xboole_0(k3_xboole_0(X26,k1_xboole_0),X27) = k5_xboole_0(k3_xboole_0(k1_xboole_0,k2_xboole_0(X26,X27)),k3_xboole_0(X26,k1_xboole_0))) )),
% 21.97/3.12    inference(superposition,[],[f5501,f3830])).
% 21.97/3.12  fof(f5501,plain,(
% 21.97/3.12    ( ! [X8,X9] : (k3_xboole_0(X8,X9) = k5_xboole_0(k4_xboole_0(X8,X9),X8)) )),
% 21.97/3.12    inference(backward_demodulation,[],[f1030,f5498])).
% 21.97/3.12  fof(f1030,plain,(
% 21.97/3.12    ( ! [X8,X9] : (k5_xboole_0(k4_xboole_0(X8,X9),X8) = k5_xboole_0(X8,k4_xboole_0(X8,X9))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f1029,f281])).
% 21.97/3.12  fof(f1029,plain,(
% 21.97/3.12    ( ! [X8,X9] : (k5_xboole_0(k4_xboole_0(X8,X9),X8) = k2_xboole_0(k3_xboole_0(X8,X9),k4_xboole_0(X8,k2_xboole_0(X9,X8)))) )),
% 21.97/3.12    inference(forward_demodulation,[],[f998,f22])).
% 21.97/3.12  fof(f998,plain,(
% 21.97/3.12    ( ! [X8,X9] : (k5_xboole_0(k4_xboole_0(X8,X9),X8) = k2_xboole_0(k3_xboole_0(X8,X9),k4_xboole_0(k4_xboole_0(X8,X9),X8))) )),
% 21.97/3.12    inference(superposition,[],[f271,f18])).
% 21.97/3.12  fof(f77819,plain,(
% 21.97/3.12    ( ! [X15,X16] : (k3_xboole_0(X16,k3_xboole_0(k1_xboole_0,k2_xboole_0(X15,X16))) = k3_xboole_0(X16,k4_xboole_0(X15,X16))) )),
% 21.97/3.12    inference(superposition,[],[f68,f77409])).
% 21.97/3.12  fof(f81586,plain,(
% 21.97/3.12    ( ! [X21,X20] : (k5_xboole_0(k3_xboole_0(X20,X21),k5_xboole_0(X20,X21)) = k2_xboole_0(k3_xboole_0(X20,X21),k3_xboole_0(k2_xboole_0(X20,X21),k5_xboole_0(X20,X21)))) )),
% 21.97/3.12    inference(backward_demodulation,[],[f81314,f81579])).
% 21.97/3.12  fof(f81314,plain,(
% 21.97/3.12    ( ! [X21,X20] : (k5_xboole_0(k3_xboole_0(X20,X21),k5_xboole_0(X20,X21)) = k2_xboole_0(k3_xboole_0(X20,X21),k4_xboole_0(k5_xboole_0(X20,X21),k3_xboole_0(X20,X21)))) )),
% 21.97/3.12    inference(superposition,[],[f20,f78393])).
% 21.97/3.12  fof(f1044,plain,(
% 21.97/3.12    k2_xboole_0(sK0,sK1) != k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 21.97/3.12    inference(superposition,[],[f14,f1010])).
% 21.97/3.12  fof(f14,plain,(
% 21.97/3.12    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 21.97/3.12    inference(cnf_transformation,[],[f13])).
% 21.97/3.12  fof(f13,plain,(
% 21.97/3.12    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 21.97/3.12    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 21.97/3.12  fof(f12,plain,(
% 21.97/3.12    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 21.97/3.12    introduced(choice_axiom,[])).
% 21.97/3.12  fof(f11,plain,(
% 21.97/3.12    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 21.97/3.12    inference(ennf_transformation,[],[f10])).
% 21.97/3.12  fof(f10,negated_conjecture,(
% 21.97/3.12    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 21.97/3.12    inference(negated_conjecture,[],[f9])).
% 21.97/3.12  fof(f9,conjecture,(
% 21.97/3.12    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 21.97/3.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 21.97/3.12  % SZS output end Proof for theBenchmark
% 21.97/3.12  % (18755)------------------------------
% 21.97/3.12  % (18755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.97/3.12  % (18755)Termination reason: Refutation
% 21.97/3.12  
% 21.97/3.12  % (18755)Memory used [KB]: 59999
% 21.97/3.12  % (18755)Time elapsed: 2.712 s
% 21.97/3.12  % (18755)------------------------------
% 21.97/3.12  % (18755)------------------------------
% 21.97/3.12  % (18738)Success in time 2.768 s
%------------------------------------------------------------------------------
