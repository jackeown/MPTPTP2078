%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   84 (1162 expanded)
%              Number of leaves         :   13 ( 391 expanded)
%              Depth                    :   23
%              Number of atoms          :   90 (1253 expanded)
%              Number of equality atoms :   76 (1088 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1537,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1534])).

fof(f1534,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f1418,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f31,f30,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f1418,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f1226,f1414])).

fof(f1414,plain,(
    ! [X12,X13] : k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X13,X12)) = k4_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X12,k4_xboole_0(X12,X13))) ),
    inference(forward_demodulation,[],[f1413,f944])).

fof(f944,plain,(
    ! [X10,X8,X9] : k4_xboole_0(X8,k2_xboole_0(k4_xboole_0(X9,X8),X10)) = k4_xboole_0(X8,X10) ),
    inference(superposition,[],[f34,f503])).

fof(f503,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(resolution,[],[f480,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f480,plain,(
    ! [X10,X9] : r1_xboole_0(X9,k4_xboole_0(X10,X9)) ),
    inference(forward_demodulation,[],[f477,f22])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f477,plain,(
    ! [X10,X9] : r1_xboole_0(k4_xboole_0(X9,k1_xboole_0),k4_xboole_0(X10,X9)) ),
    inference(backward_demodulation,[],[f267,f476])).

fof(f476,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f447,f443])).

fof(f443,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f207,f434])).

fof(f434,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = X0 ),
    inference(resolution,[],[f410,f32])).

fof(f410,plain,(
    ! [X14,X13] : r1_xboole_0(X13,k4_xboole_0(k1_xboole_0,X14)) ),
    inference(superposition,[],[f377,f22])).

fof(f377,plain,(
    ! [X10,X8,X9] : r1_xboole_0(k4_xboole_0(X10,X8),k4_xboole_0(X8,X9)) ),
    inference(superposition,[],[f81,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f29,f27])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f81,plain,(
    ! [X4,X2,X3] : r1_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,X4)),X4) ),
    inference(superposition,[],[f23,f34])).

fof(f23,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f207,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f145,f62])).

fof(f62,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f28,f55])).

fof(f55,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f53,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f53,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f50,f22])).

fof(f50,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f28,f22])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f145,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f37,f22])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f24,f27,f27])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f447,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(backward_demodulation,[],[f74,f443])).

fof(f74,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),X3) ),
    inference(superposition,[],[f34,f62])).

fof(f267,plain,(
    ! [X10,X9] : r1_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,k2_xboole_0(X9,X10))),k4_xboole_0(X10,X9)) ),
    inference(superposition,[],[f157,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f28,f25])).

fof(f157,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f23,f37])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1413,plain,(
    ! [X12,X13] : k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X13,X12)) = k4_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X12,k2_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(X12,X13)))) ),
    inference(forward_demodulation,[],[f1412,f1221])).

fof(f1221,plain,(
    ! [X8,X9] : k2_xboole_0(X9,X8) = k2_xboole_0(X8,k2_xboole_0(X8,X9)) ),
    inference(backward_demodulation,[],[f795,f1220])).

fof(f1220,plain,(
    ! [X14,X13] : k2_xboole_0(X13,X14) = k2_xboole_0(k4_xboole_0(X13,X14),X14) ),
    inference(forward_demodulation,[],[f1180,f28])).

fof(f1180,plain,(
    ! [X14,X13] : k2_xboole_0(X13,X14) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X13,X14),X14),X14) ),
    inference(superposition,[],[f39,f494])).

fof(f494,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = X7 ),
    inference(forward_demodulation,[],[f492,f22])).

fof(f492,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = k4_xboole_0(X7,k1_xboole_0) ),
    inference(backward_demodulation,[],[f146,f488])).

fof(f488,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f465,f482])).

fof(f482,plain,(
    ! [X12,X11] : k2_xboole_0(X11,X12) = k2_xboole_0(X11,k4_xboole_0(X12,X11)) ),
    inference(backward_demodulation,[],[f366,f481])).

fof(f481,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) = X6 ),
    inference(forward_demodulation,[],[f479,f22])).

fof(f479,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) ),
    inference(backward_demodulation,[],[f195,f476])).

fof(f195,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(X6,k2_xboole_0(X6,X7))) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) ),
    inference(superposition,[],[f37,f48])).

fof(f366,plain,(
    ! [X12,X11] : k2_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X11,X12),k4_xboole_0(X12,X11)),k4_xboole_0(X12,X11)) ),
    inference(superposition,[],[f39,f48])).

fof(f465,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(backward_demodulation,[],[f79,f443])).

fof(f79,plain,(
    ! [X6,X5] : k4_xboole_0(k1_xboole_0,k4_xboole_0(X5,X6)) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f34,f62])).

fof(f146,plain,(
    ! [X6,X7] : k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(X6,X7))) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f37,f28])).

fof(f795,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k2_xboole_0(X8,X9)) = k2_xboole_0(k4_xboole_0(X9,X8),X8) ),
    inference(forward_demodulation,[],[f794,f55])).

fof(f794,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k2_xboole_0(X8,X9)) = k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X9,X8)),X8) ),
    inference(forward_demodulation,[],[f793,f22])).

fof(f793,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k2_xboole_0(X8,X9)) = k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X9,X8)),k4_xboole_0(X8,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f742,f476])).

fof(f742,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k2_xboole_0(X8,X9)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X8,k2_xboole_0(X8,X9)),k4_xboole_0(X9,X8)),k4_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X8,X9)))) ),
    inference(superposition,[],[f40,f48])).

fof(f1412,plain,(
    ! [X12,X13] : k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X13,X12)) = k4_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X12,k2_xboole_0(k4_xboole_0(X12,X13),k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X13,X12))))) ),
    inference(forward_demodulation,[],[f1367,f34])).

fof(f1367,plain,(
    ! [X12,X13] : k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X13,X12)) = k4_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X13,X12)))) ),
    inference(superposition,[],[f481,f40])).

fof(f1226,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1225,f944])).

fof(f1225,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK1)))) ),
    inference(backward_demodulation,[],[f835,f1221])).

fof(f835,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f42,f766])).

fof(f766,plain,(
    ! [X4,X5] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,X4)),k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X4,k4_xboole_0(X4,X5))) ),
    inference(superposition,[],[f28,f40])).

fof(f42,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f35,f34])).

fof(f35,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f20,f30,f30,f27])).

fof(f20,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:37:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (28399)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (28405)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (28396)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (28393)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (28395)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (28404)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (28402)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (28403)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (28403)Refutation not found, incomplete strategy% (28403)------------------------------
% 0.22/0.49  % (28403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (28403)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (28403)Memory used [KB]: 10490
% 0.22/0.49  % (28403)Time elapsed: 0.062 s
% 0.22/0.49  % (28403)------------------------------
% 0.22/0.49  % (28403)------------------------------
% 0.22/0.50  % (28401)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (28400)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (28406)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.51  % (28397)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.51  % (28398)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (28394)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.51  % (28408)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.52  % (28392)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.52  % (28393)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f1537,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f1534])).
% 0.22/0.52  fof(f1534,plain,(
% 0.22/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1)),
% 0.22/0.52    inference(superposition,[],[f1418,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f31,f30,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 0.22/0.52  fof(f1418,plain,(
% 0.22/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.22/0.52    inference(backward_demodulation,[],[f1226,f1414])).
% 0.22/0.52  fof(f1414,plain,(
% 0.22/0.52    ( ! [X12,X13] : (k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X13,X12)) = k4_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X12,k4_xboole_0(X12,X13)))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f1413,f944])).
% 0.22/0.52  fof(f944,plain,(
% 0.22/0.52    ( ! [X10,X8,X9] : (k4_xboole_0(X8,k2_xboole_0(k4_xboole_0(X9,X8),X10)) = k4_xboole_0(X8,X10)) )),
% 0.22/0.52    inference(superposition,[],[f34,f503])).
% 0.22/0.52  fof(f503,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 0.22/0.52    inference(resolution,[],[f480,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(nnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.52  fof(f480,plain,(
% 0.22/0.52    ( ! [X10,X9] : (r1_xboole_0(X9,k4_xboole_0(X10,X9))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f477,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.52  fof(f477,plain,(
% 0.22/0.52    ( ! [X10,X9] : (r1_xboole_0(k4_xboole_0(X9,k1_xboole_0),k4_xboole_0(X10,X9))) )),
% 0.22/0.52    inference(backward_demodulation,[],[f267,f476])).
% 0.22/0.52  fof(f476,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f447,f443])).
% 0.22/0.52  fof(f443,plain,(
% 0.22/0.52    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 0.22/0.52    inference(backward_demodulation,[],[f207,f434])).
% 0.22/0.52  fof(f434,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = X0) )),
% 0.22/0.52    inference(resolution,[],[f410,f32])).
% 0.22/0.52  fof(f410,plain,(
% 0.22/0.52    ( ! [X14,X13] : (r1_xboole_0(X13,k4_xboole_0(k1_xboole_0,X14))) )),
% 0.22/0.52    inference(superposition,[],[f377,f22])).
% 0.22/0.52  fof(f377,plain,(
% 0.22/0.52    ( ! [X10,X8,X9] : (r1_xboole_0(k4_xboole_0(X10,X8),k4_xboole_0(X8,X9))) )),
% 0.22/0.52    inference(superposition,[],[f81,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.52    inference(definition_unfolding,[],[f29,f27])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    ( ! [X4,X2,X3] : (r1_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,X4)),X4)) )),
% 0.22/0.52    inference(superposition,[],[f23,f34])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.52  fof(f207,plain,(
% 0.22/0.52    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) )),
% 0.22/0.52    inference(superposition,[],[f145,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0)) )),
% 0.22/0.52    inference(superposition,[],[f28,f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.22/0.52    inference(superposition,[],[f53,f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 0.22/0.52    inference(forward_demodulation,[],[f50,f22])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k1_xboole_0)) )),
% 0.22/0.52    inference(superposition,[],[f28,f22])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.22/0.52  fof(f145,plain,(
% 0.22/0.52    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 0.22/0.52    inference(superposition,[],[f37,f22])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f24,f27,f27])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.52  fof(f447,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) )),
% 0.22/0.52    inference(backward_demodulation,[],[f74,f443])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),X3)) )),
% 0.22/0.52    inference(superposition,[],[f34,f62])).
% 0.22/0.52  fof(f267,plain,(
% 0.22/0.52    ( ! [X10,X9] : (r1_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,k2_xboole_0(X9,X10))),k4_xboole_0(X10,X9))) )),
% 0.22/0.52    inference(superposition,[],[f157,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 0.22/0.52    inference(superposition,[],[f28,f25])).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(superposition,[],[f23,f37])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.52  fof(f1413,plain,(
% 0.22/0.52    ( ! [X12,X13] : (k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X13,X12)) = k4_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X12,k2_xboole_0(k4_xboole_0(X13,X12),k4_xboole_0(X12,X13))))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f1412,f1221])).
% 0.22/0.52  fof(f1221,plain,(
% 0.22/0.52    ( ! [X8,X9] : (k2_xboole_0(X9,X8) = k2_xboole_0(X8,k2_xboole_0(X8,X9))) )),
% 0.22/0.52    inference(backward_demodulation,[],[f795,f1220])).
% 0.22/0.52  fof(f1220,plain,(
% 0.22/0.52    ( ! [X14,X13] : (k2_xboole_0(X13,X14) = k2_xboole_0(k4_xboole_0(X13,X14),X14)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f1180,f28])).
% 0.22/0.52  fof(f1180,plain,(
% 0.22/0.52    ( ! [X14,X13] : (k2_xboole_0(X13,X14) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X13,X14),X14),X14)) )),
% 0.22/0.52    inference(superposition,[],[f39,f494])).
% 0.22/0.52  fof(f494,plain,(
% 0.22/0.52    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = X7) )),
% 0.22/0.52    inference(forward_demodulation,[],[f492,f22])).
% 0.22/0.52  fof(f492,plain,(
% 0.22/0.52    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = k4_xboole_0(X7,k1_xboole_0)) )),
% 0.22/0.52    inference(backward_demodulation,[],[f146,f488])).
% 0.22/0.52  fof(f488,plain,(
% 0.22/0.52    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f465,f482])).
% 0.22/0.52  fof(f482,plain,(
% 0.22/0.52    ( ! [X12,X11] : (k2_xboole_0(X11,X12) = k2_xboole_0(X11,k4_xboole_0(X12,X11))) )),
% 0.22/0.52    inference(backward_demodulation,[],[f366,f481])).
% 0.22/0.52  fof(f481,plain,(
% 0.22/0.52    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) = X6) )),
% 0.22/0.52    inference(forward_demodulation,[],[f479,f22])).
% 0.22/0.52  fof(f479,plain,(
% 0.22/0.52    ( ! [X6,X7] : (k4_xboole_0(X6,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6))) )),
% 0.22/0.52    inference(backward_demodulation,[],[f195,f476])).
% 0.22/0.52  fof(f195,plain,(
% 0.22/0.52    ( ! [X6,X7] : (k4_xboole_0(X6,k4_xboole_0(X6,k2_xboole_0(X6,X7))) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6))) )),
% 0.22/0.52    inference(superposition,[],[f37,f48])).
% 0.22/0.52  fof(f366,plain,(
% 0.22/0.52    ( ! [X12,X11] : (k2_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X11,X12),k4_xboole_0(X12,X11)),k4_xboole_0(X12,X11))) )),
% 0.22/0.52    inference(superposition,[],[f39,f48])).
% 0.22/0.52  fof(f465,plain,(
% 0.22/0.52    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 0.22/0.52    inference(backward_demodulation,[],[f79,f443])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    ( ! [X6,X5] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(X5,X6)) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 0.22/0.52    inference(superposition,[],[f34,f62])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    ( ! [X6,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(X6,X7))) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7))) )),
% 0.22/0.52    inference(superposition,[],[f37,f28])).
% 0.22/0.52  fof(f795,plain,(
% 0.22/0.52    ( ! [X8,X9] : (k2_xboole_0(X8,k2_xboole_0(X8,X9)) = k2_xboole_0(k4_xboole_0(X9,X8),X8)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f794,f55])).
% 0.22/0.52  fof(f794,plain,(
% 0.22/0.52    ( ! [X8,X9] : (k2_xboole_0(X8,k2_xboole_0(X8,X9)) = k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X9,X8)),X8)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f793,f22])).
% 0.22/0.52  fof(f793,plain,(
% 0.22/0.52    ( ! [X8,X9] : (k2_xboole_0(X8,k2_xboole_0(X8,X9)) = k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X9,X8)),k4_xboole_0(X8,k1_xboole_0))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f742,f476])).
% 0.22/0.52  fof(f742,plain,(
% 0.22/0.52    ( ! [X8,X9] : (k2_xboole_0(X8,k2_xboole_0(X8,X9)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X8,k2_xboole_0(X8,X9)),k4_xboole_0(X9,X8)),k4_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X8,X9))))) )),
% 0.22/0.52    inference(superposition,[],[f40,f48])).
% 0.22/0.52  fof(f1412,plain,(
% 0.22/0.52    ( ! [X12,X13] : (k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X13,X12)) = k4_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X12,k2_xboole_0(k4_xboole_0(X12,X13),k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X13,X12)))))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f1367,f34])).
% 0.22/0.52  fof(f1367,plain,(
% 0.22/0.52    ( ! [X12,X13] : (k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X13,X12)) = k4_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X13)),k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X13,X12))))) )),
% 0.22/0.52    inference(superposition,[],[f481,f40])).
% 0.22/0.52  fof(f1226,plain,(
% 0.22/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.22/0.52    inference(forward_demodulation,[],[f1225,f944])).
% 0.22/0.52  fof(f1225,plain,(
% 0.22/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK1))))),
% 0.22/0.52    inference(backward_demodulation,[],[f835,f1221])).
% 0.22/0.52  fof(f835,plain,(
% 0.22/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 0.22/0.52    inference(backward_demodulation,[],[f42,f766])).
% 0.22/0.52  fof(f766,plain,(
% 0.22/0.52    ( ! [X4,X5] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,X4)),k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X4,k4_xboole_0(X4,X5)))) )),
% 0.22/0.52    inference(superposition,[],[f28,f40])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 0.22/0.52    inference(backward_demodulation,[],[f35,f34])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.22/0.52    inference(definition_unfolding,[],[f20,f30,f30,f27])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.52    inference(negated_conjecture,[],[f14])).
% 0.22/0.52  fof(f14,conjecture,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (28393)------------------------------
% 0.22/0.52  % (28393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28393)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (28393)Memory used [KB]: 2430
% 0.22/0.52  % (28393)Time elapsed: 0.102 s
% 0.22/0.52  % (28393)------------------------------
% 0.22/0.52  % (28393)------------------------------
% 0.22/0.52  % (28391)Success in time 0.16 s
%------------------------------------------------------------------------------
