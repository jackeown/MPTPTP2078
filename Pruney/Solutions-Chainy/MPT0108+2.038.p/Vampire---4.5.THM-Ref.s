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
% DateTime   : Thu Dec  3 12:32:23 EST 2020

% Result     : Theorem 5.73s
% Output     : Refutation 5.73s
% Verified   : 
% Statistics : Number of formulae       :  109 (1826 expanded)
%              Number of leaves         :   14 ( 554 expanded)
%              Depth                    :   31
%              Number of atoms          :  115 (1847 expanded)
%              Number of equality atoms :  101 (1809 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23694,plain,(
    $false ),
    inference(subsumption_resolution,[],[f21,f23693])).

fof(f23693,plain,(
    ! [X80,X81] : k5_xboole_0(X80,X81) = k4_xboole_0(k2_xboole_0(X80,X81),k3_xboole_0(X80,X81)) ),
    inference(forward_demodulation,[],[f23536,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f23536,plain,(
    ! [X80,X81] : k5_xboole_0(X80,X81) = k4_xboole_0(k2_xboole_0(k5_xboole_0(X80,X81),k3_xboole_0(X80,X81)),k3_xboole_0(X80,X81)) ),
    inference(superposition,[],[f4673,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(resolution,[],[f31,f25])).

fof(f25,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f4673,plain,(
    ! [X33,X32] : k4_xboole_0(k2_xboole_0(X33,X32),k4_xboole_0(X32,X33)) = X33 ),
    inference(forward_demodulation,[],[f4627,f615])).

fof(f615,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X8,X7)) = X7 ),
    inference(forward_demodulation,[],[f601,f48])).

fof(f48,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f45,f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f45,plain,(
    ! [X2] : k2_xboole_0(X2,X2) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f26,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f24,f22])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f601,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X8,X7)) = k5_xboole_0(X7,k1_xboole_0) ),
    inference(superposition,[],[f27,f559])).

fof(f559,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f546,f353])).

fof(f353,plain,(
    ! [X12,X13] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X12,X13),X12) ),
    inference(forward_demodulation,[],[f344,f107])).

fof(f107,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f87,f105])).

fof(f105,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f97,f48])).

fof(f97,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f27,f84])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f83,f36])).

fof(f83,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f76,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f76,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f28,f67])).

fof(f67,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f29,f36])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f87,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f77,f36])).

fof(f77,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f27,f67])).

fof(f344,plain,(
    ! [X12,X13] : k4_xboole_0(k3_xboole_0(X12,X13),X12) = k5_xboole_0(k3_xboole_0(X12,X13),k3_xboole_0(X12,X13)) ),
    inference(superposition,[],[f59,f72])).

fof(f72,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k3_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f68,f29])).

fof(f68,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f29,f28])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f27,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f546,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X0)),X0) ),
    inference(resolution,[],[f545,f31])).

fof(f545,plain,(
    ! [X2,X1] : r1_xboole_0(k3_xboole_0(X1,k4_xboole_0(X2,X1)),X1) ),
    inference(forward_demodulation,[],[f544,f72])).

fof(f544,plain,(
    ! [X2,X1] : r1_xboole_0(k3_xboole_0(X1,k3_xboole_0(X1,k4_xboole_0(X2,X1))),X1) ),
    inference(forward_demodulation,[],[f516,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f516,plain,(
    ! [X2,X1] : r1_xboole_0(k3_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X1)),X1) ),
    inference(superposition,[],[f50,f376])).

fof(f376,plain,(
    ! [X10,X11] : k2_xboole_0(X10,k3_xboole_0(X10,X11)) = X10 ),
    inference(forward_demodulation,[],[f373,f48])).

fof(f373,plain,(
    ! [X10,X11] : k2_xboole_0(X10,k3_xboole_0(X10,X11)) = k5_xboole_0(X10,k1_xboole_0) ),
    inference(superposition,[],[f26,f353])).

fof(f50,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f46,f23])).

fof(f46,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(k4_xboole_0(X1,X0),X0),k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f37,f26])).

fof(f37,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f25,f23])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f4627,plain,(
    ! [X33,X32] : k4_xboole_0(X33,k4_xboole_0(X32,X33)) = k4_xboole_0(k2_xboole_0(X33,X32),k4_xboole_0(X32,X33)) ),
    inference(superposition,[],[f4145,f3861])).

fof(f3861,plain,(
    ! [X8,X7] : k2_xboole_0(X7,X8) = k2_xboole_0(k4_xboole_0(X8,X7),X7) ),
    inference(backward_demodulation,[],[f956,f3838])).

fof(f3838,plain,(
    ! [X8,X7] : k4_xboole_0(X8,X7) = k5_xboole_0(X7,k2_xboole_0(X7,X8)) ),
    inference(superposition,[],[f3825,f26])).

fof(f3825,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f3791,f643])).

fof(f643,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(backward_demodulation,[],[f111,f642])).

fof(f642,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f641,f22])).

fof(f641,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f619,f109])).

fof(f109,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(backward_demodulation,[],[f67,f105])).

fof(f619,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f30,f107])).

fof(f111,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f82,f109])).

fof(f82,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X1)) ),
    inference(superposition,[],[f26,f67])).

fof(f3791,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f33,f107])).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f956,plain,(
    ! [X8,X7] : k2_xboole_0(X7,X8) = k2_xboole_0(k5_xboole_0(X7,k2_xboole_0(X7,X8)),X7) ),
    inference(backward_demodulation,[],[f629,f940])).

fof(f940,plain,(
    ! [X8,X7] : k2_xboole_0(X7,X8) = k2_xboole_0(X7,k2_xboole_0(X7,X8)) ),
    inference(superposition,[],[f890,f108])).

fof(f108,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k2_xboole_0(X3,X4)) = X3 ),
    inference(backward_demodulation,[],[f69,f105])).

fof(f69,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k2_xboole_0(X3,X4)) = k4_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f29,f24])).

fof(f890,plain,(
    ! [X2,X1] : k2_xboole_0(k3_xboole_0(X2,X1),X1) = X1 ),
    inference(superposition,[],[f876,f23])).

fof(f876,plain,(
    ! [X2,X1] : k2_xboole_0(k3_xboole_0(X1,X2),X1) = X1 ),
    inference(forward_demodulation,[],[f856,f657])).

fof(f657,plain,(
    ! [X10,X9] : k2_xboole_0(k3_xboole_0(X9,X10),k4_xboole_0(X9,X10)) = X9 ),
    inference(forward_demodulation,[],[f656,f451])).

fof(f451,plain,(
    ! [X30,X31] : k2_xboole_0(X30,k4_xboole_0(X30,X31)) = X30 ),
    inference(superposition,[],[f376,f74])).

fof(f74,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k3_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f70,f28])).

fof(f70,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k4_xboole_0(X5,X6)) = k4_xboole_0(X5,k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f29,f29])).

fof(f656,plain,(
    ! [X10,X9] : k2_xboole_0(X9,k4_xboole_0(X9,X10)) = k2_xboole_0(k3_xboole_0(X9,X10),k4_xboole_0(X9,X10)) ),
    inference(forward_demodulation,[],[f630,f454])).

fof(f454,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k5_xboole_0(X6,k4_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f440,f29])).

fof(f440,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(X6,X7)) = k5_xboole_0(X6,k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f27,f74])).

fof(f630,plain,(
    ! [X10,X9] : k2_xboole_0(X9,k4_xboole_0(X9,X10)) = k2_xboole_0(k5_xboole_0(X9,k4_xboole_0(X9,X10)),k4_xboole_0(X9,X10)) ),
    inference(superposition,[],[f30,f74])).

fof(f856,plain,(
    ! [X2,X1] : k2_xboole_0(k3_xboole_0(X1,X2),X1) = k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f649,f28])).

fof(f649,plain,(
    ! [X6,X5] : k2_xboole_0(X5,X6) = k2_xboole_0(X5,k4_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f648,f129])).

fof(f129,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f125,f48])).

fof(f125,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f26,f85])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f56,f84])).

fof(f56,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) ),
    inference(resolution,[],[f52,f31])).

fof(f52,plain,(
    ! [X1] : r1_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1) ),
    inference(superposition,[],[f25,f48])).

fof(f648,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k4_xboole_0(X6,X5)) = k2_xboole_0(k2_xboole_0(X5,X6),k1_xboole_0) ),
    inference(forward_demodulation,[],[f622,f559])).

fof(f622,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k4_xboole_0(X6,X5)) = k2_xboole_0(k2_xboole_0(X5,X6),k3_xboole_0(X5,k4_xboole_0(X6,X5))) ),
    inference(superposition,[],[f30,f26])).

fof(f629,plain,(
    ! [X8,X7] : k2_xboole_0(X7,k2_xboole_0(X7,X8)) = k2_xboole_0(k5_xboole_0(X7,k2_xboole_0(X7,X8)),X7) ),
    inference(superposition,[],[f30,f108])).

fof(f4145,plain,(
    ! [X6,X5] : k4_xboole_0(k2_xboole_0(X5,X6),X5) = k4_xboole_0(X6,X5) ),
    inference(forward_demodulation,[],[f4133,f3838])).

fof(f4133,plain,(
    ! [X6,X5] : k4_xboole_0(k2_xboole_0(X5,X6),X5) = k5_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    inference(backward_demodulation,[],[f286,f4119])).

fof(f4119,plain,(
    ! [X12,X13] : k5_xboole_0(X12,X13) = k5_xboole_0(X13,X12) ),
    inference(superposition,[],[f3825,f4087])).

fof(f4087,plain,(
    ! [X12,X13] : k5_xboole_0(X13,k5_xboole_0(X12,X13)) = X12 ),
    inference(forward_demodulation,[],[f4063,f48])).

fof(f4063,plain,(
    ! [X12,X13] : k5_xboole_0(X12,k1_xboole_0) = k5_xboole_0(X13,k5_xboole_0(X12,X13)) ),
    inference(superposition,[],[f3825,f3806])).

fof(f3806,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f33,f107])).

fof(f286,plain,(
    ! [X6,X5] : k4_xboole_0(k2_xboole_0(X5,X6),X5) = k5_xboole_0(k2_xboole_0(X5,X6),X5) ),
    inference(superposition,[],[f59,f108])).

fof(f21,plain,(
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:05:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (20794)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (20795)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (20792)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (20793)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (20791)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (20799)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (20805)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (20798)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (20802)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (20801)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (20801)Refutation not found, incomplete strategy% (20801)------------------------------
% 0.21/0.48  % (20801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (20801)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (20801)Memory used [KB]: 10618
% 0.21/0.48  % (20801)Time elapsed: 0.075 s
% 0.21/0.48  % (20801)------------------------------
% 0.21/0.48  % (20801)------------------------------
% 0.21/0.48  % (20806)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (20804)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (20800)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (20807)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (20796)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (20797)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (20790)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (20803)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 4.87/1.02  % (20794)Time limit reached!
% 4.87/1.02  % (20794)------------------------------
% 4.87/1.02  % (20794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.87/1.02  % (20794)Termination reason: Time limit
% 4.87/1.02  % (20794)Termination phase: Saturation
% 4.87/1.02  
% 4.87/1.02  % (20794)Memory used [KB]: 25330
% 4.87/1.02  % (20794)Time elapsed: 0.600 s
% 4.87/1.02  % (20794)------------------------------
% 4.87/1.02  % (20794)------------------------------
% 5.73/1.10  % (20806)Refutation found. Thanks to Tanya!
% 5.73/1.10  % SZS status Theorem for theBenchmark
% 5.73/1.11  % SZS output start Proof for theBenchmark
% 5.73/1.11  fof(f23694,plain,(
% 5.73/1.11    $false),
% 5.73/1.11    inference(subsumption_resolution,[],[f21,f23693])).
% 5.73/1.11  fof(f23693,plain,(
% 5.73/1.11    ( ! [X80,X81] : (k5_xboole_0(X80,X81) = k4_xboole_0(k2_xboole_0(X80,X81),k3_xboole_0(X80,X81))) )),
% 5.73/1.11    inference(forward_demodulation,[],[f23536,f30])).
% 5.73/1.11  fof(f30,plain,(
% 5.73/1.11    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 5.73/1.11    inference(cnf_transformation,[],[f12])).
% 5.73/1.11  fof(f12,axiom,(
% 5.73/1.11    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.73/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 5.73/1.11  fof(f23536,plain,(
% 5.73/1.11    ( ! [X80,X81] : (k5_xboole_0(X80,X81) = k4_xboole_0(k2_xboole_0(k5_xboole_0(X80,X81),k3_xboole_0(X80,X81)),k3_xboole_0(X80,X81))) )),
% 5.73/1.11    inference(superposition,[],[f4673,f41])).
% 5.73/1.11  fof(f41,plain,(
% 5.73/1.11    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 5.73/1.11    inference(resolution,[],[f31,f25])).
% 5.73/1.11  fof(f25,plain,(
% 5.73/1.11    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 5.73/1.11    inference(cnf_transformation,[],[f3])).
% 5.73/1.11  fof(f3,axiom,(
% 5.73/1.11    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 5.73/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 5.73/1.11  fof(f31,plain,(
% 5.73/1.11    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 5.73/1.11    inference(cnf_transformation,[],[f20])).
% 5.73/1.11  fof(f20,plain,(
% 5.73/1.11    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 5.73/1.11    inference(nnf_transformation,[],[f10])).
% 5.73/1.11  fof(f10,axiom,(
% 5.73/1.11    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 5.73/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 5.73/1.11  fof(f4673,plain,(
% 5.73/1.11    ( ! [X33,X32] : (k4_xboole_0(k2_xboole_0(X33,X32),k4_xboole_0(X32,X33)) = X33) )),
% 5.73/1.11    inference(forward_demodulation,[],[f4627,f615])).
% 5.73/1.11  fof(f615,plain,(
% 5.73/1.11    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X8,X7)) = X7) )),
% 5.73/1.11    inference(forward_demodulation,[],[f601,f48])).
% 5.73/1.11  fof(f48,plain,(
% 5.73/1.11    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = X2) )),
% 5.73/1.11    inference(forward_demodulation,[],[f45,f22])).
% 5.73/1.11  fof(f22,plain,(
% 5.73/1.11    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 5.73/1.11    inference(cnf_transformation,[],[f16])).
% 5.73/1.11  fof(f16,plain,(
% 5.73/1.11    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 5.73/1.11    inference(rectify,[],[f2])).
% 5.73/1.11  fof(f2,axiom,(
% 5.73/1.11    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 5.73/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 5.73/1.11  fof(f45,plain,(
% 5.73/1.11    ( ! [X2] : (k2_xboole_0(X2,X2) = k5_xboole_0(X2,k1_xboole_0)) )),
% 5.73/1.11    inference(superposition,[],[f26,f36])).
% 5.73/1.11  fof(f36,plain,(
% 5.73/1.11    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 5.73/1.11    inference(superposition,[],[f24,f22])).
% 5.73/1.11  fof(f24,plain,(
% 5.73/1.11    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 5.73/1.11    inference(cnf_transformation,[],[f6])).
% 5.73/1.11  fof(f6,axiom,(
% 5.73/1.11    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 5.73/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 5.73/1.11  fof(f26,plain,(
% 5.73/1.11    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 5.73/1.11    inference(cnf_transformation,[],[f13])).
% 5.73/1.11  fof(f13,axiom,(
% 5.73/1.11    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 5.73/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 5.73/1.11  fof(f601,plain,(
% 5.73/1.11    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X8,X7)) = k5_xboole_0(X7,k1_xboole_0)) )),
% 5.73/1.11    inference(superposition,[],[f27,f559])).
% 5.73/1.11  fof(f559,plain,(
% 5.73/1.11    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 5.73/1.11    inference(forward_demodulation,[],[f546,f353])).
% 5.73/1.11  fof(f353,plain,(
% 5.73/1.11    ( ! [X12,X13] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X12,X13),X12)) )),
% 5.73/1.11    inference(forward_demodulation,[],[f344,f107])).
% 5.73/1.11  fof(f107,plain,(
% 5.73/1.11    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 5.73/1.11    inference(backward_demodulation,[],[f87,f105])).
% 5.73/1.11  fof(f105,plain,(
% 5.73/1.11    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 5.73/1.11    inference(forward_demodulation,[],[f97,f48])).
% 5.73/1.11  fof(f97,plain,(
% 5.73/1.11    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,k1_xboole_0)) )),
% 5.73/1.11    inference(superposition,[],[f27,f84])).
% 5.73/1.11  fof(f84,plain,(
% 5.73/1.11    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 5.73/1.11    inference(forward_demodulation,[],[f83,f36])).
% 5.73/1.11  fof(f83,plain,(
% 5.73/1.11    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_xboole_0(X0,k1_xboole_0)) )),
% 5.73/1.11    inference(forward_demodulation,[],[f76,f29])).
% 5.73/1.11  fof(f29,plain,(
% 5.73/1.11    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 5.73/1.11    inference(cnf_transformation,[],[f8])).
% 5.73/1.11  fof(f8,axiom,(
% 5.73/1.11    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.73/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.73/1.11  fof(f76,plain,(
% 5.73/1.11    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 5.73/1.11    inference(superposition,[],[f28,f67])).
% 5.73/1.11  fof(f67,plain,(
% 5.73/1.11    ( ! [X0] : (k3_xboole_0(X0,X0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 5.73/1.11    inference(superposition,[],[f29,f36])).
% 5.73/1.11  fof(f28,plain,(
% 5.73/1.11    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.73/1.11    inference(cnf_transformation,[],[f7])).
% 5.73/1.11  fof(f7,axiom,(
% 5.73/1.11    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.73/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 5.73/1.11  fof(f87,plain,(
% 5.73/1.11    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 5.73/1.11    inference(forward_demodulation,[],[f77,f36])).
% 5.73/1.11  fof(f77,plain,(
% 5.73/1.11    ( ! [X1] : (k4_xboole_0(X1,X1) = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 5.73/1.11    inference(superposition,[],[f27,f67])).
% 5.73/1.11  fof(f344,plain,(
% 5.73/1.11    ( ! [X12,X13] : (k4_xboole_0(k3_xboole_0(X12,X13),X12) = k5_xboole_0(k3_xboole_0(X12,X13),k3_xboole_0(X12,X13))) )),
% 5.73/1.11    inference(superposition,[],[f59,f72])).
% 5.73/1.11  fof(f72,plain,(
% 5.73/1.11    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k3_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 5.73/1.11    inference(forward_demodulation,[],[f68,f29])).
% 5.73/1.11  fof(f68,plain,(
% 5.73/1.11    ( ! [X2,X1] : (k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 5.73/1.11    inference(superposition,[],[f29,f28])).
% 5.73/1.11  fof(f59,plain,(
% 5.73/1.11    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 5.73/1.11    inference(superposition,[],[f27,f23])).
% 5.73/1.11  fof(f23,plain,(
% 5.73/1.11    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.73/1.11    inference(cnf_transformation,[],[f1])).
% 5.73/1.11  fof(f1,axiom,(
% 5.73/1.11    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.73/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.73/1.11  fof(f546,plain,(
% 5.73/1.11    ( ! [X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) )),
% 5.73/1.11    inference(resolution,[],[f545,f31])).
% 5.73/1.11  fof(f545,plain,(
% 5.73/1.11    ( ! [X2,X1] : (r1_xboole_0(k3_xboole_0(X1,k4_xboole_0(X2,X1)),X1)) )),
% 5.73/1.11    inference(forward_demodulation,[],[f544,f72])).
% 5.73/1.11  fof(f544,plain,(
% 5.73/1.11    ( ! [X2,X1] : (r1_xboole_0(k3_xboole_0(X1,k3_xboole_0(X1,k4_xboole_0(X2,X1))),X1)) )),
% 5.73/1.11    inference(forward_demodulation,[],[f516,f34])).
% 5.73/1.11  fof(f34,plain,(
% 5.73/1.11    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 5.73/1.11    inference(cnf_transformation,[],[f9])).
% 5.73/1.11  fof(f9,axiom,(
% 5.73/1.11    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 5.73/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 5.73/1.11  fof(f516,plain,(
% 5.73/1.11    ( ! [X2,X1] : (r1_xboole_0(k3_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X1)),X1)) )),
% 5.73/1.11    inference(superposition,[],[f50,f376])).
% 5.73/1.11  fof(f376,plain,(
% 5.73/1.11    ( ! [X10,X11] : (k2_xboole_0(X10,k3_xboole_0(X10,X11)) = X10) )),
% 5.73/1.11    inference(forward_demodulation,[],[f373,f48])).
% 5.73/1.11  fof(f373,plain,(
% 5.73/1.11    ( ! [X10,X11] : (k2_xboole_0(X10,k3_xboole_0(X10,X11)) = k5_xboole_0(X10,k1_xboole_0)) )),
% 5.73/1.11    inference(superposition,[],[f26,f353])).
% 5.73/1.11  fof(f50,plain,(
% 5.73/1.11    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1))) )),
% 5.73/1.11    inference(forward_demodulation,[],[f46,f23])).
% 5.73/1.11  fof(f46,plain,(
% 5.73/1.11    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(k4_xboole_0(X1,X0),X0),k2_xboole_0(X0,X1))) )),
% 5.73/1.11    inference(superposition,[],[f37,f26])).
% 5.73/1.11  fof(f37,plain,(
% 5.73/1.11    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X0,X1))) )),
% 5.73/1.11    inference(superposition,[],[f25,f23])).
% 5.73/1.11  fof(f27,plain,(
% 5.73/1.11    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.73/1.11    inference(cnf_transformation,[],[f4])).
% 5.73/1.11  fof(f4,axiom,(
% 5.73/1.11    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.73/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 5.73/1.11  fof(f4627,plain,(
% 5.73/1.11    ( ! [X33,X32] : (k4_xboole_0(X33,k4_xboole_0(X32,X33)) = k4_xboole_0(k2_xboole_0(X33,X32),k4_xboole_0(X32,X33))) )),
% 5.73/1.11    inference(superposition,[],[f4145,f3861])).
% 5.73/1.11  fof(f3861,plain,(
% 5.73/1.11    ( ! [X8,X7] : (k2_xboole_0(X7,X8) = k2_xboole_0(k4_xboole_0(X8,X7),X7)) )),
% 5.73/1.11    inference(backward_demodulation,[],[f956,f3838])).
% 5.73/1.11  fof(f3838,plain,(
% 5.73/1.11    ( ! [X8,X7] : (k4_xboole_0(X8,X7) = k5_xboole_0(X7,k2_xboole_0(X7,X8))) )),
% 5.73/1.11    inference(superposition,[],[f3825,f26])).
% 5.73/1.11  fof(f3825,plain,(
% 5.73/1.11    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 5.73/1.11    inference(forward_demodulation,[],[f3791,f643])).
% 5.73/1.11  fof(f643,plain,(
% 5.73/1.11    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 5.73/1.11    inference(backward_demodulation,[],[f111,f642])).
% 5.73/1.11  fof(f642,plain,(
% 5.73/1.11    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 5.73/1.11    inference(forward_demodulation,[],[f641,f22])).
% 5.73/1.11  fof(f641,plain,(
% 5.73/1.11    ( ! [X0] : (k2_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,X0)) )),
% 5.73/1.11    inference(forward_demodulation,[],[f619,f109])).
% 5.73/1.11  fof(f109,plain,(
% 5.73/1.11    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 5.73/1.11    inference(backward_demodulation,[],[f67,f105])).
% 5.73/1.11  fof(f619,plain,(
% 5.73/1.11    ( ! [X0] : (k2_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0))) )),
% 5.73/1.11    inference(superposition,[],[f30,f107])).
% 5.73/1.11  fof(f111,plain,(
% 5.73/1.11    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,X1)) )),
% 5.73/1.11    inference(backward_demodulation,[],[f82,f109])).
% 5.73/1.11  fof(f82,plain,(
% 5.73/1.11    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X1))) )),
% 5.73/1.11    inference(superposition,[],[f26,f67])).
% 5.73/1.11  fof(f3791,plain,(
% 5.73/1.11    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 5.73/1.11    inference(superposition,[],[f33,f107])).
% 5.73/1.11  fof(f33,plain,(
% 5.73/1.11    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 5.73/1.11    inference(cnf_transformation,[],[f11])).
% 5.73/1.11  fof(f11,axiom,(
% 5.73/1.11    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 5.73/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 5.73/1.11  fof(f956,plain,(
% 5.73/1.11    ( ! [X8,X7] : (k2_xboole_0(X7,X8) = k2_xboole_0(k5_xboole_0(X7,k2_xboole_0(X7,X8)),X7)) )),
% 5.73/1.11    inference(backward_demodulation,[],[f629,f940])).
% 5.73/1.11  fof(f940,plain,(
% 5.73/1.11    ( ! [X8,X7] : (k2_xboole_0(X7,X8) = k2_xboole_0(X7,k2_xboole_0(X7,X8))) )),
% 5.73/1.11    inference(superposition,[],[f890,f108])).
% 5.73/1.11  fof(f108,plain,(
% 5.73/1.11    ( ! [X4,X3] : (k3_xboole_0(X3,k2_xboole_0(X3,X4)) = X3) )),
% 5.73/1.11    inference(backward_demodulation,[],[f69,f105])).
% 5.73/1.11  fof(f69,plain,(
% 5.73/1.11    ( ! [X4,X3] : (k3_xboole_0(X3,k2_xboole_0(X3,X4)) = k4_xboole_0(X3,k1_xboole_0)) )),
% 5.73/1.11    inference(superposition,[],[f29,f24])).
% 5.73/1.11  fof(f890,plain,(
% 5.73/1.11    ( ! [X2,X1] : (k2_xboole_0(k3_xboole_0(X2,X1),X1) = X1) )),
% 5.73/1.11    inference(superposition,[],[f876,f23])).
% 5.73/1.11  fof(f876,plain,(
% 5.73/1.11    ( ! [X2,X1] : (k2_xboole_0(k3_xboole_0(X1,X2),X1) = X1) )),
% 5.73/1.11    inference(forward_demodulation,[],[f856,f657])).
% 5.73/1.11  fof(f657,plain,(
% 5.73/1.11    ( ! [X10,X9] : (k2_xboole_0(k3_xboole_0(X9,X10),k4_xboole_0(X9,X10)) = X9) )),
% 5.73/1.11    inference(forward_demodulation,[],[f656,f451])).
% 5.73/1.11  fof(f451,plain,(
% 5.73/1.11    ( ! [X30,X31] : (k2_xboole_0(X30,k4_xboole_0(X30,X31)) = X30) )),
% 5.73/1.11    inference(superposition,[],[f376,f74])).
% 5.73/1.11  fof(f74,plain,(
% 5.73/1.11    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k3_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 5.73/1.11    inference(forward_demodulation,[],[f70,f28])).
% 5.73/1.11  fof(f70,plain,(
% 5.73/1.11    ( ! [X6,X5] : (k3_xboole_0(X5,k4_xboole_0(X5,X6)) = k4_xboole_0(X5,k3_xboole_0(X5,X6))) )),
% 5.73/1.11    inference(superposition,[],[f29,f29])).
% 5.73/1.11  fof(f656,plain,(
% 5.73/1.11    ( ! [X10,X9] : (k2_xboole_0(X9,k4_xboole_0(X9,X10)) = k2_xboole_0(k3_xboole_0(X9,X10),k4_xboole_0(X9,X10))) )),
% 5.73/1.11    inference(forward_demodulation,[],[f630,f454])).
% 5.73/1.11  fof(f454,plain,(
% 5.73/1.11    ( ! [X6,X7] : (k3_xboole_0(X6,X7) = k5_xboole_0(X6,k4_xboole_0(X6,X7))) )),
% 5.73/1.11    inference(forward_demodulation,[],[f440,f29])).
% 5.73/1.11  fof(f440,plain,(
% 5.73/1.11    ( ! [X6,X7] : (k4_xboole_0(X6,k4_xboole_0(X6,X7)) = k5_xboole_0(X6,k4_xboole_0(X6,X7))) )),
% 5.73/1.11    inference(superposition,[],[f27,f74])).
% 5.73/1.11  fof(f630,plain,(
% 5.73/1.11    ( ! [X10,X9] : (k2_xboole_0(X9,k4_xboole_0(X9,X10)) = k2_xboole_0(k5_xboole_0(X9,k4_xboole_0(X9,X10)),k4_xboole_0(X9,X10))) )),
% 5.73/1.11    inference(superposition,[],[f30,f74])).
% 5.73/1.11  fof(f856,plain,(
% 5.73/1.11    ( ! [X2,X1] : (k2_xboole_0(k3_xboole_0(X1,X2),X1) = k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))) )),
% 5.73/1.11    inference(superposition,[],[f649,f28])).
% 5.73/1.11  fof(f649,plain,(
% 5.73/1.11    ( ! [X6,X5] : (k2_xboole_0(X5,X6) = k2_xboole_0(X5,k4_xboole_0(X6,X5))) )),
% 5.73/1.11    inference(forward_demodulation,[],[f648,f129])).
% 5.73/1.11  fof(f129,plain,(
% 5.73/1.11    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 5.73/1.11    inference(forward_demodulation,[],[f125,f48])).
% 5.73/1.11  fof(f125,plain,(
% 5.73/1.11    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,k1_xboole_0)) )),
% 5.73/1.11    inference(superposition,[],[f26,f85])).
% 5.73/1.11  fof(f85,plain,(
% 5.73/1.11    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 5.73/1.11    inference(backward_demodulation,[],[f56,f84])).
% 5.73/1.11  fof(f56,plain,(
% 5.73/1.11    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0)) )),
% 5.73/1.11    inference(resolution,[],[f52,f31])).
% 5.73/1.11  fof(f52,plain,(
% 5.73/1.11    ( ! [X1] : (r1_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1)) )),
% 5.73/1.11    inference(superposition,[],[f25,f48])).
% 5.73/1.11  fof(f648,plain,(
% 5.73/1.11    ( ! [X6,X5] : (k2_xboole_0(X5,k4_xboole_0(X6,X5)) = k2_xboole_0(k2_xboole_0(X5,X6),k1_xboole_0)) )),
% 5.73/1.11    inference(forward_demodulation,[],[f622,f559])).
% 5.73/1.11  fof(f622,plain,(
% 5.73/1.11    ( ! [X6,X5] : (k2_xboole_0(X5,k4_xboole_0(X6,X5)) = k2_xboole_0(k2_xboole_0(X5,X6),k3_xboole_0(X5,k4_xboole_0(X6,X5)))) )),
% 5.73/1.11    inference(superposition,[],[f30,f26])).
% 5.73/1.11  fof(f629,plain,(
% 5.73/1.11    ( ! [X8,X7] : (k2_xboole_0(X7,k2_xboole_0(X7,X8)) = k2_xboole_0(k5_xboole_0(X7,k2_xboole_0(X7,X8)),X7)) )),
% 5.73/1.11    inference(superposition,[],[f30,f108])).
% 5.73/1.11  fof(f4145,plain,(
% 5.73/1.11    ( ! [X6,X5] : (k4_xboole_0(k2_xboole_0(X5,X6),X5) = k4_xboole_0(X6,X5)) )),
% 5.73/1.11    inference(forward_demodulation,[],[f4133,f3838])).
% 5.73/1.11  fof(f4133,plain,(
% 5.73/1.11    ( ! [X6,X5] : (k4_xboole_0(k2_xboole_0(X5,X6),X5) = k5_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 5.73/1.11    inference(backward_demodulation,[],[f286,f4119])).
% 5.73/1.11  fof(f4119,plain,(
% 5.73/1.11    ( ! [X12,X13] : (k5_xboole_0(X12,X13) = k5_xboole_0(X13,X12)) )),
% 5.73/1.11    inference(superposition,[],[f3825,f4087])).
% 5.73/1.11  fof(f4087,plain,(
% 5.73/1.11    ( ! [X12,X13] : (k5_xboole_0(X13,k5_xboole_0(X12,X13)) = X12) )),
% 5.73/1.11    inference(forward_demodulation,[],[f4063,f48])).
% 5.73/1.11  fof(f4063,plain,(
% 5.73/1.11    ( ! [X12,X13] : (k5_xboole_0(X12,k1_xboole_0) = k5_xboole_0(X13,k5_xboole_0(X12,X13))) )),
% 5.73/1.11    inference(superposition,[],[f3825,f3806])).
% 5.73/1.11  fof(f3806,plain,(
% 5.73/1.11    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 5.73/1.11    inference(superposition,[],[f33,f107])).
% 5.73/1.11  fof(f286,plain,(
% 5.73/1.11    ( ! [X6,X5] : (k4_xboole_0(k2_xboole_0(X5,X6),X5) = k5_xboole_0(k2_xboole_0(X5,X6),X5)) )),
% 5.73/1.11    inference(superposition,[],[f59,f108])).
% 5.73/1.11  fof(f21,plain,(
% 5.73/1.11    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 5.73/1.11    inference(cnf_transformation,[],[f19])).
% 5.73/1.11  fof(f19,plain,(
% 5.73/1.11    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 5.73/1.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 5.73/1.11  fof(f18,plain,(
% 5.73/1.11    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 5.73/1.11    introduced(choice_axiom,[])).
% 5.73/1.11  fof(f17,plain,(
% 5.73/1.11    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.73/1.11    inference(ennf_transformation,[],[f15])).
% 5.73/1.11  fof(f15,negated_conjecture,(
% 5.73/1.11    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.73/1.11    inference(negated_conjecture,[],[f14])).
% 5.73/1.11  fof(f14,conjecture,(
% 5.73/1.11    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 5.73/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 5.73/1.11  % SZS output end Proof for theBenchmark
% 5.73/1.11  % (20806)------------------------------
% 5.73/1.11  % (20806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.73/1.11  % (20806)Termination reason: Refutation
% 5.73/1.11  
% 5.73/1.11  % (20806)Memory used [KB]: 17782
% 5.73/1.11  % (20806)Time elapsed: 0.696 s
% 5.73/1.11  % (20806)------------------------------
% 5.73/1.11  % (20806)------------------------------
% 5.73/1.11  % (20789)Success in time 0.754 s
%------------------------------------------------------------------------------
