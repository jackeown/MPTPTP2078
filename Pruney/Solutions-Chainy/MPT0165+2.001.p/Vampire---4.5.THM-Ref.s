%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:53 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 373 expanded)
%              Number of leaves         :   11 ( 124 expanded)
%              Depth                    :   26
%              Number of atoms          :   60 ( 374 expanded)
%              Number of equality atoms :   59 ( 373 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f284,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f282])).

fof(f282,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(superposition,[],[f16,f279])).

fof(f279,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(backward_demodulation,[],[f50,f278])).

fof(f278,plain,(
    ! [X21,X19,X17,X22,X20,X18] : k2_xboole_0(k2_tarski(X17,X18),k2_enumset1(X19,X20,X21,X22)) = k4_enumset1(X17,X18,X19,X20,X21,X22) ),
    inference(backward_demodulation,[],[f117,f277])).

fof(f277,plain,(
    ! [X24,X23,X21,X19,X22,X20] : k5_enumset1(X19,X19,X20,X21,X22,X23,X24) = k4_enumset1(X19,X20,X21,X22,X23,X24) ),
    inference(forward_demodulation,[],[f271,f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_enumset1)).

fof(f271,plain,(
    ! [X24,X23,X21,X19,X22,X20] : k5_enumset1(X19,X19,X20,X21,X22,X23,X24) = k2_xboole_0(k1_enumset1(X19,X20,X21),k1_enumset1(X22,X23,X24)) ),
    inference(superposition,[],[f25,f232])).

fof(f232,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(superposition,[],[f154,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

fof(f154,plain,(
    ! [X6,X4,X5,X3] : k2_enumset1(X3,X4,X5,X6) = k3_enumset1(X3,X3,X4,X5,X6) ),
    inference(backward_demodulation,[],[f114,f153])).

fof(f153,plain,(
    ! [X6,X4,X7,X5] : k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5)) = k2_enumset1(X6,X7,X4,X5) ),
    inference(forward_demodulation,[],[f152,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f152,plain,(
    ! [X6,X4,X7,X5] : k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5)) = k2_xboole_0(k1_tarski(X6),k1_enumset1(X7,X4,X5)) ),
    inference(forward_demodulation,[],[f149,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] : k1_enumset1(X2,X0,X1) = k2_enumset1(X2,X0,X0,X1) ),
    inference(backward_demodulation,[],[f113,f143])).

fof(f143,plain,(
    ! [X4,X2,X3] : k1_enumset1(X2,X3,X4) = k2_xboole_0(k1_tarski(X2),k2_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f134,f19])).

fof(f134,plain,(
    ! [X4,X2,X3] : k3_enumset1(X2,X2,X2,X3,X4) = k2_xboole_0(k1_tarski(X2),k2_tarski(X3,X4)) ),
    inference(superposition,[],[f21,f128])).

fof(f128,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(superposition,[],[f122,f90])).

fof(f90,plain,(
    ! [X0,X1] : k1_enumset1(X0,X1,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(forward_demodulation,[],[f75,f17])).

fof(f17,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f75,plain,(
    ! [X0,X1] : k1_enumset1(X0,X1,X1) = k2_xboole_0(k2_tarski(X0,X0),k1_tarski(X1)) ),
    inference(backward_demodulation,[],[f28,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(forward_demodulation,[],[f72,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f72,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(superposition,[],[f63,f20])).

fof(f63,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X0,X1)) ),
    inference(superposition,[],[f56,f17])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X1,X1,X2)) ),
    inference(forward_demodulation,[],[f54,f19])).

fof(f54,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X1,X1,X2)) ),
    inference(superposition,[],[f43,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X2,X3,X4,X0,X0,X0,X1) = k3_enumset1(X2,X3,X4,X0,X1) ),
    inference(forward_demodulation,[],[f41,f21])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X2,X3,X4,X0,X0,X0,X1) = k2_xboole_0(k1_enumset1(X2,X3,X4),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f24,f18])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(superposition,[],[f25,f18])).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X1,X1) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_tarski(X1)) ),
    inference(superposition,[],[f27,f19])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X1,X2,X3,X0,X0) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)) ),
    inference(superposition,[],[f21,f17])).

fof(f122,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(forward_demodulation,[],[f112,f17])).

fof(f112,plain,(
    ! [X0] : k2_tarski(X0,X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(superposition,[],[f74,f90])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

fof(f113,plain,(
    ! [X2,X0,X1] : k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f20,f74])).

fof(f149,plain,(
    ! [X6,X4,X7,X5] : k2_xboole_0(k1_tarski(X6),k2_enumset1(X7,X4,X4,X5)) = k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f146,f74])).

fof(f146,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(backward_demodulation,[],[f43,f137])).

fof(f137,plain,(
    ! [X14,X17,X15,X13,X16] : k5_enumset1(X13,X13,X13,X14,X15,X16,X17) = k2_xboole_0(k1_tarski(X13),k2_enumset1(X14,X15,X16,X17)) ),
    inference(superposition,[],[f24,f128])).

fof(f114,plain,(
    ! [X6,X4,X5,X3] : k3_enumset1(X3,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X3,X4),k2_tarski(X5,X6)) ),
    inference(superposition,[],[f21,f74])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_enumset1)).

fof(f117,plain,(
    ! [X21,X19,X17,X22,X20,X18] : k5_enumset1(X17,X17,X18,X19,X20,X21,X22) = k2_xboole_0(k2_tarski(X17,X18),k2_enumset1(X19,X20,X21,X22)) ),
    inference(superposition,[],[f24,f74])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(superposition,[],[f26,f18])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(f16,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k6_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k6_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k6_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:25:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.19/0.42  % (6889)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.45  % (6888)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.47  % (6888)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f284,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(trivial_inequality_removal,[],[f282])).
% 0.19/0.47  fof(f282,plain,(
% 0.19/0.47    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)),
% 0.19/0.47    inference(superposition,[],[f16,f279])).
% 0.19/0.47  fof(f279,plain,(
% 0.19/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.19/0.47    inference(backward_demodulation,[],[f50,f278])).
% 0.19/0.47  fof(f278,plain,(
% 0.19/0.47    ( ! [X21,X19,X17,X22,X20,X18] : (k2_xboole_0(k2_tarski(X17,X18),k2_enumset1(X19,X20,X21,X22)) = k4_enumset1(X17,X18,X19,X20,X21,X22)) )),
% 0.19/0.47    inference(backward_demodulation,[],[f117,f277])).
% 0.19/0.47  fof(f277,plain,(
% 0.19/0.47    ( ! [X24,X23,X21,X19,X22,X20] : (k5_enumset1(X19,X19,X20,X21,X22,X23,X24) = k4_enumset1(X19,X20,X21,X22,X23,X24)) )),
% 0.19/0.47    inference(forward_demodulation,[],[f271,f23])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,axiom,(
% 0.19/0.47    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_enumset1)).
% 0.19/0.47  fof(f271,plain,(
% 0.19/0.47    ( ! [X24,X23,X21,X19,X22,X20] : (k5_enumset1(X19,X19,X20,X21,X22,X23,X24) = k2_xboole_0(k1_enumset1(X19,X20,X21),k1_enumset1(X22,X23,X24))) )),
% 0.19/0.47    inference(superposition,[],[f25,f232])).
% 0.19/0.47  fof(f232,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.19/0.47    inference(superposition,[],[f154,f19])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f10])).
% 0.19/0.47  fof(f10,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).
% 0.19/0.47  fof(f154,plain,(
% 0.19/0.47    ( ! [X6,X4,X5,X3] : (k2_enumset1(X3,X4,X5,X6) = k3_enumset1(X3,X3,X4,X5,X6)) )),
% 0.19/0.47    inference(backward_demodulation,[],[f114,f153])).
% 0.19/0.47  fof(f153,plain,(
% 0.19/0.47    ( ! [X6,X4,X7,X5] : (k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5)) = k2_enumset1(X6,X7,X4,X5)) )),
% 0.19/0.47    inference(forward_demodulation,[],[f152,f20])).
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f3])).
% 0.19/0.47  fof(f3,axiom,(
% 0.19/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.19/0.47  fof(f152,plain,(
% 0.19/0.47    ( ! [X6,X4,X7,X5] : (k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5)) = k2_xboole_0(k1_tarski(X6),k1_enumset1(X7,X4,X5))) )),
% 0.19/0.47    inference(forward_demodulation,[],[f149,f144])).
% 0.19/0.47  fof(f144,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X2,X0,X1) = k2_enumset1(X2,X0,X0,X1)) )),
% 0.19/0.47    inference(backward_demodulation,[],[f113,f143])).
% 0.19/0.47  fof(f143,plain,(
% 0.19/0.47    ( ! [X4,X2,X3] : (k1_enumset1(X2,X3,X4) = k2_xboole_0(k1_tarski(X2),k2_tarski(X3,X4))) )),
% 0.19/0.47    inference(forward_demodulation,[],[f134,f19])).
% 0.19/0.47  fof(f134,plain,(
% 0.19/0.47    ( ! [X4,X2,X3] : (k3_enumset1(X2,X2,X2,X3,X4) = k2_xboole_0(k1_tarski(X2),k2_tarski(X3,X4))) )),
% 0.19/0.47    inference(superposition,[],[f21,f128])).
% 0.19/0.47  fof(f128,plain,(
% 0.19/0.47    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.19/0.47    inference(superposition,[],[f122,f90])).
% 0.19/0.47  fof(f90,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X1,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.19/0.47    inference(forward_demodulation,[],[f75,f17])).
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f8])).
% 0.19/0.47  fof(f8,axiom,(
% 0.19/0.47    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.47  fof(f75,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X1,X1) = k2_xboole_0(k2_tarski(X0,X0),k1_tarski(X1))) )),
% 0.19/0.47    inference(backward_demodulation,[],[f28,f74])).
% 0.19/0.47  fof(f74,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.19/0.47    inference(forward_demodulation,[],[f72,f18])).
% 0.19/0.47  fof(f18,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f9])).
% 0.19/0.47  fof(f9,axiom,(
% 0.19/0.47    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 0.19/0.47  fof(f72,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.19/0.47    inference(superposition,[],[f63,f20])).
% 0.19/0.47  fof(f63,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X0,X1))) )),
% 0.19/0.47    inference(superposition,[],[f56,f17])).
% 0.19/0.47  fof(f56,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X1,X1,X2))) )),
% 0.19/0.47    inference(forward_demodulation,[],[f54,f19])).
% 0.19/0.47  fof(f54,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X1,X1,X2))) )),
% 0.19/0.47    inference(superposition,[],[f43,f42])).
% 0.19/0.47  fof(f42,plain,(
% 0.19/0.47    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X2,X3,X4,X0,X0,X0,X1) = k3_enumset1(X2,X3,X4,X0,X1)) )),
% 0.19/0.47    inference(forward_demodulation,[],[f41,f21])).
% 0.19/0.47  fof(f41,plain,(
% 0.19/0.47    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X2,X3,X4,X0,X0,X0,X1) = k2_xboole_0(k1_enumset1(X2,X3,X4),k2_tarski(X0,X1))) )),
% 0.19/0.47    inference(superposition,[],[f24,f18])).
% 0.19/0.47  fof(f24,plain,(
% 0.19/0.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f6])).
% 0.19/0.47  fof(f6,axiom,(
% 0.19/0.47    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).
% 0.19/0.47  fof(f43,plain,(
% 0.19/0.47    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.19/0.47    inference(superposition,[],[f25,f18])).
% 0.19/0.47  fof(f28,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X1,X1) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_tarski(X1))) )),
% 0.19/0.47    inference(superposition,[],[f27,f19])).
% 0.19/0.47  fof(f27,plain,(
% 0.19/0.47    ( ! [X2,X0,X3,X1] : (k3_enumset1(X1,X2,X3,X0,X0) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))) )),
% 0.19/0.47    inference(superposition,[],[f21,f17])).
% 0.19/0.47  fof(f122,plain,(
% 0.19/0.47    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 0.19/0.47    inference(forward_demodulation,[],[f112,f17])).
% 0.19/0.47  fof(f112,plain,(
% 0.19/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 0.19/0.47    inference(superposition,[],[f74,f90])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).
% 0.19/0.47  fof(f113,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))) )),
% 0.19/0.47    inference(superposition,[],[f20,f74])).
% 0.19/0.47  fof(f149,plain,(
% 0.19/0.47    ( ! [X6,X4,X7,X5] : (k2_xboole_0(k1_tarski(X6),k2_enumset1(X7,X4,X4,X5)) = k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5))) )),
% 0.19/0.47    inference(superposition,[],[f146,f74])).
% 0.19/0.47  fof(f146,plain,(
% 0.19/0.47    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.19/0.47    inference(backward_demodulation,[],[f43,f137])).
% 0.19/0.47  fof(f137,plain,(
% 0.19/0.47    ( ! [X14,X17,X15,X13,X16] : (k5_enumset1(X13,X13,X13,X14,X15,X16,X17) = k2_xboole_0(k1_tarski(X13),k2_enumset1(X14,X15,X16,X17))) )),
% 0.19/0.47    inference(superposition,[],[f24,f128])).
% 0.19/0.47  fof(f114,plain,(
% 0.19/0.47    ( ! [X6,X4,X5,X3] : (k3_enumset1(X3,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X3,X4),k2_tarski(X5,X6))) )),
% 0.19/0.47    inference(superposition,[],[f21,f74])).
% 0.19/0.47  fof(f25,plain,(
% 0.19/0.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f7])).
% 0.19/0.47  fof(f7,axiom,(
% 0.19/0.47    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_enumset1)).
% 0.19/0.47  fof(f117,plain,(
% 0.19/0.47    ( ! [X21,X19,X17,X22,X20,X18] : (k5_enumset1(X17,X17,X18,X19,X20,X21,X22) = k2_xboole_0(k2_tarski(X17,X18),k2_enumset1(X19,X20,X21,X22))) )),
% 0.19/0.47    inference(superposition,[],[f24,f74])).
% 0.19/0.47  fof(f50,plain,(
% 0.19/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))) )),
% 0.19/0.47    inference(superposition,[],[f26,f18])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f2])).
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).
% 0.19/0.47  fof(f16,plain,(
% 0.19/0.47    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k6_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4,sK5)),
% 0.19/0.47    inference(cnf_transformation,[],[f15])).
% 0.19/0.47  fof(f15,plain,(
% 0.19/0.47    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k6_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4,sK5)),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f13,f14])).
% 0.19/0.47  fof(f14,plain,(
% 0.19/0.47    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k6_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4,sK5)),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f13,plain,(
% 0.19/0.47    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)),
% 0.19/0.47    inference(ennf_transformation,[],[f12])).
% 0.19/0.47  fof(f12,negated_conjecture,(
% 0.19/0.47    ~! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)),
% 0.19/0.47    inference(negated_conjecture,[],[f11])).
% 0.19/0.47  fof(f11,conjecture,(
% 0.19/0.47    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (6888)------------------------------
% 0.19/0.47  % (6888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (6888)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (6888)Memory used [KB]: 1918
% 0.19/0.47  % (6888)Time elapsed: 0.022 s
% 0.19/0.47  % (6888)------------------------------
% 0.19/0.47  % (6888)------------------------------
% 0.19/0.47  % (6882)Success in time 0.115 s
%------------------------------------------------------------------------------
