%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0202+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:16 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 147 expanded)
%              Number of leaves         :   15 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :   63 ( 148 expanded)
%              Number of equality atoms :   62 ( 147 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f753,plain,(
    $false ),
    inference(subsumption_resolution,[],[f752,f582])).

fof(f582,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X5,X6,X7,X8)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k4_enumset1(X3,X4,X5,X6,X7,X8)))) ),
    inference(forward_demodulation,[],[f581,f326])).

fof(f326,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(definition_unfolding,[],[f292,f286])).

fof(f286,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f235])).

fof(f235,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

fof(f292,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f230])).

fof(f230,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

fof(f581,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X5,X6,X7,X8)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k4_enumset1(X2,X3,X4,X5,X6,X7),k1_tarski(X8)))) ),
    inference(backward_demodulation,[],[f369,f580])).

fof(f580,plain,(
    ! [X6,X12,X10,X8,X7,X13,X11,X9] : k2_xboole_0(k4_enumset1(X6,X7,X8,X9,X10,X11),k2_xboole_0(k1_tarski(X12),X13)) = k2_xboole_0(k1_tarski(X6),k2_xboole_0(k4_enumset1(X7,X8,X9,X10,X11,X12),X13)) ),
    inference(forward_demodulation,[],[f570,f280])).

fof(f280,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f570,plain,(
    ! [X6,X12,X10,X8,X7,X13,X11,X9] : k2_xboole_0(k4_enumset1(X6,X7,X8,X9,X10,X11),k2_xboole_0(k1_tarski(X12),X13)) = k2_xboole_0(k2_xboole_0(k1_tarski(X6),k4_enumset1(X7,X8,X9,X10,X11,X12)),X13) ),
    inference(superposition,[],[f280,f326])).

fof(f369,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_xboole_0(k1_tarski(X7),k1_tarski(X8)))) = k2_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k4_enumset1(X4,X4,X5,X6,X7,X8)) ),
    inference(forward_demodulation,[],[f368,f317])).

fof(f317,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(definition_unfolding,[],[f294,f286])).

fof(f294,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f248])).

fof(f248,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f368,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_xboole_0(k1_tarski(X7),k1_tarski(X8)))) = k2_xboole_0(k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k1_tarski(X3)),k4_enumset1(X4,X4,X5,X6,X7,X8)) ),
    inference(forward_demodulation,[],[f367,f317])).

fof(f367,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k1_tarski(X3)),k2_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k1_tarski(X8))) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_xboole_0(k1_tarski(X7),k1_tarski(X8)))) ),
    inference(forward_demodulation,[],[f337,f280])).

fof(f337,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k1_tarski(X3)),k2_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k1_tarski(X8))) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)),k1_tarski(X8))) ),
    inference(definition_unfolding,[],[f310,f315,f316])).

fof(f316,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)),k1_tarski(X7)) ),
    inference(definition_unfolding,[],[f284,f286])).

fof(f284,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f242])).

fof(f242,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

fof(f315,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k1_tarski(X3)),k2_xboole_0(k4_enumset1(X4,X4,X4,X5,X6,X7),k1_tarski(X8))) ),
    inference(definition_unfolding,[],[f309,f313,f314])).

fof(f314,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(definition_unfolding,[],[f295,f286])).

fof(f295,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_enumset1)).

fof(f313,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k1_tarski(X3)) ),
    inference(definition_unfolding,[],[f296,f286])).

fof(f296,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f259])).

fof(f259,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_enumset1)).

fof(f309,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f188])).

fof(f188,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l142_enumset1)).

fof(f310,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f212])).

fof(f212,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).

fof(f752,plain,(
    k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)))) ),
    inference(superposition,[],[f579,f280])).

fof(f579,plain,(
    k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))) ),
    inference(backward_demodulation,[],[f565,f567])).

fof(f567,plain,(
    ! [X14,X19,X17,X15,X13,X18,X16] : k2_xboole_0(k1_tarski(X19),k4_enumset1(X13,X14,X15,X16,X17,X18)) = k2_xboole_0(k1_tarski(X13),k4_enumset1(X14,X15,X16,X17,X18,X19)) ),
    inference(superposition,[],[f326,f282])).

fof(f282,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f565,plain,(
    k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK8),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))) ),
    inference(forward_demodulation,[],[f562,f282])).

fof(f562,plain,(
    k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK8),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))) ),
    inference(backward_demodulation,[],[f343,f534])).

fof(f534,plain,(
    ! [X2,X1] : k4_enumset1(X1,X1,X1,X1,X1,X2) = k2_xboole_0(k1_tarski(X2),k1_tarski(X1)) ),
    inference(superposition,[],[f317,f366])).

fof(f366,plain,(
    ! [X0,X1] : k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k1_tarski(X1)) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(forward_demodulation,[],[f335,f333])).

fof(f333,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k1_tarski(X1)) ),
    inference(definition_unfolding,[],[f305,f311])).

fof(f311,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k1_tarski(X1)) ),
    inference(definition_unfolding,[],[f298,f286])).

fof(f298,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f266])).

fof(f266,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_enumset1)).

fof(f305,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f215])).

fof(f215,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f335,plain,(
    ! [X0,X1] : k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k1_tarski(X1)) = k2_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k1_tarski(X0)) ),
    inference(definition_unfolding,[],[f307,f311,f311])).

fof(f307,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f173])).

fof(f173,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f343,plain,(
    k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k1_tarski(sK8),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))) ),
    inference(backward_demodulation,[],[f340,f282])).

fof(f340,plain,(
    k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))) != k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3),k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8)) ),
    inference(forward_demodulation,[],[f339,f317])).

fof(f339,plain,(
    k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))) != k2_xboole_0(k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k1_tarski(sK3)),k4_enumset1(sK4,sK4,sK5,sK6,sK7,sK8)) ),
    inference(forward_demodulation,[],[f338,f317])).

fof(f338,plain,(
    k2_xboole_0(k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k1_tarski(sK3)),k2_xboole_0(k4_enumset1(sK4,sK4,sK4,sK5,sK6,sK7),k1_tarski(sK8))) != k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k2_xboole_0(k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))) ),
    inference(forward_demodulation,[],[f319,f317])).

fof(f319,plain,(
    k2_xboole_0(k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k1_tarski(sK3)),k2_xboole_0(k4_enumset1(sK4,sK4,sK4,sK5,sK6,sK7),k1_tarski(sK8))) != k2_xboole_0(k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k1_tarski(sK1)),k2_xboole_0(k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))) ),
    inference(definition_unfolding,[],[f277,f315,f311,f286])).

fof(f277,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k2_tarski(sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f276])).

fof(f276,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k2_tarski(sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f274,f275])).

fof(f275,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k2_tarski(sK0,sK1),k5_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    introduced(choice_axiom,[])).

fof(f274,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(ennf_transformation,[],[f214])).

fof(f214,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(negated_conjecture,[],[f213])).

fof(f213,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_enumset1)).
%------------------------------------------------------------------------------
