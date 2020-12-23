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
% DateTime   : Thu Dec  3 12:34:42 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   38 (  89 expanded)
%              Number of leaves         :   10 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :   39 (  90 expanded)
%              Number of equality atoms :   38 (  89 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f52])).

fof(f52,plain,(
    k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k2_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK6,sK7,sK8)))) != k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k2_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK6,sK7,sK8)))) ),
    inference(superposition,[],[f33,f42])).

fof(f42,plain,(
    ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : k2_xboole_0(k4_enumset1(X9,X10,X11,X12,X13,X14),k2_xboole_0(k2_enumset1(X15,X15,X15,X15),k2_xboole_0(k2_enumset1(X16,X16,X16,X16),k2_enumset1(X17,X17,X17,X17)))) = k2_xboole_0(k4_enumset1(X9,X9,X9,X9,X10,X11),k2_xboole_0(k2_enumset1(X12,X12,X12,X12),k2_xboole_0(k2_enumset1(X13,X13,X13,X13),k2_enumset1(X14,X15,X16,X17)))) ),
    inference(forward_demodulation,[],[f38,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f38,plain,(
    ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : k2_xboole_0(k4_enumset1(X9,X9,X9,X9,X10,X11),k2_xboole_0(k2_xboole_0(k2_enumset1(X12,X12,X12,X12),k2_enumset1(X13,X13,X13,X13)),k2_enumset1(X14,X15,X16,X17))) = k2_xboole_0(k4_enumset1(X9,X10,X11,X12,X13,X14),k2_xboole_0(k2_enumset1(X15,X15,X15,X15),k2_xboole_0(k2_enumset1(X16,X16,X16,X16),k2_enumset1(X17,X17,X17,X17)))) ),
    inference(superposition,[],[f34,f18])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k2_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X4,X4,X4,X4))),k2_enumset1(X5,X6,X7,X8)) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_xboole_0(k2_enumset1(X6,X6,X6,X6),k2_xboole_0(k2_enumset1(X7,X7,X7,X7),k2_enumset1(X8,X8,X8,X8)))) ),
    inference(forward_demodulation,[],[f29,f18])).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k2_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X4,X4,X4,X4))),k2_enumset1(X5,X6,X7,X8)) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_xboole_0(k2_xboole_0(k2_enumset1(X6,X6,X6,X6),k2_enumset1(X7,X7,X7,X7)),k2_enumset1(X8,X8,X8,X8))) ),
    inference(definition_unfolding,[],[f22,f26,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X2,X2,X2,X2)) ),
    inference(definition_unfolding,[],[f17,f23,f15])).

fof(f15,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ),
    inference(definition_unfolding,[],[f16,f15,f15])).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f17,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k2_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X4,X4,X4,X4))),k2_enumset1(X5,X6,X7,X8)) ),
    inference(definition_unfolding,[],[f21,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k2_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X4,X4,X4,X4))) ),
    inference(definition_unfolding,[],[f19,f24])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_xboole_0(k2_enumset1(X6,X6,X6,X6),k2_enumset1(X7,X7,X7,X7))) ),
    inference(definition_unfolding,[],[f20,f23])).

fof(f20,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_enumset1)).

fof(f21,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).

fof(f22,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).

fof(f33,plain,(
    k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k2_enumset1(sK6,sK6,sK6,sK6),k2_xboole_0(k2_enumset1(sK7,sK7,sK7,sK7),k2_enumset1(sK8,sK8,sK8,sK8)))) != k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k2_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK6,sK7,sK8)))) ),
    inference(forward_demodulation,[],[f32,f18])).

fof(f32,plain,(
    k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k2_enumset1(sK6,sK6,sK6,sK6),k2_xboole_0(k2_enumset1(sK7,sK7,sK7,sK7),k2_enumset1(sK8,sK8,sK8,sK8)))) != k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k2_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK5,sK6,sK7,sK8))) ),
    inference(forward_demodulation,[],[f31,f18])).

fof(f31,plain,(
    k2_xboole_0(k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK4))),k2_enumset1(sK5,sK6,sK7,sK8)) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k2_enumset1(sK6,sK6,sK6,sK6),k2_xboole_0(k2_enumset1(sK7,sK7,sK7,sK7),k2_enumset1(sK8,sK8,sK8,sK8)))) ),
    inference(forward_demodulation,[],[f30,f18])).

fof(f30,plain,(
    k2_xboole_0(k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK4))),k2_enumset1(sK5,sK6,sK7,sK8)) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k2_xboole_0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)),k2_enumset1(sK8,sK8,sK8,sK8))) ),
    inference(backward_demodulation,[],[f28,f18])).

fof(f28,plain,(
    k2_xboole_0(k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK4))),k2_enumset1(sK5,sK6,sK7,sK8)) != k2_xboole_0(k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))),k2_enumset1(sK8,sK8,sK8,sK8)) ),
    inference(definition_unfolding,[],[f14,f26,f24,f15])).

fof(f14,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:52:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.39  % (27275)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.14/0.40  % (27275)Refutation found. Thanks to Tanya!
% 0.14/0.40  % SZS status Theorem for theBenchmark
% 0.14/0.40  % SZS output start Proof for theBenchmark
% 0.14/0.40  fof(f57,plain,(
% 0.14/0.40    $false),
% 0.14/0.40    inference(trivial_inequality_removal,[],[f52])).
% 0.14/0.40  fof(f52,plain,(
% 0.14/0.40    k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k2_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK6,sK7,sK8)))) != k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k2_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK6,sK7,sK8))))),
% 0.14/0.40    inference(superposition,[],[f33,f42])).
% 0.14/0.40  fof(f42,plain,(
% 0.14/0.40    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : (k2_xboole_0(k4_enumset1(X9,X10,X11,X12,X13,X14),k2_xboole_0(k2_enumset1(X15,X15,X15,X15),k2_xboole_0(k2_enumset1(X16,X16,X16,X16),k2_enumset1(X17,X17,X17,X17)))) = k2_xboole_0(k4_enumset1(X9,X9,X9,X9,X10,X11),k2_xboole_0(k2_enumset1(X12,X12,X12,X12),k2_xboole_0(k2_enumset1(X13,X13,X13,X13),k2_enumset1(X14,X15,X16,X17))))) )),
% 0.14/0.40    inference(forward_demodulation,[],[f38,f18])).
% 0.14/0.40  fof(f18,plain,(
% 0.14/0.40    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.14/0.40    inference(cnf_transformation,[],[f1])).
% 0.14/0.40  fof(f1,axiom,(
% 0.14/0.40    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.14/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.14/0.40  fof(f38,plain,(
% 0.14/0.40    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : (k2_xboole_0(k4_enumset1(X9,X9,X9,X9,X10,X11),k2_xboole_0(k2_xboole_0(k2_enumset1(X12,X12,X12,X12),k2_enumset1(X13,X13,X13,X13)),k2_enumset1(X14,X15,X16,X17))) = k2_xboole_0(k4_enumset1(X9,X10,X11,X12,X13,X14),k2_xboole_0(k2_enumset1(X15,X15,X15,X15),k2_xboole_0(k2_enumset1(X16,X16,X16,X16),k2_enumset1(X17,X17,X17,X17))))) )),
% 0.14/0.40    inference(superposition,[],[f34,f18])).
% 0.14/0.40  fof(f34,plain,(
% 0.14/0.40    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k2_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X4,X4,X4,X4))),k2_enumset1(X5,X6,X7,X8)) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_xboole_0(k2_enumset1(X6,X6,X6,X6),k2_xboole_0(k2_enumset1(X7,X7,X7,X7),k2_enumset1(X8,X8,X8,X8))))) )),
% 0.14/0.40    inference(forward_demodulation,[],[f29,f18])).
% 0.14/0.40  fof(f29,plain,(
% 0.14/0.40    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k2_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X4,X4,X4,X4))),k2_enumset1(X5,X6,X7,X8)) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_xboole_0(k2_xboole_0(k2_enumset1(X6,X6,X6,X6),k2_enumset1(X7,X7,X7,X7)),k2_enumset1(X8,X8,X8,X8)))) )),
% 0.14/0.40    inference(definition_unfolding,[],[f22,f26,f27])).
% 0.14/0.40  fof(f27,plain,(
% 0.14/0.40    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X2,X2,X2,X2))) )),
% 0.14/0.40    inference(definition_unfolding,[],[f17,f23,f15])).
% 0.14/0.40  fof(f15,plain,(
% 0.14/0.40    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.14/0.40    inference(cnf_transformation,[],[f7])).
% 0.14/0.40  fof(f7,axiom,(
% 0.14/0.40    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)),
% 0.14/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).
% 0.14/0.40  fof(f23,plain,(
% 0.14/0.40    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 0.14/0.40    inference(definition_unfolding,[],[f16,f15,f15])).
% 0.14/0.40  fof(f16,plain,(
% 0.14/0.40    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.14/0.40    inference(cnf_transformation,[],[f4])).
% 0.14/0.40  fof(f4,axiom,(
% 0.14/0.40    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.14/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.14/0.40  fof(f17,plain,(
% 0.14/0.40    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.14/0.40    inference(cnf_transformation,[],[f5])).
% 0.14/0.40  fof(f5,axiom,(
% 0.14/0.40    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.14/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.14/0.40  fof(f26,plain,(
% 0.14/0.40    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k2_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X4,X4,X4,X4))),k2_enumset1(X5,X6,X7,X8))) )),
% 0.14/0.40    inference(definition_unfolding,[],[f21,f25])).
% 0.14/0.40  fof(f25,plain,(
% 0.14/0.40    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k2_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X4,X4,X4,X4)))) )),
% 0.14/0.40    inference(definition_unfolding,[],[f19,f24])).
% 0.14/0.40  fof(f24,plain,(
% 0.14/0.40    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_xboole_0(k2_enumset1(X6,X6,X6,X6),k2_enumset1(X7,X7,X7,X7)))) )),
% 0.14/0.40    inference(definition_unfolding,[],[f20,f23])).
% 0.14/0.40  fof(f20,plain,(
% 0.14/0.40    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 0.14/0.40    inference(cnf_transformation,[],[f6])).
% 0.14/0.40  fof(f6,axiom,(
% 0.14/0.40    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.14/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).
% 0.14/0.40  fof(f19,plain,(
% 0.14/0.40    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.14/0.40    inference(cnf_transformation,[],[f8])).
% 0.14/0.40  fof(f8,axiom,(
% 0.14/0.40    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)),
% 0.14/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_enumset1)).
% 0.14/0.40  fof(f21,plain,(
% 0.14/0.40    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 0.14/0.40    inference(cnf_transformation,[],[f2])).
% 0.14/0.40  fof(f2,axiom,(
% 0.14/0.40    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 0.14/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).
% 0.14/0.40  fof(f22,plain,(
% 0.14/0.40    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))) )),
% 0.14/0.40    inference(cnf_transformation,[],[f3])).
% 0.14/0.40  fof(f3,axiom,(
% 0.14/0.40    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 0.14/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).
% 0.14/0.40  fof(f33,plain,(
% 0.14/0.40    k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k2_enumset1(sK6,sK6,sK6,sK6),k2_xboole_0(k2_enumset1(sK7,sK7,sK7,sK7),k2_enumset1(sK8,sK8,sK8,sK8)))) != k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k2_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK6,sK7,sK8))))),
% 0.14/0.40    inference(forward_demodulation,[],[f32,f18])).
% 0.14/0.40  fof(f32,plain,(
% 0.14/0.40    k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k2_enumset1(sK6,sK6,sK6,sK6),k2_xboole_0(k2_enumset1(sK7,sK7,sK7,sK7),k2_enumset1(sK8,sK8,sK8,sK8)))) != k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k2_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK5,sK6,sK7,sK8)))),
% 0.14/0.40    inference(forward_demodulation,[],[f31,f18])).
% 0.14/0.40  fof(f31,plain,(
% 0.14/0.40    k2_xboole_0(k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK4))),k2_enumset1(sK5,sK6,sK7,sK8)) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k2_enumset1(sK6,sK6,sK6,sK6),k2_xboole_0(k2_enumset1(sK7,sK7,sK7,sK7),k2_enumset1(sK8,sK8,sK8,sK8))))),
% 0.14/0.40    inference(forward_demodulation,[],[f30,f18])).
% 0.14/0.40  fof(f30,plain,(
% 0.14/0.40    k2_xboole_0(k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK4))),k2_enumset1(sK5,sK6,sK7,sK8)) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k2_xboole_0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7)),k2_enumset1(sK8,sK8,sK8,sK8)))),
% 0.14/0.40    inference(backward_demodulation,[],[f28,f18])).
% 0.14/0.40  fof(f28,plain,(
% 0.14/0.40    k2_xboole_0(k2_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k2_enumset1(sK4,sK4,sK4,sK4))),k2_enumset1(sK5,sK6,sK7,sK8)) != k2_xboole_0(k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_xboole_0(k2_enumset1(sK6,sK6,sK6,sK6),k2_enumset1(sK7,sK7,sK7,sK7))),k2_enumset1(sK8,sK8,sK8,sK8))),
% 0.14/0.40    inference(definition_unfolding,[],[f14,f26,f24,f15])).
% 0.14/0.40  fof(f14,plain,(
% 0.14/0.40    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))),
% 0.14/0.40    inference(cnf_transformation,[],[f13])).
% 0.14/0.40  fof(f13,plain,(
% 0.14/0.40    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))),
% 0.14/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f11,f12])).
% 0.14/0.40  fof(f12,plain,(
% 0.14/0.40    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))),
% 0.14/0.40    introduced(choice_axiom,[])).
% 0.14/0.40  fof(f11,plain,(
% 0.14/0.40    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 0.14/0.40    inference(ennf_transformation,[],[f10])).
% 0.14/0.40  fof(f10,negated_conjecture,(
% 0.14/0.40    ~! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 0.14/0.40    inference(negated_conjecture,[],[f9])).
% 0.14/0.40  fof(f9,conjecture,(
% 0.14/0.40    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 0.14/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_enumset1)).
% 0.14/0.40  % SZS output end Proof for theBenchmark
% 0.14/0.40  % (27275)------------------------------
% 0.14/0.40  % (27275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.40  % (27275)Termination reason: Refutation
% 0.14/0.40  
% 0.14/0.40  % (27275)Memory used [KB]: 6140
% 0.14/0.40  % (27275)Time elapsed: 0.008 s
% 0.14/0.40  % (27275)------------------------------
% 0.14/0.40  % (27275)------------------------------
% 0.14/0.40  % (27270)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.14/0.40  % (27260)Success in time 0.051 s
%------------------------------------------------------------------------------
