%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 178 expanded)
%              Number of leaves         :   14 (  59 expanded)
%              Depth                    :   18
%              Number of atoms          :   71 ( 179 expanded)
%              Number of equality atoms :   70 ( 178 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f274,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f265])).

fof(f265,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f20,f156])).

fof(f156,plain,(
    ! [X6,X4,X5,X3] : k2_enumset1(X3,X4,X5,X6) = k3_enumset1(X3,X3,X4,X5,X6) ),
    inference(superposition,[],[f152,f77])).

% (10373)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X1,X2,X3,X4) ),
    inference(backward_demodulation,[],[f62,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(forward_demodulation,[],[f74,f64])).

fof(f64,plain,(
    ! [X6,X8,X7,X5,X9] : k4_enumset1(X9,X5,X6,X6,X7,X8) = k3_enumset1(X9,X5,X6,X7,X8) ),
    inference(forward_demodulation,[],[f63,f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(f63,plain,(
    ! [X6,X8,X7,X5,X9] : k4_enumset1(X9,X5,X6,X6,X7,X8) = k2_xboole_0(k1_tarski(X9),k2_enumset1(X5,X6,X7,X8)) ),
    inference(superposition,[],[f29,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X3,X0,X0,X1,X2) = k2_enumset1(X3,X0,X1,X2) ),
    inference(forward_demodulation,[],[f40,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X3,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f28,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k4_enumset1(X0,X1,X2,X2,X3,X4) ),
    inference(superposition,[],[f30,f43])).

fof(f43,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X7,X4,X5,X5,X6) = k2_enumset1(X7,X4,X5,X6) ),
    inference(forward_demodulation,[],[f41,f26])).

fof(f41,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X7,X4,X5,X5,X6) = k2_xboole_0(k1_tarski(X7),k1_enumset1(X4,X5,X6)) ),
    inference(superposition,[],[f28,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X2,X0,X0,X1) = k1_enumset1(X2,X0,X1) ),
    inference(backward_demodulation,[],[f35,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(forward_demodulation,[],[f36,f25])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(superposition,[],[f27,f21])).

fof(f21,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f26,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X1,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(superposition,[],[f30,f42])).

fof(f152,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(forward_demodulation,[],[f149,f42])).

fof(f149,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X1,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(superposition,[],[f139,f105])).

fof(f105,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(forward_demodulation,[],[f100,f28])).

fof(f100,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(superposition,[],[f55,f21])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(superposition,[],[f31,f22])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

fof(f139,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X3,X4,X5,X0,X0,X1,X2) = k4_enumset1(X3,X4,X5,X0,X1,X2) ),
    inference(backward_demodulation,[],[f57,f136])).

fof(f136,plain,(
    ! [X14,X12,X17,X15,X13,X16] : k2_xboole_0(k1_enumset1(X15,X16,X17),k1_enumset1(X12,X13,X14)) = k4_enumset1(X15,X16,X17,X12,X13,X14) ),
    inference(backward_demodulation,[],[f59,f135])).

fof(f135,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X5,X0) ),
    inference(forward_demodulation,[],[f134,f30])).

fof(f134,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0)) ),
    inference(superposition,[],[f88,f21])).

fof(f88,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k2_tarski(X0,X1)) = k5_enumset1(X2,X3,X4,X5,X6,X0,X1) ),
    inference(forward_demodulation,[],[f81,f85])).

fof(f85,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k6_enumset1(X10,X11,X12,X13,X7,X8,X8,X9) = k5_enumset1(X10,X11,X12,X13,X7,X8,X9) ),
    inference(backward_demodulation,[],[f69,f83])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(forward_demodulation,[],[f79,f72])).

fof(f72,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k6_enumset1(X7,X8,X8,X9,X10,X11,X12,X13) = k5_enumset1(X7,X8,X9,X10,X11,X12,X13) ),
    inference(forward_demodulation,[],[f66,f31])).

fof(f66,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k6_enumset1(X7,X8,X8,X9,X10,X11,X12,X13) = k2_xboole_0(k1_enumset1(X7,X8,X9),k2_enumset1(X10,X11,X12,X13)) ),
    inference(superposition,[],[f33,f39])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X1,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(superposition,[],[f34,f42])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

fof(f69,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k6_enumset1(X10,X11,X12,X13,X7,X8,X8,X9) = k2_xboole_0(k2_enumset1(X10,X11,X12,X13),k1_enumset1(X7,X8,X9)) ),
    inference(superposition,[],[f33,f39])).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X2,X3,X4,X5,X6,X0,X0,X1) = k2_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f34,f22])).

fof(f59,plain,(
    ! [X14,X12,X17,X15,X13,X16] : k5_enumset1(X15,X16,X17,X12,X13,X14,X14) = k2_xboole_0(k1_enumset1(X15,X16,X17),k1_enumset1(X12,X13,X14)) ),
    inference(superposition,[],[f31,f47])).

fof(f47,plain,(
    ! [X2,X3,X1] : k2_enumset1(X3,X1,X2,X2) = k1_enumset1(X3,X1,X2) ),
    inference(forward_demodulation,[],[f46,f38])).

fof(f46,plain,(
    ! [X2,X3,X1] : k2_enumset1(X3,X1,X2,X2) = k2_xboole_0(k1_tarski(X3),k2_tarski(X1,X2)) ),
    inference(superposition,[],[f26,f45])).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X1,X0,X0) = k2_tarski(X1,X0) ),
    inference(forward_demodulation,[],[f44,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X1,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(superposition,[],[f38,f21])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X3,X4,X5,X0,X0,X1,X2) = k2_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f31,f25])).

fof(f20,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:06:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.47  % (10371)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (10377)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (10378)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (10369)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (10374)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (10372)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (10382)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (10375)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (10383)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (10371)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f265])).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3)),
% 0.21/0.50    inference(superposition,[],[f20,f156])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    ( ! [X6,X4,X5,X3] : (k2_enumset1(X3,X4,X5,X6) = k3_enumset1(X3,X3,X4,X5,X6)) )),
% 0.21/0.50    inference(superposition,[],[f152,f77])).
% 0.21/0.50  % (10373)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X1,X2,X3,X4)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f62,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f74,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X6,X8,X7,X5,X9] : (k4_enumset1(X9,X5,X6,X6,X7,X8) = k3_enumset1(X9,X5,X6,X7,X8)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f63,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X6,X8,X7,X5,X9] : (k4_enumset1(X9,X5,X6,X6,X7,X8) = k2_xboole_0(k1_tarski(X9),k2_enumset1(X5,X6,X7,X8))) )),
% 0.21/0.50    inference(superposition,[],[f29,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X3,X0,X0,X1,X2) = k2_enumset1(X3,X0,X1,X2)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f40,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X3,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))) )),
% 0.21/0.50    inference(superposition,[],[f28,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k4_enumset1(X0,X1,X2,X2,X3,X4)) )),
% 0.21/0.50    inference(superposition,[],[f30,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X6,X4,X7,X5] : (k3_enumset1(X7,X4,X5,X5,X6) = k2_enumset1(X7,X4,X5,X6)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f41,f26])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X6,X4,X7,X5] : (k3_enumset1(X7,X4,X5,X5,X6) = k2_xboole_0(k1_tarski(X7),k1_enumset1(X4,X5,X6))) )),
% 0.21/0.50    inference(superposition,[],[f28,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X2,X0,X0,X1) = k1_enumset1(X2,X0,X1)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f35,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f36,f25])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.50    inference(superposition,[],[f27,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))) )),
% 0.21/0.50    inference(superposition,[],[f26,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X1,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.21/0.50    inference(superposition,[],[f30,f42])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f149,f42])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X1,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.50    inference(superposition,[],[f139,f105])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f100,f28])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.50    inference(superposition,[],[f55,f21])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))) )),
% 0.21/0.50    inference(superposition,[],[f31,f22])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X3,X4,X5,X0,X0,X1,X2) = k4_enumset1(X3,X4,X5,X0,X1,X2)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f57,f136])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    ( ! [X14,X12,X17,X15,X13,X16] : (k2_xboole_0(k1_enumset1(X15,X16,X17),k1_enumset1(X12,X13,X14)) = k4_enumset1(X15,X16,X17,X12,X13,X14)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f59,f135])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X5,X0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f134,f30])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) )),
% 0.21/0.50    inference(superposition,[],[f88,f21])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k2_tarski(X0,X1)) = k5_enumset1(X2,X3,X4,X5,X6,X0,X1)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f81,f85])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X12,X10,X8,X7,X13,X11,X9] : (k6_enumset1(X10,X11,X12,X13,X7,X8,X8,X9) = k5_enumset1(X10,X11,X12,X13,X7,X8,X9)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f69,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f79,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X12,X10,X8,X7,X13,X11,X9] : (k6_enumset1(X7,X8,X8,X9,X10,X11,X12,X13) = k5_enumset1(X7,X8,X9,X10,X11,X12,X13)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f66,f31])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X12,X10,X8,X7,X13,X11,X9] : (k6_enumset1(X7,X8,X8,X9,X10,X11,X12,X13) = k2_xboole_0(k1_enumset1(X7,X8,X9),k2_enumset1(X10,X11,X12,X13))) )),
% 0.21/0.50    inference(superposition,[],[f33,f39])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X1,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 0.21/0.50    inference(superposition,[],[f34,f42])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X12,X10,X8,X7,X13,X11,X9] : (k6_enumset1(X10,X11,X12,X13,X7,X8,X8,X9) = k2_xboole_0(k2_enumset1(X10,X11,X12,X13),k1_enumset1(X7,X8,X9))) )),
% 0.21/0.50    inference(superposition,[],[f33,f39])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X2,X3,X4,X5,X6,X0,X0,X1) = k2_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k2_tarski(X0,X1))) )),
% 0.21/0.50    inference(superposition,[],[f34,f22])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X14,X12,X17,X15,X13,X16] : (k5_enumset1(X15,X16,X17,X12,X13,X14,X14) = k2_xboole_0(k1_enumset1(X15,X16,X17),k1_enumset1(X12,X13,X14))) )),
% 0.21/0.50    inference(superposition,[],[f31,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X2,X3,X1] : (k2_enumset1(X3,X1,X2,X2) = k1_enumset1(X3,X1,X2)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f46,f38])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X3,X1] : (k2_enumset1(X3,X1,X2,X2) = k2_xboole_0(k1_tarski(X3),k2_tarski(X1,X2))) )),
% 0.21/0.50    inference(superposition,[],[f26,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_enumset1(X1,X0,X0) = k2_tarski(X1,X0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f44,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_enumset1(X1,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) )),
% 0.21/0.50    inference(superposition,[],[f38,f21])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X3,X4,X5,X0,X0,X1,X2) = k2_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2))) )),
% 0.21/0.50    inference(superposition,[],[f31,f25])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.50    inference(negated_conjecture,[],[f15])).
% 0.21/0.50  fof(f15,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (10371)------------------------------
% 0.21/0.50  % (10371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (10371)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (10371)Memory used [KB]: 1791
% 0.21/0.50  % (10371)Time elapsed: 0.078 s
% 0.21/0.50  % (10371)------------------------------
% 0.21/0.50  % (10371)------------------------------
% 0.21/0.51  % (10367)Success in time 0.137 s
%------------------------------------------------------------------------------
