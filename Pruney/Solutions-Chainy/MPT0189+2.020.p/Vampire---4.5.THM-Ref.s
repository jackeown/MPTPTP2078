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
% DateTime   : Thu Dec  3 12:34:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 (  88 expanded)
%              Number of leaves         :   14 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :   57 (  89 expanded)
%              Number of equality atoms :   56 (  88 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f281,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f272])).

fof(f272,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f21,f225])).

fof(f225,plain,(
    ! [X10,X8,X7,X9] : k2_enumset1(X7,X8,X9,X10) = k2_enumset1(X8,X7,X9,X10) ),
    inference(superposition,[],[f215,f77])).

fof(f77,plain,(
    ! [X14,X17,X15,X16] : k3_enumset1(X14,X15,X14,X16,X17) = k2_enumset1(X14,X15,X16,X17) ),
    inference(forward_demodulation,[],[f74,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f71,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(superposition,[],[f30,f22])).

fof(f22,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

fof(f74,plain,(
    ! [X14,X17,X15,X16] : k3_enumset1(X14,X15,X14,X16,X17) = k2_xboole_0(k2_tarski(X14,X15),k2_tarski(X16,X17)) ),
    inference(superposition,[],[f30,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0) ),
    inference(superposition,[],[f25,f22])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

fof(f215,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X5,X4,X6,X7) = k2_enumset1(X5,X4,X6,X7) ),
    inference(forward_demodulation,[],[f211,f78])).

fof(f78,plain,(
    ! [X21,X19,X20,X18] : k3_enumset1(X18,X19,X19,X20,X21) = k2_enumset1(X19,X18,X20,X21) ),
    inference(forward_demodulation,[],[f75,f76])).

fof(f75,plain,(
    ! [X21,X19,X20,X18] : k3_enumset1(X18,X19,X19,X20,X21) = k2_xboole_0(k2_tarski(X19,X18),k2_tarski(X20,X21)) ),
    inference(superposition,[],[f30,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[],[f25,f22])).

fof(f211,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X5,X4,X6,X7) = k3_enumset1(X4,X5,X5,X6,X7) ),
    inference(superposition,[],[f197,f177])).

fof(f177,plain,(
    ! [X21,X19,X17,X20,X18] : k3_enumset1(X17,X18,X19,X20,X21) = k4_enumset1(X17,X18,X19,X17,X20,X21) ),
    inference(forward_demodulation,[],[f174,f30])).

fof(f174,plain,(
    ! [X21,X19,X17,X20,X18] : k4_enumset1(X17,X18,X19,X17,X20,X21) = k2_xboole_0(k1_enumset1(X17,X18,X19),k2_tarski(X20,X21)) ),
    inference(superposition,[],[f82,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X0) ),
    inference(superposition,[],[f27,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(forward_demodulation,[],[f79,f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f33,f28])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

fof(f197,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X1,X2,X3,X4) ),
    inference(forward_demodulation,[],[f195,f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f195,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X1,X2,X3,X4) ),
    inference(superposition,[],[f183,f31])).

fof(f183,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X2,X3,X4,X5) ),
    inference(forward_demodulation,[],[f181,f31])).

fof(f181,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X2,X3,X4,X5) ),
    inference(superposition,[],[f137,f32])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f137,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X4,X5,X6,X0,X0,X1,X2,X3) = k5_enumset1(X4,X5,X6,X0,X1,X2,X3) ),
    inference(backward_demodulation,[],[f100,f134])).

fof(f134,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(forward_demodulation,[],[f124,f32])).

fof(f124,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(superposition,[],[f35,f26])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(f100,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X4,X5,X6,X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X4,X5,X6),k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f34,f28])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_enumset1)).

fof(f21,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:38:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.41  % (23566)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.41  % (23566)Refutation not found, incomplete strategy% (23566)------------------------------
% 0.22/0.41  % (23566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.41  % (23566)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.41  
% 0.22/0.41  % (23566)Memory used [KB]: 10618
% 0.22/0.41  % (23566)Time elapsed: 0.003 s
% 0.22/0.41  % (23566)------------------------------
% 0.22/0.41  % (23566)------------------------------
% 0.22/0.42  % (23555)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.43  % (23558)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.44  % (23558)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f281,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(trivial_inequality_removal,[],[f272])).
% 0.22/0.44  fof(f272,plain,(
% 0.22/0.44    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3)),
% 0.22/0.44    inference(superposition,[],[f21,f225])).
% 0.22/0.44  fof(f225,plain,(
% 0.22/0.44    ( ! [X10,X8,X7,X9] : (k2_enumset1(X7,X8,X9,X10) = k2_enumset1(X8,X7,X9,X10)) )),
% 0.22/0.44    inference(superposition,[],[f215,f77])).
% 0.22/0.44  fof(f77,plain,(
% 0.22/0.44    ( ! [X14,X17,X15,X16] : (k3_enumset1(X14,X15,X14,X16,X17) = k2_enumset1(X14,X15,X16,X17)) )),
% 0.22/0.44    inference(forward_demodulation,[],[f74,f76])).
% 0.22/0.44  fof(f76,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.22/0.44    inference(forward_demodulation,[],[f71,f28])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.44  fof(f71,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.22/0.44    inference(superposition,[],[f30,f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,axiom,(
% 0.22/0.44    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    ( ! [X14,X17,X15,X16] : (k3_enumset1(X14,X15,X14,X16,X17) = k2_xboole_0(k2_tarski(X14,X15),k2_tarski(X16,X17))) )),
% 0.22/0.44    inference(superposition,[],[f30,f37])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 0.22/0.44    inference(superposition,[],[f25,f22])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).
% 0.22/0.44  fof(f215,plain,(
% 0.22/0.44    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X5,X4,X6,X7) = k2_enumset1(X5,X4,X6,X7)) )),
% 0.22/0.44    inference(forward_demodulation,[],[f211,f78])).
% 0.22/0.44  fof(f78,plain,(
% 0.22/0.44    ( ! [X21,X19,X20,X18] : (k3_enumset1(X18,X19,X19,X20,X21) = k2_enumset1(X19,X18,X20,X21)) )),
% 0.22/0.44    inference(forward_demodulation,[],[f75,f76])).
% 0.22/0.44  fof(f75,plain,(
% 0.22/0.44    ( ! [X21,X19,X20,X18] : (k3_enumset1(X18,X19,X19,X20,X21) = k2_xboole_0(k2_tarski(X19,X18),k2_tarski(X20,X21))) )),
% 0.22/0.44    inference(superposition,[],[f30,f39])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)) )),
% 0.22/0.44    inference(superposition,[],[f25,f22])).
% 0.22/0.44  fof(f211,plain,(
% 0.22/0.44    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X5,X4,X6,X7) = k3_enumset1(X4,X5,X5,X6,X7)) )),
% 0.22/0.44    inference(superposition,[],[f197,f177])).
% 0.22/0.44  fof(f177,plain,(
% 0.22/0.44    ( ! [X21,X19,X17,X20,X18] : (k3_enumset1(X17,X18,X19,X20,X21) = k4_enumset1(X17,X18,X19,X17,X20,X21)) )),
% 0.22/0.44    inference(forward_demodulation,[],[f174,f30])).
% 0.22/0.44  fof(f174,plain,(
% 0.22/0.44    ( ! [X21,X19,X17,X20,X18] : (k4_enumset1(X17,X18,X19,X17,X20,X21) = k2_xboole_0(k1_enumset1(X17,X18,X19),k2_tarski(X20,X21))) )),
% 0.22/0.44    inference(superposition,[],[f82,f47])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X0)) )),
% 0.22/0.44    inference(superposition,[],[f27,f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).
% 0.22/0.44  fof(f82,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 0.22/0.44    inference(forward_demodulation,[],[f79,f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.44  fof(f79,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 0.22/0.44    inference(superposition,[],[f33,f28])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).
% 0.22/0.44  fof(f197,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X1,X2,X3,X4)) )),
% 0.22/0.44    inference(forward_demodulation,[],[f195,f29])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.44  fof(f195,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X1,X2,X3,X4)) )),
% 0.22/0.44    inference(superposition,[],[f183,f31])).
% 0.22/0.44  fof(f183,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X2,X3,X4,X5)) )),
% 0.22/0.44    inference(forward_demodulation,[],[f181,f31])).
% 0.22/0.44  fof(f181,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X2,X3,X4,X5)) )),
% 0.22/0.44    inference(superposition,[],[f137,f32])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.44  fof(f137,plain,(
% 0.22/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X4,X5,X6,X0,X0,X1,X2,X3) = k5_enumset1(X4,X5,X6,X0,X1,X2,X3)) )),
% 0.22/0.44    inference(backward_demodulation,[],[f100,f134])).
% 0.22/0.44  fof(f134,plain,(
% 0.22/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 0.22/0.44    inference(forward_demodulation,[],[f124,f32])).
% 0.22/0.44  fof(f124,plain,(
% 0.22/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 0.22/0.44    inference(superposition,[],[f35,f26])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).
% 0.22/0.44  fof(f100,plain,(
% 0.22/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X4,X5,X6,X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X4,X5,X6),k2_enumset1(X0,X1,X2,X3))) )),
% 0.22/0.44    inference(superposition,[],[f34,f28])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_enumset1)).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 0.22/0.44    inference(cnf_transformation,[],[f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 0.22/0.44    inference(ennf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 0.22/0.44    inference(negated_conjecture,[],[f16])).
% 0.22/0.44  fof(f16,conjecture,(
% 0.22/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (23558)------------------------------
% 0.22/0.44  % (23558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (23558)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (23558)Memory used [KB]: 1918
% 0.22/0.44  % (23558)Time elapsed: 0.016 s
% 0.22/0.44  % (23558)------------------------------
% 0.22/0.44  % (23558)------------------------------
% 0.22/0.44  % (23554)Success in time 0.083 s
%------------------------------------------------------------------------------
