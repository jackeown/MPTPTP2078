%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 462 expanded)
%              Number of leaves         :   13 ( 154 expanded)
%              Depth                    :   20
%              Number of atoms          :   76 ( 463 expanded)
%              Number of equality atoms :   75 ( 462 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1316,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1313,f326])).

fof(f326,plain,(
    ! [X14,X15,X13] : k1_enumset1(X13,X14,X15) = k2_enumset1(X13,X14,X13,X15) ),
    inference(forward_demodulation,[],[f321,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f94,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f94,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(superposition,[],[f72,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f71,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(superposition,[],[f49,f24])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(forward_demodulation,[],[f47,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(superposition,[],[f30,f25])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(f321,plain,(
    ! [X14,X15,X13] : k2_enumset1(X13,X14,X13,X15) = k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X15)) ),
    inference(superposition,[],[f72,f278])).

fof(f278,plain,(
    ! [X12,X13] : k2_tarski(X12,X13) = k1_enumset1(X12,X13,X12) ),
    inference(superposition,[],[f187,f157])).

fof(f157,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(superposition,[],[f145,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f39,f22])).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2)) ),
    inference(forward_demodulation,[],[f36,f24])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f35,f25])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X3,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f27,f24])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(f145,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) = k2_enumset1(X2,X0,X0,X1) ),
    inference(superposition,[],[f127,f22])).

fof(f127,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) = k2_enumset1(X3,X0,X1,X2) ),
    inference(backward_demodulation,[],[f35,f126])).

fof(f126,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X5,X5,X6,X7) = k2_enumset1(X4,X5,X6,X7) ),
    inference(forward_demodulation,[],[f122,f125])).

fof(f125,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3) ),
    inference(forward_demodulation,[],[f121,f25])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3) ),
    inference(superposition,[],[f92,f26])).

fof(f92,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4) ),
    inference(forward_demodulation,[],[f90,f26])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4) ),
    inference(superposition,[],[f60,f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X5,X0) ),
    inference(forward_demodulation,[],[f56,f30])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0)) ),
    inference(superposition,[],[f32,f20])).

fof(f20,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

fof(f122,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X5,X6,X7,X7) = k3_enumset1(X4,X5,X5,X6,X7) ),
    inference(superposition,[],[f92,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X4,X0,X0,X1,X2,X3) = k3_enumset1(X4,X0,X1,X2,X3) ),
    inference(forward_demodulation,[],[f41,f27])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X4,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f29,f25])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f187,plain,(
    ! [X4,X2,X3] : k2_enumset1(X4,X2,X2,X3) = k1_enumset1(X4,X3,X2) ),
    inference(backward_demodulation,[],[f155,f183])).

fof(f183,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) = k1_enumset1(X2,X0,X1) ),
    inference(backward_demodulation,[],[f37,f182])).

fof(f182,plain,(
    ! [X6,X7,X5] : k3_enumset1(X5,X6,X6,X6,X7) = k1_enumset1(X5,X6,X7) ),
    inference(forward_demodulation,[],[f177,f95])).

fof(f177,plain,(
    ! [X6,X7,X5] : k3_enumset1(X5,X6,X6,X6,X7) = k2_xboole_0(k2_tarski(X5,X6),k1_tarski(X7)) ),
    inference(superposition,[],[f49,f166])).

fof(f166,plain,(
    ! [X0,X1] : k2_tarski(X1,X0) = k2_enumset1(X1,X0,X0,X0) ),
    inference(forward_demodulation,[],[f154,f106])).

fof(f106,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(forward_demodulation,[],[f103,f22])).

fof(f103,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(superposition,[],[f95,f20])).

fof(f154,plain,(
    ! [X0,X1] : k2_enumset1(X1,X0,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(superposition,[],[f145,f20])).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_enumset1(X2,X0,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f35,f22])).

fof(f155,plain,(
    ! [X4,X2,X3] : k2_enumset1(X4,X2,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_tarski(X3,X2)) ),
    inference(superposition,[],[f145,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f1313,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK0,sK2) ),
    inference(superposition,[],[f34,f181])).

fof(f181,plain,(
    ! [X4,X2,X3,X1] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f176,f131])).

fof(f131,plain,(
    ! [X17,X15,X18,X16] : k4_enumset1(X18,X15,X15,X15,X16,X17) = k2_enumset1(X18,X15,X16,X17) ),
    inference(backward_demodulation,[],[f70,f127])).

fof(f70,plain,(
    ! [X17,X15,X18,X16] : k4_enumset1(X18,X15,X15,X15,X16,X17) = k2_xboole_0(k1_tarski(X18),k1_enumset1(X15,X16,X17)) ),
    inference(superposition,[],[f29,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(superposition,[],[f39,f35])).

fof(f176,plain,(
    ! [X4,X2,X3,X1] : k4_enumset1(X1,X2,X2,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(superposition,[],[f59,f166])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(forward_demodulation,[],[f54,f28])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f32,f25])).

fof(f34,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2)) ),
    inference(forward_demodulation,[],[f33,f21])).

fof(f33,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2)) ),
    inference(backward_demodulation,[],[f19,f21])).

fof(f19,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:04:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (1911)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (1901)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (1912)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (1898)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (1902)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (1910)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (1897)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (1899)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (1904)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (1903)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.51  % (1905)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (1918)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (1908)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (1914)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (1908)Refutation not found, incomplete strategy% (1908)------------------------------
% 0.22/0.51  % (1908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (1908)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (1908)Memory used [KB]: 10618
% 0.22/0.51  % (1908)Time elapsed: 0.092 s
% 0.22/0.51  % (1908)------------------------------
% 0.22/0.51  % (1908)------------------------------
% 0.22/0.51  % (1896)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.52  % (1900)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (1906)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.53  % (1915)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.56  % (1899)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f1316,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f1313,f326])).
% 0.22/0.56  fof(f326,plain,(
% 0.22/0.56    ( ! [X14,X15,X13] : (k1_enumset1(X13,X14,X15) = k2_enumset1(X13,X14,X13,X15)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f321,f95])).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f94,f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.22/0.56    inference(superposition,[],[f72,f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f71,f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.22/0.56    inference(superposition,[],[f49,f24])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f47,f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.22/0.56    inference(superposition,[],[f30,f25])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).
% 0.22/0.56  fof(f321,plain,(
% 0.22/0.56    ( ! [X14,X15,X13] : (k2_enumset1(X13,X14,X13,X15) = k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X15))) )),
% 0.22/0.56    inference(superposition,[],[f72,f278])).
% 0.22/0.56  fof(f278,plain,(
% 0.22/0.56    ( ! [X12,X13] : (k2_tarski(X12,X13) = k1_enumset1(X12,X13,X12)) )),
% 0.22/0.56    inference(superposition,[],[f187,f157])).
% 0.22/0.56  fof(f157,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.56    inference(superposition,[],[f145,f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.22/0.56    inference(superposition,[],[f39,f22])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f36,f24])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2))) )),
% 0.22/0.56    inference(superposition,[],[f35,f25])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X3,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))) )),
% 0.22/0.56    inference(superposition,[],[f27,f24])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
% 0.22/0.56  fof(f145,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) = k2_enumset1(X2,X0,X0,X1)) )),
% 0.22/0.56    inference(superposition,[],[f127,f22])).
% 0.22/0.56  fof(f127,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) = k2_enumset1(X3,X0,X1,X2)) )),
% 0.22/0.56    inference(backward_demodulation,[],[f35,f126])).
% 0.22/0.56  fof(f126,plain,(
% 0.22/0.56    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X5,X5,X6,X7) = k2_enumset1(X4,X5,X6,X7)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f122,f125])).
% 0.22/0.56  fof(f125,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f121,f25])).
% 0.22/0.56  fof(f121,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3)) )),
% 0.22/0.56    inference(superposition,[],[f92,f26])).
% 0.22/0.56  fof(f92,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f90,f26])).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)) )),
% 0.22/0.56    inference(superposition,[],[f60,f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X5,X0)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f56,f30])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) )),
% 0.22/0.56    inference(superposition,[],[f32,f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).
% 0.22/0.56  fof(f122,plain,(
% 0.22/0.56    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X5,X6,X7,X7) = k3_enumset1(X4,X5,X5,X6,X7)) )),
% 0.22/0.56    inference(superposition,[],[f92,f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X4,X0,X0,X1,X2,X3) = k3_enumset1(X4,X0,X1,X2,X3)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f41,f27])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X4,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3))) )),
% 0.22/0.56    inference(superposition,[],[f29,f25])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 0.22/0.56  fof(f187,plain,(
% 0.22/0.56    ( ! [X4,X2,X3] : (k2_enumset1(X4,X2,X2,X3) = k1_enumset1(X4,X3,X2)) )),
% 0.22/0.56    inference(backward_demodulation,[],[f155,f183])).
% 0.22/0.56  fof(f183,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) = k1_enumset1(X2,X0,X1)) )),
% 0.22/0.56    inference(backward_demodulation,[],[f37,f182])).
% 0.22/0.56  fof(f182,plain,(
% 0.22/0.56    ( ! [X6,X7,X5] : (k3_enumset1(X5,X6,X6,X6,X7) = k1_enumset1(X5,X6,X7)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f177,f95])).
% 0.22/0.56  fof(f177,plain,(
% 0.22/0.56    ( ! [X6,X7,X5] : (k3_enumset1(X5,X6,X6,X6,X7) = k2_xboole_0(k2_tarski(X5,X6),k1_tarski(X7))) )),
% 0.22/0.56    inference(superposition,[],[f49,f166])).
% 0.22/0.56  fof(f166,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_tarski(X1,X0) = k2_enumset1(X1,X0,X0,X0)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f154,f106])).
% 0.22/0.56  fof(f106,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f103,f22])).
% 0.22/0.56  fof(f103,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.56    inference(superposition,[],[f95,f20])).
% 0.22/0.56  fof(f154,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_enumset1(X1,X0,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) )),
% 0.22/0.56    inference(superposition,[],[f145,f20])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k3_enumset1(X2,X0,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))) )),
% 0.22/0.56    inference(superposition,[],[f35,f22])).
% 0.22/0.56  fof(f155,plain,(
% 0.22/0.56    ( ! [X4,X2,X3] : (k2_enumset1(X4,X2,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_tarski(X3,X2))) )),
% 0.22/0.56    inference(superposition,[],[f145,f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.56  fof(f1313,plain,(
% 0.22/0.56    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK1,sK0,sK2)),
% 0.22/0.56    inference(superposition,[],[f34,f181])).
% 0.22/0.56  fof(f181,plain,(
% 0.22/0.56    ( ! [X4,X2,X3,X1] : (k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f176,f131])).
% 0.22/0.56  fof(f131,plain,(
% 0.22/0.56    ( ! [X17,X15,X18,X16] : (k4_enumset1(X18,X15,X15,X15,X16,X17) = k2_enumset1(X18,X15,X16,X17)) )),
% 0.22/0.56    inference(backward_demodulation,[],[f70,f127])).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    ( ! [X17,X15,X18,X16] : (k4_enumset1(X18,X15,X15,X15,X16,X17) = k2_xboole_0(k1_tarski(X18),k1_enumset1(X15,X16,X17))) )),
% 0.22/0.56    inference(superposition,[],[f29,f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.56    inference(superposition,[],[f39,f35])).
% 0.22/0.56  fof(f176,plain,(
% 0.22/0.56    ( ! [X4,X2,X3,X1] : (k4_enumset1(X1,X2,X2,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))) )),
% 0.22/0.56    inference(superposition,[],[f59,f166])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f54,f28])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 0.22/0.56    inference(superposition,[],[f32,f25])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2))),
% 0.22/0.56    inference(forward_demodulation,[],[f33,f21])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2))),
% 0.22/0.56    inference(backward_demodulation,[],[f19,f21])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.22/0.56    inference(negated_conjecture,[],[f14])).
% 0.22/0.56  fof(f14,conjecture,(
% 0.22/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (1899)------------------------------
% 0.22/0.56  % (1899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (1899)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (1899)Memory used [KB]: 2430
% 0.22/0.56  % (1899)Time elapsed: 0.126 s
% 0.22/0.56  % (1899)------------------------------
% 0.22/0.56  % (1899)------------------------------
% 0.22/0.56  % (1894)Success in time 0.193 s
%------------------------------------------------------------------------------
