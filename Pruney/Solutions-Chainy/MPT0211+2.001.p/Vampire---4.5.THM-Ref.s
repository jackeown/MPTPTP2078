%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 171 expanded)
%              Number of leaves         :   12 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :   58 ( 172 expanded)
%              Number of equality atoms :   57 ( 171 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f901,plain,(
    $false ),
    inference(subsumption_resolution,[],[f883,f859])).

fof(f859,plain,(
    ! [X17,X18,X16] : k3_enumset1(X16,X17,X16,X16,X18) = k1_enumset1(X16,X17,X18) ),
    inference(forward_demodulation,[],[f858,f547])).

fof(f547,plain,(
    ! [X12,X13,X11] : k2_xboole_0(k2_tarski(X12,X13),k1_tarski(X11)) = k1_enumset1(X13,X12,X11) ),
    inference(backward_demodulation,[],[f297,f537])).

fof(f537,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) ),
    inference(backward_demodulation,[],[f45,f483])).

fof(f483,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X0,X0,X1) ),
    inference(superposition,[],[f468,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f468,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6) ),
    inference(superposition,[],[f248,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f248,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X3,X0,X1,X2) ),
    inference(forward_demodulation,[],[f236,f46])).

fof(f46,plain,(
    ! [X6,X4,X7,X5] : k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7) ),
    inference(superposition,[],[f33,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f236,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(superposition,[],[f82,f31])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(forward_demodulation,[],[f77,f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(superposition,[],[f37,f32])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f33,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f297,plain,(
    ! [X12,X13,X11] : k2_xboole_0(k1_tarski(X11),k2_tarski(X13,X12)) = k2_xboole_0(k2_tarski(X12,X13),k1_tarski(X11)) ),
    inference(superposition,[],[f54,f52])).

fof(f52,plain,(
    ! [X4,X2,X3] : k2_enumset1(X4,X2,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_tarski(X3,X2)) ),
    inference(superposition,[],[f45,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f54,plain,(
    ! [X4,X5,X3] : k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k2_enumset1(X3,X4,X4,X5) ),
    inference(superposition,[],[f45,f27])).

fof(f858,plain,(
    ! [X17,X18,X16] : k3_enumset1(X16,X17,X16,X16,X18) = k2_xboole_0(k2_tarski(X17,X16),k1_tarski(X18)) ),
    inference(superposition,[],[f82,f575])).

fof(f575,plain,(
    ! [X23,X22] : k2_tarski(X22,X23) = k2_enumset1(X23,X22,X23,X23) ),
    inference(backward_demodulation,[],[f491,f569])).

fof(f569,plain,(
    ! [X0,X1] : k2_tarski(X1,X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(backward_demodulation,[],[f289,f493])).

fof(f493,plain,(
    ! [X26,X27] : k2_tarski(X27,X26) = k2_enumset1(X27,X26,X26,X26) ),
    inference(superposition,[],[f468,f132])).

fof(f132,plain,(
    ! [X6,X7] : k2_tarski(X7,X6) = k2_enumset1(X6,X6,X6,X7) ),
    inference(superposition,[],[f52,f62])).

fof(f62,plain,(
    ! [X2,X1] : k2_tarski(X2,X1) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X1)) ),
    inference(superposition,[],[f59,f26])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(forward_demodulation,[],[f50,f28])).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f45,f31])).

fof(f289,plain,(
    ! [X0,X1] : k2_enumset1(X1,X0,X0,X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(superposition,[],[f54,f25])).

fof(f25,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f491,plain,(
    ! [X23,X22] : k2_xboole_0(k1_tarski(X23),k1_tarski(X22)) = k2_enumset1(X23,X22,X23,X23) ),
    inference(superposition,[],[f468,f289])).

fof(f883,plain,(
    k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK1,sK0,sK0,sK2) ),
    inference(superposition,[],[f44,f204])).

fof(f204,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X6,X7,X4,X4,X5) = k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f72,f28])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(forward_demodulation,[],[f66,f34])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(superposition,[],[f36,f28])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

fof(f44,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2)) ),
    inference(forward_demodulation,[],[f43,f26])).

fof(f43,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2)) ),
    inference(backward_demodulation,[],[f24,f26])).

fof(f24,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:17:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (13498)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.46  % (13493)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (13506)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (13494)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (13492)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (13503)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (13505)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (13497)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (13502)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (13502)Refutation not found, incomplete strategy% (13502)------------------------------
% 0.22/0.49  % (13502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (13502)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (13502)Memory used [KB]: 10618
% 0.22/0.49  % (13502)Time elapsed: 0.063 s
% 0.22/0.49  % (13502)------------------------------
% 0.22/0.49  % (13502)------------------------------
% 0.22/0.49  % (13495)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (13501)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (13499)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (13491)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.50  % (13494)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f901,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f883,f859])).
% 0.22/0.50  fof(f859,plain,(
% 0.22/0.50    ( ! [X17,X18,X16] : (k3_enumset1(X16,X17,X16,X16,X18) = k1_enumset1(X16,X17,X18)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f858,f547])).
% 0.22/0.50  fof(f547,plain,(
% 0.22/0.50    ( ! [X12,X13,X11] : (k2_xboole_0(k2_tarski(X12,X13),k1_tarski(X11)) = k1_enumset1(X13,X12,X11)) )),
% 0.22/0.50    inference(backward_demodulation,[],[f297,f537])).
% 0.22/0.50  fof(f537,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))) )),
% 0.22/0.50    inference(backward_demodulation,[],[f45,f483])).
% 0.22/0.50  fof(f483,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X0,X0,X1)) )),
% 0.22/0.50    inference(superposition,[],[f468,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.50  fof(f468,plain,(
% 0.22/0.50    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6)) )),
% 0.22/0.50    inference(superposition,[],[f248,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.50  fof(f248,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X3,X0,X1,X2)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f236,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X6,X4,X7,X5] : (k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7)) )),
% 0.22/0.50    inference(superposition,[],[f33,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.22/0.50  fof(f236,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.22/0.50    inference(superposition,[],[f82,f31])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f77,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.22/0.50    inference(superposition,[],[f37,f32])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))) )),
% 0.22/0.50    inference(superposition,[],[f33,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.50  fof(f297,plain,(
% 0.22/0.50    ( ! [X12,X13,X11] : (k2_xboole_0(k1_tarski(X11),k2_tarski(X13,X12)) = k2_xboole_0(k2_tarski(X12,X13),k1_tarski(X11))) )),
% 0.22/0.50    inference(superposition,[],[f54,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X4,X2,X3] : (k2_enumset1(X4,X2,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_tarski(X3,X2))) )),
% 0.22/0.50    inference(superposition,[],[f45,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X4,X5,X3] : (k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k2_enumset1(X3,X4,X4,X5)) )),
% 0.22/0.50    inference(superposition,[],[f45,f27])).
% 0.22/0.50  fof(f858,plain,(
% 0.22/0.50    ( ! [X17,X18,X16] : (k3_enumset1(X16,X17,X16,X16,X18) = k2_xboole_0(k2_tarski(X17,X16),k1_tarski(X18))) )),
% 0.22/0.50    inference(superposition,[],[f82,f575])).
% 0.22/0.50  fof(f575,plain,(
% 0.22/0.50    ( ! [X23,X22] : (k2_tarski(X22,X23) = k2_enumset1(X23,X22,X23,X23)) )),
% 0.22/0.50    inference(backward_demodulation,[],[f491,f569])).
% 0.22/0.50  fof(f569,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_tarski(X1,X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.50    inference(backward_demodulation,[],[f289,f493])).
% 0.22/0.50  fof(f493,plain,(
% 0.22/0.50    ( ! [X26,X27] : (k2_tarski(X27,X26) = k2_enumset1(X27,X26,X26,X26)) )),
% 0.22/0.50    inference(superposition,[],[f468,f132])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    ( ! [X6,X7] : (k2_tarski(X7,X6) = k2_enumset1(X6,X6,X6,X7)) )),
% 0.22/0.50    inference(superposition,[],[f52,f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X2,X1] : (k2_tarski(X2,X1) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X1))) )),
% 0.22/0.50    inference(superposition,[],[f59,f26])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f50,f28])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.22/0.50    inference(superposition,[],[f45,f31])).
% 0.22/0.50  fof(f289,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_enumset1(X1,X0,X0,X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.50    inference(superposition,[],[f54,f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.50  fof(f491,plain,(
% 0.22/0.50    ( ! [X23,X22] : (k2_xboole_0(k1_tarski(X23),k1_tarski(X22)) = k2_enumset1(X23,X22,X23,X23)) )),
% 0.22/0.50    inference(superposition,[],[f468,f289])).
% 0.22/0.50  fof(f883,plain,(
% 0.22/0.50    k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK1,sK0,sK0,sK2)),
% 0.22/0.50    inference(superposition,[],[f44,f204])).
% 0.22/0.50  fof(f204,plain,(
% 0.22/0.50    ( ! [X6,X4,X7,X5] : (k3_enumset1(X6,X7,X4,X4,X5) = k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5))) )),
% 0.22/0.50    inference(superposition,[],[f72,f28])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f66,f34])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.22/0.50    inference(superposition,[],[f36,f28])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK2))),
% 0.22/0.50    inference(forward_demodulation,[],[f43,f26])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK0,sK2))),
% 0.22/0.50    inference(backward_demodulation,[],[f24,f26])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.22/0.50    inference(negated_conjecture,[],[f19])).
% 0.22/0.50  fof(f19,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (13494)------------------------------
% 0.22/0.50  % (13494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (13494)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (13494)Memory used [KB]: 2302
% 0.22/0.50  % (13494)Time elapsed: 0.072 s
% 0.22/0.50  % (13494)------------------------------
% 0.22/0.50  % (13494)------------------------------
% 0.22/0.50  % (13490)Success in time 0.132 s
%------------------------------------------------------------------------------
