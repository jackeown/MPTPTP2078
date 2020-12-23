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
% DateTime   : Thu Dec  3 12:34:18 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   27 (  39 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   28 (  40 expanded)
%              Number of equality atoms :   27 (  39 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1646,plain,(
    $false ),
    inference(subsumption_resolution,[],[f22,f1634])).

fof(f1634,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X6,X4,X5,X7) = k2_enumset1(X4,X6,X5,X7) ),
    inference(superposition,[],[f96,f75])).

fof(f75,plain,(
    ! [X10,X8,X7,X9] : k2_enumset1(X7,X8,X9,X10) = k2_xboole_0(k1_enumset1(X8,X9,X7),k1_tarski(X10)) ),
    inference(superposition,[],[f32,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f96,plain,(
    ! [X4,X2,X5,X3] : k2_enumset1(X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X2,X4,X3),k1_tarski(X5)) ),
    inference(superposition,[],[f32,f83])).

fof(f83,plain,(
    ! [X14,X15,X13] : k1_enumset1(X13,X15,X14) = k1_enumset1(X13,X14,X15) ),
    inference(superposition,[],[f79,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X0,X1) ),
    inference(superposition,[],[f30,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(f79,plain,(
    ! [X12,X13,X11] : k2_enumset1(X11,X12,X11,X13) = k1_enumset1(X11,X12,X13) ),
    inference(forward_demodulation,[],[f76,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f73,f29])).

fof(f73,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(superposition,[],[f32,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f76,plain,(
    ! [X12,X13,X11] : k2_enumset1(X11,X12,X11,X13) = k2_xboole_0(k2_tarski(X11,X12),k1_tarski(X13)) ),
    inference(superposition,[],[f32,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0) ),
    inference(superposition,[],[f28,f25])).

fof(f22,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:57:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.44  % (5905)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (5898)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (5897)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (5895)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (5902)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (5904)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.50  % (5906)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (5903)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (5903)Refutation not found, incomplete strategy% (5903)------------------------------
% 0.22/0.50  % (5903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (5903)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (5903)Memory used [KB]: 10618
% 0.22/0.50  % (5903)Time elapsed: 0.072 s
% 0.22/0.50  % (5903)------------------------------
% 0.22/0.50  % (5903)------------------------------
% 0.22/0.50  % (5896)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (5907)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.52  % (5893)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.52  % (5894)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.52  % (5908)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.52  % (5899)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.53  % (5892)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.53  % (5909)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.53  % (5900)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.54  % (5901)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.58/0.58  % (5908)Refutation found. Thanks to Tanya!
% 1.58/0.58  % SZS status Theorem for theBenchmark
% 1.58/0.58  % SZS output start Proof for theBenchmark
% 1.58/0.58  fof(f1646,plain,(
% 1.58/0.58    $false),
% 1.58/0.58    inference(subsumption_resolution,[],[f22,f1634])).
% 1.58/0.58  fof(f1634,plain,(
% 1.58/0.58    ( ! [X6,X4,X7,X5] : (k2_enumset1(X6,X4,X5,X7) = k2_enumset1(X4,X6,X5,X7)) )),
% 1.58/0.58    inference(superposition,[],[f96,f75])).
% 1.58/0.58  fof(f75,plain,(
% 1.58/0.58    ( ! [X10,X8,X7,X9] : (k2_enumset1(X7,X8,X9,X10) = k2_xboole_0(k1_enumset1(X8,X9,X7),k1_tarski(X10))) )),
% 1.58/0.58    inference(superposition,[],[f32,f28])).
% 1.58/0.58  fof(f28,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f4])).
% 1.58/0.58  fof(f4,axiom,(
% 1.58/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).
% 1.58/0.58  fof(f32,plain,(
% 1.58/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.58/0.58    inference(cnf_transformation,[],[f6])).
% 1.58/0.58  fof(f6,axiom,(
% 1.58/0.58    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 1.58/0.58  fof(f96,plain,(
% 1.58/0.58    ( ! [X4,X2,X5,X3] : (k2_enumset1(X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X2,X4,X3),k1_tarski(X5))) )),
% 1.58/0.58    inference(superposition,[],[f32,f83])).
% 1.58/0.58  fof(f83,plain,(
% 1.58/0.58    ( ! [X14,X15,X13] : (k1_enumset1(X13,X15,X14) = k1_enumset1(X13,X14,X15)) )),
% 1.58/0.58    inference(superposition,[],[f79,f55])).
% 1.58/0.58  fof(f55,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X0,X1)) )),
% 1.58/0.58    inference(superposition,[],[f30,f29])).
% 1.58/0.58  fof(f29,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f12])).
% 1.58/0.58  fof(f12,axiom,(
% 1.58/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.58/0.58  fof(f30,plain,(
% 1.58/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f5])).
% 1.58/0.58  fof(f5,axiom,(
% 1.58/0.58    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).
% 1.58/0.58  fof(f79,plain,(
% 1.58/0.58    ( ! [X12,X13,X11] : (k2_enumset1(X11,X12,X11,X13) = k1_enumset1(X11,X12,X13)) )),
% 1.58/0.58    inference(forward_demodulation,[],[f76,f78])).
% 1.58/0.58  fof(f78,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.58/0.58    inference(forward_demodulation,[],[f73,f29])).
% 1.58/0.58  fof(f73,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.58/0.58    inference(superposition,[],[f32,f25])).
% 1.58/0.58  fof(f25,plain,(
% 1.58/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f11])).
% 1.58/0.58  fof(f11,axiom,(
% 1.58/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.58/0.58  fof(f76,plain,(
% 1.58/0.58    ( ! [X12,X13,X11] : (k2_enumset1(X11,X12,X11,X13) = k2_xboole_0(k2_tarski(X11,X12),k1_tarski(X13))) )),
% 1.58/0.58    inference(superposition,[],[f32,f39])).
% 1.58/0.58  fof(f39,plain,(
% 1.58/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X0)) )),
% 1.58/0.58    inference(superposition,[],[f28,f25])).
% 1.58/0.58  fof(f22,plain,(
% 1.58/0.58    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 1.58/0.58    inference(cnf_transformation,[],[f21])).
% 1.58/0.58  fof(f21,plain,(
% 1.58/0.58    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 1.58/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f20])).
% 1.58/0.58  fof(f20,plain,(
% 1.58/0.58    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 1.58/0.58    introduced(choice_axiom,[])).
% 1.58/0.58  fof(f19,plain,(
% 1.58/0.58    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 1.58/0.58    inference(ennf_transformation,[],[f18])).
% 1.58/0.58  fof(f18,negated_conjecture,(
% 1.58/0.58    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 1.58/0.58    inference(negated_conjecture,[],[f17])).
% 1.58/0.58  fof(f17,conjecture,(
% 1.58/0.58    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).
% 1.58/0.58  % SZS output end Proof for theBenchmark
% 1.58/0.58  % (5908)------------------------------
% 1.58/0.58  % (5908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.58  % (5908)Termination reason: Refutation
% 1.58/0.58  
% 1.58/0.58  % (5908)Memory used [KB]: 6652
% 1.58/0.58  % (5908)Time elapsed: 0.141 s
% 1.58/0.58  % (5908)------------------------------
% 1.58/0.58  % (5908)------------------------------
% 1.58/0.58  % (5891)Success in time 0.212 s
%------------------------------------------------------------------------------
